import sys

from collections import deque

class VerifierException(Exception):
    pass

class Constraint(object):
    def __init__(self, lhs, rhs, var_num_to_name):
        self.lhs = {}
        self.rhs = rhs
        for coef, literal in lhs:
            if literal in self.lhs or ~literal in self.lhs:
                raise VerifierException("Duplicate variable.")
            if coef < 0:
                literal = ~literal
                self.rhs -= coef
                coef = -coef
            self.lhs[literal] = coef
        if self.rhs < 0:
            self.rhs = 0
        self.var_num_to_name = var_num_to_name

    def copy(self):
        return Constraint([(coef, lit) for lit, coef in self.lhs.items()], self.rhs, self.var_num_to_name)

    def opposite(self):
        new_lhs = [(-coef, literal) for literal, coef in self.lhs.items()]
        new_rhs = -(self.rhs - 1)
        return Constraint(new_lhs, new_rhs, self.var_num_to_name)

    def other_half_of_equality_constraint(self):
        new_lhs = [(-coef, literal) for literal, coef in self.lhs.items()]
        new_rhs = -self.rhs
        return Constraint(new_lhs, new_rhs, self.var_num_to_name)

    def add_constraint(self, c):
        for literal, coef in c.lhs.items():
            if literal in self.lhs:
                self.lhs[literal] += coef
            elif ~literal in self.lhs:
                if self.lhs[~literal] > coef:
                    self.rhs -= coef
                    self.lhs[~literal] -= coef
                if self.lhs[~literal] == coef:
                    self.rhs -= coef
                    del self.lhs[~literal]
                else:
                    self.rhs -= self.lhs[~literal]
                    self.lhs[literal] = coef - self.lhs[~literal]
                    del self.lhs[~literal]
            else:
                self.lhs[literal] = coef
        self.rhs += c.rhs

    def div_and_round_up(self, x, d):
        return (x + d - 1) // d

    def saturate(self):
        for literal in self.lhs:
            if self.lhs[literal] > self.rhs:
                self.lhs[literal] = self.rhs

    def divide(self, d):
        if d <= 0:
            raise VerifierException("Trying to divide by {}".format(d))
        self.rhs = self.div_and_round_up(self.rhs, d)
        for literal in self.lhs:
            self.lhs[literal] = self.div_and_round_up(self.lhs[literal], d)

    def multiply(self, m):
        if m <= 0:
            raise VerifierException("Trying to multiply by {}".format(m))
        for var_num in self.lhs:
            self.lhs[var_num] *= m
        self.rhs *= m

    def literal_to_name(self, literal):
        if literal >= 0:
            return self.var_num_to_name[literal]
        else:
            return "~" + self.var_num_to_name[~literal]

    def __repr__(self):
        terms = sorted(self.lhs.items(), key=lambda term: term[0] if term[0] >= 0 else ~term[0])
        return " ".join("{} {}".format(str(coef), self.literal_to_name(literal))
                        for literal, coef in terms) + " >= " + str(self.rhs)


class VarNameNumMap(object):
    def __init__(self):
        self.next_var_num = 0
        self.var_name_to_num = {}
        self.var_num_to_name = {}

    def get_num(self, var_str):
        try:
            return self.var_name_to_num[var_str]
        except KeyError:
            var_num = self.next_var_num
            self.var_name_to_num[var_str] = var_num
            self.var_num_to_name[var_num] = var_str
            self.next_var_num += 1
            return var_num


class Proof(object):
    def __init__(self, opb):
        self.opb = opb
        self.var_name_num_map = VarNameNumMap()
        self.levels = {}
        self.level = -1
        self.constraint_num = 1
        self.constraints = {}
        self.objective = None
        self.numvars = int(opb[0][2])
        self.numcons = int(opb[0][4])
        print(self.numvars, self.numcons)

    def __repr__(self):
        return "Proof" + str(self.constraints)

    def parse_literal(self, lit_str):
        if lit_str[0] == "~":
            return ~self.var_name_num_map.get_num(lit_str[1:])
        else:
            return self.var_name_num_map.get_num(lit_str)

    def make_opb_constraint(self, line, equality_constraint_permitted=False):
        if line[-1] == ";":
            del line[-1]
        if line[-2] not in [">=", "="]:
            raise VerifierException("Can't find >=")
        is_equality_constraint = line[-2] == "="
        if is_equality_constraint and not equality_constraint_permitted:
            raise VerifierException("Equality constraint not permitted here!")
        lhs = []
        if line[-1][-1] == ";":
            line[-1] = line[-1][:-1]
        rhs = int(line[-1])
        for i in range(0, len(line)-2, 2):
            coef = int(line[i])
            literal = self.parse_literal(line[i+1])
            lhs.append((coef, literal))
        return is_equality_constraint, Constraint(lhs, rhs, self.var_name_num_map.var_num_to_name)

    def delete_constraint(self, num):
        del self.constraints[num]

    def add_constraint(self, constraint, num):
        terms = constraint.lhs.items()
        slack = sum(coef for (literal, coef) in terms) - constraint.rhs
        if self.level != -1 and num != -1:
            self.levels[self.level].append(num)
        self.constraints[num] = constraint

    def add_constraint_to_sequence(self, constraint):
        self.add_constraint(constraint, self.constraint_num)
        if verbose:
            print("  {}: {}".format(self.constraint_num, constraint))
        self.constraint_num += 1

    def process_p_line(self, line):
        stack = []
        pos = 0
        while pos < len(line):
            if pos < len(line)-1 and line[pos+1] == "*":
                stack[-1].multiply(int(line[pos]))
                pos += 1
            elif pos < len(line)-1 and line[pos+1] == "d":
                stack[-1].divide(int(line[pos]))
                pos += 1
            elif line[pos] == "s":
                stack[-1].saturate()
            elif line[pos] == "+":
                stack[-2].add_constraint(stack[-1])
                del stack[-1]
            elif line[pos][0] not in "0123456789":
                literal = self.parse_literal(line[pos])
                stack.append(Constraint([(1, literal)], 0, self.var_name_num_map.var_num_to_name))
            else:
                constraint_num = int(line[pos])
                if constraint_num == 0:
                    break
                stack.append(self.constraints[constraint_num].copy())
            pos += 1
        if len(stack) != 1:
            print(line)
            raise VerifierException("Stack length is {}!".format(len(stack)))
        self.add_constraint_to_sequence(stack[0])

    def unit_propagate(self):
        """Return None iff unit propagation wipes out a constraint"""
        known_literals = set()
        while True:
            prev_known_literals_sz = len(known_literals)
            for constraint in self.constraints.values():
                rhs = constraint.rhs
                unassigned_terms = []
                coef_sum = 0
                for literal, coef in constraint.lhs.items():
                    if literal in known_literals:
                        rhs -= coef
                    elif ~literal not in known_literals:
                        unassigned_terms.append((coef, literal))
                        coef_sum += coef
                slack = coef_sum - rhs
                if slack < 0:
                    return None
                for coef, literal in unassigned_terms:
                    if coef > slack:
                        known_literals.add(literal)
            if len(known_literals) == prev_known_literals_sz:
                return known_literals

    def process_u_line(self, line):
        _, constraint = self.make_opb_constraint(line)
        self.add_constraint(constraint.opposite(), -1)
        if self.unit_propagate() is not None:
            raise VerifierException("Failed to do proof for u constraint")
        self.delete_constraint(-1)
        self.add_constraint_to_sequence(constraint)

    def unit_propagate_solution(self, constraint, line_type):
        self.add_constraint(constraint, -1)
        known_literals = self.unit_propagate()
        if known_literals is None:
            raise VerifierException("{} rule leads to contradiction".format(line_type))
        known_vars = set(~lit if lit < 0 else lit for lit in known_literals)
        if not known_vars.issuperset(set(self.var_name_num_map.var_num_to_name.keys())):
            raise VerifierException("{} rule does not lead to full assignment".format(line_type))
        self.delete_constraint(-1)

    def process_o_line(self, line):
        vars_in_objective = set(~lit if lit<0 else lit for coef, lit in self.objective)
        literals_in_line = set(self.parse_literal(token) for token in line)
        rhs = len(line)
        vars_in_line = set(literal if literal >= 0 else ~literal for literal in literals_in_line)
        if not vars_in_line.issuperset(vars_in_objective):
            raise VerifierException("A variable appears in an o line but not in the objective")
        constraint = Constraint([(1, lit) for lit in literals_in_line], rhs, self.var_name_num_map.var_num_to_name)
        self.unit_propagate_solution(constraint, "o")
        f_of_line = 0
        for coef, lit in self.objective:
            if lit in literals_in_line:
                f_of_line += coef
        lhs = [(-coef, lit) for coef, lit in self.objective]
        self.add_constraint_to_sequence(Constraint(lhs, 1 - f_of_line, self.var_name_num_map.var_num_to_name))

    def process_v_line(self, line):
        terms = [(1, self.parse_literal(token)) for token in line]
        rhs = len(line)
        constraint = Constraint(terms, rhs, self.var_name_num_map.var_num_to_name)
        self.unit_propagate_solution(constraint, "v")
        self.add_constraint_to_sequence(constraint.opposite())

    def process_a_line(self, line):
        _, constraint = self.make_opb_constraint(line)
        self.add_constraint_to_sequence(constraint)

    def process_e_line(self, line):
        C = self.constraints[int(line[0])]
        _, D = self.make_opb_constraint(line[1:])
        for literal, coef in C.lhs.items():
            if literal not in D.lhs or coef != D.lhs[literal]:
                raise VerifierException()
        for literal, coef in D.lhs.items():
            if literal not in C.lhs or coef != C.lhs[literal]:
                raise VerifierException()
        if D.rhs != C.rhs:
            raise VerifierException("D.rhs != C.rhs")

    def process_ij_line(self, line, add_to_sequence):
        C = self.constraints[int(line[0])]
        is_equality_constraint, D = self.make_opb_constraint(line[1:])
        if is_equality_constraint:
            raise VerifierException("Wasn't expecting an equality constraint.")
        change = 0
        for literal, coef in D.lhs.items():
            if ~literal in C.lhs:
                change += C.lhs[~literal]
            elif literal in C.lhs and coef < C.lhs[literal]:
                change += C.lhs[literal] - coef
        if D.rhs > C.rhs - change:
            raise VerifierException("D.rhs > C.rhs")
        if add_to_sequence:
            self.add_constraint_to_sequence(D)

    def process_i_line(self, line):
        self.process_ij_line(line, False)

    def process_j_line(self, line):
        self.process_ij_line(line, True)

    def process_f_line(self, line):
        for line in self.opb[1:]:
            if not line:
                continue
            if line[0] == "min:":
                self.objective = []
                for i in range(1, len(line) - 1, 2):
                    coef = int(line[i])
                    literal = self.parse_literal(line[i+1])
                    self.objective.append((coef, literal))
            elif line[0][0] != "*":
                is_equality_constraint, constraint = self.make_opb_constraint(line, True)
                self.add_constraint_to_sequence(constraint)
                if is_equality_constraint:
                    self.add_constraint_to_sequence(constraint.other_half_of_equality_constraint())

    def process_set_level_line(self, line):
        self.level = int(line[0])
        if self.level not in self.levels:
            self.levels[self.level] = []

    def process_wipe_level_line(self, line):
        level = int(line[0])
        for key in self.levels:
            if key >= level:
                for constraint_num in self.levels[key]:
                    if constraint_num in self.constraints:
                        self.delete_constraint(constraint_num)
                self.levels[key].clear()

    def process_d_line(self, line):
        if line[-1] != "0":
            raise VerifierException("expected 0")
        for token in line[:-1]:
            constraint_num = int(token)
            self.delete_constraint(constraint_num)

    def process_c_line(self, line):
        c_constraint_num = int(line[0])
        constraint = self.constraints[c_constraint_num]
        if not constraint.lhs and constraint.rhs > 0:
            print("Proof checked.")
        else:
            raise VerifierException()

    def process_line(self, line):
        processing_functions = {"p": self.process_p_line,
                                "a": self.process_a_line,
                                "f": self.process_f_line,
                                "i": self.process_i_line,
                                "j": self.process_j_line,
                                "e": self.process_e_line,
                                "u": self.process_u_line,
                                "c": self.process_c_line,
                                "v": self.process_v_line,
                                "o": self.process_o_line,
                                "#": self.process_set_level_line,
                                "w": self.process_wipe_level_line,
                                "d": self.process_d_line}
        if line:
            if verbose:
                print(" ".join(line))
            if line[0] in processing_functions:
                processing_functions[line[0]](line[1:])
            elif line[0][0] != "*" and line[0] != "pseudo-Boolean":
                raise VerifierException("{} rule not implemented".format(line[0]))


if __name__=="__main__":
    verbose = False
    if len(sys.argv) > 3:
        if sys.argv[3] == "--verbose":
            verbose = True
    with open(sys.argv[1], "r") as f:
        opb_lines = [line.strip().split() for line in f.readlines()]
    proof = Proof(opb_lines)
    line_count = 0
    with open(sys.argv[2], "r") as f:
        for line in f.readlines():
            line_count += 1
    line_num = 0
    with open(sys.argv[2], "r") as f:
        for line in f.readlines():
            if not verbose:
                sys.stdout.write("\rprogress: {}%".format(int(line_num / line_count * 100)))
            line = line.strip().split()
            proof.process_line(line)
            line_num += 1
    if not verbose:
        print("\rprogress: 100%")
