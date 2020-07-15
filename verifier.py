import sys

from collections import deque

class VerifierException(Exception):
    pass

class Constraint(object):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
        self.make_canonical_form()

    def copy(self):
        return Constraint(dict(self.lhs), self.rhs)

    def opposite(self):
        new_lhs = {var: -coef for (var, coef) in self.lhs.items()}
        new_rhs = -(self.rhs - 1)
        return Constraint(new_lhs, new_rhs)

    def other_half_of_equality_constraint(self):
        new_lhs = {var: -coef for (var, coef) in self.lhs.items()}
        new_rhs = -self.rhs
        return Constraint(new_lhs, new_rhs)

    def simplify(self):
        self.lhs = {var: coef for (var, coef) in self.lhs.items() if coef != 0}
        self.make_canonical_form()

    def add_constraint(self, c):
        for var_num in c.lhs:
            try:
                self.lhs[var_num] += c.lhs[var_num]
            except:
                self.lhs[var_num] = c.lhs[var_num]
        self.rhs += c.rhs
        self.make_canonical_form()

    def div_and_round_up(self, x, d):
        return (x + d - 1) // d

    def make_canonical_form(self):
        rhs = self.rhs
        terms = []
        for var, coef in self.lhs.items():
            if coef < 0:
                literal = ~var
                rhs -= coef
                coef = -coef
            else:
                literal = var
            terms.append((coef, literal))
        if rhs < 0:
            rhs = 0
        self.canonical_form = (terms, rhs)

    def saturate(self):
        terms, rhs = self.canonical_form
        for coef, literal in terms:
            if coef > rhs:
                coef = rhs
            if literal < 0:
                var = ~literal
                rhs -= coef
                coef = -coef
            else:
                var = literal
            self.lhs[var] = coef
        self.rhs = rhs
        self.make_canonical_form()

    def divide(self, d):
        terms, rhs = self.canonical_form
        rhs = self.div_and_round_up(rhs, d)
        for coef, literal in terms:
            coef = self.div_and_round_up(coef, d)
            if literal < 0:
                var = ~literal
                rhs -= coef
                coef = -coef
            else:
                var = literal
            self.lhs[var] = coef
        self.rhs = rhs
        self.make_canonical_form()

    def multiply(self, m):
        for var_num in self.lhs:
            self.lhs[var_num] *= m
        self.rhs *= m
        self.make_canonical_form()

    def __repr__(self):
        return str(self.lhs) + " >= " + str(self.rhs)

        
class Proof(object):
    def __init__(self, opb):
        self.opb = opb
        self.next_var_num = 1
        self.var_name_to_num = {}
        self.levels = {}
        self.level = -1
        self.numvars = int(opb[0][2])
        self.numcons = int(opb[0][4])
        print(self.numvars, self.numcons)
        self.constraint_num = 1
        self.constraints = {}
        self.literal_to_constraints = {literal: set() for var in range(1, self.numvars + 1)
                                       for literal in [var, ~var]}
        self.constraints_that_unit_propagate = set()
        self.known_literals = set()

    def __repr__(self):
        return "Proof" + str(self.constraints)

    def parse_term(self, coef, var):
        coef = int(coef)
        rhs_change = 0
        if var[0] == "~":
            rhs_change = -coef
            var = var[1:]
            coef = -coef
        if var in self.var_name_to_num:
            var_num = self.var_name_to_num[var]
        else:
            var_num = self.next_var_num
            self.var_name_to_num[var] = var_num
            self.next_var_num += 1
        return (coef, var_num), rhs_change

    def make_opb_constraint(self, line, equality_constraint_permitted=False):
        if line[-1] == ";":
            del line[-1]
        if line[-2] not in [">=", "="]:
            raise VerifierException("Can't find >=")
        is_equality_constraint = line[-2] == "="
        if is_equality_constraint and not equality_constraint_permitted:
            raise VerifierException("Equality constraint not permitted here!")
        lhs = {} 
        if line[-1][-1] == ";":
            line[-1] = line[-1][:-1]
        rhs = int(line[-1])
        for i in range(0, len(line)-2, 2):
            (coef, var_num), rhs_change = self.parse_term(line[i], line[i+1])
            lhs[var_num] = coef
            rhs += rhs_change
        return is_equality_constraint, Constraint(lhs, rhs)

    def delete_constraint(self, num):
        if num in self.constraints_that_unit_propagate:
            self.constraints_that_unit_propagate.remove(num)
        for coef, literal in self.constraints[num].canonical_form[0]:
            self.literal_to_constraints[literal].remove(num)
        del self.constraints[num]

    def add_constraint(self, constraint, num):
        terms, rhs = constraint.canonical_form
        slack = sum(coef for (coef, literal) in terms) - rhs
        if len(terms)==1 or any(coef > slack for (coef, literal) in terms):
            self.constraints_that_unit_propagate.add(num)
        for coef, literal in constraint.canonical_form[0]:
            self.literal_to_constraints[literal].add(num)
        if self.level != -1 and num != -1:
            self.levels[self.level].append(num)
        self.constraints[num] = constraint

    def add_constraint_to_sequence(self, constraint):
        self.add_constraint(constraint, self.constraint_num)
#       print(self.constraint_num)
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
                (coef, var_num), rhs = self.parse_term(1, line[pos])
                stack.append(Constraint({var_num: coef}, rhs))
            else:
                constraint_num = int(line[pos])
                if constraint_num == 0:
                    break
                stack.append(self.constraints[constraint_num].copy())
            pos += 1
        if len(stack) != 1:
            print(line)
            raise VerifierException("Stack length is {}!".format(len(stack)))
        stack[0].simplify()
        self.add_constraint_to_sequence(stack[0])


    def propagate_constraint(self, constraint_num, known_literals, constraints_to_process, constraints_to_process_set):
        # literals are stored as var-number (positive literal) or ~var-number (negated literal)
        constraint = self.constraints[constraint_num]
        terms, rhs = constraint.canonical_form
        unassigned_terms = []
        coef_sum = 0
        for coef, literal in terms:
            if literal in known_literals:
                rhs -= coef
            elif ~literal not in known_literals:
                unassigned_terms.append((coef, literal))
                coef_sum += coef

        slack = coef_sum - rhs
        if slack < 0:
            return True

        for coef, literal in unassigned_terms:
            if coef > slack:
                known_literals.add(literal)
                for constraint_num in self.literal_to_constraints[~literal]:
                    if constraint_num not in constraints_to_process_set:
                        constraints_to_process.append(constraint_num)
                        constraints_to_process_set.add(constraint_num)

        return False

    def unit_propagate(self, save_known_literals=False):
        """Return true iff unit propagation wipes out a constraint"""
        known_literals = set() if save_known_literals else set(self.known_literals)
        constraints_to_process = deque()
        constraints_to_process_set = set(self.constraints_that_unit_propagate)
        for num in constraints_to_process_set:
            constraints_to_process.append(num)
        while constraints_to_process:
            constraint_num = constraints_to_process.popleft()
            if self.propagate_constraint(constraint_num, known_literals, constraints_to_process, constraints_to_process_set):
                return True
            constraints_to_process_set.remove(constraint_num)
        if save_known_literals:
            self.known_literals = known_literals
            self.constraints_that_unit_propagate.clear()
        return False

    def process_u_line(self, line):
        _, constraint = self.make_opb_constraint(line)
        self.add_constraint(constraint.opposite(), -1)
        if not self.unit_propagate():
            raise VerifierException("Failed to do proof for u constraint")
        self.delete_constraint(-1)
        self.add_constraint_to_sequence(constraint)

    def process_a_line(self, line):
        _, constraint = self.make_opb_constraint(line)
        self.add_constraint_to_sequence(constraint)

    def process_e_line(self, line):
        C = self.constraints[int(line[0])]
        _, D = self.make_opb_constraint(line[1:])
        for var, coef in C.lhs.items():
            if var not in D.lhs or coef != D.lhs[var]:
                raise VerifierException()
        for var, coef in D.lhs.items():
            if var not in C.lhs or coef != C.lhs[var]:
                raise VerifierException()
        if D.rhs != C.rhs:
            raise VerifierException("D.rhs != C.rhs")

    def process_ij_line(self, line, add_to_sequence):
        C = self.constraints[int(line[0])]
        _, D = self.make_opb_constraint(line[1:])
        for var, coef in C.lhs.items():
            if var not in D.lhs or (coef>=0) != (D.lhs[var]>=0):
                raise VerifierException()
        if D.rhs > C.rhs:
            raise VerifierException("D.rhs > C.rhs")
        if add_to_sequence:
            self.add_constraint_to_sequence(D)

    def process_i_line(self, line):
        self.process_ij_line(line, False)

    def process_j_line(self, line):
        self.process_ij_line(line, True)

    def process_f_line(self, line):
        for line in self.opb[1:]:
            if line and line[0][0] != "*":
                is_equality_constraint, constraint = self.make_opb_constraint(line, True)
                self.add_constraint_to_sequence(constraint)
                if is_equality_constraint:
                    self.add_constraint_to_sequence(constraint.other_half_of_equality_constraint())
        self.unit_propagate(True)

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
                                "#": self.process_set_level_line,
                                "w": self.process_wipe_level_line,
                                "d": self.process_d_line}
        if line:
            if line[0] in processing_functions:
                processing_functions[line[0]](line[1:])
            elif line[0][0] != "*" and line[0] != "pseudo-Boolean":
                raise VerifierException("{} rule not implemented".format(line[0]))


if __name__=="__main__":
    with open(sys.argv[1], "r") as f:
        opb_lines = [line.strip().split() for line in f.readlines()]
    proof = Proof(opb_lines)
    with open(sys.argv[2], "r") as f:
        for line in f.readlines():
            line = line.strip().split()
            proof.process_line(line)
