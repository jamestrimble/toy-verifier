import sys

from collections import deque

class VerifierException(Exception):
    pass

class Constraint(object):
    def __init__(self, lhs, rhs):
        # TODO: don't require all vars to be positive; convert them here if necessary
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
        self.var_numbers = set()
        self.objective = None

    def __repr__(self):
        return "Proof" + str(self.constraints)

    def parse_literal(self, lit_str):
        if lit_str[0] == "~":
            negated = True
            var_str = lit_str[1:]
        else:
            negated = False
            var_str = lit_str[:]
        if var_str in self.var_name_to_num:
            var_num = self.var_name_to_num[var_str]
        else:
            var_num = self.next_var_num
            self.var_name_to_num[var_str] = var_num
            self.var_numbers.add(var_num)
            self.next_var_num += 1
        return ~var_num if negated else var_num

    def parse_term(self, coef, lit_str):
        coef = int(coef)
        rhs_change = 0
        literal = self.parse_literal(lit_str)
        if literal < 0:
            rhs_change = -coef
            var_num = ~literal
            coef = -coef
        else:
            var_num = literal
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
                if rhs <= 0:
                    return False
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
                return None
            constraints_to_process_set.remove(constraint_num)
        if save_known_literals:
            self.known_literals = known_literals
            self.constraints_that_unit_propagate.clear()
        return known_literals

    def process_u_line(self, line):
        _, constraint = self.make_opb_constraint(line)
        self.add_constraint(constraint.opposite(), -1)
        if self.unit_propagate() is not None:
            raise VerifierException("Failed to do proof for u constraint")
        self.delete_constraint(-1)
        self.add_constraint_to_sequence(constraint)

    def process_o_line(self, line):
        vars_in_objective = set(~lit if lit<0 else lit for coef, lit in self.objective)
        literals_in_line = set()
        vars_in_line = set()
        terms = {}
        rhs = len(line)
        for token in line:
            literals_in_line.add(self.parse_literal(token))
            (coef, var), rhs_change = self.parse_term("1", token)
            if var in vars_in_line:
                raise VerifierException("A variable appears more than once in an o line")
            vars_in_line.add(var)
            terms[var] = coef
            rhs += rhs_change
        if not vars_in_line.issuperset(vars_in_objective):
            raise VerifierException("A variable appears in an o line but not in the objective")
        constraint = Constraint(terms, rhs)
        self.add_constraint(constraint, -1)
        known_literals = self.unit_propagate()
        if known_literals is None:
            raise VerifierException("o rule leads to contradiction")
        known_vars = set(~lit if lit < 0 else lit for lit in known_literals)
        if not known_vars.issuperset(self.var_numbers):
            raise VerifierException("o rule does not lead to full assignment")
        self.delete_constraint(-1)
        f_of_line = 0
        for coef, lit in self.objective:
            if lit in literals_in_line:
                f_of_line += coef
#        print("f", f_of_line)
        rhs = 1 - f_of_line
        lhs = {}
        for coef, lit in self.objective:
            coef = -coef
            if lit < 0:
                var = ~lit
                rhs -= coef
                coef = -coef
            else:
                var = lit
            lhs[var] = coef
        constraint = Constraint(lhs, rhs)
#        print("(o)", constraint)
        self.add_constraint_to_sequence(constraint)

    def process_v_line(self, line):
        terms = {}
        rhs = len(line)
        for token in line:
            (coef, var), rhs_change = self.parse_term("1", token)
            terms[var] = coef
            rhs += rhs_change
        constraint = Constraint(terms, rhs)
        self.add_constraint(constraint, -1)
        known_literals = self.unit_propagate()
        if known_literals is None:
            raise VerifierException("v rule leads to contradiction")
        known_vars = set(~lit if lit < 0 else lit for lit in known_literals)
        if not known_vars.issuperset(self.var_numbers):
            raise VerifierException("v rule does not lead to full assignment")
        self.delete_constraint(-1)
        self.add_constraint_to_sequence(constraint.opposite())

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
                                "v": self.process_v_line,
                                "o": self.process_o_line,
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
