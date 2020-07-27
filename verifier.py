import sys

class VerifierException(Exception):
    pass

def negated(literal):
    return literal[1:] if literal[0] == "~" else "~" + literal

def lit2var(literal):
    return literal[1:] if literal[0] == "~" else literal

class Constraint(object):
    def __init__(self, lhs, rhs):
        self.lhs = {}
        self.rhs = rhs
        for coef, literal in lhs:
            if literal in self.lhs or negated(literal) in self.lhs:
                raise VerifierException("Duplicate variable.")
            if coef < 0:
                literal = negated(literal)
                self.rhs -= coef
                coef = -coef
            self.lhs[literal] = coef
        if self.rhs < 0:
            self.rhs = 0

    def copy(self):
        return Constraint([(coef, lit) for lit, coef in self.lhs.items()], self.rhs)

    def opposite(self):
        new_lhs = [(-coef, literal) for literal, coef in self.lhs.items()]
        new_rhs = -(self.rhs - 1)
        return Constraint(new_lhs, new_rhs)

    def other_half_of_equality_constraint(self):
        new_lhs = [(-coef, literal) for literal, coef in self.lhs.items()]
        new_rhs = -self.rhs
        return Constraint(new_lhs, new_rhs)

    def add_constraint(self, c):
        for literal, coef in c.lhs.items():
            if literal in self.lhs:
                self.lhs[literal] += coef
            elif negated(literal) in self.lhs:
                if self.lhs[negated(literal)] > coef:
                    self.rhs -= coef
                    self.lhs[negated(literal)] -= coef
                if self.lhs[negated(literal)] == coef:
                    self.rhs -= coef
                    del self.lhs[negated(literal)]
                else:
                    self.rhs -= self.lhs[negated(literal)]
                    self.lhs[literal] = coef - self.lhs[negated(literal)]
                    del self.lhs[negated(literal)]
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
        for literal in self.lhs:
            self.lhs[literal] = self.div_and_round_up(self.lhs[literal], d)
        self.rhs = self.div_and_round_up(self.rhs, d)

    def multiply(self, m):
        if m <= 0:
            raise VerifierException("Trying to multiply by {}".format(m))
        for literal in self.lhs:
            self.lhs[literal] *= m
        self.rhs *= m

    def equals(self, other):
        for lhs1, lhs2 in [(self.lhs, other.lhs), (other.lhs, self.lhs)]:
            for literal, coef in lhs1.items():
                if literal not in lhs2 or coef != lhs2[literal]:
                    return False
        return other.rhs == self.rhs

    def syntactically_implies(self, other):
        change = 0
        for literal, coef in other.lhs.items():
            if negated(literal) in self.lhs:
                change += self.lhs[negated(literal)]
            elif literal in self.lhs and coef < self.lhs[literal]:
                change += self.lhs[literal] - coef
        return other.rhs <= self.rhs - change

    def __repr__(self):
        terms = sorted(self.lhs.items(), key=lambda term: lit2var(term[0]))
        return " ".join("{} {}".format(str(coef), literal)
                        for literal, coef in terms) + " >= " + str(self.rhs)


def solve_p_line(line, constraints):
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
            literal = line[pos]
            stack.append(Constraint([(1, literal)], 0))
        else:
            constraint_num = int(line[pos])
            if constraint_num == 0:
                break
            stack.append(constraints[constraint_num].copy())
        pos += 1
    if len(stack) != 1:
        raise VerifierException("Stack length is {}!".format(len(stack)))
    return stack[0]

def unit_propagate(constraints):
    """Return None iff unit propagation wipes out a constraint"""
    known_literals = set()
    while True:
        prev_known_literals_sz = len(known_literals)
        for constraint in constraints:
            rhs = constraint.rhs
            unassigned_terms = []
            for literal, coef in constraint.lhs.items():
                if literal in known_literals:
                    rhs -= coef
                elif negated(literal) not in known_literals:
                    unassigned_terms.append((coef, literal))
            slack = sum(coef for coef, literal in unassigned_terms) - rhs
            if slack < 0:
                return None
            for coef, literal in unassigned_terms:
                if coef > slack:
                    known_literals.add(literal)
        if len(known_literals) == prev_known_literals_sz:
            return known_literals


class Verifier(object):
    def __init__(self):
        self.levels = {}
        self.level = -1
        self.next_constraint_num = 1
        self.constraints = {}
        self.objective = None
        self.vars_in_model = None
        self.contradiction_found = False

    def __repr__(self):
        return "Verifier" + str(self.constraints)

    def delete_constraint(self, num):
        del self.constraints[num]

    def add_constraint_to_sequence(self, constraint):
        if self.level != -1:
            self.levels[self.level].append(self.next_constraint_num)
        self.constraints[self.next_constraint_num] = constraint
        if verbose:
            print("  {}: {}".format(self.next_constraint_num, constraint))
        self.next_constraint_num += 1

    def process_p_rule(self, line):
        self.add_constraint_to_sequence(solve_p_line(line, self.constraints))

    def process_u_rule(self, constraint):
        if unit_propagate(list(self.constraints.values()) + [constraint.opposite()]) is not None:
            raise VerifierException("Failed to do proof for u constraint")
        self.add_constraint_to_sequence(constraint)

    def unit_propagate_solution(self, constraint, line_type):
        known_literals = unit_propagate(list(self.constraints.values()) + [constraint])
        if known_literals is None:
            raise VerifierException("{} rule leads to contradiction".format(line_type))
        known_vars = set(lit2var(lit) for lit in known_literals)
        if not known_vars.issuperset(self.vars_in_model):
            raise VerifierException("{} rule does not lead to full assignment".format(line_type))

    def process_o_rule(self, line):
        vars_in_objective = set(lit2var(lit) for coef, lit in self.objective)
        literals_in_line = set(line)
        vars_in_line = set(lit2var(literal) for literal in literals_in_line)
        if not vars_in_line.issuperset(vars_in_objective):
            raise VerifierException("A variable appears in an the objective but not in an o line")
        constraint = Constraint([(1, lit) for lit in literals_in_line], len(line))
        self.unit_propagate_solution(constraint, "o")
        f_of_line = sum(coef for coef, lit in self.objective if lit in literals_in_line)
        lhs = [(-coef, lit) for coef, lit in self.objective]
        self.add_constraint_to_sequence(Constraint(lhs, 1 - f_of_line))

    def process_v_rule(self, line):
        terms = [(1, token) for token in line]
        constraint = Constraint(terms, len(line))
        self.unit_propagate_solution(constraint, "v")
        self.add_constraint_to_sequence(constraint.opposite())

    def process_a_rule(self, constraint):
        self.add_constraint_to_sequence(constraint)

    def process_e_rule(self, C_num, D):
        if not self.constraints[C_num].equals(D):
            raise VerifierException("Constraints not equal.")

    def process_i_rule(self, C_num, D):
        if not self.constraints[C_num].syntactically_implies(D):
            raise VerifierException("Syntactic implication was not proven.")

    def process_set_level_rule(self, level):
        self.level = level
        if level not in self.levels:
            self.levels[level] = []

    def process_wipe_level_rule(self, level):
        for key in self.levels:
            if key >= level:
                for constraint_num in self.levels[key]:
                    if constraint_num in self.constraints:
                        self.delete_constraint(constraint_num)
                self.levels[key].clear()

    def process_c_rule(self, c_constraint_num):
        constraint = self.constraints[c_constraint_num]
        if not constraint.lhs and constraint.rhs > 0:
            self.contradiction_found = True
        else:
            raise VerifierException()

    def set_objective(self, objective):
        self.objective = objective

    def make_set_of_vars_in_model(self):
        self.vars_in_model = set(lit2var(lit) for c in self.constraints.values() for lit in c.lhs)
        if self.objective is not None:
            self.vars_in_model |= set(lit2var(literal) for coef, literal in self.objective)

    def check_var_count(self, expected_var_count):
        if expected_var_count != len(self.vars_in_model):
            sys.stderr.write("Warning: Number of vars disagrees with first line of OPB file.\n")


class OpbVerifier(object):
    def __init__(self, opb):
        self.opb = opb
        self.verifier = Verifier()

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
            literal = line[i+1]
            lhs.append((coef, literal))
        return is_equality_constraint, Constraint(lhs, rhs)

    def process_f_line(self, line):
        num_constraints_before_reading_opb = len(self.verifier.constraints)
        for line in self.opb[1:]:
            if not line:
                continue
            if line[0] == "min:":
                objective = []
                for i in range(1, len(line) - 1, 2):
                    coef = int(line[i])
                    literal = line[i+1]
                    objective.append((coef, literal))
                self.verifier.set_objective(objective)
            elif line[0][0] != "*":
                is_equality_constraint, constraint = self.make_opb_constraint(line, True)
                self.verifier.process_a_rule(constraint)
                if is_equality_constraint:
                    self.verifier.process_a_rule(constraint.other_half_of_equality_constraint())
        self.verifier.make_set_of_vars_in_model()
        if self.opb[0][1] == "#variable=":
            self.verifier.check_var_count(int(self.opb[0][2]))
            expected_constraint_count = int(self.opb[0][4]) + num_constraints_before_reading_opb
            if expected_constraint_count != len(self.verifier.constraints):
                sys.stderr.write("Warning: Number of constraints disagrees with first line of OPB file.\n")

    def process_line(self, line):
        if verbose:
            print(" ".join(line))

        if line[0] == "p":
            self.verifier.process_p_rule(line[1:])
        elif line[0] == "u":
            _, constraint = self.make_opb_constraint(line[1:])
            self.verifier.process_u_rule(constraint)
        elif line[0] == "o":
            self.verifier.process_o_rule(line[1:])
        elif line[0] == "v":
            self.verifier.process_v_rule(line[1:])
        elif line[0] == "a":
            _, constraint = self.make_opb_constraint(line[1:])
            self.verifier.process_a_rule(constraint)
        elif line[0] == "e":
            C_num = int(line[1])
            _, D = self.make_opb_constraint(line[2:])
            self.verifier.process_e_rule(C_num, D)
        elif line[0] == "i":
            C_num = int(line[1])
            _, D = self.make_opb_constraint(line[2:])
            self.verifier.process_i_rule(C_num, D)
        elif line[0] == "j":
            C_num = int(line[1])
            _, D = self.make_opb_constraint(line[2:])
            self.verifier.process_i_rule(C_num, D)
            self.verifier.process_a_rule(D)
        elif line[0] == "#":
            self.verifier.process_set_level_rule(int(line[1]))
        elif line[0] == "w":
            self.verifier.process_wipe_level_rule(int(line[1]))
        elif line[0] == "d":
            if line[-1] != "0":
                raise VerifierException("expected 0")
            for token in line[1:-1]:
                constraint_num = int(token)
                self.verifier.delete_constraint(constraint_num)
        elif line[0] == "c":
            self.verifier.process_c_rule(int(line[1]))
        elif line[0] == "f":
            self.process_f_line(int(line[1]))
        elif line[0][0] != "*" and line[0] != "pseudo-Boolean":
            raise VerifierException("{} rule not implemented".format(line[0]))


if __name__=="__main__":
    verbose = False
    if len(sys.argv) > 3:
        if sys.argv[3] == "--verbose":
            verbose = True
    with open(sys.argv[1], "r") as f:
        opb_lines = [line.strip().split() for line in f.readlines()]
    opb_verifier = OpbVerifier(opb_lines)
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
            if not line:
                continue
            opb_verifier.process_line(line)
            line_num += 1
    if not verbose:
        print("\rprogress: 100%")
    if opb_verifier.verifier.contradiction_found:
        print("Contradiction found.")
