import sys

from collections import deque

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

        
def parse_term(coef, var):
    coef = int(coef)
    rhs_change = 0
    if var[0] == "~":
        rhs_change = -coef
        var = var[1:]
        coef = -coef
    var_num = int(var[1:])
    return (coef, var_num), rhs_change

def make_opb_constraint(line):
    if line[-1] == ";":
        del line[-1]
    if line[-2] != ">=":
        print("Can't find >=")
        exit(1)
    lhs = {} 
    if line[-1][-1] == ";":
        line[-1] = line[-1][:-1]
    rhs = int(line[-1])
    for i in range(0, len(line)-2, 2):
        (coef, var_num), rhs_change = parse_term(line[i], line[i+1])
        lhs[var_num] = coef
        rhs += rhs_change
    return Constraint(lhs, rhs)


class Proof(object):
    def __init__(self, opb):
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
        for line in opb[1:]:
            self.add_constraint_to_sequence(make_opb_constraint(line))
        self.unit_propagate(True)
        self.constraints_that_unit_propagate.clear()

    def __repr__(self):
        return "Proof" + str(self.constraints)

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
            elif line[pos] == "+":
                stack[-2].add_constraint(stack[-1])
                del stack[-1]
            elif line[pos][0] in "~x":
                (coef, var_num), rhs = parse_term(1, line[pos])
                stack.append(Constraint({var_num: coef}, rhs))
            else:
                constraint_num = int(line[pos])
                if constraint_num == 0:
                    break
                stack.append(self.constraints[constraint_num].copy())
            pos += 1
        if len(stack) != 1:
            print("Stack length is {}!".format(len(stack)))
            exit(1)
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
        return False

    def process_u_line(self, line):
        self.add_constraint(make_opb_constraint(line).opposite(), -1)
        if not self.unit_propagate():
            print("Failed to do proof for u constraint")
            exit(1)
        self.delete_constraint(-1)
        self.add_constraint_to_sequence(make_opb_constraint(line))

    def process_set_level_line(self, line):
        self.level = int(line[0])
        if self.level not in self.levels:
            self.levels[self.level] = []

    def process_wipe_level_line(self, line):
        level = int(line[0])
        for key in self.levels:
            if key >= level:
                for constraint_num in self.levels[key]:
                    self.delete_constraint(constraint_num)
                self.levels[key].clear()

    def process_c_line(self, line):
        c_constraint_num = int(line[0])
        constraint = self.constraints[c_constraint_num]
        if not constraint.lhs and constraint.rhs == 1:
            print("Proof checked.")
        else:
            exit(1)

    def process_line(self, line):
        if line[0] == "p":
            self.process_p_line(line[1:])
        elif line[0] == "u":
            self.process_u_line(line[1:])
        elif line[0] == "c":
            self.process_c_line(line[1:])
        elif line[0] == "#":
            self.process_set_level_line(line[1:])
        elif line[0] == "w":
            self.process_wipe_level_line(line[1:])


if __name__=="__main__":
    with open(sys.argv[1], "r") as f:
        opb_lines = [line.strip().split() for line in f.readlines()]
    proof = Proof(opb_lines)
    with open(sys.argv[2], "r") as f:
        for line in f.readlines():
            line = line.strip().split()
            proof.process_line(line)
