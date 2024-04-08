############################################################
# CMPSC 442: Logic
############################################################

student_name = "Justin Cote"

############################################################
# Imports
############################################################

# Include your imports here, if any are used.
import copy


############################################################
# Section 1: Propositional Logic
############################################################

class Expr(object):
    def __hash__(self):
        return hash((type(self).__name__, self.hashable))

class Atom(Expr):
    def __init__(self, name):
        self.name = name
        self.hashable = name

    def __hash__(self):
        return super().__hash__()

    def __eq__(self, other):
        return type(self) == type(other) and self.name == other.name

    def __repr__(self):
        return "Atom("+str(self.name)+")"

    def atom_names(self):
        return set([self.name])

    def evaluate(self, assignment):
        return assignment[self.name]

    def to_cnf(self):
        return self

class Not(Expr):
    def __init__(self, arg):
        self.arg = arg
        self.hashable = arg

    def __hash__(self):
        return super().__hash__()

    def __eq__(self, other):
        return type(self) == type(other) and self.arg == other.arg

    def __repr__(self):
        return "Not("+str(self.arg)+")"

    def atom_names(self):
        return self.arg.atom_names()

    def evaluate(self, assignment):
        return not self.arg.evaluate(assignment)

    def to_cnf(self):
        clause = self.arg.to_cnf()
        # De Morgan Or
        if isinstance(clause, Or):
            return And(*(Not(disj).to_cnf() for disj in clause.hashable))
        # De Morgan AND
        elif isinstance(clause, And):
            return Or(*(Not(conj).to_cnf() for conj in clause.hashable))
        # Double Negate
        elif isinstance(clause, Not):
            return clause.arg
        elif isinstance(clause, Atom):
            return Not(clause)

class And(Expr):
    def __init__(self, *conjuncts):
        self.conjuncts = frozenset(conjuncts)
        self.hashable = self.conjuncts

    def __hash__(self):
        return super().__hash__()

    def __eq__(self, other):
        return type(self) == type(other) and self.conjuncts == other.conjuncts

    def __repr__(self):
        str = "And("
        for value in self.hashable:
            str += repr(value) + ", "
        return str[:-2]+")"

    def atom_names(self):
        name = set()
        for value in self.conjuncts:
            name = name.union(value.atom_names())
        return name

    def evaluate(self, assignment):
        for value in self.hashable:
            if not value.evaluate(assignment):
                return False
        return True

    def to_cnf(self):
        clauses = []
        if len(self.hashable) == 1:
            for atom in self.hashable:
                return atom
            
        for i in self.hashable:
            if isinstance(i,Not):
                if isinstance(i.arg, Or):
                    for j in i.arg.hashable:
                        clauses.append(Not(j))
                elif isinstance(i.arg, And):
                    struc = []
                    for j in i.arg.hashable:
                        struc.append(Not(j))
                    clauses.append(Or(*struc))
                else:
                    clauses.append(i)
            elif isinstance(i, And):
                for j in i.hashable:
                    clauses.append(j)
            else:
                clauses.append(i)
        return And(*clauses)

class Or(Expr):
    def __init__(self, *disjuncts):
        self.disjuncts = frozenset(disjuncts)
        self.hashable = self.disjuncts

    def __hash__(self):
        return super().__hash__()

    def __eq__(self, other):
        return type(self) == type(other) and self.disjuncts == other.disjuncts

    def __repr__(self):
        str = "Or("
        for value in self.hashable:
            str += repr(value) + ", "
        return str[:-2]+")"

    def atom_names(self):
        name = set()
        for value in self.disjuncts:
            name = name.union(value.atom_names())
        return name

    def evaluate(self, assignment):
        for value in self.hashable:
            if value.evaluate(assignment):
                return True
        return False

    def to_cnf(self):
        clauses = []
        clause = []
        And_struc = []
        Or_struc = []
        for x in self.hashable:
            if isinstance(x, Not):
                if isinstance(x.arg, Atom):
                    clauses.append(x)
                else:
                    clauses.append(x.to_cnf())
            else:
                clauses.append(x.to_cnf())

        for x in clauses:
            if isinstance(x,Or):
                for y in x.hashable:
                    Or_struc.append(y)
            elif isinstance(x, Not):
                if isinstance(x.arg, Atom):
                    Or_struc.append(x)
                else:
                    Or_struc.append(x.to_cnf())
            elif isinstance(x, And):
                tmp = []
                for y in x.hashable:
                    tmp.append(y)
                And_struc.append(tmp)
            else:
                Or_struc.append(x)

        if len(And_struc) > 1:
            for list in And_struc:
                for x in list:
                    for list1 in And_struc:
                        i = 0
                        if list != list1:
                            while i < 2:
                                tmp = copy.deepcopy(Or_struc)
                                if isinstance(list1[i], Not):
                                    if list1[i].arg != x:
                                        tmp.append(x)
                                        tmp.append(list1[i])
                                        clause.append(Or(*tmp))
                                elif isinstance(x, Not):
                                    if x.arg != list1[i]:
                                        tmp.append(x)
                                        tmp.append(list1[i])
                                        clause.append(Or(*tmp))
                                elif isinstance(x, Atom) and isinstance(list1[1], Atom):
                                    if x != list1[i]:
                                        tmp.append(x)
                                        tmp.append(list1[i])
                                        if (tmp == list) or (tmp==list1) or (tmp == [list1[1],list1[0]]) or (tmp ==[list[1],list[0]]):
                                            tmp = copy.deepcopy(Or_struc)
                                            i =2
                                        else:
                                            clause.append(Or(*tmp))
                                    else:
                                        clause.append(x)

                                i = i + 1
            return And(*clause)
        elif len(And_struc) == 1:
            for x in And_struc:
                for y in x:
                    tmp = copy.deepcopy(Or_struc)
                    tmp.append(y)
                    clause.append(Or(*tmp))
            return And(*clause)
        else:
            return Or(*Or_struc)

class Implies(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)

    def __hash__(self):
        return super().__hash__()

    def __eq__(self, other):
        return type(self) == type(other) and self.left == other.left and self.right == other.right

    def __repr__(self):
        return "Implies(" + str(repr(self.left))+", "+str(repr(self.right))+")"

    def atom_names(self):
        return self.left.atom_names().union(self.right.atom_names())

    def evaluate(self, assignment):
        if (self.left.evaluate(assignment) == True) and (self.right.evaluate(assignment) == False):
            return False
        else:
            return True

    def to_cnf(self):
        return Or(Not(self.left).to_cnf(), self.right).to_cnf()

class Iff(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.hashable = (left, right)

    def __hash__(self):
        return super().__hash__()

    def __eq__(self, other):
        return type(self) == type(other) and ((self.left == other.left and self.right == other.right) or (self.left == other.right and self.right == other.left))

    def __repr__(self):
        return "Iff("+str(self.left)+", "+str(self.right)+")"

    def atom_names(self):
        return self.left.atom_names().union(self.right.atom_names())

    def evaluate(self, assignment):
        if ((self.left.evaluate(assignment) and self.right.evaluate(assignment)) or (not self.left.evaluate(assignment) and not self.right.evaluate(assignment))):
            return True
        else:
            return False

    def to_cnf(self):
        return And(Implies(self.left, self.right).to_cnf(), Implies(self.right, self.left).to_cnf()).to_cnf()

def satisfying_assignments(expr):

    # Recursive Helper Function
    def generate_assignments(atom_names):
        if not atom_names:
            yield {}
        else:
            first_atom, *rest_atoms = atom_names
            for rest_assignment in generate_assignments(rest_atoms):
                yield {first_atom: False, **rest_assignment}
                yield {first_atom: True, **rest_assignment}

    all_atoms = expr.atom_names()

    for assignment in generate_assignments(all_atoms):
        if expr.evaluate(assignment):
            yield assignment

class KnowledgeBase(object):
    def __init__(self):
        self.facts = set()

    def get_facts(self):
        return self.facts

    def tell(self, expr):
        cnf_expr = expr.to_cnf()
        if isinstance(cnf_expr, And):
            self.facts.update(cnf_expr.hashable)
        else:
            self.facts.add(cnf_expr)

    def ask(self, expr):
        negation = Not(expr)
        current_facts = self.get_facts()
        assumption = And(*current_facts, negation).to_cnf()
        try:
            next(satisfying_assignments(assumption))
        except:
            return True
        return False
        

############################################################
# Section 2: Logic Puzzles
############################################################

# Puzzle 1


# Populate the knowledge base using statements of the form kb1.tell(...)
kb1 = KnowledgeBase()
kb1.tell(Implies(Atom("mythical"), Not(Atom("mortal"))))
kb1.tell(Implies(Not(Atom("mythical")), And(Atom("mortal"), Atom("mammal"))))
kb1.tell(Implies(Or(Not(Atom("mortal")), Atom("mammal")), Atom("horned")))
kb1.tell(Implies(Atom("horned"), Atom("magical")))


# Write an Expr for each query that should be asked of the knowledge base
mythical_query = Atom("mythical")
magical_query = Atom("magical")
horned_query = Atom("horned")

# Record your answers as True or False; if you wish to use the above queries,
# they should not be run when this file is loaded
is_mythical = False # kb1.ask(mythical_query)
is_magical = True # kb1.ask(magical_query)
is_horned = True # kb1.ask(horned_query)

# Puzzle 2

# Write an Expr of the form And(...) encoding the constraints
party_constraints = And(
    Implies(Or(Atom("m"),Atom("a")),Atom("j")),
    Implies(Not(Atom("m")),Atom("a")),
    Implies(Atom("a"), Not(Atom("j")))
)

# Compute a list of the valid attendance scenarios using a call to
# satisfying_assignments(expr)
valid_scenarios = list(satisfying_assignments(party_constraints))

# Write your answer to the question in the assignment
puzzle_2_question = """
John And Mary can go.
"""

# Puzzle 3

# rule 1 : room 1 has a prize in it and other room is empty 
# rule 2 : at least one door contains a prize and at least one is empty
# rule 3 : exactly one of the rules above is true

# Populate the knowledge base using statements of the form kb3.tell(...)
d1 = And(Atom('e1'),Atom('p2'),Not(Atom('e2')),Not(Atom('p1')))
d2 = And(Or(Atom('p1'),Atom('p2')),Or(Atom('e1'),Atom('e2')))
s1 = Iff(d2,Not(Atom('s1')))
s2 = Iff(d2,Atom('s2'))

kb3 = KnowledgeBase()
kb3.tell(d1)
kb3.tell(d2)
kb3.tell(s1)
kb3.tell(s2)


# Write your answer to the question in the assignment; the queries you make
# should not be run when this file is loaded
# is_first_room_empty = kb3.ask(Atom("e1"))
# is_first_room_occupied = kb3.ask(Atom("p1"))
# is_second_room_empty = kb3.ask(Atom("e2"))
# is_second_room_occupied = kb3.ask(Atom("p2"))
# is_first_sign_true = kb3.ask(Atom("s1"))
# is_second_sign_true = kb3.ask(Atom("s2"))

puzzle_3_question = f"""
Based on the given statements and the possible scenarios, the correct state of affairs is as follows:

- First Room:
  - Empty: True
  - Occupied: False

- Second Room:
  - Empty: False
  - Occupied: True

- First Sign Truth: False
- Second Sign Truth: True

Therefore the Prize is in Room 2, Room 1 is empty, and sign 2 is True
"""

# Puzzle 4

# Populate the knowledge base using statements of the form kb4.tell(...)
kb4 = KnowledgeBase() 
# add statements to the knowledge base
adams = And(Atom("ia"), Atom("kb"), Not(Atom("kc")))
brown = And(Atom("ib"), Not(Atom("kb")))
clark = And(Atom("kb"), Atom('ka'), Atom('ic'))
kb4.tell(adams) 
kb4.tell(brown) 
kb4.tell(clark)


# Determine the guilty suspect based on the queries
guilty_suspect = None

print(kb4.ask(And(brown, clark)))
print(kb4.ask(And(adams,clark)))
print(kb4.ask(And(adams,brown)))
print(kb4.ask(Atom('kb')))
print(kb4.ask(Atom('ka')))
print(kb4.ask(Atom('kc')))

# Query to determine the guilty suspect
# If Adams is guilty, then Brown's statement is true and Clark's statement is true
# if kb4.ask(And(brown, clark)):
#     guilty_suspect = "Adams"

# # If Brown is guilty, then Adams's statement is true and Clark's statement is true
# elif kb4.ask(And(adams,clark)):
#     guilty_suspect = "Brown"

# # If Clark is guilty, then both Adams and Brown's statements are true
# elif kb4.ask(And(adams,brown)):
#     guilty_suspect = "Clark"

# Uncomment the line corresponding to the guilty suspect
# guilty_suspect = "Adams"
guilty_suspect = "Brown"
# guilty_suspect = "Clark"
# Describe the queries made to ascertain the findings

puzzle_4_question = """
To determine the guilty suspect, we made the following queries:
1. I queried whether Brown's statement is true and Clark's statement is true, assuming Adams is guilty.
2. I queried whether Adams's statement is true and Clark's statement is true, assuming Brown is guilty.
3. I queried whether both Adams and Brown's statements are false, assuming Clark is guilty.

Note that my knowledge base failed so to get the correct answer I made my own truth table and solved it myself using pen and paper to get the answer brown.

Based on the results of these queries, we identified the guilty suspect.
"""




