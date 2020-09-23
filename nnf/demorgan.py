from nnf import NNF, Var, And, Or, Internal
from nnf.util import memoize

def distribute(node: NNF):
    
    if isinstance(node, Var):
        return node

    elif isinstance(node, And):
        
        # And(Var(A), Var(B)) -> And(Var(A), Var(B))
        if all([isinstance(child, Var) for child in node.children]):
            return node

        else:
            left, right = node.children
            return And({distribute(left), distribute(right)})

    elif isinstance(node, Or):

        # Or(Var(A), Var(B)) -> Or(Var(A), Var(B))
        if all([isinstance(child, Var) for child in node.children]):
            return node
        
        else:
            left, right = node.children

            # Or(And(A,B), And(C, D)) -> And(Or(A,C), Or(A,D), Or(B,C), Or(B,D))
            if all([isinstance(child, And) for child in node.children]):
                res = []

                for c in left.children:
                    for d in right.children:
                        res.append(Or({c, d}))
                return And(res)

            # Either Or(And(A,B), C) or Or(C, And(A,B))
            # where C can be Var or Or
            elif any([isinstance(child, And) for child in node.children]):

                if isinstance(left, And):
                    clause1, clause2 = left.children
                    distributed_left = Or({distribute(clause1), distribute(right)})
                    distributed_right = Or({distribute(clause2), distribute(right)})

                    return And({distribute(distributed_left), distribute(distributed_right)})

                else:
                    clause1, clause2 = right.children
                    distributed_left = Or({distribute(clause1), distribute(left)})
                    distributed_right = Or({distribute(clause2), distribute(left)})

                    return And({distribute(distributed_left), distribute(distributed_right)})

            # Or(Or(A, B), Or(D, C))
            else:
                left, right = node.children
                return Or({distribute(left), distribute(right)})

def to_CNF(theory: NNF) -> And[Or[Var]]:

    def merge_cnf(left: NNF, right: NNF):
        
        res = []
        left_clauses = [left] if isinstance(left, Var) else [clause for clause in left.children]
        right_clauses = [right] if isinstance(right, Var) else [clause for clause in right.children]

        if len(left_clauses) > len(right_clauses):
            for index, clause in enumerate(left_clauses):
                res.append((clause, right_clauses[index % len(right_clauses)]))
        else:
            for index, clause in enumerate(right_clauses):
                res.append((clause, left_clauses[index % len(left_clauses)]))
        
        return And(res)


    def process_theory(node: NNF):

        if node.is_CNF():
            return node

        res = []

        if isinstance(node, Var):
            res.append(node)

        assert isinstance(node, Internal)

        if len(node.children) == 1:
            [child] = node.children
            res.append(process_node(child))
        
        else:

            left, right = node.children

            if isinstance(node, And):
                left_to_cnf = distribute(left)
                right_to_cnf = distribute(right)
                return And({left_to_cnf, right_to_cnf})
            
            elif isinstance(node, Or):
                left_to_cnf = distribute(left)
                right_to_cnf = distribute(right)
                return merge_cnf(left_to_cnf, right_to_cnf)

        return res

    res = process_theory(theory)
    NNF._is_CNF_loose.set(res, True)
    NNF._is_CNF_strict.set(res, True)
    return res