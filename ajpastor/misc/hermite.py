r"""
Python file for an implementation of Bareiss' algorithm

This module offers an implementation of Hermite Normal Form computation. This algorithm can later be used to
solve linear system within Euclidean domains.

This is an adaptation of method described in https://www.ams.org/journals/mcom/1996-65-216/S0025-5718-96-00766-1/
for computing the Hermite Normal Form in Dedekind domains. Since Euclidean Domains are, in particular, Dedekind
domains, we use the corresponding and adapted method.

The main differences with the algorithm described in that paper is that we do a row echelon form and 
that we do not force the diagonal to have 1. Moreover, we do not need to have maximal rank, obtaining zero
rows in the end of the matrix.

Given a matrix `M` with `n` rows and `m` columns, a Hermite normal form (or HNF) is a matrix `H` equivalent
to `M` (i.e., there is a unimodular matrix `U` such that `UM = H`, also called *transformation matrix*)
such that every element below the main diagonal is zero. This is similar to computing the echelon
form as in a Gauss-Jordan elimination, but all operations stays in the same ring as the elements of 
`M` belong (given that it is an Euclidean domain).

AUTHORS:

    - Antonio Jimenez-Pastor (2021-02-08): initial version

"""

# ****************************************************************************
#  Copyright (C) 2021 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.all import identity_matrix, Matrix, vector, xgcd

from ajpastor.misc.linear_solver import LinearSystemSolver, NoSolutionError

class HermiteSolver(LinearSystemSolver):
    r'''
        This class represents the solving of a linear system using Hermite Normal Forms.

        Solving a linear system using Hermite normal forms is possible by solving each of the equations
        and extending the result to the rest of the system. This can be done in every Euclidean Domain.

        This algorithm is based on the Euclidean division algorithm and work anywhere where the elements
        of the parent structure have the methods ``__div__``, ``__rem__`` and ``xgcd``.

        INPUT:
            * ``parent``: the ring where the solutions will be searched. This parent can be a localization 
              ring that can be provided as a triplet ``(R, g, d)`` where ``R`` is a euclidean domain, ``g``
              is an empty list and ``d`` is a list of elements on ``R`` that will be localized.
            * ``matrix``: matrix for the system.
            * ``inhomogeneous``: the inhomogeneous vector for the system.
            * ``euclidean``: method for computing the euclidean division with remainder.
            * ``xgcd``: method for computing the Extended Euclidean GCD.

        TODO:
            * Add tests
    '''
    def __init__(self, parent, matrix, inhomogeneous, euclidean=lambda p,q: (p//q, p%q), xgcd = lambda p,q : xgcd(p,q)):
        if(type(parent) is tuple):
            base,g,d = parent
            if(not base.is_euclidean_domain()):
                raise TypeError("The base ring for Hermite must be euclidean")
            if(len(g) > 0):
                raise TypeError("The base ring for Hermite must not have generators")
            parent = base.localization(tuple(d))
            def new_euclidean(p,q):
                pn = p.numerator(); pd = p.denominator()
                qn = q.numerator(); qd = q.denominator()
                d, r = euclidean(pn, qn)
                return (parent((d*qd)/pd), parent(r/pd))
            
            def new_xgcd(p,q):
                if(q == 0):
                    return p, parent.one(), parent.zero()
                aux_den,_,_ = xgcd(p.denominator(),q.denominator())
                p *= aux_den; q *= aux_den
                if(p.denominator() == 1 and q.denominator() == 1):
                    g,P,Q = xgcd(p.numerator(),q.numerator())
                    return g, aux_den*parent(P), aux_den*parent(Q)
                m,r = new_euclidean(p,q)
                if(self.is_zero(r)):
                    return q, parent.zero(), parent.one()
                if(r.is_unit()):
                    return parent.one(), aux_den*parent(1/r), aux_den*parent(-m/r)
                g, P, Q = new_xgcd(q,r)
                return (g, aux_den*Q, aux_den*(P-m*Q))

            self.__euclidean = new_euclidean
            self.__xgcd = new_xgcd
        else:
            self.__euclidean = euclidean
            self.__xgcd = xgcd

        super().__init__(parent, matrix, inhomogeneous)

    def _compute_echelon(self):
        A = Matrix(self.solution_parent(), self.A.rows()) # we create a copy
        U = identity_matrix(self.solution_parent(), A.nrows())
        ## Step 1: initialize
        r = 0; c = 0 # we are looking from (r,c)
        while(r < A.nrows() and c < A.ncols()):
            ir = self.__find_pivot(A, r,c)
            if(ir != None): # we found a pivot
                if(ir != r): # swapping rows
                    A.swap_rows(r, ir); U.swap_rows(r,ir)
                
                # We reduce in each row
                for m in range(r+1, A.nrows()):
                    if(A[m][c] != 0):
                        g, t, s = self.__xgcd(A[r][c], A[m][c])
                        p,_ = self.__euclidean(A[r][c],g); q,_ = self.__euclidean(A[m][c],g)

                        Ar = A.row(r); Am = A.row(m)
                        Ur = U.row(r); Um = U.row(m)

                        A.set_row(r,t*Ar + s*Am); U.set_row(r,t*Ur + s*Um)
                        A.set_row(m,q*Ar - p*Am); U.set_row(m,q*Ur - p*Um)
                r += 1
            c+= 1
        return A, U

    def _compute_solution(self):
        
        A = self.echelon_form()
        b = self.transformation_matrix()*self.inhomogeneous().change_ring(self.solution_parent())

        ## We compute the solution equation by equation
        r = A.nrows()-1
        while(all(self.is_zero(el) for el in A[r])):
            r-=1
        ## A.row(r) is the first real equation
        solution = vector(self.solution_parent(), self.A.ncols()*[0])
        syzygy = identity_matrix(self.solution_parent(), self.A.ncols())
        while(r >= 0):
            M = Matrix(self.solution_parent(),[A.row(r)]).transpose()
            hs = HermiteSolver(self.solution_parent(), M, vector([b[r]]), self.__euclidean, self.__xgcd)
            ## We check the condition for having a solution
            g = hs.echelon_form()[0][0]
            quo,rem = self.__euclidean(b[r],g)
            if(rem != 0):
                raise NoSolutionError("There is no solution to equation %s = %s" %(M.tranpose(), b[r]))
            
            U = hs.transformation_matrix()
            ## Solution to the particular equation (alpha + S*beta)
            alpha = quo*U.row(0)
            S = Matrix(self.solution_parent(), U.rows()[1:]).transpose()
            ##Update the general values
            solution += syzygy*alpha
            syzygy *= S

            ## Update the system
            b -= A*alpha
            A *= S

            # We update the index of the equation
            while(r >= 0 and all(self.is_zero(el) for el in A[r])):
                r-=1
        return solution, syzygy
    
    #########################################################
    ###
    ### Private method
    ###
    #########################################################
    def __find_pivot(self, A, r, c):
        r'''
            Method to find the next valid pivot.

            TODO:
                * Fill documentation
                * Add example
        '''
        for i in range(r, A.nrows()):
            if(not self.is_zero(A[i][c])):
                return i
        return None
