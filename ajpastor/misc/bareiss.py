r"""
Python file for an implementation of Bareiss' algorithm

This module offers an implementation of Bareiss algorithm (https://www.ams.org/journals/mcom/1968-22-103/S0025-5718-1968-0226829-0/).
Such algorithm computes (fraction-free) an echelon form of a matrix whose coefficients are in an integral domain. 

AUTHORS:

    - Antonio Jimenez-Pastor (2016-10-01): initial version

"""

# ****************************************************************************
#  Copyright (C) 2019 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

# Sage imports
from sage.all import (Matrix, gcd, vector, lcm, prod,
                        identity_matrix, diagonal_matrix)
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isUniPolynomial
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing as isMPolynomial

# ajpastor imports
from ajpastor.misc.linear_solver import LinearSystemSolver

# Main class of the file
class BareissAlgorithm(LinearSystemSolver):
    r'''
        This class represents the application of the Bareiss' algorithm over a matrix with polynomial coefficients.

        Bareiss' algorithm is a division-free algorithm to compute an echelon form of a matrix over an integral domain. 
        The main idea from Bareiss algorithm is to perform some type of Gauss-Jordan elimination on the matrix but keeping track
        that we never get denominators and ensuring that, in the end, the main diagonal has the extra property that `d_{i+1,i+1}\ |\ d_{i,i}`.

        This implementation only works with polynomial coefficients, however we allow to provide a method that solves the 
        membership problem for the ideal `I = \{p(X) \in R[X]\ |\ p(X) = 0\}`. If such method is not provided, the algorithm work over
        the polynomials as no relation between the variables exist.

        This algorithm allows to solve homogeneous system (no inhomogeneous term is allowed).

        INPUT:
            * ``parent``: the ring where the coefficients will be treated. It has to be a polynomial ring or its field of
              fractions.
            * ``matrix``: matrix for the homogeneous system.
            * ``method``: method for the membership problem for the ideal `I`.
            * ``relations``: list of relation known for the variables of ``parent``. This, together with ``method`` is use to 
              check the membership to the ideal `I`.

        EXAMPLES::

            sage: from ajpastor.misc.bareiss import *
            sage: R.<a,b> = PolynomialRing(QQ)
            sage: M = Matrix([[a^2, b], [-b, 1]])
            sage: BA = BareissAlgorithm(R, M)
            sage: BA.parent()
            Multivariate Polynomial Ring in a, b over Rational Field
            sage: BA.echelon_form()
            [1 0]
            [0 1]
            sage: BA.rank()
            2
            sage: BA = BareissAlgorithm(FractionField(R), M)
            sage: BA.parent()
            Multivariate Polynomial Ring in a, b over Rational Field
        
        We can see how the relations involved on the coefficients are important::

            sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
            sage: BA.echelon_form()
            [-b 1]
            [ 0 0]
            sage: BA.rank()
            1

        This class also works with non-square matrices::

            sage: M = Matrix([[a, b, a],[-b,a,-b]])
            sage: BA = BareissAlgorithm(R, M)
            sage: BA.echelon_form()
            [-1  0 -1]
            [ 0  1  0]
            sage: BA.rank()
            2
            sage: BA.syzygy()
            [ 1]
            [ 0]
            [-1]
            sage: # Example where M is not square and we have relations
            sage: BA = BareissAlgorithm(R, M, relations=[a^2+b^2])
            sage: BA.echelon_form()
            [a b a]
            [0 0 0]
            sage: BA.rank()
            1
            sage: BA.syzygy()
            [-b -a]
            [ a  0]
            [ 0  a]
            sage: # Another example with M being non-square
            sage: M = Matrix([[a,b],[-b,a],[a^3 - 3*b^4, 1+b^5]])
            sage: BA = BareissAlgorithm(R, M)
            sage: BA.echelon_form()
            [1 0]
            [0 1]
            [0 0]
            sage: BA.rank()
            2

        This algorithm can find the relations on the fly thanks to the input ``is_zero``::

            sage: M = Matrix([[a, b, a],[-b,a,-b]])
            sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
            sage: BA.relations()
            [0]
            sage: H = BA.echelon_form()
            sage: BA.relations()
            [a^2 + b^2]

        The algorithm can improve the given relations on the fly::

            sage: M = Matrix([[a^2, b^2+2*a^2,b],[-b^2, a^2, 3],[1, 1, 1]])
            sage: BA = BareissAlgorithm(R, M, relations=[a^4 + 2*a^2*b^2 + b^4])
            sage: BA.echelon_form()
            [1 0 0]
            [0 1 0]
            [0 0 1]
            sage: BA.relations()
            [a^4 + 2*a^2*b^2 + b^4]
            sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0, [a^4 + 2*a^2*b^2 + b^4])
            sage: BA.echelon_form()
            [1 1 0]
            [0 0 1]
            [0 0 0]
            sage: BA.relations()
            [a^2 + b^2]
    '''
    ### Initialization method
    def __init__(self, parent, matrix, is_zero=lambda p : False, relations = []):
        ## Checking the parent parameter
        if(parent.is_field()):
            parent = parent.base()
        if(not (isUniPolynomial(parent) or isMPolynomial(parent))):
            raise TypeError("The parent for this algorithm must be a polynomial ring.\n\t Got: %s" %parent)

        ## Checking the matrix input
        matrix = Matrix(parent, matrix)
        super().__init__(parent, matrix, vector(parent, matrix.ncols()*[0]), is_zero, relations)
                
    #################################################
    ### Linear algebra methods
    #################################################
    def _compute_echelon(self):
        A = Matrix(self.parent(), self.A.rows()) # we create a copy of the matrix
        U = identity_matrix(self.parent(), A.nrows())

        if(self.have_ideal): # we do simplifications
            A = self.simplify(A)

        ## Step 1: initialize
        r = 0; c = 0 # we look from the position (r,c)
        while(r < A.nrows() and c < A.ncols()):
            ir = self.__find_pivot(A, r, c)
            A = self.simplify(A); U = self.simplify(U) # we simplify in case relations pop up
            
            if(ir != None): # we found a pivot
                # We do the swapping (if needed)
                if(ir != r):
                    A.swap_rows(r, ir); U.swap_rows(r, ir)

                # We do the bareiss step
                Arc = A[r][c]
                Arows = A.rows(); Urows = U.rows()
                for i in range(r): # we create zeros on top of the pivot
                    Aic = A[i][c]
                    A.set_row(i, Arc*Arows[i] - Aic*Arows[r]); U.set_row(i, Arc*Urows[i] - Aic*Urows[r])

                # We then leave the row r without change
                for i in range(r+1, A.nrows()): # we create zeros below the pivot
                    Aic = A[i][c]
                    A.set_row(i, Aic*Arows[r] - Arc*Arows[i]); U.set_row(i, Aic*Urows[r] - Arc*Urows[i])
                
                r +=1; c+=1

            else: # no pivot then only advance in column
                c+=1

        # We finish simplifying the gcds in each row
        gcds = [gcd(row) for row in A]
        T = diagonal_matrix([1/el if el != 0 else 1 for el in gcds])
        A = (T*A).change_ring(self.parent()); U = T*U
        return A, U

    def _compute_solution(self):
        H = self.echelon_form()
        ker_vectors = []
        cpivots = [min([j for j in range(H.ncols()) if H[i][j] != 0]) for i in range(self.rank())] + [H.ncols()]
        for i in range(self.rank()):
            LCM = self.__get_lcm([H[j][cpivots[j]] for j in range(i+1)])
            to_mult = [self.parent()(-LCM/H[j][cpivots[j]]) for j in range(i+1)]
            for c in range(cpivots[i]+1, cpivots[i+1]):
                new_vector = []
                for k in range(H.ncols()):
                    if(k < c and k in cpivots):
                        index_pivot = cpivots.index(k)
                        new_vector += [to_mult[index_pivot]*H[index_pivot][c]]
                    elif(k == c):
                        new_vector += [LCM]
                    else:
                        new_vector += [0]
                ker_vectors += [new_vector]

        return vector(self.parent(), H.ncols()*[0]), Matrix(self.parent(), ker_vectors).transpose()
                
        
    #################################################
    ### Private methods for Bareiss Algorithm 
    #################################################
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
        
        
    def __get_lcm(self, input):
        r'''
            Auxiliary method for computing the lcm of a sequence.

            Private method for computing a common multiple of a sequence given in ``input``.
            This method relies on the Sage implementation of ``lcm`` and, if this fails tries
            to compute a least common multiple using the GCD of the sequence:

            .. MATH::

                lcm(a_1,\ldots,a_n) = \frac{a_1 \cdots a_n}{gcd(a_1,\ldots,a_n)}.

            In case the computation of the gcd fails again, we just return the product of all
            the elements of the input.
        '''
        try:
            return lcm(input)
        except AttributeError:
            ## No lcm for this class, implementing a general lcm
            try:
                ## Relying on gcd
                p = self.__parent
                res = p(1 )
                for el in input:
                    res = p((res*el)/gcd(res,el))
                return res
            except AttributeError:
                ## Returning the product of everything
                return prod(input)
        
        

