r"""
Python file for an implementation of Bareiss' algorithm

This module offers an implementation of Bareiss algorithm. Such algorithm computes the right nullspace of a matrix where its coefficients
belong to an Integral Domain. This algorithm is division-free.

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
from sage.all import (Matrix, Permutations, ideal, gcd, cached_method, vector, lcm, prod)
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isUniPolynomial
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing as isMPolynomial

# ajpastor imports
from ajpastor.misc.matrix import swap_rows
from ajpastor.misc.matrix import swap_cols
from ajpastor.misc.cached_property import derived_property

# Private variables for this module
_Permutations = Permutations()

# Main class of the file
class BareissAlgorithm(object):
    r'''
        This class represents the application of the Bareiss Algorithm over a matrix with polynomial coefficients.

        We use a class representation to allow the user to save all the information of the algorithm in one particular 
        object from which extract the information needed in the future. Hence, for using this class, the corresponding method
        and some other extra configuration parameters has to be given.

        Bareiss' algorithm is a division-free algorithm to compute a basis for a nullspace of a matrix over an integral domain. 
        The main idea from Bareiss algorithm is to perform some type of Gauss-Jordan elimination on the matrix but keeping track
        of necer divide and ensuring that, in the end, the main diagonal has the extra property that `d_{i+1,i+1}\ |\ d_{i,i}`.

        This implementation only works with polynomial coefficients, however we allow to provide a method that solves the 
        membership problem for the ideal `I = \{p(X) \in R[X]\ |\ p(X) = 0\}`. If such method is not provided, the algorithm work over
        the polynomials as no relation between the variables exist.

        INPUT:
            * ``parent``: the ring where the coefficients will be treated. It has to be a polynomial ring or its field of
              fractions.
            * ``M``: matrix with coefficients in ``parent``.
            * ``method``: method for the membership problem for the ideal `I`.
            * ``relations``: list of relation known for the variables of ``parent``. This, together with ``method`` is use to 
              check the membership to the ideal `I`.
    '''
    ### Initialization method
    def __init__(self, parent, M, method=None, relations = []):
        ## Checking the parent parameter
        if(parent.is_field()):
            parent = parent.base()
        if(not (isUniPolynomial(parent) or isMPolynomial(parent))):
            raise TypeError("The parent for this algorithm must be a polynomial ring.\n\t Got: %s" %parent)
        self.__parent = parent
            
        ## Checking the matrix input
        self.base_matrix = Matrix(self.parent(), M)
        
        self.change_of_columns = _Permutations(range(1 ,self.base_matrix.ncols()))
        
        ## Storing the checking method
        self.__in_ideal = method
        
        ## Cached elements
        self.__steps = None
        self.__actions = None
        self.__gb = ideal(self.parent(), relations).groebner_basis()
        self.__echelon = None
        
        
    ### Getter methods
    def parent(self):
        r'''
            Method to retrieve the ring for the coefficients of the algorithm.

            This method (very used in Sage for knowing the hierarchy of elements) returns the ring of polynomials where
            Bareiss' algorithm is working in this instance. It may differ to the ring provided by the argument ``parent``
            in the method :func:`__init__`.

            EXAMPLES::

                sage: from ajpastor.misc.bareiss import *
                sage: R.<a,b> = PolynomialRing(QQ)
                sage: M = Matrix([[a^2, b], [-b, 1]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.parent()
                Multivariate Polynomial Ring in a, b over Rational Field
                sage: BA = BareissAlgorithm(FractionField(R), M)
                sage: BA.parent()
                Multivariate Polynomial Ring in a, b over Rational Field
        '''
        return self.__parent
        
    #################################################
    ### Linear algebra methods
    #################################################
    def echelon_form(self):
        r'''
            Method to compute the right echelon form of the matrix.

            This method applies Bareiss' algorithm to compute the right-echelon form, i.e., a triangular matrix
            where the right-nullspace is the same as the original matrix and has zeros below the main diagonal.

            From this matrix it is extremely easy to compute a basis for the right-nullspace.

            REMARK:
                * This method caches the result to avoid recomputing the Bareiss' algorithm over the same matrix.

            EXAMPLE::

                sage: from ajpastor.misc.bareiss import *
                sage: R.<a,b> = PolynomialRing(QQ)
                sage: M = Matrix([[a^2, b], [-b, 1]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.echelon_form()
                [1 0]
                [0 1]
                sage: # Example where the matrix M is not invertible
                sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
                sage: BA.echelon_form()
                [-b 1]
                [ 0 0]
                sage: # Example where the matrix M is not square
                sage: M = Matrix([[a, b, a],[-b,a,-b]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.echelon_form()
                [1 0 1]
                [0 1 0]
                sage: # Example where M is not square and we have relations
                sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
                sage: BA.echelon_form()
                [a b a]
                [0 0 0]
                sage: # Another example with M not square
                sage: M = Matrix([[a,b],[-b,a],[a^3 - 3*b^4, 1+b^5]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.echelon_form()
                [1 0]
                [0 1]
                [0 0]
        '''
        if(self.__echelon is None):
            self.__compute_echelon()
        return self.__echelon
        
    #@wverbose
    def __compute_echelon(self):
        r'''
            Private method that performs operations for the echelon form.

            This method is private and should never be called by the user. See method :func:`echelon_form`
            for a public usage of this method.

            This method computes the echelon form of the matrix given in this instance of Bareiss' algorithm
            and saves all the steps and the result for further use. These steps are retrievable by the method
            :func:`steps` and the final form with the method :func:`echelon_form`.

            This method is the main implementation of Bareiss's algorithm over the given matrix. For each iteration
            we look for a feasable pivot in the current row ensuring the elements are not in the zero ideal 
            defined with the method provided.

            In the end, we break the assumptions of Bareiss performing an extra simplification in each row independently:
            we compute the gcd of each row and divide such row by it. With these, we end up with a simpler echelon
            form but the assumption on the main diagonal is no longer valid.
        '''
        self.__actions = [("base")]
        self.__steps = [self.base_matrix]
        
        ## If we have initial relations, we perform the first reduction
        if(self.__have_ideal()):
            #Initial reduction of the matrix
            self.__steps += [self.__simplify_matrix(self.__steps[-1])]
            self.__actions += [("f_reduce", self.__gb)]
        
        tr = self.__steps[-1 ].nrows()
        tc = self.__steps[-1].ncols()
        cr = 0
        cc = 0
        i = -1 
        
        # Starting the iterations
        while(i < min(tr,tc)):
            i = i + 1 
            
            pivot = self.__choose_pivot(self.__steps[-1], i,i)
            
            cr,cc = pivot[0]
            new_rels = pivot[2]
            
            ## If there are new relations, we simplify the matrix
            if(len(new_rels) > 0):
                # New relations found looking for a pivot
                self.__gb = ideal(self.parent(), tuple(new_rels) + tuple(self.__gb)).groebner_basis()
                self.__steps += [self.__simplify_matrix(self.__steps[-1])]
                self.__actions += [("reduce", new_rels)]
                    
            ## If no pivot was found, we finish
            if(cr == -1 or cc == -1):
                # No pivot found. Finishing the iterations
                break
                    
            ## If we have a new pivot, we moved everythin so it is in the proper position
            swap_actions = pivot[1]
            for action in swap_actions:
                if(action[0] == "sw_r"):
                    self.__steps += [swap_rows(self.__steps[-1], action[1],action[2])]
                elif(action[0] == "sw_c"):
                    self.__steps += [swap_cols(self.__steps[-1], action[1], action[2])]
                    self.change_of_columns = _Permutations((action[1]+1, action[2]+1))*self.change_of_columns
                    
                self.__actions += [action]
                
            ## One the pivot is in position, we proceed with the Bareiss elimination
            # M = self.__steps[-1]
            
                
            ## We save the new matrix and go on
            self.__steps += [self.__bareiss(self.__steps[-1], i)]
            self.__actions += [("bareiss", i)]
            
        # Simplifying each row with its GCD.
        gcds = [gcd(row) for row in self.__steps[-1]]
        for i in range(len(gcds)):
            if(gcds[i] == 0 ):
                gcds[i] = 1
        self.__steps += [Matrix(self.parent(), [[el/gcds[i] for el in self.__steps[-1][i]] for i in range(self.__steps[-1].nrows())])]
        self.__actions += [("gcd_simpl")]
            
        # Saving the final echelon form
        self.__echelon = self.__steps[-1]
                                
        return
        
    @cached_method
    def rank(self):
        r'''
            Method to compute the rank of the given matrix

            This method uses the echelon form from Bareiss algorithm to compute the 
            rank of the matrix for this instance of the algorithm. 

            After computing an echelon form, the rank is the number of non-zero rows that
            remains. Since the rows are ordered, which means that all zero rows are in the end of
            the echelon form, we can just look for the firts zero row.

            EXAMPLE::

                sage: from ajpastor.misc.bareiss import *
                sage: R.<a,b> = PolynomialRing(QQ)
                sage: M = Matrix([[a^2, b], [-b, 1]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.rank()
                2
                sage: # Example where the matrix M is not invertible
                sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
                sage: BA.rank()
                1
                sage: # Example where the matrix M is not square
                sage: M = Matrix([[a, b, a],[-b,a,-b]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.rank()
                2
                sage: # Example where M is not square and we have relations
                sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
                sage: BA.rank()
                1
                sage: # Another example with M not square
                sage: M = Matrix([[a,b],[-b,a],[a^3 - 3*b^4, 1+b^5]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.rank()
                2
        '''
        for i in range(self.base_matrix.nrows()):
            if(any((el != 0 ) for el in self.echelon_form()[-(i+1 )])):
                return self.base_matrix.nrows()-i


    def relations(self):
        r'''
            Method to get the realtions between the variables found in the matrix.

            A relation is a polynomial `p` in ``self.parent()`` such that ``self.is_in_ideal(p)`` is ``True``.
            See method :func:`is_in_ideal` for further information.

            This method just return the found relations while computing the echelon form of the Matrix
            using Bareiss' algorithm. These relations are returned in the form of a Groebner basis. Hence,
            if no relations are found, the result is the zero ideal: ``[0]``

            WARNING: It is important to remark that this method does not return the basis
            of the ideal that ``self.is_in_ideal()`` defines. This is because only found relations
            are taking into account at this step.

            EXAMPLE::

                sage: from ajpastor.misc.bareiss import *
                sage: R.<a,b> = PolynomialRing(QQ)
                sage: M = Matrix([[a^2, b], [-b, 1]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.relations()
                [0]
                sage: # Example where the matrix M is not invertible
                sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
                sage: BA.relations()
                [a^2 + b^2]
                sage: # Example where the matrix M is not square
                sage: M = Matrix([[a, b, a],[-b,a,-b]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.relations()
                [0]
                sage: # Example where M is not square and we have relations
                sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
                sage: BA.relations()
                [a^2 + b^2]
                sage: # Another example with M not square
                sage: M = Matrix([[a,b],[-b,a],[a^3 - 3*b^4, 1+b^5]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.relations()
                [0]

            This method also can improve the relations given at inizialization::

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
                [-1 0 -1]
                [ 0 1  0]
                [ 0 0  0]
                sage: BA.relations()
                [a^2 + b^2]
        '''
        # Compute the echelon form and the relations with it
        self.echelon_form()
        # Returning the relations
        return self.__gb
                
    @cached_method
    def right_kernel_matrix(self):
        r'''
            Method to compute the right kernel matrix of self.base_matrix.

            This method computes the echelon form of the matrix and then starts a
            simple computation to clean denominator and obtain a basis formed with 
            elements of the integral domain self.parent().

            After performing Bareiss algorithm we have the echelon form for the 
            instance matrix `M`. This echelon form has been built after some swapping
            of columns of `M` and some linear combinations of its rows. And the shape of 
            this echelon form is:

            .. MATH::

                \left(\begin{array}{ccccc}
                    d_{11} & 0 & 0 & \ldots & 0 & d_{1,m+1} & \ldots & d_{1n} \\
                    0 & d_{22} & 0 & \ldots & 0 & d_{2,m+1} & \ldots & d_{2n} \\
                    \vdots & \vdots & \vdots & \ddots & \vdots & \vdots & \ddots & \vdots \\
                    0 & 0 & 0 & \ldots & d_{mm} & d_{m,m+1} & \ldots & d_{mn} \\
                    0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\\
                    \vdots & \vdots & \vdots & \ddots & \vdots & \vdots & \ddots & \vdots \\
                \end{array}\right)

            Which is, a triagular matrix where the first `m\times m` matrix is diagonal and all the 
            elements in the rows `m+1`, `m+2`, etc. are zero. In this case, `m` is the rank of 
            the original matrix.

            Starting from this echelon form, the nullspace is easy to compute via basic linear algebra.
            Let `d = lcm(d_11,\ldots,d_mm)` and `D_i = d/d_{ii}`. Then we have that the following vectors 
            are on the nullspace:

            .. MATH::
                
                \begin{array}{c}
                    (d_{1,m+1}D_1, d_{2,m+1}D_2, \ldots, d_{m,m+1}D_m, d, 0, \ldots, 0)\\
                    (d_{1,m+2}D_1, d_{2,m+2}D_2, \ldots, d_{m,m+2}D_m, 0, d, \ldots, 0)\\
                    \vdots\\
                    (d_{1,n}D_1, d_{2,n}D_2, \ldots, d_{m,n}D_m, 0, 0, \ldots, d)
                \end{array}

            And, due to the structure of the last coordinates, these verctors are linearly independent. Hence
            they form a base of the nullspace and all their coordinates are elements on the integral domain.

            This method a list with the vectors we have just described.

            EXAMPLE::

                sage: from ajpastor.misc.bareiss import *
                sage: R.<a,b> = PolynomialRing(QQ)
                sage: M = Matrix([[a^2, b], [-b, 1]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.right_kernel_matrix()
                [(0, 0)]
                sage: # Example where the matrix M is not invertible
                sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
                sage: BA.right_kernel_matrix()
                [(-1, -b)]
                sage: # Example where the matrix M is not square
                sage: M = Matrix([[a, b, a],[-b,a,-b]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.right_kernel_matrix()
                [(-1, 0, 1)]
                sage: # Example where M is not square and we have relations
                sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0)
                sage: BA.right_kernel_matrix()
                [(-b, a, 0), (-a, 0, a)]
                sage: # Another example with M not square
                sage: M = Matrix([[a,b],[-b,a],[a^3 - 3*b^4, 1+b^5]])
                sage: BA = BareissAlgorithm(R, M)
                sage: BA.right_kernel_matrix()
                [(0, 0)]
                sage: M = Matrix([[a^2, b^2+2*a^2,b],[-b^2, a^2, 3],[1, 1, 1]])
                sage: BA = BareissAlgorithm(R, M, relations=[a^4 + 2*a^2*b^2 + b^4])
                sage: BA.right_kernel_matrix()
                [(0, 0, 0)]
                sage: BA = BareissAlgorithm(R, M, lambda p : p.reduce([a^2+b^2]) == 0, [a^4 + 2*a^2*b^2 + b^4])
                sage: BA.right_kernel_matrix()
                [(1, -1, 0)]
        '''
        sol_dimension = self.base_matrix.ncols()-self.rank()        
        M = self.echelon_form()
        
        if(sol_dimension > 0 ):
            ## Compute the product of the nice diagonal
            A = self.__get_lcm([M[i][i] for i in range(self.rank())])
            to_mult = [-A/M[i][i] for i in range(self.rank())]
        
            ker_basis = [vector(self.parent(), [to_mult[j]*M[j][i+self.rank()] for j in range(self.rank())] + [0  for j in range(i)] + [A] + [0  for j in range(i+1 , sol_dimension)]) for i in range(sol_dimension)]
            
            ch = self.change_of_columns
            ## If there were a change of columns (i.e. ch is not the trivial permutation) 
            ## we swap the result
            if(_Permutations(range(1 ,self.base_matrix.ncols())) != ch):
                ch = ch.inverse()
                rows = [[0  for i in range(M.ncols())] for j in range(len(ker_basis))]
                for j in range(M.ncols()):
                    new_col = ch(j+1 )-1
                    for i in range(len(ker_basis)):
                        rows[i][new_col] = ker_basis[i][j]
                
                ker_basis = [vector(self.parent(), row) for row in rows]           
            
            return ker_basis
        else:
            return [vector(self.parent(), [0  for i in range(M.ncols())])]
        
    #################################################
    ### Other cached methods
    #################################################
    @cached_method
    def is_in_ideal(self, p):
        r'''
            Method that defines the ideal over this algorithm is working on.

            This method is a boolean method (returns ``True`` or ``False``) in such a way that
            ``I = {g in self.parent() : self.is_in_ideal(g) == True}`` is an ideal
            of self.parent().
        '''
        p = self.parent()(p)
        
        try:
            return self.__in_ideal(p) is True
        except Exception:
            return False
          
    @cached_method
    def steps(self):
        r'''
            Method to see the details of Bareiss algorithm.

            This method returns a fully detailled exmplanation of the steps we performed for computing
            the echelon form of the given matrix using Bareiss' algorithm. This information is intended for
            reproduce the operations of the algorithm by the user and check the result of the echelon
            form is correct.

            OUTPUT:
                
            This method returns a list of touples containing:
                * The matrix after this step
                * The action corresponding to the current step. These are touples containing a name (or type 
                  of operation) and the arguments required for performing such operation. There is a limited 
                  number of posible steps:
                    * ``reduce`` or ``f_reduce``: reduce all entries of the matrix using the found relations.
                    * ``bareiss``: perform a Bareiss reduction step on the given index.
                    * ``sw_c`` or ``sw_r``: swap the two given columns (or rows, respectively).
                    * ``gcd_simpl``: simplifies the gcd on each row of the matrix.
                    * ``base``: the original matrix. This is always the first step. 

            WARNING:

            Due to long and unstructured outputs for this method, no tests are provided for it.
        '''
        self.echelon_form()
        
        return [(self.__steps[i],self.__actions[i]) for i in range(len(self.__steps))]
        
    #################################################
    ### Private methods for Bareiss Algorithm 
    #################################################
    def __choose_pivot(self, M, ir, ic):
        r'''
            Method for choosing a valid pivot on a Matrix for Bareiss reduction.

            This method computes the next pivot element for the algorithm and returns the information 
            to prepare the matrix for the next step. The ``ir`` and ``ic`` are parameters to begin the 
            search from the position `(ir,ic)`.

            A valid pivot is any element on the matrix with position strictly greater than `(ir,ic)`
            (i.e., both coordinates must be greater or equal to those) and must not be in the
            ideal defined by ``self.is_in_ideal()``.

            INPUT:
                - ``M``: the current matrix we are choosing the pivot.
                - ``ir``: initial index for the rows.
                - ``ic``: initial index fot the columns.
            OUTPUT:

            This method returns a tuple of 4 elements:
                * A pair `(fr,fc)` for the position of the chosen pivot. `(-1,-1)` means no pivot 
                  was found.
                * A tuple of actions to transform `M` in order to put the pivot in the appropriate 
                  position.
                * A set of new relations found during this pivot chosing.
        '''
        relations = set()
        actions = []
        end = False
        fc = -1 ; fr = -1 
        ## Checking rows
        for cc in range(ic, M.ncols()):
            ## Checking columns
            for cr in range(ir, M.nrows()):
                # Checking if position (cr,cc) is in the ideal
                to_check = M[cr][cc]
                if(len(relations) > 0 ):
                    # Reducing the selected element with the found relations
                    to_check = M[cr][cc].reduce(relations)
                    
                if(not to_check == self.parent().zero()):
                    if(not self.is_in_ideal(to_check)):
                        # Non-zero element found --> Valid pivot
                        end = True
                        fr = cr
                        break
                    else:
                        # Non trivial zero found --> New relation
                        relations.add(to_check)
            
            if(end):
                fc = cc
                break
        
        if(fc != -1  and fc != ic):
            actions += [("sw_c", ic, cc)]
            for i in range(1 ,(min(cc-ic, M.ncols()-cc))):
                actions += [("sw_c", ic+i, M.ncols()-i)]
        
        if(fr != -1  and fr != ir):
            actions += [("sw_r", ir, cr)]
                
        return ((fr,fc), tuple(actions), relations)
        
    def __bareiss(self, M, i):
        r'''
            Method to perform a Bareiss reduction step.

            Method that applies a Bareiss reduction to the matrix `M` on the position `(i,i)`.
            This method assumes that ``M[i][i]`` is a valid pivot for this reduction.

            The output matrix will preserve the structure of M for positions (j,k) with 
            j,k < i and will create zeros on the i-th column. A final reduction with gcds 
            for each column is performed to keep the degrees of the polynomials as small as 
            possible.

            These computations are not in-place, so the resulting matrix needs more
            memory allocation to be computed.

            INPUT:
                - ``M``: matrix where we want perform the Bareiss reduction.
                - ``i``: position where we have a pivot.
        '''
        rows = []
        ## Reduction of the rows before i
        for j in range(i):
            if(M[j][i] != 0 ):
                rows += [[M[j][k]*M[i][i]-M[j][i]*M[i][k] for k in range(M.ncols())]]
            else:
                rows += [[M[j][k] for k in range(M.ncols())]]

        ## The i-th row remains the same as before
        rows += [[M[i][k] for k in range(M.ncols())]]

        ## Reduction of the rows after i
        for j in range(i+1 , M.nrows()):
            if(M[j][i] != 0 ):
                rows += [[M[j][k]*M[i][i]-M[j][i]*M[i][k] for k in range(M.ncols())]]
            else:
                rows += [[M[j][k] for k in range(M.ncols())]]
        
        ## GCD simplification of the rows
        try:
            gcds = [gcd(row) for row in rows]
            rows = [[el/gcds[i] for el in rows[i]] for i in range(len(rows))]
        except Exception:
            pass
            
        return Matrix(self.parent(), rows)
        
    def __have_ideal(self):
        r'''
            Auxiliar method to know if some relation have been already found.

            This method returns ``True`` if the current Groebner basis we have computed
            gives some non-trivial ideal.
        '''
        if(len(self.__gb) == 1):
            return self.__gb[0] != 0
        return len(self.__gb) > 0
        
    def __simplify_matrix(self, M):
        r'''
            Method to simplify a polynomial matrix using the relations found.

            This methods use the Sage implementation of the method ``reduce`` on polynomials
            to simplify a matrix ``M`` using the relations that have been found so far during 
            the Bareiss' algorithm.

            This method unifies the way to perform such reduction taking care of iterate through 
            the elements of `M` and to check that there are relations to use.
        '''
        rows = [[el for el in row] for row in M]
        if(self.__have_ideal()):
            rows = [[el.reduce(self.__gb) for el in row] for row in rows]
        
        return Matrix(self.parent(), rows)
        
    def __get_lcm(self, input):
        r'''
            Auxiliar method for computing the lcm of a sequence.

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
        
        

