r"""
Python file for TwoSteps Operators

This module offers an abstract class of linear differential operators which its linear algebra operations
are performed in two different steps: 
* Computing a matrix
* Getting an element of its nullspace.

EXAMPLES::
    sage: from ajpastor.operator.twoStepsOperator import *

TODO::
    * Complete the Examples section of this documentation
    * Document the package
    * Review the functionality of the package

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
from sage.all import (Matrix, vector)

####################################################################################################
####################################################################################################
###
### TwoStepsOperator module
###
### ------------------------------------------------------------------------------------------------
###
### This file contains an abstract extension of a ListOperator that add the structure for different algorithms fro computing the solution methods of operators
###
### ------------------------------------------------------------------------------------------------
###
### Version: 0.0
### Date of begining: 05-05-2017
###
### Updated (21-08-2017)
###     - Changed name parent to base
###
###
### ------------------------------------------------------------------------------------------------
### Dependencies:
###     - ListOperator class
####################################################################################################
####################################################################################################

#sage imports
from sage.all import cached_method, lcm

# Local imports
from .listOperator import ListOperator
from .operator import foo_derivative

class TwoStepsOperator(ListOperator):

    #######################################################
    ### INIT METHOD AND GETTERS
    #######################################################
    def __init__(self, base, input, derivate = foo_derivative):
        super(TwoStepsOperator, self).__init__(base, input, derivate)
            
    ####################################################### 
    
    ####################################################### 
    ### SOLUTION ARITHMETHIC METHODS (ABSTRACT)
    ####################################################### 
    def _compute_add_solution(self, other):
        M = self._get_system_addition(other, self.order()+other.order()+1, False)
        v = self._get_element_nullspace(M)
        
        return self.__class__(self.base(), [el for el in v], self.derivate())
        
    def _compute_mult_solution(self, other):
        M = self._get_system_product(other,self.order()*other.order()+1, False)
        v = self._get_element_nullspace(M)
        
        return self.__class__(self.base(), [el for el in v], self.derivate())
        
    def _compute_compose_solution(self, other):
        M = self._get_matrix_composition(other)
        v = self._get_element_nullspace(M)
        
        return self.__class__(self.base(), [el for el in v], self.derivate())
    ####################################################### 

    ####################################################### 
    ### SOLUTION SIMPLE ARITHMETHIC METHODS (ABSTRACT)
    ####################################################### 
    def _compute_simple_add_solution(self, other, S=None, bound=5):
        ## Checking the set S
        ring = self.noetherian_ring(other)
        S_aux = ring[2]
        if(not S is None): ## Checking that the required denominators are in S
            if(type(S) in (list, tuple, set)):
                S = [ring[0](el) for el in S]
                S = [el for el in S if (not el.is_unit())] # removing units (we can divide already)
                for el in S_aux:
                    element = el; i = 0
                    while(not element.is_unit()):
                        while(S[i].divides(element)):
                            element = element // S[i]
                        i+=1
                    if(not element.is_unit()):
                        raise ValueError("The set %s does not cover the minimal elements for this simple operation")
                ring = (ring[0],ring[1],S)
            else:
                raise NotImplementedError("Multiplicative closed set defined via %s is not implemented" %type(S))

        ## Performing the computations
        order = self.order()+other.order(); i = 0
        solution = None
        while((solution is None) and (i < bound)):
            A,b = self._get_system_addition(other, order+i, True)
            try:
                solution = self._solve_linear_system(A,b,ring)
                den_lcm = lcm([el.denominator() for el in solution])
                solution = [(-el.numerator()*den_lcm)//el.denominator() for el in solution]
            except ValueError: # No solution to the system
                i += 1
                
        return self.__class__(self.base(), solution + [den_lcm], self.derivate())
        
    def _compute_simple_mult_solution(self, other, S=None, bound = 5):
        ## Checking the set S
        ring = self.noetherian_ring(other)
        S_aux = ring[2]
        if(not S is None): ## Checking that the required denominators are in S
            if(type(S) in (list, tuple, set)):
                S = [ring[0](el) for el in S]
                S = [el for el in S if (not el.is_unit())] # removing units (we can divide already)
                for el in S_aux:
                    element = el; i = 0
                    while(not element.is_unit()):
                        while(S[i].divides(element)):
                            element = element // S[i]
                        i+=1
                    if(not element.is_unit()):
                        raise ValueError("The set %s does not cover the minimal elements for this simple operation")
                ring[2] = S
            else:
                raise NotImplementedError("Multiplicative closed set defined via %s is not implemented" %type(S))

        ## Performing the computations
        order = self.order()+other.order(); i = 0
        solution = None
        while((solution is None) and (i < bound)):
            A,b = self._get_system_product(other, order+i, True)
            try:
                solution = self._solve_linear_system(A,b,ring)
                den_lcm = lcm([el.denominator() for el in solution])
                solution = [(-el.numerator()*den_lcm)//el.denominator() for el in solution]
            except ValueError: # No solution to the system
                i += 1
                
        return self.__class__(self.base(), solution + [den_lcm], self.derivate())
        
    def _compute_simple_derivative_solution(self, S=None, bound = 5):
        ## Checking the set S
        ring = self.noetherian_ring()
        S_aux = ring[2]
        if(not S is None): ## Checking that the required denominators are in S
            if(type(S) in (list, tuple, set)):
                S = [ring[0](el) for el in S]
                S = [el for el in S if (not el.is_unit())] # removing units (we can divide already)
                for el in S_aux:
                    element = el; i = 0
                    while(not element.is_unit()):
                        while(S[i].divides(element)):
                            element = element // S[i]
                        i+=1
                    if(not element.is_unit()):
                        raise ValueError("The set %s does not cover the minimal elements for this simple operation")
                ring[2] = S
            else:
                raise NotImplementedError("Multiplicative closed set defined via %s is not implemented" %type(S))

        ## Performing the computations
        order = self.order(); i = 0
        solution = None
        while((solution is None) and (i < bound)):
            A,b = self._get_system_derivative(order+i, True)
            try:
                solution = self._solve_linear_system(A,b,ring)
                den_lcm = lcm([el.denominator() for el in solution])
                solution = [(-el.numerator()*den_lcm)//el.denominator() for el in solution]
            except ValueError: # No solution to the system
                i += 1
                
        return self.__class__(self.base(), solution + [den_lcm], self.derivate())
    ####################################################### 
    
    ####################################################### 
    ### GETTING MATRICES METHODS
    ####################################################### 
    def _get_derivation_matrix_self(self):
        r'''
            Method to get the derivation matrix of the module of ``self``

            This method computes a derivation matrix for the D-module generated by the solutions
            of ``self``. Namely, if `f(x)` is a solution to ``self``, we can consider the module:

            .. MATH::

                M = \langle f, \partial(f),\ldots\rangle

            which (since `f(x)` is annihilated by ``self``) is a finitely
            generated module. Then the derivation matrix allows to compute derivatives within this 
            module.

            In particular, this derivation matrix is `\mathcal{C}_f`.

            OUTPUT:

            A derivation matrix of the module `M`.
        '''
        return self._pre_proc(self.companion())

    def _get_derivation_matrix_addition(self, other):
        r'''
            Method to get the derivation matrix of the addition module of the two equations

            This method computes a derivation matrix for the D-module generated by the solutions
            of the two operators. Namely, if `f(x)` is a solution to ``self`` and `g(x)` is a solution
            to ``other``, then we can consider the module:

            .. MATH::

                M = \langle f, \partial(f),\ldots\rangle + \langle g, \partial(g),\ldots\rangle

            which (since `f(x)` and `g(x)` are annihilated by ``self`` and ``other``) is a finitely
            generated module. Then the derivation matrix allows to compute derivatives within this 
            module.

            In particular, this derivation matrix is `\mathcal{C}_f \oplus \mathcal{C}_g`.

            INPUT:
                * ``other``: the operator for the second operand.

            OUTPUT:

            A derivation matrix of the module `M`.
        '''
        from ajpastor.misc.matrix import diagonal_matrix as diagonal
        Mf = self.companion()
        Mg = other.companion()
        
        Mf, Mg, parent = self._mix_matrices(other, Mf, Mg)
        
        full_companion = diagonal(parent, [Mf,Mg])
        return self._pre_proc(full_companion)

    def _get_derivation_matrix_product(self, other):
        r'''
            Method to get the derivation matrix of the product module of the two equations

            This method computes a derivation matrix for the D-module generated by the solutions
            of the two operators. Namely, if `f(x)` is a solution to ``self`` and `g(x)` is a solution
            to ``other``, then we can consider the module:

            .. MATH::

                M = \langle \partial^i(f)\partial^j(g)\ :\ i,j\in \mathbb{n}\rangle.

            which (since `f(x)` and `g(x)` are annihilated by ``self`` and ``other``) is a finitely
            generated module. Then the derivation matrix allows to compute derivatives within this 
            module.

            In particular, this derivation matrix is the Kronecker sum of the companion matrices
            `\mathcal{C}_f \boxplus \mathcal{C}_g`.
            
            INPUT:
                * ``other``: the operator for the second operand.

            OUTPUT:

            A derivation matrix of the module `M`.
        '''        
        Mf = self.companion()
        Mg = other.companion()
        
        Mf, Mg, parent = self._mix_matrices(other, Mf, Mg)
        
        ## Using tensor product for Kronecker sum
        full_companion = Mf.tensor_product(Matrix.identity(parent, Mg.nrows())) + Matrix.identity(parent, Mf.nrows()).tensor_product(Mg)
        return self._pre_proc(full_companion)

    def _get_vector_addition(self, other):
        r'''
            Method that return the addition represented in the D-module of ``self`` and ``other``.

            This method computes a vector that represent the addition of solutions to ``self`` and
            ``other`` for the D-module generated by the solutions of the two operators. Namely, if 
            `f(x)` is a solution to ``self`` and `g(x)` is a solution to ``other``, then we can 
            consider the module:

            .. MATH::

                M = \langle f, \partial(f),\ldots\rangle + \langle g, \partial(g),\ldots\rangle

            which (since `f(x)` and `g(x)` are annihilated by ``self`` and ``other``) is a finitely
            generated module. This method returns the vector representing the function `f(x)+g(x)`
            within this D-module.

            INPUT:
                * ``other``: the operator for the second operand.

            OUTPUT:

            The vector representing `f(x)+g(x)` in the module `M`.
        '''
        return self._pre_proc(vector(
            ([1] + [0 for i in range(self.order()-1)])+
            ([1] + [0 for i in range(other.order()-1)])))

    def _get_vector_product(self, other):
        r'''
            Method that return the product represented in the D-module of ``self`` and ``other``.

            This method computes a vector that represent the product of solutions to ``self`` and
            ``other`` for the D-module generated by the solutions of the two operators. Namely, if 
            `f(x)` is a solution to ``self`` and `g(x)` is a solution to ``other``, then we can 
            consider the module:

            .. MATH::

                M = \langle \partial^i(f)\partial^j(g)\ :\ i,j\in \mathbb{n}\rangle.

            which (since `f(x)` and `g(x)` are annihilated by ``self`` and ``other``) is a finitely
            generated module. This method returns the vector representing the function ``f(x)g(x)``
            within this D-module.

            INPUT:
                * ``other``: the operator for the second operand.

            OUTPUT:

            The vector representing `f(x)g(x)` in the module `M`.
        '''
        return self._pre_proc(vector(([1] + [0 for i in range(self.order()*other.order()-1)])))

    @cached_method
    def _get_system_derivative(self, ncols, inhom=False):
        r'''
            Method to compute an ansatz system for the derivative of a fixed size.

            This method computes an ansatz system for the derivative of solutions to
            ``self``. Namely, if `f(x)` is a solution to ``self``, we can consider the module:

            .. MATH::

                M = \langle f, \partial(f),\ldots\rangle

            which (since `f(x)` is annihilated by ``self``) is a finitely
            generated module. Hence, the module generated by `f'(x)` is also finitely generated.
            This method creates an ansatz system in the module `M` for computing the linear
            relation between `h(x) = f'(x)` and its derivatives.

            INPUT:
                * ``other``: the operator for the second operand.
                * ``ncols``: size of the desired system (in number of columns)
                * ``inhom``: if ``True``, the method return the ansazt matrix system together
                  with a vector representing the inhomogeneous term of the system.

            OUTPUT:

            The ansazt system for compute a linear relation with `\partial^{ncols}(f'(x))` 
            and its previous derivatives within the module `M`.
        '''        
        from ajpastor.misc.matrix import vector_derivative as der
        
        ## Controlling the input ncols
        if(ncols < 0):
            raise ValueError("The number of columns must be a natural number")
        
        d_matrix = self._get_derivation_matrix_self()

        ## Base case: 0 column, only inhomogeneous term
        if(ncols == 0):
            v = d_matrix*self._pre_proc(vector([1]+(self.order()-1)*[0]))
            system = Matrix(d_matrix.parent().base(), [[]])
        else: # General case, we build the next column
            aux_s, new_v = self._get_system_derivative(ncols-1, True)
            system = Matrix(aux_s.columns()+[new_v]).transpose()
            v = der(d_matrix, new_v, self.derivate())
        
        if(inhom):
            return self._post_proc(system), v
        else:
            return self._post_proc(system)

    @cached_method
    def _get_system_addition(self, other, ncols, inhom=False):
        r'''
            Method to compute an ansatz system for the addition of a fixed size.

            This method computes an ansatz system for the addition of two solutions to
            ``self`` and ``other`` respectively. Namely, if `f(x)` is a solution to 
            ``self`` and `g(x)` is a solution to ``other``, then we can consider the module:

            .. MATH::

                M = \langle f, \partial(f),\ldots\rangle + \langle g, \partial(g),\ldots\rangle

            which (since `f(x)` and `g(x)` are annihilated by ``self`` and ``other``) is a finitely
            generated module. Hence, the module generated by `f(x)+g(x)` is also finitely generated.
            This method creates an ansatz system in the module `M` for computing the linear
            relation between `h(x) = f(x)+g(x)` and its derivatives.

            INPUT:
                * ``other``: the operator for the second operand.
                * ``ncols``: size of the desired system (in number of columns)
                * ``inhom``: if ``True``, the method return the ansazt matrix system together
                  with a vector representing the inhomogeneous term of the system.

            OUTPUT:

            The ansazt system for compute a linear relation with `\partial^{ncols}(f(x)+g(x))` 
            and its previous derivatives within the module `M`.
        '''        
        from ajpastor.misc.matrix import vector_derivative as der
        
        ## Controlling the input ncols
        if(ncols < 0):
            raise ValueError("The number of columns must be a natural number")
        
        d_matrix = self._get_derivation_matrix_addition(other)

        ## Base case: 0 column, only inhomogeneous term
        if(ncols == 0):
            v = self._get_vector_addition(other)
            system = Matrix(d_matrix.parent().base(), [[]])
        else: # General case, we build the next column
            aux_s, new_v = self._get_system_addition(other, ncols-1, True)
            system = Matrix(aux_s.columns()+[new_v]).transpose()
            v = der(d_matrix, new_v, self.derivate())
        
        if(inhom):
            return self._post_proc(system), v
        else:
            return self._post_proc(system)
        
    @cached_method
    def _get_system_product(self, other, ncols, inhom=False):
        r'''
            Method to compute an ansatz system for the addition of a fixed size.

            This method computes an ansatz system for the addition of two solutions to
            ``self`` and ``other`` respectively. Namely, if `f(x)` is a solution to 
            ``self`` and `g(x)` is a solution to ``other``, then we can consider the module:

            .. MATH::

                M = \langle \partial^i(f)\partial^j(g)\ :\ i,j\in \mathbb{n}\rangle.

            which (since `f(x)` and `g(x)` are annihilated by ``self`` and ``other``) is a finitely
            generated module. Hence, the module generated by `f(x)+g(x)` is also finitely generated.
            This method creates an ansatz system in the module `M` for computing the linear
            relation between `h(x) = f(x)g(x)` and its derivatives.

            INPUT:
                * ``other``: the operator for the second operand.
                * ``ncols``: size of the desired system (in number of columns)
                * ``inhom``: if ``True``, the method return the ansazt matrix system together
                  with a vector representing the inhomogeneous term of the system.

            OUTPUT:

            The ansazt system for compute a linear relation with `\partial^{ncols}(f(x)g(x))` 
            and its previous derivatives within the module `M`.
        '''         
        from ajpastor.misc.matrix import vector_derivative as der
        
        ## Controlling the input ncols
        if(ncols < 0):
            raise ValueError("The number of columns must be a natural number")
        
        d_matrix = self._get_derivation_matrix_product(other)

        ## Base case: 0 column, only inhomogeneous term
        if(ncols == 0):
            v = self._get_vector_product(other)
            system = Matrix(d_matrix.parent().base(), [[]])
        else: # General case, we build the next column
            aux_s, new_v = self._get_system_product(other, ncols-1, True)
            system = Matrix(aux_s.columns()+[new_v]).transpose()
            v = der(d_matrix, new_v, self.derivate())
        
        if(inhom):
            return self._post_proc(system), v
        else:
            return self._post_proc(system)
        
    def _get_matrix_composition(self, other):
        from ajpastor.misc.matrix import matrix_of_dMovement as move
    
        g = other
        
        Mf = self.companion()
        
        full_companion, parent = self._compose_companion(Mf,g)
        init_vector = vector(parent, [1] + [0 for i in range(1,self.order())])
        
        return self._post_proc(move(self._pre_proc(full_companion), self._pre_proc(init_vector), self.derivate(), full_companion.ncols()+1))
        
    def _mix_matrices(self, other, Mf, Mg):
        return Mf, Mg, Mf.parent().base()
        
    def _compose_companion(self,Mf,g):
        dg = Mf.parent().base()(self.derivate()(self.base()(g)))
        return dg*Mf, Mf.parent().base()
        
    def _pre_proc(self, M):
        return M
        
    def _post_proc(self, M):
        return M
    ####################################################### 
    
    ####################################################### 
    ### SOLVING MATRICES METHOD
    ####################################################### 
    def _get_element_nullspace(self, M):
        '''
            Method that computes an element in the nullspace of M.
        '''        
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)

    def _solve_linear_system(self, A, b, ring):
        r'''
            Method that computes a solution to `A\alpha = \mathbf{b}` in the given ring.

            This method computes a solution to the inhomogeneous system 
            `A\alpha = \mathbf{b}` within a given ring. If the given ring is 
            the field of fractions of the parent of `A`, then this is a simple
            linear algebra computation. Otherwise, special code may be needed for
            computations.

            The given ring is either a ring structure in Sage or a triplet
            with the following format:
                * A ring `R`. This must be a Noetherian ring.
                * A list of generators `\alpha_1,\ldots,\alpha_n`. We may need to
                  compute algebraic relations between these elements.
                * A list of valid denominators `\gamma_1,\ldots,\gamma_k`. These 
                  elements must be either a generator `\alpha_l` or an element in 
                  `R`.
            If a triplet is provided, the computations will be performed in the 
            ring `R[\alpha_1,\ldots,\alpha_n]_{\gamma_1,\ldots,\gamma_k}`.
        '''        
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)
    ####################################################### 
    

