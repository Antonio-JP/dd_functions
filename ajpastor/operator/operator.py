r"""
Python file for linear differential operator

This module offers an abstract class of linear differential operators giving a general interface for being used
independently of the implementation.

EXAMPLES::
    sage: from ajpastor.operator.operator import *

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

#Sage imports
from sage.all import (cached_function, ZZ, PolynomialRing, cached_method, kronecker_delta, 
                        Matrix, falling_factorial)

from sage.all_cmdline import x

####################################################################################################
####################################################################################################
###
### Operator module
###
### ------------------------------------------------------------------------------------------------
###
### This file contains the code for the ABSTRACT class operator, that will be a helpful tool to the 
### implementation of DD-Rings and DD-Functions.
### 
### ------------------------------------------------------------------------------------------------
###
### Version: 2.0
### Date of begining: 21-11-2016
###
### Updated (28-04-2017)
###     - Added forward and backward polynomial
###     - Added the computation of the jp_value and jp_matrix
###     - Added a cache functionality to high cost elements
###
### Updated (05-04-2017)
###     - Added the Ring_w_Sequence to this file
###     - Deleted the method _get_sequence_element
###     - Added cached methods "parent" and "derivate"
###     - Deleted the method coefficientsParent (now self.parent() do the same)
###     - Rearrange file: more readable structure
###     - Added the methods add_solution, mult_solution, derivative_solution and integral_solution.
###     - Added the methods __compute_add_solution, __compute_mult_solution, __compute_derivative_solution and __compute_integral_solution.
###     - Added a preference system for casting operators (see methods *_solution and get_preference 
###     - Changed name: method "isZero" to "is_zero"
###
### Updated (21-08-2017)
###     - Changed name parent to base
###
####################################################################################################
####################################################################################################

from ajpastor.misc.cached_property import derived_property
from ajpastor.misc.ring_w_sequence import Ring_w_Sequence
from ajpastor.misc.ring_w_sequence import Wrap_w_Sequence_Ring

from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing


## GENERIC UTILITIES METHODS
def foo_derivative(p):
    try:
        return p.derivative(x)
    except AttributeError:
        return 0
    
@cached_function
def get_integer_roots(element):
    if(not is_PolynomialRing(element.parent())):
        raise TypeError("Incompatible element to compute integer roots")
    base,deep_vars,_ = _tower_variables(element.parent().base())
    gen = str(element.parent().gens()[0])
    
    ring = element.parent().change_ring(base)
    deg = element.degree()
    p = ring.one()
    while(p.degree() < deg):
        new_ev = {var : base.random_element() for var in deep_vars}
        p = ring(element(**new_ev))
    
    pos_roots = [ZZ(root) for root in p.roots(multiplicities=False) if (root in ZZ)]
    return [rt for rt in pos_roots if element(**{gen : rt}) == 0]
    
@cached_function
def _tower_variables(parent):
    result = []
    n_vars = 0
    while(is_PolynomialRing(parent) or is_MPolynomialRing(parent)):
        result += [str(gen) for gen in parent.gens()]
        n_vars += parent.ngens()
        parent = parent.base()

    return (parent,result, n_vars)

## Operator class
class Operator(object):
    ### Static parameters
    _op_preference = 0

    #######################################################
    ### INIT METHOD AND GETTERS
    #######################################################
    def __init__(self, base, input, derivate = foo_derivative):
        '''
        This method allows the user to instantiate a new object of type Operator. 
        
        This method must be extended in each child-class of Operator.
        
        INPUT:
            - base: the Structure where the coefficients of the operator will be
            - input: the input data for the operator. The format must be checked in each class.
        '''
        
        ## Computing the polynomial associated ring
        try:
            self.__pol_var = 'n'
            i = -1
            names = [str(gen) for gen in base.base_ring().gens()]
            while(self.__pol_var in names):
                i += 1
                self.__pol_var = 'n' + str(i)
            
            self.__polynomialRing = PolynomialRing(base.base_ring(), self.__pol_var)
        except RuntimeError:
            self.__pol_var = 'n'
            self.__polynomialRing = PolynomialRing(base.base_ring(),self.__pol_var)
            
        ## Computing the Ring_w_Sequence associated to base
        if(isinstance(base, Ring_w_Sequence)):
            self.__base = base
        else:
            self.__base = Wrap_w_Sequence_Ring(base)
        self._original_base = base
                
        ## Declaring private fields
        self.__derivate = derivate
        
    def base(self):
        return self.__base
        
    def derivate(self):
        return self.__derivate
        
    def _get_preference(self):
        return self._op_preference
    
    ### Getter methods
    def order(self):
        '''
        This method allows the user to get the order of the operator. 
        
        This method must be extended in each child-class of Operator.
        '''
        raise NotImplementedError('Method not implemented -- Abstract class asked')
        
    def coefficients(self):
        '''
        This method allows the user to get the coefficients of the operator. 
        
        This method must be extended in each child-class of Operator.
        '''
        raise NotImplementedError('Method not implemented -- Abstract class asked')
    
    def coefficient(self, i):
        if (i < 0):
            raise IndexError('The argument must be a number greater or equal to zero')
        elif (i <= self.order()):
            return self.coefficients()[i]
        else:
            return 0

    def lc(self):
        r'''
            Method to get the leading coefficient of a differential operator.

            The leading coefficient is the coefficient that multiplies the 
            highest order derivation with a non-zero coefficient.
        '''
        return self.coefficients()[self.order()]
        
    @cached_method
    def companion(self):
        field = self.base().fraction_field()
        
        coefficients = [field(el) for el in self.coefficients()]
        
        ## We divide by the leading coefficient
        coefficients = [-(coefficients[i]/coefficients[-1]) for i in range(len(coefficients)-1)]
        ## Trying to reduce the elements
        try:
            for i in range(len(coefficients)):
                coefficients[i].reduce()
        except (AttributeError, ArithmeticError):
            pass
        d = len(coefficients)
        
        ## Building the rows of our matrix
        rows = [[0 for i in range(d-1)] + [coefficients[0]]]
        for i in range(d-1):
            rows += [[kronecker_delta(i,j) for j in range(d-1)] + [coefficients[i+1]]]
            
        ## Returning the matrix
        return Matrix(field, rows)
    
    @cached_method
    def noetherian_ring(self, other=None):
        r'''
            Method that builds a noetherian ring that contains all the coefficients

            This method computes a differential noetherian ring in Sage that contains all
            the coefficients of ``self`` and ``other`` and where we can divide
            be the leading coefficients of both operators. This method will
            rely on the method :func:`~ajpastor.dd_functions.ddFunction.DDFunction.noetherian_ring`.

            This method currently does not work if ``self.base()`` is a DDRing.

            INPUT:
                * ``other``: other operator to compute the common noetherian ring at the same time
                * ``structure``: determines the format of the output.

            OUTPUT:

            The output have always 3 main entries:
                * The ring `R` that is the base of the Noetherian extension
                * The list of elements `\alpha_i` that will generate the final ring.
                * The list of generators of `S`.
            In the case of ``structure`` being ``True``, a fourth entry will be added
            with the ring `R[x_1,\ldots,x_n]_S` where the variable `x_i` represent the 
            element `\alpha_i`.
        '''
        from ajpastor.dd_functions import is_DDRing
        if(is_DDRing(self.base())):
            raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)

        c = [self.lc()]
        if(not (other is None)): c += [other.lc()]
        final_dens = []
        for el in c:
            if((not el in self.base()) or (not self.base()(el).is_unit())):
                final_dens += [el]
        
        return self.base(), [], final_dens

    #######################################################
    
    #######################################################
    ### RECURSION POLYNOMIALS METHODS
    #######################################################        
    def get_recursion_polynomial(self, n):
        '''
            Method to get a recursion polynomial associated with this operator.
            
            If the requested polynomial is greater than zero, then we will return a `forward` polynomial, but if the request is lesser than zero, we will return a backward polynomial, computing it if necessary.
            
            INPUT:
                - n: index of the recursion polynomial requested.
                
            OUTPUT:
                A polynomial on self.base()[nx] where x will be an integer such the variable nx is not in self.base().gens()
        '''
        if(n >= 0):
            try:
                return self.forward(n)
            except IndexError:
                return 0
        else:
            return self.backward(-n)
            
    @cached_method
    def forward(self, n):
        if(n < 0):
            raise IndexError("Forward polynomials have only positive index")
        elif(n > self.order()):
            return 0
        elif(self.is_zero()):
            return 0
        else: 
            var = self.__polynomialRing.gens()[-1]
            
            return sum([self.base().sequence(self.coefficient(l),l-n)*falling_factorial(var+n,l) for l in range(n, self.order()+1)])
          
    @cached_method  
    def backward(self, n):
        if(n < 0):
            raise IndexError("Backward polynomials have only positive index")
        elif(self.is_zero()):
            return 0
        
        var = self.__polynomialRing.gens()[-1]
        return sum([self.base().sequence(self.coefficient(l), l+n)*falling_factorial(var-n, l) for l in range(0,self.order()+1)])
        
    def get_recursion_row(self,i):
        r = self.coefficients()
        d = self.order()
        row = []
        
        #var = self.__polynomialRing.gens()[-1]
        ### First summation part
        #row += [sum([falling_factorial(k,l)*self.base().sequence(r[l],i-k+l) for l in range(0,k+1)]) for k in range(0,min(i,d))]
        #if(i<d):
        #    ## Second summation part
        #    row += [sum([falling_factorial(k+i,l)*self.base().sequence(r[l], l-k) for l in range(k,i+k+1)]) for k in range(d-i)]
        #    ## Third summation part
        #    row += [self.forward(k)(**{str(var):i}) for k in range(d-i,d+1)]
        #else:
        #    ## Second summation part
        #    row += [self.backward(i-d-k)(**{str(var):i}) for k in range(i-d)]
        #    ## Third summation part
        #    row += [self.forward(k)(**{str(var):i}) for k in range(0,d+1)]
        
        ## First summation part
        row += [sum([falling_factorial(k,l)*self.base().sequence(r[l],i-k+l) for l in range(0,k+1)]) for k in range(0,min(i,d))]
        if(i<d):
            ## Second summation part
            row += [sum([falling_factorial(k+i,l)*self.base().sequence(r[l], l-k) for l in range(k,i+k+1)]) for k in range(d-i)]
            ## Third summation part
            row += [self.__eval_pol(self.forward(k),i) for k in range(d-i,d+1)]
        else:
            ## Second summation part
            row += [self.__eval_pol(self.backward(i-d-k),i) for k in range(i-d)]
            ## Third summation part
            row += [self.__eval_pol(self.forward(k),i) for k in range(0,d+1)]
            
        return row
        
    def get_recursion_matrix(self, n):
        nrows = n+1
        ncols = n+self.forward_order+1
        rows = []
        
        for i in range(nrows):
            row = self.get_recursion_row(i)
            
            rows += [[row[i] for i in range(min(len(row),ncols))] + [0 for i in range(ncols-len(row))]]
            
        return Matrix(self.__polynomialRing.base(), rows)
    #######################################################
        
    #######################################################
    ### SOLUTION SPACE METHODS
    #######################################################
    @derived_property
    def dimension(self):
        return self.jp_matrix().right_kernel_matrix().nrows()
    
    @derived_property
    def forward_order(self):
        if(self.is_zero()):
            raise ValueError("The zero operator has not forward order")
        
        n = self.order()
        while(self.get_recursion_polynomial(n) == 0):
            n -= 1
        
        return n
    
    @cached_method
    def jp_value(self):
        ## TODO Be careful with this computation: only valid is the base field are the rational
        jp_pol = self.get_recursion_polynomial(self.forward_order)
        return max([self.order()-self.forward_order] + get_integer_roots(jp_pol))
       
    @cached_method
    def jp_matrix(self):
        return self.get_recursion_matrix(self.jp_value())
        
    def get_jp_fo(self):
        return self.jp_value()+self.forward_order
    #######################################################
    
    #######################################################
    ### OPERATOR ARITHMETIC METHODS (ABSTRACT)
    ####################################################### 
    def add(self, other):
        '''
        This method allows the user to add two operators. 
        
        This method must be extended in each child-class of Operator.
        '''
        raise NotImplementedError('Method not implemented -- Abstract class asked')
        
    def scalar(self, other):
        '''
        This method allows the user to do a (left)scalar multiplication. 
        
        This method must be extended in each child-class of Operator.
        '''
        raise NotImplementedError('Method not implemented -- Abstract class asked')
        
    def mult(self, other):
        '''
        This method allows the user to multiply two operators. 
        
        This method must be extended in each child-class of Operator.
        '''
        raise NotImplementedError('Method not implemented -- Abstract class asked')
        
    def is_zero(self):
        '''
        This method allows the user to know if this operator is the zero operator. 
        
        This method must be extended in each child-class of Operator.
        '''
        raise NotImplementedError('Method not implemented -- Abstract class asked')
        
    def derivative(self):
        '''
        This method allows the user to derivate the operator (if possible). If not, it will raise a
        NotImplementedError. 
        
        This method must be extended in each child-class of Operator.
        '''
        raise NotImplementedError('This operator can not be derivated')
    ####################################################### 
    
    ####################################################### 
    ### SOLUTION ARITHMETHIC METHODS
    ####################################################### 
    def add_solution(self, other):
        '''
        This method computes a new operator such any solution of 'self == 0' plus any solution of 'other == 0' must satisfy.
        '''
        ## If the input is not an operator, trying the casting
        if(not isinstance(other, Operator)):
            other = self.__class__(self.base(), other, self.derivate())
            
        ## If the input is an Operator we guess the hightest preference type
        if(not isinstance(other, self.__class__)):
            if(other._get_preference() > self._get_preference()):
                return other.add_solution(self)
            other = self.__class__(self.base(), other, self.derivate())
            
        return self._compute_add_solution(other)
                
    def mult_solution(self, other):
        '''
        This method computes a new operator such any solution of 'self == 0' multiplied by any solution of 'other == 0' must satisfy.
        '''
        ## If the input is not an operator, trying the casting
        if(not isinstance(other, Operator)):
            other = self.__class__(self.base(), other, self.derivate())
            
        ## If the input is an Operator we guess the hightest preference type
        if(not isinstance(other, self.__class__)):
            if(other._get_preference() > self._get_preference()):
                return other.mult_solution(self)
            other = self.__class__(self.base(), other, self.derivate())
            
        return self._compute_mult_solution(other)
        
    def derivative_solution(self):
        '''
        This method computes a new operator such the derivative of any solution of 'self == 0' must satisfy.
        '''
        return self._compute_derivative_solution()
        
    def integral_solution(self):
        '''
        This method computes a new operator such any anti-derivative of any solution of 'self == 0' must satisfy.
        '''
        return self._compute_integral_solution()
        
    def compose_solution(self, other):
        '''
        Let c be the coefficients of 'self'. This method computes a differential operator such any solution 'f' of the equation with coefficients 'c(other^(-1))' composed with 'other' will satisfy.
        
        This method (awkward by definition) requires that 'other' is in self.base().
        
        INPUT:
            - other: an element of 'self.base()'
            
        OUTPUT:
            - A new operator 'A' of the same class as 'self' with 'A.base() == self.base()'
        
        ERRORS:
            - 'TypeError' wil be raised if 'other' is not in 'self.base()'
        '''
        ## If the input is not an operator, trying the casting
        if(not other in self.base()):
            raise TypeError("Element (%s) is not valid for compose with a solution of %s" %(other, str(self)))
        
        return self._compute_compose_solution(other)
    
    def _compute_add_solution(self, other):
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)
        
    def _compute_mult_solution(self, other):
        '''
        This method computes a new operator such any solution of 'self == 0' multiplied by any solution of 'other == 0' must satisfy.
        It assumes that other and self are exactly the same type.
        '''
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)
        
    def _compute_derivative_solution(self):
        '''
        This method computes a new operator such the derivative of any solution of 'self == 0' must satisfy.
        '''
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)
        
    def _compute_integral_solution(self):
        '''
        This method computes a new operator such any anti-derivative of any solution of 'self == 0' must satisfy.
        '''
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)
        
    def _compute_compose_solution(self, other):
        '''
        This method computes a new operator that annihilates any solution of 'self' compose with any solution of 'other'.
        '''
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)
    #######################################################

    ####################################################### 
    ### SIMPLE ARITHMETHIC METHODS
    ####################################################### 
    def simple_add_solution(self, other, S=None):
        r'''
            Method to compute the annihilator of the addition of solutions to two operators.

            This method computes a new operator `A` that annihilates all the functions that 
            are the addition of the solutions of ``self`` and ``other``.
            This method takes care that the singularities of the new equation are included in 
            the zeros of elements in the set `S`.
            
            Currently this only work if the coefficients are univariate polynomials.

            INPUT:

            * ``other``: the operator to compute the addition of solutions.
            * ``S``: (optional) a set for considering the leading coefficients as 
                simple elements. This set must be either a list of generators in ``self.base()``
                (from which we consider then the smallest multiplicatively close set) or 
                a structure where the ``in`` python command can detect if elements in 
                ``self.base()`` are contained in them. If ``None`` is given, 
                a default minimal set is computed for this particular operation.
        '''
        ## If the input is not an operator, trying the casting
        if(not isinstance(other, Operator)):
            other = self.__class__(self.base(), other, self.derivate())
            
        ## If the input is an Operator we guess the hightest preference type
        if(not isinstance(other, self.__class__)):
            if(other._get_preference() > self._get_preference()):
                return other.add_solution(self)
            other = self.__class__(self.base(), other, self.derivate())
            
        return self._compute_simple_add_solution(other, S)

    def simple_mult_solution(self, other, S=None):
        r'''
            Method to compute the annihilator of the product of solutions to two operators.

            This method computes a new operator `A` that annihilates all the functions that 
            are the product of the solutions of ``self`` and ``other``.
            This method takes care that the singularities of the new equation are included in 
            the zeros of elements in the set `S`.
            
            Currently this only work if the coefficients are univariate polynomials.

            INPUT:

            * ``other``: the operator to compute the product of solutions.
            * ``S``: (optional) a set for considering the leading coefficients as 
                simple elements. This set must be either a list of generators in ``self.base()``
                (from which we consider then the smallest multiplicatively close set) or 
                a structure where the ``in`` python command can detect if elements in 
                ``self.base()`` are contained in them. If ``None`` is given, 
                a default minimal set is computed for this particular operation.
        '''
        ## If the input is not an operator, trying the casting
        if(not isinstance(other, Operator)):
            other = self.__class__(self.base(), other, self.derivate())
            
        ## If the input is an Operator we guess the hightest preference type
        if(not isinstance(other, self.__class__)):
            if(other._get_preference() > self._get_preference()):
                return other.mult_solution(self)
            other = self.__class__(self.base(), other, self.derivate())
            
        return self._compute_simple_mult_solution(other, S)

    def simple_derivative_solution(self, S=None):
        r'''
            Method to compute the annihilator of the derivative of solutions to ``self``.

            This method computes a new operator `A` that annihilates all the functions that 
            are the derivative of the solutions of ``self``.
            This method takes care that the singularities of the new equation are included in 
            the zeros of elements in the set `S`.
            
            Currently this only work if the coefficients are univariate polynomials.

            INPUT:

            * ``S``: (optional) a set for considering the leading coefficients as 
                simple elements. This set must be either a list of generators in ``self.base()``
                (from which we consider then the smallest multiplicatively close set) or 
                a structure where the ``in`` python command can detect if elements in 
                ``self.base()`` are contained in them. If ``None`` is given, 
                a default minimal set is computed for this particular operation.
        '''
        return self._compute_simple_derivative_solution(S)

    def _compute_simple_add_solution(self, other, S=None, bound=5):
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)

    def _compute_simple_mult_solution(self, other, S=None, bound=5):
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)

    def _compute_simple_derivative_solution(self, S=None, bound=5):
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)

    ####################################################### 
    
    ####################################################### 
    ### MAGIC PYTHON METHODS
    ####################################################### 
    def __getitem__(self, key):
        if(key > self.order() or key < 0):
            raise IndexError("No coefficient can be get bigger than the order or with negative index")
        return self.coefficient(key)
    
    def __call__(self, obj):
        '''
        This method allows the user to apply the operator to an object. 
        
        This method must be extended in each child-class of Operator.
        '''
        try:
            res = obj.parent().zero()
            to_mult = obj
            for i in range(self.order()+1):
                res += self.coefficient(i)*to_mult
                to_mult = to_mult.derivative()
            return res
        except Exception:
            raise NotImplementedError('Method not implemented -- Abstract class asked')
        
    def __hash__(self):
        return hash(tuple(self.coefficients()))
    ### Addition
    def __add__(self, other):
        try:
            return self.add(other)
        except Exception:
            return NotImplemented
            
    ### Substraction
    def __sub__(self, other):
        try:
            #return self.add(other.scalar(-1))
            return self.scalar(-1).add(other).scalar(-1)
        except Exception:
            return NotImplemented
            
    ### Multiplication
    def __mul__(self, other):
        try:                
            return self.mult(other)
        except Exception:
            return NotImplemented

    def __pow__(self, other):
        if(not other in ZZ or other <= 0):
            return NotImplemented
        if(other == 1):
            return self
        else:
            return self.__mul__(self.__pow__(other-1))
  
    ### Reverse addition
    def __radd__(self, other):
        return self.__add__(other)
            
    ### Reverse substraction
    def __rsub__(self, other):
        return self.scalar(-1).__add__(other)
            
    ### Reverse multiplication
    def __rmul__(self, other):
        try:
            if(not isinstance(other, Operator)):
                return self.scalar(other)
                
            return other.mult(self)
        except Exception:
            return NotImplemented
        
    ### Implicit addition
    def __iadd__(self, other):
        return self.__add__(other)
            
    ### Implicit substraction
    def __isub__(self, other):
        return self.__sub__(other)
            
    ### Implicit multiplication
    def __imul__(self, other):
        return self.__mul__(other)
            
    ### Unary '-'
    def __neg__(self):
        return self.scalar(-1)
    ####################################################### 
    
    def __eval_pol(self,pol, val):
        try:
            return pol(**{self.__pol_var:val})
        except RuntimeError:
            coeffs = pol.coefficients(False)
            return sum(coeffs[i]*val**i for i in range(len(coeffs)))

