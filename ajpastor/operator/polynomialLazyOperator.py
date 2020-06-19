r"""
Python file for Polynomial Lazy Operators

This module offers an implementation of a TwoStepsOperator using lazy operations with polynomials.

**This module requires a huge review**

EXAMPLES::
    sage: from ajpastor.operator.polynomialLazyOperator import *

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
from sage.all import (cached_method, kronecker_delta, Matrix, lcm, gcd, vector)

####################################################################################################
####################################################################################################
###
### PolynomialLazyOperator module
###
### ------------------------------------------------------------------------------------------------
###
### This file contains an extension of a LazyStepOperator that computes the kernell of the appropiate matrix trnaslating the elements into polynomials and reversing the change once obtained the final vector.
###
### If some relations between the variables are known, Groebner basis reduction will be used.
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
###     - TwoStepsOperator class
####################################################################################################
####################################################################################################

# Local imports
from .twoStepsOperator import TwoStepsOperator
from .operator import foo_derivative

from ajpastor.lazy.lazyIDElements import LazyIntegralDomain
from ajpastor.lazy.lazyToPoly import LazyToPoly

from ajpastor.misc.bareiss import BareissAlgorithm

class PolynomialLazyOperator(TwoStepsOperator):
    ### Static parameters
    _op_preference = 4

    #######################################################
    ### INIT METHOD AND GETTERS
    #######################################################
    def __init__(self, base, input, derivate = foo_derivative):
        super(PolynomialLazyOperator, self).__init__(base, input, derivate)
        
        self.__conversion = None
            
    ####################################################### 
    
    @cached_method
    def companion(self):
        field = LazyIntegralDomain(self._original_base).fraction_field()
        
        coefficients = [field(el) for el in self.getCoefficients()]
        
        if(self.__conversion is None):  
            self.__conversion = LazyToPoly(self.base(), coefficients)
                    
        coefficients = self.__conversion.to_poly(coefficients)
            
        ## We divide by the leading coefficient
        coefficients = [-(coefficients[i]/coefficients[-1]) for i in range(len(coefficients)-1)]
        ## Trying to reduce the elements
        try:
            for i in range(len(coefficients)):
                coefficients[i].reduce()
        except AttributeError:
            pass
        d = len(coefficients)
        
        ## Building the rows of our matrix
        rows = [[0 for i in range(d-1)] + [coefficients[0]]]
        for i in range(d-1):
            rows += [[kronecker_delta(i,j) for j in range(d-1)] + [coefficients[i+1]]]
            
        ## Returning the matrix
        return Matrix(self.__conversion.poly_field(), rows)
        
    def _mix_matrices(self, other, Mf, Mg):
        new_conversion = self.__conversion.mix_conversion(other.__conversion)
        self.__conversion = new_conversion
        self.__dict__['companion'].cache.clear()
        other.__conversion = new_conversion
        other.__dict__['companion'].cache.clear()
        
        
        return self.companion(), other.companion(), self.companion().parent().base()
        
    def _compose_companion(self, Mf, g):
        raise NotImplementedError("Method not implemented for this class of operators: %s" %(self.__class__))
        
    def _pre_proc(self, M):
        return self.__conversion.to_real(M)
        
    def _post_proc(self, M):
        try:
            return self.__conversion.to_poly(M)
        except Exception:
            new_conversion = self.__conversion.mix_conversion(LazyToPoly(self.base(), M))
            self.__conversion = new_conversion
            self.__dict__['companion'].cache.clear()
            
            return self.__conversion.to_poly(M)
            
        
    ####################################################### 
    ### SOLVING MATRICES METHOD
    ####################################################### 
    def _get_element_nullspace(self, M):
        ## We take the domain where our elements will lie
        ## conversion->lazy domain->domain
        parent = self.__conversion.base().base()
        
        ## We assume the matrix is in the correct space
        M = self.__conversion.simplify(M)
        
        ## We clean denominators to lie in the polynomial ring
        lcms = [lcm([el.denominator() for el in row]) for row in M]
        R = M.parent().base().base()
        M = Matrix(R, [[el*lcms[i] for el in M[i]] for i in range(M.nrows())])
        f = lambda p: self.__smart_is_null(p)
        try:
            assert(f(1) == False)
        except Exception:
            raise ValueError("The method to check membership is not correct")
            
        from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isUniPolynomial
        from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing as isMPolynomial
        ## Computing the kernell of the matrix
        if(isUniPolynomial(R) or isMPolynomial(R)):
            bareiss_algorithm = BareissAlgorithm(R,M,f)
            ker = bareiss_algorithm.right_kernel_matrix()
            ## If some relations are found during this process, we add it to the conversion system
            self.__conversion.add_relations(bareiss_algorithm.relations())
        else:
            ker = [v for v in M.right_kernel_matrix()]
                
        ## If the nullspace has high dimension, we try to reduce the final vector computing zeros at the end
        aux = [row for row in ker]
        i = 1
        
        while(len(aux) > 1):
            new = []
            current = None
            for j in range(len(aux)):
                if(aux[j][-(i)] == 0):
                    new += [aux[j]]
                elif(current is None):
                    current = j
                else:
                    new += [aux[current]*aux[j][-(i)] - aux[j]*aux[current][-(i)]]
                    current = j
            aux = [el/gcd(el) for el in new]
            i = i+1

            
        ## When exiting the loop, aux has just one vector
        sol = aux[0]
        sol = [self.__conversion.simplify(a) for a in sol]
        
        ## This steps for clearing denominator are no longer needed
        #lazyLcm = lcm([a.denominator() for a in sol])
        #finalLazySolution = [a.numerator()*(lazyLcm/(a.denominator())) for a in sol]
        
        ## Just to be sure everything is as simple as possible, we divide again by the gcd of all our
        ## coefficients and simplify them using the relations known.
        fin_gcd = gcd(sol)
        finalSolution = [a/fin_gcd for a in sol]
        finalSolution = [self.__conversion.simplify(a) for a in finalSolution]
        
        ## We transform our polynomial into elements of our destiny domain
        finalSolution = [self.__conversion.to_real(a).raw() for a in finalSolution]
        
        return vector(parent, finalSolution)
    ####################################################### 
    
    def __smart_is_null(self, p):
        try:
            return any(self.__conversion.to_real(factor[0]).raw().is_null for factor in p.factor())
        except AttributeError:
            return self.__conversion.to_real(p).raw().is_null
            


