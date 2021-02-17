r"""
Python file for Ore Operators

This module offers an implementation of an linear differential operator based on the implementation on the package ore_algebra
by Manuel Kauers and Marc Mezzarobba. This class is a simply wrapper putting a common interface from the ore operators with
the other operators provided in ajpastor.operator.

EXAMPLES::
    sage: from ajpastor.operator.oreOperator import *

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
from sage.all_cmdline import x

####################################################################################################
####################################################################################################
###
### Ore-Operator module
###
### ------------------------------------------------------------------------------------------------
###
### This file contains a wrapper that adapts the OreOperator class from Manuel Kauers' package (see
### ore_algebra.OreOperator) so we can use them together with other classes of Operators
### 
### ------------------------------------------------------------------------------------------------
###
### Version: 2.0
### Date of begining: 21-11-2016
###
### Update (05-05-2017)
###     - Deleted the method getCoefficientParent (now the Operator method parent() do the same)
###     - Deleted the field "parent" (it is stored in the Operator class)
###     - Made the imports more precise
###     - Created a new attribute "__oa" where the OreAlgebra of the element is stored
###     - Rearrange file: more readable structure
###     - Added the methods __compute_add_solution, __compute_mult_solution, __compute_derivative_solution and __compute_integral_solution.
###     - Changed name: method "isZero" to "is_zero"
###
### Update (10-05-2017)
###     - Updated the code for the new version of ore_algebra package (
###
### Updated (21-08-2017)
###     - Changed name parent to base
###
### ------------------------------------------------------------------------------------------------
### Dependencies:
###     - Operator class
###     - ore_algebra package 
####################################################################################################
####################################################################################################

# General imports
from ore_algebra import OreAlgebra
from ore_algebra.ore_operator import OreOperator

# Local imports
from .operator import Operator
from .directStepOperator import DirectStepOperator
from .operator import foo_derivative

class w_OreOperator(Operator):
    ### Static parameters
    map_to_algebras = {}
    _op_preference = 1

    #######################################################
    ### INIT METHOD AND GETTERS
    #######################################################
    def __init__(self, base, input, derivate = foo_derivative):
        '''
        This method allows the user to instantiate a new object of type Operator. 
        
        This method must be extended in each child-class of Operator.
        
        INPUT:
            - base: the Structure where the coefficients of the operator will be
            - input: the input data for the operator. It can be an element of the associated 
            OreAlgebra for `base` or a list of elements of `base`
        '''
        ## Initializing the minimal structure
        super(w_OreOperator, self).__init__(base, input, derivate)
        
        ## Computing the Ore_Algebra associated with base
        if(not base in w_OreOperator.map_to_algebras):
            newOreAlgebra = OreAlgebra(base, ('D', lambda p : p, derivate))
            w_OreOperator.map_to_algebras[self.base()] = newOreAlgebra
            
        self.__oa = w_OreOperator.map_to_algebras[self.base()]
        d = self.__oa.gen()
        
        ## Computing the operator
        try:
            if isinstance(input, w_OreOperator):
                self.operator = input.operator
            else:
                if isinstance(input, Operator):
                    input = input.coefficients()
                if isinstance(input, list):
                    res = self.__oa(0)
                    for i in range(len(input)):
                        res += self.base()(input[i])*d**i
                    self.operator = res
                else:
                    self.operator = self.__oa(input)
                    
            if(self.operator == 0):
                self.operator = d
                
        except TypeError as e:
            raise e
        except Exception as e:
            raise TypeError('The input (%s) is not valid for an oreOperator with coefficients in (%s)\nCaused by: %s - %s' %(input,format(base),type(e),e))
            
            
    ### Getter methods
    def order(self):
        return self.operator.order()
        
    def coefficients(self):
        return self.operator.coefficients(sparse=False)
    
    #######################################################
        
    #######################################################
    ### OPERATOR ARITHMETIC METHODS (ABSTRACT)
    ####################################################### 
    ### Arithmetic
    def add(self, other):
        if(isinstance(other, w_OreOperator)):
            return w_OreOperator(self.base(), self.operator+self.__oa(other.operator))
        elif(isinstance(other, Operator)):
            return self+w_OreOperator(self.base(),other.coefficients())
        else:
            return w_OreOperator(self.base(), self.operator+self.__oa(other))
        
    def scalar(self, other):
        return w_OreOperator(self.base(), self.__oa(other)*self.operator)
        
    def mult(self, other):
        if(isinstance(other, w_OreOperator)):
            return w_OreOperator(self.base(), self.operator*self.__oa(other.operator))
        elif(isinstance(other, Operator)):
            try:
                return self*w_OreOperator(self.base(),other.coefficients())
            except Exception:
                return other.__class__(self.base(),self).mult(other)
        else:
            return w_OreOperator(self.base(), self.operator*self.__oa(other))
        
    ### Equality
    def is_zero(self):
        return self.operator == 0
        
    def __eq__(self, other):
        try:
            if(isinstance(other, Operator)):
                other = self.__oa(other.coefficients())
            return self.operator == other
        except Exception:
            pass
        return False

    __hash__ = Operator.__hash__
        
    ### Differential
    def derivative(self):
        d = self.__oa.gen()
        return w_OreOperator(self.base(), d*self.operator)
    ####################################################### 
        
    ####################################################### 
    ### SOLUTION ARITHMETHIC METHODS (ABSTRACT)
    ####################################################### 
    def _compute_add_solution(self, other):
        try:
            return w_OreOperator(self.base(),self.operator.lclm(other.operator, algorithm="linalg"))
        except TypeError:
            return w_OreOperator(self.base(),self.operator.lclm(other.operator, algorithm="euclid"))
        
    def _compute_mult_solution(self, other):
        return w_OreOperator(self.base(),self.operator.symmetric_product(other.operator))
        
    def _compute_derivative_solution(self):
        d = self.__oa.gen()
        return w_OreOperator(self.base(), self.operator.annihilator_of_associate(d))
        
    def _compute_integral_solution(self):
        return w_OreOperator(self.base(),self.operator.annihilator_of_integral())
        
    def _compute_compose_solution(self, other):
        op1 = DirectStepOperator(self.base(), self, self.derivate())
        
        return w_OreOperator(self.base(), op1._compute_compose_solution(other), self.derivate())
    ####################################################### 

    ####################################################### 
    ### SIMPLE SOLUTION ARITHMETHIC METHODS (ABSTRACT)
    ####################################################### 
    def _compute_simple_add_solution(self, other, bound = 5):
        equ1 = DirectStepOperator(self.base(), self)
        equ2 = DirectStepOperator(self.base(), other)
        return w_OreOperator(self.base(), equ1._compute_simple_add_solution(equ2, bound))
        
    def _compute_simple_mult_solution(self, other, bound = 5):
        equ1 = DirectStepOperator(self.base(), self)
        equ2 = DirectStepOperator(self.base(), other)
        return w_OreOperator(self.base(), equ1._compute_simple_mult_solution(equ2, bound))
        
    def _compute_simple_derivative_solution(self, bound = 5):
        equ1 = DirectStepOperator(self.base(), self)
        return w_OreOperator(self.base(), equ1._compute_simple_derivative_solution(bound))
    ####################################################### 
    
    ####################################################### 
    ### MAGIC PYTHON METHODS
    ####################################################### 
    def __call__(self, obj):
        return self.operator(obj, action=lambda p : p.derivative(x))
        
    def __repr__(self):
        return ("Wrapped_OreOperator(%s)"%(self.operator.__repr__()))
        
    ####################################################### 
    
    #######################################################
    ### OTHER WRAPPED METHODS
    #######################################################
    def annihilator_of_associate(self, M):
        M = w_OreOperator(self.base(), M).operator
        return w_OreOperator(self.base(), self.operator.annihilator_of_associate(M))
        
    def annihilator_of_polynomial(self, poly):
        return w_OreOperator(self.base(), self.operator.annihilator_of_polynomial(poly))

