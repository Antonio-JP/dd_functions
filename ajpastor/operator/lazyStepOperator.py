r"""
Python file for lazyStepOperators

This module offers an implementarion of a TwoStepsOperator where the companion matrix is computed lazily, and
hence, the computation of the matrix is lazy. However, the computation of the final nullspace is performed
with all the operations.

**This package need a huge review**

EXAMPLES::
    sage: from ajpastor.operator.lazyStepOperator import *

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
from sage.all import (cached_method, kronecker_delta, Matrix) 

####################################################################################################
####################################################################################################
###
### LazyStepOperator module
###
### ------------------------------------------------------------------------------------------------
###
### This file contains an extension of a TwoStepsOperator that computes the companion matrix in a lazy field, so the computations of the matrix are not directly done.
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

# Imports
from .twoStepsOperator import TwoStepsOperator
from .operator import foo_derivative

from ajpastor.lazy.lazyIDElements import LazyIntegralDomain

class LazyStepOperator(TwoStepsOperator):
    ### Static parameters
    _op_preference = 3

    #######################################################
    ### INIT METHOD AND GETTERS
    #######################################################
    def __init__(self, base, input, derivate = foo_derivative):
        super(LazyStepOperator, self).__init__(base, input, derivate)
            
    ####################################################### 
        
    @cached_method
    def companion(self):
        field = LazyIntegralDomain(self._original_base).fraction_field()
        
        coefficients = [field(el) for el in self.getCoefficients()]
            
        ## We divide by the leading coefficient
        coefficients = [-(coefficients[i]/coefficients[-1]) for i in range(len(coefficients)-1)]
        ## Trying to reduce the elements
        try:
            for i in range(len(coefficients)):
                coefficients[i].reduce()
        except AttributeError:
            pass
        except ArithmeticError:
            pass
        d = len(coefficients)
        
        ## Building the rows of our matrix
        rows = [[0 for i in range(d-1)] + [coefficients[0]]]
        for i in range(d-1):
            rows += [[kronecker_delta(i,j) for j in range(d-1)] + [coefficients[i+1]]]
            
        ## Returning the matrix
        return Matrix(field, rows)
    

