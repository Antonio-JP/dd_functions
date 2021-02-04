r"""
Python file for directStepOperator

This module offers an implementation of a TwoStepsOperator.

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

#Sage imports
from sage.all import (lcm, Matrix, gcd, prod, vector)

####################################################################################################
####################################################################################################
###
### DirectStepOperator module
###
### ------------------------------------------------------------------------------------------------
###
### This file contains an extension of a TwoStepsOperator that computes the kernell of the appropriate matrix using standard SAGE algorithms.
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

class DirectStepOperator(TwoStepsOperator):

    #######################################################
    ### INIT METHOD AND GETTERS
    #######################################################
    def __init__(self, base, input, derivate = foo_derivative):
        super(DirectStepOperator, self).__init__(base, input, derivate)
            
    ####################################################### 
        
    ####################################################### 
    ### SOLVING MATRICES METHOD
    ####################################################### 
    def _get_element_nullspace(self, M):
        from ajpastor.misc.bareiss import BareissAlgorithm
        ## We take the domain where our elements will lie
        parent = M.parent().base().base()
        
        ## Computing the kernell of the matrix
        try:
            lcms = [lcm([el.denominator() for el in row]) for row in M]
            N = Matrix(parent, [[el*lcms[i] for el in M[i]] for i in range(M.nrows())])
            ba = BareissAlgorithm(parent, N, lambda p : False)
            
            ker = ba.right_kernel_matrix()
        except Exception as e:
            print(e)
            ker = M.right_kernel_matrix()
        #ker = M.right_kernel_matrix()
        ## If the nullspace has hight dimension, we try to reduce the final vector computing zeros at the end
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
        
        ## Our solution has denominators. We clean them all
        p = prod([el.denominator() for el in sol])
        return vector(parent, [el*p for el in sol])
    ####################################################### 
    

