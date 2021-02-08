r"""
Python file for fullLazyOperators

This module offers an implementation of a TwoStepsOperator where all the operations are performed lazily.

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
from sage.all import (Matrix, vector, gcd, kronecker_delta, lcm, prod)

####################################################################################################
####################################################################################################
###
### FullLazyOperator module
###
### ------------------------------------------------------------------------------------------------
###
### This file contains an extension of a TwoStepsOperator that computes the kernell of the appropriate matrix 
### translating the elements into polynomials and reversing the change once obtained the final vector.
###
### If some relations between the variables are known, Gröbner basis reduction will be used.
### ------------------------------------------------------------------------------------------------
###
### Version: 0.0
### Date of begining: 07-02-2018
###
### ------------------------------------------------------------------------------------------------
### Dependencies:
###     - TwoStepsOperator class
####################################################################################################
####################################################################################################

# Local imports
from .twoStepsOperator import TwoStepsOperator
from .operator import foo_derivative

from ajpastor.lazy.lazyRing import LazyRing

from ajpastor.misc.bareiss import BareissAlgorithm

class FullLazyOperator(TwoStepsOperator):
    ### Static parameters
    _op_preference = 5

    #######################################################
    ### INIT METHOD AND GETTERS
    #######################################################
    def __init__(self, base, input, derivate = foo_derivative):
        super(FullLazyOperator, self).__init__(base, input, derivate)
        
        self.__conversion = LazyRing(self.base(), self.base().base_ring())
        self.__version = self.__conversion.version()
        self.__companion = None
            
    ####################################################### 
    def companion(self):
        R = self.__conversion
        if(self.__companion is None or self.__version != R.version()):
            self.__version = R.version()
            coefficients = [R(el) for el in self.getCoefficients()]
                                    
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
            self.__companion = Matrix(R, rows)
            
        return self.__companion
        
    ####################################################### 
    ### GETTING MATRICES METHODS
    ####################################################### 
    def _get_matrix_composition(self, other):
        from ajpastor.misc.matrix import matrix_of_dMovement as move
        R = self.__conversion
    
        dg = R(other).derivative()
        
        full_companion = dg*self.companion()
        
        init_vector = vector(R, [1] + [0 for i in range(1,self.getOrder())])
        
        return move(full_companion, init_vector, lambda p : p.derivative(), full_companion.ncols()+1)
    ####################################################### 
    
    ####################################################### 
    ### SOLVING MATRICES METHOD
    ####################################################### 
    def _get_element_nullspace(self, M):
        ## We take the Conversion System
        R = self.__conversion
        
        ## We assume the matrix is in the correct space
        M = Matrix(R.poly_field(), [[R.simplify(el.poly()) for el in row] for row in M])
        
        ## We clean denominators to lie in the polynomial ring
        lcms = [self.__get_lcm([el.denominator() for el in row]) for row in M]
        M = Matrix(R.poly_ring(), [[el*lcms[i] for el in M[i]] for i in range(M.nrows())])
        f = lambda p: R(p).is_zero()
        try:
            assert(f(1) == False)
        except Exception:
            raise ValueError("The method to check membership is not correct")

        ## Computing the kernell of the matrix
        if(len(R.map_of_vars()) > 0):
            bareiss_algorithm = BareissAlgorithm(R.poly_ring(),M,f,R._ConversionSystem__relations)
            ker = bareiss_algorithm.right_kernel_matrix()
            ## If some relations are found during this process, we add it to the conversion system
            R.add_relations(bareiss_algorithm.relations())
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
        sol = [R.simplify(a) for a in sol]
        
        ## Just to be sure everything is as simple as possible, we divide again by the gcd of all our
        ## coefficients and simplify them using the relations known.
        fin_gcd = gcd(sol)
        finalSolution = [a/fin_gcd for a in sol]
        finalSolution = [R.simplify(a) for a in finalSolution]
        
        ## We transform our polynomial into elements of our destiny domain
        realSolution = [R.to_real(a) for a in finalSolution]
        for i in range(len(realSolution)):
            try:
                realSolution[i].change_built("polynomial", (finalSolution[i], {str(key): R.map_of_vars()[str(key)] for key in finalSolution[i].variables()}))
            except AttributeError:
                pass
        
        return vector(R.base(), realSolution)

    def _solve_linear_system(self, A, b, ring):
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__)
        
    def __get_lcm(self, input):
        try:
            return lcm(input)
        except AttributeError:
            ## No lcm for this class, implementing a general lcm
            try:
                ## Relying on gcd
                p = self.__conversion.poly_ring()
                res = p(1)
                for el in input:
                    res = p((res*el)/gcd(res,el))
                return res
            except AttributeError:
                ## Returning the product of everything
                return prod(input)
    ####################################################### 

