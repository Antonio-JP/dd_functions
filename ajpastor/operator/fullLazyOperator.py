r"""
Python file for fullLazyOperators

This module offers an implementarion of a TwoStepsOperator where all the operations are performed lazily.

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

from sage.all_cmdline import *   # import sage library

_sage_const_1 = Integer(1); _sage_const_0 = Integer(0); _sage_const_5 = Integer(5)

####################################################################################################
####################################################################################################
###
### FullLazyOperator module
###
### ------------------------------------------------------------------------------------------------
###
### This file contains an extension of a TwoStepsOperator that computes the kernell of the appropiate matrix trnaslating the elements into polynomials and reversing the change once obtained the final vector.
###
### If some relations between the variables are known, Groebner basis reduction will be used.
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
from .twoStepsOperator import TwoStepsOperator;
from .operator import foo_derivative;

from ajpastor.lazy.lazyRing import LazyRing;

from ajpastor.misc.bareiss import BareissAlgorithm;

class FullLazyOperator(TwoStepsOperator):
    ### Static parameters
    _op_preference = _sage_const_5 ;

    #######################################################
    ### INIT METHOD AND GETTERS
    #######################################################
    def __init__(self, base, input, derivate = foo_derivative):
        super(FullLazyOperator, self).__init__(base, input, derivate);
        
        self.__conversion = LazyRing(self.base(), self.base().base_ring());
        self.__version = self.__conversion.version();
        self.__companion = None;
            
    ####################################################### 
    def companion(self):
        R = self.__conversion;
        if(self.__companion is None or self.__version != R.version()):
            self.__version = R.version();
            coefficients = [R(el) for el in self.getCoefficients()];    
                                    
            ## We divide by the leading coefficient
            coefficients = [-(coefficients[i]/coefficients[-_sage_const_1 ]) for i in range(len(coefficients)-_sage_const_1 )];
            ## Trying to reduce the elements
            try:
                for i in range(len(coefficients)):
                    coefficients[i].reduce();
            except AttributeError:
                pass;
            d = len(coefficients);
            
            ## Building the rows of our matrix
            rows = [[_sage_const_0  for i in range(d-_sage_const_1 )] + [coefficients[_sage_const_0 ]]];
            for i in range(d-_sage_const_1 ):
                rows += [[kronecker_delta(i,j) for j in range(d-_sage_const_1 )] + [coefficients[i+_sage_const_1 ]]];
                
            ## Returning the matrix
            self.__companion = Matrix(R, rows);
            
        return self.__companion;
        
    ####################################################### 
    ### GETTING MATRICES METHODS
    ####################################################### 
    def _get_matrix_add(self, other):
        '''
            Method to obtain a matrix such any element of the nullspace can be interpreted as a new operator that annihilates the sum (f+g) where f is solution to 'self=0' and g is solution to 'other=0'
        '''        
        from ajpastor.misc.matrix import diagonal_matrix as diagonal;
        from ajpastor.misc.matrix import matrix_of_dMovement as move;
        
        f = self;
        g = other;
        
        R = self.__conversion;
                
        ## Computing the companion matrices
        Mf = f.companion();
        Mg = g.companion();
        
        full_companion = diagonal(R, [Mf,Mg]);
        init_vector = vector(R,([_sage_const_1 ] + [_sage_const_0  for i in range(self.getOrder()-_sage_const_1 )])+([_sage_const_1 ] + [_sage_const_0  for i in range(other.getOrder()-_sage_const_1 )]));
        
        return move(full_companion, init_vector, lambda p : p.derivative(), full_companion.ncols()+_sage_const_1 );
        
    def _get_matrix_mult(self, other):
        '''
            Method to obtain a matrix such any element of the nullspace can be interpreted as a new operator that annihilates the product (fg) where f is solution to 'self=0' and g is solution to 'other=0'
        '''        
        from ajpastor.misc.matrix import matrix_of_dMovement as move;
        
        f = self;
        g = other;
        
        R = self.__conversion;
                
        ## Computing the companion matrices
        Mf = f.companion();
        Mg = g.companion();
        
        ## Computing Kroenecker sum of the matrices
        full_companion = Mf.tensor_product(Matrix.identity(R, Mg.nrows())) + Matrix.identity(R, Mf.nrows()).tensor_product(Mg);
        
        init_vector = vector(R,([_sage_const_1 ] + [_sage_const_0  for i in range(f.getOrder()*g.getOrder()-_sage_const_1 )]));
                
        return move(full_companion, init_vector, lambda p : p.derivative(), full_companion.ncols()+_sage_const_1 );
        
    def _get_matrix_composition(self, other):
        from ajpastor.misc.matrix import matrix_of_dMovement as move;
        R = self.__conversion;
    
        dg = R(other).derivative();
        
        full_companion = dg*self.companion();
        
        init_vector = vector(R, [_sage_const_1 ] + [_sage_const_0  for i in range(_sage_const_1 ,self.getOrder())]);
        
        return move(full_companion, init_vector, lambda p : p.derivative(), full_companion.ncols()+_sage_const_1 );
    ####################################################### 
    
    ####################################################### 
    ### SOLVING MATRICES METHOD
    ####################################################### 
    def _get_element_nullspace(self, M):
        ## We take the Conversion System
        R = self.__conversion;
        
        ## We assume the matrix is in the correct space
        M = Matrix(R.poly_field(), [[R.simplify(el.poly()) for el in row] for row in M]);
        
        ## We clean denominators to lie in the polynomial ring
        lcms = [self.__get_lcm([el.denominator() for el in row]) for row in M];
        M = Matrix(R.poly_ring(), [[el*lcms[i] for el in M[i]] for i in range(M.nrows())]);
        f = lambda p: R(p).is_zero();
        try:
            assert(f(_sage_const_1 ) == False);
        except Exception:
            raise ValueError("The method to check membership is not correct");

        ## Computing the kernell of the matrix
        if(len(R.map_of_vars()) > _sage_const_0 ):
            bareiss_algorithm = BareissAlgorithm(R.poly_ring(),M,f,R._ConversionSystem__relations);
            ker = bareiss_algorithm.right_kernel_matrix();
            ## If some relations are found during this process, we add it to the conversion system
            R.add_relations(bareiss_algorithm.relations());
        else:
            ker = [v for v in M.right_kernel_matrix()];
                
        ## If the nullspace has high dimension, we try to reduce the final vector computing zeros at the end
        aux = [row for row in ker];
        i = _sage_const_1 ;
        
        while(len(aux) > _sage_const_1 ):
            new = [];
            current = None;
            for j in range(len(aux)):
                if(aux[j][-(i)] == _sage_const_0 ):
                    new += [aux[j]];
                elif(current is None):
                    current = j;
                else:
                    new += [aux[current]*aux[j][-(i)] - aux[j]*aux[current][-(i)]];
                    current = j;
            aux = [el/gcd(el) for el in new];
            i = i+_sage_const_1 ;

            
        ## When exiting the loop, aux has just one vector
        sol = aux[_sage_const_0 ];
        sol = [R.simplify(a) for a in sol];
        
        ## Just to be sure everything is as simple as possible, we divide again by the gcd of all our
        ## coefficients and simplify them using the relations known.
        fin_gcd = gcd(sol);
        finalSolution = [a/fin_gcd for a in sol];
        finalSolution = [R.simplify(a) for a in finalSolution];
        
        ## We transform our polynomial into elements of our destiny domain
        realSolution = [R.to_real(a) for a in finalSolution];
        for i in range(len(realSolution)):
            try:
                realSolution[i].change_built("polynomial", (finalSolution[i], {str(key): R.map_of_vars()[str(key)] for key in finalSolution[i].variables()}));
            except AttributeError:
                pass;
        
        return vector(R.base(), realSolution);
        
    def __get_lcm(self, input):
        try:
            return lcm(input);
        except AttributeError:
            ## No lcm for this class, implementing a general lcm
            try:
                ## Relying on gcd
                p = self.__conversion.poly_ring();
                res = p(_sage_const_1 );
                for el in input:
                    res = p((res*el)/gcd(res,el));
                return res;
            except AttributeError:
                ## Returning the product of everything
                return prod(input);
    ####################################################### 

