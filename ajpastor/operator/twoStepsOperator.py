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

from sage.all_cmdline import *   # import sage library

_sage_const_1 = Integer(1); _sage_const_0 = Integer(0)

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

# Local imports
from .listOperator import ListOperator;
from .operator import foo_derivative;

class TwoStepsOperator(ListOperator):

    #######################################################
    ### INIT METHOD AND GETTERS
    #######################################################
    def __init__(self, base, input, derivate = foo_derivative):
        super(TwoStepsOperator, self).__init__(base, input, derivate);
            
    ####################################################### 
    
    ####################################################### 
    ### SOLUTION ARITHMETHIC METHODS (ABSTRACT)
    ####################################################### 
    def _compute_add_solution(self, other):
        M = self._get_matrix_add(other);
        v = self._get_element_nullspace(M);
        
        return self.__class__(self.base(), [el for el in v], self.derivate());
        
    def _compute_mult_solution(self, other):
        M = self._get_matrix_mult(other);
        v = self._get_element_nullspace(M);
        
        return self.__class__(self.base(), [el for el in v], self.derivate());
        
    def _compute_compose_solution(self, other):
        M = self._get_matrix_composition(other);
        v = self._get_element_nullspace(M);
        
        return self.__class__(self.base(), [el for el in v], self.derivate());
    ####################################################### 
    
    ####################################################### 
    ### GETTING MATRICES METHODS
    ####################################################### 
    def _get_matrix_add(self, other):
        '''
            Method to obtain a matrix such any element of the nullspace can be interpreted as a new operator that annihilates the sum (f+g) where f is solution to 'self=0' and g is solution to 'other=0'
        '''        
        from ajpastor.misc.matrix import diagonal_matrix as diagonal;
        from ajpastor.misc.matrix import matrix_of_dMovement as move;
        
        Mf = self.companion();
        Mg = other.companion();
        
        Mf, Mg, parent = self._mix_matrices(other, Mf, Mg);
        
        full_companion = diagonal(parent, [Mf,Mg]);
        init_vector = vector(parent,([_sage_const_1 ] + [_sage_const_0  for i in range(self.getOrder()-_sage_const_1 )])+([_sage_const_1 ] + [_sage_const_0  for i in range(other.getOrder()-_sage_const_1 )]));
        
        return self._post_proc(move(self._pre_proc(full_companion), self._pre_proc(init_vector), self.derivate(), full_companion.ncols()+_sage_const_1 ));
        
    def _get_matrix_mult(self, other):
        '''
            Method to obtain a matrix such any element of the nullspace can be interpreted as a new operator that annihilates the product (fg) where f is solution to 'self=0' and g is solution to 'other=0'
        '''        
        from ajpastor.misc.matrix import block_matrix as block;
        from ajpastor.misc.matrix import diagonal_matrix as diagonal;
        from ajpastor.misc.matrix import matrix_of_dMovement as move;
        
        f = self;
        g = other;
        
        Mf = f.companion();
        Mg = g.companion();
        
        Mf, Mg, parent = self._mix_matrices(other, Mf, Mg);
        
        ## Using tensor product
        full_companion = Mf.tensor_product(Matrix.identity(parent.base(), Mg.nrows())) + Matrix.identity(parent.base(), Mf.nrows()).tensor_product(Mg);
        
        init_vector = vector(parent,([_sage_const_1 ] + [_sage_const_0  for i in range(f.getOrder()*g.getOrder()-_sage_const_1 )]));
                
        return self._post_proc(move(self._pre_proc(full_companion), self._pre_proc(init_vector), self.derivate(), full_companion.ncols()+_sage_const_1 ));
        
    def _get_matrix_composition(self, other):
        from ajpastor.misc.matrix import matrix_of_dMovement as move;
    
        g = other;
        
        Mf = self.companion();
        
        full_companion, parent = self._compose_companion(Mf,g);
        init_vector = vector(parent, [_sage_const_1 ] + [_sage_const_0  for i in range(_sage_const_1 ,self.getOrder())]);
        
        return self._post_proc(move(self._pre_proc(full_companion), self._pre_proc(init_vector), self.derivate(), full_companion.ncols()+_sage_const_1 ));
        
    def _mix_matrices(self, other, Mf, Mg):
        return Mf, Mg, Mf.parent().base();
        
    def _compose_companion(self,Mf,g):
        dg = Mf.parent().base()(self.derivate()(self.base()(g)));
        return dg*Mf, Mf.parent().base();
        
    def _pre_proc(self, M):
        return M;
        
    def _post_proc(self, M):
        return M;
    ####################################################### 
    
    ####################################################### 
    ### SOLVING MATRICES METHOD
    ####################################################### 
    def _get_element_nullspace(self, M):
        '''
            Method that computes an element in the nullspace of M.
        '''        
        raise NotImplementedError('Method not implemented. Class: %s' %self.__class__);
    ####################################################### 
    

