r"""
Python file for TwoSteps Operators

This module offers an abstract class of linear differential operators which basic structure is a list of coefficients.

EXAMPLES::
	sage: from ajpastor.operator.listOperator import *

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

_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_0 = Integer(0)

####################################################################################################
####################################################################################################
###
### ListOperator module
###
### ------------------------------------------------------------------------------------------------
###
### This file contains a simple implementation of the abstract class Operator needed to the some 
### of the calculations for DD-Rings and DD-Functions
### ------------------------------------------------------------------------------------------------
###
### Version: 2.0
### Date of begining: 21-11-2016
###
### Update (05-05-2017):
###     - Deleted method getCoefficientParent (now the Operator method parent() do the same)
###     - Deleted attributes "parent" and "__derivate" (the Operator methods parent() and derivate() do the same)
###     - Added the option of initialize a FooOperator from another operator.
###     - Maded the imports more precise
###     - Rearrange file: more readable structure
###     - Added the methods __compute_add_solution, __compute_mult_solution, __compute_derivative_solution and __compute_integral_solution.
###     - Changed name: method "isZero" to "is_zero"
###     - Changed name of class FooOperator to ListOperator
###
### Updated (21-08-2017)
###     - Changed name parent to base
###
### ------------------------------------------------------------------------------------------------
### Dependencies:
###     - Operator class
####################################################################################################
####################################################################################################

# Local imports
from .operator import Operator;
from .operator import foo_derivative;
from ajpastor.misc.ring_w_sequence import Wrap_w_Sequence_Ring;

from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isPolynomial;

class ListOperator(Operator):
    ### Static parameters
    _op_preference = _sage_const_2 ;

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
        ## Initializing the minimal structure
        super(ListOperator, self).__init__(base, input, derivate);
                
        if (isinstance(input, list)):
            if(len(input) == _sage_const_0 ):
                self.__coefficients = [_sage_const_1 ];
            else:
                # Getting the las non-zero position
                i = len(input);
                while(input[i-_sage_const_1 ] == _sage_const_0  and i > _sage_const_0 ):
                    i -= _sage_const_1 ; 
                try:
                    if(i == _sage_const_0 ):
                        self.__coefficients = [self.base().one()];
                    else:
                        self.__coefficients = [self.base()(input[j]) for j in range(i)];
                except Exception as e:
                    raise TypeError('The input (%s) is not valid for a ListOperator with coefficients in (%s)' %(input,format(base)));
        elif(isinstance(input, Operator)):
            self.__coefficients = [self.base()(coeff) for coeff in input.getCoefficients()];
        else:
            try:
                self.__coefficients = [self.base()(input)];
            except Exception:
                raise TypeError('The input is not valid for an operator with coefficients in (%s)' %(format(base)));
        #coeff_gcd = gcd(self.__coefficients);
        #if(coeff_gcd != 0):
        #    self.__coefficients = [self.base()(el/coeff_gcd) for el in self.__coefficients];
        #if(isinstance(self.base(), Wrap_w_Sequence_Ring) and isPolynomial(self.base().base())):
        #    l = []
        #    for el in self.__coefficients:
        #        l += el.coefficients(x);
        #    
        #    coeff_gcd = gcd(l);
        #    if(coeff_gcd != 0):
        #        self.__coefficients = [el/coeff_gcd for el in self.__coefficients];
            
    ### Getter methods
    def getOrder(self):
        return len(self.__coefficients)-_sage_const_1 ;
        
    def getCoefficients(self):
        return self.__coefficients;
    
    def getCoefficient(self, i):
        if (i < _sage_const_0 ):
            raise IndexError('The argument must be a number greater or equal to zero');
        elif (i < len(self.__coefficients)):
            return self.__coefficients[i];
        
        return _sage_const_0 ;
    #######################################################
        
    #######################################################
    ### OPERATOR ARITHMETIC METHODS (ABSTRACT)
    ####################################################### 
    ### Arithmetic
    def add(self, other):
        if(isinstance(other, ListOperator)):
            if(self.is_zero()):
                return other;
            if(other.is_zero()):
                return self;
            return self.__class__(self.base(), 
                [self.getCoefficient(i)+self.base()(other.getCoefficient(i)) for i in range(max(self.getOrder(), other.getOrder())+_sage_const_1 )], 
                self.derivate());
        elif(isinstance(other, Operator)):
            return other.__radd__(self);
        else:
            return self.add(self.__class__(self.base(),other, self.derivate()));
        
    def scalar(self, other):
        try:
            r = self.base()(other);
            if(r == _sage_const_0 ):
                return self.__class__(self.base(), _sage_const_0 , self.derivate());
            return self.__class__(self.base(), [r*coeff for coeff in self.getCoefficients()], self.derivate());
        except TypeError:
            raise TypeError("The argument for this method must be an element of the current domain");
        
    def mult(self, other):
        try:
            if(isinstance(other, ListOperator)):
                if(self.is_zero() or other.is_zero()):
                    self.__class__(self.base(), _sage_const_0 , self.derivate()); 
                res = self.__class__(self.base(), _sage_const_0 , self.derivate());
                aux = None;
                for coeff in self.getCoefficients():
                    if(aux is None):
                        aux = other;
                    else:
                        aux = aux.derivative();
                    res = res.add(aux.scalar(coeff));
                return res;
            elif(isinstance(other, Operator)):
                return other.__rmul__(self);
            else:
                return self.mult(self.__class__(self.base(),other, self.derivate()));
        except Exception as e:
            print "Got an exception: %s"%(e);
            raise e;
    
    ### Equality
    def is_zero(self):
        for coeff in self.getCoefficients():
            if not (coeff == _sage_const_0 ):
                return False;
        return True;
        
    def __eq__(self, other):
        if(isinstance(other, ListOperator)):
            selfCoeffs = self.getCoefficients();
            otherCoeffs = other.getCoefficients();
            
            if(len(selfCoeffs) == len(otherCoeffs)):
                for i in range(len(selfCoeffs)):
                    if(not (selfCoeffs[i] == otherCoeffs[i])):
                        return False;
                return True;
        return False;
        
    ### Differential
    def derivative(self):
        newCoeffs = [self.derivate()(self.getCoefficient(_sage_const_0 ))];
        for j in range(_sage_const_1 ,self.getOrder()+_sage_const_1 ):
            newCoeffs += [self.derivate()(self.getCoefficient(j)) + self.getCoefficient(j-_sage_const_1 )];
        newCoeffs += [self.getCoefficient(self.getOrder())];
        
        return self.__class__(self.base(), newCoeffs, self.derivate());
    ####################################################### 
    
    ####################################################### 
    ### SOLUTION ARITHMETHIC METHODS (ABSTRACT)
    ####################################################### 
    def _compute_derivative_solution(self):
        r = self.getCoefficients();
        ### The operation depends on the first coefficient of the equation
        if(r[_sage_const_0 ] == _sage_const_0 ):
            ### If is zero, then the next derivative has the same coefficients shifted 1 position to the left.
            newCoeffs = [r[i] for i in range(_sage_const_1 ,len(r))];
        else:
            ### Otherwise, we compute another operator
            der0 = self.derivate()(r[_sage_const_0 ]);
            newCoeffs = [r[i]*r[_sage_const_0 ] + self.derivate()(r[i+_sage_const_1 ])*r[_sage_const_0 ]-der0*r[i+_sage_const_1 ] for i in range(self.getOrder())];
            newCoeffs += [r[_sage_const_0 ]*r[-_sage_const_1 ]];
            
        return self.__class__(self.base(), newCoeffs, self.derivate());
            
    def _compute_integral_solution(self):
        return self.__class__(self.base(), [_sage_const_0 ] + self.getCoefficients(), self.derivate());
    ####################################################### 
    
    ####################################################### 
    ### MAGIC PYTHON METHODS
    ####################################################### 
    def __call__(self, obj):
        try:
            obj = self.base()(obj);
        except Exception:
            verbose("The object %s can not be casted into an element of the coefficient ring" %(obj), level=_sage_const_3 );
        res = _sage_const_0 ;
        for coeff in self.getCoefficients():
            res += coeff*obj;
            obj = self.derivate()(obj);
        return res;
        
    def __repr__(self):
        return ("%s(%s)"%(self.__class__.__name__,self.__coefficients.__repr__()));
        
    #######################################################         
    

