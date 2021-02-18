"""
Python file for sequence manipulations

This module provides several methods for manipulating sequences in a black-box format, i.e., when the
sequence is given as a function that receives the index and returns the corresponding element
of the sequence.

EXAMPLES::

    sage: from ajpastor.misc.sequence_manipulation import *

TODO:
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
from sage.all import (factorial, bell_polynomial, falling_factorial, cached_function)

################################################################################
################################################################################
################################################################################
## Sequence operations
def addition(f,g):
    return lambda n : f(n)+g(n)

def hadamard_product(f,g):
    return lambda n : f(n)*g(n)

def cauchy_product(f,g):
    return lambda n : sum(f(m)*g(n-m) for m in range(n+1))

def standard_derivation(f):
    return lambda n : (n+1)*f(n+1)

def shift(f):
    return lambda n : f(n+1)
        
def composition(f,g):   
    if(g(0) != 0):                     
        raise ValueError("Impossible compose with g(0) != 0")
    @cached_function
    def _composition(n):                                     
        if(n == 0):                                                                
            return f(0)
        result = 0
        current = g
        for k in range(1,n+1):
            result += f(k)*current(n)
            current = cauchy_product(current, g)
        return result
    return _composition

def egf_ogf(f):       
    '''
        Method that receives a sequence in the form of a black-box function
        and return a sequence h(n) such that egf(f) = ogf(h).
        
        Then h(n) = f(n)/factorial(n)
    '''
    return lambda n: f(n)/factorial(n)

def ogf_egf(f):       
    '''
        Method that receives a sequence in the form of a black-box function
        and return a sequence h(n) such that egf(h) = ogf(f).
        
        Then h(n) = f(n)*factorial(n)
    '''
    return lambda n: f(n)*factorial(n)

def inv_lagrangian(f):
    '''
        Inverse of a power series sequence using lagrangian inverse.
        
        This methods computes the functional inverse of the sequence
        defined by ``f`` as an ordinary generating function using the lagrangian
        inversion formula (see https://en.wikipedia.org/wiki/Lagrange_inversion_theorem
        for further information).
        
        Then composition(f, inv_lagrangian(f))(n) = delta(1,n).
    '''
    if(f(0) != 0):
        raise ValueError("Power serie not invertible")
    if(f(1) == 0):
        raise NotImplementedError("Case with order higher than 1 not implemented")
    f = ogf_egf(f)
    @cached_function
    def _inverse_egf(n):
        if(n == 0):
            return 0
        elif(n == 1):
            return 1/f(1)
        else:
            result = 0
            for k in range(1,n):
                poly = bell_polynomial(n-1,k)
                extra = ((-1)**k)*falling_factorial(n+k-1, k)
                if(k == n-1):
                    evaluation = poly(x=f(2)/2/f(1))
                else:
                    evaluation = poly(**{"x%d" %(i) : f(i+2)/(i+2)/f(1) for i in range(n-k)})
                
                result += extra*evaluation
                
            return (1/(f(1)**n)) * result
    return egf_ogf(_inverse_egf)

def Richardson(f,order):
    '''
        Applies the Richardson transformation.
        
        Builds the Richarsdon's sequence of order ``order`` for the sequence given 
        ``f``. This sequence has the same asymptotic behavior as ``f`` but it converges 
        faster (meaning less number of elements are required to get the samy asymptotic 
        information).
        
        LINKS::
            * https://en.wikipedia.org/wiki/Richardson_extrapolation
            * https://www3.risc.jku.at/publications/download/risc_4324/techrep.pdf
        
    '''
    return lambda n : (2**order*f(2*n)-f(n))/(2**order-1)

################################################################################
################################################################################
################################################################################
## From list to sequence method
def list_to_seq(input):
    '''
        Convert a list into a sequence (i.e., a method)
        
        This method convert a list or any other iterable indexed by integers into 
        a method that receives a index as input and returns the corresponding element 
        of the sequence.
    '''
    return lambda n : input[n]
    
def seq_to_list(f, bound=None):
    '''
        Convert a sequence into a list.
        
        This method converts a sequence into a list exploring the sequence until it is 
        not defined or ``bound`` elements have been computed.
        
        WARNING:: if bound is None, the method may not finish. 
    '''
    result = []; i = 0
    while(((bound is None) or (i < bound))):
        try:
            result += [f(i)]
            i += 1
        except Exception:
            break
    return result
    
    
