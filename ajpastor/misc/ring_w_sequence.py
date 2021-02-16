"""
Python file for Ring with Sequences

This module implements a Ring Parent structure in Sage such that all its elements define a sequence in some space. This
implies that the elements of a Ring with Sequence must provide a method (sequence).

EXAMPLES::
    sage: from ajpastor.misc.ring_w_sequence import *

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
# from sage.all import *   # import sage library
from sage.all import (UniqueRepresentation, Ring, derivative, factorial, SR)


class Ring_w_Sequence (UniqueRepresentation, Ring):
    def __init__(self, base, method = None, category = None):
        Ring.__init__(self, base, category=category)
        self.__method = method
        
    def sequence(self, el, n, list=False):
        if(el in self):
            if(list):
                return [self.__method(el,i) for i in range(n)]
            else: 
                return self.__method(el, n)
        raise TypeError("Can not compute a sequence for an element which is not in the ring")
        
class Wrap_w_Sequence_Ring (Ring_w_Sequence):
    def __init__(self, base, method = None):
        super().__init__(base, method=method, category=base.category())

    def _coerce_map_from_(self, S):
        return self.base()._coerce_map_from_(S)

    def _has_coerce_map_from(self, S):
        return self.base()._has_coerce_map_from(S)

    def __call__(self, *args, **kwds):
        return self.base()(*args, **kwds)
    
    def __getattribute__(self, name):
        ## Avoiding infinite recursion
        if(name == "base"):
            return super().__getattribute__(name)
        
        ## Now that base is not the attribute
        try:
            ## Trying to have the attribute f the base ring
            attr = self.base().__getattribute__(name)
            if(attr is None):
                raise AttributeError
            return attr
        except AttributeError:
            ## No attribute for the ring, searching for this ring
            attr = super().__getattribute__(name)
            if(attr is None):
                raise AttributeError
            return attr
            
        raise AttributeError("'%s' object has no attribute '%s'" %(self.__class__, name))
        
    def __repr__(self):
        return "(SR)" + repr(self.base())

    def __str__(self):
        return "(SR)" + str(self.base())

    def sequence(self, el, n, list=False):
        if(list):
            return [self.sequence(el, i) for i in range(n)]
        self_gen = 'x'
        try:
            self_gen = self.base().gens()[-1 ]
        except:
            pass
            
        if(self_gen == 1 ):
            if(n > 0 ):
                return 0 
            elif(n==0 ):
                return el
            else:
                raise ValueError("Impossible get negative element of the sequence")
        if(el in self):
            res = el
            for _ in range(n):
                try:
                    res = derivative(res,self_gen)
                except AttributeError:
                    ## Not derivative possible. Considering a constant
                    if(n == 0 ):
                        return res
                    return 0 
            try:
                return res(**{repr(self_gen):0 })/factorial(n)
            except TypeError:
                ## Not callable element. Returning the element without evaluation
                return res/factorial(n)
        else:
            raise TypeError("Element not in `self` to compute the sequence.")
#####################################################################

def sequence(el, n, list=False, x_required=True):
    R = el.parent()
    if(R is SR):
        variables = [str(v) for v in el.variables()]
        if('x' in variables):
            variable = el.variables()[variables.index('x')]
        elif(not x_required):
            variable = el.variables()[0]
        else:
            if(n > 0):
                return 0
            else:
                return el
        if(list):
            return [el.derivative(variable,i)(**{str(variable):0})/factorial(i) for i in range(n)]
        else:
            return el.derivative(variable,n)(**{str(variable):0})/factorial(n)
    if(not isinstance(R, Ring_w_Sequence)):
        R = Wrap_w_Sequence_Ring(R)
        
    return R.sequence(el,n)

