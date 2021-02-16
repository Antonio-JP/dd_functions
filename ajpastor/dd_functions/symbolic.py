r"""
Python file for symbolic DDFunctions

This package provides all the functionality to manage the DDFunction as symbolic expressions and viceversa,
being able to build DDFunctions from Symbolic Expressions when the functions employed are in the library
ddExamples.

EXAMPLES::

    sage: from ajpastor.dd_functions import *
    sage: DFinite
    DD-Ring over (Univariate Polynomial Ring in x over Rational Field)

TODO::
    * Do the Examples section of this documentation
    * Document the package
    * Check the functionality of the package
    
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
# This file was *autogenerated* from the file ./symbolic.sage
from sage.all_cmdline import *   # import sage library

_sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_0 = Integer(0)

from .ddFunction import *;
from .ddFunction import DDFunction;
from .ddExamples import *;

from ajpastor.misc.verbose import *;

###################################################################################################
### SYMBOLIC CONVERSION OF DD_FUNCTIONS
###################################################################################################
def symbolic(function):
    if(isinstance(function, DDFunction)):
        try:
            return function.to_symbolic();
        except Exception as e:
            return e;
    return None;
    
#@wverbose
def from_symbolic(exp, dR = DFinite):
    exp = SR(exp);
    ## Base case: The expression is a polynomial
    try:
        polynomial = dR.original_ring()(str(exp));
        #sverbose("A polynomial found");
        return polynomial;
    except Exception:
        pass;
    
    ## Other cases: We choose between operands
    try:
        import types;
        operator = exp.operator();
        if(operator is None):
            raise ValueError("Impossible to cast: reach bottom without polynomial");
        
        ## Getting the name
        name = None;
        try:
            name = operator.__name__;
        except AttributeError:
            name = operator.name();
            
        #sverbose("Operator name: %s" %name);
            
        ## Converting the operands
        operands = [from_symbolic(el, dR) for el in exp.operands()];
                
        ## Choosing the operation
        ### Python types
        if(name == "list"):
            #sverbose("Returning list");
            return operands;
        elif(name == "tuple"):
            #sverbose("Returning tuple");
            return tuple(operands);
            #sverbose("Returning set");
        elif(name == "set"):
            return set(operands);
        ### Arithmetic
        elif(name == "add_vararg"):
            #sverbose("Returning sum");
            return sum(operands);
        elif(name == "mul_vararg"):
            #sverbose("Returning mult");
            for el in operands:
                print(el);
            return prod(operands);
        elif(name == "pow"):
            try:
                exponent = int(operands[_sage_const_1 ]);
                #if(exponent < 0 and (not(isinstance(operands[0], DDFunction)))):
                #    operands[0] = dR(operands[0]);
            except ValueError:
                pass;
            #sverbose("Returning pow");
            return pow(operands[_sage_const_0 ],operands[_sage_const_1 ]);
        ### Trigonometric
        elif(name == "sin"):
            #sverbose("Returning sin");
            #sverbose("%s" %str(operands[0]));
            return Sin(operands[_sage_const_0 ]);
        elif(name == "cos"):
            #sverbose("Returning cos");
            return Cos(operands[_sage_const_0 ]);
        elif(name == "sinh"):
            #sverbose("Returning sinh");
            return Sinh(operands[_sage_const_0 ]);
        elif(name == "cosh"):
            #sverbose("Returning cosh");
            return Cosh(operands[_sage_const_0 ]);
        elif(name == "tan"):
            #sverbose("Returning tan");
            return Tan(operands[_sage_const_0 ]);
        ### Logarithmic and exponential
        elif(name == "log"):
            #sverbose("Returning log");
            return Log(operands[_sage_const_0 ]);
        elif(name == "exp"):
            #sverbose("Returning exp");
            return Exp(operands[_sage_const_0 ]);
        ### Special functions
        elif(name == "bessel_J"):
            return BesselD(operands[_sage_const_0 ])(operands[_sage_const_1 ]);
        elif(name == "legendre_P"):
            return LegendreD(operands[_sage_const_0 ])(operands[_sage_const_1 ]);
        elif(name == "chebyshev_T"):
            return ChebyshevD(operands[_sage_const_0 ],_sage_const_1 )(operands[_sage_const_1 ]);
        elif(name == "chebyshev_U"):
            return ChebyshevD(operands[_sage_const_1 ],_sage_const_2 )(operands[_sage_const_1 ]);
        ### Hypergeometric functions
        elif(name == "hypergeometric"):
            return GenericHypergeometricFunction(operands[_sage_const_0 ],operands[_sage_const_1 ])(operands[_sage_const_2 ]);
        
        raise TypeError("No valid operator found");
    except AttributeError:
        return None; # Impossible to get the name of the operator
        
def symbolic_simplify(function):
    '''
    An inplace simplification using the symbolic SAGE expressions
    '''
    ## If the input is not a DDFunction, we just return it
    if(isinstance(function, DDFunction)):
        ## First, we check the function itself
        symbolic = from_symbolic(function.to_symbolic(), function.parent());
        if(not isinstance(symbolic, DDFunction)):
            symbolic = function.parent()(symbolic);
            
        if(symbolic.size() < function.size()):
            function.equation = symbolic.equation;
        if(len(repr(symbolic)) < len(repr(function))):
            function._DDFunction__name = repr(symbolic);
            
        ## Now we check the coefficients of the equation
        symbolic_simplify_coefficients(function);
    return function;
    
def symbolic_simplify_coefficients(function):
    if(isinstance(function, DDFunction)):
        for i in range(function.order()+_sage_const_1 ):
            symbolic_simplify(function.equation.coefficient(i));
        
###################################################################################################
### PACKAGE ENVIRONMENT VARIABLES
###################################################################################################
__all__ = ["symbolic", "from_symbolic", "symbolic_simplify", "symbolic_simplify_coefficients"];

