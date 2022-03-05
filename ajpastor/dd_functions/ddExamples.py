r"""
Python file for examples of Differentially definable functions.

With this module the user has access to many special functions with the :class:`~ajpastor.dd_functions.ddFunction.DDFunction` structure.
Here we describe the functions available in this module. For further information on each function, 
please access the documentation for that particular function.
        
All the elements that are returned in this module instances of :class:`~ajpastor.dd_functions.ddFunction.DDFunction`, i.e.,
formal power series defined with a linear differential equation and some appropriate initial values. See the module
:mod:`~ajpastor.dd_functions.ddFunction` for further information.
        
When possible, the functions returned by this module are associated with
the usual implementation of those functions in Sage, (see the module :mod:`~ajpastor.dd_functions.symbolic`
for further information).

This module includes lots of examples and test that should be always checked to run completely. The identities
checked in these tests can all be found in the literature of `here <https://fungrim.org/>`_.
        
The functions available in this module are the following:

* TRIGONOMETRIC FUNCTIONS:
    * :func:`Sin`
    * :func:`Cos`
    * :func:`Tan`
    * :func:`Sinh`
    * :func:`Cosh`
    * :func:`Tanh`
    * :func:`Arcsin`
    * :func:`Arccos`
    * :func:`Arctan`
    * :func:`Arcsinh`
    * :func:`Arccosh`
    * :func:`Arctanh`
* EXPONENTIAL FUNCTIONS:
    * :func:`Exp`
    * :func:`Log`
    * :func:`Log1`
* BESSEL TYPE FUNCTIONS (:dlmf:`10` and :dlmf:`11`):
    * :func:`BesselJ`
    * :func:`BesselI`
    * :func:`StruveH`
    * :func:`StruveL`
* ORTHOGONAL POLYNOMIALS:
    * :func:`LegendreD` (:dlmf:`14`)
    * :func:`ChebyshevD` (:dlmf:`18`)
* HYPERGEOMETRIC FUNCTIONS (:dlmf:`15` and :dlmf:`16`):
    * :func:`HypergeometricFunction`
    * :func:`GenericHypergeometricFunction`
    * :func:`PolylogarithmD` (:dlmf:`25.12`)
* RICCATI EQUATION (:wiki:`Riccati_equation`):
    * :func:`RiccatiD`
* MATHIEU TYPE FUNCTIONS (:dlmf:`28`):
    * :func:`MathieuD`
    * :func:`MathieuSin`
    * :func:`MathieuCos`
    * :func:`MathieuH`
    * :func:`MathieuSinh`
    * :func:`MathieuCosh`
    * :func:`HillD`
* AIRY'S FUNCTIONS:
    * :func:`AiryD`
* PARABOLIC-CYLINDER TYPE FUNCTIONS:
    * :func:`ParabolicCylinderD`
* ELLIPTIC INTEGRALS (:dlmf:`19`):
    * :func:`EllipticLegendreD`
* SPHEROIDAL WAVE FUNCTIONS (:dlmf:`30`):
    * :func:`CoulombSpheroidalFunctionD`
    * :func:`SpheroidalWaveFunctionD`
* HEUN'S FUNCTIONS (:dlmf:`31`):
    * :func:`FuchsianD`
    * :func:`HeunD`
* COULOMB WAVE FUNCTION (:dlmf:`33`):
    * :func:`FCoulombD`  
* COMBINATORIAL FUNCTIONS: 
    * :func:`FactorialD`
    * :func:`CatalanD`
    * :func:`FibonacciD`
    * :func:`BellD`
    * :func:`BernoulliD`

EXAMPLES::

    sage: from ajpastor.dd_functions import *
    sage: Exp(x).init(10, True) == [1]*10
    True

TODO:
    * Improve the Examples section of this doc
    * Improve the documentation of the functions in this package

AUTHORS:
    * Antonio Jimenez-Pastor (2016-10-01): initial version

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
from sage.all import (cached_function, factorial, bell_polynomial, QQ, ZZ, pi,
                        sqrt, sin, cos, gamma, prod, PolynomialRing, Matrix, vector, lcm, SR,
                        ideal)
from sage.all_cmdline import x

from sage.rings.fraction_field import is_FractionField
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isPolynomial
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing as isMPolynomial
from sage.categories.pushout import pushout, FractionField

# ajpastor imports
from ajpastor.dd_functions import (is_DDFunction, is_DDRing, DDRing, ParametrizedDDRing, DFinite, DFiniteI, DDFinite)
from ajpastor.dd_functions.exceptions import ZeroValueRequired
from ajpastor.dd_functions.lazyDDRing import LazyDDRing
from ajpastor.misc.dynamic_string import DynamicString
from ajpastor.misc.matrix import matrix_of_dMovement as move

##################################################################################
##################################################################################
###
### Trigonometric and Hyperbolic trigonometric Functions
###
##################################################################################
##################################################################################
@cached_function
def Sin(input, ddR = None):
    r'''
        D-finite implementation of the Sine function (`\sin(x)`).

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a sine-type function. For more
        information about the sine function, consult the following references:
            
        * :wolf:`Sine`
        * :wiki:`Sine`

        This function can be converted into symbolic expressions.

        INPUT:
            
        * ``input``: a valid input for the sine function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition will 
              be computed. The function must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.

        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.
                
        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: Sin(x).init(10, True)
            [0, 1, 0, -1, 0, 1, 0, -1, 0, 1]
            sage: Sin(x)[0]
            1
            sage: Sin(x)[1]
            0
            sage: Sin(x)[2]
            1
            sage: Sin(x).derivative() == Cos(x)
            True
            sage: Sin(x).derivative(times=2) == -Sin(x)
            True
            sage: Cos(x)^2 + Sin(x)^2 == 1
            True
            sage: # checking the object with polynomial coefficients
            sage: polys = [QQ[x](x*(x-1)), QQ[x](x*(x-3)*(x+1)), QQ[x](x*(x-2/3)*(x+10)*(x-1)),
            ....: QQ[x](x*(x-1)^2*(x+3)^2)]
            sage: for p in polys:
            ....:     l1 = Sin(p).init(10, True)
            ....:     l2 = [sin(p).derivative(i)(x=0) for i in range(10)]
            ....:     if(not l1 == l2):
            ....:         print(p)
            sage: # checking the composition with polynomial coefficients
            sage: for p in polys:
            ....:     l1 = (Sin(x)(p)).init(10, True)
            ....:     l2 = [sin(p).derivative(i)(x=0) for i in range(10)]
            ....:     if(not l1 == l2):
            ....:         print(p)
            sage: Sin(2*x) == 2*Sin(x)*Cos(x)
            True
            sage: Sin(2*x).init(10, True) == [sin(2*x).derivative(i)(x=0) for i in range(10)]
            True
            sage: Sin(3*x) == 3*Sin(x) - 4*Sin(x)^3
            True
            sage: Sin(-x) == -Sin(x)
            True
            sage: Sin(x)*(Tan(x/2)^2+1) == 2*Tan(x/2)^2 # long time (> 1 min)
            True

        We can also check identities with complex exponential::

            sage: I = DFiniteI.base_ring().gens()[0]; I
            I
            sage: X = DFiniteI.variables()[0]; X
            x
            sage: Exp(I*X) - Exp(-I*X) == 2*I*Sin(x)
            True
            sage: I*Sin(x) == Sinh(I*X)
            True

        And also the relation with the hypergeometric functions::

            sage: Sin(x) == x*F01(3/2)(-x^2/4)
            True

        Due to the nature of this implementation, the case for `x^n` for `n > 2` 
        must be treated as functions instead of computing directly the function. 
        The key here is that for that kind of input, the initial conditions required
        to define ``Sin(x^n)`` are not the first 3 but further::

            sage: all(Sin(x^i).is_fully_defined for i in range(1,10))
            True
            sage: Sin(x^4).init(20, True) == [sin(x^4).derivative(i)(x=0) for i in range(20)]
            True

        This method can throw some error when the input evaluates to something different than zero::

            sage: Sin(x+1)
            Traceback (most recent call last):
            ...
            ZeroValueRequired: required a zero value for x + 1 in sin(x + 1)
            sage: Sin(Exp(x))
            Traceback (most recent call last):
            ...
            ZeroValueRequired: required a zero value for exp(x)
    '''
    if(is_DDFunction(input)):
        return Sin(x)(input)
    f,dR = __decide_parent(input, ddR)
    
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(f) != 0):
        raise ZeroValueRequired(repr(input), "sin(%s)" %repr(input))
    
    df = dR.base_derivation(f)
    df2 = dR.base_derivation(df)
    
    newName = repr(f)
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name
    
    sol = dR.element([df**3 ,-df2,df],[0,evaluate(df),evaluate(df2)], name=DynamicString("sin(_1)", newName))
    if(not sol.is_fully_defined):
        return Sin(x)(input)
    return sol

@cached_function    
def Cos(input, ddR = None):
    r'''
        D-finite implementation of the Cosine function (`\cos(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` instance 
        of a cosine-type function. For more information about the cosine function, consult the following references:

        * :wolf:`Cosine`
        * :wiki:`Cosine`
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the cosine function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition will 
              be computed. The function must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.                

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: Cos(x).init(10, True)
            [1, 0, -1, 0, 1, 0, -1, 0, 1, 0]
            sage: Cos(x)[0]
            1
            sage: Cos(x)[1]
            0
            sage: Cos(x)[2]
            1
            sage: Cos(x).derivative() == -Sin(x)
            True
            sage: Cos(x).derivative(times=2) == -Cos(x)
            True
            sage: Sin(x)^2 + Cos(x)^2 == 1
            True
            sage: polys = [QQ[x](x*(x-1)), QQ[x](x*(x-3)*(x+1)), QQ[x](x*(x-2/3)*(x+10)*(x-1)),
            ....: QQ[x](x*(x-1)^2*(x+3)^2)]
            sage: # checking the method with polynomial input
            sage: for p in polys:
            ....:     l1 = Cos(p).init(10, True)
            ....:     l2 = [cos(p).derivative(i)(x=0) for i in range(10)]
            ....:     if(not l1 == l2):
            ....:         print(p)
            sage: # checking composition with polynomial coefficients
            sage: for p in polys:
            ....:     l1 = (Cos(x)(p)).init(10, True)
            ....:     l2 = [cos(p).derivative(i)(x=0) for i in range(10)]
            ....:     if(not l1 == l2):
            ....:         print(p)
            sage: Cos(2*x) == Cos(x)^2 - Sin(x)^2
            True
            sage: Cos(2*x).init(10, True) == [cos(2*x).derivative(i)(x=0) for i in range(10)]
            True

        We can also check identities with complex exponential::

            sage: I = DFiniteI.base_ring().gens()[0]; X = DFiniteI.variables()[0]
            sage: Exp(I*X) + Exp(-I*X) == 2*Cos(x)
            True
            sage: Cos(x) == Cosh(I*X)
            True

        Due to the nature of this implementation, the case for `x^n` for `n > 2` must 
        be treated as functions instead of computing directly the function. The 
        key here is that for that kind of input, the initial conditions required
        to define ``Cos(x^n)`` are not the first 3 but further::

            sage: all(Cos(x^i).is_fully_defined for i in range(1,10))
            True
            sage: Cos(x^4).init(20, True) == [cos(x^4).derivative(i)(x=0) for i in range(20)]
            True

        This method can throw some error when the input evaluates to something different than zero::

            sage: Cos(x+1)
            Traceback (most recent call last):
            ...
            ZeroValueRequired: required a zero value for x + 1 in cos(x + 1)
            sage: Cos(Exp(x))
            Traceback (most recent call last):
            ...
            ZeroValueRequired: required a zero value for exp(x)
    '''
    if(is_DDFunction(input)):
        return Cos(x)(input)
    f,dR = __decide_parent(input, ddR)
    
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(f) != 0):
        raise ZeroValueRequired(repr(input), "cos(%s)" %repr(input))
    
    df = dR.base_derivation(f)
    df2 = dR.base_derivation(df)
    
    newName = repr(f)
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name
    
    sol = dR.element([df**3 ,-df2,df], [1,0,-evaluate(df)**2 ], name=DynamicString("cos(_1)",newName))
    if(not sol.is_fully_defined):
        return Cos(x)(input)
    return sol
    
@cached_function
def Tan(input, ddR = None):
    r'''
        DD-finite implementation of the Tangent function (`\tan(x)`).

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a tangent-type function. For more
        information about the tangent function, consult the following references:

        * :wolf:`Tangent`
        * :wiki:`Tangent`
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the tangent function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition will 
              be computed. The function must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: Tan(x).init(10, True)
            [0, 1, 0, 2, 0, 16, 0, 272, 0, 7936]
            sage: Tan(x)[0]
            -2
            sage: Tan(x)[1]
            0
            sage: Tan(x)[2]
            (cos(x))^2
            sage: is_DDFunction(Tan(x)[2])
            True
            sage: Tan(x)[2] == Cos(x)^2
            True
            sage: Tan(x) == Sin(x)/Cos(x)
            True
            sage: Tan(x).derivative() == 1/(Cos(x)^2)
            True
            sage: Tan(x).derivative() == 1 + Tan(x)^2 # long time (> 1 min)
            True
            sage: polys = [QQ[x](x*(x-1)), QQ[x](x*(x-3)*(x+1)), QQ[x](x*(x-2/3)*(x+10)*(x-1)),
            ....: QQ[x](x*(x-1)^2*(x+3)^2)]
            sage: # checking the object with polynomial coefficients
            sage: for p in polys:
            ....:     l1 = Tan(p).init(10, True)
            ....:     l2 = [tan(p).derivative(i)(x=0) for i in range(10)]
            ....:     if(not l1 == l2):
            ....:         print(p)
            sage: # checking the composition with polynomial coefficients
            sage: for p in polys:
            ....:     l1 = (Tan(x)(p)).init(10, True)
            ....:     l2 = [tan(p).derivative(i)(x=0) for i in range(10)]
            ....:     if(not l1 == l2):
            ....:         print(p)
    '''
    if(is_DDFunction(input)):
        return Tan(x)(input)
    g, dR = __decide_parent(input, ddR,2 )
    
    
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute tan(f) with f(0) != 0")
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg)
    a = Cos(input)**2 ; b = dR.base().zero(); c = dR.base()(-2 )
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([dg**3 *c,dg**2 *b-ddg*a,dg*a]).equation
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1]
    else:
        required = newOperator.get_jp_fo()+1
            
        init_tan = Tan(x).init(required, True)
        init_input = [factorial(i)*dR.sequence(g,i) for i in range(required)]
            
        newInit = [init_tan[0]]+[sum([init_tan[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)] ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit)
    
    newName = repr(input)
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name
    
    result._DDFunction__name = DynamicString("tan(_1)",newName)
    return result

@cached_function    
def Sinh(input, ddR = None):
    r'''
        D-finite implementation of the Hyperbolic Sine function (`\sinh(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a hyperbolic sine-type function. For more
        information about the hyperbolic sine, consult the following references:

        * :wolf:`HyperbolicSine`
        * :wiki:`Hyperbolic_function`
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the hyperbolic sine function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition 
              will be computed. This function must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: s = Sinh(x); c = Cosh(x)
            sage: s[0]
            -1
            sage: s[1]
            0
            sage: s[2]
            1
            sage: s.init(10, True) # initial values
            [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
            sage: # checking derivatives
            sage: s.derivative() == c
            True
            sage: s.derivative(times=2) == s
            True
            sage: # checking definition by exponential
            sage: s == (Exp(x) - Exp(-x))/2
            True
            sage: s == (1 - Exp(-2*x))/(2*Exp(-x))
            True
            sage: s == (Exp(2*x) - 1)/(2*Exp(x))
            True
            sage: # checking relations
            sage: Sinh(-x) == -Sinh(x)
            True
            sage: s + c == Exp(x)
            True
            sage: c - s == Exp(-x)
            True
            sage: c^2-s^2 == 1
            True
            sage: # checking the addition formulas
            sage: Sinh(2*x) == 2*s*c
            True
            sage: Sinh(3*x) == s^3 + 3*s*c^2
            True
    '''
    if(is_DDFunction(input)):
        return Sinh(x)(input)
    f,dR = __decide_parent(input, ddR)
    
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(f) != 0):
        raise ValueError("Impossible to compute sin(f) with f(0) != 0")
    
    df = dR.base_derivation(f)
    df2 = dR.base_derivation(df)
    
    newName = repr(f)
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name
    
    return dR.element([-df**3 ,-df2,df],[0,evaluate(df),evaluate(df2)], name=DynamicString("sinh(_1)",newName))

@cached_function    
def Cosh(input, ddR = None):
    r'''
        D-finite implementation of the Hyperbolic Cosine function (`\cosh(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a hyperbolic cosine-type function. For more
        information about the hyperbolic cosine, consult the following references:

        * :wolf:`HyperbolicCosine`
        * :wiki:`Hyperbolic_function`
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the hyperbolic cosine function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition 
              will be computed. This function must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: s = Sinh(x); c = Cosh(x)
            sage: c[0]
            -1
            sage: c[1]
            0
            sage: c[2]
            1
            sage: c.init(10, True) # initial values
            [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
            sage: # checking derivatives
            sage: c.derivative() == s
            True
            sage: c.derivative(times=2) == c
            True
            sage: # checking definition by exponential
            sage: c == (Exp(x) + Exp(-x))/2
            True
            sage: c == (1 + Exp(-2*x))/(2*Exp(-x))
            True
            sage: c == (Exp(2*x) + 1)/(2*Exp(x))
            True
            sage: # checking relations
            sage: Cosh(-x) == Cosh(x)
            True
            sage: s + c == Exp(x)
            True
            sage: c - s == Exp(-x)
            True
            sage: c^2-s^2 == 1
            True
            sage: # checking the addition formulas
            sage: Cosh(2*x) == s^2 + c^2
            True
            sage: Cosh(3*x) == c^3 + 3*c*s^2
            True
    '''
    if(is_DDFunction(input)):
        return Cosh(x)(input)
    f,dR = __decide_parent(input, ddR)
    
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(f) != 0):
        raise ValueError("Impossible to compute cos(f) with f(0) != 0")
    
    df = dR.base_derivation(f)
    df2 = dR.base_derivation(df)
    
    newName = repr(f)
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name
    
    return dR.element([-df**3 ,-df2,df],[1,0,evaluate(df)**2 ], name=DynamicString("cosh(_1)", newName))

@cached_function
def Tanh(input, ddR = None):
    r'''
        DD-finite implementation of the Hyperbolic Tangent function (`\tanh(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a hyperbolic tangent-type function. For more
        information about the hyperbolic tangent, consult the following references:

        * :wolf:`HyperbolicTangent`
        * :wiki:`Hyperbolic_function`
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the hyperbolic tangent function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition 
              will be computed. The DDFunction must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions.ddExamples import Sinh, Cosh, Tanh, Exp
            sage: s = Sinh(x); c = Cosh(x); t = Tanh(x)
            sage: t[0]
            2
            sage: t[1]
            0
            sage: t[2]
            (cosh(x))^2
            sage: t.init(10, True) # initial values
            [0, 1, 0, -2, 0, 16, 0, -272, 0, 7936]
            sage: # checking derivatives
            sage: t.derivative() == 1-t^2
            True
            sage: t.derivative() == 1/(c^2)
            True
            sage: # checking definition by exponential
            sage: t == s/c
            True
            sage: t == (Exp(x) - Exp(-x))/(Exp(x) + Exp(-x))
            True
            sage: t == (Exp(2*x)-1)/(Exp(2*x)+1)
            True
            sage: # checking relations
            sage: Tanh(-x) == -Tanh(x)
            True
    '''
    if(is_DDFunction(input)):
        return Tanh(x)(input)
    g, dR = __decide_parent(input, ddR,2 )
    
    
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute tan(f) with f(0) != 0")
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg)
    a = Cosh(input)**2
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([2*dg**3, -ddg*a, dg*a]).equation
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1]
    else:
        required = newOperator.get_jp_fo()+1
            
        init_tanh = Tanh(x).init(required, True)
        init_input = [factorial(i)*dR.sequence(g,i) for i in range(required)]
            
        newInit = [init_tanh[0]]+[sum([init_tanh[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)] ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit)
    
    newName = repr(input)
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name
    
    result._DDFunction__name = DynamicString("tanh(_1)",newName)
    return result

@cached_function
def Arcsin(input, ddR = None):
    r'''
        D-finite implementation of the inverse sine function (`\arcsin(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a arcsine-type function. For more
        information about the inverse sine function, consult the following references:

        * :wolf:`InverseSine`
        * :wiki:`Inverse_trigonometric_functions`
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the inverse sine function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition 
              will be computed. The DDFunction must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: arcsin = Arcsin(x); arcsin
            arcsin(x)
            sage: arcsin[0]
            0
            sage: arcsin[1]
            -x
            sage: arcsin[2]
            -x^2 + 1
            sage: arcsin.init(10, True)
            [0, 1, 0, 1, 0, 9, 0, 225, 0, 11025]
            sage: # cheking identities with trigonometric functions
            sage: Sin(arcsin).sequence(10, True) # sin(arcsin(x)) == x
            [0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
            sage: (Cos(arcsin)^2).sequence(10, True) # cos(arcsin(x))^2 = 1 - x^2
            [1, 0, -1, 0, 0, 0, 0, 0, 0, 0]
            sage: # checking identities with derivatives
            sage: (1-x^2)*arcsin.derivative()^2 == 1
            True
            sage: Arcsin(-x) == -arcsin
            True
    '''
    if(is_DDFunction(input)):
        return Arcsin(x)(input)
    g, dR = __decide_parent(input, ddR)
        
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arcsin(f) with f(0) != 0")
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg)
    a = dR.base().zero(); b = -(ddg*(1-g**2) + g*dg**2); c = (1-g**2)*dg
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([a,b,c]).equation
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1]
    else:
        required = newOperator.get_jp_fo()+1
            
        init_arcsin = Arcsin(x).init(required, True)
        init_input = [factorial(i)*dR.sequence(g,i) for i in range(required)]
            
        newInit = [init_arcsin[0]]+[sum([init_arcsin[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)] ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit)
    newName = repr(input)
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name
    
    result._DDFunction__name = DynamicString("arcsin(_1)",newName)
    
    return result

@cached_function
def Arccos(input, ddR = None):
    r'''
        D-finite implementation of the inverse cosine function (`\arccos(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a arccosine-type function. For more
        information about the inverse cosine function, consult the following references:

        * :wolf:`InverseCosine`
        * :wiki:`Inverse_trigonometric_functions`
            
        Since the default initial conditions for `\arccos(x)` is `\pi/2`, this method
        extends the DFinite ring with a parameter called ``"pi"``. Since `\pi` is a
        transcendental number, this implementation works without any issue. However
        it implies some unnecessary performance difficulties when computing with
        this function, since::

            sage: from ajpastor.dd_functions.ddExamples import *
            sage: arccos = Arccos(x); pi = arccos.parent().parameters()[0]
            sage: arccos - pi/2 == Arcsin(-x)
            True
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the inverse cosine function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition 
              will be computed. The DDFunction must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: arccos = Arccos(x); arccos
            arccos(x)
            sage: arccos[0]
            0
            sage: arccos[1]
            -x
            sage: arccos[2]
            -x^2 + 1
            sage: arccos.init(10, True)
            [1/2*pi, -1, 0, -1, 0, -9, 0, -225, 0, -11025]
            sage: # cheking identities with trigonometric functions
            sage: Sin(arccos - pi/2) == -x # cos(arccos(x)) = x
            True
            sage: Cos(arccos - pi/2)^2 == 1 - x^2
            True
            sage: Arccos(-x) == pi - arccos
            True
            sage: # checking identities with derivatives
            sage: arccos.derivative() == -Arcsin(x).derivative()
            True
    '''
    if(is_DDFunction(input)):
        return Arccos(x)(input)
    g, dR = __decide_parent(input, ddR)
    dR = ParametrizedDDRing(dR, 'pi'); pi = dR.parameter('pi')
        
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arccos(f) with f(0) != 0")
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg)
    a = dR.base().zero(); b = -(ddg*(1-g**2) + g*dg**2); c = (1-g**2)*dg
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([a,b,c]).equation
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [pi/ZZ(2),-1]
    else:
        required = newOperator.get_jp_fo()+1
            
        init_arccos = Arccos(x).init(required, True)
        init_input = [factorial(i)*dR.sequence(g,i) for i in range(required)]
            
        newInit = [init_arccos[0]]+[sum([init_arccos[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)] ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit)
    newName = repr(input)
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name
    
    result._DDFunction__name = DynamicString("arccos(_1)",newName)
    
    return result

@cached_function
def Arctan(input, ddR = None):
    r'''
        D-finite implementation of the inverse tangent function (`\arctan(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a arctangent-type function. For more
        information about the inverse tangent function, consult the following references:

        * :wolf:`InverseTangent`
        * :wiki:`Inverse_trigonometric_functions`
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the inverse tangent function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition 
              will be computed. The DDFunction must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions.ddExamples import Arctan
            sage: arctan = Arctan(x); arctan
            arctan(x)
            sage: arctan[0]
            0
            sage: arctan[1]
            2*x
            sage: arctan[2]
            x^2 + 1
            sage: arctan.init(10, True)
            [0, 1, 0, -2, 0, 24, 0, -720, 0, 40320]
            sage: Arctan(-x) == -arctan
            True
            sage: # cheking identities with trigonometric functions
            sage: from ajpastor.dd_functions.ddExamples import Sin, Cos
            sage: Sin(arctan)^2 == x^2/(1+x^2) # long time (> 1 min)
            True
            sage: Cos(arctan)^2 == 1/(1 + x^2) # long time (> 1 min)
            True
            sage: # checking identities with derivatives
            sage: arctan.derivative() == 1/(1+x^2)
            True
    '''
    if(is_DDFunction(input)):
        return Arctan(x)(input)
    g, dR = __decide_parent(input, ddR)
        
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arctan(f) with f(0) != 0")
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg)
    a = dR.base().zero(); b = (2*g*dg**2 - (1+g**2)*ddg); c = (1+g**2)*dg
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([a,b,c]).equation
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1]
    else:
        required = newOperator.get_jp_fo()+1
            
        init_arctan = Arctan(x).init(required, True)
        init_input = [factorial(i)*dR.sequence(g,i) for i in range(required)]
            
        newInit = [init_arctan[0]]+[sum([init_arctan[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)] ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit)
    
    newName = repr(input)
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name
    
    result._DDFunction__name = DynamicString("arctan(_1)",newName)
    return result

@cached_function 
def Arcsinh(input, ddR = None):
    r'''
        D-finite implementation of the inverse hyperbolic sine function (`arcsinh(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a hyperbolic arcsine-type function. For more
        information about the inverse hyperbolic sine function, consult the following references:

        * :wolf:`InverseHyperbolicSine`
        * :wiki:`Inverse_hyperbolic_functions`

        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the inverse hyperbolic sine function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition 
              will be computed. The DDFunction must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: arcsinh = Arcsinh(x); arcsinh
            arcsinh(x)
            sage: arcsinh[0]
            0
            sage: arcsinh[1]
            x
            sage: arcsinh[2]
            x^2 + 1
            sage: arcsinh.init(10, True)
            [0, 1, 0, -1, 0, 9, 0, -225, 0, 11025]
            sage: # cheking identities with logarithmic function
            sage: g = DAlgebraic(QQ[x]['y']('y^2 - x^2-1'), [1,0]) # g = sqrt(x^2+1)
            sage: h.init(100,True) == arcsinh.init(100,True)
            True
            sage: arcsinh == Log(x+g) # long time (> 1 min)
            True
            sage: arcsinh.derivative()^2*(1+x^2) == 1 
            True
    '''
    if(is_DDFunction(input)):
        return Arcsinh(x)(input)
    g, dR = __decide_parent(input, ddR)
        
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arcsinh(f) with f(0) != 0")
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg); a = g**2+1
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([dR.base().zero(),(g*dg**2 - ddg*a),dg*a]).equation
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1]
    else:
        required = newOperator.get_jp_fo()+1
            
        init_arcsinh = Arcsinh(x).init(required, True)
        init_input = [factorial(i)*dR.sequence(g,i) for i in range(required)]
            
        newInit = [init_arcsinh[0]]+[sum([init_arcsinh[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)] ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit)
    newName = repr(input)
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name
    
    result._DDFunction__name = DynamicString("arcsinh(_1)",newName)
    
    return result

@cached_function
def Arccosh(input, ddR = None):
    r'''
        D-finite implementation of the inverse hyperbolic cosine function (`arccosh(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a hyperbolic arccosine-type function. For more
        information about the inverse hyperbolic cosine function, consult the following references:

        * :wolf:`InverseHyperbolicCosine`
        * :wiki:`Inverse_hyperbolic_functions`

        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the inverse hyperbolic cosine function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition 
              will be computed. The DDFunction must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: arccosh = Arccosh(x); arccosh
            arccosh(x)
            sage: arccosh[0]
            0
            sage: arccosh[1]
            x
            sage: arccosh[2]
            x^2 - 1
            sage: arccosh.init(10, True)
            [1/2*I*pi, -I, 0, -I, 0, -9*I, 0, -225*I, 0, -11025*I]
            sage: arccosh.derivative()^2*(x^2-1) == 1 
            True
    '''
    if(is_DDFunction(input)):
        return Arccosh(x)(input)

    # Forcing "I" to exists in the final ring
    if(ddR is None): ddR = DFiniteI
    else: ddR = pushout(ddR, DFiniteI)
    g, dR = __decide_parent(input, ddR)
    I = DFiniteI.coeff_field.gens()[0]

    # Adding "pi" as a parameter
    dR = ParametrizedDDRing(dR, 'pi'); pi = dR.parameter('pi')
        
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arccosh(f) with f(0) != 0")
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg); a = g**2-1
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([dR.base().zero(),(g*dg**2 - ddg*a),dg*a]).equation
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [I*pi/2,-I]
    else:
        required = newOperator.get_jp_fo()+1
            
        init_arccosh = Arccosh(x).init(required, True)
        init_input = [factorial(i)*dR.sequence(g,i) for i in range(required)]
            
        newInit = [init_arccosh[0]]+[sum([init_arccosh[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)] ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit)
    newName = repr(input)
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name
    
    result._DDFunction__name = DynamicString("arccosh(_1)",newName)
    
    return result

@cached_function 
def Arctanh(input, ddR = None):
    r'''
        D-finite implementation of the inverse hyperbolic tangent function (`arctanh(x)`).
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a hyperbolic arctangent-type function. For more
        information about the inverse hyperbolic tangent function, consult the following references:

        * :wolf:`InverseHyperbolicTangent`
        * :wiki:`Inverse_hyperbolic_functions`

        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the inverse hyperbolic tangent function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression with `x` as a factor.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must be divisible by the main 
              variable.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition 
              will be computed. The DDFunction must have initial value 0.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: arctanh = Arctanh(x); arctanh
            arctanh(x)
            sage: arctanh[0]
            0
            sage: arctanh[1]
            -2*x
            sage: arctanh[2]
            -x^2 + 1
            sage: arctanh.init(10, True)
            [0, 1, 0, 2, 0, 24, 0, 720, 0, 40320]
            sage: arctanh.derivative()*(1-x^2) == 1 
            True
            sage: 2*arctanh == Log(DFinite((1+x)/(1-x)))
            True
            sage: i = DFiniteI.coeff_field.gens()[0]; x = DFiniteI.variable('x')
            sage: Arctan(i*x) == i*arctanh
            True
    '''
    if(is_DDFunction(input)):
        return Arctanh(x)(input)
    g, dR = __decide_parent(input, ddR)
        
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arctanh(f) with f(0) != 0")
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg); a = 1-g**2
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([dR.base().zero(), -(ddg*a + g*dg**2*2), dg*a]).equation
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1]
    else:
        required = newOperator.get_jp_fo()+1
            
        init_arctanh = Arctanh(x).init(required, True)
        init_input = [factorial(i)*dR.sequence(g,i) for i in range(required)]
            
        newInit = [init_arctanh[0]]+[sum([init_arctanh[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)] ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit)
    
    newName = repr(input)
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name
    
    result._DDFunction__name = DynamicString("arctanh(_1)",newName)
    return result

##################################################################################
##################################################################################
###
### Exponential and Logarithm Functions
###
##################################################################################
##################################################################################   
@cached_function  
def Log(input, ddR = None):
    r'''
        DD-finite implementation of the logarithm function (`\log(x+1)`).

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a logarithm-type function. For more
        information about the logarithm function, consult the following references:

        * :wolf:`Logarithm`
        * :wiki:`Logarithm`
        * :funtop:`Natural_logarithm`
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the logarithm function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression evaluating to `1` when `x=0`.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must evaluate to `1` when
              the main variable is `0`.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition will 
              be computed. The function must have initial value 1.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: log = Log(x+1)
            sage: log.init(10, True)
            [0, 1, -1, 2, -6, 24, -120, 720, -5040, 40320]
            sage: log[0]
            0
            sage: log[1]
            1
            sage: log[2]
            x + 1
            sage: (x+1)*log.derivative() == 1
            True

        This package allows to check that `log(x)` is the functional inverse of 
        the exponential function (see :func:`Exp`)::

            sage: Exp(log) == x+1
            True
            sage: log(Exp(x)-1) == x
            True

        We can also check some basic properties from the Logarithm::

            sage: log + log == Log((x+1)^2)
            True
            sage: Log(x^3 + 4*x^2 + 4*x + 1) - Log(x+1) == Log(x^2 + 3*x + 1)
            True
            sage: log == -Log(DFinite(1/(x+1)))
    '''
    if(is_DDFunction(input)):
        return Log(x+1)(input-1)
    f,dR = __decide_parent(input, ddR)
    
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(f) != 1):
        raise ValueError("Impossible to compute ln(f) with f(0) != 1")
    
    df = dR.base_derivation(f)
    df2 = dR.base_derivation(df)
    
    newName = repr(f)
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name
    
    return dR.element([0,df**2 -df2*f,df*f],[0,evaluate(df), evaluate(df2)-evaluate(df)**2 ], name=DynamicString("log(_1)",newName))
    
@cached_function 
def Log1(input, ddR = None):
    r'''
        Alias or ``Log(input + 1, ddR)``. See method :func:`Log` for further information.
    '''
    return Log(input+1, ddR)
    
@cached_function 
def Exp(input, ddR = None):
    r'''
        DD-finite implementation of the exponential function (`e^x`).

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a exponential-type function. For more
        information about the exponential function, consult the following references:

        * :wolf:`ExponentialFunction`
        * :wiki:`Exponential_function`
        * :funtop:`Exponential_function`
            
        This function can be converted into symbolic expressions.

        INPUT:

        * ``input``: a valid input for the exponential function. Namely:
            * A symbolic expression: all variables but `x` will be considered as 
              parameters. Must be a polynomial expression evaluating to `1` when `x=0`.
            * A polynomial: the first generator of the polynomial ring will be 
              considered the variable to compute derivatives and the rest will be 
              considered as parameters. The polynomial must evaluate to `1` when
              the main variable is `0`.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDFunction`: the composition will 
              be computed. The function must have initial value 1.
        * ``ddR``: a :class:`~ajpastor.dd_functions.ddFunction.DDRing` where we want to 
          embed the output. If this is not enough for representing the function, a bigger
          :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: exp = Exp(x)
            sage: exp.init(10, True)
            [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
            sage: exp[0]
            -1
            sage: exp[1]
            1
            sage: exp.derivative() == exp
            True

        We can check that the `log(x+1)` is the functional inverse of `e^x` (see :func:`Log`)::

            sage: Log(x+1)(exp(x)-1) == x
            True
            sage: exp(Log(x+1)) == x+1
            True

        Also, we can check the multiplicative properties of the exponential with some examples::

            sage: exp^2 == Exp(2*x)
            True
            sage: Exp(x+1) * Exp(x+2) == Exp(2*x+3)
            True
        
        The exponential function is closely related with the trigonometric functions (see
        :func:`Sin`, :func:`Cos`, :func:`Tan`, :func:`Sinh`, :func:`Cosh`, :func:`Tanh`)::

            sage: i = DFiniteI.coeff_field.gens()[0]; x = DFiniteI.variable('x')
            sage: Exp(x) == Cosh(x) + Sinh(x)
            True
            sage: Exp(i*x) == Cos(x) + i*Sin(x)
            True
            sage: 2*Sin(x) == i*(Exp(-i*x) - Exp(i*x))
            True
            sage: 2*Cos(x) == (Exp(-i*x) + Exp(i*x))
            True

        The exponential function can also be seen as a hypergeometric function, more precisely,
        the exponential is the `_0F_0(x)` function::

            sage: Exp(x) == F00()
            True
    '''
    if(is_DDFunction(input)):
        return Exp(x)(input)
    f,dR = __decide_parent(input, ddR)
    
    evaluate = lambda p : dR.sequence(p,0)
    if(evaluate(f) != 0):
        raise ValueError("Impossible to compute exp(f) with f(0) != 0")
    
    newName = repr(f)
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name
        
    return dR.element([-dR.base_derivation(f),1],[1], name=DynamicString("exp(_1)", newName))

##################################################################################
##################################################################################
###
### Special Functions
###
##################################################################################
##################################################################################    
##### BESSEL TYPE FUNCTIONS
### Bessel Functions
@cached_function 
def BesselJ(n = 'n'):
    r'''
        DD-finite implementation of the first kind Bessel function (`J_n(x)`).

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a bessel function of the first kind. For more
        information about the Bessel function, consult the following references:

        * :wolf:`BesselFunctionoftheFirstKind`
        * :wiki:`Bessel_function`
        * :funtop:`Bessel_functions`
            
        This function can be converted into symbolic expressions.

        The Bessel functions are those satisfying the following differential equation:

        .. MATH::

            x^2 f''(x) + xf'(x) + (x^2 - n^2)f(x) = 0,

        where `n` is a constant parameter. Since the base of this package is to 
        work with formal power series, we can not represent any bessel function
        of second kind (i.e., singular at `x=0`) nor a bessel function with fractional 
        parameter.

        However, we allow the parameter to be a string (name for the parameter)
        instead of an integer to manipulate the generic operator.

        INPUT:
        
        - `n`: a non-negative integer or a string (that will be taken as name 
          of a parameter).

        OUTPUT:

        The :class:`~ajpastor.dd_function.DDFunction` representing the corresponding
        bessel function of the first kind.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: BesselJ(3)
            bessel_J(3, x)
            sage: BesselJ(3).init(3, True)
            [0, 0, 0]

        Bessel functions satisfies several identities when varying the parameters
        (see :funent:`d56914`)::

            sage: all(
            ....: BesselJ(n) == (x/(2*n))*(BesselJ(n-1) + BesselJ(n+1))
            ....: for n in range(1,20,3))
            True

        Bessel functions of first kind also have a representation using a 
        hypergeometric function (see :funent:`ecd36f`). Remark than this
        identity uses the *regularized hypergeometric function*, meaning 
        that we have to divide by the factorials of the low-rank arguments
        of the hypergeometric function::

            sage: all(
            ....: BesselJ(n) == (x/2)**n*(F01(n+1)(-(x**2)/4)/factorial(n))
            ....: for n in range(20))
            True
    '''
    parent, n = __check_list([n], DFinite.variables())
    n = n[0]
        
    if(parent is QQ):
        parent = DFinite
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
        n = parent.base()(n)
    x = parent.variables()[0]
        
    func = parent.element([x**2-n**2, x, x**2], name=DynamicString("bessel_J(_1,_2)", [repr(n),"x"]))
    if(n in ZZ):
        alpha = ZZ(n)
        func = func.change_init_values([0 for i in range(alpha)] + [1/ZZ(2) **alpha, 0, -((alpha+2)/(2**(alpha+2)))], name = func._DDFunction__name)
    
    return func

@cached_function 
def BesselI(n = 'n'):
    r'''
        DD-finite implementation of the modified first kind Bessel function (`I_n(x)`).

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a modified bessel function of the first kind. For more
        information about the Bessel function, consult the following references:

        * :wolf:`ModifiedBesselFunctionoftheFirstKind`
        * :wiki:`Bessel_function`
        * :funtop:`Bessel_functions`
            
        This function can be converted into symbolic expressions.

        The modified Bessel functions are those satisfying the following differential equation:

        .. MATH::

            x^2 f''(x) + xf'(x) - (x^2 + n^2)f(x) = 0,

        where `n` is a constant parameter. Since the base of this package is to 
        work with formal power series, we can not represent any bessel function
        of second kind (i.e., singular at `x=0`) nor a bessel function with fractional 
        parameter.

        However, we allow the parameter to be a string (name for the parameter)
        instead of an integer to manipulate the generic operator.

        The modified Bessel function is a simple transform with complex numbers to the 
        usual Bessel function of the first kind, obtaining a formal power series
        anytime the original Bessel function was a formal power series. Namely:

        .. MATH::

            I_n(x) = i^{-n}J_n(ix).

        INPUT:
        
        - `n`: a non-negative integer or a string (that will be taken as name 
          of a parameter).

        OUTPUT:

        The :class:`~ajpastor.dd_function.DDFunction` representing the corresponding
        modified bessel function of the first kind.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: BesselI(3)
            bessel_I(3, x)
            sage: BesselI(3).init(3, True)
            [0, 0, 0]
            sage: BesselI(5).init(10, True) == [bessel_I(5,x).derivative(i)(x=0) for i in range(10)]
            True

        We can check for different parameters values its relation with the usual 
        Bessel function (see :func:`BesselJ`)::

            sage: I = DFiniteI.coeff_field('I')
            sage: X = DFiniteI.variable('x')
            sage: all(
            ....: BesselI(n) == (I**(-n)*BesselJ(n)(I*X))
            ....: for n in range(20))
            True

        Bessel functions satisfies several identities when varying the parameters
        (see :funent:`d56914`)::

            sage: all(
            ....: BesselI(n) == (x/(2*n))*(BesselI(n-1) - BesselI(n+1))
            ....: for n in range(1,20,3))
            True

        Modified Bessel functions of first kind also have a representation using a 
        hypergeometric function (see :funent:`ecd36f`). Remark than this
        identity uses the *regularized hypergeometric function*, meaning 
        that we have to divide by the factorials of the low-rank arguments
        of the hypergeometric function::

            sage: all(
            ....: BesselI(n) == (x/2)**n*(F01(n+1)(x**2/4)/factorial(n))
            ....: for n in range(20))
            True
    '''
    parent, n = __check_list([n], DFinite.variables())
    n = n[0]
        
    if(parent is QQ):
        parent = DFinite
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
        n = parent.base()(n)
    x = parent.variables()[0]
        
    func = parent.element([-(x**2+n**2), x, x**2], name=DynamicString("bessel_I(_1,_2)", [repr(n),"x"]))
    if(n in ZZ):
        alpha = ZZ(n)
        func = func.change_init_values([0 for i in range(alpha)] + [1/ZZ(2) **alpha, 0, ((alpha+2)/(2**(alpha+2)))], name = func._DDFunction__name)
    
    return func
    
### Struve's functions
@cached_function
def StruveH(n='n'):
    r"""
        DD-finite implementation of the Struve function of first kind (`H_n(x)`).

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a Struve function of the first kind. For more
        information about the Struve functions, consult the following references:

        * :dlmf:`11.2`
        * :wolf:`StruveFunction`
        * :wiki:`Struve_function`
        
        The Struve functions are those satisfying the following inhomogeneous differential equation:

        .. MATH::

            x^2 H_n''(x) + xH_n'(x) + (x^2 - n^2)H_n(x) = \frac{(2x)^{n+1}n!}{(2n)!\pi},

        where `n` is a constant parameter. Since the base of this package is to 
        work with formal power series, we can not represent any Struve function
        of second kind (i.e., singular at `x=0`) nor a Struve function with fractional 
        parameter.

        To avoid the use of `\pi` as a parameter in these functions, we instead create the 
        standardized Struve function `h_n(x) = \piH_n(x)`.

        We allow the parameter to be a string (name for the parameter)
        instead of an integer to manipulate the generic operator.

        This inhomogeneous equation can be easily transformed into a homogeneous equation
        more fitting for the content of this package. The resulting differential equation is:

        .. MATH::

            x^3 h_n'''(x) + (2-n)x^2h_n''(x) + x(x^2 - n(n+1))h_n'(x) + ((1-n)x^2 + n^2(n+1))h_n(x) = 0.

        Then the first nonzero initial value for each of these functions (when `n` is a non-negative
        integer) is the `(n+1)`-th element with the formula:

        .. MATH::

            h_n^{(n+1)}(0) = \frac{2^{n+1}n!(n+1)!}{(2n+1)!}

        INPUT:
        
        - `n`: a non-negative integer or a string (that will be taken as name 
          of a parameter).

        OUTPUT:

        The :class:`~ajpastor.dd_function.DDFunction` representing the corresponding
        Struve function of the first kind.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: StruveH(3)
            pi*struve_H(3, x)
            sage: StruveH(3).init(5, True)
            [0, 0, 0, 0, 16/35]

        Similarly to the Bessel functions (see :func:`BesselJ`), the Struve functions of
        first kind satisfy some relations when considering `\pm 1` elements::

            sage: all(
            ....: StruveH(n-1) + StruveH(n+1) == 2*n*StruveH(n)/x + (x^n * 2^(n+1) * factorial(n))/factorial(2*n+1)
            ....: for n in range(1,20))
            True
            sage: all(
            ....: StruveH(n-1) - StruveH(n+1) == 2*StruveH(n).derivative() - (x^n * 2^(n+1) * factorial(n))/factorial(2*n+1)
            ....: for n in range(1,20))
    """
    parent, n = __check_list([n], DFinite.variables())
    n = n[0]
        
    if(parent is QQ):
        parent = DFinite
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    f = parent.element([(1-n)*x**2+n**2*(n+1),x*(x**2-n**2-n),(2-n)*x**2,x**3], name=DynamicString("pi*struve_H(_1,_2)", [repr(n),"x"]))
    if(n in ZZ and n >= 0):
        val = 2**(n+1)*(factorial(n)*factorial(n+1))/ZZ(factorial(2*n+1))
        f = f.change_init_values([0 for _ in range(n+1)] + [val], name=f._DDFunction__name)
    
    return f

@cached_function
def StruveL(n='n'):
    r"""
        DD-finite implementation of the modified Struve function of first kind (`L_n(x)`).

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a modified Struve function of the first kind. For more
        information about the Struve functions, consult the following references:

        * :dlmf:`11.2`
        * :wolf:`StruveFunction`
        * :wiki:`Struve_function`
        
        The modified Struve functions are those satisfying the following inhomogeneous differential equation:

        .. MATH::

            x^2 L_n''(x) + xL_n'(x) - (x^2 + n^2)L_n(x) = \frac{(2x)^{n+1}n!}{(2n)!\pi},

        where `n` is a constant parameter. Since the base of this package is to 
        work with formal power series, we can not represent any Struve function
        of second kind (i.e., singular at `x=0`) nor a Struve function with fractional 
        parameter.

        To avoid the use of `\pi` as a parameter in these functions, we instead create the 
        standardized Struve function `l_n(x) = \pi L_n(x)`.

        We allow the parameter to be a string (name for the parameter)
        instead of an integer to manipulate the generic operator.

        This inhomogeneous equation can be easily transformed into a homogeneous equation
        more fitting for the content of this package. The resulting differential equation is:

        .. MATH::

            x^3 l_n'''(x) + (2-n)x^2l_n''(x) - x(x^2 + n(n+1))l_n'(x) + ((n-1)x^2 + n^2(n+1))l_n(x) = 0.

        Then the first nonzero initial value for each of these functions (when `n` is a non-negative
        integer) is the `(n+1)`-th element with the formula:

        .. MATH::

            h_n^{(n+1)}(0) = \frac{2^{n+1}n!(n+1)!}{(2n+1)!}

        INPUT:
        
        - `n`: a non-negative integer or a string (that will be taken as name 
          of a parameter).

        OUTPUT:

        The :class:`~ajpastor.dd_function.DDFunction` representing the corresponding
        modified Struve function of the first kind.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: StruveL(3)
            pi*struve_L(3, x)
            sage: StruveL(3).init(5, True)
            [0, 0, 0, 0, 16/35]

        We can check the relation between the Struve function and its modified version
        (see :func:`StruveH`)::

            sage: I = DFiniteI.coeff_field('I')
            sage: X = DFiniteI.variable('x')
            sage: all(
            ....: StruveL(n) == I**(-n-1)*StruveH(n)(I*X)
            ....: for n in range(20))
            True
    """
    parent, n = __check_list([n], DFinite.variables())
    n = n[0]
        
    if(parent is QQ):
        parent = DFinite
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    f = parent.element([(n - 1)*x**2 + n**3 + n**2,-x**3 + (-n**2 - n)*x,(-n + 2)*x**2,x**3], name=DynamicString("pi*struve_L(_1,_2)", [repr(n),"x"]))
    if(n in ZZ and n >= 0):
        val = 2**(n+1)*(factorial(n)*factorial(n+1))/ZZ(factorial(2*n+1))
        f = f.change_init_values([0 for _ in range(n+1)] + [val], name=f._DDFunction__name)
    
    return f


###### ORTHOGONAL POLYNOMIALS
### Legendre Polynomials 
def __init_value_associated_legendre(n,m,kind):
    S1_2 = ZZ(1)/ZZ(2)
    S2 = ZZ(2)
    S1 = ZZ(1)
    
    if(kind == 1):
        res = (2**m*sqrt(pi))/gamma((n-m)/S2 + S1)/gamma(S1_2-(n+m)/S2)
    else:
        res = -(S2**(m-S1)*sqrt(pi)*sin((S1_2)*(n+m)*pi))*gamma((n+m)/S2 + S1_2)/gamma((n-m)/S2 + S1)

    return res

def __first_derivative_associated_legendre(n,m,kind):
    S1_2 = ZZ(1)/ZZ(2)
    S2 = ZZ(2)
    S1 = ZZ(1)
    
    if(kind == 1):
        res = -(S2**(m+S1)*sqrt(pi))/gamma((n-m)/S2 + S1_2)/gamma(-(n+m)/S2)
    else:
        res = (S2**m*sqrt(pi)*cos((S1_2)*(n+m)*pi))*gamma((n+m)/S2 + S1)/gamma((n-m)/S2 + S1_2)

    return res

@cached_function 
def LegendreD(nu='n', mu = 0, kind=1):
    r'''
        TODO: Review this documentation
        D-finite implementation of the Legendre functions (P_n(x) and Q_n(x))
        
        References:
    - https://dlmf.nist.gov/18.3 & https://dlmf.nist.gov/14.2
    - https://en.wikipedia.org/wiki/Legendre_polynomials
    - http://mathworld.wolfram.com/LegendrePolynomial.html & http://mathworld.wolfram.com/LegendreFunctionoftheSecondKind.html
            
        Legendre functions are the solutions to the differential equation:
            (1-x^2)f'' - 2xf' + n(n+1)f = 0
        
        This equation has a parameter 'n'. When 'n' takes non-negative integer
        values, it has polynomial solutions, the so called Legendre polynomials (P_n(x)). 
        This family of polynomials is a orthogonal set of polynomials. In particular

        .. MATH:: 

            \int_{-1}^{1} P_n(x)P_m(x) = (2/(2n+1))\delta_{m,n}

        This set of polynomials (as any orthogonal family of polynomials), also satisfies
        a recursive relation:

        .. MATH::

            (n+1)P_{n+1}(x) = (2n+1)xP_n(x) - nP_{n-1}(x)
        
        The other solution are the Legendre functions of second kind (Q_n(x)). They also 
        satisfy the same recurrence relation as the Legendre polynomials. They are power series
        that converges from x=-1 to x=1.
        
        There is an associated differential equation with an extra parameter:

        .. MATH::

            (1-x^2)^2f'' - 2x(1-x^2)f' + (n(n+1)(1-x^2) - m^2)f = 0,

        that reduces to the original equation when m=0.
        
        This method allows the user to get the D-finite representation of the associated
        Legendre differential equation. 
        
        INPUT:
    - nu: the parameter 'n' on the associated differential equation. If not provided, ot takes the value 'n' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - mu: the parameter 'm' on the associated differential equation. If not provided, ot takes the value 0 by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - kind: the kind of the Legendre function the user want to get. It can take the values 1 and 2 (1 by default).
            
        WARNING:
    - Initial values will also be computed for the parameter values that have power series solutions. The second kind may have non-rational initial values and those will not be computed.
    - When evaluating parameters, the initial values will not update and must be set by hand.
    '''
    parent, par = __check_list([nu,mu], DFinite.variables())
    n = par[0]; m = par[1]
    
    ## Building the final parent
    if(parent is QQ):
        parent = DFinite
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    
    ## Building the final name
    x = parent.variables()[0]
    if(kind == 1): kind = "P"
    elif(kind == 2): kind = "Q"
    else: raise ValueError("Only Legendre functions of first and second kind are implemented. Got %s" %kind)

    if(m != 0):
        name = DynamicString("gen_legendre_%s(_1,_2,_3)" %kind, [repr(n), repr(m), repr(x)])
    else:
        name = DynamicString("legendre_%s(_1,_2)" %kind, [repr(n),repr(x)])
    
    ## Building the initial values
    init = []
    if((m == 0) and (n in ZZ) and (n >= 0)):
        try:
            init = [__init_value_associated_legendre(n,m,kind), __first_derivative_associated_legendre(n,m,kind)]
            if(any(el not in parent.coeff_field for el in init)):
                init = []
        except:
            pass
    ## Building the coefficients of the equation
    if(m == 0):
        coeffs = [(n*(n+1)),-2*x,1-x**2]
    else:
        coeffs = [n*(n+1)*(1-x**2) - m**2, -2*x*(1-x**2), (1-x**2)**2]
     
    ## Returning the final element
    return parent.element(coeffs, init, name=name)
   
### Chebyshev Polynomials        
@cached_function    
def ChebyshevD(input='n', kind = 1, poly=True):
    r'''
        TODO: Review this documentation
        D-finite implementation of the Chebyshev polynomials (T_n(x), U_n(x))
        
        References:
    - https://dlmf.nist.gov/18.3
    - https://en.wikipedia.org/wiki/Chebyshev_polynomials
    - http://mathworld.wolfram.com/ChebyshevPolynomialoftheFirstKind.html & http://mathworld.wolfram.com/ChebyshevPolynomialoftheSecondKind.html
            
        The Chebyshev polynomials of the first kind T_n(x) are the polynomial solutions 
        to the differential equation
            (1-x^2)f'' - xf' + n^2f = 0
        with a parameter 'n'. The polynomial solutions (with the appropriate normalization)
        form a orthogonal basis with the orthogonality relation:
            \int_{-1}^{1} (T_n(x)T_m(x))/(sqrt(1-x^2)) = \delta_{n,m}pi/(2-\delta_{0,n})
        
        The Chebyshev polynomials of the second kind U_n(x) are the polynomial solutions 
        to the differential equation
            (1-x^2)f'' - 3xf' + n(n+2)f = 0
        with a parameter 'n'. The polynomial solutions (with the appropriate normalization)
        form a orthogonal basis with the orthogonality relation:
            \int_{-1}^{1} U_n(x)U_m(x))sqrt(1-x^2) = \delta_{n,m}pi/2
            
        The Chebyshev polynomials of the third kind V_n(x) are the polynomial solutions
        to the differential equation
            (1-x^2)f'' + (1-2x)f' + n(n+1)f = 0
            
        THe Chebyshev polynomials of the fourth kind W_n(x) are the polynomial solutions to
        the differential equation
            (1-x^2)f'' - (1+2x)f' + n(n+1)f = 0
            
        This method allows the user to get the D-finite representation of the associated
        Chebyshev differential equation. 
        
        INPUT:
    - input: the parameter 'n' on the differential equation. If not provided, it takes the value 'n' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - kind: the kind of the Chebyshev polynomials the user want to get. It can take the values 1, 2, 3 and 4 (1 by default).
    - poly: a boolean value that refer to the polynomial solution to the differential equation or the other power series solution. If False, the other power series solution will be returned such that the Wronskian of this solution with the polynomial solution is 1. NOTE: when the parameter is not an integer, this parameter only makes a difference in the name of the function, adding a "P_" at the beginning.
            
        WARNING:
    - Initial values will also be computed for the integer parameter values.
    - When evaluating parameters, the initial values will not update and must be set by hand.
    '''
    parent, par = __check_list([input], DFinite.variables())
    n = par[0]
    
    ## Building the final parent
    if(parent is QQ):
        parent = DFinite
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    
    ## Building the final name and the equation
    x = parent.variables()[0]
    name = "chebyshev"
    if(not poly):
        name = "P_" + name
        
    if(kind == 1):
        coeffs = [n**2, -x, 1-x**2]
        name = DynamicString("%s_T(_1;_2)" %name, [repr(n), repr(x)])
    elif(kind == 2):
        coeffs = [n*(n+2), -3*x, 1-x**2]
        name = DynamicString("%s_U(_1;_2)" %name, [repr(n),repr(x)])
    elif(kind == 3):
        coeffs = [n*(n+1), 1-2*x, 1-x**2]
        name = DynamicString("%s_V(_1;_2)" %name, [repr(n),repr(x)])
    elif(kind == 4):
        coeffs = [n*(n+1), -1-2*x, 1-x**2]
        name = DynamicString("%s_W(_1;_2)" %name, [repr(n),repr(x)])
    else:
        raise ValueError("Only Chebyshev polynomials of first, second, third and fourth kind are implemented. Got %s" %kind)
    
    ## Building the initial values
    init = []
    if(n in ZZ):
        if(n%2 == 0):
            n = n/2
            if(poly):
                init = [(-1)**(n),0]
            else:
                init = [0, (-1)**(n)]
        else:
            n = (n-1)/2
            if(kind == 1):
                init = [0, ((-1)**n)*(2*n+1)]
            else:
                init = [0, ((-1)**n)*(2*n+2)]
            if(not poly):
                init = [-1/init[1], 0]
     
    ## Returning the final element
    return parent.element(coeffs, init, name=name)

###### HYPERGEOMETRIC FUNCTIONS
### Hypergeometric Functions
__CACHED_HYPERGEOMETRIC = {}

def HypergeometricFunction(a='a',b='b',c='c', init = 1):
    r'''
        D-finite implementation of the Gauss Hypergeometric function
        `_2F_1\left(\begin{array}{cc}a, b\\c\end{array}; x\right)`.

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a gaussian hypergeometric function. For more
        information about these functions, consult the following references:
        
        * :dlmf:`15`.
        * :wiki:`Hypergeometric_function`.
        * :wolf:`HypergeometricFunction`.
            
        The Gaussian hypergeometric function is a special case of the 
        generalized hypergeometric function (see :func:`GenericHypergeometricFunction`).            
        The associated sequence to this functions have the following expression:

        .. MATH::
            f_n = \frac{(a)_n  (b)_n}{n!(c)_n},

        where `(a)_n = a(a+1)...(a+n-1)` is the raising factorial notation. Hence, 
        if `a` or `b` is a negative integer this is a polynomial.
        
        TThis method is also equivalent to the alias :func:`F21`.
        
        INPUT:

        * ``a``: the parameter `a` for the hypergeometric equation. If not provided, a parameter ``"a"`` will be used instead.
        * ``b``: the parameter `b` for the hypergeometric equation. If not provided, a parameter ``"b"`` will be used instead.
        * ``c``: the parameter `c` for the hypergeometric equation. If not provided, a parameter ``"c"`` will be used instead.
        * ``init``: the initial value for the hypergeometric function. By default it takes the value 1.
    '''
    return GenericHypergeometricFunction([a,b],[c],init)

def GenericHypergeometricFunction(num=[],den=[],init=1):
    r'''
        D-finite implementation of the generalized hypergeometric function 
        (`_pF_q\left(\begin{array}{c}a_1,\ldots,a_p\\b_1,\ldots,b_q\end{array};x\right)`).

        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a hypergeometric function. For more
        information about these functions, consult the following references:
            
        * :dlmf:`16`
        * :wolf:`GeneralizedHypergeometricFunction`
        * :wiki:`Generalized_hypergeometric_function`

        The Generalized Hypergeometric function is a special function denoted by 
        `_pF_q\left(\begin{array}{c}a_1,\ldots,a_p\\b_1,\ldots,b_q\end{array};x\right)` which represents
        the formal power series whose coefficients are

        .. MATH::

            f_n = \frac{(a_1)_n \cdots (a_p)_n}{n! (b_1)_n\cdots (b_q)_n}

        where `(a)_n = a(a+1)\cdots(a+n-1)` is the Pochhammer symbol. 

        The hypergeometric functions satisfy a linear differential equation of order `\max(p,q)` that can be represented
        using the Euler differential operator `\theta_x = x\partial_x`:

        .. MATH::

            (\theta_x(\theta_x+b_1-1)\cdots(\theta_x+b_q-1) - x(\theta_x+a_1)\cdots(\theta_x+a_p)) \cdot f = 0.

        We can see from the coefficient formula that
        if, for some `i \in \{1,\ldots, p\}` and `j \in \{1,\ldots, q\}` we have `a_i = b_j`, then 
        the `_pF_q` function is identical to a `_{p-1}F_{q-1}` function. This method removes these extra 
        coefficients before computing the differential equation.

        The particular case of a `_2F_1` function is called gaussian hypergeometric function and can be obtained directly
        with the method :func:`HypergeometricFunction`.

        For particular cases of the hypergeometric function, use the following alias:

        * :func:`Fpq`: equivalent to this method
        * :func:`F00`: the case where no parameter is given. This is equal to `e^x`.
        * :func:`F01`: only one extra parameter on the denominator is given. Also called 
          *confluent hypergeometric limit function*.
        * :func:`F11`: one parameter for the numerator and another for the denominator. This 
          function is also called *Kummer confluent hypergeometric function*.
        * :func:`F21`: the gaussian hypergeometric function.

        INPUT:

        * ``num``: list of coefficients `a_i`. These elements may be any valid input from the following options:
            * A constant in `\mathbb{Q}`. 
            * A string that will be considered the name for a parameter.
        * ``den``: list of coefficients `b_j`. These elements may be of the same types as
          those in ``num``.
        * ``init``: initial value at `x=0` of this function. By default it takes the value `1`,
          but it can be any value valid for the input ``num``.
            
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in ring of D-finite functions.
                
        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: f = Fpq([1,4],[3,2])
            sage: f.init(5,True)
            [1, 2/3, 5/9, 1/2, 7/15]
            sage: f.equation.operator
            -x^2*D^3 + (x^2 - 6*x)*D^2 + (6*x - 6)*D + 4
            sage: Fpq([1,2],[1]) == Fpq([2],[])
            True
            sage: f = Fpq(['a',1],[2])
            sage: f.sequence(5)
            1/120*a^4 + 1/20*a^3 + 11/120*a^2 + 1/20*a
            sage: f = Fpq(['a','b','c'],['d','e'])
            sage: f.init(2)
            (2*a^2*c^2*b^2 + 2*a^2*c^2*b + 2*a^2*c*b^2 + 2*a*c^2*b^2 + 2*a^2*c*b + 2*a*c^2*b + 2*a*c*b^2 + 2*a*c*b)/(2*e^2*d^2 + 2*e^2*d + 2*e*d^2 + 2*e*d)

        We can use this function to prove some known identities. For example, we can prove 
        identities :funent:`651a4a`, :funent:`b25089` and :funent:`504717`::

            sage: R = F21().parent(); c,b,a = R.parameters()
            sage: factor_651a4a = R.element([c-a-b, (1-x)],[1]) # (1-x)^(c-a-b)
            sage: F21(a,b,c) == factor_651a4a*F21(c-a,c-b,c)
            True
            sage: factor_b25089 = R.element([-a, (1-x)], [1]) # (1-x)^(-a)
            sage: lhs = F21(a,b,c); rhs = factor_b25089*F21(a,c-b,c)(DFinite(x/(x-1)))
            sage: lhs.init(20, True) == rhs.init(20, True)
            True
            sage: factor_504717 = R.element([-b, (1-x)], [1]) # (1-x)^(-b)
            sage: lhs = F21(a,b,c); rhs = factor_504717*F21(c-a,b,c)(DFinite(x/(x-1)))
            sage: lhs.init(20, True) == rhs.init(20, True)
            True

        We can also prove the Kummer transformation for the confluent hypergeometric function 
        (see :funent:`be533c`)::

            sage: F11(a,b) == Exp(x)*F11(b-a,b)(-x)
            True
    '''
    ## Checking arguments: num
    if (not (type(num) in (list, tuple, set))):
        num = [num]
    else:
        num = list(num)
    if (not (type(den) in (list, tuple, set))):
        den = [den]
    else:
        den = list(den)
        
    parent, new_all = __check_list(num+den+[init], [str(el) for el in DFinite.variables()])
    numerator = new_all[:len(num)]
    denominator = new_all[len(num):-1]
    initial = new_all[-1]
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    else:
        destiny_ring = DFinite
    destiny_ring = pushout(destiny_ring, parent)
    x = destiny_ring.variable('x')
        
    ## Cleaning repeated values 
    i = 0
    while(i < len(numerator) and len(denominator) > 0):
        if(numerator[i] in denominator):
            denominator.remove(numerator[i])
            numerator.remove(numerator[i])
        else:
            i += 1
    
    ## Sort list for canonical input
    numerator.sort(); denominator.sort()
    
    ## Casting to tuples to have hash  
    numerator = tuple(numerator); denominator = tuple(denominator)

    ## Checking trivial cases
    if(any(el in ZZ and ZZ(el) <= 0 for el in denominator)):
        raise ValueError("Parameters in the denominator for a hypergeometric function can not be non-positive integers")

    if(0 in numerator):
        return initial
    
    ## Checking the function is cached
    if(not((numerator,denominator,initial) in __CACHED_HYPERGEOMETRIC)):
        ## Building differential operator
        from .ddFunction import DDFunction
        auxR = PolynomialRing(destiny_ring.original_ring(), 'theta'); E = auxR.gens()[0]
        op_num = prod([E + el for el in numerator], auxR.one()); op_den = E*prod([E + el - 1 for el in denominator], auxR.one())
        op_num = [x*sum(
            op_num[j]*DDFunction.euler_coefficient(j,i) for j in range(i,op_num.degree()+1)
            ) for i in range(op_num.degree()+1)]
        op_den = [sum(
            op_den[j]*DDFunction.euler_coefficient(j,i) for j in range(i,op_den.degree()+1)
            ) for i in range(op_den.degree()+1)]
        
        op = [(op_num[i] if i < len(op_num) else 0) - (op_den[i] if i < len(op_den) else 0)
                for i in range(max(len(op_num), len(op_den)))]
        
        f = destiny_ring.element(op)
        
        if(initial == 1):
            __CACHED_HYPERGEOMETRIC[(numerator,denominator,initial)] = f.change_init_values([1],name=DynamicString("hypergeometric(_1,_2,_3)", [str(numerator),str(denominator),"x"]))
        else:
            __CACHED_HYPERGEOMETRIC[(numerator,denominator,initial)] = f.change_init_values([initial],name=DynamicString("(_1)*(hypergeometric(_2,_3,_4))", [str(initial),str(numerator),str(denominator),"x"]))
        
    ## Return the cached element
    return __CACHED_HYPERGEOMETRIC[(numerator,denominator,initial)]

def Fpq(a, b):
    r'''
        Alias for :func:`GenericHypergeometricFunction`.
    '''
    return GenericHypergeometricFunction(a,b)

def F00():
    r'''
        Alias for a `(0,0)`-hypergeometric function. See :func:`GenericHypergeometricFunction` for further information.
    '''
    return GenericHypergeometricFunction((),())

def F10(a='a'):
    r'''
        Alias for a `(1,0)`-hypergeometric function. See :func:`GenericHypergeometricFunction` for further information.
    '''
    return GenericHypergeometricFunction((a),())

def F01(b='b'):
    r'''
        Alias for a `(0,1)`-hypergeometric function. See :func:`GenericHypergeometricFunction` for further information.
    '''
    return GenericHypergeometricFunction((),(b))

def F11(a='a',b='b'):
    r'''
        Alias for a `(1,1)`-hypergeometric function. See :func:`GenericHypergeometricFunction` for further information.
    '''
    return GenericHypergeometricFunction((a),(b))

def F21(a='a',b='b',c='c'):
    r'''
        Alias for a `(2,1)`-hypergeometric function. See also method :func:`HypergeometricFunction`.
    '''
    return HypergeometricFunction(a,b,c)
    
@cached_function
def PolylogarithmD(s=1):
    '''
        TODO: Review this documentation
        Implementation using DDFunctions of the Polylogarithms

        References:
    - https://en.wikipedia.org/wiki/Polylogarithm
    - http://mathworld.wolfram.com/Polylogarithm.html
    - https://dlmf.nist.gov/25.12

        The s-Polylogarithm is the power series defined with the sequence (1/n^s) for n >= 0. It can be computed
        recursively using and integral formula using the (s-1)-Polylogarithm.

        INPUT:
    - s: Integer and positive value. All other possible powers are not accepted so far.
    '''
    if((not (s in ZZ)) or s < 1):
        raise ValueError("The parameter 's' must be a positive integer. Got %d" %s)
    
    destiny_ring = DFinite
    
    get_op = lambda p : destiny_ring.operator_class(destiny_ring.base(),p,destiny_ring.base_derivation)
    pos_part = prod((get_op([1,x]) for i in range(1,s+2)), get_op([1]))
    neg_part = prod((get_op([1,x]) for i in range(1,s+1)), get_op([1])).derivative()
    
    final_eq = pos_part-neg_part
    Li_x = DFinite.element(final_eq, [ZZ(1)/(n**s) *factorial(n-1) for n in range(1,s+1)])
    result = Li_x*x
    result._DDFunction__name = DynamicString("Li(_1;_2)", [str(s), "x"])
    return result
    
###### RICCATI DIFFERENTIAL EQUATION
### Basic Riccati differential equation
@cached_function
def RiccatiD(a,b,c,init=None, ddR = None, full = False, name="w"):
    '''
        TODO: Review this documentation
        Implementation using DDFunctions of the solutions for the Riccati differential equation.
        
        References:
    - https://en.wikipedia.org/wiki/Riccati_equation
            
        The Riccati differential equation is a non-linear differential equation of order one of the shape
            u' = a + bu + cu^2
        
        In particular, this represent all the monomials of degree 2 or less. It can be shown that if
        a and b are Dn-finite and c is D(n-1)-finite, then u(x) will be the logarithmic derivative
        of a D(n+1)-finite function (w), and hence, it is D(n+2)-finite. More precisely:
            w'' - (b + c'/c) w' + acw = 0
            
        Given the initial condition u(0) is enough to determined all the coefficients of the solution.
        
        INPUT:
    - a: function to represent the constant term in the quadratic polynomial that is the derivative of u(x)
    - b: function to represent the linear term in the quadratic polynomial that is the derivative of u(x)
    - c: function to represent the leading term in the quadratic polynomial that is the derivative of u(x)
    - init: initial condition u(0) of the solution. None is also valid
    - ddR: basic DDRing where to put all the inputs a,b,c if they are not DDFunctions
    - full: if True, it returns also the function w used to build the solution in a tuple (solution, w)
    - name: name the system will give to the function w. By default this is "w"
    '''
    ## Considering the three parameters    
    if(is_DDFunction(a)):
        da, dRa = (a.parent().depth(), a.parent())
    else:
        a, dRa = __decide_parent(a, ddR); da = dRa.depth()-1
    if(is_DDFunction(b)):
        db, dRb = (b.parent().depth(), b.parent())
    else:
        b, dRb = __decide_parent(b, ddR); db = dRb.depth()-1
    if(is_DDFunction(c)):
        dc, dRc = (c.parent().depth(), c.parent())
    else:
        c, dRc = __decide_parent(c, ddR); dc = dRc.depth()-1
        
    R = pushout(dRa, pushout(dRb, dRc))
    R = R.to_depth(max(da+1, db+1, dc+2))
    
    x = R.variables()[0]
    
    w = R.base().element([a*c, -b + c.derivative()/c,1], [1, -c(0)*init],name=DynamicString("_1(_2)", [name,repr(x)]))
    solution = -w.derivative()*(c*w).inverse
    solution._DDFunction__name = DynamicString("Riccati(_1,_2,_3;_4)(_5)", [repr(a),repr(b),repr(c),str(init),repr(x)])
    
    if(full):
        return solution,w
    return solution
    
###### MATHIEU TYPE FUNCTIONS
### Mathieu's Functions
@cached_function
def MathieuD(a='a',q='q',init=()):
    '''
        TODO: Review this documentation
        DD-finite implementation of the Mathieu function
        
        References:
    - https://dlmf.nist.gov/28.2
    - https://en.wikipedia.org/wiki/Mathieu_function
    - http://mathworld.wolfram.com/MathieuFunction.html
            
        The Mathieu functions are the solutions to the DD-finite differential equation

        .. MATH::

            f'' + (a - 2 q cos(2x))f = 0.
            
        This is a generalization of the differential equation of the trigonometric functions
        sine and cosine (for q=0, a=1), and have several physical applications.
        
        INPUT:
    - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - q: the parameter 'q' on the differential equation. If not provided, it takes the value 'q' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, new_all = __check_list([a,q] + list(init), [str(el) for el in DFinite.variables()])
    ra = new_all[0]; rq = new_all[1]; rinit = new_all[2:]
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DDFinite, [str(v) for v in parent.gens()])
    else:
        destiny_ring = DDFinite
    x = destiny_ring.variables()[0]
    
    return destiny_ring.element([ra-2 *rq*Cos(2 *x), 0, 1], rinit, name=DynamicString("Mathieu(_1,_2;_3)(_4)", [repr(ra),repr(rq),str(rinit[:2 ]),repr(x)]))

@cached_function
def MathieuSin(a='a',q='q'):
    '''
        TODO: Review this documentation
        DD-finite implementation of the Mathieu Sine function.
        
        References:
    - https://dlmf.nist.gov/28.2
    - https://en.wikipedia.org/wiki/Mathieu_function
    - http://mathworld.wolfram.com/MathieuFunction.html
            
        This is the sine function with the Mathieu equation (i.e., with initial values
        0 an 1). It is equivalent to MathieuD(a,q,(0,1)).
    '''
    return MathieuD(a,q,(0,1))
    
@cached_function
def MathieuCos(a='a',q='q'):
    '''
        TODO: Review this documentation
        DD-finite implementation of the Mathieu Cosine function.
        
        References:
    - https://dlmf.nist.gov/28.2
    - https://en.wikipedia.org/wiki/Mathieu_function
    - http://mathworld.wolfram.com/MathieuFunction.html
            
        This is the cosine function with the Mathieu equation (i.e., with initial values
        1 an 0). It is equivalent to MathieuD(a,q,(1,0)).
    '''
    return MathieuD(a,q,(1,0))

### Modified Mathieu's Functions
@cached_function
def MathieuH(a='a',q='q',init=()):
    '''
        TODO: Review this documentation
        DD-finite implementation of the Modified Mathieu functions.
        
        References:
    - https://dlmf.nist.gov/28.20
    - https://en.wikipedia.org/wiki/Mathieu_function
            
        The Modified Mathieu functions are the solutions to the DD-finite differential equation

        .. MATH::

            f'' - (a - 2 q cosh(2x))f = 0.
            
        This is a generalization of the differential equation of the hyperbolic trigonometric functions
        sinh and cosh (for q=0, a=1), and have several physical applications.
        
        INPUT:
    - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - q: the parameter 'q' on the differential equation. If not provided, it takes the value 'q' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, new_all = __check_list([a,q] + list(init), [str(el) for el in DFinite.variables()])
    ra = new_all[0]; rq = new_all[1]; rinit = new_all[2:]
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    else:
        destiny_ring = DDFinite
    x = destiny_ring.variables()[0]
    
    return destiny_ring.element([-ra-2 *rq*Cosh(2 *x), 0, 1], rinit, name=DynamicString("MathieuH(_1,_2;_3)(_4)", [repr(ra),repr(rq),str(rinit[:2 ]),repr(x)]))

@cached_function
def MathieuSinh(a='a',q='q'):
    '''
        TODO: Review this documentation
        DD-finite implementation of the Modified Mathieu functions.
        
        References:
    - https://dlmf.nist.gov/28.20
    - https://en.wikipedia.org/wiki/Mathieu_function
            
        This is the hyperbolic sine function with the Mathieu equation (i.e., with initial values
        0 an 1). It is equivalent to MathieuH(a,q,(0,1)).
    '''
    return MathieuH(a,q,(0,1))
    
@cached_function
def MathieuCosh(a='a',q='q'):
    '''
        TODO: Review this documentation
        DD-finite implementation of the Modified Mathieu functions.
        
        References:
    - https://dlmf.nist.gov/28.20
    - https://en.wikipedia.org/wiki/Mathieu_function
            
        This is the hyperbolic cosine function with the Mathieu equation (i.e., with initial values
        1 an 0). It is equivalent to MathieuH(a,q,(1,0)).
    '''
    return MathieuH(a,q,(1,0))

### Hill's equation
@cached_function
def HillD(a='a',q='q',init=()):
    '''
        TODO: Review this documentation
        DD-finite implementation of the Hill equation.
        
        References:
    - https://dlmf.nist.gov/28.29
    - https://en.wikipedia.org/wiki/Hill_differential_equation
    - http://mathworld.wolfram.com/HillsDifferentialEquation.html
            
        The Hill differential equation is defined as
            f'' + (a + q(x))f = 0
        where 'a' is a parameter and q(x) is a function on the variable 'x'. This generalize the
        Mathieu differential equation and the modified Mathieu differential equation (taking the
        corresponding value for the function q(x)).
        
        This method allows the user to get the representation of the Hill function with some particular
        initial values. The possible values for the function q(x) is any polynomial function with x and 
        any DDFunction of any depth.
        
        INPUT:
    - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - q: the parameter 'q' on the differential equation. If not provided, it takes the value 'q' by default. This argument can be any DDFunction, rational number or any polynomial expression, which all variables (except 'x') will be considered as parameters.
    - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    if(is_DDFunction(q)):
        destiny_ring = q.parent().to_depth(q.parent().depth())
        parent, new_all = __check_list([a] + list(init), [str(el) for el in DFinite.variables()])
        
        if(not (parent is QQ)):
            destiny_ring = ParametrizedDDRing(QQ, [str(v) for v in parent.gens()])
        ra = new_all[0]; rq = destiny_ring.base()(q); rinit = new_all[-len(init):]
    else:
        parent, new_all = __check_list([a,q] + list(init), [])
        ra = new_all[0]; rq = new_all[1]; rinit = new_all[-len(init):]
        
        if(parent is QQ):
            destiny_ring = DFinite
        else:
            new_vars = [str(v) for v in parent.gens()]
            
            if('x' in new_vars):
                x = parent.gens()[new_vars.index('x')]
                if(x in ra.variables() or any(x in el.variables() for el in rinit)):
                    raise ValueError("The variable 'x' can not appear in the parameter 'a' or in the initial values.\n\t- a: %s\n\t- init: %s" %(ra,rinit))
                new_vars.remove('x')
            
            destiny_ring = ParametrizedDDRing(DFinite, new_vars)
            
    return destiny_ring.element([ra+rq, 0, 1], rinit, name=DynamicString("HillEq(_1,_2;_3)(_4)", [repr(ra),repr(rq),str(list(init[:2 ])),"x"]))

###### AIRY TYPE FUNCTIONS
### Airy's functions
@cached_function
def AiryD(init=('a','b')):
    r'''
        D-finite implementation of the Airy's functions (Ai(x), Bi(x)).
        
        The Airy functions `Ai(x)` and `Bi(x)` are the two linearly independent
        solutions to the *Airy* or *Stokes* equation:
        
        .. MATH::

            \frac{d^2y}{dx^2} - xy = 0

        It has several applications in physics (for example, it is the solution
        to Schrodinger's equation for a particle confined within a triangular 
        potential well and for a particle in a one-dimensional constant force 
        field).

        The main definition shows that Airy functions are D-finite functions.
        The classical Airy functions has as initial values:
        
        .. MATH::

            \begin{array}{cc}
                Ai(0) = \frac{1}{3^{2/3} \Gamma(2/3)};& Ai'(0) = \frac{-1}{3^{1/3}\Gamma(1/3)}\\
                Bi(0) = \frac{1}{3^{1/6} \Gamma(2/3)};& Bi'(0) = \frac{3^{1/6}}{\Gamma(1/3)}
            \end{array}

        Due to this fact, the classical Airy functions do not have rational 
        initial values. This is why this method can not retrieve te user with 
        the functions `Ai(x)` or `Bi(x)`. This method returns the solution of the 
        Airy's differential equation with some particular initial values.

        For further references, the user can look into the following references:
            * :dlmf:`9.2`
            * :wiki:`Airy_function`
            * :wolf:`AiryFunctions`
                
        INPUT:

            * ``init``: a **tuple** with the initial values for the function. Each
              element can be a string to create a variable, any rational number 
              or any polynomial expression which variables will be considered as
              parameters (so ``x`` is not allowed).

              By default, two parameters ``a`` and ``b`` are created.

        EXAMPLES::

            sage: from ajpastor.dd_functions.ddExamples import AiryD, F01
            sage: from ajpastor.dd_functions.ddFunction import DFinite
            sage: Ai = AiryD(); R = DFinite.base()
            sage: Ai[0] == R(-x)
            True
            sage: Ai[1] == 0
            True
            sage: Ai[2] == 1
            True
            sage: Ai.init(10, True)
            [a, b, 0, a, 2*b, 0, 4*a, 10*b, 0, 28*a]
            sage: for n in range(3,10):
            ....:     Ai_n = [Ai.derivative(times=n-i) for i in range(4)]
            ....:     assert Ai_n[0] == x*Ai_n[2] + (n-2)*Ai_n[3], "ERROR AiryD -- [%d]" %n
            sage: a = Ai(0); b = Ai.derivative()(0)

        We can check with this code that the Airy function can be written as as 
        combination of Hypergeometric functions::

            sage: Ai == a*F01(2/3)(x^3/9) + b*F01(4/3)(x^3/9)*x # hyperg. representation
            True
    '''
    parent, rinit = __check_list(list(init), [str(el) for el in DFinite.variables()])
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    else:
        destiny_ring = DFinite
    x = destiny_ring.variables()[0]
    
    name = None
    if(len(rinit) >= 2): ## Complete Airy function, we can build the name
        ## Rejecting the zero case
        if(rinit[0] == rinit[1] and rinit[0] == 0):
            return DFinite.zero()
        
        ## Simplifying the name if there is zero coefficients
        if(rinit[0] != 0):
            name_a1 = DynamicString("(3**(2/3)*gamma(2/3))*_1", [repr(rinit[0])])
            name_b1 = DynamicString("(3**(1/3)*gamma(2/3))*_1", [repr(rinit[0])])
        else:
            name_a1 = DynamicString("", [])
            name_b1 = DynamicString("", [])
        if(rinit[1] != 0):
            name_a2 = DynamicString("-(3**(1/3)*gamma(1/3))*_1", [repr(rinit[1])])
            name_b2 = DynamicString("+(gamma(1/3))*_1", [repr(rinit[1])])
        else:
            name_a2 = DynamicString("", [])
            name_b2 = DynamicString("", [])
            
        ## Building the final name
        name = DynamicString("((_1_2)/2)*airy_ai(_5) + ((_3_4)/(2*3**(1/6)))*airy_bi(_5)", [name_a1, name_a2, name_b1, name_b2,repr(x)])
    else:
        name = DynamicString("airy(_1; _2)", [repr(x), repr(rinit)])
    return destiny_ring.element([-x,0,1], rinit, name=name)


###### PARABOLIC-CYLINDER TYPE FUNCTIONS
### Parabolic Cylinder Functions
@cached_function
def ParabolicCylinderD(a='a',b='b',c='c', init=()):
    '''
        TODO: Review this documentation
        D-finite implementation of Parabolic Cylinder functions.
        
        References:
    - https://dlmf.nist.gov/12.2
    - https://en.wikipedia.org/wiki/Parabolic_cylinder_function
    - http://mathworld.wolfram.com/ParabolicCylinderDifferentialEquation.html
            
        The parabolic cylinder function is a solution to the differential equation:
            f'' + (c + bx + ax^2)f = 0
            
        INPUT:
    - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - b: the parameter 'b' on the differential equation. If not provided, it takes the value 'b' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - c: the parameter 'c' on the differential equation. If not provided, it takes the value 'c' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, new_all = __check_list([a,b,c]+list(init), [str(el) for el in DFinite.variables()])
    ra = new_all[0]; rb = new_all[1]; rc = new_all[2]; rinit = new_all[-len(init):]
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    else:
        destiny_ring = DFinite
    x = destiny_ring.variables()[0]
    
    return destiny_ring.element([(rc+rb*x+ra*x**2),0,1], rinit, name=DynamicString("ParabolicCylinder(_1,_2,_3;_4;_5)", [repr(ra), repr(rb), repr(rc), repr(rinit), repr(x)]))
    
###### ELLIPTIC INTEGRALS
## Legendre elliptic integrals
def EllipticLegendreD(kind,var='phi'):
    '''
        TODO: Review this documentation
        DD-finite implementation of the Legendre elliptic integrals (F(phi,k), E(phi,k), D(phi,k)
        
        References:
    - https://dlmf.nist.gov/19.2
    - https://en.wikipedia.org/wiki/Legendre_form
    - http://mathworld.wolfram.com/EllipticIntegraloftheFirstKind.html & http://mathworld.wolfram.com/EllipticIntegraloftheSecondKind.html & http://mathworld.wolfram.com/EllipticIntegraloftheThirdKind.html
            
        Given a function s(t) such that s^2 is a cubic or quartic polynomial in t and r(s,t) a rational function on s and t, 
        then the integral of r(s,t) w.r.t. t is calles an elliptic integral. The Legendre elliptic integral are obtained from
        the following functions:
        
    - First kind:
                s^2(t) = (1-t^2)(1-k^2t^2), r(s,t) = 1/s --> F(phi,k) = int_{0}^{sin(phi)} r(s,t).
    - Second kind:
                s^2(t) = (1-t^2)(1-k^2t^2), r(s,t) = s/(1-t^2) --> E(phi,k) = int_{0}^{sin(phi)} r(s,t).
    - Third kind:
                s^2(t) = (1-t^2)(1-k^2t^2), r(s,t) = t^2/s --> D(phi,k) = (F(phi,k)-E(phi,k))/k^2.
                
        These elliptic functions (called incomplete Legendre integrals) satisfies differential equations w.r.t. both k and phi.
        When phi=pi/2, they are called the complete Legendre integrals.
        
        This method allows the user to get the complete Legendre differential equations with respect to k (which are D-finite)
        or the incomplete differential equation with respect to phi (which is DD-finite). In the latter case, we consider k as a
        parameter for the differential equation.
        
        INPUT:
    - kind: determines the kind of the Legendre elliptic integral the user will get. Can only take the values 1,2 or 3 and MUST be provided.
    - var: the variable to consider. If str(var) is 'k', then the complete Legendre elliptic integral is returned. If it is 'phi' (as it is by default) then the incomplete Legendre elliptic integral is returned with k as a parameter.
    '''
    if(kind not in [1,2,3]):
        raise ValueError("The kind of legendre elliptic integral is not valid. Required 0,1 or 2")
    if(str(var) not in ['m','phi']):
        raise ValueError("The variable for taking the equation must be 'm' or 'phi'")
        
    var = str(var)
    if(var == 'm'):
        if(kind == 1):
            name = DynamicString("(2/pi)*elliptic_f(pi/2,_1)", ["x"])
            return DFinite.element([-x,(1-3*x**2), x*(1-x**2)],[1], name=name)
        elif(kind == 2):
            name = DynamicString("(2/pi)*elliptic_e(pi/2,_1)", ["x"])
            return DFinite.element([x,(1-x**2), x*(1-x**2)],[1], name=name)
        else:
            return (EllipticLegendreD(1,var)-EllipticLegendreD(2,var))/x**2
            
    if(var == 'phi'):
        DDFiniteK = ParametrizedDDRing(DDFinite, 'k')
        P = DDFiniteK.parameters()[0]
        s = DDFiniteK.to_depth(1)(Sin(x))
        c = DDFiniteK.to_depth(1)(Cos(x))
        if(kind == 1):
            name = DynamicString("(2/pi)*elliptic_f(_2,_1)", [repr(P),"x"])
            return DDFiniteK.element([0,-P**2*s*c,1-P**2*s**2], [0,1], name=name)
        elif(kind == 2):
            name = DynamicString("(2/pi)*elliptic_e(_2,_1)", [repr(P),"x"])
            return DDFiniteK.element([0,P**2*s*c,1-P**2*s**2], [0,1], name=name)
        else:
            return (EllipticLegendreD(1,var)-EllipticLegendreD(2,var))/P**2
        
###### SPHEROIDAL WAVE FUNCTIONS
## Generalized (or Coulomb) Spheroidal Differential Equation
@cached_function
def CoulombSpheroidalFunctionD(a='a', b='b', c='c', d='d', kind = 1, init=()):
    '''
        TODO: Review this documentation
        D-finite implementation of the Coulomb spheroidal function 
        
        References:
    - https://dlmf.nist.gov/30.12
            
        This method retrieves the Coulomb Spheroidal Wave function that is a generalization of the Spheroidal Wave 
        function (see documentation of SpheroidalWaveFunctionD). This function adds a new parameter (d). There are
        two kinds of generalizations (both caught vy this function with the argument 'kind'). They satisfy 
        the following differential equation:
    - First kind:
                ((1-x^2)f')' + (a + dx + b^2(1-x^2) - c^2/(1-x^2))f = 0
    - Second kind:
                ((1-x^2)f')' + (a+ b^2(1-x^2) - d(d+1)/x^2 - c^2/(1-x^2))f = 0
                
        Both equations reduce to the Spheroidal Wave differential equation when d=0.
        
        INPUT:
    - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - b: the parameter 'b' on the differential equation. If not provided, it takes the value 'b' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - c: the parameter 'c' on the differential equation. If not provided, it takes the value 'c' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - d: the parameter 'd' on the differential equation. If not provided, it takes the value 'd' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - kind: the kind of Coulomb Spheroidal function. Currently this can take the value 1 or 2 (1 by default).
    - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    if(kind not in [1,2]):
        raise ValueError("Generalized Spheroidal functions only allowed in two different generalizations (1 or 2). Got %s" %kind)
    parent, new_all = __check_list([a,b,c,d]+list(init), [str(el) for el in DFinite.variables()])
    ra = new_all[0]; rb = new_all[1]; rc = new_all[2]; rd = new_all[3] # rinit = new_all[-len(init):]
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    else:
        destiny_ring = DFinite
    x = destiny_ring.variables()[0]
    
    coeffs = [ra*(1-x**2)**2-(rb*(1-x**2))**2-rc**2, -2*x*(1-x**2), (1-x**2)**2]
    if(kind == 1):
        coeffs[0] += rd*x*(1-x**2)
    else:
        coeffs = [el*x**2 for el in coeffs]
        coeffs[0] -= rd*(rd+1)*(1-x**2)
    return destiny_ring.element(coeffs, init, name=DynamicString("CoulombSpheroidal(_1,_2,_3,_4;%d;%s)(_5)" %(kind,init), [repr(ra), repr(rb), repr(rc), repr(rd), "x"]))

@cached_function
def SpheroidalWaveFunctionD(a='a', b='b', c='c', init=()):
    '''
        TODO: Review this documentation
        D-finite implementation of the spheroidal wave function.
        
        References:
    - https://dlmf.nist.gov/30.2
    - https://en.wikipedia.org/wiki/Spheroidal_wave_function
    - http://mathworld.wolfram.com/SpheroidalWaveFunction.html
            
        The Spheroidal Wave functions are the solutions to the differential equation
            ((1-x^2)f')' + (a + b^2*(1-x^2) - c^2/(1-x^2))f = 0.
            
        This functions are related with the related Legendre functions (taking b = 0).
        
        This method allows to get the D-finite representation of the Spheroidal Wave functions
        with a set of initial values.
        
        INPUT:
    - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - b: the parameter 'b' on the differential equation. If not provided, it takes the value 'b' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - c: the parameter 'c' on the differential equation. If not provided, it takes the value 'c' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, new_all = __check_list([a,b,c]+list(init), [str(el) for el in DFinite.variables()])
    ra = new_all[0]; rb = new_all[1]; rc = new_all[2] # rinit = new_all[-len(init):]
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    else:
        destiny_ring = DFinite
    x = destiny_ring.variables()[0]
    
    coeffs = [ra*(1-x**2)**2-(rb*(1-x**2))**2-rc**2, -2*x*(1-x**2), (1-x**2)**2]
    
    return destiny_ring.element(coeffs, init, name=DynamicString("SpheroidalWave(_1,_2,_3;_4)(_5)", [repr(ra), repr(rb), repr(rc), repr(init), repr(x)]))

###### HEUN FUNCTIONS
### Fuchsian equation
@cached_function
def FuchsianD(a = (), q = (), init=(), parent=QQ):
    r'''
        Representation of Fuchsian differential equations.

        This methdod creates a :class:`ajpastor.dd_functions.ddFunction.DDFunction` representation
        of a function that satisfies a Fuchsian differential equation. This means that the differential
        equation has analytic coefficients and the singularities for the linear differential equation 
        are all regular (see :wiki:`Regular_singular_point` for further information).

        There is more information about these types of linear differential equations in the following
        reference:

        * :dlmf:`31.14`

        But generally, we can write a Fuchsian differential equation in the form:

        .. MATH::

            f^{(n)}(x) + p_{n-1}(x)f^{(n-1)}(x) + \ldots + p_0(x)f(x) = 0,

        where the coefficients `p_i(x)` can be written as:

        .. MATH::

            p_i(x) = q_i(x)\prod_{j=1}^k (x - a_j)^{-i}.

        Here, the points `a_1,\ldots,a_k` are the singularities of the linear differential equation and 
        `q_i(x)` are polynomials of degree `\leq i(k-1)`. By clearing denominators, we can write this
        linear differential equation as follows:

        .. MATH::

            \left(\prod_{j=1}^k (x-a_j)^{n-1}\right)f^{(n)}(x) + Q_{n-1}(x)f^{(n-1)}(x) + \ldots + Q_0(x)f(x) = 0,

        where 
        
        .. MATH::
        
            Q_i(x) = \left(\prod_{j=1}^k (x-a_j)^{n-1 - i}\right)q_i(x)


        INPUT:

        * ``a``: tuple of singularities of the linear differential equation. We consider internally
          the set of this tuple, removing repeated elements. In practice, these objects can be symbolic
          paramters that will be considered as constants of the field of coefficients for the final function.
        * ``q``: tuple of coefficients `q_i(x)` described above. These must be valid polynomials
          in the final ring (this depends on the parameters included in ``a``)
        * ``init``: list of initial values used for specifying the particular solution of the linear differential
          equation specified by ``a`` and ``q``. This tuple can be empty.

        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the solution of the Fuchsian differential
        equation created by ``a`` and ``q`` with initial values specified by ``init``. 

        EXAMPLES::

            sage: from ajpastor.dd_functions.ddExamples import FuchsianD
            sage: FuchsianD(1,(0,2),(1,1)) == 1/(1-x)
            True
            sage: FuchsianD(1,(0,2),(1,0)) == 1
            True
            sage: FuchsianD(1,(0,2),(0,1)) == x/(1-x)
            True
            
        TODO: allow `q_i(x)` to be other :class:`~ajpastor.dd_functions.ddFunction.DDFunction`.
    '''
    ## Checking parameters
    if (not (isinstance(a,list) or isinstance(a,set) or isinstance(a,tuple))):
        a = [a]
    if (not (isinstance(q,list) or isinstance(q,set) or isinstance(q,tuple))):
        q = [q]
    if(len(q) == 0):
        raise ValueError("The argument 'q' must be non-empty (at least order 1 for the differential equation")
    
    k = len(a); li = len(init)
    input_to_check = list(a)+list(init)
    if(parent != QQ): input_to_check += list(parent.gens())
    new_parent, new_input = __check_list(input_to_check, [str(el) for el in DFinite.variables()])
    new_a = list(set(new_input[:k])) ## Clearing repeated elements
    new_init = new_input[k:k+li]
  
    ## Getting the destiny ring
    if(new_parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in new_parent.gens()])
    else:
        destiny_ring = DFinite

    ## Checking the input for 'q'
    new_q = []
    for el in q:
        if(type(el) in (tuple, list)):
            new_q += [destiny_ring.original_ring()(list(el))]
        else:
            new_q += [destiny_ring.original_ring()(el)]
    
    N = len(new_q)

    ## computing the final coefficients Q_i(x)
    x = destiny_ring.variables()[0]
    singular_part = prod((x-pole) for pole in new_a)
    Q = [new_q[i]*singular_part**(N-1-i) for i in range(N)]

    ## getting the final name for the function
    name = DynamicString("Fuchsian(_1,_2;%s)(_3)" %(str(new_init)), [repr(new_a), repr(new_q), repr(x)])
    
    ## Returning the solution
    return destiny_ring.element(Q + [singular_part**(N-1)], new_init, name=name)

### Heun's function
def HeunD(a='a',beta='b',delta='d',gamma='g',epsilon='e',q='q'):
    r'''
        TODO: Review this documentation
        D-finite implementation of the Heun's functions.
        
        References:
            * https://dlmf.nist.gov/31.2
            * https://en.wikipedia.org/wiki/Heun_function
            * http://mathworld.wolfram.com/HeunsDifferentialEquation.html
            
        Heun functions are the solutions of the differential equation

        .. MATH::

            w''(x) + \left(\frac{\gamma}{x} + \frac{\delta}{x-1} + \frac{\epsilon}{x-a}\right)w'(x) + \frac{\alpha\beta x - q}{x(x-1)(x-a)} w(x) = 0,

        where `\alpha = \delta+\gamma+\epsilon-\beta-1`.
        
        This equation has regular singularities at `0`, `1`, `a` and `\infty` and
        captures all the possible differential equation of order two with four 
        regular singularities.
        
        The parameter `a` is called *singularity parameter*, `\alpha`, `\beta`,
        `\gamma`, `\delta`, `\epsilon` are called *exponent parameters* 
        and `q` is called the *accessory parameter*.
        
        INPUT:
            * ``a``: the parameter `a` on the differential equation. If not provided, 
              it takes the value ``'a'`` by default. This argument can be any rational 
              number or any polynomial expression, which variables will be considered 
              as parameters (so ``x`` is not allowed).
            * ``beta``: the parameter `\beta` on the differential equation. If not provided, 
              it takes the value ``'b'`` by default. This argument can be any rational 
              number or any polynomial expression, which variables will be considered 
              as parameters (so ``x`` is not allowed).
            * ``delta``: the parameter `\delta` on the differential equation. If not provided, 
              it takes the value ``'d'`` by default. This argument can be any rational 
              number or any polynomial expression, which variables will be considered 
              as parameters (so ``x`` is not allowed).
            * ``gamma``: the parameter `\gamma` on the differential equation. If not provided, 
              it takes the value ``'g'`` by default. This argument can be any rational 
              number or any polynomial expression, which variables will be considered 
              as parameters (so ``x`` is not allowed).
            - ``epsilon``: the parameter `\epsilon` on the differential equation. If not provided, 
              it takes the value ``'e'`` by default. This argument can be any rational 
              number or any polynomial expression, which variables will be considered 
              as parameters (so ``x`` is not allowed).
            - ``q``: the parameter `q` on the differential equation. If not provided, 
              it takes the value ``'q'`` by default. This argument can be any rational 
              number or any polynomial expression, which variables will be considered 
              as parameters (so ``x`` is not allowed).
            
        WARNING:
            * This method does not compute initial values for the solution of this 
              differential equation since no power series solution is guaranteed 
              due to the singularity at 0.

        EXAMPLES::

            sage: from ajpastor.dd_functions.ddExamples import HeunD
            sage: H = HeunD(); H
            Heun(a,b,d,g,e,q)(x)
            sage: H.change_init_values([1]).sequence(3, True)
            [1, 0, q/(2*a + 2*d)]
    '''
    parent, new_all = __check_list([a,beta,delta,gamma,epsilon,q], [str(el) for el in DFinite.variables()])
    ra,rb,rd,rg,re,rq = new_all
        
    if(ra == 0 or ra == 1):
        raise ValueError(("The singularity parameter is not valid: the extra singularity must be"
                           "different than 0 or 1"))

    al = rg+rd+re-rb-1
    gamma = [rd,rg,re]; q=[-rq/ra,(rq-al*rb)/(ra-1), (rq/ra)-((rq-al*rb)/(ra-1))]
    to_poly_coeffs = lambda obj: (obj[0],(ra+1)*obj[0] + ra*obj[1]+obj[2], obj[0]+obj[1]+obj[2])
    fuchs_q = (to_poly_coeffs(q), to_poly_coeffs(gamma))
    f = FuchsianD(a=(0,1,ra),q=fuchs_q,parent=parent)
    f.name = DynamicString("Heun(_1,_2,_3,_4,_5,_6)(_7)", [repr(ra),repr(rb),repr(rd),repr(rg),repr(re),repr(rq),"x"])
    return f

###### COULOMB FUNCTIONS
def FCoulombD(m='m', l=-1):
    r'''
        D-finite implementation of the regular Coulomb wave function `F_{l,\mu}(x)`.
        
        Method to create a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        instance of a regular Coulomb wave function. For more
        information about this function, consult the following references:

        * :dlmf:`33.2`
        * :funtop:`Coulomb_wave_functions`
        * :wiki:`Coulomb_wave_function`

        The regular Coulomb wave function is a function `w_{\nu,l}(x)` defined with the differential
        equation

        .. MATH::
        
            \frac{d^2w}{dx^2} + \left(1-\frac{2\nu}{x} - \frac{l(l+1)}{x^2}\right)w = 0.

        This equation falls naturally in the realm of D-finite functions, and can be written
        as follows:

        .. MATH::

            x^2 w_{\nu,l}''(x) + (x^2 - 2\nu x - l(l+1))w_{\nu,l}(x) = 0.

        This equation has a singularity at zero, so it will only have 1 regular solution at this
        point that is the function defined via this method.

        INPUT:

        * ``m``: value of the parameter `\nu`. It can be a numerical value or a string. In the 
          latter case, it will be used to create a new parameter with such name.
        * ``l``: value of the parameter `l`. It has to be an integer greater or equal to `-1`.
          Then the equation has a unique power series solution of order `l+1`. If this
          is not an integer value, an error is raised.
              
        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representing the corresponding
        power series in the appropriate :class:`~ajpastor.dd_functions.ddFunction.DDRing`.
              
        EXAMPLE::

            sage: from ajpastor.dd_functions import *
            sage: F = FCoulombD(1/2,2)
            sage: x^2*F.derivative(times=2) + (x^2-x-6)*F
            0
            sage: for l in range(-1,10): # checking with m parameter
            ....:     F = FCoulombD('m',l)
            ....:     m = F.parent().parameter('m')
            ....:     assert x^2*F.derivative(times=2) + (x^2-2*m*x-l*(l+1))*F == 0, "ERROR:%d" %l

        We can check with this function the Kummer function (see :funent:`d280c5`). Remark that 
        our Coulomb function is such that the first non-zero initial condition is 1, so we have
        to scale the identity accordingly::

            sage: R = ParametrizedDDRing(DFiniteI, 'm')
            sage: i = R.base().base().base().base().gens()[0]; x = R.variable('x'); m = R.parameter('m')
            sage: for l in range(0, 10):
            ....:     for w in (-1,1):
            ....:         lhs = FCoulombD(m, l)
            ....:         rhs = x^(l+1)*Exp(SR('x'))(w*i*x)*F11(1+l+w*i*m, 2*l+2)(-2*w*i*x)
            ....:         assert factorial(l+1)*lhs == rhs, "ERROR: %d-%d" %(l,w)
    '''
    parent, new_all = __check_list([m,l], [str(el) for el in DFinite.variables()])
    rm, rl = new_all
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()])
    else:
        destiny_ring = DFinite
    x = destiny_ring.variables()[0]
    init = []
    
    ## Checking the `l` argument
    if(not (rl in ZZ)):
        raise TypeError("The parameter `l` has to be an integer")
    rl = ZZ(rl)
    if(rl < -1): 
        raise ValueError("The parameter `l` has to be an integer greater or equal than -1")
    
    if(rl in [-1,0]): ## Special cases
        init = [0,1]
    elif(rl > 0):
        init = [0 for i in range(rl+1)] + [1]
            
    return destiny_ring.element([x**2-2*rm*x-rl*(rl+1), 0, x**2], init=init, name=DynamicString("CoulombF(_1;_2)(_3)", [repr(rm), repr(rl), "x"]))

##################################################################################
##################################################################################
###
### Combinatorial functions
###
##################################################################################
################################################################################## 
@cached_function
def FactorialD():
    r'''
        DDFunction of the generating function for the factorial sequence.

        The factorial sequence is easily defined with the recurrence 
        `f_{n+1} = (n+1)f_n` with `f_0 =1` and it is commonly represented as 
        `f_n = n!`. As a P-finite recurrence, its generating function
        `Fa(x)` satisfies a linear differential equation: 
        
        .. MATH::

            x^2 Fa''(x) + (3x-1)Fa'(x) + Fa(x) = 0.

        This method returns the :class:`~ajpastor.dd_functions.ddFunction.DDFunction`
        representing this function `Fa(x)`.
        
        EXAMPLES::

            sage: from ajpastor.dd_functions.ddExamples import FactorialD
            sage: from ajpastor.dd_functions.ddFunction import DFinite
            sage: fa = FactorialD(); R = DFinite.base(); fa
            Fa(x)
            sage: fa[0] == 1
            True
            sage: fa[1] == R(3*x-1)
            True
            sage: fa[2] == R(x^2)
            True
            sage: fa.sequence(10, True)
            [1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880]
            sage: fa.init(10, True) == [factorial(i)^2 for i in range(10)]
            True
    '''
    return DFinite.element([1,3*x-1,x**2],[1], name=DynamicString("Fa(_1)", ["x"]))

@cached_function
def CatalanD():
    r'''
        DDFunction of the generating function for the Catalan numbers.

        References:

        * :oeis:`A000108`
        * :wiki:`Catalan_number`

        The Catalan sequence is defined with a closed formula 
        `c_n = \binom{2n}{n}/(n+1)`. It has been widely studied 
        and it is known that this sequence satisfies a linear recurrence:
        
        .. MATH::

            c_{n+1} = \sum_{i=0}^n c_i c_{n-i},
        
        which leads to the functional equation:
        
        .. MATH::

            C(x) = 1+ xC(x)^2,
            
        where `C(x)` is the ordinary generating function for the sequence `(c_n)_n`. 
        This algebraic equation implies that `C(x)` is D-finite with 
        differential equation:
        
        .. MATH::

            (4x^2-x)C''(x) + (10x - 2)C'(x) + 2C(x) = 0.
            
        This method returns the :class:`~ajpastor.dd_functions.ddFunction.DDFunction`
        representing this function `C(x)`.
        
        EXAMPLES::

            sage: from ajpastor.dd_functions.ddExamples import CatalanD
            sage: from ajpastor.dd_functions.ddFunction import DFinite
            sage: C = CatalanD(); R = DFinite.base(); C
            C(x)
            sage: C[0] == 2
            True
            sage: C[1] == R(10*x-2)
            True
            sage: C[2] == R(4*x^2-x)
            True
            sage: C.sequence(10, True)
            [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]
            sage: x*C^2 + 1 == C # algebraic relation
            True
    '''
    return DFinite.element([2, 10*x-2, 4*x**2-x], [1,1], name=DynamicString("C(_1)", ["x"]))

@cached_function
def FibonacciD(init=('a','b')):
    r'''
        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` for the generating function of a Fibonacci-type sequence.

        References:
        
        * :oeis:`A000045`
        * :wiki:`Fibonacci_number`

        The Fibonacci sequence `(f_n)_n` is defined classically with the linear recurrence 

        .. MATH::

            f_{n+2} = f_{n+1} + f_{n},
            
        starting with initial values `f_0 = 0`, `f_1 = 1`. 

        This linear recurrence implies that the ordinary generating function for
        the Fibonacci sequence is D-finite independently to initial conditions 
        `f_0`, `f_1`.

        In fact, since the recurrence relation is C-finite (with constant 
        coefficients), the generating function is a rational function:
        
        .. MATH::

            F(f_0,f_1;x) = \frac{f_0 + (f_1-f_0)x}{1-x-x^2}

        This method returns the :class:`~ajpastor.dd_functions.ddFunction.DDFunction` object 
        for the ordinary generating function for a particular Fibonacci-type 
        sequence provided the initial conditions `f_0` and `f_1`.
        
        INPUT:
            
        * ``init``: a tuple with the initial conditions `f_0` and `f_1`. This
          list can be of any length containing integer, strings or polynomials
          with variables that will be considered as parameters. If not enough 
          elements are provided, more parameters will be added.
              
          By default, this argument takes the value ``('a','b')``.
              
        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: Fp = FibonacciD(); Fp
            F(a,b;x)
            sage: Fp.sequence(5, True)
            [a, b, b + a, 2*b + a, 3*b + 2*a]
            sage: F = FibonacciD((0,1))
            sage: F.sequence(10, True) == [fibonacci(i) for i in range(10)]
            True
            sage: F == x/(1-x-x^2)
            True
            sage: a = Fp.sequence(0); b = Fp.sequence(1)
            sage: x = Fp.parent().variables()[0]
            sage: Fp == (a + (b-a)*x)/(1-x-x^2)
            True
            sage: f = FibonacciD(tuple([2*a-3*b]));
            sage: all(f.sequence(i+2) - f.sequence(i+1) - f.sequence(i) == 0 for i in range(20))
            True
            sage: FibonacciD(('a','c_1')) # with strings
            F(a,c_1;x)
            sage: FibonacciD(('f',a*2+1,0,0,0)) # with long tuple
            F(f,2*a + 1;x)
    '''
    parent, rinit = __check_list([el for el in init], [str(el) for el in DFinite.variables()])
    params = [str(v) for v in parent.gens()]
    pos = ord('a')
    if(len(init) < 2):
        if(len(init) < 1):
            while(chr(pos) in params):
                pos += 1
            rinit = [chr(pos)]
        if(len(init) == 1):
            while(chr(pos) in params):
                pos += 1
            rinit += [chr(pos)]
        return FibonacciD(tuple(rinit))
    
    if(parent is QQ):
        destiny_ring = DFinite
    else:
        destiny_ring = ParametrizedDDRing(DFinite, params)
    
    x = destiny_ring.variables()[0]
    f = destiny_ring(((rinit[1]-rinit[0])*x + rinit[0])/(1-x-x**2))
    f.name = DynamicString("F(_1,_2;_3)", [str(rinit[0]),str(rinit[1]),"x"])
    return f
    
@cached_function
def BellD():
    r'''
        DDFunction of the exponential generating function for the Bell numbers.

        References:

        * :wiki:`Bell_number`
        * :oeis:`A000110`
        * :wolf:`BellNumber`

        The Bell numbers are a sequence `B_n` that counts the amount of possible
        partitions of a set with `n` element. This sequence is well known to be
        non holonomic. Moreover, its ordinary generating function is not 
        differentially algebraic.
        
        However, if we consider its *exponential generating function*, the
        Bell numbers can be represented with

        .. MATH::

            B(x) = \sum_{n \geq 0} B_n \frac{x^n}{n!} = e^{e^{x}-1}
             
        This formula shows that `B(x)` is DD-finite since it is the composition
        of two exponential functions. 
            
        This method returns the :class:`~ajpastor.dd_functions.ddFunction.DDFunction` 
        representing this function `B(x)`.
        
        EXAMPLES::

            sage: from ajpastor.dd_functions.ddExamples import Exp,BellD
            sage: B = BellD(); B
            B(x)
            sage: B == Exp(Exp(x)-1)
            True
            sage: B.init(10, True) == [bell_number(i) for i in range(10)]
            True
    '''
    f = DFinite.element([-1,1],[-1], name = DynamicString("-exp(_1)", ["x"])) # -exp(x)
    return DDFinite.element([f, 1], [1], name=DynamicString("B(_1)", ["x"]))
    
@cached_function
def BernoulliD():
    r'''
        DDFunction of the exponential generating function for the Bernoulli numbers.

        References:

        * :wiki:`Bernoulli_number`
        * Numerator sequence: :oeis:`A027641`
        * Denominator sequence: :oeis:`A027642`
        * :wolf:`BernoulliNumber`

        The Bernoulli numbers are a sequence `B_n` that arise in the series 
        expansions of trigonometric functions, and are extremely important 
        in number theory and analysis. This sequence is well known to be
        non holonomic. 
        
        However, if we consider its *exponential generating function*, the
        Bernoulli numbers can be represented with
        
        .. MATH::

            B(x) = \sum_{n \geq 0} B_n \frac{x^n}{n!} = \frac{x}{e^x-1}
             
        This formula shows that `B(x)` is DD-finite since it is the quotient of
        two D-finite functions.
        
        This method returns the :class:`~ajpastor.dd_functions.ddFunction.DDFunction`
        representing this function `B(x)`.
        
        EXAMPLES::

            sage: from ajpastor.dd_functions.ddExamples import Exp,BernoulliD
            sage: from ajpastor.dd_functions.ddFunction import DFinite
            sage: B = BernoulliD(); B
            B(x)
            sage: B == DFinite(x)/(Exp(x)-1)
            True
            sage: B.init(10, True) == [bernoulli(i) for i in range(10)]
            True
    '''
    return DDFinite.element([x*Exp(x)-Exp(x)+1, x*(Exp(x)-1)],[1], name=DynamicString("B(_1)", ["x"]))

##################################################################################
##################################################################################
###
### P-Weierstrass function
###
##################################################################################
##################################################################################
def DFiniteWP(g2 = 'a', g3 = 'b', with_x = False):
    r'''
        TODO: Review this documentation
        Method that create the ring of diff. definable elements over the `\wp`-Weierstrass
        function.

        The `\wp`-Weierstrass function is a special function related with elliptic curves.
        In fact, the `\wp`-Weierstrass function together with its derivative form
        a very particular type of elliptic curves:

        .. MATH::

            \wp'^2 = \wp^3 - g_2\wp - g_3,

        where `g_2,g_3` are constants complex elements.

        TODO:
            * Complete this introduction

        INPUT:
            * ``g2``: the constant `g_2` defining the elliptic curve.
            * ``g3``: the constant `g_3` defining the elliptic curve.
            * ``with_x``: boolean value deciding whether adding the `x` variable 
              or not.
    '''
    ## Checking input
    parent, vals = __check_list([g2, g3], ['x','u','v'])
    rg2,rg3 = vals

    vars = ['u','v']
    if(with_x): vars = ['x'] + vars

    base_ring = PolynomialRing(parent, vars)
    if(with_x) : x = base_ring('x')
    u = base_ring('u'); v = base_ring('v')
    I = ideal(v**2 - u**3 + rg2*u + rg3)
    final_base_ring = base_ring.quotient(I)

    if(with_x):
        def inner_derivation(p):
            p = p.lift()
            return final_base_ring(p.derivative(x) + v*p.derivative(u) + (3/2*u**2 - g3)*p.derivative(v))
    else:
        def inner_derivation(p):
            p = p.lift()
            return final_base_ring(v*p.derivative(u) + (3/2*u**2 - g3)*p.derivative(v))
    
    return DDRing(final_base_ring, 1, parent, derivation=inner_derivation)
          
##################################################################################
##################################################################################
###
### Algebraic functions
###
##################################################################################
################################################################################## 
def DAlgebraic(polynomial, init=[], dR=None):
    '''
        TODO: Review this documentation
        Method that transform an algebraic function to a DD-Function.
                
        INPUT:
    - polynomial: the minimal polynomial of the function we want to transform.
    - init: the initial values that the function will have. Two options are 
            possible: a list is given, then we will use it directly to build the final 
            result, or a value is given an we will compute the others using the polynomial 
            equation.
    - dR: the ring where we want to include the result. If None, an automatic 
            destiny ring will be computed.
            
        OUTPUT:
    - A DDFunction in a particuar DDRing.
            
        WARNINGS:
    - There is no control about the irreducibility of the polynomial.
            
        ERRORS:
    - If the function can not be represented in dR a TypeError will be raised
    - If any error happens with the initial values, a ValueError will be raised
    '''    
    ###############################################
    ## Dealing with the polynomial input
    ###############################################
    parent = polynomial.parent()
    if(not (isPolynomial(parent) or isMPolynomial(parent))):
        raise TypeError("DAlgebraic: the input polynomial is NOT a polynomial")
    
    base_ring = None
    F = None
    poly_ring = parent
    if(isMPolynomial(parent)):
        ## Only valid for 2 variables
        if(parent.ngens() > 2):
            raise TypeError("DAlgebraic: the input can not be a multivariate polynomial with more than 2 variables")
        base_ring = PolynomialRing(parent.base(),parent.gens()[0])
        F = base_ring.fraction_field()
    else:
        if(isinstance(parent.base().construction()[0], FractionField)):
            base_ring = parent.base().base()
        else:
            base_ring = parent.base()
        
        if(is_DDRing(base_ring)):
            F = LazyDDRing(base_ring)
        elif(not base_ring.is_field()):
            F = base_ring.fraction_field()
        else:
            F = base_ring
            
    poly_ring = PolynomialRing(F, parent.gens()[-1])
    y = poly_ring.gens()[-1]
    
    ## At this point we have the following
    ##   - F is a field
    ##   - y is a variable
    ##   - poly_ring == F[y]
    polynomial = poly_ring(polynomial) ## Now the structure is univariate
    if(polynomial.degree() == 1):
        return -polynomial[0]/polynomial[1]
    elif(polynomial.degree() <= 0):
        raise TypeError("DAlgebraic: constant polynomial given for algebraic function: IMPOSSIBLE!!")
        
    #################################################
    ## Building and checking the destiny ring
    #################################################
    destiny_ring = None
    if(dR is None):
        destiny_ring = DDRing(base_ring)
    else:
        destiny_ring = dR
        coercion = destiny_ring.base()._coerce_map_from_(base_ring)
        if((coercion is None) or (coercion is False)):
            raise TypeError("Incompatible polynomial with destiny ring:\n\t- Coefficients in: %s\n\t- Destiny Ring: %s" %(base_ring, destiny_ring))
            
    dest_var = repr(destiny_ring.variables()[0])
    
    ##################################################
    ## Computing the differential equation
    ##################################################
    ## Computing the derivative
    dy = polynomial.derivative(y)
        
    ## Computing the coefficient-wise derivation of polynomial
    ky = sum(polynomial[i].derivative()*y**i for i in range(polynomial.degree()+1))
    
    ### WARNING From this point until said otherwise, in the case base_ring is DDRing
    ### we change the polynomials to a finite setting because when this was code, 
    ### computing remainders with InfinitePolynomial coefficients broke the program.
    ###
    ### For further information about it, please check the track: (pending)
    ### The code that should work once that is solved is the following:
    if(is_DDRing(base_ring)): 
        # Changing to a finite setting
        def get_sub_vars(*polys):
            if(len(polys) > 1):
                return get_sub_vars(polys)
            return list(set(sum([sum([list(el[i].variables()) for i in range(el.degree()+1)],[]) for el in polys[0]],[])))
        
        sub_vars = get_sub_vars([polynomial, dy, ky])
        poly_ring_fin = PolynomialRing(PolynomialRing(base_ring.base_ring(), sub_vars).fraction_field(), poly_ring.gens_dict().items()[0][0])
        polynomial = poly_ring_fin(str(polynomial))
        dy = poly_ring_fin(str(dy))
        ky = poly_ring_fin(str(ky))
        y = poly_ring_fin.gens()[0]
                            
    ## Getting its gcd with the polynomial
    g,_,s = polynomial.xgcd(dy)
    if((g != 1) and (g.degree() != 0)):
        raise ValueError("DAlgebraic: no irreducible polynomial (%s) given" %polynomial)
    
    ## Getting the polynomial expression of y'
    yp = (-(ky*s))%polynomial
    
    ## Building the derivation matrix of <1,y,y^2,...>
    rows = [[0]*polynomial.degree()]
    for i in range(1,polynomial.degree()):
        # (y^i)' = i*y^(i-1)*y'
        current = ((i*yp*y**(i-1))%polynomial).coefficients(False)
        current += [0 for i in range(len(current),polynomial.degree())]
        rows += [current]
    
    M = Matrix(F, rows).transpose()
    ## Creating the vector representing y
    y_vector = vector(F, [0,1] + [0]*(polynomial.degree()-2 ))
    
    if(is_DDRing(base_ring)): raise RuntimeError("DEBUG Stop")
    
    ## Building and solving the system
    to_solve = move(M, y_vector, lambda p : p.derivative(), M.ncols()+1)
    
    if(is_DDRing(base_ring)): raise RuntimeError("DEBUG Stop")
    
    v = to_solve.right_kernel_matrix()[0]
    
    if(is_DDRing(base_ring)): raise RuntimeError("DEBUG Stop")
    
    ## Cleaning denominators
    cleaning = lcm(el.denominator() for el in v)
    
    equation = destiny_ring.element([F.base()(el*cleaning) for el in v]).equation
    
    ##################################################
    ## Getting the initial values
    ##################################################
    if(not (type(init) is list)):
        ## We try to compute the new initial values
        init = [init]
        go_on = True
        for i in range(1,min(equation.get_jp_fo()+2 , to_solve.ncols())):
            try:
                init += [sum(to_solve[j,i](**{dest_var:0})*init[0]**j for j in range(polynomial.degree()))]
            except ZeroDivisionError:
                go_on = False
                break
        
        if(go_on and (equation.get_jp_fo()+2 > to_solve.ncols())):
            extra = move(M, vector(F,[el[0] for el in to_solve[:,-1]]),lambda p: p.derivative(), equation.get_jp_fo()+2 -to_solve.ncols())
            init += [sum(extra[j,i](**{dest_var:0})*init[0]**j for j in range(polynomial.degree())) for i in range(extra.ncols())]
    
    ##################################################
    ## Returning the DDFunction
    ##################################################
    return destiny_ring.element(equation, init)
    
def polynomial_inverse(polynomial):
    '''
        TODO: Review this documentation
        Method that computes the functional inverse for a polynomial. As the functional
        inverse of a polynomial is an algebraic series, then it is D-finite.
        
        The polynomial provided must be univariate.
    '''
    from ajpastor.misc.sequence_manipulation import inv_lagrangian
    
    ###############################################
    ## Dealing with the polynomial input
    ###############################################
    parent = polynomial.parent()
    if(not isPolynomial(parent)):
        raise TypeError("The minimal polynomial is NOT a polynomial")
        
    if(polynomial.constant_coefficient() != 0):
        raise ValueError("Non-invertible polynomial given: %s" %polynomial)
    
    ## Building the extra variable needed for algebraic   
    x = parent.gens()[0]
    y = str(x)+"_y"
    R = PolynomialRing(parent.fraction_field(), [y])
    y = R.gens()[0]
    
    ## Building the initial conditions
    coeffs = polynomial.coefficients(False)
    inv = inv_lagrangian(lambda n : factorial(n)*coeffs[n])
    init = [inv(i) for i in range(len(coeffs))]
    
    return DAlgebraic(polynomial(**{str(x):y})-x, init)
  
##################################################################################
##################################################################################
###
### Private methods
###
##################################################################################
##################################################################################    
def __decide_parent(input, parent = None, depth = 1):
    r'''      
        Method to decide the parent from a given input.

        This method is an auxiliary method that decides the parent associated
        with an input given some basic possible parent and depth.
        
        This method will compute a :class:`~ajpastor.dd_functions.ddFunction.DDRing` such that
        the element in ``input`` is can be used as a coefficient in the defining differential 
        equations of its elements and it contains (at least) the depth ``depth`` of the 
        :class:`~ajpastor.dd_functions.ddFunction.DDRing` given by ``parent``.

        If ``parent`` is ``None``, then a minimal :class:`~ajpastor.dd_functions.ddFunction.DDRing`
        is computed such that ``input``  can be used as coefficient. 

        The treatment of ``input`` depends on its type:
            * If it is a Symbolic Expression, we will consider `x` as a main variable and 
              all other variables in the expression as parameters. Then the minimal 
              :class:`~ajpastor.dd_functions.ddFunction.DDRing` is computed with that information.
              This only works if ``input`` is a polynomial in `x` and a rational function on the 
              other variables.
            * If it is a polynomial, the first variable will be used as the main variable and the 
              other as parameters. The the same procedure as for the Symbolic Expression will 
              happen.

        INPUT:

        * ``input``: the input from which we start.
        * ``parent``: a possible :class:`~ajpastor.dd_functions.ddFunction.DDRing` that has to be included
          in the output.
        * ``depth``: desired depth of the final :class:`~ajpastor.dd_functions.ddFunction.DDRing`.

        OUTPUT:

        A tuple containing:
            * The element in ``input`` casted to the base ring of the final parent ring.
            * A :class:`~ajpastor.dd_functions.ddFunction.DDRing` that can represent objects over the ``input``
              that also includes the ``parent`` and has depth ``depth``.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: from ajpastor.dd_functions.ddExamples import __decide_parent as decide
            sage: decide(x)
            (x, DD-Ring over (Univariate Polynomial Ring in x over Rational Field))
            sage: decide(x)[0] in decide(x)[1].base()
            True
            sage: decide(x, depth=3)[0].parent() is decide(x, depth=3)[1].base()
            True
            sage: i = DFiniteI.base().base().gens()[0]; X = DFiniteI.variable('x')
            sage: decide(i*X)
            (I*x, DD-Ring over (Univariate Polynomial Ring in x over Number Field in I with defining polynomial x^2 + 1)))
            sage: decide(Exp(x), DFiniteI)
            (exp(x), DD-Ring over (DD-Ring over (Univariate Polynomial Ring in x over Number Field 
            in I with defining polynomial x^2 + 1)))

        This method detects some of the parameters included in the parent of the input, putthing them appropriately 
        into the system::

            sage: ParametrizedDDRing(DFiniteI, 'm').variable('x')
            sage: x.parent()
            Univariate Polynomial Ring in x over Fraction Field of Univariate Polynomial Ring 
            in m over Number Field in I with defining polynomial x^2 + 1
            sage: decide(x)
            (x, DD-Ring over (Univariate Polynomial Ring in x over Number Field in I with defining polynomial x^2 + 1) with parameter (m))
    '''
    ## Treating the input
    input_parent = input.parent()
    if(input in QQ):
        input_parent = DFinite
    elif(input_parent is SR):
        parameters = set([str(el) for el in input.variables()])-set(['x'])
        if(len(parameters) > 0 ):
            input_parent = ParametrizedDDRing(DFinite, parameters)
        else:
            input_parent = DDRing(PolynomialRing(QQ,x))
    elif(isMPolynomial(input_parent) or isPolynomial(input_parent)):
        parameters = [str(gen) for gen in input_parent.gens()[1:]]
        var = input_parent.gens()[0]

        current = input_parent.base()
        while((is_FractionField(current) or isMPolynomial(current) or isPolynomial(current)) and (current.gens() != (1))):
            parameters += [str(gen) for gen in current.gens() if str(gen) != '1']
            current = current.base()
        parameters = list(set(parameters))

        if(len(parameters) > 0):
            input_parent = ParametrizedDDRing(DDRing(PolynomialRing(current,var)), parameters)
        else:
            input_parent = DDRing(PolynomialRing(input_parent.base_ring(),var))
    else:
        try:
            input_parent = DDRing(input_parent)
        except Exception as e:
            raise TypeError("The object provided is not in a valid Parent", e)
    input = input_parent.base()(input)

    ## Computing the common parent
    if(parent is None):
        parent = input_parent.to_depth(depth)
    elif(is_DDRing(parent)):
        parent = parent.to_depth(depth)

    final_parent = pushout(input_parent, parent)
    return final_parent.base()(input), final_parent

def __check_list(list_of_elements, invalid_vars=[]):
    '''
        TODO: Review this documentation
        This method computes a field of rational functions in several variables given a list of 
        elements, where all the elements can be casted into. This method also allows to ban some variables
        to appear in the elements, raising an error if that happens.
        
        The elements on the list can be:
    - A string: it will be consider as the name of a parameter.
    - Any element with attribute 'variables'. All the variables found will be add as parameters.
    - Elements of a FractionField. The base ring must provide the method 'variables'. All the variables found will be added as parameters.
            
        Once all the variables are computed, we checked that there are no invalid variables and then we 
        build the field of rational functions in the variables found. Then we return this field together 
        with the original list, now with all elements casted to this field.
        
    '''
    invalid_vars = [str(el) for el in invalid_vars]
    all_vars = []
    parent = QQ
    for i in range(len(list_of_elements)):
        el = list_of_elements[i]
        if(el in QQ):
            pass
        elif(isinstance(el, str)):
            all_vars += [el]
        else:
            from sage.rings.fraction_field import is_FractionField
            if(is_FractionField(el.parent())):
                all_vars += [str(v) for v in el.numerator().variables()]
                all_vars += [str(v) for v in el.denominator().variables()]
            else:
                all_vars += [str(v) for v in el.variables()]
            parent = pushout(parent, el.parent().base_ring())
            list_of_elements[i] = str(el)
    
    if(any(el in all_vars for el in invalid_vars)):
        raise ValueError("An invalid variable detected in the list.\n\t- Got: %s\n\t- Invalid: %s" %(list_of_elements, invalid_vars))
    
    if(len(all_vars) > 0):
        all_vars = list(set(all_vars))
        parent = PolynomialRing(parent, all_vars).fraction_field()
        list_of_elements = [parent(el) for el in list_of_elements]
    
    return (parent, list_of_elements)
