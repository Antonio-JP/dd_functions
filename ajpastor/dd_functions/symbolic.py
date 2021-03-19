r"""
Python file to work between the Symbolic Ring and Differentially definable functions

This package provides functionality to interact between the Symbolic Ring in Sage and the 
rings of Differentially Definable functions (see :class:`~ajpastor.dd_functions.ddFunction.DDRing`). in 
particular, this module offers several methods to use the simplification of symbolic expressions 
to simplify the structure for a :class:`~ajpastor.dd_functions.ddFunction.DDFunction`. 

This module is related with :mod:`~ajpastor.dd_functions.ddExamples`, since all the examples we offer in
that module (when they have a Symbolic equivalent) can be transformed with this module.

EXAMPLES::

    sage: from ajpastor.dd_functions import *
    sage: from_symbolic(symbolic(Exp(x))) == Exp(x)
    True

TODO:
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

import logging

from sage.all import SR, prod, ZZ, QQ, PolynomialRing

from ajpastor.dd_functions.ddFunction import is_DDFunction, DFinite, ParametrizedDDRing
from ajpastor.dd_functions.ddExamples import (Sin, Cos, Sinh, Cosh, Tan, Log, Exp, 
                                                BesselD, LegendreD, ChebyshevD,
                                                GenericHypergeometricFunction, DAlgebraic)

logger = logging.getLogger(__name__)

###################################################################################################
### SYMBOLIC CONVERSION OF DD_FUNCTIONS
###################################################################################################
def symbolic(function):
    r'''
        Method to cast a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` into a symbolic expression.

        This method relies on the method :func:`~ajpastor.dd_functions.ddFunction.DDFunction.to_symbolic`. 
        If, for any reason, we can not cast the element to a Symbolic expression, we raise an error.

        INPUT:

        * ``function``: a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` to convert to a Symbolic expression.

        OUTPUT:

        An element in the Symbolic Ring of Sage.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: symbolic(Exp(x))
            e^x
            sage: symbolic(BesselD(2))
            bessel_J(2, x)
            sage: symbolic(LegendreD('n','m'))
            gen_legendre_P(n, m, x)
    '''
    if(not is_DDFunction(function)):
        raise TypeError("The input of 'symbolic' has to be a DDFunction")

    output = None
    try:
        output = function.to_symbolic()
    except (NameError, SyntaxError):
        raise TypeError("The object given can not be transformed into Symbolic expression")
    
    if(output is None):
        raise ValueError("The object does ot produce a symbolic expression")
    return output

def from_symbolic(exp, dR = None):
    r'''
        Method to transform a symbolic expression into a :class:`~ajpastor.dd_functions.ddFunction.DDFunction`.

        This method takes a symbolic expression an tries to cast it into a differentially definable function.
        This is closed related with the names that the module :mod:`~ajpastor.dd_functions.ddExamples` gives to 
        the functions.

        This method is the inverse of :func:`symbolic`, meaning that the output of this method after applying
        :func:`symbolic` is always an object that is equal to the first input.

        INPUT:

        * ``exp``: symbolic expression or an object that can be casted into one. We also allow lists, tuples and
          sets as possible inputs, applying this method recursively to each of its elements.
        * ``dR``: :class:`~ajpastor.dd_functions.ddFunction.DDRing` in which hierarchy we try to include
          the symbolic expression ``exp``. If ``None`` is given, we compute a :class:`~ajpastor.dd_functions.ddFunction.DDRing`
          using `x` as a variable and all other variables appearing in ``exp`` considered as parameters.

        OUTPUT:

        A :class:`~ajpastor.dd_functions.ddFunction.DDFunction` representation of ``exp``.

        TODO: add more cases from ddExamples

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: var('y', 'm', 'n')
            (y, m, n)
            sage: from_symbolic(exp(x)) == Exp(x)
            True
            sage: sin_yx = from_symbolic(sin(y*x))
            sage: parent(sin_yx)
            DD-Ring over (Univariate Polynomial Ring in x over Rational Field) with parameter (y)
            sage: sin_yx.init(6, True)
            [0, y, 0, -y^3, 0, y^5]
            sage: from_symbolic(cos(x)) == Cos(x)
            True
            sage: from_symbolic(sinh(x)) == Sinh(x)
            True
            sage: from_symbolic(cosh(x)) == Cosh(x)
            True
            sage: from_symbolic(tan(x)) == Tan(x)
            True
            sage: from_symbolic(log(x + 1)) == Log(x+1)
            True
            sage: from_symbolic(bessel_J(4, x)) == BesselD(4)
            True
            sage: from_symbolic(hypergeometric([1,2,3],[5,6,7],x)) == GenericHypergeometricFunction((1,2,3),(5,6,7))
            True
    '''
    logger.debug("Looking for a DD-finite representation of %s", exp)
    
    if(isinstance(exp, list)):
        logger.debug("List case: converting each element")
        return [from_symbolic(el,dR) for el in exp]
    elif(isinstance(exp, tuple)):
        logger.debug("Tuple case: converting each element")
        return tuple([from_symbolic(el,dR) for el in exp])
    elif(isinstance(exp, set)):
        logger.debug("Set case: converting each element")
        return set([from_symbolic(el,dR) for el in exp])

    ## If it is not from the basic structures, we required a symbolic expression
    exp = SR(exp)
    
    logger.debug("Deciding the starting DDRing")
    if(not dR is None):
        logger.debug("User required solution to be in the hierarchy of %s", dR)
        if(any(v not in list(dR.variables(True)) + list(dR.parameters(True)) for v in exp.variables())):
            raise TypeError("The symbolic expression has unknown variables")
    else:
        logger.debug("DDRing not specified: we compute one")
        params = [str(v) for v in exp.variables() if str(v) != 'x']
        if(len(params) > 0):
            dR = ParametrizedDDRing(DFinite, [str(v) for v in exp.variables() if str(v) != 'x'])
        else:
            dR = DFinite

    name = None
    try: 
        name = exp.operator().__name__ 
    except AttributeError: 
        try:
            name = exp.operator().name()
        except AttributeError:
            pass

    operands = exp.operands()
    if(name in ("list", "tuple")): # special tuple and list cases
        logger.debug("Found a symbolic list or tuple")
        return tuple([from_symbolic(el,dR) for el in operands])
    elif(name == "set"): # special set case
        logger.debug("Found a symbolic set")
        return set([from_symbolic(el,dR) for el in operands])
    elif(exp.is_rational_expression()): # rational expression case
        logger.debug("Rational expression found")
        num = exp.numerator().polynomial(ring=dR.original_ring())
        den = exp.denominator().polynomial(ring=dR.original_ring())
        if(den == 1):
            return num
        
        return num/den
    elif(name == "add_vararg"):
        logger.debug("Found an addition")
        return sum([from_symbolic(el,dR) for el in operands])
    elif(name == "mul_vararg"):
        logger.debug("Found an product")
        return prod([from_symbolic(el,dR) for el in operands])
    elif(name == "pow"):
        logger.debug("Found an power")
        if(not operands[1] in QQ):
            raise TypeError("The exponent has to be a rational number")
        if(operands[1] in ZZ):
            logger.debug("Integer power: simple output")
            return pow(from_symbolic(operands[0],dR), ZZ(operands[1]))
        else:
            base = from_symbolic(operands[0], dR)
            if(is_DDFunction(base)):
                logger.debug("Fractional power: base DDFunction")
                return pow(base, QQ(operands[1]))
            else:
                logger.debug("Fractional power: base rational function")
                params = [str(el) for el in dR.parameters()]; i = 0
                while("y%d" %i in params): i += 1

                R = PolynomialRing(dR.original_ring(), "y%d" %i); y = R.gens()[0]
                pq = QQ(operands[1]); p = pq.numerator(); q = pq.denominator()

                poly = y**q - R(str(operands[0]))**p
                x = dR.variables(True)[0]
                init = [dR.coeff_field(exp.derivative(x, i)(**{str(x): 0})) for i in range(p+q)]

                return DAlgebraic(poly, init, dR.to_depth(1))
    elif(name == "sin"):
        logger.debug("Found an sine")
        return Sin(operands[0])
    elif(name == "cos"):
        logger.debug("Found an cosine")
        return Cos(operands[0])
    elif(name == "sinh"):
        logger.debug("Found a hyperbolic sine")
        return Sinh(operands[0])
    elif(name == "cosh"):
        logger.debug("Found an hyperbolic cosine")
        return Cosh(operands[0])
    elif(name == "tan"):
        logger.debug("Found a tangent")
        return Tan(operands[0])
    elif(name == "log"):
        logger.debug("Found a logarithm")
        return Log(operands[0])
    elif(name == "exp"):
        logger.debug("Found an exponential")
        return Exp(operands[0])
    elif(name == "bessel_J"):
        logger.debug("Found an Bessel function of first kind")
        if(not (operands[0] in ZZ and operands[0] >= 0)):
            raise ValueError("The Bessel has to have a non-negative integer index")
        return BesselD(ZZ(operands[0]))(from_symbolic(operands[1],dR))
    elif(name == "legendre_P"):
        logger.debug("Found an Legendre function of first kind")
        return LegendreD(operands[0], 0, 1)(from_symbolic(operands[1],dR))
    elif(name == "gen_legendre_P"):
        logger.debug("Found an generic Legendre function of first kind")
        return LegendreD(operands[0], operands[1], 1)(from_symbolic(operands[1],dR))
    elif(name == "legendre_Q"):
        logger.debug("Found an Legendre function of second kind")
        return LegendreD(operands[0], 0, 2)(from_symbolic(operands[1],dR))
    elif(name == "gen_legendre_Q"):
        logger.debug("Found an generic Legendre function of second kind")
        return LegendreD(operands[0], operands[1], 2)(from_symbolic(operands[1],dR))
    elif(name == "chebyshev_T"):
        logger.debug("Found an Chebyshev function of first kind")
        return ChebyshevD(operands[0], 1)(from_symbolic(operands[1],dR))
    elif(name == "chebyshev_U"):
        logger.debug("Found an Chebyshev function of second kind")
        return ChebyshevD(operands[0], 2)(from_symbolic(operands[1],dR))
    elif(name == "hypergeometric"):
        return GenericHypergeometricFunction(from_symbolic(operands[0],dR),from_symbolic(operands[1],dR))(from_symbolic(operands[2],dR))
    else:
        raise NotImplementedError("The operator %s is not valid for 'from_symbolic'" %name)

def symbolic_simplify(function):
    r'''
        Method to simplify in-place a :class:`~ajpastor.dd_functions.ddFunction.DDFunction`.

        This method uses the conversion between symbolic expressions and :class:`~ajpastor.dd_functions.ddFunction.DDFunction`
        to simplify te construction of a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` through the ``simplify``
        method of symbolic expressions.

        What this method does is to convert the input to a symbolic expression, run the method ``simplify_full`` 
        from symbolic expressions, then build a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` from that new expression
        and compare what we obtained with the original. if the size is smaller, we change the equation and the name of the 
        original function using the new information.

        INPUT:

        * ``function``: a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` we want to simplify.
        
        OUTPUT:

        The same object but (in case we get a smaller representation) with the equation and name simplified. Sometimes
        this could even change the depth of the current object since while doing closure properties we did not recognize
        the simplification.

        TODO: add examples and check functionality
    '''
    ## If the input is not a DDFunction, we just return it
    if(is_DDFunction(function)):
        ## First, we check the function itself
        symbolic = from_symbolic(function.to_symbolic(), function.parent())
        if(not is_DDFunction(symbolic)):
            symbolic = function.parent()(symbolic)

        if(symbolic.size() < function.size()):
            function._DDFunction__equation = symbolic.equation # WARNING: this is not "good"
        if(len(repr(symbolic)) < len(repr(function))):
            function.name = repr(symbolic)

        ## Now we check the coefficients of the equation
        symbolic_simplify_coefficients(function)
    return function

def symbolic_simplify_coefficients(function):
    if(is_DDFunction(function)):
        for i in range(function.order()+1):
            symbolic_simplify(function.equation.coefficient(i))

###################################################################################################
### PACKAGE ENVIRONMENT VARIABLES
###################################################################################################
__all__ = ["symbolic", "from_symbolic", "symbolic_simplify", "symbolic_simplify_coefficients"]

