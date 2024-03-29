r"""
Python file for LazyRing

This module implements all the functionality of a ConversionSystem based on a Ring using
lazy operations. This means all the arithmetic operations are done in a polynomial ring.
This structure also increase the number of variables employed in the polynomial ring
as the suer require to represent more elements of the ring.

EXAMPLES::

    sage: from ajpastor.lazy.lazyRing import *

TODO:
    * Do the examples section in this documentation
    * Document all the package
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
from sage.all import (QQ, gcd, lcm, UniqueRepresentation, var, PolynomialRing, 
                        IntegralDomains, Fields, IntegralDomain, IntegralDomainElement)
from sage.categories.map import Map #pylint: disable=no-name-in-module
from sage.categories.pushout import ConstructionFunctor
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isUniPolynomial
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing as isMPolynomial

from ajpastor.misc.ring_w_sequence import Ring_w_Sequence

from .conversion import ConversionSystem
from .lazyIDElements import LazyDomain

_Fields = Fields.__classcall__(Fields)
_IntegralDomains = IntegralDomains.__classcall__(IntegralDomains)


####################################################################################################
####################################################################################################
### ELEMENT CLASS
####################################################################################################
####################################################################################################
class _LazyElement(IntegralDomainElement):
    def __init__(self, parent, el):
        if(not (isinstance(parent, LazyRing))):
            parent = LazyDomain(parent)

        self.__raw = None
        self.__poly = None

        IntegralDomainElement.__init__(self, parent)

        try:
        #if(el in parent.poly_ring()):
            self.__poly = parent.poly_ring()(str(el))
        except:
        #elif(el in parent.poly_field()):
            try:
                self.__poly = parent.poly_field()(str(el))
            except:
        #else:
                self.__raw = parent.base()(el)
                self.__poly = self.parent().to_poly(self.__raw)

        self.simplify()

    ################################################################################################
    ### Methods for a LazyElement
    ################################################################################################
    def raw(self):
        '''
        Method that computes (if needed) and returns an element of `self.base()` that is equal to `self`.
        '''
        if(self.__raw is None):
            self.__raw = self.parent().to_real(self.__poly)

        return self.__raw

    def poly(self):
        '''
        Method that computes (if needed) and returns an polynomial such that the conversion using
        self.parent() returns self.raw().
        '''
        if(self.__poly is None):
            self.__poly = self.parent().to_poly(self.__raw)

        return self.__poly

    def simplify(self):
        self.__poly = self.parent().simplify(self.poly())

    def variables(self):
        '''
        Method that returns a tuple with the variables that appear in self.poly().

        If such polynomial representation is a quotient of polynomials, it take the union of the variables in the numerator and denominator.
        If such polynomial representation has no variables, returns an empty tuple.
        '''
        if(self.poly() not in QQ):
            if(self.poly() in self.parent().poly_ring()):
                return self.parent().poly_ring()(self.poly()).variables()
            else:
                var_n = self.parent().poly_ring()(self.poly().numerator()).variables()
                var_d = self.parent().poly_ring()(self.poly().denominator()).variables()

                return tuple(set(var_n+var_d))
        return tuple()

    def derivative(self, *args):
        '''
        Method that computes the derivative of an element in the laziest way possible.

        This method compute the derivative of each of the variables in 'self.poly()' and then build
        a new polynomial using this expressions.

        This method rely on the parent method 'get_derivative()' which saves the derivatives of the
        variables as a dictionary
        '''
        map_of_derivatives = {var : self.parent().get_derivative(var) for var in self.variables()}

        return _LazyElement(self.parent(),sum(map_of_derivatives[key]*self.parent().poly_field()(self.poly()).derivative(key) for key in map_of_derivatives))

    ################################################################################################
    ### Arithmetics methods
    ################################################################################################
    def _add_(self, other):
        if(isinstance(other, _LazyElement)):
            try:
                return _LazyElement(self.parent(), self.poly()+self.parent()(other).poly())
            except NotImplementedError:
                pass

        return NotImplemented

    def _sub_(self,other):
        return self.__add__(-other)

    def _neg_(self):
        try:
            return _LazyElement(self.parent(), -self.poly()) #pylint: disable=invalid-unary-operand-type
        except NotImplementedError:
            pass

        return NotImplemented

    def _mul_(self,other):
        if(isinstance(other, _LazyElement)):
            try:
                return _LazyElement(self.parent(), self.poly()*self.parent()(other).poly())
            except NotImplementedError:
                pass

        return NotImplemented

    def _div_(self,other):
        if(isinstance(other, _LazyElement)):
            try:
                return _LazyElement(self.parent(), self.parent().poly_field()(self.poly())/self.parent().poly_field()(self.parent()(other).poly()))
            except NotImplementedError:
                pass

        return NotImplemented

    def _pow_(self,i):
        try:
            return _LazyElement(self.parent(), self.poly()**i)
        except NotImplementedError:
            return NotImplemented

    def __eq__(self, other):
        return (self-other).is_zero()

    def __call__(self, *input, **kwds):
        if(self.__raw is None):
            try:
                return self.poly()(**{str(var):self.parent().to_real(var)(*input,**kwds) for var in self.variables()})
            except TypeError:
                pass
        return self.raw()(*input,**kwds)

    ################################################################################################
    ### Non-trivial arithmetics methods
    ################################################################################################
    def gcd(self,*input):
        '''
        Method that a common divisor of 'self' and the input
        '''
        if(len(input) > 1 ):
            return self.gcd(input)

        return _LazyElement(self.parent(), gcd([self.poly()]+[self.parent()(el).poly() for el in input]))

    def lcm(self,*input):
        '''
        Method that a common multiple of 'self' and the input
        '''
        if(len(input) > 1 ):
            return self.gcd(input)

        return _LazyElement(self.parent(), lcm([self.poly()]+[self.parent()(el).poly() for el in input]))

    def divides(self, other):
        '''
        Method that returns True if 'other = a*self'.

        REMARK: If this methods return False does not mean we can not divide other by self in the level of 'base'.
        '''
        return self.poly().divides(self.parent()(other).poly())

    #def is_zero_real(self):
    #    if(not self.is_zero()):
    #        result = False
    #        if(not (self.__raw is None)):
    #            result = self.raw() == 0
    #        else:
    #            pol = None
    #            if(self.poly() in self.parent().poly_ring()):
    #            else:
    #                pol = self.parent().poly_ring()(self.poly().numerator())
    #
    #            for factor in pol.factor():
    #                result = (self.parent().to_real(factor[0]) == 0)
    #                if(result):
    #                    self.parent().add_relations(factor[0])
    #                    break
    #
    #    return result

    def is_zero(self):
        result = (self.poly() == 0 )
        if((not result) and (self(**{repr(self.parent().base().variables()[0]):0}) == 0)):
            if(not (self.__raw is None)):
                result = self.raw() == 0
            else:
                pol = None
                if(self.poly() in self.parent().poly_ring()):
                    pol = self.parent().poly_ring()(self.poly())
                else:
                    pol = self.parent().poly_ring()(self.poly().numerator())

                factors = None
                try:
                    try:
                        factors = pol.factor(proof=True)
                    except NotImplementedError:
                        factors = pol.factor(proof=False)
                except:
                    factors = [(pol,1 )]
                for factor in factors:
                    result = (self.parent().to_real(factor[0 ]) == 0 )
                    if(result):
                        self.parent().add_relations(factor[0 ])
                        break

        return result

    def is_one(self):
        try:
            result = (self.poly() == 1 ) or (self.raw() == self.parent().one())
            if(result):
                self.parent().add_relations(self.poly()-1 )
            return result
        except TypeError:
            return False

    ################################################################################################
    ### Representation methods
    ################################################################################################
    def __repr__(self):
        return repr(self.poly())

    def __str__(self):
        if(self.__raw is None):
            return "Lazy Element: %s" %(repr(self))
        else:
            return "Lazy Element: %s\n%s" %(repr(self), str(self.raw()))

####################################################################################################
####################################################################################################
### RING CLASS
####################################################################################################
####################################################################################################
class LazyRing (UniqueRepresentation, ConversionSystem, IntegralDomain):

    Element = _LazyElement

    def __init__(self, base, constants=QQ, category=None):
        ## Checking the arguments
        if(not (constants in _Fields)):
            raise TypeError("The argument 'constants' must be a Field")
        if(not (isinstance(base, Ring_w_Sequence))):
            raise TypeError("The argument 'base' must be a Ring with Sequence")

        ## Initializing the parent structures
        ConversionSystem.__init__(self, base)
        IntegralDomain.__init__(self, base, category)

        ## Initializing the attributes
        self.__constants = constants

        self.__poly_ring = None
        self._change_poly_ring(constants)

        ## Initializing the map of variables (if there is enough)
        self.__map_of_vars = {}

        ## Initializing the map of derivatives
        self.__map_of_derivatives = {}

        ## Casting and Coercion system
        self.base().register_conversion(LRSimpleMorphism(self, self.base()))

        ## Auxiliary data
        self.__var_name = "x"
        self.__version = 1


    ################################################################################################
    ### Implementing methods of ConversionSystem
    ################################################################################################
    def poly_ring(self):
        return self.__poly_ring

    def poly_field(self):
        return self.__poly_field

    def map_of_vars(self):
        return self.__map_of_vars

    def variables(self):
        return tuple(self.poly_ring()(key) for key in self.map_of_vars().keys())

    def _change_poly_ring(self, new_ring):
        super(LazyRing, self)._change_poly_ring(new_ring)
        if(not (self.poly_ring() is new_ring)):
            self.__poly_ring = new_ring
            self.__create_poly_field()

    def _to_poly_element(self, element):
        if(element.parent() is self):
            return element.poly()
        elif(not (element in self.base())):
            raise TypeError("Element is not in the base ring.\n\tExpected: %s\n\tGot: %s" %(element.parent(), self.base()))

        ## We try to cast to a polynomial. If we can do it, it means no further operations has to be done
        try:
            return self.poly_ring()(element)
        except:
            pass

        ## Now we check if the element has a built method
        try:
            built = element.built
            if(not (built is None)):
                if(built[0 ] == "derivative"):
                    if(not(element in built[1 ])):
                        integral = self(built[1 ][0 ])
                        if(not (integral.poly().is_monomial() and integral.poly().degree() == 1 )):
                            return self(built[1 ][0 ]).derivative().poly()
                elif(built[0 ] == "polynomial"):
                    ## We check we do not have infinite recursion
                    if(not element in built[1 ][1 ].values()):
                        ## We have some building information
                        polys = {key : self.to_poly(built[1 ][1 ][key]) for key in built[1 ][1 ]}
                        return built[1 ][0 ](**polys)
        except AttributeError:
            pass

        ## Otherwise we look for a linear relation between the element and the variables
        var_found = None
        rel = None
        for key in self.map_of_vars().keys():
            rel = self.__find_relation(element, self.map_of_vars()[key])
            if(not (rel is None)):
                var_found = key
                break

        ## If we find no relation, we add a new variable
        if(rel is None):
            new_var = None
            if(self.poly_ring() is self.__constants):
                new_var = var("%s0" %self.__var_name)
                self._change_poly_ring(PolynomialRing(self.__constants,new_var, order="lex"))
                self.__map_of_vars[str(new_var)] = element
            else:
                new_var = var("%s%d" %(self.__var_name,self.poly_ring().ngens()))
                self._change_poly_ring(PolynomialRing(self.__constants, [new_var]+list(self.poly_ring().gens()), order="lex"))
                self.__map_of_vars[str(new_var)] = element

            return new_var

        ## We try to keep the real representations small
        try:
            new_elem = (element-rel[1 ])/rel[0 ]
            if(new_elem.size() < self.map_of_vars()[var_found].size()):
                self.__map_of_vars[var_found] = new_elem
        except:
            pass

        ## Otherwise, we return the polynomial computed
        return self.poly_ring()(rel[0 ]*self.poly_ring()(var_found) + rel[1 ])

    ################################################################################################
    ### Other Methods for LazyRing
    ################################################################################################
    def sequence(self, el, n, list=False):
        if(not isinstance(el, _LazyElement)):
            return el.parent().sequence(el,n,list=list)

        return self.base().sequence(el.raw(),n,list=list)

    def clean_ring(self):
        ## Clean the relations
        self.clean_relations()

        ## Return to the basic constant field
        self._change_poly_ring(self.__constants)

        ## Deleting the variables created
        self.__map_of_vars = {}

        ## Deleting the map of derivatives
        self.__map_of_derivatives = {}

        self.__version += 1

    def change_variable_name(self, new_name):
        self.__var_name = str(new_name)

    def version(self):
        return self.__version

    def get_derivative(self, el):
        if(el in self.__map_of_derivatives):
            return self.__map_of_derivatives[el]

        if(el in self.__constants):
            return 0
        else:
            try:
                el = self.poly_ring()(el)
                if(el in self.poly_ring().gens()):
                    new_poly = self.to_poly(self.map_of_vars()[str(el)].derivative())
                    self.__map_of_derivatives[el] = new_poly
                    return new_poly
            except:
                pass
        raise ValueError("Method 'get_derivative' can only be summoned with variables.\nGot: %s -- %s" %(el, el.parent()))

    ################################################################################################
    ### Other Integral Domain methods
    ################################################################################################
    def base_ring(self):
        return self.base().base_ring()

    def characteristic(self):
        return self.base().characteristic()

    def _an_element_(self):
        return self.one()

    def element(self, X):
        return self(X)

    ################################################################################################
    ### Other Ring methods
    ################################################################################################
    def is_field(self):
        return self.base().is_field()

    def is_finite(self):
        return self.base().is_finite()

    def is_integrally_closed(self):
        return self.base().is_integrally_closed()

    def is_noetherian(self):
        return self.base().is_noetherian()

    ################################################################################################
    ### Coercion methods
    ################################################################################################
    def _coerce_map_from_(self, S):
        coer = None
        if(isinstance(S, LazyRing)):
            coer = self.base()._coerce_map_from_(S.base())
        elif(S == self.base()):
            coer = True
        else:
            coer = self.base()._coerce_map_from_(S)

        if(not(coer is False) and not(coer is None)):
            return True
        return None

    def _has_coerce_map_from(self, S):
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))

    def _element_constructor_(self, *args, **kwds):
        if(len(args) < 1 ):
            print(str(args))
            raise ValueError("Impossible to build an element without arguments")

        i = 0
        if(len(args) >= 2 ):
            if(not (args[0 ] is self)):
                raise ValueError("The first element in the arguments must be self (%s)" %self)
            i = 1
        X = args[i]

        try:
            if(not isinstance(X, _LazyElement)):
                ## If the element is not a LazyElement, then we try to create a new element with it
                return _LazyElement(self, X)
            elif (X.parent() is self):
                return X
            else:
                ## Otherwise, X.parent() may have different variables
                other = X.parent()
                pol = X.poly()

                ## For each variable in X.poly(), we get the new polynomial
                translate = {}
                for var in X.variables():
                    translate[str(var)] = self.to_poly(other.map_of_vars()[str(var)])

                ## We now plugin the expressions
                return _LazyElement(self, pol(**translate))
        except TypeError:
            raise TypeError("This element can not be casted to %s" %repr(self))

    def construction(self):
        return (LazyRingFunctor(), self.base())

    def __contains__(self, X):
        try:
            return (X.parent() is self) or (self._has_coerce_map_from(X.parent()))
        except AttributeError:
            try:
                self(X)
                return True
            except Exception:
                return False

    ################################################################################################
    ### Representation methods
    ################################################################################################
    def __repr__(self):
        return "Lazy Ring over (%s)" %(repr(self.base()))

    def __str__(self):
        final = "%s with %d variables\n{\n" %(self.__repr__(),len(self.__map_of_vars.keys()))
        for k,v in self.__map_of_vars.items():
            final += "\t%s : %s,\n" %(k, repr(v))
        final += "}"
        return final

        ################################################################################################
    ### Private methods
    ################################################################################################
    def __create_poly_field(self):
        if(isUniPolynomial(self.__poly_ring) or (isMPolynomial(self.__poly_ring))):
            self.__poly_field = self.__poly_ring.fraction_field()
        else:
            self.__poly_field = self.__poly_ring

    def __find_relation(self, a, b):
        ## TODO We assume a and b are not constants
        i = 1
        while(self.sequence(a,i) == 0  and self.sequence(b,i) == 0 ):
            i = i + 1

        ai = self.sequence(a,i)
        bi = self.sequence(b,i)
        if(bi == 0  or ai == 0 ):
            return None

        c = ai/bi
        d = self.sequence(a,0 )-c*self.sequence(b,0 )

        if(a == c*b + d):
            return (c,d)
        else:
            return None

####################################################################################################
####################################################################################################
### Construction Functor for LazyRing
####################################################################################################
####################################################################################################
class LazyRingFunctor (ConstructionFunctor):
    def __init__(self):
        ID = _IntegralDomains
        self.rank = 20
        super(LazyRingFunctor, self).__init__(ID,ID)

    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        if(isinstance(x, LazyRing)):
            return x.base()
        return x

    def _apply_functor(self, x):
        return LazyRing(x)

####################################################################################################
####################################################################################################
### General Morphism for return to basic rings
####################################################################################################
####################################################################################################
class LRSimpleMorphism (Map):
    def __init__(self, domain, codomain):
        super(LRSimpleMorphism, self).__init__(domain, codomain)

    def _call_(self, p):
        return self.codomain()(p.raw())

