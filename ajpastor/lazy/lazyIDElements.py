r"""
Python file for Integral Domain Elements for LazyRings

This module provides the implementation of the Element class for LazyRings
based on Integral Domains. It contains all the arithmetic functionality
required to make it work with linear algebra algorithms.

EXAMPLES::

    sage: from ajpastor.lazy.lazyIDElements import *

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
from sage.all import (IntegralDomain, IntegralDomainElement, gcd, UniqueRepresentation, ZZ)

from sage.categories.integral_domains import IntegralDomains
from sage.categories.map import Map #pylint: disable=no-name-in-module
from sage.categories.pushout import ConstructionFunctor

_MAX_INTEGER = 2**10-1

_IntegralDomains = IntegralDomains.__classcall__(IntegralDomains)

#####################################################
### Class for Lazy Integral Domain Elements
#####################################################
class LazyIDElement(IntegralDomainElement):
    def __init__(self, parent):
        if(not (isinstance(parent, LazyIntegralDomain))):
            parent = LazyDomain(parent)

        self.__raw = None
        self.__max_divisor = None

        IntegralDomainElement.__init__(self, parent)

    ###############################
    ### Public methods
    ###############################
    def base(self):
        return self.parent().base()

    def raw(self):
        '''
        Method that computes (if needed) and returns an element of `self.base()` that is equal to `self`.
        '''
        if(self.__raw is None):
            self.__raw = self.base()(self.__compute_raw_element__())

        return self.__raw

    def max_divisor(self):
        '''
        Method that computes (if needed) and returns a SumLIDElement which we know we can divide `self`.
        '''
        if(self.__max_divisor is None):
            self.__max_divisor = self.__compute_max_divisor__()

        return self.__max_divisor

    def gcd(self,*input):
        '''
        Method that computes a SumLIDElement which we know we can divide `self` and every element on `input`.
        '''
        return self.max_divisor().gcd(*input)

    def lcm(self, *input):
        '''
        Method that computes a lazyElement such every element of input and self are divisors
        '''
        ## Checking the arguments
        if(len(input) == 1 and type(input[0]) == list):
            input = input[0]

        if(len(input) == 0):
            return self

        smallLcm = (self*input[0]).divide(self.gcd(input[0]))
        if(len(input) == 1):
            return smallLcm

        return smallLcm.lcm(input[1:])

    def is_multiple_of(self,element):
        '''
        Method that returns whether `self` can be divided by `element`.
        '''
        if(self == element or element == self.base().one()):
            return True

        return self.__inner_is_multiple__(element)

    def divide(self,element):
        '''
            Method that performs (if possible) the division of `self` by `element`.
        '''
        if((not element in self.base()) and (not isinstance(element, LazyIDElement))):
            raise TypeError("Impossible divide by a %s" %(type(element)))
        if(not self.is_multiple_of(element)):
            raise ValueError("Impossible divide [%s] by [%s] within the domain" %(self, element))

        element = self.parent()(element)

        if(self == self.parent().zero()):
            return self
        elif(self == element):
            return self.parent().one()
        elif(element == self.base().one()):
            return self

        return self.__compute_division__(element)

    def simplify(self):
        '''
        Method that simplifies (if possible) the current element. It is a change inside the structure and the return is the result of the changes
        '''
        return self

    def derivative(self, *input):
        '''
        Method that computes the lazy derivative of an element. It assumes that the parent ring has a derivation and the arguments for such derivation are provided in 'input'.
        '''
        raise AttributeError("Method not implemented")

    def is_zero(self):
        if(self.__raw is None):
            return self.__inner_is_zero__()
        return self.raw() == self.base().zero()

    def is_one(self):
        if(self.__raw is None):
            return self.__inner_is_one__()
        return self.raw() == self.base().one()

    ###############################
    ### Arithmetic methods
    ###############################
    def _add_(self, other):
        if(isinstance(other, LazyIDElement)):
            if(other.is_zero()):
                return self
            try:
                return self.__inner_add__(other)
            except NotImplementedError:
                pass

        return NotImplemented

    def _sub_(self,other):
        return self.__add__(-other)

    def _neg_(self):
        try:
            return self.__inner_neg__()
        except NotImplementedError:
            pass

        return NotImplemented

    def _mul_(self,other):
        if(isinstance(other, LazyIDElement)):
            if(other.is_zero()):
                return self.parent().zero()
            if(other.is_one()):
                return self
            try:
                return self.__inner_mul__(other)
            except NotImplementedError:
                pass

        return NotImplemented

    def _pow_(self,i):
        try:
            return self.__inner_pow__(i)
        except NotImplementedError:
            return NotImplemented

    ###############################
    ### Representation methods
    ###############################
    def _repr_(self):
        return self.__inner_printing__(repr)

    def __str__(self):
        return self.__inner_printing__(str)

    def __inner_printing__(self, method):
        return "LazyElement(%s)" %(method(self.raw()))

    ###############################
    ### Abstract methods definition
    ###############################
    def get_basic_elements(self):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __compute_raw_element__(self):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __change_domain__(self, newParent):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __compute_max_divisor__(self):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __struct__(self):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __inner_is_multiple__(self, element):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __compute_division__(self, element):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __inner_is_zero__(self):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __inner_is_one__(self):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __inner_add__(self, other):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __inner_neg__(self):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __inner_mul__(self, other):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    def __inner_pow__(self, other):
        raise NotImplementedError("This method has not been implemented for this type of LazyElement")

    ###############################
    ### Private methods definition
    ###############################
    def _is_pure_in_base(self,element):
        return ((not isinstance(element, LazyIDElement)) and (element in self.base()))

#####################################################
### Class for Simple LazyIDElements
#####################################################
class SimpleLIDElement(LazyIDElement):
    def __init__(self, parent, element):
        super(SimpleLIDElement, self).__init__(parent)

        if(isinstance(element, LazyIDElement)):
            element = element.raw()

        self.__element = element
        self.raw()

    ###############################
    ### Overridden methods
    ###############################
    def derivative(self, *input):
        return SimpleLIDElement(self.parent(), self.raw().derivative(*input))

    ###############################
    ### Abstract methods implementation
    ###############################
    def get_basic_elements(self):
        try:
            self.parent().base_ring()(self.raw())
        except Exception:
            return {self}
        return set()

    def __compute_raw_element__(self):
        return self.__element

    def __change_domain__(self, newParent):
        if(newParent == self.parent()):
            return self
        return SimpleLIDElement(newParent, self.raw())

    def __compute_max_divisor__(self):
        return SumLIDElement(self.parent(), ProductLIDElement(self.parent(),self))

    def __struct__(self):
        return self.raw()

    def __inner_is_multiple__(self, element):
        return False

    def __compute_division__(self, element):
        if(isinstance(element, SimpleLIDElement)):
            inner = element
            number = 1
        elif(isinstance(element, ProductLIDElement)):
            inner = element
            number = 1
        elif(isinstance(element, SumLIDElement)):
            inner = element.__struct__().keys()[0]
            number = element.__struct__()[inner]

        if(number == 1):
            if(inner == self.parent().one()):
                return self
            else:
                return self.parent().one()
        elif(number == -1):
            if(inner == self.parent().one()):
                return self._neg_()
            else:
                return self.parent().one()._neg_()
        raise ValueError("Impossible Exception: can not perform division")

    def __inner_add__(self, other):
        if(isinstance(other, SumLIDElement)):
            return SumLIDElement(self.parent(), self, other.__struct__())
        else:
            return SumLIDElement(self.parent(), self, other)

    def __inner_neg__(self):
        return SumLIDElement(self.parent(), {self:-1})

    def __inner_mul__(self, other):
        if(isinstance(other, SumLIDElement)):
            other_dic = other.__struct__()
            new_dic = {}
            for key in other_dic:
                new_dic[key*self] = other_dic[key]

            return SumLIDElement(self.parent(), new_dic)
        elif(isinstance(other, ProductLIDElement)):
            return ProductLIDElement(self.parent(), self, other.__struct__())
        else:
            return ProductLIDElement(self.parent(), self, other)

    def __inner_pow__(self, other):
        return ProductLIDElement(self.parent(), {self:other})

    ###############################
    ### Equality methods
    ###############################
    def __eq__(self, other):
        if(self._is_pure_in_base(other)):
            other = self.parent()(other)
        if(isinstance(other, LazyIDElement)):
            if(isinstance(other, SimpleLIDElement)):
                return self.raw() == other.raw()
            else:
                return other.__eq__(self)

        return False

    def __hash__(self):
        return hash(self.raw())%_MAX_INTEGER

    ###############################
    ### Representation methods
    ###############################
    def __inner_printing__(self, method):
        return "Simple(%s)" %(method(self.raw()))

#####################################################
### Class for Product of LazyIDElements
#####################################################
class ProductLIDElement(LazyIDElement):
    def __init__(self, parent, *input):
        super(ProductLIDElement, self).__init__(parent)

        self.__factors = {}

        for el in input:
            self.__add_element(el)
        self.__simplified = False
        #self.simplify()

    def __add_element(self, el, n=1):
        ## Checking the n argument
        if(n == 0):
            return
        elif(n < 0):
            raise ValueError("Impossible have a negative exponent")

        ## If we are zero, we do nothing
        zero = self.parent().zero()
        one = self.parent().one()
        if(zero in self.__struct__()):
            return

        ## Other structures checking
        if(isinstance(el,list)):
            for aux in el:
                self.__add_element(aux,n)
        elif(isinstance(el, dict)):
            for aux in el:
                self.__add_element(aux,el[aux])
        ## Checking if the element is zero 9simplify operations
        elif(isinstance(el,LazyIDElement) and zero == el):
            self.__factors = {zero : 1}
            return
        elif((not isinstance(el, LazyIDElement)) and zero.raw() == el):
            self.__factors = {zero : 1}
            return
        ## We do nothing if we are adding +1
        elif(isinstance(el,LazyIDElement) and one == el):
            return
        elif((not isinstance(el, LazyIDElement)) and one.raw() == el):
            return
        ## Otherwise, we do as usual
        elif(self._is_pure_in_base(el)):
            self.__add_element(SimpleLIDElement(self.parent(),el),n)
        elif(isinstance(el,SimpleLIDElement)):
            self.__factors[el] = self.__factors.get(el,0)+n
        else:
            raise Exception("Impossible to put a %s in a Product Lazy Element" %type(el))

    ###############################
    ### Overridden methods
    ###############################
    def simplify(self):
        if(not self.__simplified):
            self.__simplified = True
            current_dic = self.__struct__()

            new_dic = {}

            for key in current_dic:
                current = current_dic[key]
                s_key = key.simplify()
                if(s_key.is_zero()):
                    self.__factors = {self.parent().zero():1}
                    return self.parent().zero()
                if((not (s_key.is_one())) and (current > 0)):
                    new_dic[s_key] = new_dic.get(s_key, 0) + current_dic[key]

            mone = SimpleLIDElement(self.parent(),-self.base().one())
            if(mone in new_dic):
                new_dic[mone] = new_dic[mone]%2

            self.__factors = new_dic

        if(len(self.__factors) == 0):
            return self.parent().one()

        return self

    def derivative(self, *input):
        self.simplify()

        resList = []
        aux_dic = {}
        current_dic = self.__struct__()

        #Preparing the aux_dic variable
        for key in current_dic:
            aux_dic[key] = current_dic[key]

        # Iterating for each element
        for key in current_dic:
            # Creating the new element to the sum
            der = key.derivative(*input)
            aux_dic[key] = max(0,aux_dic[key]-1)
            aux_dic[der] = aux_dic.get(der, 0)+1
            resList += [{ProductLIDElement(self.parent(), aux_dic) : current_dic[key]}]

            #Restoring the aux_dic
            aux_dic[key] = current_dic[key]
            if(der in current_dic):
                aux_dic[der] = aux_dic[der]-1
            else:
                del aux_dic[der]

        return SumLIDElement(self.parent(), resList)

    ###############################
    ### Abstract methods implementation
    ###############################
    def get_basic_elements(self):
        res = set()
        for key in self.__struct__().keys():
            res = res.union(key.get_basic_elements())
        return res

    def __compute_raw_element__(self):
        res = self.base().one()

        current_dic = self.__struct__()
        for key in current_dic:
            res *= (key.raw())**current_dic[key]

        return res

    def __change_domain__(self, newParent):
        if(newParent == self.parent()):
            return self

        new_dic = {}
        current_dic = self.__struct__()

        for key in current_dic:
            new_dic[key.__change_domain(newParent)] = current_dic[key]

        return ProductLIDElement(newParent, new_dic)

    def __compute_max_divisor__(self):
        return SumLIDElement(self.parent(), self)

    def __struct__(self):
        return self.__factors

    def __inner_is_multiple__(self, element):
        if(self._is_pure_in_base(element)):
            element = self.parent()(element)

        if(isinstance(element, LazyIDElement)):
            if(element.is_one()):
                return True
            elif(isinstance(element, SimpleLIDElement)):
                return not(self.__struct__().get(element) is None)
            elif(isinstance(element, ProductLIDElement)):
                return self.gcd(element) == element
            elif(isinstance(element, SumLIDElement)):
                el_dic = element.__struct__()
                if(len(el_dic) == 1):
                    key = el_dic.keys()[0]
                    if(el_dic[key] == 1):
                        return self.is_multiple_of(key)

        return False

    def __compute_division__(self, element):
        if(not isinstance(element, LazyIDElement)):
            return self.__compute_division__(SimpleLIDElement(self.parent(),element))

        if(isinstance(element, SimpleLIDElement)):
            inner = element
            number = 1
        elif(isinstance(element, ProductLIDElement)):
            inner = element
            number = 1
        elif(isinstance(element, SumLIDElement)):
            inner = element.__struct__().keys()[0]
            number = element.__struct__()[inner]

        if(number != 1 and number != -1):
            raise ValueError("Impossible Exception: can not perform division")

        new_dic = {}
        current_dic = self.__struct__()
        if(isinstance(inner, SimpleLIDElement)):
            for key in current_dic:
                new_dic[key] = current_dic[key]
            new_dic[inner] = new_dic.get(inner,0)-1
            if(new_dic[inner] == 0):
                del new_dic[inner]
        elif(isinstance(inner, ProductLIDElement)):
            for key in current_dic:
                value = current_dic[key]-inner.__struct__().get(key,0)
                if(value != 0):
                    new_dic[key] = value
        else:
            raise TypeError("Error with types wile dividing in a Product Lazy Element (%s)" %type(element))

        if(number == 1):
            return ProductLIDElement(self.parent(), new_dic).simplify()
        else: ## number == -1
            return (ProductLIDElement(self.parent(), new_dic))._neg_().simplify()

    def __inner_is_zero__(self):
        zero = self.parent().zero()
        return zero in self.__struct__()

    def __inner_is_one__(self):
        self.simplify()
        return (len(self.__struct__()) == 0)


    def __inner_add__(self, other):
        if(isinstance(other, SumLIDElement)):
            return SumLIDElement(self.parent(), self, other.__struct__())
        else:
            return SumLIDElement(self.parent(), self, other)

    def __inner_neg__(self):
        return SumLIDElement(self.parent(), {self:-1})
        #return self*(-self.parent().one())

    def __inner_mul__(self, other):
        if(isinstance(other, SumLIDElement)):
            other_dic = other.__struct__()
            new_dic = {}
            for key in other_dic:
                new_dic[key*self] = other_dic[key]

            return SumLIDElement(self.parent(), new_dic)
        elif(isinstance(other, ProductLIDElement)):
            return ProductLIDElement(self.parent(), self.__struct__(), other.__struct__())
        else:
            return ProductLIDElement(self.parent(), self.__struct__(), other)

    def __inner_pow__(self, other):
        current_dic = self.__struct__()
        new_dic = {}

        for key in current_dic:
            new_dic[key] = current_dic[key]*other
        return ProductLIDElement(self.parent(), new_dic)

    ###############################
    ### Equality methods
    ###############################
    def __eq__(self, other):
        if(self._is_pure_in_base(other)):
            other = self.parent()(other)

        current_dic = self.__struct__()
        if(len(current_dic) == 0):
            return other == 1
        if(isinstance(other, LazyIDElement)):
            if(isinstance(other, SimpleLIDElement)):
                return (len(current_dic) == 1 and current_dic.get(other,0) == 1)
            elif(isinstance(other, ProductLIDElement)):
                other_dir = other.__struct__()
                if(len(other_dir) == len(current_dic)):
                    for key in current_dic:
                        if(not(current_dic[key] == other_dir.get(key,0))):
                            return False
                    return True
            elif(isinstance(other, SumLIDElement)):
                return other.__eq__(self)

        return False

    def __hash__(self):
        res = 1
        current_dic = self.__struct__()

        for key in current_dic:
            res *= (hash(key)**current_dic[key] % _MAX_INTEGER)
        return res

    ###############################
    ### Representation methods
    ###############################
    def __inner_printing__(self, method):
        res = "ProductOf("
        current_dic = self.__struct__()
        if(len(current_dic) != 0):
            first = True
            for key in current_dic:
                if(not first):
                    res += " * "
                else:
                    first = False
                res += "(%s)^%s" %(method(key),current_dic[key])
        res += ")"
        return res

#####################################################
### Class for Sum of LazyIDElements
#####################################################
class SumLIDElement(LazyIDElement):
    def __init__(self, parent, *input):
        super(SumLIDElement, self).__init__(parent)

        self.__summands = {}
        self.__simplified = False

        for el in input:
            self.__add_element(el)
        #self.simplify()

    def __add_element(self, el, n=1):
        ## Checking the n argument
        if(n == 0):
            return

        zero = self.parent().zero()

        ## Checking other structures
        if(isinstance(el,list)):
            for aux in el:
                self.__add_element(aux,n)
        elif(isinstance(el, dict)):
            for aux in el:
                self.__add_element(aux,el[aux]*n)
        ## We do nothing if we want to add the zero element
        elif(isinstance(el,LazyIDElement) and zero == el):
            return
        elif((not isinstance(el, LazyIDElement)) and zero.raw() == el):
            return
        ## Otherwise, we do as usual
        elif(self._is_pure_in_base(el)):
            self.__add_element(SimpleLIDElement(self.parent(),el),n)
        elif(isinstance(el,SimpleLIDElement) or isinstance(el, ProductLIDElement)):
            self.__summands[el] = self.__summands.get(el,0)+n
        elif(isinstance(el, SumLIDElement)):
            self.__add_element(el.__struct__(),n)
        else:
            raise Exception("Impossible to put a %s in a Sum Lazy Element" %type(el))

    ###############################
    ### Overridden methods
    ###############################
    def gcd(self,*input):
        max_divisors = []
        for el in input:
            if(self._is_pure_in_base(el)):
                el = self.parent()(el)

            if(isinstance(el, LazyIDElement)):
                max_divisors += [el.max_divisor()]
            else:
                raise TypeError("Impossible compute gcd with %s" %(type(el)))

        myProd = self.__struct__().keys()[0]
        products = [el.__struct__().keys()[0] for el in max_divisors]
        vals = [self.__struct__()[myProd]] + [max_divisors[i].__struct__()[products[i]] for i in range(len(products))]
        val_gcd = gcd(vals)

        new_dic = {}
        current_dic = myProd.__struct__()
        for key in current_dic:
            minimum = current_dic[key]
            for el in products:
                minimum = min(minimum, el.__struct__().get(key,0))
                if(minimum == 0):
                    break
            if(minimum > 0):
                new_dic[key] = minimum
        return SumLIDElement(self.parent(), {ProductLIDElement(self.parent(),new_dic) : val_gcd})


    def simplify(self):
        if(not self.__simplified):
            self.__simplified = True
            current_dic = self.__struct__()

            new_dic = {}
            for key in current_dic:
                current = current_dic[key]
                s_key = key.simplify()
                if((not (s_key.is_zero())) and (not(current == 0))):
                    new_dic[s_key] = new_dic.get(s_key,0) + current

            self.__summands = new_dic

        if(len(self.__summands) == 0):
            return self.parent().zero()

        return self

    def derivative(self, *input):
        current_dic = self.__struct__()
        new_dic = {}

        for key in current_dic:
            der = key.derivative(*input)
            new_dic[der] = new_dic.get(der,0)+current_dic[key]

        return SumLIDElement(self.parent(), new_dic)

    ###############################
    ### Abstract methods implementation
    ###############################
    def get_basic_elements(self):
        res = set()
        for key in self.__struct__().keys():
            res = res.union(key.get_basic_elements())
        return res

    def __compute_raw_element__(self):
        res = self.base().zero()

        current_dic = self.__struct__()
        for key in current_dic:
            res += (key.raw())*current_dic[key]

        return res

    def __change_domain__(self, newParent):
        if(newParent == self.parent()):
            return self

        new_dic = {}
        current_dic = self.__struct__()

        for key in current_dic:
            new_dic[key.__change_domain(newParent)] = current_dic[key]

        return SumLIDElement(newParent, new_dic)

    def __compute_max_divisor__(self):
        current_dic = self.__struct__()
        max_divisors = [SumLIDElement(self.parent(), {key.max_divisor() : current_dic[key]}) for key in current_dic]

        if(len(max_divisors) > 0):
            return max_divisors[0].gcd(*max_divisors[1:])

        return SumLIDElement(self.parent(), ProductLIDElement(self.parent()))

    def __struct__(self):
        return self.__summands

    def __inner_is_multiple__(self, element):
        max_divisor = self.max_divisor()
        inner = max_divisor.__struct__().keys()[0]
        if(isinstance(element, SimpleLIDElement)):
            return inner.is_multiple_of(element)
        elif(isinstance(element, ProductLIDElement)):
            return inner.is_multiple_of(element)
        elif(isinstance(element, SumLIDElement)):
            if(len(element.__struct__()) == 1):
                number = max_divisor.__struct__()[inner]
                other_inner = element.__struct__().keys()[0]
                other_number = element.__struct__()[other_inner]

                return (ZZ(other_number).divides(number)) and (inner.is_multiple_of(other_inner))

        return False

    def __compute_division__(self, element):
        if(isinstance(element, SimpleLIDElement)):
            inner = element
            number = 1
        elif(isinstance(element, ProductLIDElement)):
            inner = element
            number = 1
        elif(isinstance(element, SumLIDElement)):
            inner = element.__struct__().keys()[0]
            number = element.__struct__()[inner]

        new_dic = {}
        current_dic = self.__struct__()
        try:
            for key in current_dic:
                new_dic[key.__compute_division__(inner)] = ZZ(current_dic[key]/number)

            return SumLIDElement(self.parent(), new_dic)
        except TypeError:
            raise ValueError("Impossible Exception: can not perform division because integer coefficients")

    def __inner_is_zero__(self):
        self.simplify()
        return (len(self.__struct__()) == 0)

    def __inner_is_one__(self):
        self.simplify()
        return self == self.parent().one()

    def __inner_add__(self, other):
        if(isinstance(other, SumLIDElement)):
            return SumLIDElement(self.parent(), self.__struct__(), other.__struct__())
        else:
            return SumLIDElement(self.parent(), self.__struct__(), other)

    def __inner_neg__(self):
        new_dic = {}
        current_dic = self.__struct__()

        for key in current_dic:
            new_dic[key] = -current_dic[key]
        return SumLIDElement(self.parent(), new_dic)

    def __inner_mul__(self, other):
        if(isinstance(other, SumLIDElement)):
            current_dic = self.__struct__()
            other_dic = other.__struct__()
            new_dic = {}
            for key_current in current_dic:
                for key_other in other_dic:
                    el = key_current*key_other
                    new_dic[el] = new_dic.get(el,0)+current_dic[key_current]*other_dic[key_other]

            return SumLIDElement(self.parent(), new_dic)
        else:
            current_dic = self.__struct__()
            new_dic = {}
            for key in current_dic:
                new_dic[key*other] = current_dic[key]

            return SumLIDElement(self.parent(), new_dic)

    def __inner_pow__(self, other):
        aux = self.parent().one()
        for _ in range(other):
            aux = aux*self
        return aux

    ###############################
    ### Equality methods
    ###############################
    def __eq__(self, other):
        if(self._is_pure_in_base(other)):
            other = self.parent()(other)

        current_dic = self.__struct__()
        if(len(current_dic) == 0):
            return other == 0
        elif(len(current_dic) == 1 and (not isinstance(other, SumLIDElement))):
            key = current_dic.keys()[0]
            return (current_dic[key] == 1) and (key == other)
        elif(isinstance(other, SumLIDElement)):
            other_dir = other.__struct__()
            if(len(other_dir) == len(current_dic)):
                for key in current_dic:
                    if(not(current_dic[key] == other_dir.get(key,0))):
                        return False
                return True

        return False

    def __hash__(self):
        res = 0
        current_dic = self.__struct__()

        for key in current_dic:
            res += (hash(key)*current_dic[key] % _MAX_INTEGER)
        return res

    ###############################
    ### Representation methods
    ###############################
    def __inner_printing__(self, method):
        res = "SumOf("
        current_dic = self.__struct__()
        if(len(current_dic) != 0):
            first = True
            for key in current_dic:
                if(not first):
                    res += " + "
                else:
                    first = False
                res += "%s*(%s)" %(current_dic[key],method(key))
        res += ")"
        return res

#####################################################
### Class for Lazy Integral Domain
#####################################################
class LazyIntegralDomain(UniqueRepresentation, IntegralDomain):
    Element = SimpleLIDElement

    Fraction_Field = None

    def __init__(self, base):
        if base not in _IntegralDomains:
            raise ValueError("%s is no integral domain" % base)
        IntegralDomain.__init__(self, base, category=_IntegralDomains)

        self._zero_element = SimpleLIDElement(self, base.zero())
        self._one_element = SimpleLIDElement(self, base.one())

        self.base().register_conversion(LIDSimpleMorphism(self, self.base()))


    def fraction_field(self):
        if(not(LazyIntegralDomain.Fraction_Field is None)):
            return LazyIntegralDomain.Fraction_Field(self) #pylint: disable=not-callable
        return super(LazyIntegralDomain, self).fraction_field()


    ### Coercion methods
    def _coerce_map_from_(self, S):
        coer = None
        if(isinstance(S, LazyIntegralDomain)):
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
        if(len(kwds) > 1):
            raise TypeError("Unexpected argument for _element_constructor_")
        if(len(args) < 1):
            print(str(args))
            raise ValueError("Impossible to build a lazy element without arguments")

        i = 0
        if(len(args) >= 2):
            if(not (args[0] is self)):
                raise ValueError("What the .... are you sending to this method?")
            i = 1
        X = args[i]

        try:
            if(not isinstance(X, LazyIDElement)):
                X_is_int = (X in ZZ) or (type(X) == int)
                if((X_is_int) and (not (self.base() is ZZ))):
                    if(X == 0):
                        return self.zero()
                    elif(X == 1):
                        return self.one()
                    else:
                        return SumLIDElement(self, {self.base().one() : ZZ(X)})

                return SimpleLIDElement(self, self.base()(X))
            else:
                if(X.parent() is self):
                    return X
                elif(self._has_coerce_map_from(X.parent().base())):
                    return X.__change_domain__(self)
                else:
                    return self._element_constructor_(X.raw())
        except TypeError:
            raise TypeError("This element can not be casted to %s" %repr(self))

    def construction(self):
        return (LazyIntegralDomainFunctor(), self.base())

    def __contains__(self, X):
        try:
            return (X.parent() is self) or (self._has_coerce_map_from(X.parent()))
        except AttributeError:
            try:
                self(X)
                return True
            except Exception:
                return False

    # Other Integral Domain methods
    def _repr_(self):
        return "LazyDomain(%s)"%repr(self.base())

    def base_ring(self):
        return self.base().base_ring()

    def characteristic(self):
        return self.base().characteristic()

    def _an_element_(self):
        return self.one()

    def element(self, X):
        return self(X)

    # Ring is_* methods
    def is_field(self):
        return self.base().is_field()

    def is_finite(self):
        return self.base().is_finite()

    def is_integrally_closed(self):
        return self.base().is_integrally_closed()

    def is_noetherian(self):
        return self.base().is_noetherian()

#####################################################
### Construction Functor for LID
#####################################################
class LazyIntegralDomainFunctor (ConstructionFunctor):
    def __init__(self):
        ID = _IntegralDomains
        self.rank = 20
        super(LazyIntegralDomainFunctor, self).__init__(ID,ID)

    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        if(isinstance(x, LazyIntegralDomain)):
            return x.base()
        return x

    def _apply_functor(self, x):
        return LazyIntegralDomain(x)

#####################################################
### General Morphism for return to basic rings
#####################################################
class LIDSimpleMorphism (Map):
    def __init__(self, domain, codomain):
        super(LIDSimpleMorphism, self).__init__(domain, codomain)

    def _call_(self, p):
        return self.codomain()(p.raw())

#####################################################
### Global and static elements
#####################################################
__MAP_TO_LAZY_DOMAINS = {}
def LazyDomain(X):
    if(not X in __MAP_TO_LAZY_DOMAINS):
        __MAP_TO_LAZY_DOMAINS[X] = LazyIntegralDomain(X)

    return __MAP_TO_LAZY_DOMAINS[X]


