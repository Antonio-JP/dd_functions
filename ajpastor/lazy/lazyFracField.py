r"""
Python file for a Lazy Fraction Field

This module implements a conversion system based on a Fraction Field. This requires a Lazy Integral Domain.

EXAMPLES::

    sage: from ajpastor.lazy.lazyFracField import *

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

from sage.all_cmdline import *   # import sage library

_sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_0 = Integer(0); _sage_const_25 = Integer(25)

# Some needed imports
from sage.structure.element import FieldElement;
from sage.rings.ring import Field;
from sage.structure.unique_representation import UniqueRepresentation;
from sage.categories.quotient_fields import QuotientFields;
from sage.categories.pushout import ConstructionFunctor;

# risc.ajpastor imports
from .lazyIDElements import *;

#####################################################
### Class for Lazy Fraction Field Elements
#####################################################
class LazyFFElement(FieldElement):
    def __init__(self, parent,n,d=None):
        if(not isinstance(parent, LazyFracField)):
            raise TypeError("The parent of a fraction must be a Fraction Field");
            
        B = parent.base(); # B is the lazy domain
        ### Checking/Adapting numerator
        if(not(n in B)):
            raise TypeError("Element for numerator must be in %s" %(repr(B)));
        elif(not (isinstance(n, LazyIDElement))):
            n = B(n);
            
        ### Checking/Adapting denominator
        if(d is None):
            d = B.one();
        elif(not (d in B)):
            raise TypeError("Element for denominator must be in %s" %(repr(B)));
        elif(d == B.zero()):
            raise ZeroDivisionError("The denominator can not be zero");
        elif(not (isinstance(d, LazyIDElement))):
            d = B(d);
        elif(isinstance(d, SumLIDElement)):
            #raise TypeError("No additions are allowed as denominators in a Lazy Fraction Field");
            #d = B(d.raw());
            pass;
            
        self.__n = n;
        self.__d = d;
        FieldElement.__init__(self,parent);
        
    def numerator(self):
        return self.__n;
        
    def denominator(self):
        return self.__d;
        
    def _repr_(self):
        return "(%s):(%s)"%(repr(self.numerator()),repr(self.denominator()));
        
    def __str__(self):
        return "(%s):(%s)"%(str(self.numerator()),str(self.denominator()));
        
    def _add_(self, other):
        if(not(other in self.parent())):
            return NotImplemented;
        if(not isinstance(other, LazyFFElement)):
            other = self.parent()(other);
            
        N = self.numerator()*other.denominator()+self.denominator()*other.numerator();
        D = self.denominator()*other.denominator();
        return LazyFFElement(self.parent(), N, D).simplify();
        
    def _sub_(self, other):
        if(not(other in self.parent())):
            return NotImplemented;
        if(not isinstance(other, LazyFFElement)):
            other = self.parent()(other);
            
        N = self.numerator()*other.denominator()-self.denominator()*other.numerator();
        D = self.denominator()*other.denominator();
        return LazyFFElement(self.parent(), N, D).simplify();
        
    def _neg_(self):
        return LazyFFElement(self.parent(), -self.numerator(), self.denominator());
        
    def _mul_(self, other):
        if(not(other in self.parent())):
            return NotImplemented;
        if(not isinstance(other, LazyFFElement)):
            other = self.parent()(other);
            
        N = self.numerator()*other.numerator();
        D = self.denominator()*other.denominator();
        return LazyFFElement(self.parent(), N, D).simplify();
        
    def _div_(self, other):
        if(not(other in self.parent())):
            return NotImplemented;
        if(not isinstance(other, LazyFFElement)):
            other = self.parent()(other);
            
        N = self.numerator()*other.denominator();
        D = self.denominator()*other.numerator();
        return LazyFFElement(self.parent(), N, D).simplify();
        
    ###############################
    ### Equality methods
    ############################### 
    def __eq__(self, other):
        self.simplify();
        try:
            if(isinstance(other, LazyFFElement)):
                other.simplify();
                return (self.numerator() == other.numerator()) and (self.denominator() == other.denominator());
            elif(isinstance(other, LazyIDElement)):
                other = other.simplify();
                
            return (self.numerator() == other) and (self.denominator() == self.parent().base().one());
        except Exception as e:
            return False;
        
        
    ###############################
    ### Other methods
    ############################### 
    def raw(self):
        self.simplify();
        if(self.denominator().raw() == _sage_const_1 ):
            return self.numerator().raw();
        raise ValueError("Impossible to compute an element within the domain: non 1 denominator");
    
    def simplify(self):
        n = self.numerator().simplify();
        d = self.denominator().simplify();
        
        ## Special case: numerator is zero --> Return the zero element
        if(n == self.parent().base().zero()):
            self.__n = self.parent().base().zero();
            self.__d = self.parent().base().one();
            return self;
            
        ## Special case: numerator and denominator are the same --> Return the one element
        if(n == d):
            self.__n = self.parent().base().one();
            self.__d = self.parent().base().one();
            return self;
            
        ## Generic algorithm: compute gcd of numerator and denominator and divide by it
        num_divisor = n.max_divisor();
        den_divisor = d.max_divisor();
        common = num_divisor.gcd(den_divisor);
        
        n = n.divide(common);
        d = d.divide(common);
        
        ## Special case for sign: check if the denominator has all negative. In that case
        ## change the sign of the numerator.
        if(isinstance(d, SumLIDElement)):
            toChange = True;
            for key in d.__struct__():
                toChange = (d.__struct__()[key] < _sage_const_0 );
                if(not toChange):
                    break;
            
            if(toChange):
                n = -n;
                d = -d;
                
        self.__n = n;
        self.__d = d;
        return self;
        
    def reduce(self):
        return self.simplify();
        
    def derivative(self, *input):
        try:
            N = self.numerator().derivative(*input)*self.denominator()-self.denominator().derivative(*input)*self.numerator();
            D = self.denominator()**_sage_const_2 ;
            
            return LazyFFElement(self.parent(), N, D).simplify();
        except AttributeError:
            raise AttributeError("Impossible derivate elements of %s" %(self.parent().base()));
            
    def get_basic_elements(self):
        return self.numerator().get_basic_elements().union(self.denominator().get_basic_elements());
        
#####################################################
### Class for Lazy Fraction Fields
#####################################################
class LazyFracField(UniqueRepresentation, Field):
    Element = LazyFFElement;

    def __init__(self, base):
        if base not in IntegralDomains():
            raise ValueError("%s is no integral domain" % base);
        if (not isinstance(base, LazyIntegralDomain)):
            base = LazyDomain(base);
        Field.__init__(self, base, category=QuotientFields());
        
        self.base().register_conversion(LFFSimpleMorphism(self, self.base()));
        self.base().base().register_conversion(LFFSimpleMorphism(self, self.base().base()));
        try:
            self.base().base().fraction_field().register_conversion(LFFSimpleMorphism(self, self.base().base().fraction_field()));
        except Exception:
            pass;
        
    ### Coercion methods
    def _coerce_map_from_(self, S):
        coer = None;
        if(isinstance(S, LazyFracField)):
            coer = self.base()._coerce_map_from_(S.base());
        elif(S in QuotientFields()):
            coer = self.base()._coerce_map_from_(S.base());
        elif(S == self.base()):
            coer = True;
        else:
            coer = self.base()._coerce_map_from_(S);
            
        if(not(coer is False) and not(coer is None)):
            return True;
        return None;
        
    def _has_coerce_map_from(self, S):
        coer =  self._coerce_map_from_(S);
        return (not(coer is False) and not(coer is None));
        
    def _element_constructor_(self, *args, **kwds):
        el_class = self.element_class;
        if(len(args) < _sage_const_1 ):
            raise ValueError("Impossible to build a lazy element without arguments");
        
        i = _sage_const_0 ;
        if(args[_sage_const_0 ] is self):
            i = _sage_const_1 ;
            
        X = args[i];
        Y = None;
        
        if(len(args) > i+_sage_const_1 ):
            Y = args[i+_sage_const_1 ];
        
        try:
            if(isinstance(X, el_class)):
                if((not(Y is None)) and (Y in self)):
                    if(isinstance(Y, el_class)):
                        return X/Y;
                    else:
                        return X/(el_class(self,_sage_const_1 ,Y));
            else:
                try:
                    if(X.parent() in QuotientFields()):
                        return self._element_constructor_(X.numerator(), X.denominator());
                except AttributeError:
                    pass;
                return el_class(self, X,Y);
        except TypeError as e:
            raise TypeError("Can not cast %s to a Lazy Fraction of %s because:\n\t- %s" %(repr(X), repr(self.base()), e));
            
    def construction(self):
        return (LazyFracFieldFunctor(), self.base());
        
    def __contains__(self, X):
        try:
            return (X.parent() is self) or (self._has_coerce_map_from(X.parent()));
        except AttributeError:
            try:
                self(X)
                return True;
            except Exception:
                return False;
         
    def _repr_(self):
        return "LazyFractionField for(%s)"%repr(self.base().base());
        
    def base_ring(self):
        return self.base().base_ring();
        
    def characteristic(self):
        return self.base().characteristic();
        
    def _an_element_(self):
        return self.one();
        
    def element(self, n,d = None):
        return LazyFFElement(self, n,d);
        
## Changes in LazyIntegralDomain

LazyIntegralDomain.Fraction_Field = LazyFracField;
        
#####################################################
### Construction Functor for LID
#####################################################
class LazyFracFieldFunctor (ConstructionFunctor):
    def __init__(self):
        self.rank = _sage_const_25 ;
        super(LazyFracFieldFunctor, self).__init__(IntegralDomains(),QuotientFields());
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()));
        if(isinstance(x, LazyFracField)):
            return x.base();
        return x;
        
    def _apply_functor(self, x):
        return LazyIntegralDomain(x);
        
#####################################################
### General Morphism for return to basic rings
#####################################################
class LFFSimpleMorphism (sage.categories.map.Map):
    def __init__(self, domain, codomain):
        super(LFFSimpleMorphism, self).__init__(domain, codomain);
        
    def _call_(self, p):
        if(self.codomain() in QuotientFields()):
            return self.codomain()(p.numerator().raw(), p.denominator().raw());
        elif(self.codomain() in IntegralDomains()):
            return self.codomain()((p.numerator().divide(p.denominator())).raw());
            
        raise TypeError("Impossible the conversion of %s to %s" %(p, self.codomain()));

