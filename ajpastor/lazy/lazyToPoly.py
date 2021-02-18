r"""
Python file an abstract class LazyToPoly. 

This module includes the abstract basic definition of any ConversionSystem that use as basis computations
a variable polynomial ring which variables increase under demand of the user. It performs several simplifications
to avoid adding too many (unnecessary) variables.
        
EXAMPLES::

    sage: from ajpastor.lazy.lazyToPoly import *

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

_sage_const_1 = Integer(1); _sage_const_0 = Integer(0)

from .lazyIDElements import *;
from .lazyFracField import *;
from .conversion import ConversionSystem;

class LazyToPoly(ConversionSystem):
    def __init__(self, base, *args):

        if(not isinstance(base, LazyIntegralDomain)):
            base = LazyIntegralDomain(base);
            
        super(LazyToPoly,self).__init__(base);
        
        self.__basic = base.base();
        
        self.__map_c_to_v = {};
        self.__map_v_to_c = {};
        
        self.__inner_poly_ring = None;
        for element in args:
            self.__add_components(element);
            
        if(len(self.__map_c_to_v) > _sage_const_0 ):
            self.__inner_poly_ring = PolynomialRing(self.base().base_ring(), self.__map_v_to_c.keys());
            self.__is_polynomial = True;
        else:
            self.__inner_poly_ring = base.base_ring();
        self.__inner_poly_field = self.poly_ring().fraction_field();
        
        self.__map_v_to_c = {self.poly_ring()(key): self.__map_v_to_c[key] for key in self.__map_v_to_c};
    
    ## Abstract methods of ConversionSystem
    # Public
    def poly_ring(self):
        return self.__inner_poly_ring;
        
    def poly_field(self):
        return self.__inner_poly_field;
    
    def map_of_vars(self):
        return self.__map_v_to_c;
        
    # Protected
    def _to_poly_element(self, element):
        if(not element in self.base()):
            raise TypeError("The element is not an element in the base ring");
            
        if(element in self.__basic):
            element = self.base()(element);
            
        if(isinstance(element, SimpleLIDElement)):
            basic = element.get_basic_elements();
            if(len(basic) == _sage_const_0 ):
                return self.poly_ring()(element.raw());
            else:
                # Converting the simple element
                # Trying to find a variable
                el = self.__v(element);
                if(el is None):
                    raise ValueError("Impossible to cast the element to a polynomial with this conversion system");
                return self.poly_ring()(el);
        elif(isinstance(element, ProductLIDElement)):
            res = self.poly_ring().one();
            current_dic = element.__struct__();
            for key in current_dic:
                res *= self.to_poly(key)**current_dic[key];
            return res;
        elif(isinstance(element, SumLIDElement)):
            res = self.poly_ring().zero();
            current_dic = element.__struct__();
            for key in current_dic:
                res += self.to_poly(key)*current_dic[key];
            return res;
        else:
            raise ValueError("Impossible to cast the element. Not recognized type");
    
    ## Mixing conversions systems
    def _mix_conversion(self, conversion):
        if(isinstance(conversion, LazyToPoly)):
            return LazyToPoly(self.base(), self.__map_c_to_v.keys(), conversion.__map_c_to_v.keys());
        if(conversion in self.base().fraction_field()):
            if(conversion in self.base()):
                return LazyToPoly(self.base(), self.__map_c_to_v.keys(), self.base()(conversion));
            return LazyToPoly(self.base(), self.__map_c_to_v.keys(), self.base()(conversion.numerator()), self.base()(conversion.denominator()));
            
    
    ##########################################
    ### PRIVATE METHODS
    ##########################################
    def __add_components(self, element):
        '''
            Auxiliar method for adding new components to the variables (if needed).
            
            This method is private and should only be called during the initialization.
            
            This method allows to give as inputs:
                - Elements in `self.base()` or `self.base().fraction_field()`
                - Lists or Sets
                - Matrices with elements in `self.base()` or `self.base().fraction_field()`
        '''
        try:
            if(isinstance(element, list) or isinstance(element, set)):
                for el in element:
                    self.__add_components(el);
            else:
                try:
                    self.__add_components(element.numerator()); 
                    self.__add_components(element.denominator());
                    return;
                except AttributeError:
                    pass;
                try:
                    self.base().base_ring()(element);
                except Exception:
                    if(element in self.base().base()):
                        self.__add_components(self.base()(element));
                    elif(isinstance(element, SimpleLIDElement) and len(element.get_basic_elements()) > _sage_const_0 ):
                        if(not self.base()._coerce_map_from_(element.parent().base())):
                            raise TypeError("Incompatible lazy element to ring %s" %(self.base()));
                        if(self.__v(element, check=True) is None):
                            aux_var = var("x%d" %(len(self.__map_c_to_v)));
                            self.__map_c_to_v[element] = aux_var;
                            self.__map_v_to_c[aux_var] = element;
                    elif(isinstance(element, sage.matrix.matrix.Matrix)):
                        for row in element:
                            for el in row:
                                self.__add_components(el);
                    else:
                        self.__add_components(element.get_basic_elements());
        except AttributeError:
            raise TypeError("Impossible to polynomize unlazy elements (%s)" %(element));
            
    def __v(self, element, check=True):
        '''
            Auxiliar method to see if a SimpleLIDElement can be converted into a variable.
            
            This method check if `element` satisfies a linear equation of the form
                ``element == c*var + d``
            for some elements c,d in `self.base().base_ring()`.
            
            If some error occur during this checking (because the elements does not fit the interfaces usually uses here) we only will check the proper equality (``element == var``)
            
            RETURN:
                - A polynomial in `self.poly_ring()` or `self.poly_field()` if we can cast the element or `None` otherwise.
        '''
        try:
            if(element == _sage_const_0 ):
                return self.poly_ring().zero();
                
            ## Getting the unlazy element an the ring self.__basic
            R = self.__basic;
            el = R(element.raw());
            init_value = lambda p,n : R.sequence(p,n)*factorial(n);
            
            ## For each lazy element in the conversion system
            c = None; d = None; comp = None; k = None; ch_key = None;
            for key in self.__map_c_to_v.keys():
                k = R(key.raw());
                ## We compute the ratio c
                c = None; i = _sage_const_1 ;
                while(c is None):
                    el_init = init_value(el, i); k_init = init_value(k,i);
                    if(el_init == _sage_const_0  and k_init == _sage_const_0 ):
                        i += _sage_const_1 ;
                    elif(el_init == _sage_const_0  or k_init == _sage_const_0 ):
                        break;
                    else:
                        c = el_init/k_init;
                if(not (c is None)):
                    d = init_value(el, _sage_const_0 ) - c*init_value(k,_sage_const_0 );
                    comp = (el-d)/c;
                    if(comp == k):
                        ch_key = key;
                        break;
            
            ## If we found a conversion (i.e. ch_key variable is set)
            if(not (ch_key is None)):
                ## If the size is smaller than before, we change the associated function
                try:
                    var = self.__map_c_to_v[key];
                    if(check and (self.__size(comp) < self.__size(k))):
                        #print "Changing representative of a variable:\n\t- Before: %s\n\t- Now: %s" %(repr(k),repr(comp));
                        comp = self.base()(comp);
                        del self.__map_c_to_v[key];
                        self.__map_c_to_v[comp] = var;
                        if(self.__inner_poly_ring is None):
                            self.__map_v_to_c[var] = comp;
                        else:
                            self.__map_v_to_c[self.poly_ring()(var)] = comp;
                except Exception as e:
                    print("Exception caught");
                    print(e);
                    pass;
                ## We return the compute conversion
                return c*var + d;
            ## Otherwise, we return None
            return None;
                
            #if(el == c*k+d):
            #   return c*self.__map_c_to_v[key] + d;
            ## PREVIOUS VERSION: Just check the equality f == c*g
            #el = element.raw().zero_extraction;
            #for key in self.__map_c_to_v.keys():
            #    k = key.raw().zero_extraction;
            #    if(el[0] == k[0]):
            #        l = el[1](0)/k[1](0);
            #        if(el[1] == l*k[1]):
            #            return l*self.__map_c_to_v[key]; 
            #return None;
        except Exception:
            return self.__map_c_to_v.get(element);
        
    def __size(self, element):
        return element.size();

