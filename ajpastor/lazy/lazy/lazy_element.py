r"""
File for the element structure of Lazy rings

This file contains all the element structures for Lazy rings. See documentation
of :mod:`~ajpastor.lazy.lazy.lazy_ring` for further information.

AUTHORS:

    - Antonio Jimenez-Pastor (2012-05-25): initial version

"""

# ****************************************************************************
#  Copyright (C) 2021 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.structure.element import CommutativeRingElement # pylint: disable=no-name-in-module

def is_LazyElement(element):
    r'''
        Method to decide whether or not an element is a polynomial with infinite variables.

        This is a call to ``isinstance`` with the two main element classes of Infinite Polynomial
        Rings.
    '''
    return isinstance(element, LazyElement)

class LazyElement(CommutativeRingElement):
    r'''
        Class for elements in a :class:`~ajpastor.lazy.lazy.lazy_ring.LazyRing`.

        This class is used to represent any object on a :class:`~ajpastor.lazy.lazy.lazy_ring.LazyRing`.
        These objects have the particularity that are splitted in two parts: a lazy polynomial and 
        a real element.

        Computations are performed lazily using the polynomials and the computation of the real 
        object is only done when needed. The method :func:`real` will compute such value and
        all the methods starting with ``verified_*`` will do the usual computation but guaranteeing
        the real value of the output is computed.

        INPUT:

        * ``parent``: the parent structure (a :class:`~ajpastor.lazy.lazy.lazy_ring.LazyRing`) where ``self``
          will be included.
        * ``real``: the real element (see :func:`~ajpastor.lazy.lazy.lazy_ring.LazyRing.ring`)
        * ``polynomial``: the lazy representation of ``self``.
    '''
    def __init__(self, parent, real, polynomial):
        from .lazy_ring import LazyRing
        if(not isinstance(parent, LazyRing)):
            raise TypeError("The parent must be a LazyRing")
        if(not polynomial in parent.poly_ring):
            raise TypeError("The polynomial representation must be in the corresponding polynomial ring")

        super().__init__(parent)
        self.__real = real
        self.__polynomial = polynomial

    @property
    def real(self):
        r'''
            Attribute for the real element represented by ``self``.
        '''
        if(not self.computed()):
            self.__real = self.polynomial(**self.parent().map_of_vars)
        return self.__real

    def computed(self):
        r'''
            Method that checks if the real values has been computed.
        '''
        return not(self.__real is None)

    polynomial = property(lambda self: self.__polynomial) #: Attribute with the polynomial representation of ``self``.

    ## Arithmetic methods
    def _add_(self, x):
        return LazyElement(self.parent(), None, self.polynomial + x.polynomial)
    def _sub_(self, x):
        return LazyElement(self.parent(), None, self.polynomial - x.polynomial)
    def _mul_(self, x):
        print("here")
        return LazyElement(self.parent(), None, self.polynomial * x.polynomial)
    def _rmul_(self, x):
        return LazyElement(self.parent(), None, self.polynomial._rmul_(x.polynomial))
    def _lmul_(self, x):
        return LazyElement(self.parent(), None, self.polynomial._lmul_(x.polynomial))
    def __pow__(self, n):
        return LazyElement(self.parent(), None, self.polynomial**n)

    ## Simplicity methods
    def reduce(self, relations):
        r'''
            Method that reduces the current polynomial representation of a Lazy element

            This method changes the internal information about this lazy element (see 
            :func:`polynomial`). This could change the nature of the element, making it a
            very simple element.

            This method never discovers a new relation, and no computation in the real ring are
            performed.

            INPUT:

            * ``relations``: list of relations (i.e., polynomials that are equal to zero in the real
              ring).
            
            OUTPUT:

            The method returns ``self``.

            TODO: add examples and tests
        '''
        R = self.parent().poly_ring._P # polynomial ring where everything will be contained

        relations = [R(el) for el in relations]# We convert all the element in the relation to R
        poly = R(self.polynomial) # we convert the polynomial representation of self into R

        result = poly.reduce(relations) # reducing via the reduce method for polynomials
        
        self.__polynomial = self.parent().poly_ring(result) # changing the stored value
        return self

    ## Other operations
    def gcd(self, other):
        r'''
            Method that comptues the greatest common divisor of two elements.

            This method computes the GCD of ``self`` with another object of ``self.parent()``
            using the information within the lazy representation (see :func:`polynomial`).

            This method never discovers a new relation, and no computations in the real ring are
            performed. Moreover, the result may change after repetition, since the lazy 
            representation may change through time. 
        '''
        other = self.parent()(other)
        return LazyElement(self.parent(), None, self.polynomial.gcd(other.polynomial))

    def derivative(self, times=1):
        raise NotImplementedError()

    ## Equality methods
    def is_zero(self):
        r'''
            Method to check is an object is zero.

            This method checks if the current lazy representation of ``self`` is zero.
            This method does not perform any operation on the real ring (so it is a fast
            method) but it could change the output through time.

            For completely cheking if ``self`` is zero, use method :func:`verify_zero`.

            OUTPUT:

            ``True`` if the lazy representation of ``self`` is zero.

            TODO: add tests and examples
        '''
        ## We first simplify the element (in case new relations are found)
        self.parent().simplify(self)

        return self.polynomial == 0

    def verify_zero(self):
        r'''
            Method to check is an object is zero.

            This method checks if the real representation of ``self`` is zero.
            This method **performs** operations on the real ring. For a faster (but incomplete)
            checking, use method :func:`is_zero`.

            OUTPUT:

            ``True`` if ``self`` is zero.

            TODO: add tests and examples
        '''
        if(not self.computed()): # if it is not computed, we use the lazy information first
            if(self.is_zero()): # we see if the polynomial gets to zero
                return True
        ## Otherwise we use the real value of ``self``.
        result = self.real == 0
        if(result): # Updating the relations
            self.parent().add_relations(self)
            self.__real = self.parent().ring.zero()
            self.__polynomial = self.parent().poly_ring.zero()

        return result
    
    def is_one(self):
        r'''
            Method to check is an object is one.

            This method checks if the current lazy representation of ``self`` is one.
            This method does not perform any operation on the real ring (so it is a fast
            method) but it could change the output through time.

            For completely cheking if ``self`` is one, use method :func:`verify_one`.

            OUTPUT:

            ``True`` if the lazy representation of ``self`` is one.

            TODO: add tests and examples
        '''
        ## We first simplify the element (in case new relations are found)
        self.parent().simplify(self)

        return self.polynomial == 1

    def verify_one(self):
        r'''
            Method to check is an object is one.

            This method checks if the real representation of ``self`` is one.
            This method **performs** operations on the real ring. For a faster (but incomplete)
            checking, use method :func:`is_one`.

            OUTPUT:

            ``True`` if ``self`` is one.

            TODO: add tests and examples
        '''
        if(not self.computed()): # if it is not computed, we use the lazy information first
            if(self.is_one()): # we see if the polynomial gets to zero
                return True
        ## Otherwise we use the real value of ``self``.
        result = self.real == 1
        if(result): # Updating the relations
            self.parent().add_relations(self-1)
            self.__real = self.parent().ring.one()
            self.__polynomial = self.parent().poly_ring.one()

        return result

    def equals(self, other):
        r'''
            Method to check equality between objects.

            This method checks if the current lazy representation of ``self`` and ``other`` 
            are the same. This method does not perform any operation on the real ring (so it is a fast
            method) but it could change the output through time.

            For completely cheking if ``self`` is ``other``, use method :func:`verify_equals`.

            INPUT: 

            * ``other``: an object we will check if it is equals to ``self``.

            OUTPUT:

            ``True`` is the current lazy representation of ``self`` coincides with the 
            lazy representation of ``other``.

            TODO: add examples and tests.
        '''
        try:
            other = self.parent()(other)
            
            return (self-other).is_zero()
        except: # other can not be casted into ``self.parent()``
            return False

    def verify_equals(self, other):
        r'''
            Method to check equality between objects.

            This method checks if ``self`` and ``other`` are the same object.
            This method performs operations on the real ring that may be slow. 
            For a faster (but incomplete) checking of equality, use the method
            :func:`equals`.

            INPUT: 

            * ``other``: an object we will check if it is equals to ``self``.

            OUTPUT:

            ``True`` is ``self`` coincides with ``other``.

            TODO: add examples and tests.
        '''
        try:
            other = self.parent()(other)
            
            return (self-other).verify_zero()
        except: # other can not be casted into ``self.parent()``
            return False

    ## Representation methods
    def _repr_(self):
        if(not self.computed()):
            return "[%s]" %repr(self.polynomial)
        else:
            return "(%s [%s])" %(self.real, self.polynomial)

    def _latex_(self):
        return r"\mathcal{Lazy}(" + (r"%s \rightarrow" %self.real if self.computed() else "") + r"%s" %self.polynomial