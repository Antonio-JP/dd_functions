r'''
    File for a basic structure for lazy rings.

    A ring is a mathematical structured composed by a set of elements `R` 
    and two operations `+` and `\cdot` with the appropriate and intuitive 
    properties.

    For any computable ring (i.e., a ring where we can perform the operations
    `+` and `\cdot` algorithmically) we can always construct a *lazy ring*, i.e.,
    a lazy implementation of the operations of the rings using a polynomial
    ring for doing fast computations and evaluating those polynomials only 
    when knowing the exact element in `R` is required.

    This file contains the base implementation of a lazy ring. In terms of
    Sage coercion system, a lazy ring will be a ring structure with its 
    associated element structure. Both of them will have basic interfaces
    to work with the real element in `R` or the polynomial representation.

    EXAMPLES::

        sage: from ajpastor.lazy.lazy_ring import *
'''

from .lazy_element import LazyElement

from sage.all import CommutativeRing, CommutativeRings, IntegralDomains, parent, Matrix, vector
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing
from sage.structure.element import is_Matrix, is_Vector # pylint: disable=no-name-in-module
from sage.structure.unique_representation import UniqueRepresentation

_CommutativeRings = CommutativeRings.__classcall__(CommutativeRings)
_IntegralDomains = IntegralDomains.__classcall__(IntegralDomains)

class LazyRing(CommutativeRing, UniqueRepresentation):
    r'''
        Class representing a lazy ring.

        This class represents a ring which operations are performed lazily.
        This means that, inside this structure, operations such as addition,
        multiplication and derivation are performed as polynomial operations.

        All the elements inside this class will have a method to retrieve the
        actual value of the element in the original ring.

        INPUT:

        * ``ring``: the ring that this class will represent with lazy computations.

        TODO: add examples.    
    '''

    Element = LazyElement

    def __init__(self, ring):
        if(not ring in _CommutativeRings):
            raise TypeError("LazyRing must wrap an actual commutative ring")

        # Initializing the ring structure
        super().__init__(ring.base_ring())

        # Creating important data
        self.__ring = ring # attribute with the real ring

        # Looking for a valid name for variables
        possible_names = ['x', 'y', 'a', 'b', 'c', 'd', 'p', 'q']
        prev_gens = [str(v) for v in self.base().gens()]

        self.__poly = None
        for name in possible_names:
            if(not name in prev_gens):
                self.__poly = InfinitePolynomialRing(ring.base_ring(), name)
                break
        if(self.__poly is None):
            raise NameError("The base ring %s has too many generators")

        self.__var_to_real = {} # See method map_of_vars
        self.__real_to_var = {} # See method map_of_elements
        self.__used = 0 # Attribute for counting the number of used variables

    ring = property(lambda self: self.__ring) #: Immutable attribute for the real ring
    poly_ring = property(lambda self : self.__poly) #: Immutable attribute for the insider polynomial ring
    poly_field = property(lambda self : self.poly_ring.fraction_field()) #: Immutable attribute for the insider polynomial fraction field

    def map_of_vars(self):
        r'''
            Method to get the values of used variables.

            This method returns a dictionary. The keys of the dictionary are the strings of
            some variables of :func:`poly_ring` and the values are the real elements in 
            :func:`ring`.

            OUTPUT:

            A dictionary mapping used variables to real elements.

            TODO: add examples and tests
        '''
        return self.__var_to_real

    def map_of_elements(self):
        r'''
            Method to get the variables associated with some elements.

            This method returns a dictionary. The keys of the dictionary are some real elements in 
            :func:`ring` and the values are variables with which are represented in :func:`poly_ring`.

            OUTPUT:

            A dictionary mapping real elements to variables.

            TODO: add examples and tests
        '''
        return self.__var_to_real

    ## Inclusion methods
    def __contains__(self, element):
        r'''
            Method to see if an object is in this ring.

            This method decides whether an element can be represented in this 
            ring or not. Since we are working with lazy operations, we allow 
            elements of :func:`ring`, elements of :func:`poly_ring` or 
            lazy elements.

            INPUT:

            * ``element``: object to be checked.

            OUTPUT:

            ``True`` if ``element`` can be interpret as an element in ``self``,
            i.e., the call ``self(element)`` will succeed. ``False`` otherwise.

            TODO: add examples and tests.
        '''
        return parent(element) is self or element in self.ring or element in self.poly_ring

    def __call__(self, element):
        r'''
            Adds the lazy structure to an object (if possible).

            This method converts an object and provides the lazy operations
            for it. This element can be an actual element of ``self`` (see
            method :func:`__contains__`) or a more complex structure that
            will be preserved and each of its elements will be converted.

            The current accepted *complex* structures that we allow are:

            * Iterable objects: such as ``list``, ``tuple`` or ``set``.
            * Vectors: see :func:`~sage.structure.element.is_Vector`.
            * Matrices: see :func:`~sage.structure.element.is_Matrix`.
            * Fractions: this method will also work with fractions of 
              elements in :func:`ring`.

            INPUT:

            * ``element``: the object to be casted

            TODO: add examples and tests
        '''
        ## Cases accepted by self.__contains__
        if(parent(element) is self):
            return element
        elif(element in self.ring):
            return self._create_from_real(self.ring(element))
        elif(element in self.poly_ring):
            return self._create_from_poly(self.poly_ring(element))
        ## Cases of fractions
        elif(self.ring in _IntegralDomains):
            if(element in self.ring.fraction_field()):
                n = self(self.ring(element.numerator()))
                d = self(self.ring(element.denominator()))
                return n/d
            if(element in self.poly_field):
                n = self(self.poly_ring(element.numerator()))
                d = self(self.poly_ring(element.denominator()))
                return n/d
        ## Cases of other structures
        elif(is_Matrix(element)):
            return Matrix(self, [[self(el) for el in row] for row in element])
        elif(is_Vector(element)):
            return vector(self, [self(el) for el in element])
        elif(isinstance(element, list)):
            return [self(el) for el in element]
        elif(isinstance(element, set)):
            return set([self(el) for el in element])
        elif(isinstance(element, tuple)):
            return tuple([self(el) for el in element])
        else:
            raise TypeError("Wrong type: Impossible to get lazy element from (%s)" %(element))

    def _create_from_real(self, element):
        r'''
            Method that create a lazy element from a real element

            This method takes an element from :func:`ring` and cast it into 
            an actual element of ``self``. While creating the object,
            the polynomial (or lazy) representation is computed.

            There are different possible strategies for deciding when or how
            to add new variables to the lazy system. The default option
            is to add a new variable whenever the object has not yet been seen.

            Different strategies can be implemented by overriding this method
            in any subclass.

            INPUT:

            * ``element``: an element in :func:`ring`.

            OUTPUT:

            An element in ``self``.

            TODO: add tests and examples
        '''
        if(not element in self.map_of_elements()):
            x = self.poly_ring.gens()[0]
            self.map_of_elements()[element] = x[self.__used]
            self.map_of_vars()[str(x[self.__used])] = element
            self.__used += 1

        return self.Element(self, element, self.map_of_elements()[element])

    def _create_from_poly(self, element):
        r'''
            Method that create a lazy element from a polynomial

            This method takes an element from :func:`poly_ring` and cast it into 
            an actual element of ``self``. The real representation of the 
            object is **not** computed in this creation.

            INPUT:

            * ``element``: an element in :func:`poly_ring`.

            OUTPUT:

            An element in ``self``.

            TODO: add tests and examples
        '''  
        return self.Element(self, self.map_of_vars().get(str(element), None), element)

## GO ON WITH THE RELATIONS AND SIMPLIFY METHODS