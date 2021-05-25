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

from sage.all import CommutativeRing, CommutativeRings, IntegralDomains, parent, Matrix, vector, ideal, latex
from sage.categories.all import Morphism
from sage.categories.pushout import pushout, ConstructionFunctor
from sage.rings.fraction_field import is_FractionField
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

    @staticmethod
    def __classcall__(cls, ring):
        ## We avoid iterative constructions over lazy rings
        if(isinstance(ring, LazyRing)):
            ring = ring.ring

        return super().__classcall__(cls, ring)

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
        self.__relations = [] # Attribute for generators of known relations

        ## Setting new conversions to simpler structures
        current = self.ring
        morph = LazyRing_Base(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = LazyRing_Base(self, current)
            current.register_conversion(morph)

    ring = property(lambda self: self.__ring) #: Immutable attribute for the real ring
    poly_ring = property(lambda self : self.__poly) #: Immutable attribute for the insider polynomial ring
    poly_field = property(lambda self : self.poly_ring.fraction_field()) #: Immutable attribute for the insider polynomial fraction field
    relations = property(lambda self : self.__relations) #: Immutable attribute for the generators of current relations

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
        return self.__real_to_var

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
        ## Cases of__contains__
        if(element in self):
            return super().__call__(element)
        ## Cases of fractions
        if(self.ring in _IntegralDomains):
            if(element in self.ring.fraction_field()):
                n = self(self.ring(element.numerator()))
                d = self(self.ring(element.denominator()))
                return n/d
            if(element in self.poly_field):
                n = self(self.poly_ring(element.numerator()))
                d = self(self.poly_ring(element.denominator()))
                return n/d
        ## Cases of other structures
        if(is_Matrix(element)):
            return Matrix(self, [[self(el) for el in row] for row in element])
        if(is_Vector(element)):
            return vector(self, [self(el) for el in element])
        if(isinstance(element, list)):
            return [self(el) for el in element]
        if(isinstance(element, set)):
            return set([self(el) for el in element])
        if(isinstance(element, tuple)):
            return tuple([self(el) for el in element])

        raise TypeError("Error casting an element (%s) into the Lazy framework %s" %(element, self))

    def _element_constructor_(self, element):
        r'''
            Method to create an element in ``self`` from an object that is *in* ``self``.

            This method implements the way Sage construct an element. This can be use in general
            for checking if something is in ``self`` or, more precisely, to build an 
            object for any of the possible inputs allowed.

            INPUT:

            * ``element``: data from which construct a new object in ``self``.

            TODO: add examples and tests
        '''
        print("_element_constructor_")
        if(parent(element) is self):
            return element
        elif(element in self.ring):
            return self._create_from_real(self.ring(element))
        elif(element in self.poly_ring):
            return self._create_from_poly(self.poly_ring(element))
        raise TypeError("Type not recognized to create an element")
            
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

    ## Coercion methods
    def _has_coerce_map_from(self, S):
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))

    def _coerce_map_from_(self, S):
        if(self.ring._coerce_map_from_(S)):
            return True
        return None

    def construction(self):
        r'''
            Returns a functor that builds the :class:`Lazyring`.

            Method that construct a functor `F` and an commutative ring `R` such that ``self == F(R)``. This method allows the 
            coerce system in Sage to handle :class:`LazyElement` and :class:`LazyRing` appropriately.

            OUTPUT:

            This method returns a tuple `(F,R)` where `F` is a functor such that ``self == F(R)``.

            EXAMPLES::

                sage: from ajpastor.lazy.lazy.lazy_ring import *
                sage: A = LazyRing(QQ)
                sage: F,R = A.construction()
                sage: F == LazyRingFunctor()
                True
                sage: R == QQ
                True
                sage: B = LazyRing(A)
                sage: F,R = B.construction()
                sage: F == DDRingFunctor()
                True
                sage: R == QQ
                True
        '''
        return (LazyRingFunctor(), self.ring)

    def _pushout_(self, S):
        r'''
            Mathod to compute the pushout of ``self`` with ``S``.

            This method computes a :class:`LazyRing` that contains both ``self`` and ``S`` or returns ``None``.
            The idea behind this pushout is that:

            * If `R \subset S`, then the lazy ring of `R` is contained in the lazy ring of `S`.
            * For any ring `R`, it is contained in the lazy ring of `R`.

            INPUT:

            * ``S``: the other structure to compare.

            OUTPUT:

            ``None`` if there is no valid pushout from ``self`` or a :class:`LazyRing` contining both ``self`` and ``S``.

            TODO: add examples and tests.
        '''
        print("Here")
        try:
            if(isinstance(S, LazyRing)):
                R = pushout(self.ring, S.ring)
            else:
                R = pushout(self.ring, S)
        except: # any error implies there is not known pushout from ``self``.
            return None
        
        return LazyRing(R)

    def gens(self):
        return tuple(self(el) for el in self.ring.gens())

    def ngens(self):
        return len(self.gens())

    ## Relations and simplification methods
    def add_relations(self, relations):
        r'''
            Method that add new relations to a lazy system.

            This method takes a series of elements in ``self`` (which is checked using a
            call to ``self.simplify(relations)``) and then adds all the polynomial representations
            of the elements to the computed relations.

            This method assumes that the elements are indeed zero. Otherwise the 
            behavior of this method is not guaranteed.

            INPUT:

            * ``relations``: element in ``self`` or iterable of elements in ``self``. 

            OUTPUT:

            The final generators of the relations. 

            TODO: add examples and tests
        '''
        relations = self.simplify(relations)
        R = self.poly_ring._P # biggest polynomial ring found so far
        self.__relations = [R(el) for el in self.relations]
        if(relations in self): # just one relation
            if(relations.polynomial != 0):
                self.__relations += [R(relations.polynomial.polynomial())]
        elif(is_Vector(relations) or type(relations) in (tuple, list, set)):
            self.__relations += [R(el.polynomial.polynomial()) for el in relations if el.polynomial != 0] 
        if(len(self.relations) > 0):
            self.__relations = ideal(self._relations).groebner_basis()

        return self.relations

    def simplify(self, element):
        r'''
            Method to simplify an element involving the lazy system.

            This method simplifies a structure that contains lazy elements using the
            discovered relations (see :func:`relations`) in the lazy ring. This 
            will imply casting the element to a polynomial form, and substitute that
            representation for the reduced version.

            This method allows to simplify a wide variety of structures (as it did 
            the casting system into a lazy ring). Namely:

            * Iterable objects: such as ``list``, ``tuple`` or ``set``.
            * Vectors: see :func:`~sage.structure.element.is_Vector`.
            * Matrices: see :func:`~sage.structure.element.is_Matrix`.
            * Fractions: this method will also work with fractions of 
              elements in :func:`ring`.

            INPUT:

            * ``element``: the element to be simplified.

            OUTPUT:

            An object with the same structure as ``element`` but with all the
            lazy elements simplified.

            TODO: add examples and tests
        '''
        element = self(element)
        ## Element in the lazy system
        if(element in self):
            element.reduce(self.relations)
        ## Cases of fractions
        elif(self.ring in _IntegralDomains):
            if(is_FractionField(parent(element))):
                self.simplify(element.numerator())
                self.simplify(element.denominator())
                return element
        ## Cases of other structures
        elif(is_Matrix(element)):
            for row in element:
                for el in row:
                    self.simplify(el)
        elif(is_Vector(element)):
            for el in element:
                self.simplify(el)
        elif(isinstance(element, list)):
            for el in element:
                self.simplify(el)
        elif(isinstance(element, set)):
            for el in element:
                self.simplify(el)
        elif(isinstance(element, tuple)):
            for el in element:
                self.simplify(el)
        else:
            raise TypeError("Wrong type: Impossible to get lazy element from (%s)" %(element))

        return element

    ## Representation methods
    def _repr_(self):
        return "Lazy ring over [%s]" %(self.ring)

    def _latex_(self):
        return r"\mathcal{Lazy}(%s)" %(latex(self.ring))

    ## Element methods
    def one(self):
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from ajpastor.lazy.lazy.lazy_ring import *
                sage: R = LazyRing(QQ['x'])
                sage: R.one()
                1
        '''
        return self(1)
    
    def zero(self):
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from ajpastor.lazy.lazy.lazy_ring import *
                sage: R = LazyRing(QQ['x'])
                sage: R.zero()
                0
        '''
        return self(0)

    def random_element(self,*args,**kwds):
        r'''
            Creates a randome element in this ring.

            This method creates a random element in the base infinite polynomial ring and 
            cast it into an element of ``self``.
        '''
        try:
            p = self.ring.random_element(*args,**kwds)
        except AttributeError:
            p = self.ring.one()
        return self(p)

    ## Ring methods
    def is_integral_domain(self):
        return self.ring.is_integral_domain()

    def is_noetherian(self):
        return self.ring.is_noetherian()

    def is_field(self):
        return self.ring.is_field()

class LazyRingFunctor (ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`LazyRing`.

        This functor maps commutative rings into other structures that 
        implements the lazy computations as intended. This functor does
        not require any extra argument since it will create the corresponding
        :class:`LazyRing` from any ring.

        EXAMPLES::

            sage: from ajpastor.lazy.lazy.lazy_ring import *
            sage: R = LazyRing(QQ['x'])
            sage: F, S = R.construction()
            sage: F(S) is R
            True
            sage: F
            LazyRing(*)
    '''
    def __init__(self):
        self.rank = 12
        super().__init__(_CommutativeRings,_CommutativeRings)
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        return x
        
    def _apply_functor(self, x):
        if(isinstance(x, LazyRing)):
            return x
        return LazyRing(x)
        
    def _repr_(self):
        return "LazyRing(*)" %(str(self.__variables))
        
    def __eq__(self, other):
        return other.__class__ == self.__class__

    def merge(self, other):
        scls = self.__class__; ocls = other.__class__
        if(issubclass(scls, ocls) and not (issubclass(ocls, scls))):
            return other
        elif(issubclass(ocls, scls)):
            return self
        return None

    def variables(self):
        return self.__variables

class LazyRing_Base (Morphism):
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)
        
    def _call_(self, p):
        return self.codomain()(p.real)