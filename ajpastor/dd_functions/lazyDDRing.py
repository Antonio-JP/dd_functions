r"""
Python file for lazy implementation of a DDRing

This package provides the implementation of a DDRing which elements perform lazily all the possible operations.


EXAMPLES::

    sage: from ajpastor.dd_functions import *
    sage: DFinite
    DD-Ring over (Univariate Polynomial Ring in x over Rational Field)

TODO::
    * Make the EXAMPLES section in this documentation
    * Document the package
    * Review the package functionality

AUTHORS:

    - Antonio Jimenez-Pastor (2016-01-29): initial version

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
from sage.all import (IntegralDomain, IntegralDomainElement, prod, lcm, UniqueRepresentation,
                        ideal, Integer, DiGraph, QQ, gcd, Matrix, PolynomialRing, kronecker_delta,
                        vector, InfinitePolynomialRing, cached_method)

from sage.categories.map import Map #pylint: disable=no-name-in-module
from sage.categories.integral_domains import IntegralDomains
from sage.categories.fields import Fields
from sage.categories.pushout import ConstructionFunctor

from ajpastor.dd_functions.ddFunction import DFinite, is_DDFunction

from ajpastor.lazy.conversion import ConversionSystem

from ajpastor.misc.ring_w_sequence import Ring_w_Sequence
from ajpastor.misc.matrix import vector_derivative


_Fields = Fields.__classcall__(Fields)
_IntegralDomains = IntegralDomains.__classcall__(IntegralDomains)

####################################################################################################
####################################################################################################
### ELEMENT CLASS
####################################################################################################
####################################################################################################
class _LazyDDFunction(IntegralDomainElement):
    def __init__(self, parent, el):
        if(not (isinstance(parent, LazyDDRing))):
            raise TypeError("The parent for a _LazyDDFunction is not a LazyDDRing")

        self.__raw = None
        self.__poly = None

        IntegralDomainElement.__init__(self, parent)

        try:
            self.__poly = parent.poly_ring()(el)
        except:
            try:
                self.__poly = parent.poly_field()(el)
            except:
                try:
                    self.__poly = self.parent().to_poly(el)
                except:
                    self.__raw = parent.base()(el)
                    self.__poly = self.parent().to_poly(self.__raw)

        self.simplify() # We try to simplify the element from the beginning

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
        if(self.__poly != 0):
            # First we remove common factors in numerator and denominator
            n_pol = self.__poly.parent()(prod(self.__poly.factor()))
            # We then call the simplify method from parent
            self.__poly = self.parent().simplify(n_pol)
        return self

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

    def derivative(self, times = 1):
        '''
        Method that computes the derivative of an element in the laziest way possible.

        This method compute the derivative of each of the variables in 'self.poly()' and then build
        a new polynomial using this expressions.

        This method rely on the parent method 'get_derivative()' which saves the derivatives of the
        variables as a dictionary
        '''
        return self.parent().derivative(self, times)

    ################################################################################################
    ### Arithmetics methods
    ################################################################################################
    def _add_(self, other):
        try:
            return _LazyDDFunction(self.parent(), self.poly()+self.parent()(other).poly())
        except:
            return NotImplemented

    def _sub_(self,other):
        return self.__add__(-other)

    def _neg_(self):
        try:
            return _LazyDDFunction(self.parent(), self.poly()._neg_())
        except NotImplementedError:
            return NotImplemented

    def _mul_(self,other):
        try:
            return _LazyDDFunction(self.parent(), self.poly()*self.parent()(other).poly())
        except:
            return NotImplemented

    def _div_(self,other):
        try:
            return _LazyDDFunction(self.parent(), self.poly()/self.parent()(other).poly())
        except:
            return NotImplemented

    def _pow_(self,i):
        try:
            return _LazyDDFunction(self.parent(), self.poly()**i)
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
        if(len(input) > 1):
            return self.gcd(input)

        return _LazyDDFunction(self.parent(), gcd([self.poly()]+[self.parent()(el).poly() for el in input]))

    def lcm(self,*input):
        '''
        Method that a common multiple of 'self' and the input
        '''
        if(len(input) > 1 ):
            return self.gcd(input)

        return _LazyDDFunction(self.parent(), lcm([self.poly()]+[self.parent()(el).poly() for el in input]))

    def divides(self, other):
        '''
        Method that returns True if 'other = a*self'.

        REMARK: If this methods return False does not mean we can not divide other by self in the level of 'base'.
        '''
        return self.poly().divides(self.parent()(other).poly())

    @cached_method
    def is_zero(self):
        result = (self.poly() == 0 )
        map_to_values = {repr(var) : self.parent().to_real(var)(0) for var in self.poly().variables()}
        if((not result) and (self.poly()(**map_to_values) == 0)):
            if(not (self.__raw is None)):
                result = (self.raw() == 0)
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

        if(result):
            self.__poly = self.parent().poly_ring().zero()

        return result

    @cached_method
    def is_one(self):
        # Computing self-1 and checking if it is zero
        result = (self-1).is_zero()

        # Doing a great simplification in __poly
        if(result):
            self.__poly = self.parent().poly_ring().one()
        return result

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
class LazyDDRing (UniqueRepresentation, ConversionSystem, IntegralDomain):

    Element = _LazyDDFunction

    def __init__(self, base, constants=QQ, var_name="z", category=None):
        '''
            Implementation of a Covnersion System using InfinitePolynomialRing as a basic structure.

            Elements of 'base' will be represented in this ring using elements of
            'InfinitePolynomialRing(constants, names=[var_name])' and linear relations of the type
            'f = cg+d' where 'f in base', 'g in self.gens()' and 'c,d in constants'.

            This class captures all the functionality to work as a ConversionSystem and all the
            data structures required for ompting lazily with those objects.
        '''
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

        self.__poly_ring = InfinitePolynomialRing(constants, names=[var_name])
        self.__poly_field = self.__poly_ring.fraction_field()
        self.__gen = self.__poly_ring.gens()[0]
        self.__used = 0

        ## Initializing the map of variables
        self.__map_of_vars = {} # Map where each variable is associated with a 'base' object
        self.__map_to_vars = {} # Map where each variable is associated with a 'base' object
        self.__r_graph = DiGraph() # Graph of relations between the already casted elements
        self.__trans = dict() # Dictionary with the transformation to get into a node in 'r_graph'

        self.__gens = []

        self.__map_of_derivatives = {} # Map for each variable to its derivative (as a polynomial)

        ## Casting and Coercion system
        self.base().register_conversion(LDRSimpleMorphism(self, self.base()))

        ## Adding the 'x' as a basic variable in the ring
        self(DFinite.element([0,0,1],[0,1],name="x"))

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
        ## Breath-search for a linear relation
        roots = [el for el in self.__r_graph if self.__r_graph.in_degree(el) == 0] # Getting roots
        from collections import deque
        to_search = deque(roots) # Initializing the queue
        while(len(to_search) > 0):
            # Updating the queue
            current = to_search.popleft()
            for edge in self.__r_graph.outgoing_edges(current):
                to_search.append(edge[1])

            # Visiting the current node
            relation = self.__find_relation(element, current, self.__trans[current][1].nrows())
            if(not (relation is None)):
                ## If it is not just the function, create a new node for future relations
                if(relation[0] != 0):
                    self.__add_function(element)
                    self.__r_graph.add_edge((current, element, relation))

                ## Creating the vector in the current level
                v = [0 for i in range(self.__trans[current][1].nrows())]
                v[relation[0]] = relation[1][0]
                v = vector(self.poly_field(), v)

                ## Going to a root with the vector
                v,const,dest = self.__pullup_vector(v, relation[1][1], current)

                ## Returning the appropriate polynomial using the final vector
                return self.__vector_to_poly(v, dest)+const

        ## At this point, no direct relation was found. We look for relation between element and the roots
        for root in roots:
            relation = self.__find_relation(root, element)
            if(not (relation is None)):
                # Adding the element to the graph
                self.__add_function(element, gen=True)
                self.__r_graph.add_edge((element, root, relation))

                # Adding the relation for future simplifications
                rel = self.__gen[root] - relation[1][1]*self.__gen[self.__map_to_vars[element]+relation[0]] - relation[1][1]
                self.add_relations(rel)

                # Removing root as a generator
                index = self.__gens.index(self.__gen[self.__map_to_vars[root]])
                for _ in range(self.__trans[root][1].nrows()):
                    self.__gens.pop(index)

                return self.__gen[self.__map_to_vars[element]]

        ## Otherwise, we add the element to the variables and return it
        self.__add_function(element, gen=True)
        return self.__gen[self.__map_to_vars[element]]

    def _relations(self):
        '''
            Returns a Groebner Basis of the relations ideals known in this conversion system.
        '''
        if(self._ConversionSystem__relations is None):
            self._ConversionSystem__relations = []
            self._ConversionSystem__rel_ideal = ideal([Integer(0)])

        return self._ConversionSystem__relations

    def _groebner_basis(self):
        if(len(self._ConversionSystem__relations) >= 1):
            gens_in_relations = list(set(sum([[str(v) for v in el.variables()] for el in self._ConversionSystem__relations], [])))
            Poly = PolynomialRing(self.poly_ring().base_ring(), gens_in_relations, order='deglex')
            rels = [Poly(el) for el in self._ConversionSystem__relations]
            self._ConversionSystem__rel_ideal = ideal(Poly, rels)
            return self._ConversionSystem__rel_ideal.groebner_basis()
        return [self.poly_ring().base_ring().zero()]

    def _simplify(self, poly):
        gens = list(set([str(g) for g in self._ConversionSystem__rel_ideal.parent().ring().gens() if g != 1] + [str(g) for g in poly.variables()]))
        Poly = PolynomialRing(self.poly_ring().base_ring(), gens)
        try:
            poly = Poly(poly)
        except TypeError:
            return poly
        try:
            return self.poly_ring()(poly.reduce([Poly(el) for el in self._ConversionSystem__relations]))
        except AttributeError:
            return self.poly_ring()(poly)

    ################################################################################################
    ### Other Methods for LazyRing
    ################################################################################################
    def sequence(self, el, n, list=False):
        if(not isinstance(el, _LazyDDFunction)):
            return el.parent().sequence(el,n,list=list)

        return self.base().sequence(el.raw(),n, list=list)

    def clean_ring(self):
        ## Cleaning the relations
        self.clean_relations()

        ## Cleaning all the variables for the laziness
        self.__used = 0
        self.__map_of_vars = {}
        self.__map_to_vars = {}
        self.__r_graph = DiGraph()
        self.__trans = dict()
        self.__gens = []
        self.__map_of_derivatives = {}

    def derivative(self, el, times=1):
        '''
            Method that computes the derivative of an element in the LazyDDRing. It performs a casting to 'self' before starting the algorithm.
        '''
        el = self(el)

        if(times == 0):
            return el
        elif(times > 1):
            return self.derivative(self.derivative(el, times-1))

        ## COmputing the derivative of the polynomial associated
        poly = el.poly()
        ## Rational function case
        try:
            if(poly.denominator() != 1):
                n = self(poly.numerator()); dn = self.derivative(n)
                d = self(poly.denominator()); dd = self.derivative(d)

                return (dn*d - dd*n)/d**2
        except AttributeError:
            pass

        ## Splitting the derivative into the monomials
        if(poly == 0):
            return self.zero()
        coeffs = poly.coefficients()
        monomials = poly.monomials()

        ## Base case (monomial case)
        if(len(monomials) == 1):
            gens = poly.variables()
            degrees = [poly.degree(g) for g in gens]

            res = sum(prod(gens[j]**(degrees[j]-kronecker_delta(i,j)) for j in range(len(gens)))*degrees[i]*self.get_derivative(gens[i]) for i in range(len(gens)))

            return self(coeffs[0]*res)
        else: ## Generic case (polynomial)
            return self(sum(coeffs[i]*self.derivative(monomials[i]) for i in range(len(coeffs))))

    def get_derivative(self, el):
        return self(self.__map_of_derivatives[el]).poly()

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

    def gens(self):
        return self.__gens

    def ngens(self):
        return len(self.__gens)

    ################################################################################################
    ### Other Ring methods
    ################################################################################################
    def is_field(self):
        return self.base().is_field()
        #return True

    def is_finite(self):
        return self.base().is_finite()

    def is_integrally_closed(self):
        return self.base().is_integrally_closed()

    def is_noetherian(self):
        return self.base().is_noetherian()

    def _xgcd_univariate_polynomial(self, a, b):
        '''
        Return an extended gcd of ``a`` and ``b``.

            INPUT:

            - ``a``, ``b`` -- two univariate polynomials defined over ``self``

            OUTPUT:

            A tuple ``(t, r, s)`` of polynomials such that ``t`` is the
            greatest common divisor (monic or zero) of ``a`` and ``b``,
            and ``r``, ``s`` satisfy ``t = r*a + s*b``.
        '''
        SY = a.parent()
        ## Casting the polynomials a and b to polynomials with rational functions coefficients
        # Getting the variables
        coeffs = [self.to_poly(el) for el in a.coefficients() + b.coefficients()]
        gens = list(set(sum([[str(g) for g in poly.variables()] for poly in coeffs], [])))
        # Building the rational functions
        F = PolynomialRing(self.base_ring(), gens).fraction_field()
        # Building the polynomial ring
        y = a.parent().gens_dict().items()[0][0]
        R = PolynomialRing(F, y)
        a = R(str(a)); b = R(str(b))

        ## Computing the xgcd in that extended field using the standard algorithm
        t,r,s = F._xgcd_univariate_polynomial(a,b)

        ## Returning the result casted to Lazy Elements
        return (SY(t.coefficients(False)), SY(r.coefficients(False)), SY(s.coefficients(False)))

    ################################################################################################
    ### Coercion methods
    ################################################################################################
    def _coerce_map_from_(self, S):
        coer = None
        if(isinstance(S, LazyDDRing)):
            coer = self.base()._coerce_map_from_(S.base())
        elif(S == self.poly_ring() or S == self.poly_field()):
            coer = True
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
            raise TypeError("Unexpected arguments in _element_constructor_")
        if(len(args) < 1 ):
            raise ValueError("Impossible to build an element without arguments")

        i = 0 
        if(len(args) >= 2 ):
            if(not (args[0 ] is self)):
                raise ValueError("RIOKO: What the .... are you sending to this method?")
            i = 1 
        X = args[i]

        try:
            if(not isinstance(X, _LazyDDFunction)):
                ## If the element is not a LazyElement, then we try to create a new element with it
                return _LazyDDFunction(self, X)
            elif (X.parent() is self):
                return X
            else:
                ## Otherwise, X.parent() may have different variables
                other = X.parent()
                pol = X.poly()

                ## For each variable in X.poly(), we get the new polynomial
                translate = {}
                for var in X.variables():
                    translate[var] = self.to_poly(other.map_of_vars()[str(var)])

                ## We now plugin the expressions
                return _LazyDDFunction(self, pol(**translate))
        except TypeError:
            raise TypeError("This element can not be casted to %s" %repr(self))

    def construction(self):
        return (LazyDDRingFunctor(), self.base())

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
        return "Lazy DD-Ring over (%s)" %(repr(self.base()))

    def __str__(self):
        final = "%s with %d variables\n{\n" %(repr(self),len(self.__gens))
        for g in self.__gens:
            final += "\t%s : %s,\n" %(g, repr(self.__map_of_vars[str(g)]))
        final += "}"
        return final

    ################################################################################################
    ### Private methods
    ################################################################################################
    def __pullup_vector(self, vector, constant, current):
        if(self.__r_graph.in_degree(current) == 0):
            return (vector, constant, current)

        ## Getting all data for this case
        cR = self.__poly_field
        edge = self.__r_graph.incoming_edges(current)[0]
        C = self.__trans[edge[0]][1]
        trans_const = self.__trans[edge[0]][0]
        relation = edge[2]

        ## Computing the derivatives of current in his father vector space
        ivectors = [vector(cR, [0 for i in range(relation[0])] + [1] + [0 for i in range(relation[0]+1,self.__trans[current][1].nrows())])]
        extra_cons = [relation[1][1]]

        for i in range(len(vector)):
            extra_cons += [ivectors[-1][-1]*trans_const]
            ivectors += [vector_derivative(C, ivectors[-1], self.derivative)]

        res_vector = sum([vector(cR,[vector[i]*ivectors[i][j] for j in range(len(ivectors[i]))]) for i in range(len(vector))])
        res_constant = sum([vector[i]*extra_cons[i] for i in range(len(vector))], constant)

        return self.__pollup_vector(res_vector, res_constant, edge[0])

    def __vector_to_poly(self, vector, current):
        gen_index = self.__map_to_vars[current]
        return sum(vector[i]*self.__gen[gen_index+i] for i in range(len(vector)) if vector[i] != 0)

    def __add_function(self, f, gen=False):
        ## We look for relations with the derivatives of itself
        derivatives = [f.derivative(times=i) for i in range(f.order())]

        order = f.order()
        relation = None
        for i in range(f.order()-1,0,-1):
            n_relation = self.__find_relation(derivatives[i], derivatives[:i])
            if(not (n_relation is None)):
                order = i
                relation = n_relation
            else:
                break

        ## Create the tranformation into f

        # Companion matrix
        companion = f.equation.companion()
        companion = Matrix(self, [[self(companion[i][j]) for j in range(companion.ncols())] for i in range(companion.nrows())])
        if(order < f.order()): # Relation found
            C = []
            for i in range(order):
                new_row = [companion[i][j] for j in range(order)]
                if(i == relation[0]):
                    new_row[-1] = relation[1][0]
                C += [new_row]
            C = Matrix(self,C)
            self.__trans[f] = (relation[1][1],C)
        else:
            self.__trans[f] = (self.poly_ring().zero(),Matrix(self, companion))

        ## Adding f as a vertex (edges must be added outside this function)
        self.__r_graph.add_vertex(f)

        ## If f will become a generator, add it to the used variables
        if(gen):
            current = f
            before = self.__used
            for i in range(order):
                print("** Adding a new variable (%d)" %self.__used)
                self.__gens += [self.__gen[self.__used]]
                self.__map_of_vars[str(self.__gens[-1])] = current
                self.__map_to_vars[current] = self.__used
                self.__map_of_derivatives[self.__gen[self.__used]] = self.__gen[self.__used+1]
                self.__used += 1
                current = current.derivative()

            trans = self.__trans[f]
            self.__map_of_derivatives[self.__gen[before+order-1]] = sum([self.__gen[before+i]*trans[1][i][-1] for i in range(order)], trans[0])

        return

    def __find_relation(self, g,f,d=None):
        '''
            Method that get the relation between g and a f. If possible, it computes
            the derivatives up to some order of f and check relations with them.

            It returns a tuple (k,res) where
                - k: the first index which we found a relation
                - res: the relation (see __find_linear_relation to see how such
                relation is expressed).

            Then the following statement is always True
                g == f[k]*res[0] + res[1]

            INPUT:
                - g: Function we want to see the relation
                - f: Function or list of functions where we look for relations
                - d: Optional parameter to limit
        '''
        if(is_DDFunction(f)): # If f is a function, computing the derivatives
            f = [f.derivative(times=i) for i in range(f.order())]
        if(not(d is None)):
            f = f[:d] # Limiting the list with the optional parameter d

        for k in range(len(f)):
            res = self.__find_linear_relation(g,f[k])
            if(not (res is None)):
                return (k,res)

        return None

    def __find_linear_relation(self, f,g):
        '''
            This method receives two DDFunctions and return two constants (c,d)
            such that f = cg+d. None is return if those constants do not exist.
        '''
        if(not (is_DDFunction(f) and is_DDFunction(g))):
            raise TypeError("find_linear_relation: The functions are not DDFunctions")

        ## Simplest case: some of the functions are constants is a constant
        if(f.is_constant()):
            return (f.parent().zero(), f(0))
        elif(g.is_constant()):
            return None

        try:
            of = 1; og = 1
            while(f.sequence(of) == 0): of += 1
            while(g.sequence(og) == 0): og += 1

            if(of == og):
                c = f.sequence(of)/g.sequence(og)
                d = f(0) - c*g(0)

                if(f == c*g + d):
                    return (c,d)
        except Exception:
            pass

        return None

####################################################################################################
####################################################################################################
### Construction Functor for LazyRing
####################################################################################################
####################################################################################################
class LazyDDRingFunctor (ConstructionFunctor):
    def __init__(self):
        self.rank = 20 
        super(LazyDDRingFunctor, self).__init__(_IntegralDomains,_IntegralDomains)

    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        if(isinstance(x, LazyDDRing)):
            return x.base()
        return x

    def _apply_functor(self, x):
        return LazyDDRing(x)

####################################################################################################
####################################################################################################
### General Morphism for return to basic rings
####################################################################################################
####################################################################################################
class LDRSimpleMorphism (Map):
    def __init__(self, domain, codomain):
        super(LDRSimpleMorphism, self).__init__(domain, codomain)

    def _call_(self, p):
        return self.codomain()(p.raw())

