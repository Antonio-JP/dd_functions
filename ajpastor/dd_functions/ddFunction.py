r"""
Python file for DD-functions and DD-rings

This packages provides all the functionality for computing with Differentially Definable Functions (DD-functions) and 
the rings they form (DD-rings). It allows to create further DD-rings, compare them and add constant parameters to the
computations. The user can also compute several closure properties on te DD-functions such as addition, product, division
composition, etc.

EXAMPLES::

    sage: from ajpastor.dd_functions import DFinite
    sage: DFinite
    DD-Ring over (Univariate Polynomial Ring in x over Rational Field)
    sage: f = DFinite.element([-1,1],[1])
    sage: f.init(10, True) == [1]*10
    True

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

# Python imports
import warnings
import logging
from functools import reduce

#SAGE imports 
from sage.all import (IntegralDomain, IntegralDomainElement, IntegralDomains, Fields, derivative,
                        QQ, ZZ, SR, NumberField, PolynomialRing, factorial, latex, randint, var, Expression,
                        cached_method, Matrix, vector, gcd, binomial, falling_factorial, bell_polynomial, 
                        sage_eval, log, BackslashOperator, parent, identity_matrix, diff, kronecker_delta,
                        LaurentPolynomialRing, LaurentSeriesRing, block_matrix, infinity)
from sage.all_cmdline import x
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing
from sage.categories.all import Morphism
from sage.categories.pushout import pushout
from sage.categories.pushout import ConstructionFunctor

#ajpastor imports
from ajpastor.dd_functions.exceptions import DDFunctionError, ZeroValueRequired, InitValueError, NoValueError

from ajpastor.misc.dynamic_string import DynamicString, m_dreplace
from ajpastor.misc.serializable import SerializableObject
from ajpastor.misc.cached_property import derived_property
from ajpastor.misc.ring_w_sequence import Ring_w_Sequence
from ajpastor.misc.ring_w_sequence import Wrap_w_Sequence_Ring
from ajpastor.misc.ring_w_sequence import sequence
from ajpastor.misc.sets import FiniteEnumeratedSet, EmptySet
from ajpastor.misc.verbose import printProgressBar

from ajpastor.operator.operator import Operator
from ajpastor.operator.directStepOperator import DirectStepOperator
from ajpastor.operator.fullLazyOperator import FullLazyOperator

# Private variables for module
_IntegralDomains = IntegralDomains.__classcall__(IntegralDomains)
_Fields = Fields.__classcall__(Fields)
logger = logging.getLogger(__name__)

#####################################################
### Definition of the particular warnings we are interested to raise
#####################################################
class DDFunctionWarning(RuntimeWarning):
    pass

class MergingRingWarning(DDFunctionWarning):
    pass
    
class TooDeepWarning(DDFunctionWarning):
    pass
    
class NoOreAlgebraWarning(DDFunctionWarning):
    pass

warnings.simplefilter('always', DDFunctionWarning)
    

## Auxiliary derivative function
def _aux_derivation(p):
    try:
        R = p.parent()
        return derivative(p,R(x))
    except Exception:
        return 0
        
#####################################################
### Class for DD-Rings
#####################################################
def is_DDRing(ring):
    r'''
        Method that checks if an object is a :class:`DDRing`. 

        This method provides a general function to check the class of an object without knowing 
        exactly the name of the basic class of the module. This is basically an alias for the command 
        ``instance(ring, DDRing)``.

        INPUT:
            * ``ring``: object to be checked.

        OUTPUT: 
        
        ``True`` or ``False`` depending if ``ring`` is a :class:`DDRing` or not.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: is_DDRing(DFinite)
            True
            sage: is_DDRing(DDRing(QQ))
            True
            sage: is_DDRing(QQ)
            False

        Also :class:`ParametrizedDDRing` return ``True`` with this method::

            sage: is_DDRing(ParametrizedDDRing(DFinite, ['a']))
            True

        SEE ALSO:
            * :class:`DDRing`
    '''
    return isinstance(ring, DDRing)

class DDRing (Ring_w_Sequence, IntegralDomain, SerializableObject):
    r'''
        Class for Differentially Definable Rings (or DDRing).

        This class represents the Ring of Differentially Definable Functions with coefficients over a base ring. This rings contains all the functions
        (formal power series) that satisfy a linear differential equation with coefficients in a base ring. For further theoretical information
        about this class of functions, check `this paper <https://www.sciencedirect.com/science/article/abs/pii/S0747717118300890>`_.

        INPUT:
            * ``base``: an integral domain. Will provide the coefficients for the differential equations.
            * ``depth``: positive integer. Points how many iterations of this construction we want.
            * ``base_field``: a field. The elements of ``self`` will be formal power series over this field.
            * ``invertibility``: method. This method checks if an element of ``base`` is invertible or not.
            * ``derivation``: method. This method computes the derivative of elements in ``base``.
            * ``default_operator``: class. Class inheriting from :class:`~ajpastor.operator.Operator` for the differential equations.

        More formally, ``(base,derivation)`` is a differential integral domain and ``(self, self.derivative)`` a differential extension.

        Note that these objects are unique, so calling the constructor with the same arguments retrieve the same object.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: DDRing(QQ)
            DD-Ring over (Rational Field)
            sage: DDRing(QQ) is DDRing(QQ)
            True
            
        We can iterate the process using an iterative call of the constructor or the ``depth`` argument::

            sage: DDRing(QQ, depth=2)
            DD-Ring over (DD-Ring over (Rational Field))
            sage: DDRing(QQ, depth=2) is DDRing(DDRing(QQ))
            True
    '''
    
    Element = None
    
    _Default_Depth = 1 # Default value for the depth argument in __init__
    _Default_Base_Field = None # Default value for the base_field argument in __init__
    _Default_Invertibility = None # Default value for the invertibility argument in __init__
    _Default_Derivation = None # Default value for the base_derivation argument in __init__
    _Default_Operator = None # Default value for the default_operator argument in __init__
    _Default_Parameters = [
        ("base", None),
        ("depth", _Default_Depth),
        ("base_field", _Default_Base_Field),
        ("invertibility", _Default_Invertibility),
        ("derivation", _Default_Derivation),
        ("default_operator", _Default_Operator)]
    
    _CACHED_DD_RINGS = {} # Variable for cached DDRings (Unique Representation idea)
    
    _Default_variable = 'x' # Static name for the default variable
    
    #################################################
    ### Static methods
    #################################################
    @staticmethod
    def __algebraic_equivalent__(R,S):
        r'''
            Method that checks if two :class:`~sage.rings.number_field.number_field.NumberField` extensions are equivalent in SAGE. 
            
            We say that `R\sim S` if they have the same polynomials defining their elements
            and they have exactly the same name.
            
            If `R` or `S` are not an algebraic extension then the method returns simply ``R==S``.
        '''
        from sage.categories.pushout import AlgebraicExtensionFunctor as algebraic
        const_S = S.construction()
        const_R = R.construction()
        
        ## Checking both elements are constructed as AlgebraicExtension
        if(not(isinstance(const_S[0],algebraic) and isinstance(const_R[0], algebraic))):
            ## If not, returning the equality operator
            return R==S
        
        ## If the base field is different, the result is False
        if(const_S[1] != const_R[1]):
            return False
        
        # Getting the defining polynomials of the extensions
        polys_R = const_R[0].polys
        polys_S = const_S[0].polys
        # Getting the names defining the new variables on the extensions
        names_R = const_R[0].names
        names_S = const_S[0].names
        
        # We know comapre the four lists. We do not care about the order, so 
        # QQ(i)(sqrt(2)) == QQ(sqrt(2))(i). We check that the corresponding 
        # polynomials defined the same name.
        if(len(polys_R) != len(polys_S)):
            return False
        
        for i in range(len(polys_R)):
            try:
                index = polys_S.index(polys_R[i])
                if(names_R[i] != names_S[index]):
                    return False
            except ValueError:
                return False

        # We check all the generators of R are in the generators of S 
        # and they have the same length. Hence they are equal
        return True
        
    @staticmethod
    def __get_gens__(parent):
        r'''
            Method to get the generators of a parent structure.

            Static method that explore the list of generators of a Parent object until the method gens returns nothing or `1`.

            This method is particularly focused on Algebraic extensions, Polynomial extensions and Fraction Fields.
        '''
        from sage.categories.pushout import AlgebraicExtensionFunctor as algebraic
        from sage.categories.pushout import PolynomialFunctor as polynomial
        from sage.categories.pushout import MultiPolynomialFunctor as multi_polynomial
        from sage.categories.pushout import FractionField as fraction
        
        # We start from the current parent and go step by step in its construction getting
        # all the generators
        current = parent

        # Checking the parent object is a constructed object
        try:
            const = parent.construction()
        except AttributeError:
            raise RuntimeError("Impossible to get construction of %s" %parent)

        # Getting the generators of the current element
        gens = [el for el in parent.gens()]
        
        # The result will distinguish between algebraic extensions, polynomial extensions and other type of generators.
        res = {'algebraic' : [], 'polynomial': [], 'other' : []}
        
        # We start the main loop
        while((not(const is None)) and (not (1  in gens))):
            # If the last construction is DDRing or polynomial, we add the generators as polynomial generators
            if(isinstance(current, DDRing) or isinstance(const[0], polynomial) or isinstance(const[0], multi_polynomial)):
                res['polynomial'] += list(current.gens())
            # If the construction is an algebraic extension, we add the generators as algebraic generators
            elif(isinstance(const[0], algebraic)):
                for i in range(len(const[0].polys)):
                    name = const[0].names[i]
                    found = None
                    for gen in current.gens():
                        if(current(name) == gen):
                            found = gen
                            break
                    if(found is None):
                        raise TypeError("Impossible error: no generator for a name!!")
                    # Algebraic generators are store with defining polynomial + algebraic functor
                    res['algebraic'] += [(found, const[0].polys[i], const[1])]
            # Otherwise we get all the generators skipping the FractionField construction
            elif(not isinstance(const[0], fraction)):
                res['other'] += list(current.gens())
                
            current = const[1]
            const = current.construction()
            
        # At this point we have all the generators (including maybe a 1) splitted in the type of extension

        # Cleaning "1" from the result
        # Put everything as tuples
        try:
            if(1  in res['algebraic']):
                raise TypeError("1 is a generator of an algebraic extension")
            res['algebraic'] = tuple(res['algebraic'])
            while(1  in res['polynomial']):
                res['polynomial'].remove(1 )
            res['polynomial'] = tuple(set(res['polynomial']))
            while(1  in res['other']):
                res['other'].remove(1 )
            res['other'] = tuple(set(res['other']))
        except TypeError:
            raise RuntimeError("Non hashable object found")
        

        # Returning the basic parent structure and the list and types of generators    
        return res, current
        
    #################################################
    ### Builder
    #################################################
    @staticmethod
    def __classcall__(cls, *args, **kwds):
        r'''
            Particular builder for the class :class:`DDRing`. 

            This method do a special checking of uniqueness for two :class:`DDRing`. It maps all the arguments provided by the user
            and transform them into a standard notation that will be hashable and will allow the system to recognize two
            exact differentially definable rings.

            This implemention mimics the behavior of the class :class:`UniqueRepresentation`.
        '''
        final_args = []
                
        ## We first compile the parameters the user send
        current = 0
        if(len(args) != 1  or args[0] != None):
            for i in range(len(args)):
                final_args += [[DDRing._Default_Parameters[i][0], args[i]]]
            current = len(args)
        
        for i in range(max(1,current), len(DDRing._Default_Parameters)):
            final_args += [[DDRing._Default_Parameters[i][0], kwds.get(DDRing._Default_Parameters[i][0],DDRing._Default_Parameters[i][1])]]
            
        ## Managing the depth over DDRings
        if(isinstance(final_args[0][1], DDRing)):
            final_args[1][1] = final_args[1][1]+final_args[0][1].depth()
            final_args[0][1] = final_args[0][1]._DDRing__original
            
        ## Casting to tuple (so is hashable)
        to_hash = tuple(tuple(el) for el in final_args[:2])
        final_args = tuple(tuple(el) for el in final_args)
        
        if(final_args[1][1] == 0 ):
            return final_args[0][1]
            
        if(not cls in DDRing._CACHED_DD_RINGS):
            DDRing._CACHED_DD_RINGS[cls] = {}
        if(not (to_hash in DDRing._CACHED_DD_RINGS[cls])):
            tmp = IntegralDomain.__new__(cls)
            DDRing.__init__(tmp,**dict(final_args))
            DDRing._CACHED_DD_RINGS[cls][to_hash] = tmp
       
        return DDRing._CACHED_DD_RINGS[cls][to_hash]
    
    def __init__(self, base, depth = _Default_Depth, base_field = _Default_Base_Field, invertibility = _Default_Invertibility, derivation = _Default_Derivation, default_operator = _Default_Operator):
        ## Other attributes initialization
        self.__variables = None
        SerializableObject.__init__(self, base, depth, base_field, invertibility, derivation, default_operator)

        if(depth > 1 ):
            DDRing.__init__(self,DDRing(base, depth-1 , base_field, invertibility, derivation, default_operator), 1 , base_field, invertibility, derivation, default_operator)
        else:
            ### We call the builders of the superclasses
            Ring_w_Sequence.__init__(self, base, method = lambda p,n : self(p).sequence(n))
            IntegralDomain.__init__(self, base, category=_IntegralDomains)
            
            ### We assign the operator class
            if(default_operator is None):
                ## In this case we add an default Operator
                if(isinstance(base, DDRing)):
                    self.__default_operator = FullLazyOperator
                else:
                    self.__default_operator = DirectStepOperator
            elif(issubclass(default_operator, Operator)):
                self.__default_operator = default_operator
            else:
                raise TypeError("Invalid type for Operators in this ring. Must inherit from class Operator.")
            
            ### In order to get Initial Values, we keep the original field base 
            # If the base ring is already a DDRing, we take the correspond ring from base
            if isinstance(base, DDRing):
                self.__base_field = base.coeff_field
                self.__depth = base.__depth + 1
                self.__original = base.__original
            # Otherwise, we set this simplest ring as our current coefficient ring
            else:
                if(base_field is None):
                    from sage.categories.pushout import PolynomialFunctor, FractionField
                    current = base
                    const = base.construction()
                    while((not (const is None)) and (isinstance(const[0], PolynomialFunctor) or isinstance(const[0],FractionField))):
                        current = const[1]
                        const = current.construction()
                        
                    if(not current.is_field()):
                        self.__base_field = current.fraction_field()
                    else:
                        self.__base_field = current
                        
                        
                else:
                    self.__base_field = base_field
                self.__depth = 1
                self.__original = base
            
            ### Saving the invertibility criteria
            if(invertibility is None):
                # Default: invertibility as power series
                try:
                    self_var = self.variables(True)[0]
                    self.__base_invertibility = lambda p : p(**{self_var : 0 }) != 0 
                except IndexError:
                    self.__base_invertibility = lambda p : self.base()(p) != 0
            else:
                self.__base_invertibility = invertibility
            
            ### Saving the base derivation
            if(derivation is None):
                try:
                    self_var = self.variables(True)[0]
                    def __standard_derivation(p):
                        try:
                            return p.derivative(self.base()(self_var))
                        except AttributeError:
                            return 0
                    self.__base_derivation = __standard_derivation
                except IndexError:
                    self.__base_derivation = lambda p : 0
            else:
                self.__base_derivation = derivation
            
            ### Setting new conversions with simpler rings
            current = self.base()
            morph = DDSimpleMorphism(self, current)
            current.register_conversion(morph)
            while(not(current.base() == current)):
                current = current.base()
                morph = DDSimpleMorphism(self, current)
                current.register_conversion(morph)

    #################################################
    ### Coercion methods
    #################################################
    def _coerce_map_from_(self, S):
        r'''
            Method to get the coerce map from the Sage structure `S` (if possible).
            
            To allow the algebraic numbers, we use the method :func:`DDRing.__get_gens__` to compare how the ring `S` and
            the ring ``self`` where built. If at some point we can not use the behavior of the generators, we 
            will rely on the usual function :func:`DDRing._coerce_map_from_` with ``self.base()``.
        '''
        ## Checking the easy cases
        coer = None
        if(isinstance(S, DDRing)):
            coer = self.base()._coerce_map_from_(S.base())
        elif(S == self.base()):
            coer = True
        elif(S is SR):
            coer = True
        else:
            coer = self.base()._coerce_map_from_(S)
            
        if(not(coer is False) and not(coer is None)):
            return True
        #return None
        ## If not coercion is found, we check deeper using generators
        gens_self = DDRing.__get_gens__(self)[0]
        try:
            gens_S = DDRing.__get_gens__(S)[0]
        except RuntimeError:
            return None
        
        ## Using the 'other' generators
        if(len(gens_S['other']) > 0 ):
            return self.base()._coerce_map_from_(S)
            
        ## Comparing the algebraic construction
        for i in range(len(gens_S['algebraic'])):
            looking = gens_S['algebraic'][i]
            found = False
            for el in gens_self['algebraic']:
                if(el[1] == looking[1] and str(el[0]) == str(looking[0])):
                    found = True
                    break
            if(not found):
                return self.base()._coerce_map_from_(S)
                
        ## Comparing the parametric space
        if(any(str(el) not in [str(ob) for ob in gens_self['polynomial']] for el in gens_S['polynomial'])):
            return self.base()._coerce_map_from_(S)
            
        ## Comparing the depth of the structure S
        if(isinstance(S, DDRing)):
            return S.depth() <= self.depth()
        
    def _pushout_(self, S):
        r'''
            Method to compute the pushout of ``self`` with a parent class `S`.

            This method returns ``None`` if it is not possible to get the pushout or a :class:`DDRing` with all the properties 
            required to include ``self`` and `S`.
            
            The method goes as follows:

            1 - Compute the simplest field over everything is based (let us call it `F`). This will be `\mathbb{Q}` or an algebraic 
              extension of \mathbb{Q}` (see :class:`~sage.rings.number_field.number_field.NumberField`)
            2 - Compute the list of parameters involved. This will be the constant transcendent elements that will extend the ring 
              `F` as a rational function ring. We denote by `B` that extension.
            3 - Compute the list of variables involved. We usually expect just one variable but allow to have more of them. We will 
              build `R` the polynomial ring over `B` with those variables.
            4 - Compute the depth required for include ``self`` and `S`. Then we build the corresponding :class:`DDRing` of the appropriate 
              depth. If we had parameters, we build the :class:`ParametrizedDDRing`.
                
            INPUT:
                * ``S``: a parent structure of Sage.
                
            OUTPUT:

            A :class:`DDRing` or :class:`ParametrizedDDRing` such that contains all the elements in ``self`` and `S`.
                
            WARNINGS:
                * A warning will pop up if we merge rings with the same parameter names.
                
            ERRORS:
                * :class:`TypeError`q will be raised if a problem with the algebraic extension is found.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: from sage.categories.pushout import pushout
                sage: Qi.<i> = NumberField(QQ['i']('i^2+1'))
                sage: pushout(QQ, DFinite) is DFinite
                True
                sage: pushout(Qi, DFinite)
                DD-Ring over (Univariate Polynomial Ring in x over Number Field in i with defining polynomial x^2 + 1)
                sage: pushout(DFiniteI, ParametrizedDDRing(DDFinite, 'a'))
                DD-Ring over (DD-Ring over (Univariate Polynomial Ring in x over Number Field in I with defining polynomial x^2 + 1)) with parameter (a)
        '''        
        if(S is SR):
            return None
            
        ## We get a list of the generators of self and S with their types
        gens_self, pself = DDRing.__get_gens__(self)
        try:
            gens_S, pS = DDRing.__get_gens__(S)
        except RuntimeError:
            return None
        
        if(len(gens_S['other']) > 0  or len(gens_self['other']) > 0 ):
            raise TypeError("Impossible to compute a pushout: generators not recognized found.\n\t- %s" %(list(gens_S['other']) + list(gens_self['other'])))
        
        ##########################################
        ## Compute the basic field F
        ##########################################
        ## Computing the original field
        F = None
        try:
            F = pushout(pself, pS)
        except:
            pass
        if(F is None):
            return None
            #raise TypeError("Incompatible original structures:\n\t- %s\n\t- %s" %(pself, pS))
        
        if(not F in _IntegralDomains):
            return None
            #raise TypeError("Pushout of the original structures is not an integral domain:\n\t- %s" %F)
        if(not F.is_field()):
            F = F.fraction_field()
            
        ## Extending the field with algebraic extensions
        polys = {str(el[0]):el[1] for el in gens_self['algebraic']}
        for el in gens_S['algebraic']:
            if(polys.get(str(el[0]), el[1]) != el[1]):
                return None
                #raise TypeError("Incompatible names in algebraic extensions:\n\t- %s\n\t- %s" %(el,(el[0],polys[str(el[0])])))
            polys[str(el[0])] = el[1]
            
        sorted_names = sorted(polys)
        sorted_polys = [polys[el] for el in sorted_names]
        
        F = NumberField([PolynomialRing(F,x)(el) for el in sorted_polys], sorted_names)
        
        ##########################################
        ## Compute the list of parameters and variables
        ##########################################
        all_params = set(str(el) for el in (gens_S['polynomial']+gens_self['polynomial']))
        params = all_params - set([str(el) for el in self.variables(True)])
        variables = all_params - params
        
        ##########################################
        ## Compute the required depth
        ##########################################
        depth = self.depth()
        if(isinstance(S, DDRing)):
            depth = max(depth,S.depth())
        
        ##########################################
        ## Building the final DDRing
        ##########################################
        if(len(variables) > 0 ):
            F = PolynomialRing(F,[str(el) for el in variables])
        R = DDRing(F, depth = depth)
        if(len(params) > 0 ):
            R = ParametrizedDDRing(R, params)
            
        return R
        
    def _has_coerce_map_from(self, S):
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))
        
    def _element_constructor_(self, *args, **kwds):
        r'''
            Implementation of ``_element_constructor_``.

            This method describes how to interpret the arguments that a :class:`DDRing` can received to cast one element to a 
            :class:`DDFunction` in ``self``.
        '''
        if(len(args) < 1 ):
            raise ValueError("Impossible to build a lazy element without arguments")
        
        if(args[0] is self):
            X = args[1]
        else:
            X = args[0]
           
        try:
            if(isinstance(X, DDFunction)):
                if(X.parent() is self):
                    return X
                else:
                    return self.element([coeff for coeff in X.equation.coefficients()], X.init(X.equation.get_jp_fo()+1, True, True), name=X._DDFunction__name)
            else:
                try:
                    try:
                        num = self.base()(X)
                        den = self.base().one()
                    except TypeError as e:
                        try:
                            num = self.base()(str(X))
                            den = self.base().one()
                        except:
                            ## Trying the fraction field
                            try:
                                X = self.base().fraction_field()(X)
                                num = self.base()(X.numerator())
                                den = self.base()(X.denominator())
                            except:
                                try:
                                    X = self.base().fraction_field()(str(X))
                                    num = self.base()(X.numerator())
                                    den = self.base()(X.denominator())
                                except:
                                    raise e
                                
                    dnum = self.base_derivation(num)
                    dden = self.base_derivation(den)
                    el = self.element([dden*num - dnum*den, num*den])
                    X = num/den
                    name = str(X)
                    try:
                        name = X._DDFunction__name
                    except:
                        pass
                    return el.change_init_values([sequence(X,i)*factorial(i) for i in range(el.equation.get_jp_fo()+1 )], name=name)
                except AttributeError:
                    try:
                        return self.element([1],[], self.base()(X), name=str(X))
                    except Exception:
                        print("WHAT??")
                        return self(str(X))
        except TypeError as e:
            raise TypeError("Cannot cast an elements to a DD-Function of (%s):\n\tElement: %s (%s)\n\tReason: %s" %(self, X, type(X), e)).with_traceback(e.__traceback__)
            
    def gens(self):
        r'''
            Implementation of the method ``gens``.

            This method returns a list with all the generators of the :class:`DDRing`. This usually means nothing, although some :class:`DDRing` can 
            retrieve some special variables or its parameters as genertors.

            The methods :func:`~DDRing.variables` and :func:`~DDRing.parameters` are more useful in this regard since it separates
            the meaning of each generator.

            OUTPUT:
                List of generators provided by this :class:`DDRing`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.gens()
                ()
                sage: R = ParametrizedDDRing(DFinite, ['a'])
                sage: R.gens()
                (a,)
                sage: ParametrizedDDRing(R, ['b']).gens()
                (b, a)
        '''
        return ()
    
    def ngens(self):
        r'''
            Return the number of generators of ``self``.

            General method for Parent structures that returns the number of generators required to generate ``self``.

            OUTPUT:

            Number of generators obtained by :func:`~DDRing.gens`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.ngens()
                0
                sage: DDFinite.ngens()
                0
                sage: R = ParametrizedDDRing(DFinite, ['a'])
                sage: R.ngens()
                1
                sage: ParametrizedDDRing(R, ['b']).ngens()
                2
        '''
        return len(self.gens())
            
    def construction(self):
        r'''
            Returns a functor that builds the DDRing.

            Method that construct a functor `F` and an integral domain `R` such that ``self == F(R)``. This method allows the 
            coerce system in Sage to handle :class:`DDFunction` and :class:`DDRing` appropriately.

            OUTPUT:

            This method returns a tuple `(F,R)` where `F` is a functor such that ``self == F(R)``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: from ajpastor.dd_functions.ddFunction import DDRingFunctor
                sage: from ajpastor.dd_functions.ddFunction import ParametrizedDDRingFunctor
                sage: F,R = DFinite.construction()
                sage: F == DDRingFunctor(1,QQ)
                True
                sage: R == QQ[x]
                True
                sage: F,R = DDFinite.construction()
                sage: F == DDRingFunctor(2,QQ)
                True
                sage: R == QQ[x]
                True

            The functor for Parametrized DDRings works a bit differently: it adds the parameters to the appropriate DDRing::

                sage: S = ParametrizedDDRing(DDFinite, ['a','b'])
                sage: F, R = S.construction()
                sage: F == ParametrizedDDRingFunctor(2, QQ, set([var('a'), var('b')]))
                True
                sage: R == QQ[x]
                True
        '''
        return (DDRingFunctor(self.depth(), self.coeff_field), self.__original)
        
    def __contains__(self, X):
        r'''
            Decide if an element belongs to ``self``.

            The method is implemented in a very generic way, looking if the parent of the input is related or has a coercion
            with ``self``. In addition, we try to call the method :func:`~DDRing._element_constructor_` of ``self`` to build an 
            element from the input ``X``, whatever it is.

            See the methods :func:`DDRing._element_constructor_`, and :func:`DDRing._has_coerce_map_from` for further information.

            OUTPUT:

            ``True`` or ``False`` depending if ``X`` can be casted to an element of ``self`` or not.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: Exp(x) in DFinite
                True
                sage: Exp(Sin(x)) in DFinite
                False
                sage: Exp(Sin(x)) in DDFinite
                True
                sage: s2 = var('s2')
                sage: F.<s2> = NumberField(s2^2 - 2)
                sage: R = DDRing(F[x])
                sage: Exp(x) in R
                True
                sage: Exp(x) in DDFinite
                True
                sage: e2 = R.element([-s2,1], [1])
                sage: e2 in R
                True
                sage: e2 in DFinite
                False
                sage: e2 in DDFinite
                False
        '''
        try:
            pX = parent(X) # avoids error when X is a type (such as 'int', 'list' or 'tuple')
            if((pX is self) or (self._has_coerce_map_from(pX))):
                return True
        except AttributeError:
            pass
        try:
            self(X)
            return True
        except Exception:
            return False
    
    #################################################
    ### Magic python methods
    #################################################
    def __hash__(self):
        r'''
            Hash method for the class :class:`DDRing`.

            The hash is computed with the depth and the hash for the original ring of coefficients.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: hash(DFinite) == hash(DFinite)
                True
                sage: hash(DDFinite) == hash(DDFinite)
                True
        '''
        return hash(self.original_ring())+self.depth()

    def __eq__(self, other):
        r'''
            Method to check equality of this Parent structure

            We consider that a :class:`~sage.structure.parent.Parent` structure is equal to another if there 
            are coercion maps from both structures.

            INPUT:
                * ``other``: a Sage object.

            OUTPUT:

            ``True`` if ``self`` and ``other`` are the same parent structure.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite == DFinite
                True
                sage: DDFinite == DDFinite
                True
                sage: DFinite == DDFinite
                False
        '''
        if(isinstance(other, DDRing)):
            return self._has_coerce_map_from(other) and other._has_coerce_map_from(self)
        return False
     
    ## Other magic methods   
    def _repr_(self):
        r'''
            Method implementing the ``__repr__`` magic python method. 

            Returns a string telling that self is a :class:`DDRing` and which ring is its base.
        '''
        return "DD-Ring over (%s)" %(self.base())

    def _latex_(self):
        r'''
            Method to create the LaTeX representation for a :class:`DDRing`.

            Returns a valid LaTeX string in math mode to print the :class:`DDRing` in appropriate notation
        '''
        return "\\text{D}\\left(%s\\right)" %latex(self.base())
        
    def _to_command_(self):
        r'''
            Return a Sage command to create ``self``.

            This method returns a string that can be directly executed in Sage (once the package :mod:`ajpastor.dd_functions`) 
            that can recreate this :class:`DDRing`.

            This method is called by the more general method :func:`~ajpastor.dd_functions.ddFunction.command` provided in
            the module :mod:`~ajpastor.dd_functions.ddFunction`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: command(DFinite)
                "DDRing(PolynomialRing(QQ, ['x']))"
                sage: eval(command(DFiniteI)) == DFiniteI
                True
        '''
        return "DDRing(%s)" %command(self.base())
            
    #################################################
    ### Integral Domain and Ring methods
    #################################################
    def _an_element_(self):
        r'''
            Create the element `1` for this ring.

            This is a method required for all the :class:`~sage.structure.parent.Parent` and has to return an 
            element in this structure. In this case, we return the element `1`.

            OUTPUT:

            A :class:`DDFunction` representing the element `1` in ``self``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = DFinite._an_element_()
                sage: f == 1
                True
                sage: f.parent() is DFinite
                True
                sage: DDFinite._an_element_() in DDFinite
                True
                sage: DDFinite._an_element_() == f
                True

        '''
        return self.one()
    
    def random_element(self,**kwds):
        r'''
            Method to compute a random element in this ring. 

            This method relies in the random generator of the base ring and the field of coefficients (see method :func:`~DDRing.base_ring`.
            This method allows several arguments for fixing the bounds of the minimal and maximal order of the defining
            differential equation and if we look for a simple element (namely, the leading coefficient of the differential equation
            is equal to `1`).

            INPUT:
                * ``kwds``: custom parameters for the random generator. This method will consider the following parameters:
                    * ``min_order``: minimal order for the equation we would get (default to `1`)
                    * ``max_order``: maximal order for the equation we would get (default to `3`)
                    * ``simple``: if True, the leading coefficient will always be one (default ``True``)

                  All other parameters will be pass to the random generators.

            OUTPUT:

            A random :class:`DDFunction` included in ``self``.
        '''
        ## Getting the arguments values
        min_order = kwds.pop("min_order", 1)
        max_order = kwds.pop("max_order", 3)
        simple = kwds.pop("simple", True)

        ## Checking the argument values
        min_order = max(min_order,0) ## Need at least order 1
        max_order = max(min_order, max_order) ## At least the maximal order must be equal to the minimal
        if(simple != True and simple != False):
            simple = False

        ## Computing the list of coefficients
        R = self.base()
        S = self.coeff_field
        coeffs = [R.random_element(**kwds) for i in range(randint(min_order,max_order)+1)]
        
        init_values = [0]
        while(init_values[0] == 0):
            init_values[0] = S.random_element(**kwds)

        ## If we want simple elements, we can compute the initial values directly
        if(simple):
            coeffs[-1] = R.one()
            init_values += [S.random_element() for i in range(len(coeffs)-2)]
            return self.element(coeffs,init_values)
        ## Otherwise, we need to know the initial value condition
        warnings.warn("Not-simple random element not implemented. Returning zero", DDFunctionWarning, stacklevel=2)

        return self.zero()

    def characteristic(self):
        r'''
            Method that returns the characteristic of this :class:`DDRing`.

            The characteristic of a ring can be seen as the cardinality of the minimal additive
            subgroup generated by the element `1`. It is said to be zero if this cardinality 
            is infinite.

            The characteristic of a differentially definable ring over `R` is always the same as 
            the characteristic of `R` since, in particular, `R \subset D(R)`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.characteristic()
                0
                sage: DDFinite.characteristic()
                0
        '''
        return self.base().characteristic()
        
    def base_ring(self):
        r'''
            Return the base field for the coefficients of the elements.

            The class :class:`DDRing` represent the power series solutions over a field `\mathbb{K}`
            that satisfy a linear differential equation with some coefficients. This method
            returns the field `\mathbb{K}`.

            This is a required method for extending rings. 

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.base_ring() is DFinite.coeff_field
                True
                sage: DFinite.base_ring() == QQ
                True
                sage: DDFinite.base_ring() == QQ
                True
                sage: s2 = var('s2')
                sage: F.<s2> = NumberField(s2^2 - 2)
                sage: R = DDRing(F[x])
                sage: R.base_ring() == QQ
                False
                sage: R.base_ring() == F
                True
                sage: R.base_ring() is R.coeff_field
                True

            In the case of :class:`ParametrizedDDRing`, the base field contains the parameters::

                sage: S = ParametrizedDDRing(DFinite, ['a','b'])
                sage: pars = S.parameters()
                sage: S.base_ring() == FractionField(PolynomialRing(QQ, pars))
                True
        '''
        return self.__base_field

    coeff_field = property(base_ring, None) #: alias for method :func:`~DDRing.base_ring` 
        
    def original_ring(self):
        r'''
            Returns the original ring from which we build the iterative :class:`DDRing`.

            This method returns the original ring from which ``self`` can be constructed iteratively as a :class:`DDRing`. 
            See also :func:`~DDRing.depth` for further information.

            OUTPUT:

            An integral domain `R` such that ``DDRing(R, depth=self.depth())`` is ``self``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.original_ring() == QQ[x]
                True
                sage: DDFinite.original_ring() == QQ[x]
                True
                sage: DFiniteI.original_ring() == NumberField(QQ[x]('x^2+1'), 'I')[x]
                True

            As usual, the :class:`ParametrizedDDRing` will include the parameters in the base field::

                sage: R = ParametrizedDDRing(DDFinite, ['a','b'])
                sage: vars = R.parameters()
                sage: R.original_ring() == FractionField(PolynomialRing(QQ, vars))[x]
                True
        '''
        return self.__original
        
    def depth(self):
        r'''
            Returns the depth on iteration of the construction of ``self`` as a Differentially Definable Ring.

            The method returns the depth of ``self`` as a :class:`DDRing`. This is a measure on how many times we 
            iterate the process of building a differentially definable ring from. See :func:`~DDRing.original_ring`
            for further information.

            OUTPUT:
                
            A (strictly) positive integer `n` such that ``DDRing(self.original_ring(), n)`` is ``self``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.depth()
                1
                sage: DDFinite.depth()
                2

            The :class:`ParametrizedDDRing` will share the depth of the rings from where they are built::

                sage: ParametrizedDDRing(DDFinite, ['a','b']).depth()
                2
                sage: ParametrizedDDRing(DDRing(QQ[x], depth=10), ['a','b']).depth()
                10
        '''
        return self.__depth
        
    def to_depth(self, dest):
        r'''
            Returns the :class:`DDRing` of the corresponding depth.

            Given a differential ring `(R,\partial)`, the corresponding :class:`DDRing` (`D(R)`) is always
            a new differential ring. Hence we can iterate the process and build the ring `D^n(R)` (which
            is said to have depth `n`).

            This method takes a ring of the form `D^m(R)` and returns the ring `D^n(R)` where `n` is 
            given by the argument ``dest``.

            INPUT:
                * ``dest``: final depth for the :class:`DDRing`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.to_depth(1) is DFinite
                True
                sage: DDFinite.to_depth(1) is DFinite
                True
                sage: DFinite.to_depth(10) == DDRing(QQ[x], depth = 10)
                True
                sage: DFinite.to_depth(5) == DDFinite.to_depth(5)
                True 
        '''
        return DDRing(self.original_ring(), 
        depth = dest, 
        base_field = self.coeff_field, 
        invertibility = self.__base_invertibility, 
        derivation = self.base_derivation, 
        default_operator = self.operator_class)
    
    def extend_base_field(self, new_field):
        r'''
            Method to extend the base field of the :class:`DDRing`.

            This method creates a new :class:`DDRing` where the base field is extended using 
            the ``new_field`` argument. Namely, this method computes a common extension
            for the current field and the provided field.

            This method will also extend accordingly the ring of coefficients (since it always has to be 
            an extension of the base field). The other parameters for :class:`DDRing` are preserved.

            INPUT:
                * ``new_field``: the field that will extend :func:`~DDRing.coeff_field`.

            EXAMPLES::
            
                sage: from ajpastor.dd_functions import *
                sage: Qi.<I> = NumberField(QQ['x']('x^2+1'))
                sage: DFinite.extend_base_field(Qi) == DFiniteI
                True
                sage: DFiniteI.extend_base_field(Qi) is DFiniteI
                True
                sage: DFinite.extend_base_field(Qi).base_ring() == QQ[x]
                False
                sage: DFiniteP.extend_base_field(Qi)
                DD-Ring over (Univariate Polynomial Ring in x over Number Field in I with defining polynomial x^2 + 1) with parameter (P)
        '''
        return DDRing(pushout(self.original_ring(), new_field), 
        depth = self.depth(), 
        base_field = pushout(self.coeff_field, new_field), 
        invertibility = self.__base_invertibility, 
        derivation = self.base_derivation, 
        default_operator = self.operator_class)
        
    def is_field(self, **kwds):
        r'''
            Generic method for checking if ``self`` is a field.

            For the particular case of D-finite functions, there is a condition such that
            both `f(x)` and `1/f(x)` are D-finite. Namely, `f'(x)/f(x)` has to be algebraic.
            This is usually not the case. Hence, :class:`DDRing` is not a field.

            OUTPUT:

                It always returns ``False``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: all(F.is_field() is False for F in [DFinite, DDFinite])
                True
        '''
        return False
        
    def is_finite(self, **kwds):
        r'''
            Generic method for checking if ``self`` is finite.

            The only case in where this is ``True`` is when the ring of coefficients is
            the zero ring. In this case, the behavior of this class in unpredictable.

            OUTPUT:

                It returns whether the base ring is the zero ring or not.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: all(F.is_finite() is False for F in [DFinite, DDFinite])
                True
        '''
        return self.base().is_zero()
        
    def is_noetherian(self, **kwds):
        r'''
            Generic method for checking if ``self`` is Noetherian.

            Currently it is not known when or whether a :class:`DDRing` is Noetherian or not. Hence we always return ``False``.

            OUTPUT:
                
                This method always returns ``False``

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: all(F.is_noetherian() is False for F in [DFinite, DDFinite])
                True
        '''
        return False

    #################################################
    ### DDRings methods
    #################################################
    def default_operator(self):
        r'''
            Getter of the class for default operators.

            This method returns the default class of operators that will be use to 
            represent elements in ``self``. These operators are elements of 
            type :class:`~ajpastor.operator.Operator`. 
        '''
        return self.__default_operator

    operator_class = property(default_operator, None) #: alias for method :func:`~DDRing.default_operator`
    
    def is_invertible(self,x):
        r'''
            Method that checks whether an element in ``self.base()`` is invertible.
            
            INPUT:
                * ``x``: an element of ``self.base()``

            OUTPUT:
            
            ``True`` if ``x`` is in ``self.base()`` and it is a unit, ``False`` otherwise.
        '''
        return x in self.base() and self.__base_invertibility(self.base()(x))

    def derivation_on_base(self):
        r'''
            Method to get the method for computing derivatives in ``self.base()``.

            This method returns the function that computes derivatives of elements in the
            base ring of ``self``.
        '''
        return self.__base_derivation

    base_derivation = property(derivation_on_base, None) #: alias for method :func:`~DDRing.derivation_on_base`
    
    def element(self,coefficients=[],init=[],inhomogeneous=0 , check_init=True, name=None):
        r'''
            Method to create a :class:`DDFunction` contained in ``self``.
            
            This method creates an object of type :class:`DDFunction` that is contained in ``self``. These objects
            are formal power series that satisfy a linear differential equation with coefficients in the ring
            given by :func:`~DDRing.base`. This method receives the list of coefficients for the differential 
            equation (or the differential operator directly), and inhomogeneous term and initial values.

            This is the unique *public* way of building :class:`DDFunction`, since the class itself is not public.

            INPUT:
                * ``coefficients``: either a differential operator (:class:`~ajpastor.operator.operator.Operator`)
                  or a list of elements in the ring given by :func:`~DDRing.base`.
                * ``init``: list of initial values for the function. This is a list of elements that must be 
                  in the field given by :func:`~DDRing.base_ring`.
                * ``inhomogeneous``: element on ``self`` that will denote the inhomogeneous term in the differential
                  equation.
                * ``check_init``: boolean value to check that initial conditions are valid or not.
                * ``name``: optional argument for providing a name to the new built function.

            OUTPUT:

            A differentially definable function (:class:`DDFunction`) `f(x)` such that it satisfies the linear differential
            equation with coefficients given by ``coefficients``, inhomogeneous term given by ``inhomogeneous`` and 
            initial values (i.e., `f(0), f'(0), f''(0),\ldots`) given by ``init``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = DFinite.element([-1,1],[1])
                sage: f in DFinite
                True
                sage: f.equation[0]
                -1
                sage: f.equation[1]
                1
                sage: is_DDFunction(f)
                True
                sage: g = DFinite.element([1,-1],[1],name="g(x)"); g
                g(x)
                sage: g == f
                True
        '''
        return DDFunction(self,coefficients,init,inhomogeneous, check_init=check_init, name=name)
        
    def eval(self, element, X=None, **input):
        r'''
            Method to evaluate an element of a :class:`DDRing`.

            This method implements the evaluation of a :class:`DDFunction` in ``self``. Elements of a :class:`DDRing`
            are formal power series, hence there are three types of evaluations:
                
            * Value evaluation: we set a value for the main variable (see :func:`~DDRing.variables`)
            * Parameter evaluation: in the case that ``self`` is a :class:`ParametrizedDDRing`, 
              the parameters can be evaluated into elements of the field given by :func:`~DDRing.base_ring`.
            * Functional evaluation (i.e., composition): we can also compute the composition as 
              formal power series (if possible).

            INPUT:
                * ``element``: the element in ``self`` to be evaluated.
                * ``X``: the value to be evaluated. This has to be a :class:`DDFunction` or a value
                  in the field :func:`~DDRing.base_ring`.
                * ``input``: a dictionary with the values for the parameters. The keys need to be 
                  the names of the parameters provided by :func:`~DDRing.parameters` and the main
                  variable (see :func:`~DDRing.variables`). They have to be elements in the 
                  base field (see :func:`~DDRing.base_ring`) or, in the case of the main variable, 
                  another :class:`DDFunction`.

            OUTPUT:

            The result of evaluating the function:
            
            * In the case of being a parametric evaluation, we return another :class:`DDFunction` in 
              the corresponding ring.
            * In the case of value evaluation: this method returns the initial value at zero if that
              is the point of evaluation and a numerical approximation (see method :func:`DDFunction.numerical_solution`
              for further information) in case it is another point.
            * In the case of function evaluation: this method returns the new :class:`DDFunction`

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = DFinite.element([-1,1],[1])
                sage: DFinite.eval(f, 0)
                1
                sage: DFinite.eval(f, f-1) == DDFinite.element([-f,1],[1])
                True
                sage: DFinite.eval(f, a=2) == f # no parameter 'a' in 'f'
                True
                sage: g = DFiniteP.element([-1,1],['P'])
                sage: DFiniteP.eval(g, 0, P=3)
                3
                sage: DFiniteP.eval(g, P=1) == f
                True
                sage: DFiniteP.eval(f, P=1) == f # no parameter P appears in f
                True
                sage: DFiniteP.eval(g, 0, P=3, a=1)
                3
                sage: DFiniteP.eval(g, 0, b = 7)
                P
        '''
        if not element in self:
            raise TypeError('The element to evaluate (%s) is not an element of this ring (%s)'%(repr(element),self))
        element = self(element)
            
        ## Extracting the arguments
        rx = X
        self_var = str(self.variables(True)[0])
        if((rx is None) and (self_var in input)):
            rx = input.pop(self_var)

        ## Numerical evaluation <=> rx in self.coeff_field
        ## Parameter evaluation => len(input) > 0
        ## Functional evaluation <=> (not rx is None) and (not rx in self.coeff_field)
        
        ## First we do the parametric evaluation in case it is needed:
        element = self._parametric_evaluation(element, **input)

        ## Now we do the evaluation of the main variable
        if not (rx is None):
            if(rx == 0): # Simplest case: rx == 0 --> return the initial value
                return element.init(0)
            elif(rx in self.coeff_field): # numerical evaluation: use the numerical evaluation method
                return element.numerical_solution(rx,**input)[0]
            else: # in any other case, we return the composition
                return element.compose(rx)
        else:
            return element
                
    def _parametric_evaluation(self, element, **input):
        r'''
            Computes an evaluation of the parameters on an element of ``self``.

            Since the class :class:`DDRing` has no parameters, this method returns the same element and leave intact
            the dictionary ``input``.
        '''
        return element

    def interlace_sequences(self, *functions):
        r'''
            Method to compute the interlacing of several functions in ``self``.

            The interlacing of formal power series are the corresponding interlacing of the sequences 
            that generates them. Namely, let `f_1(x),\ldots,f_m(x)` be formal power series such that:

            .. MATH::

                f_i(x) = f_{i,0} + f_{i,1}x + \ldots + f_{i,n}x^n + \ldots

            Then the interlacing of these functions is the power series generated by the sequence

            .. MATH::

                (f_{1,0}, f_{2,0}, \ldots, f_{m,0}, f_{1,1}, f_{2,1}, \ldots)

            Functionally speaking, this is equivalent to compute the sum

            .. MATH::

                f_1(x^m) + xf_2(x^m) + \ldots + x^{m-1}f_m(x^m)

            This method computes this interlacing explicitly for a list of functions in ``self``. This 
            method takes care of checking that all the elements in the input are valid elements of ``self``.
            
            INPUT:
                * ``functions``: list of the functions `f_1(x),\ldots,f_m(x)`. In the case this input
                  has length 1 and the first is a list, we consider the latter as the input.
            
            OUTPUT:
                
            The interlaced generating function.

            ERRORS:
                * :class:`TypeError` is raised if any of the functions can not be casted to 'self'

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = DFinite.element([-1,1],[1])
                sage: g = DFinite(1/(1-x))
                sage: DFinite.interlace_sequences(f,g).sequence(10, True)
                [1, 1, 1, 1, 1/2, 1, 1/6, 1, 1/24, 1]
                sage: DFinite.interlace_sequences(g,f,g,0).sequence(20, True)
                [1, 1, 1, 0, 1, 1, 1, 0, 1, 1/2, 1, 0, 1, 1/6, 1, 0, 1, 1/24, 1, 0]
                sage: DFinite.interlace_sequences(f,0,0,0) == DFinite.eval(f, x^4)
                True
        '''
        if(len(functions) == 1 and type(functions[0]) == list):
            functions = functions[0]
        
        ## Getting the main variable for the functions
        x = self.variables()[-1]
        m = len(functions)

        if(m == 1): ## Easy case: only one function -- nothing to do
            return self(functions[0])
        
        ## Computing the dilated functions
        functions = [self.eval(el, x**m) for el in functions]
        
        ## Returning the resulting function
        return sum(x**i*functions[i] for i in range(m))
        
    def variables(self, as_symbolic=False):
        r'''
            Method that returns all the variables for ``self``.

            This method returns a tuple with all the variables involved in the :class:`DDRing`.
            These variables are considered to be non-constants. However, the main derivation
            is related with the last element of this tuple.

            This method allows to return these variables with different types,
            i.e., elements of ``self.base()`` or in the :class:`sage.symbolic.ring.SR`. 

            This method never returns a parameter. For getting the parameters (i.e., constant
            variables), see method :func:`~DDRing.parameters`.

            INPUT:
                * ``as_symbolic``: boolean value to decide whether to return the object 
                  as elements of :class:`sage.symbolic.ring.SR` (default: ``False``)

            OUTPUT:

            A tuple (maybe empty) with the variables of ``self``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.variables()
                (x,)
                sage: DFiniteP.variables()
                (x,)
                sage: all(el.parent() is SR for el in DFiniteP.variables(True))
                True
                sage: all(el.parent() is DFiniteP.base() for el in DFiniteP.variables())
                True
        '''
        if(self.__variables is None):
            self.__variables = []
            current = self.base()
            while(current != self.coeff_field):
                self.__variables += [var(str(el)) for el in current.gens()]
                current = current.base()
            if(len(self.__variables) == 0):
                self.__variables += [var(DDRing._Default_variable)]

            self.__variables = tuple(set(self.__variables))
   
        if(as_symbolic):
            return self.__variables
        else:
            return tuple(self.original_ring()(el) for el in self.__variables)

    def parameters(self, as_symbolic = False):
        r'''
            Method that returns all the parameters for ``self``.

            This method returns a tuple with all the parameters involved in the :class:`DDRing`.
            These parameters are constants elements.

            This method allows to return these variables with different types,
            i.e., elements of ``self.coeff_field`` or in the :class:`sage.symbolic.ring.SR`. 

            This method never returns a variable. For getting the variables, 
            see method :func:`~DDRing.parameters`.

            INPUT:
                * ``as_symbolic``: boolean value to decide whether to return the object 
                  as elements of :class:`sage.symbolic.ring.SR` (default: ``False``)

            OUTPUT:

            A tuple (maybe empty) with the parameters of ``self``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.parameters()
                ()
                sage: DFiniteP.parameters()
                (P,)
                sage: all(el.parent() is SR for el in DFiniteP.parameters(True))
                True
                sage: all(el.parent() is DFiniteP.coeff_field for el in DFiniteP.parameters())
                True
        '''
        return tuple([])

    def variable(self, input):
        r'''
            Method that gets a variable from the ring

            This method gets a particular variable from the set of variables (see method
            :func:`~DDRing.variables`). 
            
            INPUT:
                * ``input``: an integer (that will be use in the tuple of variables as 
                  an index) or a string that is the name of the corresponding variable.

            OUTPUT:

            The requested variable as an element in ``self.base()``.
        '''
        if(input in ZZ):
            return self.variables()[ZZ(input)]
        elif(isinstance(input, str)):
            return self.variables()[([str(v) for v in self.variables()]).index(input)]
        else:
            raise NotImplementedError("No parameter can be got with input %s" %input)

    def parameter(self,input):
        r'''
            Method that gets a parameter from the ring

            This method gets a particular parameter from the set of parameters (see method
            :func:`~DDRing.parameters`). 
            
            INPUT:
                * ``input``: an integer (that will be use in the tuple of parameters as 
                  an index) or a string that is the name of the corresponding parameter.

            OUTPUT:

            The requested parameter as an element in ``self.coeff_field``.
        '''
        if(input in ZZ):
            return self.parameters()[ZZ(input)]
        elif(isinstance(input, str)):
            return self.parameters()[([str(v) for v in self.parameters()]).index(input)]
        else:
            raise NotImplementedError("No parameter can be got with input %s" %input)
                
#############################################################################
###
### Ring class for Parametrized DD Functions
###
#############################################################################
def is_ParametrizedDDRing(ring):
    r'''
        Method that checks if an object is a :class:`ParametrizedDDRing`. 

        This method provides a general function to check the class of an object without knowing 
        exactly the name of the basic class of the module. This is basically an alias for the command 
        ``instance(ring, ParametrizedDDRing)``.

        INPUT:
            * ``ring`` -- object to be checked.

        OUTPUT: 
            * ``True`` or ``False`` depending if ``ring`` is a :class:`ParametrizedDDRing` or not.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: is_ParametrizedDDRing(DFinite)
            False
            sage: is_ParametrizedDDRing(DDRing(QQ))
            False
            sage: is_ParametrizedDDRing(QQ)
            False

        Only :class:`ParametrizedDDRing` return ``True`` with this method::

            sage: is_ParametrizedDDRing(DFiniteP)
            True
            sage: is_ParametrizedDDRing(ParametrizedDDRing(DFinite, ['a']))
            True

        SEE ALSO:
            * :class:`ParametrizedDDRing`
    '''
    return isinstance(ring, ParametrizedDDRing)

class ParametrizedDDRing(DDRing):
    r'''
        Class for Parametrized Differentially Definable Rings.

        This class represents a particular type of :class:`DDRing`. Namely, we add parameters
        that we know are constant values that can be evaluated to elements in the ground field.

        Theoretically speaking, if we were considering formal power series `\mathbb{K}[[x]]`
        and we want to add a parameter `p`, we can this by simply considering the solutions in
        `\mathbb{K}(p)[[x]]` where `\partial(p) = 0`.

        This class add extra methods to handle the parameteres as such and allows the particular 
        evaluation of these parameters (see method :func:`~ParametrizedDDRing._parametric_evaluation`).

        The parameters of this ring can be obtain again by the method :func:`parameters`.

        INPUT:
            * ``base_ddRing``: this input indicates where the coefficients will live and 
              the depth of the :class:`DDRing` we consider.
            * ``parameters``: list of variables (symbolic expressions) or names for the 
              parameters to be considered. This argument can also be given with the name
              ``names`` in order to allow the <> syntax of Sage.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: ParametrizedDDRing(DFinite, 'a')
            DD-Ring over (Univariate Polynomial Ring in x over Rational Field) with parameter (a)
            sage: ParametrizedDDRing(DFinite, 'P') is DFiniteP
            True
            sage: ParametrizedDDRing(DFinite, 'a') == DFiniteP
            False
            sage: R.<P> = ParametrizedDDRing(DFinite)
            sage: R is DFiniteP
            True
    '''
    @staticmethod
    def __classcall__(cls, *args, **kwds):
        r'''
            Particular builder for the class :class:`ParametrizedDDRing`. 

            This method do a special checking of uniqueness for two :class:`ParametrizedDDRing`. It maps all the arguments provided by the user
            and transform them into a standard notation that will be hashable and will allow the system to recognize two
            exact differentially definable rings.

            This implemention mimics the behavior of the class :class:`UniqueRepresentation`.
        '''
        ## In order to call the __classcall__ of DDRing we treat the arguments received
        base_ddRing = args[0]
        if(len(args) > 1 ):
            parameters = args[1]
        else:
            parameters = kwds.get('parameters',None)
        names = kwds.get('names',None)
        
        ## Using the "names" approach of SAGE
        if(parameters is None and names is None):
            raise ValueError("Invalid parameters input format: no parameters given")
        elif(parameters is None):
            parameters = names
        elif(not(names is None)):
            raise ValueError("Invalid syntax creating a ParametrizedDDRing. Use one of the following syntaxes:\n\t- D = ParametrizedDDRing(R,['a','b'])\n\t- D.<a,b> = ParametrizedDDRing(R)")
        
         ## First we get the new variables
        if ((not(type(parameters) == tuple)) and (not(type(parameters) == list)) and (not(type(parameters) == set))):
            parameters = [parameters]
        else:
            parameters = list(parameters)
        if(len(parameters) == 0 ):
            raise TypeError("The list of variables can not be empty")
        
        for i in range(len(parameters)):
            if(type(parameters[i]) == str):
                parameters[i] = var(parameters[i])
            elif(type(parameters[i]) != Expression):
                raise TypeError("All values of the second argument must be strings or SAGE symbolic variables")
        parameters = tuple(set(parameters))
        
        ## We consider not the case the base ring is already parametrized
        if(isinstance(base_ddRing, ParametrizedDDRing)):
            parameters = tuple(set(parameters).union(base_ddRing.parameters(True)))
            base_ddRing = base_ddRing.base_ddRing()
            
        ## We rebuild now the base ring for the DDRing operator
        base_field = base_ddRing.coeff_field
        constructions = [base_ddRing.construction()] # Here is the DD-Ring operator
            
        while(constructions[-1][1] != base_field):
            constructions += [constructions[-1][1].construction()]
             
        new_basic_field = PolynomialRing(base_field, parameters).fraction_field()
        current = new_basic_field
        for i in range(1 ,len(constructions)):
            current = constructions[-i][0](current)
            
        if(constructions[0][0].depth() > 1 ):
            base_ring = ParametrizedDDRing(DDRing(base_ddRing.original_ring(),depth=constructions[0][0].depth()-1 ), parameters)
            ring = DDRing.__classcall__(cls, base_ring, 1 , base_field = new_basic_field, default_operator = base_ddRing.operator_class)
            Ring_w_Sequence.__init__(ring, base_ring, method = lambda p,n : ring(p).sequence(n))
            IntegralDomain.__init__(ring, base_ring, category=_IntegralDomains)
        else:
            ring = DDRing.__classcall__(cls, current, depth = constructions[0][0].depth(), base_field = new_basic_field, default_operator = base_ddRing.operator_class)
            
        ring.__init__(base_ddRing, parameters)
        ring.set_sargs(*args, **kwds)
        return ring
        
    def __init__(self, base_ddRing, parameters):
        '''
            This class represent a generalized concept of DDRing. If `R` is a domain of the power series space (`K[[x]]`), and `D(R)` is its associated DDRing, then we can consider new constants elements and consider `D(R)`  but with the basic field be `K(var_1,...,var_m)`
            
            INPUT:
                - base_ddRing: Base DDRing where this new ring will be based. This parameter can be got using method ``getBaRing``.
                - variables: a list of variables or strings which will be the names of the new variables.
        '''
        ## Checking the first argument
        if ((not(isinstance(base_ddRing, DDRing))) or (isinstance(base_ddRing, ParametrizedDDRing))):
            raise TypeError("Needed a DDRing as first argument for create a Parametrized DDRing")
        
        self.__parameters = tuple(set(parameters))
                    
        self.__baseDDRing = base_ddRing
            
    def _coerce_map_from_(self, S):
        r'''
            Method to get the coerce map from the Sage structure `S` (if possible).
            
            To allow the algebraic numbers, we use the method :func:`DDRing.__get_gens__` to compare how the ring `S` and
            the ring ``self`` where built. If at some point we can not use the behavior of the generators, we 
            will rely on the function in the base :class:`DDRing`.
        '''
        coer = super(ParametrizedDDRing, self)._coerce_map_from_(S)
        if(not(coer)):
            coer = self.__baseDDRing._coerce_map_from_(S)
            
        return not(not(coer))
            
    def construction(self):
        r'''
            Returns a functor that builds the DDRing.

            Override method from class :class:`DDRing`.

            See method :func:`DDRing.construction` for further information and tests.
        '''
        return (ParametrizedDDRingFunctor(self.depth(), self.__baseDDRing.coeff_field, set(self.__parameters)), self.__baseDDRing._DDRing__original)
            
    def base_ddRing(self):
        r'''
            Method that returns the original :class:`DDRing`.

            This method returns the basic :class:`DDRing` where we added the parameters. This 
            ring must have the same depth as ``self``. 
            
            OUTPUT:

            A :class:`DDRing` where elements of ``self`` would be if we substitute the parameters by elements
            of the base ring (see :func:`DDRing.base_ring`).

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFiniteP.base_ddRing() is DFinite
                True
                sage: DFiniteP.to_depth(5).base_ddRing() is DFinite.to_depth(5)
                True

        '''
        return self.__baseDDRing
        
    def _repr_(self):
        r'''
            Method implementing the ``__repr__`` magic python method. 

            Returns a string telling that self is a :class:`DDRing` with parameters and which ring is its base.
        '''
        res = "(%s" %str(self.parameters()[0])
        for i in range(1 ,len(self.parameters())):
            res += ", " + str(self.parameters()[i])
        res += ")"
        
        if(len(self.parameters()) > 1 ):
            return "%s with parameters %s" %(self.base_ddRing(),res)
        else:
            return "%s with parameter %s" %(self.base_ddRing(),res)
    
    def parameters(self, as_symbolic = False):
        r'''
            Method that returns all the parameters for ``self``.

            Overrides the method from class :class:`DDRing`.

            See method :func:`DDRing.parameters` for further information and examples.
        '''
        if(as_symbolic):
            return self.__parameters
        else:
            return tuple([self.coeff_field(el) for el in self.__parameters])
            
    def gens(self):
        r'''
            Implementation of the method ``gens``.

            Overrides the method from class :class:`DDRing`.

            In the case of :class:`ParametrizedDDRing` and in order to make the <> creation syntax of 
            Sage work, we return the list of paramters as symbolic variables.

            For further information, see method :func:`DDRing.gens`

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: R = ParametrizedDDRing(DFinite, ['a'])
                sage: R.gens()
                (a,)
                sage: ParametrizedDDRing(R, ['b']).gens()
                (b, a)
        '''
        return self.parameters(True)
        
    def _first_ngens(self, n):
        r'''
            Auxiliary method for getting the first generators.

            This methods is required for the <> creation syntax of Sage and returns
            the first `n` generators (i.e., parameters) as elements in ``self``.
        '''
        return self.parameters(False)[:n]
                         
    def to_depth(self, dest):
        r'''
            Returns the :class:`DDRing` of the corresponding depth.

            Overrides the method from class :class:`DDRing`.

            In the case of :class:`ParametrizedDDRing`, this method guarantees that the output 
            is again a :class:`ParametrizedDDRing`. Since we could build a :class:`DDRing` with 
            the same field for the power series coefficients (see method :func:`~DDRing.base_ring`) 
            but without the parametric behavior, we need to specifically call the constructor
            of this class to keep that behavior.

            INPUT:
                * ``dest``: final depth for the :class:`DDRing`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFiniteP.to_depth(2) is ParametrizedDDRing(DDFinite, 'P')
                True

            For further information and examples, see method :func:`DDRing.to_depth`.
        '''
        return ParametrizedDDRing(self.base_ddRing().to_depth(dest), self.parameters(True))
    
    def extend_base_field(self, new_field):
        r'''
            Method to extend the base field of the :class:`DDRing`.

            Overrides the method from :class:`DDRing`.

            In the case of :class:`ParametrizedDDRing`, this method guarantees that the output 
            is again a :class:`ParametrizedDDRing`. Since we could build a :class:`DDRing` with 
            the same field for the power series coefficients (see method :func:`~DDRing.base_ring`) 
            but without the parametric behavior, we need to specifically call the constructor
            of this class to keep that behavior.

            For further information and examples, see :func:`DDRing.extend_base_field`.
        '''
        return ParametrizedDDRing(self.base_ddRing().extend_base_field(new_field), self.parameters(True))
            
    def _parametric_evaluation(self, element, **input):
        r'''
            Method to evaluate the parameters of an element of ``self``.

            This method takes an element in ``self`` (which has already the appropriate structure)
            and evaluates the parameters given by ``input``. These parameters are removed
            from the dictionary ``input``, leavin extra arguments for the method :func:`~DDRing.eval`.

            The output of this method is a :class:`DDFunction` that have evaluated all the given parameters.
            These parameters have to be elements in the field given by :func:`~DDRing.base_ring`. Interestingly,
            these values can have again new parameters  that need to be taken into consideration.
        '''
        self_var = str(self.variables(True)[0])
        ### Getting the final parameters
        original_parameters = set(str(el) for el in self.parameters()) # parameters from 'self'.
        used_parameters = set([key for key in input.keys() if key in original_parameters]) # parameters on input

        if(len(used_parameters) == 0): # nothing to evaluate
            return element
        ## We remove the used parameters
        values = {key : input.pop(key) for key in used_parameters}

        ### Getting the new parameters from the values at input
        got_parameters = reduce(lambda p,q : p.union(q), [set(str(el) for el in SR(value).variables()) for value in values.values()])
        
        destiny_parameters = (original_parameters - used_parameters).union(got_parameters)
                    
        if(self_var in destiny_parameters):
            raise TypeError("Parameters can only be evaluated to constants.\n\t- Got: %s" %(values))
        
        if(len(destiny_parameters) == 0): # all parameters evaluated: go to the DDRing
            destiny_ring = self.base_ddRing()
        else:
            destiny_ring = ParametrizedDDRing(self.base_ddRing(), tuple(destiny_parameters))
            
        new_equation = destiny_ring.element([el(**values) for el in element.equation.coefficients()]).equation
        
        new_init = [el(**values) for el in element.init(new_equation.get_jp_fo()+1, True, True)]
        new_name = None
        if(element._DDFunction__name is not None):
            new_name = m_dreplace(element._DDFunction__name, {key: str(values[key]) for key in values}, True)
        return destiny_ring.element(new_equation,new_init,name=new_name)
            
    def _to_command_(self):
        r'''
            Return a Sage command to create ``self``.

            Overrides the method from class :class:`DDRing`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: command(DFiniteP)
                "ParametrizedDDRing(DDRing(PolynomialRing(QQ, ['x'])), ['P'])"
                sage: eval(command(DFiniteP)) is DFiniteP
                True

            See method :func:`command` for further information.
        '''
        return "ParametrizedDDRing(%s, %s)" %(self.base_ddRing()._to_command_(), [str(par) for par in self.parameters()])
        
#####################################################
### Class for DD-Functions
#####################################################
def is_DDFunction(func):
    r'''
        Method that checks if an object is a :class:`DDFunction`. 

        This method provides a general function to check the class of an object without knowing 
        exactly the name of the basic class of the module. This is basically an alias for the command 
        ``instance(ring, DDFunction)``.

        INPUT:
            * ``func`` -- object to be checked.

        OUTPUT: 
        
        ``True`` or ``False`` depending if ``ring`` is a :class:`DDFunction` or not.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: is_DDFunction(DFinite)
            False
            sage: is_DDFunction(DDRing(QQ))
            False
            sage: is_DDFunction(QQ)
            False

        The objects returned by the method :func:`DDRing.element` are of this type::

            sage: is_DDFunction(DFinite.element([-1,1],[1]))
            True
            sage: is_DDFunction(DFiniteP.element(['-P',1],['P']))
            True

        SEE ALSO:
            * :class:`DDFunction`
    '''
    return isinstance(func, DDFunction)

class DDFunction (IntegralDomainElement, SerializableObject):
    r'''
        Class for representing a differentially definable function.

        A differentially differentially function is a formal power series `f(x)`
        that satisfies a linear differential equation:

        .. MATH::

            r_d(x)f^{(d)}(x) + \ldots + r_0(x)f(x) = 0,

        where the coefficients are in a particular integral domain `R`. We say that
        `f(x)` belongs to `D(R)` (see :class:`DDRing`). This set forms a ring
        being able to compute the new differential equations by solving a 
        linear system.

        Furthermore, a particular function `f(x)` can be represented using 
        a linear differential operator that annihilates it (see above) and
        some initial conditions `f(0), f'(0), \ldots`.

        This class is exactly the use of this representation (via differential
        operator plus initial values) of differentially definable functions.

        INPUT:

        * ``parent``: a :class:`DDRing` where the coefficients of the differential operator
          belongs.
        * ``input``: differential operator that annihilates ``self``. This can be given as 
          a list of coefficients (like ``[r_0, r_1,...,r_d]``) where all the elements must 
          belong to the ring of coefficients of ``parent`` (see method :class:`DDRing.base`)
        * ``init_values``: initial values for ``self``. These values can be given in two forms:
          
          * either a list ``[a0, a1, ..., an]`` such that `f^{(k)}(0) = a_k`,
          * or a dictionary ``{k: ak}``. 
          

        * ``inhomogeneous``: an element in ``parent``. If given, the function represented 
          by ``self`` will satisfy instead the linear differential equation

          .. MATH::
        
            r_d(x)f^{(d)}(x) + \ldots + r_0(x)f(x) = g(x)

          where `g(x)` is the differentially definable function defined by this argument.
        * ``check_init``: optional boolean argument to determine whether to check in the building
          the initial values provided. This is recommended to be used, but in some instances, 
          where we know that there is a solution with the initial values given by ``init_values``,
          such as when applying closure properties.
        * ``name``: in order to make objects easier to print and read, we can set a fixed name
          for a function that will be used when the method :func:`repr` is called.

        WARNING: 
        
        * This class should never be directly instanciated. It is recommended to create the 
          functions from their corresponding :class:`DDRing` (see method :func:`DDRing.element`).
          In fact, this class is not automatically loaded when importing the package 
          :mod:`ajpastor.dd_functions`.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: f = DFinite.element([-1,1],[1])
            sage: f
            (1:1:3)DD-Function in (DD-Ring over (Univariate Polynomial Ring in x over Rational Field))
            sage: g = DFinite.element([-1,1],[1,1])
            sage: f == g
            True
            sage: g = DFinite.element([-1,1],[1,2])
            Traceback (most recent call last):
            ...
            InitValueError: There is no such function satisfying ...

        TODO:

        * Add examples of incomplete DDFunctions
        * Add examples of DDFunctions that does not require the first coefficients
        * Add examples where we use the dict input for ``init``
        * Add examples with inhomogeneous term
    '''
    @staticmethod
    def __chyzak_dac(A, s, p, v, o=0, K=QQ, x='x'):
        r'''
            Divide and conquer scheme in Figure 3 of arxiv:`abs/cs/0604101`.
            
            This method presents the Divide and conquer scheme in the paper by Chyzak et. al. for computing the expansion
            of a power series solution for a differential system:
            
            .. MATH::
            
                Y' = AY, Y(0) = v
                
            where `Y \in \mathbb{M}_{r\times 1}(\mathbb{K}[[x]])` and `A` is a square matrix with coefficients in
            `\mathbb{K}[[x]]`. Here, the vector `v \in \mathbb{M}_{r\times 1}(\mathbb{K})`.
            
            More precisely, this method solves the truncated system:
            
            .. MATH::
            
                tY' + (pI_r - tA)Y = s\ (mod x^m).
            
            INPUT:
            
            * ``A``: a list of matrices `A_i \in \mathbb{M}_{r\times r}(\mathbb{K})` such that `\sum_{i=-o}^m A_it^i` is 
            a truncation of the system matrix `A`. We denote the length of his list as `m`.
            * ``s``: a list of vectors `s_i \in \mathbb{M}_{r\times 1}(\mathbb{K})` for the inhomogeneous term of the equation.
            If this is `0`, then a solution for the original system is computed. The length should be again `m`.
            * ``p``: a value on `\mathbb{K}` for the extended equation.
            * ``v``: a list of vectors in \mathbb{M}_{r\times 1}(\mathbb{K}) that contains a truncation of Y.
            * ``o``: negative order of teh matrix `A`. This value is 0 if the entries are not Laurent polynomials.
            * ``K``: field where we base all computations. It must have characteristic zero.
            * ``x``: variable for the ring of formal power series `\mathbb{K}[[x]]`
            
            OUTPUT:
            
            A vector `Y \in \mathbb{M}_{r\times 1}(\mathbb{k}[x])` such that 
            
            .. MATH::
            
                tY' + (pI_r - tA)Y = s\ (mod x^m)        

            TODO: add examples (or move them to the sequence method)
        '''
        ## Checking te input
        if(not K.is_field() or K.characteristic()!= 0):
            raise TypeError("The input 'K' must be a field of characteristic zero")
        
        if(not (o in ZZ) or o < 0):
            raise ValueError("the order input must be a non-negative integer")
            
        Kx = LaurentPolynomialRing(K, str(x)) # polynomial ring for truncations
        x = Kx.gens()[0] # casting x to the element inside the polynomial ring (avoiding casting errors)
            
        A = [a.change_ring(K) for a in A] # checking everything in A is in K
        s = [el.change_ring(K) for el in s] # checking everything in s is in K
        p = K(p) # checking p is in K
        v = [el.change_ring(K) for el in v] # checking everything in v is in K    
        
        m = len(s); r = len(s[0])
        if(len(A) < p+m+o):
            raise ValueError("The truncation of the inhomogeneous part must be at least the truncation on the matrix")
        A = A[:o+m+p] # Removing extra data
        if(any(len(v_el) != r for v_el in v) or any(len(el) != r for el in s) or any(a.nrows() != r for a in A)):
            raise TypeError("The dimensions of the input are not correct")

        ## Base case
        if(m == 1): 
            if(o > 0): # irregular case
                # we build the linear system
                fA = [j*[Matrix(r)] + [-A[i+o-1] for i in range(-o+1, p+1-j)] for j in range(p+o+1)]
                for j in range(p):
                    fA[j][o-1+j] += (p-j)*identity_matrix(r)
                fA = block_matrix(fA)
                fs = vector([el for el in s[0]] + (o+p)*r*[0])
                ## Here the system reads t*y' + (pI - tA)y = s for s vector of constants and y a vector of polynomial of 
                ## degree bounded by "o-1"
                if(p == 0): # base case, we use truncation after checking
                    fv = vector(sum([list(el) for el in v[o-1::-1]], []))
                    
                    if(fA*fv == fs):
                        return sum(v[i]*x**i for i in range(o))
                    else:
                        raise ValueError("The initial truncation is not valid")
                else: # general p: we solve the system
                    sol = list(fA.solve_right(fs))
                    sol = sum([[sol[r*i:r*(i+1)]] for i in range(len(sol)//r)], [])
                    sol.reverse(); sol = [vector(el) for el in sol]

                    return sum(sol[i+p]*x**(i) for i in range(-p, o))            
            if(o == 0): # regular case
                if(p == 0): return v[0]
                else: return s[0]/p

        ## General case
        d = m//2
        y0 = DDFunction.__chyzak_dac(A, s[:d], p, v, o, K, x) # first recursive cal
        AA = sum(A[i]*x**(i-o) for i in range(m+o)); ss = sum(s[i]*x**i for i in range(m))
        R = (ss - x*vector(Kx(diff(el)) for el in y0) - (p*identity_matrix(r) - x*AA)*y0)
        # transforming R into a valid input of DivideAndConquer
        #logger.debug("New value for R: %s" %R)
        if(any(el.valuation() < 0 for el in R)):
            raise ValueError("We got an unexpected Laurent polynomial")
        R = [vector(Kx(el)[i] for el in R) for i in range(d,m)]        
        
        y1 = DDFunction.__chyzak_dac(A, R, p+d, v, o, K, x) #second recursive call
        solution = y0 + x**d*y1
        
        return solution

    #####################################
    ### Init and Interface methods
    #####################################
    def __init__(self, parent, input = 0 , init = [], inhomogeneous = 0 , check_init = True, name = None):   
        # We check that the argument is a DDRing
        if(not isinstance(parent, DDRing)):
            raise DDFunctionError("A DD-Function must be an element of a DD-Ring")
        ### We call superclass builder
        IntegralDomainElement.__init__(self, parent)

        #########################################
        ### CHECKING ALL THE INPUTS
        #########################################
        ## Checking the argument ``input``
        if(isinstance(input, Operator)):
            equation = input.coefficients()
        else:
            equation = input

        ## Checking the argument ``init``
        if(type(init) in [list, tuple]):
            inits = {i : init[i] for i in range(len(init))}
        elif(type(init) == dict):
            inits = {k : init[k] for k in init} # if it is a dictionary, we copy it

        ## Checking the argument ``inhomogeneous``
        if(not inhomogeneous in parent):
            raise TypeError("The inhomogeneous term must be an element of parent (%s)" %inhomogeneous)

        ## Initializing the serializable structure
        SerializableObject.__init__(self, parent, equation, init=init, inhomogeneous=inhomogeneous, name=name)
        ##     input -> equation (list)
        ##     init -> inits (dictionary)
        ##     inhomogeneous -> inhom (element in self.parent())

        ## Checking the equation: if the equation is the zero equation --> error
        zero = False
        if((type(input) in [list,tuple] and len(input) == 0) or input == 0):
            zero = True
        elif(type(input) in [list,tuple] and all(el == 0  for el in input)):
            zero = True
        elif((type(input) in [list,tuple] and len(input) == 1 ) or (isinstance(input, Operator) and input.order() == 0 )):
            zero = (inhomogeneous == 0)
            
        if(zero):
            ### The equation is zero, we need inhomogeneous equals to zero
            if(not inhomogeneous == 0):
                raise DDFunctionError("Incompatible equation (%s) and inhomogeneous term (%s)" %(input, inhomogeneous))
            else: ### Also, all the initial values must be zero
                equation = [0,1]
                if(any(inits[n] != 0 for n in inits)):
                    raise InitValueError("Incompatible equation (%s) and initial values (%s)" %(input, inits))
        
        ### Definition for Cached elements
        self.__pows = {0 :1 , 1 :self} # Powers-cache
        self.__derivative = None # The derivative of a function
        self.__simple_derivative = None # The simple derivative of a function
        self.__name = name
        self.__built = None
        self.__zeros = None
        self.__singularities = None
        self.__computed = None
        self.__chyzak = {}
        
        ### Assigning the differential operator
        ### We will save the leading coefficient of the equation (lc) to future uses.
        # We create the operator using the structure given by our DDRing
        self.__equation = self.__buildOperator(equation)
            
        #################################################################################
        ### INHOMOGENEOUS PART
        # If that is not zero, then we compute the new operator and initial values needed
        # to define the equation.
        if(inhomogeneous != 0):
            ## Getting the basic elements
            inhom = self.parent()(inhomogeneous)
            field = parent.coeff_field
            
            ## Getting the homogeneous differential equation
            new_eq = inhom.equation*self.equation
            
            ## Get the number of elements to check
            ## If inits is too big, we use all the elements for a better checking
            n_init = new_eq.get_jp_fo()+1 
            to_check = max(n_init, len(inits))
            
            ## Getting the matrix of the current equation
            M = Matrix(field, self.equation.get_recursion_matrix(to_check-1 -self.equation.forward_order))
            v = vector(field, inhom.sequence(M.nrows(), True))
            
            ## Solving the system MX = v
            X = M.solve_right(v)
            ker = M.right_kernel_matrix()
            
            ## Choosing a solution such X[i]==inits[i]
            diff = vector(field, [inits[i]-X[i] for i in inits])
            N = Matrix(field, [[v[i] for i in inits] for v in ker]).transpose()

            try:
                to_sum = N.solve_right(diff)
            except Exception as e:
                raise InitValueError("There is no function satisfying\n(%s)(f) == %s\nwith initial values %s" %(self.equation,inhom,init)) from e
            
            ## Putting the new values for the equation and initial values
            inits = X+sum([to_sum[i]*ker[i] for i in range(len(to_sum))])
            inits = {i: inits[i]*factorial(i) for i in range(len(inits))}
            self.__equation = new_eq
        #################################################################################
        
        #################################################################################
        ## After creating the original operator, we check we can not extract an "x" factor
        coeff_gcd = 1 
        if(is_PolynomialRing(self.parent().base())):
            l = []
            for el in self.equation.coefficients():
                l += el.coefficients(x)
            
            coeff_gcd = gcd(l)
            if(coeff_gcd == 0 ):
                coeff_gcd = 1 
        g = coeff_gcd*gcd(self.equation.coefficients())
        if(g != 1  and g != 0 ):
            coeffs = [coeff/g for coeff in self.equation.coefficients()]
            self.__equation = self.__buildOperator(coeffs)
                
        #################################################################################
        ### Managing the initial values
        self.__sequence = {n : self.parent().coeff_field(str(inits[n]))/factorial(n) for n in inits}
        if(check_init):
            m = max([n for n in inits], default=0)+1
            if(m >= self.equation.get_recursion_matrix(0).ncols()): # if we have enough data to check
                try:
                    initSequence = self.sequence(m, True)
                except TypeError as exception: # Catching the impossibility to compute initial values
                    raise InitValueError("Error getting initial values").with_traceback(exception.__traceback__)
                M = self.equation.get_recursion_matrix(len(initSequence)-self.equation.forward_order-1)
                if(M*vector(initSequence) != 0 ):
                    raise InitValueError("There is no such function satisfying %s with initial values %s"%(self.equation,inits))     
            
    def __buildOperator(self, coeffs):
        r'''
            Auxiliary method to build an operator the fits into the parent class operator.

            This method takes care of building an operator (see :class:`~ajpastor.operator.Operator`) that 
            is valid for the parent of ``self``. The input for this operator must be a compatible input
            for the constructor of the operator class, namely, a list of coefficients or an operator itself.
        '''
        if(isinstance(coeffs, self.parent().operator_class)):
            return coeffs
        elif(type(coeffs) == list):
            new_coeffs = []
            for el in coeffs:
                try:
                    new_coeffs += [self.parent().base()(el)]
                except TypeError:
                    try:
                        new_coeffs += [self.parent().base()(str(el))]
                    except:
                        new_coeffs += [el]
            coeffs = new_coeffs
                
        return self.parent().operator_class(self.parent().base(), coeffs, self.parent().base_derivation)

    @property
    def equation(self):
        r'''
            Getter for the equation of a :class:`DDFunction`.
        '''
        return self.__equation
        
    def order(self):
        r'''
            Getter for the order of the equation that defines the :class:`DDFunction`.
        '''
        return self.equation.order()
        
    @derived_property
    def ps_order(self):
        r'''
            Order of the power series.

            This attribute is the order of ``self`` as a power series. A :class:`DDFunction` represents 
            a formal power series in `\mathbb{K}[[x]]` where `\mathbb{K}` is the field returned by
            ``self.parent().base_ring()``. 

            A formal power series is a formal sum of the form:

            .. MATH::

                f(x) = f_0 + f_1 x + \ldots + f_nx^n + \ldots = \sum_{n \geq 0} f_n x^n

            We say that the order of `f(x)` is the minimal `n \in \mathbb{N}` such that
            `f_n \neq 0`. In the case that `f(x) = 0`, we say that the order of 
            `f(x)` is `\infty` (here we return `-1`)

            All non-zero formal power series (see method :func:`~DDFunction.zero_extraction`) can be 
            uniquely written as a product of a power of `x` and a formal power series of order zero.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite.element([-1,1],[1]).ps_order
                0
                sage: DFinite.element([1,0,1],[0,1]).ps_order
                1
                sage: DFinite.element([1,0,1],[1,0]).ps_order
                0
                sage: DFinite(x^5*(x-1)).ps_order
                5
                sage: DFinite.element([-5, x], {5:3}).ps_order
                5
                sage: DFinite.element([-1,1],[0]).ps_order
                +Infinity
        '''
        if(self.is_null):
            return infinity 
        else:
            i = 0 
            while(self.init(i) == 0):
                i += 1 
            
            return i

    valuation = ps_order #: alias for the attribute :func:`ps_order`. Returns the order (as a power series) of ``self``.

    def sequence(self, n, list=False, incomplete=False):
        r'''
            Method to get the `n`-th coefficient of the power series.

            A :class:`DDFunction` represents a formal power series in `\mathbb{K}[[x]]` 
            where `\mathbb{K}` is the field returned by ``self.parent().base_ring()``. 

            A formal power series is a formal sum of the form:

            .. MATH::

                f(x) = f_0 + f_1 x + \ldots + f_nx^n + \ldots = \sum_{n \geq 0} f_n x^n

            This method returns the `n`th coefficient of the power series (i.e., `f_n`). This 
            method also allows an optional parameter (called ``list``) to return instead the 
            first `n` coefficients of the power series.

            INPUT:

            * ``n``: index for the coefficient of number of coefficients to compute
            * ``list``: boolean flag. If ``True``, the method returns a list with the ``n``
              first coefficients of the sequence. Otherwise, it returns the coefficient
              `f_n`. By default, this argument is ``False``.
            * ``incomplete``: boolean flag. If ``False``, the method will raise an error when
              the coefficients can not be computed. Only valid in the case that ``list`` is 
              ``True``, the output (instead of an :class:`~ajpastor.dd_functions.exceptions.NoValueError`)
              will be the list up to the first element we could not compute.

            OUTPUT:

            If ``list`` is ``True``, this method returns the list `[f_0,\ldots,f_{n-1}]`. Otherwise,
            this method returns the element `f_n`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite(1/(1-x)).sequence(10, True)
                [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
                sage: DFinite.element([-1,1],[1]).sequence(5)
                1/120
                sage: DFinite.element([1,0,1],[1,0]).sequence(4)
                1/24
                sage: DFinite.element([1,0,1],[1,0]).sequence(4, True)
                [1, 0, -1/2, 0]

            If the :class:`DDFunction` is not fully defined (i.e., not enough initial data is given)
            this method can also return (when returning lists) an incomplete list instead of an error::

                sage: DFinite.element([-1,1]).sequence(2)
                Traceback (most recent call last):
                ...
                NoValueError: Impossible to compute recursively the 0-th coefficient
                sage: DFinite.element([-1,1]).sequence(2, True)
                Traceback (most recent call last):
                ...
                NoValueError: Impossible to compute recursively the 0-th coefficient
                sage: DFinite.element([-1,1]).sequence(2, True, True)
                []
                sage: DFinite.element([-4, x]).sequence(4)
                Traceback (most recent call last):
                ...
                NoValueError: Impossible to compute recursively the 4-th coefficient
                sage: DFinite.element([-4, x]).sequence(10, True, True)
                [0, 0, 0, 0]
        '''
        if(list):
            if(incomplete):
                result = []
                for i in range(n):
                    try:
                        result += [self.sequence(i)]
                    except NoValueError:
                        break
                return result
            return [self.sequence(i) for i in range(n)]
        
        while(not n in self.__sequence):
            self.extend_sequence()
        
        return self.__sequence[n]

    def isequence(self, n, list=False, incomplete=False):
        r'''
            Method to get the `n`-th coefficient of the inverse for a power series.

            A :class:`DDFunction` represents a formal power series in `\mathbb{K}[[x]]` 
            where `\mathbb{K}` is the field returned by ``self.parent().base_ring()``. These power series
            can be inverted if the constant term is not zero obtaining a new power series.

            This method compute the elements in the sequence for the multiplicative inverse of 
            the differentially definable function represented by ``self`` (see property :func:`inverse`)

            INPUT:

            * ``n``: index for the coefficient of number of coefficients to compute
            * ``list``: boolean flag. If ``True``, the method returns a list with the ``n``
              first coefficients of the sequence. Otherwise, it returns the coefficient
              `f_n`. By default, this argument is ``False``.
            * ``incomplete``: boolean flag. If ``False``, the method will raise an error when
              the coefficients can not be computed. Only valid in the case that ``list`` is 
              ``True``, the output (instead of an :class:`~ajpastor.dd_functions.exceptions.NoValueError`)
              will be the list up to the first element we could not compute.

            OUTPUT:

            See method :func:`sequence` for a description of the output.

            TODO: add examples
        '''
        return self.inverse.sequence(n, list, incomplete) # pylint: disable=no-member

    def extend_sequence(self):
        r'''
            Method to actually extend the list of the computed sequence.

            This method takes into consideration the current situation of ``self`` 
            and decides on the best algorithm to extend the sequence. This decision
            is based on paper :arxiv:`abs/cs/0604101`, which describes the
            best algorithm depending on the type of the coefficients of the differential equation:

            * *Constant coefficients*: if we look to the sequence, we find out a recurrence of 
              order exactly the order of the differential equation, that is pretty simple to unroll.
            * *Polynomial coefficients*: in this case, the recursion is called P-finite. Here,
              once we computed enough initial data, we can compute the next element by evaluating
              `r` polynomials (where `r` is the size of the differential equation), performing 
              `r` multiplications and additions and, then, performing a division.
            * *Power series coefficients*: in this last case, the recursion is not finite and, hence,
              not useful for a simple unrolling. Here, the authors of :arxiv:`abs/cs/0604101` proposed
              a *Divide and Conquer* strategy to improve the performance.

            As we see, each of the cases has a different approach and, in fact, there is one last remaining
            point to consider. If the leading coefficient of the differential equation vanishes at zero
            (i.e., the point `x=0` is a singular point for the differential equation) we fall into slightly 
            different problems:

            * *Constant coefficients*: this never happends
            * *Polynomial coefficients*: the leading coefficient of the recurrence will have positive integer zeros
              which mean that coefficient is undefined. We can only apply the recurrence relation after we have passed 
              that value (i.e., the functions is defined in the sense of function :func:`is_fully_defined`)
            * *Power series coefficients*: we need to apply a relaxed version of the Divide and Conquer strategy
              presented in :arxiv:`abs/cs/0604101` where the solutions it computes will be Laurent polynomials
              instead of simply polynomials with the valuation at most the current degree we are computing and 
              degree the truncation we want plus the valuation of the differential equation.

            Finally, in order to avoid an infinite recursion loop to compute the multiplicative inverses of 
            the coefficients, we also consider the case where the function is defined as the multiplicative inverse of
            another :class:`DDFunction`. In this case, we use a newton scheme for formal power series to compute
            a truncation of self doubling the current precision. This require two multiplication of polynomials
            of size of the desired.

            OUTPUT:

            The index of the last element computed with this extension
        '''
        if(self.__computed is None):
            self.__computed = max([i for i in self.__sequence], default=-1)
            if(any(j not in self.__sequence for j in range(self.__computed))):
                raise ValueError("Missing element in the sequence")
        n = self.__computed # last computed element
        r = self.equation.order() # order of the equation

        # First consideration: self is the inverse of something
        if(self.is_inverse()): # inverse case
            ## If a function is the inverse, we use a Newton iteration to quickly
            ## compute its sequence using the computations for the originalfunction.
            n = n+1 # number of computed elements
            f = self.built[1][0] # self == 1/f
            R = PolynomialRing(self.parent().coeff_field, 'v')
            f2n = R(f.sequence(2*n, True)); y = R(self.sequence(n, True))
            Ny = y*(2 - y*f2n)
            for i in range(n, 2*n):
                self.__sequence[i] = Ny[i]
            self.__computed = 2*n-1
        elif(all(self.equation[i].is_constant() for i in range(r+1))): # constant coefficients
            m = n+1 # element to be computed
            
            if(m < r): # error: not enough data
                raise NoValueError(m)
            self.__sequence[m] = (sum(
                    -self.sequence(m-r+i)*self.equation.forward(i)(n=m-r) # pylint: disable=invalid-unary-operand-type
                    for i in range(r)
                ) / self.equation.forward(r)(n=m-r))
            self.__computed = m
        elif((n+1) > self.equation.get_jp_fo()): # all the data can be computed
            if(self.parent().depth() == 1): # polynomial coefficient case
                m = n+1 # element to be computed
                d = max(max([0,self.equation[i].degree() - i]) for i in range(r)) # maximal inverse shifts appearing in the recurrence
                r = self.equation.forward_order # maximal shift appearing in the recurrence
                polys = [self.equation.backward(-i)(n=m-r) for i in range(-d,0)] + [self.equation.forward(i)(n=m-r) for i in range(r)]
                lc = self.equation.forward(r)(n=m-r)
                self.__sequence[m] = -sum(self.sequence(m-i)*polys[-i] for i in range(1,len(polys)+1))/lc
                self.__computed = m
            else: # power series coefficient case
                ## In this case, we use the Divide and Conquer strategy proposed in 
                m = 2*n # we double the amount of data
                K = self.parent().coeff_field
                x = self.parent().variables()[0]
                r = self.equation.order()
                init = self.init(self.equation.get_jp_fo()+1, True); jp = len(init)
                Kx = PolynomialRing(K, x); x = Kx(x)

                ## we need to get the truncated associated system Y' = AY
                ## here A is the companion matrix transposed
                q = [self.equation[i].ps_order for i in range(r+1)]
                o = -min(q[i] - q[r] for i in range(r+1))
                if(o > 0): #singular case
                    q = [o-q[i]+q[r] for i in range(r+1)]
                    last_row = [
                        -x**q[j]*
                        Kx(self.equation[j].zero_extraction[1].sequence(m,True))*
                        Kx(self.equation[r].zero_extraction[1].isequence(m,True)) for j in range(r)]

                    Kx = LaurentPolynomialRing(K, str(x)); x = Kx(x)
                else:
                    last_row = [-Kx(self.equation[j].sequence(m,True))*Kx(self.equation[r].isequence(m,True)) for j in range(r)]

                A = [Matrix(K, ([[kronecker_delta(i+1,j) if(k == o) else 0 for j in range(r)] for i in range(r-1)] + 
                                    [[last_row[j][k] for j in range(r)]])) for k in range(m+o)]

                if("last" in self.__chyzak and self.__chyzak["last"][1] == n): # we can use previous initial values results
                    y0 = self.__chyzak["last"][0]
                    AA = sum(A[i]*x**(i-o) for i in range(m+o))
                    R = -x*vector(Kx(diff(el)) for el in y0) + x*AA*y0
                    # transforming R into a valid input of DivideAndConquer
                    if(any(el.valuation() < 0 for el in R)):
                        raise ValueError("We got an unexpected Laurent polynomial")
                    R = [vector(Kx(el)[i] for el in R) for i in range(n,m)]
                    y1 = DDFunction.__chyzak_dac(A, R, n, [vector(r*[0])], o, K, x)

                    self.__chyzak["last"] = (y0 + x**n*y1, m)
                else:
                    # we will need the initial conditions
                    v = Matrix([[init[i+j]/falling_factorial(j+i,i) for j in range(jp-r+1)] for i in range(r)]).columns()
                    self.__chyzak["last"] = (DDFunction.__chyzak_dac(A, (m)*[vector(K, r*[0])], 0, v, o, K, x), m)
                    
                y = self.__chyzak["last"][0][0] 
                
                for i in range(n,m):
                    self.__sequence[i] = y[i]
                self.__computed = m          
        else: ## Default case (use when the required element is below the bound)
            n  += 1 # element to be computed
           
            d = self.order()
            i = max(n-d,0)
            rec = self.equation.get_recursion_row(i)
            while(rec[n] == 0  and i <= self.equation.jp_value()):                   
                i += 1 
                rec = self.equation.get_recursion_row(i)
            if(rec[n] == 0 ):
                raise NoValueError(n)
            ## Checking that we only need previous elements
            for i in range(n+1 , len(rec)):
                if(not (rec[i] == 0 )):
                    raise NoValueError(n)
            
            ## We do this operation in a loop to avoid computing initial values 
            ## if they are not needed
            res = self.parent().coeff_field.zero()
            for i in range(n):
                if(not (rec[i] == 0 )):
                    res -= rec[i]*(self.sequence(i))
                    
            self.__sequence[n] = self.parent().coeff_field(res/rec[n])
            self.__computed += 1
        
        return self.__computed

    def init(self, n, list=False, incomplete=False):
        r'''
            Method to get the `n`-th initial value of the power series.

            A :class:`DDFunction` represents a formal power series in `\mathbb{K}[[x]]` 
            where `\mathbb{K}` is the field returned by ``self.parent().base_ring()``. 

            A formal power series is a formal sum of the form:

            .. MATH::

                f(x) = f_0 + f_1 x + \ldots + f_nx^n + \ldots = \sum_{n \geq 0} f_n x^n

            This method returns the `n`th coefficient of the power series (i.e., `f^{(n)}(0)`
            or, equivalently, `n!f_n`). This method also allows an optional parameter 
            (called ``list``) to return instead the first `n` initial values of the power series.

            INPUT:

            * ``n``: index for the coefficient of number of initial values to compute
            * ``list``: boolean flag. If ``True``, the method returns a list with the ``n``
              first initial values of the sequence. Otherwise, it returns the initial value
              `n!f_n`. By default, this argument is ``False``.
            * ``incomplete``: boolean flag. If ``False``, the method will raise an error when
              the coefficients can not be computed. Only valid in the case that ``list`` is 
              ``True``, the output (instead of an :class:`~ajpastor.dd_functions.exceptions.NoValueError`)
              will be the list up to the first element we could not compute.

            OUTPUT:

            If ``list`` is ``True``, this method returns the list `[f_0,\ldots,(n-1)!f_{n-1}]`. Otherwise,
            this method returns the element `n!f_n`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: DFinite(1/(1-x)).init(10, True)
                [1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880]
                sage: DFinite.element([-1,1],[1]).init(5)
                1
                sage: DFinite.element([1,0,1],[1,0]).init(4)
                1
                sage: DFinite.element([1,0,1],[1,0]).init(4, True)
                [1, 0, -1, 0]

            If the :class:`DDFunction` is not fully defined (i.e., not enough initial data is given)
            this method can also return (when returning lists) an incomplete list instead of an error::

                sage: DFinite.element([-1,1]).init(2)
                Traceback (most recent call last):
                ...
                NoValueError: Impossible to compute recursively the 0-th coefficient
                sage: DFinite.element([-1,1]).init(2, True)
                Traceback (most recent call last):
                ...
                NoValueError: Impossible to compute recursively the 0-th coefficient
                sage: DFinite.element([-1,1]).init(2, True, True)
                []
                sage: DFinite.element([-4, x]).init(4)
                Traceback (most recent call last):
                ...
                NoValueError: Impossible to compute recursively the 4-th coefficient
                sage: DFinite.element([-4, x]).init(10, True, True)
                [0, 0, 0, 0]
        '''
        if(list):
            if(incomplete):
                result = []
                for i in range(n):
                    try:
                        result += [self.init(i)]
                    except NoValueError:
                        break
                return result
            return [self.init(i) for i in range(n)]
        return self.sequence(n)*factorial(n)
        
    def truncation(self, bound):
        r'''
            Returns the truncation of this function up to the given order.

            Differentially definable functions are, in particular, formal power series. The truncation
            of a formal power series `f(x) = \sum_{n\geq 0} f_nx^n` up to an order `m \geq 0` is a 
            polynomial formed by the first coefficients of `f(x)`, namely:

            .. MATH
            
                \lceil f(x) \rceil^m = f_0 + f_1x + \ldots + f_{m-1}x^{m-1}

            This method computes the truncation for a given bound.

            INPUT:

            * ``bound``: value for the bound `m` of the truncation.

            OUTPUT:

            A polynomial of degree at most ``bound``.

            TODO: add examples
        '''
        if((not bound in ZZ) or (bound < 0)):
            raise ValueError("The bound for the truncation must b a non-negative integer")

        Px = PolynomialRing(self.parent().coeff_field, self.parent().variables()[0])
        return Px(self.sequence(bound, True))

    taylor = truncation #: alias of :func:`truncation`. This method returns the Taylor expansion

    @cached_method
    def size(self):
        r'''
            Method to get a number representing the size of this object

            We create a number that represents the size of the object by combining the size of 
            the coefficients  of the defining equation and the size of the initial values defining
            this object.

            This should be a reasonable representation on how much space on disk this objects takes.
        '''
        to_sum = [self.order()]
        if(isinstance(self.parent().base(), DDRing)):
            to_sum += [el.size() for el in self.equation.coefficients()]
        else:
            for coeff in self.equation.coefficients():
                try:
                    if(coeff != 0 ):
                        to_sum += [coeff.degree()+1]
                except AttributeError:
                    pass
        return sum(to_sum)
        
    @property
    def built(self):
        r'''
            Attribute determining how this object was built.

            We save in each :class:`DDFunction` the way it was constructed. Namely, if we know
            it was the addition or multiplication of two :class:`DDFunction`, we indicate it
            in this attribute. 

            This always have the following format: [type, data]. we distinguish between three 
            type of constructions:

            * ``derivative``: then ``self`` is the derivative of ``data[0]``.
            * ``polynomial``: then ``self`` is a polynomial evaluation. The polynomial can be
              found in ``data[0]`` and the relations between the variables and the actual values
              is found in a dictionary in ``data[1]``.
            * ``inverse``: then ``self`` is the multiplicative inverse of an element in 
              ``self.parent().to_depth(self.parent().depth()-1)`` (i.e., from an element 
              in the previous layer) that can be found in ``data[0]``.

            If this was not known, the attribute will take the (default) value ``None``.
        '''
        return self.__built
        
    @built.setter
    def built(self, input):
        r'''
            Documenting the setter
        '''
        type, data = input
        if(type == "derivative"):
            ## Nothing to check
            pass
        elif(type == "polynomial"):
            ## Check that the polynomial has appropriate variables
            polynomial, variables = data
            vars_in_pol = None
            if(polynomial.parent().is_field()):
                poly_ring = polynomial.parent().base()
                vars_in_pol = tuple(set(poly_ring(polynomial.numerator()).variables()).union(set(poly_ring(polynomial.denominator()).variables())))
            else:
                vars_in_pol = polynomial.variables()
                
            for var in vars_in_pol:
                if(not str(var) in variables):
                    raise TypeError("The variables in the polynomial does not appear in the given map.\n\t- Polynomial: %s\n\t- Map: %s" %(polynomial, variables))
        elif(type == "inverse"):
            ## Check that the other element is in the previous layer of depth
            if(is_DDFunction(data[0]) and not(data[0] in self.parent().to_depth(self.parent().depth()-1))):
                raise TypeError("The function must be an element of the previous layer in the hierarchy")
        else:
            raise ValueError("Built format not recognized.")
                            
        self.__built = tuple([type,data])

    @property 
    def name(self):
        r'''
            Attribute with the given name for ``self``.

            A :class:`DDFunction` is a formal power series that satisfies a linear differential
            equation. However, sometimes we would like to provide a name to refer to this function
            in a shorter way. This is only helpful for printing the object (see method :func:`DDFunction._repr_`)
            and for transforming these object to symbolic expressions.

            This attribute is extensively used in the module :mod:`~ajpastor.dd_functions.ddExamples`.

            WARNING:
            
            This attribute can only be set once. After that, trying to set a new name will raise a :class:`ValueError`.
        '''
        return self.__name

    @name.setter
    def name(self, new_name):
        if(not (isinstance(new_name, str) or isinstance(new_name, DynamicString))):
            raise TypeError("The name for this function must be a string or a DynamicString" %self.name)
        self.__name = new_name
        
    def has_name(self):
        r'''
            Checks whether ``self`` has a name or not.
        '''
        return not(self.name is None)
            
    @cached_method
    def noetherian_ring(self):
        r'''
            Method to compute a minimal noetherian ring containing ``self``.

            This method computes a minimal Noetherian differential ring in Sage that contains ``self``.
            These Noetherian rings are always of the form `R[\alpha_1,\ldots,\alpha_n]_S` where 
            `R` is a Noetherian ring, `\alpha_i` are variables with some meaning and `S` is a 
            multiplicatively closed set generated by a finite set of elements.

            Currently, this methods only works for D-finite functions (i.e., the depth of the 
            :class:`DDRing` is equal to 1).

            OUTPUT:

            The output have always 3 main entries:

            * The ring `R` that is the base of the Noetherian extension
            * The list of elements `\alpha_i` that will generate the final ring.
            * The list of generators of `S`.

            In the case of ``structure`` being ``True``, a fourth entry will be added
            with the ring `R[x_1,\ldots,x_n]_S` where the variable `x_i` represent the 
            element `\alpha_i`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = DFinite.element([-1,1],[1])
                sage: R,g,d = f.noetherian_ring()
                sage: R
                (SR)Univariate Polynomial Ring in x over Rational Field
                sage: len(g) == 1 and g[0] == f
                True
                sage: d
                []
                sage: f = DFinite.element([x^2, 3*x, 1-x],[1,1])
                sage: R,g,d = f.noetherian_ring()
                sage: R
                (SR)Univariate Polynomial Ring in x over Rational Field
                sage: len(g) == 2 and g == [f, f.derivative()]
                True
                sage: d
                [-x + 1]
        '''
        if(self.parent().depth() == 1):
            base, gens, dens = self.equation.noetherian_ring()

            d = self.order()
            gens += [self.derivative(times=i) for i in range(d)]

            return (base, gens, dens)

        raise NotImplementedError("Noetherian rings are not yet implemented")
    #####################################
    ### Arithmetic methods
    #####################################
    def scale_operator(self, r):
        r'''
            Method to scale by a constant the operator defining ``self``.

            This method returns a *new* :class:`DDFunction` that is equal to ``self``
            but hasthe differential operator multiplied by a scalar operator. Namely, 
            if `r` is the scalar factor, and ``self`` is defined with the 
            differential operator `\mathcal{A}`, then the output of this method
            has the operator `r\mathcal{A}` as a defining equation.

            If the ring of coefficients (see :func:`DDRing.base`) has a nice ``gcd``
            routine, this method does nothing.

            INPUT:

            * ``r``: the scalar factor to multiply the operator of ``self``.

            OUTPUT:

            A new :class:`DDFunction` that is equal to self after multiplying the 
            defining operator of ``self`` (see :func:`DDFunction.equation`) by `r`.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = DFinite.element([-1,1],[1])
                sage: print(f.scale_operator(x))
                (1:1:3)DD-Function in (DD-Ring over (Univariate Polynomial Ring in x over Rational Field)):
                -------------------------------------------------
                        -- Equation (self = f):
                                -     f  
                                +   D(f) 
                                = 0 
                        -- Initial values:
                        [1, 1]
                -------------------------------------------------
                sage: f.scale_operator(x-1).equation == f.equation
                True

            This behavior (of simplifying the operator by ``gcd``) does not happen any longer for 
            higher depths::

                sage: g = DDFinite.element([-f, 1],[1]) # exp(exp(x)-1)
                sage: h = g.scale_operator(x+1) 
                sage: h.equation == g.equation
                False
                sage: h == g
                True
                sage: all(h.equation[i] == (x+1)*g.equation[i] for i in range(g.order() + 1))
                True

            However, the ``gcd`` computation for DD-finite functions detects a common `x` factor
            that is, indeed, simplified in this method::

                sage: l = g.scale_operator(x*(x+1))
                sage: h.equation == l.equation
                True
                sage: l == g
                True
        '''
        r = self.parent().base()(r)
        
        return self.parent().element(r*self.equation, self.init(self.order(), True, True), check_init=False)
        
    def change_init_values(self,new_init,name=None):
        r'''
            Method to build new :class:`DDFunction` changing the initial values.

            This method allows the user to create a new :class:`DDFunction` from 
            ``self`` changing the initial values. Namely, we keep the operator
            defining ``self`` (see :func:`DDFunction.equation`) but changes the
            initial conditions to the given ones.

            INPUT:

            * ``new_init``: list or dictionary (see :class:`DDFunction`) for the 
              new initial values.
            * ``name``: optional argument for declaring the name of the new function.

            OUTPUT:

            A *new* :class:`DDFunction` that is annihilated by the same differential 
            operator as ``self`` but have the initial values provided by ``new_init``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = DFinite.element([1,0,1])
                sage: f.change_init_values([4,0]).init(4, True)
                [4, 0, -4, 0]
                sage: f.change_init_values([1]).init(5, True, True)
                [1]
                sage: f.change_init_values([4,0,2])
                Traceback (most recent call last):
                ...
                InitValueError: There is no such function satisfying ...

            If we provide the name, the new function's name is directly set::

                sage: f.change_init_values([1,0], name="sin(x)")
                sin(x)
        '''
        return self.parent().element(self.equation, new_init, name=name)
                
    @derived_property
    def inverse(self):
        '''
            Method that compute and return a DD-Function `f` such `f*self == 1`, i.e. this method computes the multiplicative inverse of `self`.
        '''
        if(self.init(0) == 0):
            raise ValueError("Can not invert a function with initial value 0 --> That is not a power series")
                
        ### Computing the new name
        newName = None
        if(not(self.__name is None)):
            newName = DynamicString("1/(_1)",self.__name)
        if(self.order() == 0 ):
            raise ZeroDivisionError("Impossible to invert the zero function")
        elif(self.order() == 1 ):
            coeffs = self.equation.coefficients()
            return self.parent().element([-coeffs[0],coeffs[1]], [1 /self.init(0 )], check_init=False, name=newName)
        else:
            newDDRing = DDRing(self.parent())
            inverse = newDDRing.element([self.derivative(), self], [1 /self.init(0 )], check_init=False, name=newName)
            inverse.built = ("inverse", [self])
            return inverse
    
    def add(self, other):
        '''
            Method that adds two DDFunctions.
            
            INPUT:
                - ``other``: a DDFunction which will be added to `self`.
                
            WARNING:
                - This method usually returns a new object different from `self` or `other`. But if one of the parameters is zero, then the output will be the other function, the SAME object.
                - Whenever an error occurs, a NotImplemented error will be returned in order to Python can make the correspondent call to _radd_ method of `other` if necessary.
        '''
        ### We check some simplifications: if one of the functions is zero, then we can return the other
        if(self.is_null):
            return other
        elif (other.is_null):
            return self
                        
        ### Computing the new name
        newName = None
        if(not(self.__name is None) and (not(other.__name is None))):
            if(other.__name[0] == '-'):
                newName = DynamicString("_1_2", [self.__name, other.__name])
            else:
                newName = DynamicString("_1+_2", [self.__name, other.__name])
                
        
        ## We check other simplifications: if the elements are constants
        if(self.is_constant() or other.is_constant()):
            result = None
            if(self.is_constant() and other.is_constant()):
                parent = self.parent()
                newOperator = [0 ,1]
                newInit = [self(0 )+other(0 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
            elif(other.is_constant()):
                parent = self.parent()
                newOperator = parent.element(self.equation, inhomogeneous=other(0 )*self.equation.coefficient(0 )).equation
                newInit = [self(0 )+other(0 )] + [self.init(i) for i in range(1 ,newOperator.get_jp_fo()+1 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,'x1')("x1+%s" %other(0 )), {'x1':self}))
            elif(self.is_constant()):
                parent = other.parent()
                newOperator = parent.element(other.equation, inhomogeneous=self(0 )*other.equation.coefficient(0 )).equation
                newInit = [self(0 )+other(0 )] + [other.init(i) for i in range(1 ,newOperator.get_jp_fo()+1 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,'x1')("x1+%s" %self(0 )), {'x1':other}))
            return result
        
        ## We build the new operator
        if(self.equation == other.equation):
            newOperator = self.equation
        else:
            newOperator = self.equation.add_solution(other.equation)
            
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 
        
        ### Getting as many initial values as possible until the new order
        op1Init = self.init(needed_initial, True, True)
        op2Init = other.init(needed_initial, True, True)
        newInit = [op1Init[i] + op2Init[i] for i in range(min(len(op1Init),len(op2Init)))]
                   
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName)
        result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,['x1','x2'])('x1+x2'), {'x1':self, 'x2': other}))
        return result
    
    def sub(self, other):
        '''
            Method that substract two DDFunctions.
            
            INPUT:
                - ``other``: a DDFunction which will be substracted to `self`.
                
            WARNING:
                - Whenever an error occurs, a NotImplemented error will be returned in order to Python can make the correspondent call to _rsub_ method of `other` if necessary.
        '''
        if(self.is_null):
            return -other
        elif (other.is_null):
            return self
            
            
        ### Computing the new name
        newName = None
        if(not(self.__name is None) and (not(other.__name is None))):
            newName = DynamicString("_1-_2", [self.__name, other.__name])
        
        ## We check other simplifications: if the elements are constants
        if(self.is_constant() or other.is_constant()):
            result = None
            if(self.is_constant() and other.is_constant()):
                parent = self.parent()
                newOperator = [0 ,1]
                newInit = [self(0 )-other(0 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
            elif(other.is_constant()):
                parent = self.parent()
                newOperator = parent.element(self.equation, inhomogeneous=other(0 )*self.equation.coefficient(0 )).equation
                newInit = [self(0 )-other(0 )] + [self.init(i) for i in range(1 ,newOperator.get_jp_fo()+1 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,'x1')("x1-%s" %other(0 )), {'x1':self}))
            elif(self.is_constant()):
                parent = other.parent()
                newOperator = parent.element(other.equation, inhomogeneous=self(0 )*other.equation.coefficient(0 )).equation
                newInit = [self(0 )-other(0 )] + [-other.init(i) for i in range(1 ,newOperator.get_jp_fo()+1 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,'x1')("-x1+%s" %self(0 )), {'x1':other}))
            return result
           
        ## We build the new operator
        if(self.equation == other.equation):
            newOperator = self.equation
        else:
            newOperator = self.equation.add_solution(other.equation)
            
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 
        
        ### Getting as many initial values as possible until the new order
        op1Init = self.init(needed_initial, True, True)
        op2Init = other.init(needed_initial, True, True)
        newInit = [op1Init[i] - op2Init[i] for i in range(min(len(op1Init),len(op2Init)))]
                           
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName)
        result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,['x1','x2'])('x1-x2'), {'x1':self, 'x2': other}))
        return result
    
    def mult(self, other):
        '''
            Method that calculate the product of two DDFunctions.
            
            INPUT:
                - ``other``: a DDFunction which will be multiplied to `self`.
                
            WARNING:
                - This method always returns a new object different from `self` or `other`.
                - Whenever an error occurs, a NotImplemented error will be returned in order to Python can make the correspondent call to _rmult_ method of `other` if necessary.
        '''
        ### We check some simplifications: if one of the functions is zero, then we can return directly 0
        if ((other.is_null) or (self.is_null)):
            return 0 
        if(self.is_one):
            return other
        elif(other.is_one):
            return self
        elif(self.is_constant() and other.is_constant()):
            return self.init(0 )*other.init(0 )
        elif(self.is_constant()):
            return other.scalar(self.init(0 ))
        elif(other.is_constant()):
            return self.scalar(other.init(0 ))
            
        ### We build the new operator
        newOperator = self.equation.mult_solution(other.equation)
        
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 
               
        ### Getting as many initial values as possible until the new order
        op1Init = self.init(needed_initial, True, True)
        op2Init = other.init(needed_initial, True, True)
        newInit = [sum([binomial(i,j)*op1Init[j] * op2Init[i-j] for j in range(i+1 )]) for i in range(min(len(op1Init),len(op2Init)))]
        
        ### Computing the new name
        newName = None
        if(not(self.__name is None) and (not(other.__name is None))):
            newName = DynamicString("(_1)*(_2)", [self.__name, other.__name])
            
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName)
        result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,['x1','x2'])('x1*x2'), {'x1':self, 'x2': other}))
        return result
    
    def scalar(self, r):
        r'''
            This method returns the original function multiplied by a constant, i.e. `D(k) = 0`. 
            
            INPUT:
                - ``k``: scalar from the coefficient ring of `self`. It MUST be a constant.
                
            OUTPUT:
                This method will raise TypeError if the value is not a constant. In order to do so,
                this method will cast the argument into the coefficient ring and try to derivate it. 
                Just if the result is zero, the method will return a new DDFunction representing the function `k\cdot(self)`.
                
            INFO:
                - This method must return always true for the following statements:
                    - ``self.scalar(k) == self.mult(DDFunction.getConstantFunction(k))``.
        '''
        ### We first check if the scalar is zero, because the return is direct.
        if(r == 0 ):
            return self.parent().zero()

        ### Otherwise, we check that the element is a constant or not because the algorithm is 
        ### much easier
        r = self.parent().base()(r)
        if(self.parent().base_derivation(r) == 0 ):
            if(r == 1 ):
                return self
            n = self.equation.get_jp_fo()+1 
            init = self.init(n, True, True)
            
            if(isinstance(r, DDFunction)):
                r = r.init(0 )
            
            ### Computing the new name
            newName = None
            if(not(self.__name is None)):
                if(r == -1 ):
                    newName = DynamicString("-(_1)" ,self.__name)
                else:
                    newName = DynamicString("(_1)*(_2)", [repr(r), self.__name])
                   
            result = self.parent().element(self.equation, [r*el for el in init], check_init=False, name=newName)
            result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,['x1'])('(%s)*x1' %repr(r)), {'x1':self}))
            return result
        else:
            return self.mult(self.parent()(r))
    
    @derived_property        
    def zero_extraction(self):
        if(self == self.parent().zero()):
            return (0 ,self)
        else:
            n = 0 
            while(self.init(n) == 0 ):
                n = n+1 
                
            X = self.parent().variables()[0]
            if(n == 0 ):
                return (0 ,self)
            else:
                d = self.order()
                coeffs = self.equation.coefficients()
                newEquation = self.parent().element([sum([coeffs[j+l]*(binomial(j+l, j)*falling_factorial(n,l)*X**(n-l)) for l in range(min(n,d-j)+1 )]) for j in range(d+1 )], check_init = False).equation
            newInit = [factorial(i)*self.sequence(i+n) for i in range(newEquation.get_jp_fo()+1 )]
            
            ### Computing the new name
            newName = None
            if(not(self.__name is None)):
                newName = DynamicString("(_1)/(_2^%d)" %n, [self.__name, repr(X)])
               
            result = self.parent().element(newEquation, newInit, check_init=False, name=newName)
            result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,[repr(X),'x1']).fraction_field()('x1/(%s^%d)' %(repr(X),n)), {repr(X):self.parent()(X),'x1':self}))
            return (n,result)
        
    def min_coefficient(self):
        '''
            Method that computes the first non-zero coefficient. IN case 'self' is zero, this method returns 0.
        '''
        if(self.is_null): return 0
        return self.sequence(self.ps_order)
    
    def contraction(self, level):
        '''
            Method that tries to compute the contraction of a sequence jumping through the elements 0 (mod level).
            
            This is equivalent to compose self(pow(x,1/level)) if 'self' only has non-zero element in the positions 0 (mod level).
        '''
        ## Computing the resulting differential equation
        raise NotImplementedError("Method not yet implemented: contraction")
        
    def divide(self, other):
        if(self.is_null):
            return self.parent().zero()
        if(other.is_constant()):
            return self.scalar(1 /other.init(0 ))
        if(self == other):
            return self.parent().one()
            
        s_ze = self.zero_extraction
        o_ze = other.zero_extraction
        
        if(s_ze[0] >= o_ze[0]):
            result = self.parent()(x)**(s_ze[0]-o_ze[0])*(s_ze[1]*o_ze[1].inverse)
            
            ### Computing the new name
            newName=None
            if(not(self.__name is None) and (not(other.__name is None))):
                newName = DynamicString("(_1)/(_2)", [self.__name, other.__name])
                
            result.__name = newName
            return result
        else:
            raise ValueError("Impossible perform a division if the x factor of the denominator (%d) is greater than in the numerator (%d)"%(o_ze[0],s_ze[0]))
            
    def gcd(self, other):
        if(other in self.parent()):
            other = self.parent()(other)
        elif(self in other.parent()):
            return other.gcd(self)
        
        if(self.is_null):
            return other
        elif(other.is_null):
            return self
        
        if(self == other):
            return self
            
        X = self.parent().variables()[0]
        
        se = self.zero_extraction
        oe = other.zero_extraction
        
        return self.parent()(X**min(se[0],oe[0])*gcd(se[1].init(0 ),oe[1].init(0 )))
    
    #####################################
    ###
    ### Simple computations
    ###
    #####################################
    def simple_add(self, other):
        r'''
            Method to compute the simple addition of two DDFunctions.

            This method computes the addition of two DDFunctions that are represented with an 
            annihilating differential equation and some initial values. These defining equations
            have a particular set of singularities. This method guarantees that the annihilator
            returned have the same apparent singularities as the two operands.

            Currently, this method only works with D-finite functions.

            INPUT:
                * ``other``: the other :class:`DDFunction` that will be added to ``self``.

            OUTPUT:
            
            A new :class:`DDFunction` representing the addition of ``self`` and ``other`` such that
            the defining equation has the same singularities as ``self`` and ``other``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = AiryD(); g = Sin(x)
                sage: h = f.simple_add(g)
                sage: # h.singularities()
                sage: h.equation[h.order()] in h.parent().coeff_field
                True

            TODO:
                * Improve the tests
        '''
        ### We check some simplifications: if one of the functions is zero, then we can return the other
        if(self.is_null):
            return other
        elif(other.is_null):
            return self

        if(self.parent().depth() > 1):
            raise NotImplementedError("This method is not implemented")
        
        ### Computing the new name
        newName = None
        if(not(self.__name is None) and (not(other.__name is None))):
            if(other.__name[0] == '-'):
                newName = DynamicString("_1_2", [self.__name, other.__name])
            else:
                newName = DynamicString("_1+_2", [self.__name, other.__name])

        newOperator = self.equation.simple_add_solution(other.equation)
        needed_initial = newOperator.get_jp_fo()+1
        
        ### Getting as many initial values as possible until the new order
        op1Init = self.init(needed_initial, True, True)
        op2Init = other.init(needed_initial, True, True)
        newInit = [op1Init[i] + op2Init[i] for i in range(min(len(op1Init),len(op2Init)))]

        result = self.parent().element(newOperator, newInit, check_init=False, name=newName)
        result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,['x1','x2'])('x1+x2'), {'x1':self, 'x2': other}))

        return result

    def simple_mult(self, other):
        r'''
            Method to compute the simple product of two DDFunctions.

            This method computes the product of two DDFunctions that are represented with an 
            annihilating differential equation and some initial values. These defining equations
            have a particular set of singularities. This method guarantees that the annihilator
            returned have the same apparent singularities as the two operands.

            Currently, this method only works with D-finite functions.

            INPUT:
                * ``other``: the other :class:`DDFunction` that will be multiplied to ``self``.

            OUTPUT:
            
            A new :class:`DDFunction` representing the product of ``self`` and ``other`` such that
            the defining equation has the same singularities as ``self`` and ``other``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = AiryD(); g = Sin(x)
                sage: h = f.simple_mult(g)
                sage: # h.singularities()
                sage: h.equation[h.order()] in h.parent().coeff_field
                True

            TODO:
                * Improve the tests
        '''
        ### We check some simplifications: if one of the functions is zero, then we can return directly 0
        if ((other.is_null) or (self.is_null)):
            return 0 
        if(self.is_one):
            return other
        elif(other.is_one):
            return self
        elif(self.is_constant() and other.is_constant()):
            return self.init(0 )*other.init(0 )
        elif(self.is_constant()):
            return other.scalar(self.init(0 ))
        elif(other.is_constant()):
            return self.scalar(other.init(0 ))

        if(self.parent().depth() > 1):
            raise NotImplementedError("This method is not implemented")
            
        ### We build the new operator
        newOperator = self.equation.simple_mult_solution(other.equation)
        
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 
               
        ### Getting as many initial values as possible until the new order
        op1Init = self.init(needed_initial, True, True)
        op2Init = other.init(needed_initial, True, True)
        newInit = [sum([binomial(i,j)*op1Init[j] * op2Init[i-j] for j in range(i+1 )]) for i in range(min(len(op1Init),len(op2Init)))]
        
        ### Computing the new name
        newName = None
        if(not(self.__name is None) and (not(other.__name is None))):
            newName = DynamicString("(_1)*(_2)", [self.__name, other.__name])
            
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName)
        result.built = ("polynomial", (PolynomialRing(self.parent().coeff_field,['x1','x2'])('x1*x2'), {'x1':self, 'x2': other}))
        return result

    def simple_derivative(self):
        r'''
            Method to compute the simple derivative of a DDFunction.

            This method computes the derivative of a DDFunction that is represented with an 
            annihilating differential equation and some initial values. This defining equation
            have a particular set of singularities. This method guarantees that the annihilator
            returned have the same apparent singularities.

            Currently, this method only works with D-finite functions.

            OUTPUT:
            
            A new :class:`DDFunction` representing the derivative of ``self`` such that
            the defining equation has the same singularities as ``self``.

            EXAMPLES::

                sage: from ajpastor.dd_functions import *
                sage: f = AiryD()
                sage: h = f.simple_derivative()
                sage: h == f.derivative()
                True
                sage: h.equation[h.order()] in h.parent().coeff_field
                True
                sage: f = Exp(x)
                sage: h = f.simple_derivative()
                sage: h == f.derivative()
                True
                sage: h.equation[h.order()] in h.parent().coeff_field
                True
                sage: f = BesselD(2)
                sage: h = f.simple_derivative()
                sage: h == f.derivative()
                True
                sage: h.equation[h.order()]%h.parent().base()(x) == 0 and len(h.equation[h.order()].factor()) == 1
                True

            TODO:
                * Improve the tests
        '''
        if(self.parent().depth() > 1):
            raise NotImplementedError("This method is not implemented")

        if(self.__simple_derivative is None):
            if(self.is_constant()):
                ### Special case: is a constant
                self.__simple_derivative = self.parent()(0)
            else:
                ### We get the new operator
                newOperator = self.equation.simple_derivative_solution()
            
                ### We get the required initial values (depending of the order of the next derivative)
                initList = self.init(newOperator.get_jp_fo()+2, True, True)
                newInit = [initList[i+1] for i in range(min(len(initList)-1 ,newOperator.get_jp_fo()+1 ))]
                
                ### Computing the new name
                newName = None
                if(not(self.__name is None)):
                    if(self.__name[-1] == "'"):
                        newName = DynamicString("_1'", self.__name)
                    else:
                        newName = DynamicString("(_1)'", self.__name)
                
                ### We create the next derivative with the equation, initial values
                self.__simple_derivative = self.parent().element(newOperator, newInit, check_init=False, name=newName)
                self.__simple_derivative.built = ("derivative",tuple([self]))
                
            
        return self.__simple_derivative

    #####################################
    ### Sequence methods
    #####################################
    def split_sequence(self, parts=2):
        '''
            Method that returns a list of 'parts' elements such that the interlacing of their sequence
            is equal to the sequence of 'self'.
            
            INPUT:
                - parts: positive integer
                
            OUTPUT:
                - A list 'result' of 'parts' elements such that 
                    'result[0].interlace(result[1:]) == self'
                    
            ERRORS:
                - TypeError is raised if parts is not an integer
                - ValueError is raised if 'parts' is smaller or equal to zero.
        '''
        try:
            parts = ZZ(parts)
        except:
            raise TypeError("Argument 'parts' is not an integer (split_sequence)")
        
        if(parts <= 0):
            raise ValueError("Argument 'parts' is smaller than 1 (split_sequence)")
        
        if(parts == 1):
            return self
        elif(parts == 2):
            f = self
            f1 = (f + f(-x))/2
            f2 = ((f - f(-x))/2).zero_extraction[1]
            f = [f1,f2]
        else:
            raise NotImplementedError("Method 'split_sequence' not implemented for 3 or more parts")
            
        R = PolynomialRing(QQ[x], 'y')
        y = R.gens()[0]
        p = y^parts - x
            
        return [el.compose_algebraic(p, lambda n : el.sequence(parts*n)*factorial(n)) for el in f]
    
    def interlace(self, *others):
        '''
            Method that computes a functions which sequence is the interlacing between 'self'
            and all the 'others' functions.
            
            See method 'interlace_sequences' on class DDRing for further information.
        '''
        ## Checking the argument so 'others' is a list of elements
        if(len(others) == 1 and type(others[0]) == list):
            others = [others[0]]
            
        ## Computing the common parent for all elements
        po = self.parent()
        for el in others:
            po = pushout(po, el.parent())
            
        ## Calling the method in the DDRing level
        return po.interlace_sequences([self]+list(others))
    
    #####################################
    ### Differential methods
    #####################################
    def derivative(self, *args, **kwds):
        '''
        Method to get a DDFunction `g` that satisfies `D(self) = g`.
        
        INPUT:
            - ``args``: if it has length 1 and it is an integer, it will be considered
              as how many derivatives we want to computed. Otherwise, we ignore this
              arguments.
            - ''kwds'': if times is included, we compute the times-th derivative
        '''
        if(len(args) == 1 and args[0] in ZZ):
            times = args[0]
        else:
            times = kwds.get("times", 1)

        if(times in ZZ):
            if(times < 0):
                raise ValueError("Negative derivatives can not be computed")
            elif(times == 0):
                return self
            elif(times > 1):
                return self.derivative(times=times-1).derivative()
                
        if(self.__derivative is None):
            if(self.is_constant()):
                ### Special case: is a constant
                self.__derivative = self.parent()(0 )
            else:
                ### We get the new operator
                newOperator = self.equation.derivative_solution()
            
                ### We get the required initial values (depending of the order of the next derivative)
                initList = self.init(newOperator.get_jp_fo()+2, True, True)
                newInit = [initList[i+1] for i in range(min(len(initList)-1 ,newOperator.get_jp_fo()+1 ))]
                
                ### Computing the new name
                newName = None
                if(not(self.__name is None)):
                    if(self.__name[-1] == "'"):
                        newName = DynamicString("_1'", self.__name)
                    else:
                        newName = DynamicString("(_1)'", self.__name)
                
                ### We create the next derivative with the equation, initial values
                self.__derivative = self.parent().element(newOperator, newInit, check_init=False, name=newName)
                self.__derivative.built = ("derivative",tuple([self]))
                
            
        return self.__derivative
        
    def integrate(self, constant=0 ):
        '''
        Method to get a DDFunction `g` that satisfies `D(g) = self` and `g(0) = constant`.
        
        INPUT:
            - ``constant``: element which will define the initial value of the returned primitive.
        '''
        ### First we calculate the new linear differential operator
        newOperator = self.equation.integral_solution()
        
        ### We get the initial values for the integral just adding at the begining of the list the constant value
        # If not enough initial values can be given, we create the integral with so many initial values we have
        newInit = [self.parent().coeff_field(constant)] + self.init(newOperator.get_jp_fo()+1, True, True)
        
        ### Computing the new name
        newName = None
        if(not(self.__name is None)):
            if(constant == 0 ):
                newName = DynamicString("int(_1)", self.__name)
            else:
                newName = DynamicString("int(_1) + _2", [self.__name, repr(constant)])
        
        return self.parent().element(newOperator, newInit, check_init=False, name=newName)
        
    #####################################
    ### Compositional methods
    #####################################
    def compose(self, other):
        '''
            Method to compute the composition of 'self' with 'other' (if possible).
            
            The method first compute the new ring where the composition will belong and then relies on the method 'compose_solution' of the Operator class.
            
            Then, it computes the new initial values using the Faa di Bruno's formula.
            
            INPUT:
                - 'self': a DDFunction
                - 'other': an element of SAGE
            
            OUTPUT:
                - A new DDFunction 'f' in the corresponding ring such f == self(other)
                
            ERRORS:
                - ValueError: if other(0) != 0
                - TypeError: if we can not compute a destination ring
                - Any error from Operator.compose_solution
                
            WARNINGS:
                - If the depth of the resulting DDFunction is greater than 3, a warning will pop-up
        '''
        ######################################
        ## Initial checking and considerations
        ######################################
        ## Checking that the 'other' element is NOT in the Symbolic Ring
        if(other.parent() is SR):
            try:
                other = self.parent().original_ring()(str(other))
            except Exception as e:
                raise TypeError("Impossible to perform a composition with a symbolic element. Try to cast (%s) to some field, polynomial ring or some DDRing" %(other))
            
        ## If we have the basic function we return the same element
        ## Also, if self is a constant, the composition is again the constant
        self_var = self.parent().variables(True)[0]
        if(self_var == other or self.is_constant()):
            return self
            
        ## Checking that 'other' at zero is zero
        value = None
        try:
            value = other(**{str(self_var):0 })
        except Exception as e:
            warnings.warn("Be careful my friend!! Evaluation at zero were not possible!!\nElement %s" %other, DDFunctionWarning, stacklevel=2 )
            raise e
        if(value != 0 ):
            raise ZeroValueRequired(repr(other))
        
        ######################################
        ## Computing the destiny ring
        ######################################
        destiny_ring = None
        ## First, compute the pushout fo the parents
        sp = self.parent()
        op = other.parent()
        push = pushout(sp, op)
        
        ## Second, compute the final depth of the DDRing
        if(not isinstance(push, DDRing)):
            raise TypeError("A non DDRing obtained for the composition: that is impossible -- review method _pushout_ of DDRing class")
        if(isinstance(op, DDRing)):
            destiny_ring = push.to_depth(op.depth()+sp.depth())
        else:
            destiny_ring = push.to_depth(sp.depth())
            
        if(destiny_ring.depth() >= 3 ):
            warnings.warn("You are going too deep (depth=%d). The abyss of hell is closer than this function... This may not finish." %destiny_ring.depth(), TooDeepWarning, stacklevel=2 )
            
        ######################################
        ## Computing the new operator
        ######################################
        ## HERE IS THE MAIN RECURSION STEP
        equation = destiny_ring.element([coeff(**{str(self_var) : other}) for coeff in self.equation.coefficients()]).equation ## Equation with coefficients composed with 'other'
        g = destiny_ring.base()(other) ## Casting the element 'other' to the base ring
        
        new_equation = equation.compose_solution(g)
        
        ######################################
        ## Computing the new initial values
        ######################################
        required = new_equation.get_jp_fo()+1 
        ## Getting as many initial values as we can and need
        init_f = self.init(required, True, True)
        init_g = None
        try:
            init_g = g.init(required, True, True)
        except AttributeError:
            init_g = [0] + [factorial(n)*new_equation.base().sequence(g,n) for n in range(1 ,required)]
        ## Computing the new initial values
        new_init = [init_f[0]]+[sum([init_f[j]*bell_polynomial(i,j)(*init_g[1 :i-j+2]) for j in range(1 ,i+1 )]) for i in range(1 ,min(len(init_f), len(init_g), required))] ## See Faa di Bruno's formula
        
        
        ######################################
        ## Computing the new name
        ######################################
        new_name = None
        if(not(self.__name is None)):
            if(isinstance(other, DDFunction) and (not (other.__name is None))):
                new_name = m_dreplace(self.__name, {"x":other.__name}, True)
            elif(not isinstance(other, DDFunction)):
                new_name = m_dreplace(self.__name, {"x":repr(other)}, True)
        
        return destiny_ring.element(new_equation, new_init, name=new_name)
    
    def compose_algebraic(self, poly, init):
        '''
            Method to compute the composition of 'self' with an algebraic function over some DDRing
            
            The method first compute the new ring where the composition will belong and then relies on the method 'compose_algebraic_solution' of the Operator class.
            
            Then, it uses the initial values given by init.
            
            INPUT:
                - 'self': a DDFunction
                - 'poly': polynomial in variable 'y' with coefficient in some DDRing or QQ[x]
                - 'init': initial values. This can be given as a list or a method that receives integers and return a sequence
            
            OUTPUT:
                - A new DDFunction 'f' representing the composition of 'self' with an algebraic function.
                
            ERRORS:
                - ValueError: if other(0) != 0
                - TypeError: if we can not compute a destination ring
                - Any error from Operator.compose_algebraic_solution
                
            WARNINGS:
                - If the depth of the resulting DDFunction is greater than 3, a warning will be shown
        '''
        ### Checking the input
        ## Checking 'poly' is a polynomial
        if(not _is_polynomial(poly)):
            raise TypeError("'compose_algebraic': the input 'poly' is not a polynomial")
        
        ## Checking that 'y' is a variable
        gens = [v for v in poly.parent().gens()]
        if(all(str(v) != 'y' for v in gens)):
            raise TypeError("'compose_algebraic': the input poly has no variable 'y'")
        
        if(len(gens) == 1):
            R = poly.parent().base()
            if(is_DDRing(R)):
                raise NotImplementedError("'compose_algebraic': composition with algebraic over DDFunction not implemented")
            else:
                F = DFinite.base().fraction_field()
                Q = PolynomialRing(F, 'y')
                poly = Q(poly)
                destiny_ring = self.parent()
        elif(len(gens) > 1):
            # If multivariate, we only accept 2 variables
            if(len(gens) > 2):
                raise ValueError("'compose_algebraic': the input 'poly' can only be bivariate polynomials")
            R = poly.parent().base()
            if(is_DDRing(R)):
                raise NotImplementedError("'compose_algebraic': composition with algebraic over DDFunction not implemented")
            else:
                y = gens[([str(v) for v in gens]).index('y')]
                gens = [v for v in gens if v != y]
                
                F = PolynomialRing(R, gens).fraction_field()
                Q = PolynomialRing(F, 'y')
                poly = Q(poly)
                destiny_ring = self.parent()
            
        ## At this point, we have a polynomial in 'y' with coefficients either polynomial in 'x' or DDFunctions
        # F: field of fractions of the coefficients
        # Q = F[y]
        # poly in Q
        # destiny_ring: final DDRing where the result will belong
        
        raise NotImplementedError("\n\t- ".join(["Method 'compose_algebraic' is not yet implemented. Current variables", 
                                                "coefficients: %s" %F, 
                                                "minimal polynomial: %s" %poly, 
                                                "final ring: %s" %destiny_ring]))
            
    #####################################
    ### Property methods
    #####################################  
    @derived_property  
    def is_null(self): 
        '''
            Cached property to check whether self is zero in its ring or not.
            
            The method used is comparing the first initial values of the function and check they are zero. If some initial value can not be computed, then False is returned.
        '''
        return self.is_fully_defined and all(self.init(i) == 0  for i in range(self.equation.get_jp_fo()+1 ))
        
    @derived_property
    def is_one(self):
        '''
            Cached property to check whether self is one on its ring or not.
            
            The method used is checking that the element is a constant and its first initial value is one.
        '''
        return (self.is_constant() and self.init(0 ) == 1 )
        
    @cached_method
    def is_constant(self):
        '''
            Cached property to check whether self is a constant or not.
            
            We check enough initial values to know (without computing the derivative) if it is zero or not.
        '''
        ### OPTION 1
        ## Test zero and if not, check if a constant can be solution
        try:
            if(not self.is_null):
                return self.equation[0] == 0  and all(self.init(i) == 0  for i in range(1 , self.equation.get_jp_fo()+1 ))
            return True
        except TypeError:
            return False
        ### OPTION 2 (nor proved)
        ## Test only initial values for 'self'
        #try:
        #    return all(self.init(i) == 0 for i in range(1,self.equation.get_jp_fo()+3))
        #except TypeError:
        #    return False
        ### OPTION 3 (too costly)
        ## Test the derivative
        #return self.derivative() == 0
        ### OPTION 4 (too costly)
        ## Test the difference with the constant term
        #return (self - self(0)) == 0
    
    def is_inverse(self):
        r'''
            Method to check whether a :class:`DDFunction` is an inverse.

            This method checks if the funcion represented by ``self`` was built as the multiplicative
            inverse of another :class:`DDFunction`. See property :func:`inverse` and :func:`built`
            for further information.
        '''
        return (self.built != None and self.built[0] == "inverse")

    @derived_property
    def is_fully_defined(self):
        '''
            Cached property yo check whether the function is fully defined or not.
            
            This means that, given some initial values and the differential equation, the solution of such problem is unique (True) or not (False)
        '''
        max_init = self.equation.get_jp_fo()+1 
        return len(self.init(max_init, True, True)) == max_init
        
    @property
    def computed(self):
        r'''
            Mutable attribute that counts how many coefficients have been computed.
        '''
        return max([n for n in self.__sequence], default=-1)

    #####################################
    ### Equality methods
    #####################################  
    def equals(self,other): ### TO REVIEW
        '''
            Method that checks if two DDFunctions are equal (as power-series). In orther to do so, we substract one to the other and check if the result is zero.
            
            INPUT:
                - ``other``: a DDFunction that can be substracted of ``self``.
                
            OUTPUT:
                - True if the object ``other`` represents the same function as ``self``.
                - False otherwise.
        '''
        try:
            if(not isinstance(other, DDFunction)):
                other = self.parent()(other)
            
            ## Quick check of initial values
            if(not self.quick_equals(other)):
                return False
            
            ## Special case: trying equality with zero
            if(other.is_null):
                return self.is_null
            elif(self.is_null):
                return False
                
            ## Special case with constants
            if(other.is_constant()):
                return self.is_constant() and self(0 ) == other(0 )
            elif(self.is_constant()):
                return False
                
            if(not (self.is_fully_defined and other.is_fully_defined)):
                return (self.equation == other.equation) and (self.init(self.equation.get_jp_fo()+1, True,True) == other.init(other.equation.get_jp_fo()+1, True, True))
             
            ### THREE OPTIONS
            ## 1. Compare with the JP-Values of each function
            #m = self.equation.get_jp_fo()+other.equation.get_jp_fo()+1
            #if(not all(self.init(i) == other.init(i) for i in range(m))):
            #    return False
            
            ## 2. Substract and check zero equality
            return (self-other).is_null
            
            ## 3. Check adding orders and if they are equal, substract operators and check as many initial values as needed
            #m = self.order()+other.order()+1
            #if(not all(self.init(i) == other.init(i) for i in range(m))):
            #    return False
            #   
            #M = self.equation.add_solution(other.equation).get_jp_fo()+1
            #return all(self.init(i) == other.init(i) for i in range(m,M))
        except Exception:
            ### If an error occur, then other can not be substracted from self, so they can not be equals
            return False
         
    def quick_equals(self,other): ### TO REVIEW
        '''
            Method that checks if two DDFunctions are equal (as power-series). In orther to do so, we substract one to the other and check if the result is zero.
            
            INPUT:
                - ``other``: a DDFunction that can be substracted of ``self``.
                
            OUTPUT:
                - True if the object ``other`` could represent the same function as ``self``.
                - False if we are sure ``self`` is different from ``other``.
        '''
        try:
            if(not isinstance(other, DDFunction)):
                other = self.parent()(other)
                
            m = self.equation.get_jp_fo()+other.equation.get_jp_fo()+1 
            return self.init(m, True, True) == other.init(m, True, True)
        except Exception:
            return False

    #####################################
    ### Analytic methods
    #####################################   
    def numerical_solution(self, value, delta=1e-10, max_depth=100 ):
        try:
            ## We try to delegate the computation to the operator (in case of OreOperators)
            if(self.equation.coefficients()[-1](0 ) != 0 ):
                sol = self.equation.operator.numerical_solution(self.sequence(self.order(), True), [0 ,value],delta)
                return sol.center(), sol.diameter()
            else:
                return self.__basic_numerical_solution(value, delta, max_depth)
        except AttributeError:
            ## The operator has no numerical solution method (i.e. it is not an OreOperator
            ## We compute the basic numerical approximation
            return self.__basic_numerical_solution(value, delta, max_depth)          
            
    def __basic_numerical_solution(self, value, delta,max_depth):
        res = 0 
        to_mult = 1 
        to_sum = 0 
        step = 0 
        find = 0 
        while(find < 5  and step < max_depth):
            to_sum = self.sequence(step)*to_mult
            res += to_sum
            if(self.sequence(step) != 0  and abs(to_sum) < delta):
                find += 1 
            elif(self.sequence(step) != 0 ):
                find = 0 
            
            step += 1 
            to_mult *= value
        return float(res),float(abs(to_sum))
        
    def numeric_coefficient_comparison_asymptotics(self, other, max_depth=10000, step=100, verbose=False, comparison="quotient", sequence=False):
        r'''
            Method to compare the coefficient sequence of two power sequence. 

            This method compares two sequences via division or difference (see optional arguments) and 
            may provide empirical evidence of similarity in asymptotics between the sequences.

            INPUT:

            * ``other``: the sequence with ``self`` is compared. If it is not a :class:`DDFunction` it will be casted into one.
            * ``max_depth``: number of elements of the sequence to be compared. 
            * ``step``: step-jump between comparisons. As the sequences are created recursively, this avoids a recursion overflow in Python.
            * ``verbose``: if set to ``True``, the method will print the progress of the computation.
            * ``kwds``: there are several extra options:
                * ``comparison``: the comparison can be ``"quotient"`` (``self.sequence(n)/other.sequence(n)``) 
                  or ``"difference"`` (``self.sequence(n) - other.sequence(n)``).
                * ``sequence``: the answer will be a list of comparisons in all the elements $0 (mod step)$. If not given, the 
                  answer will be just the last comparison.

            OUTPUT:

            A value with the appropriate comparison between the ``max_depth`` element of the sequences from ``self`` and ``other``.

            WARNING:

            This method can be interrupted at any point with Ctr-C and the last reached point will be returned.
        '''
        ## Treating the arguments
        if(comparison == "quotient"):
            comp = lambda p,q : float(p/q)
        elif(comparison == "difference"):
            comp = lambda p,q : float(p-q)
        else:
            raise ValueError("Argument 'comparison' must be either \"quotient\" or \"difference\"")

        if(not is_DDFunction(other)):
            other = self.parent()(other)

        total = int(max_depth/step) + 1
        iteration = 0

        result = []

        if(verbose): printProgressBar(iteration, total)
        while(iteration*step < max_depth):
            try:
                next = iteration*step
                result += [comp(self.sequence(next), other.sequence(next))]
            except KeyboardInterrupt:
                if(verbose): print("")
                break
            iteration+=1
            if(verbose): printProgressBar(iteration, total, suffix="(%s) %s" %(next, result[-1]))

        ## Finished loop: returning
        # Checking if the last iteration was made
        if(iteration*step >= max_depth):
            try:
                result += [comp(self.sequence(max_depth), other.sequence(max_depth))]
                if(verbose): printProgressBar(total, total, suffix="(%s) %s" %(max_depth, result[-1]))
            except KeyboardInterrupt:
                if(verbose): print("")
                pass

        if(sequence):
            return result
        else:
            return result[-1]

    def zeros(self):
        r'''
            Method to compute the zeros of a DDFunction.

            Let `f(x) \in \mathbb{K}[[x]]` be the power series represented by ``self``.
            This method computes symbolically a set `Z(f)` such that for all `\alpha \in Z(f)`
            we are guaranteed that `f(\alpha) = 0`.

            Currently this method only works with polynomials (since locating the zeros of 
            *differentially definable functions* is an open problem) and with special cases
            where we added the set of zeros manually while creating the function.

            OUTPUT:

            A set `Z(f)` of type :class:`~ajpastor.misc.sets.EnumeratedSet`.

            TODO:
                * Add manually zeros in the module DDExamples
                * Add manually zeros in the multiplication computation
                * Test this method
        '''
        if(self.__zeros is None):
            if(self.is_constant()):
                self.__zeros = EmptySet()
            try:
                poly = self.is_polynomial()
                self.__zeros = FiniteEnumeratedSet([root[0][0] for root in poly.roots()])
            except DDFunctionError:
                raise NotImplementedError("This method is not implemented")
        return self.__zeros

    def singularities(self):
        r'''
            Method to compute the singularities of a DDFunction.

            Let `f(x) \in \mathbb{K}[[x]]` be the power series represented by ``self``.
            This method computes symbolically a set `P(f)` such that if `\alpha \in \mathbb{C}`
            is a singularity of `f(x)` then `\alpha \in P(f)`.

            It is known that if `f(x)` satisfies a linear differential equation of the shape

            .. MATH::

                c_0(x)f(x) + \ldots + c_d(x)f^{(d)}(x) = 0,

            then all the singularities of `f(x)` are contained in the set of singularities of 
            the coefficients `c_0(x),\ldots,c_d(x)` and in the zero set of the leading 
            coefficient `c_d(x)`. 

            Hence, the singularity set can be computed recursively using this method on all
            the coefficients of the equation and the method :func:`zeros` on the leading
            coefficient exclusively. In the particular case of D-finite functions (i.e., 
            the coefficients are polynomials) we perform special computations since they 
            have no singularities and the zeros can be explicitly computed.

            OUTPUT:

            A set `P(f)` of type :class:`~ajpastor.misc.sets.EnumeratedSet`.

            TODO:
                * Test this method
        '''
        if(self.__singularities is None):
            if(self.parent().depth() == 1): # D-finite case
                try: # Trying to use desingularize from ore_algebra on the D-finite case
                    eq = self.equation.operator.desingularize()
                    lc = eq[eq.order()]
                except AttributeError:
                    lc = self.equation[self.equation.order()]
                 
                # only the zeros of the leading coefficient
                self.__singularities = FiniteEnumeratedSet([root[0][0] for root in lc.roots()])
            else:
                d = self.order()
                s = self.equation[d].zeros()
                for i in range(d+1):
                    s = s.union(self.equation[i].singularities())
                self.__singularities = s
        return self.__singularities

    #####################################
    ### Symbolic methods
    #####################################    
    @cached_method
    def to_symbolic(self):
        evaluation = sage_eval(str(self.__name).replace("'", ".derivative()").replace("^", "**"), locals=globals())
        if(isinstance(evaluation, Expression)):
            evaluation = evaluation.simplify_full()
            
        return evaluation
    
    @cached_method
    def to_simpler(self):
        try:
            R = self.parent().base()
            if(self.is_constant()):
                return self.parent().coeff_field(self.init(0))
            elif(is_DDRing(R)):
                coeffs = [el.to_simpler() for el in self.equation.coefficients()]
                parents = [el.parent() for el in coeffs]
                final_base = reduce(lambda p,q : pushout(p,q), parents, parents[0])
                
                dR = None
                if(is_DDRing(final_base)):
                    dR = final_base.to_depth(final_base.depth()+1)
                    
                elif(not is_DDRing(final_base)):
                    params = [str(g) for g in final_base.gens()]
                    var = repr(self.parent().variables()[0])
                    
                    if(var in params):
                        params.remove(var)
                    hyper_base = DDRing(PolynomialRing(QQ,[var]))
                    if(len(params) > 0):
                        dR = ParametrizedDDRing(hyper_base, params)
                    else:
                        dR = hyper_base
                else:
                    raise TypeError("1:No optimization found in the simplification")
                
                return dR.element([dR.base()(el) for el in coeffs], self.init(self.equation.jp_value()+1, True, True), name=self.__name).to_simpler()
                        
            elif(is_PolynomialRing(R)):
                degs = [self[i].degree() - i for i in range(self.order()+1)]
                m = max(degs)
                maxs = [i for i in range(len(degs)) if degs[i] == m]
                
                if(len(maxs) <= 1):
                    raise ValueError("2:Function %s is not a polynomial" %repr(self))
                
                x = R.gens()[0]
                pol = sum(falling_factorial(x,i)*self[i].lc() for i in maxs)

                root = max(root[0] for root in pol.roots() if (root[0] in ZZ and root[0] > 0))
                pol = sum(x**i*self.sequence(i) for i in range(root+1))

                if(pol == self):
                    return pol
                raise ValueError("3:Function %s is not a polynomial" %repr(self))
        except Exception:
            pass
        return self
        
    def to_poly(self):
        raise NotImplementedError("This method is not implemented")
    #####################################
    ### Magic Python methods
    #####################################
    ### Magic arithmetic
    ## Special case for Symbolic Ring
    def __check_symbolic(self, other):
        try:
            if(other.parent() is SR):
                try:
                    return self.parent()(other)
                except:
                    return ParametrizedDDRing(self.parent(),other.variables())(other)
        except Exception:
            pass
        return other
    
    def __add__(self, other):
        return super(DDFunction,self).__add__(self.__check_symbolic(other))
        
    def __sub__(self, other):
        return super(DDFunction,self).__sub__(self.__check_symbolic(other))
        
    def __mul__(self, other):
        return super(DDFunction,self).__mul__(self.__check_symbolic(other))
        
    def __div__(self, other):
        return super(DDFunction,self).__div__(self.__check_symbolic(other))
        
    def __radd__(self, other):
        return super(DDFunction,self).__radd__(self.__check_symbolic(other))
        
    def __rsub__(self, other):
        return super(DDFunction,self).__rsub__(self.__check_symbolic(other))
        
    def __rmul__(self, other):
        return super(DDFunction,self).__rmul__(self.__check_symbolic(other))
        
    def __rdiv__(self, other):
        return super(DDFunction,self).__rdiv__(self.__check_symbolic(other))
        
    def __rpow__(self, other):
        try:
            print("__rpow__ was called")
            return self.parent().to_depth(1)(other)**self
        except:
            return NotImplemented
        
    def __iadd__(self, other):
        return super(DDFunction,self).__add__(self.__check_symbolic(other))
        
    def __isub__(self, other):
        return super(DDFunction,self).__sub__(self.__check_symbolic(other))
        
    def __imul__(self, other):
        return super(DDFunction,self).__mul__(self.__check_symbolic(other))
        
    def __idiv__(self, other):
        return super(DDFunction,self).__div__(self.__check_symbolic(other))
    
    
    ## Addition
    def _add_(self, other):
        try:
            return self.add(other)
        except Exception:
            return NotImplemented
            
    ## Substraction
    def _sub_(self, other):
        try:
            return self.sub(other)
        except Exception:
            return NotImplemented
            
    ## Multiplication
    def _mul_(self, other):
        try:
            if(not isinstance(other, DDFunction)):
                return self.scalar(other)
                
            return self.mult(other)
        except Exception:
            return NotImplemented
            
    def _div_(self, other):
        try:
            return self.divide(other)
        except ValueError:
            return NotImplemented
  
    # Integer powering
    def __pow__(self, other):
        '''
            Method to compute the power of a DDFunction to other object. The current implementation allow the user to compute the power to:
                - Integers
                - Rational numbers (to be done)
                - Elements in self.parent().coeff_field (to be done)
                - Other DDFunctions (with some conditions)
                
            The method works as follows:
                1 - Tries to compute integer or rational power.
                2 - If 'other' is neither in ZZ nor QQ, then try to cast 'other' to a DDFunction.
                3 - Check if self(0) != 0. If self(0) != 1, check log(self(0)) in self.parent().coeff_field and set f2 = self/self(0).
                4 - If other(0) != 0, compute g2 = other - other(0) and return self**other(0) * self**g2
                5 - If other(0) == 0, compute ((log(self(0)) + log(f2))other)', and return the function with initial value 1.
                
                
            The only case that is not included is when self(0) = 0 or self**other(0) is not implemented.
        '''
        if(other not in self.__pows):
            f = self 
            g = other
            f0 = f(x=0)

            if(f.is_null or other == 0):
                raise ValueError("Value 0**0 not well defined")
            if(f.is_null): # Trivial case when f == 0, then f**g = 0.
                self.__pows[other] = f
            elif(g == 0): # Second trivial case when f != 0 and g == 0. Then f**g = 1
                self.__pows[other] = f.parent().one()
            elif(other in ZZ): # Integer case: can always be computed
                other = int(other)
                if(other >= 0 ):
                    a = other >> 1 
                    b = a+(other&1 )
                    self.__pows[other] = self.__pow__(a)*self.__pow__(b)
                    newName = None
                    if(not(self.__name is None)):
                        newName = DynamicString("(_1)^%d" %(other), self.__name)
                    if(isinstance(self.__pows[other], DDFunction)):
                        self.__pows[other].__name = newName
                else:
                    try:
                        inverse = self.inverse
                    except Exception:
                        raise ZeroDivisionError("Impossible to compute the inverse")
                    return inverse**(-other)
            elif(g in f.parent().coeff_field): # Constant case: need extra condition (f(0) != 0 and f(0)**g is a valid element
                g = f.parent().coeff_field(g)
                if(f0 == 0):
                    raise NotImplementedError("The powers for elements with f(0) == 0 is not implemented")
                try:
                    h0 = f0**g
                    if(not h0 in f.parent().coeff_field):
                        raise ValueError("The initial value is not in the base field")
                except Exception as e:
                    raise ValueError("The power %s^%s could not be computed, hence the initial values can not be properly computed.\n\tReason: %s" %(f0,g,e))
                R = f.parent().to_depth(f.parent().depth()+1)
                name = None
                if(f.has_name()):
                    name = DynamicString("(_1)^(%s)" %g, [repr(f)])
                self.__pows[other] = R.element([-other*f.derivative(), f], [h0])
            else: # Generic case: need extra condition (f(0) != 0, log(f(0)) and f(0)**g(0) are valid elements)
                if(f0 == 0):
                    raise NotImplementedError("The powers for elements with f(0) == 0 is not implemented")
                lf0 = log(f0)
                if(log(f0) not in f.parent().coeff_field):
                    raise ValueError("Invalid value for log(f(0)). Need to be an element of %s, but got %s" %(f.parent().coeff_field, log(f0)))
                lf0 = f.parent().coeff_field(lf0)
                f = f/f0
                
                if(is_DDFunction(g) or g in self.parent()):
                    from ajpastor.dd_functions.ddExamples import Log
                    lf = Log(self)
                    
                    R = pushout(other.parent(), lf.parent())
                    g = R(other)
                    lf = R(lf)
                    R = R.to_depth(R.depth()+1)
                    
                    g0 = g(x=0)
                    if(g0 != 0):
                        self.__pows[other] = self**g0 * self**(g-g0)
                    else:
                        name = None
                        if(g.has_name() and f.has_name()):
                            name = DynamicString("(_1)^(_2)", [f.__name, g.__name])
                        
                        self.__pows[other] = R.element([-((lf + lf0)*g).derivative(),1],[1],name=name)
                else:
                    raise NotImplementedError("No path found for this __pow__ computation:\n\t- base: %s\n\t- expo: %s" %(repr(self),repr(other)))
                #    try:
                #        newDDRing = DDRing(self.parent())
                #        other = self.parent().base_ring()(other)
                #        self.__pows[other] = newDDRing.element([(-other)*f.derivative(),f], [el**other for el in f.init(1, True, True)], check_init=False)
                #        
                #        newName = None
                #        if(not(self.__name is None)):
                #            newName = DynamicString("(_1)^%s" %(other), self.__name)
                #        self.__pows[other].__name = newName
                #    except TypeError:
                #        raise TypeError("Impossible to compute (%s)^(%s) within the basic field %s" %(f.init(0 ), other, f.parent().base_ring()))
                #    except ValueError:
                #        raise NotImplementedError("Powering to an element of %s not implemented" %(other.parent()))
        return self.__pows[other]
           
    ### Magic equality
    def __eq__(self,other):
        if (other is self):
            return True
        if((other in ZZ) and other == 0):
            return self.is_null
        return self.equals(other)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __nonzero__(self):
        return not (self.is_null)    
    ### Magic use
    def __call__(self, X=None, **input):
        '''
            Method that return the value of the function in the point given. As the function as a power-series may not converge, this method only works if the argument is 0.
            Further implementation can be done for DDFunctions that we know about the convergence.
        '''
        if ((not(X is None)) and X == 0 ):
            return self.init(0 )
        
        return self.parent().eval(self, X, **input)
        
    ### Magic representation
    def __hash__(self):
        '''
            Hash method for DDFunctions.

            Since several representations may be equal, we use the initial conditions as a mark for the hash.
        '''
        return sum(hash(el) for el in self.init(20, True, True))

    def __getitem__(self, key):
        r'''
            GetItem method for DDFunctions. It allows the user do ``self[i]`` for `i \geq -1`.
            
            INPUT:
                - ``key``: an integer.
            
            RETURN:
                - The result is the coefficient of `D^{key}(f)` on the equation.
        '''
        return self.equation.coefficient(key)

    def __missing__(self, key):
        '''
            Missing method for DDFunctions.
        '''
        return 0 
        
    def __str__(self, detail=True):
        '''
            String method for DDFunctions. It prints all information of the DDFunction.
        '''
        #if(self.is_constant()):
        #    return (self.init(0)).__str__()
            
        if(detail and (not(self.__name is None))):
            res = "%s %s in %s:\n" %(self.__critical_numbers__(),repr(self),self.parent())
        else:
            res = "%s" %(repr(self))
            if(res[0] != '('):
                res += " in %s" %(self.parent())
            res += ":\n"
        res += '-------------------------------------------------\n\t'
        res += '-- Equation (self = f):\n'
        j = 0 
        while ((j < self.order()) and (self.equation.coefficient(j) == 0 )):
            j += 1 
        res += self.__get_line__(self.equation.coefficient(j), j, detail, True)
        for i in range(j+1 ,self.order()+1 ):
            if(self.equation.coefficient(i) != 0 ):
                res += '\n'
                res += self.__get_line__(self.equation.coefficient(i), i, detail)

        res += '\n\t\t = 0 \n\t'

        res += '-- Initial values:\n\t'
        res += format(self.init(self.equation.get_jp_fo()+1, True, True))
        
        res += '\n-------------------------------------------------'
        
        return res
        
    def __get_line__(self, element, der, detail, first = False):
        res = ""
        string = repr(element)
        crit = None
        
        ## Getting the basic elements for the line
        if(isinstance(element, DDFunction) and (not(element.__name is None))):
            crit = element.__critical_numbers__()
        else:
            ind = string.find(")")+1 
            crit = string[:ind]
            string = string[ind:]
            
        ## Printing critical numbers if detail is required
        if(detail and len(crit) > 0 ):
            res += crit + "\t"
            if(len(res.expandtabs()) < len("\t\t".expandtabs())):
                res += "\t"
        else:
            res += "\t\t"
        
        ## Adding the arithmetic symbol
        is_negative = (string[0] == '-' and ((string[1] == '(' and self.__matching_par__(string,1) == len(string)-1) or (string[1] != '(' and string.find(' ') == -1)))
        if(not(first) and (not is_negative)):
            res += '+ '
        elif(is_negative):
            res += '- '
            if(string[1] == '(' and self.__matching_par__(string,1) == len(string)-1):
                string = string[2 :-1]
            else:
                string = string[1 :]
        else:
            res += '  '
            
        ## Adding the function (with its derivative if needed)
        if(der > 1 ):
            res += "D^%d(f) " %der
        elif(der == 1 ):
            res += "  D(f) "
        else:
            res += "    f  "
        
        ## Adding the coefficient
        if(string != "1"):
            res += "* (%s)" %string
        
        return res
    
    def __matching_par__(self, string, par):
        if(string[par] != '('):
            return len(string)
        
        n = 1
        i = par+1
        while(i < len(string) and n > 0):
            if(string[i] == '('):
                n += 1
            elif(string[i] == ')'):
                n -= 1
            i += 1
        if(n > 0):
            return len(string)
        return i-1
        
    def __repr__(self):
        '''
            Representation method for DDFunctions. It prints basic information of the DDFunction.
        '''
        if(self.is_constant()):
            return str(self.init(0 ))
        if(self.__name is None):
            return "(%s:%s:%s)DD-Function in (%s)" %(self.order(),self.equation.get_jp_fo(),self.size(),self.parent()) 
        else:
            return str(self.__name)
            
    def __critical_numbers__(self):
        return "(%d:%d:%d)" %(self.order(),self.equation.get_jp_fo(),self.size())
    
    def _latex_(self, name="f"):
        ## Building all coefficients in the differential equation
        equ, simpl = self._latex_coeffs_(c_name=name)
        
        ## Building the starting part
        res = "\\left\\{\\begin{array}{c}\n"
        
        ## Building the differential equation
        res += "%s = 0,\\\\\n" %equ
        
        ## Adding the non-polynomial coefficients
        if(any(el != True for el in simpl)):
            res += "where\\\\\n"
            for i in range(len(simpl)):
                if(simpl[i] != True):
                    res += simpl[i] + ":" + self[i]._latex_(name=simpl[i]) + "\\\\\n"
        
        ## Adding the initial conditions
        res += "\\hdashline\n"
        res += self._latex_ic_(name=name)
        
        ## Closing the environment
        res += "\\end{array}\\right."
        
        return res
        
    def _latex_coeffs_(self, c_name="f"):
        next_name = chr(ord(c_name[0])+1)
        parent = self.parent()
        coeffs = [self[i] for i in range(self.order()+1)]
        simpl = [(not is_DDRing(parent.base()))]*(self.order()+1)
        sgn = ['+']*(self.order()+1)
        for i in range(len(coeffs)):
            ## Computing the sign and string for the coefficient
            current = coeffs[i]
            
            if(not simpl[i] and current.is_constant()): # Recursive and constant case
                current = current.init(0) # Reduced to constant case
                simpl[i] = True
            
            ## Constant cases
            if(current == -1):
                sgn[i] = "-"
                coeffs[i] = ""
            elif(current == 1):
                coeffs[i] = ""
            elif(simpl[i]==True and current < 0):
                sgn[i] = "-"
                coeffs[i] = latex(-current)
            elif(simpl[i] == True): # Non constant and simple case
                coeffs[i] = "\\left(" + latex(current) + "\\right)"
            else: # Recursive cases
                simpl[i] = "%s_{%d}" %(next_name, i)
                coeffs[i] = "%s(x)" %simpl[i]
            
            ## Computing the corresponding function factor
            if(i == 0):
                coeffs[i] += "%s(x)" %c_name
            elif(i == 1):
                coeffs[i] += "%s'(x)" %c_name
            elif(i == 2):
                coeffs[i] += "%s''(x)" %c_name
            else:
                coeffs[i] += "%s^{(%d)}(x)" %(c_name, i)
                
        ## Building the final line from the highest order to the minimal
        coeffs.reverse()
        sgn.reverse()
        
        final = ""
        for i in range(len(coeffs)):
            ## If it is a non-zero coefficient
            if(not self[len(coeffs)-i-1] == ZZ(0)):
                ## Adding the sign
                if(i > 0 or sgn[i] == '-'):
                    final += "%s " %sgn[i]
                ## Adding the value
                final += coeffs[i]
                
        return final, simpl
    
    def _latex_ic_(self, name="f"):
        res = []
        for i in range(self.equation.get_jp_fo()+1):
            if(i == 0):
                res += ["%s(0) = %s" %(name,latex(self.init(i)))]
            elif(i == 1):
                res += ["%s'(0) = %s" %(name,latex(self.init(i)))]
            elif(i == 2):
                res += ["%s''(0) = %s" %(name, latex(self.init(i)))]
            else:
                res += ["%s^{(%d)}(0) = %s" %(name, i,latex(self.init(i)))]
        return ", ".join(res)

    ## Overriding the serializable method with an extra parameter
    def serialize(self, file, full=False):
        ## If asked for the full information
        if(full):
            ## We put the current list as argument for the initial conditions
            max_index = max(el for el in self.__sequence)
            aux = self.skwds()["init_values"]
            self.skwds()["init_values"] = self.init(max_index+1,True)

        SerializableObject.serialize(self, file)

        ## Putting back the original argument (if needed)
        if(full):
            self.skwds()["init_values"] = aux

    def save_init(self, file, init=True, bin=True, bound=None):
        r'''
            Method to save only the initial conditions for this function. 
            
            This method stores in ``file`` the initial conditions or the sequence
            of ``self`` using the method dump from the package pickle.
            
            Once the values are save, they can be recovered using the method 
            ``load_init``.
            
            INPUT::
                * file: an opened file object or a string with the Path to the file.
                * init: indicates if saving the initial values (``True``) or the sequence. 
                * bin: a flag indicating if save the object in text mode or binary mode
                * bound: number of elements of the sequence to save.
        '''
        from pickle import dump as pdump
        
        is_str = isinstance(file,str)
        if(is_str and bin): file = open(file, "wb+")
        if(is_str and not bin): file = open(file, "w+")
        
        n = max(self.equation.get_jp_fo(),max(el for el in self.__sequence))
        if((not (bound is None)) and (bound in ZZ) and (bound > 0)):
            n = min(bound, n)
        
        if(init):
            pdump(self.init(n+1,True), file)
        else:
            pdump(self.sequence(n+1, True), file)
            
        if(is_str): file.close()

    def load_init(self, file, init=True, bin=True, check=True,bound=None):
        r'''
            Method to load the initial conditions for this function. 
            
            This method loads from ``file`` the initial conditions or the sequence
            of ``self`` using the method load from the package pickle.
            
            For a proper behavior of this function, only files created with 
            the method ``save_init`` should be used.
            
            INPUT:

            * ``file``: an opened file object or a string with the Path to the file.
            * ``init``: indicates if loading the initial values (``True``) or the sequence. 
            * ``bin``: a flag indicating if load the object in text mode or binary mode.
            * ``check``: a flag to check the data is valid for the equation.
            * ``bound``: number of elements of the sequence to load.
        '''
        from pickle import load as pload
        
        is_str = isinstance(file,str)
        if(is_str and bin): file = open(file, "rb+")
        if(is_str and not bin): file = open(file, "r+")

        data = pload(file)
        if(is_str): file.close()
        
        n = len(data)
        if((not (bound is None)) and (bound in ZZ) and (bound > 0)):
            n = min(n,bound)
        
        if(not init): # Converting the data into initial conditions
            init_data = [factorial(i)*data[i] for i in range(len(data))]
        else:
            init_data = [el for el in data]
            data = [init_data[i]/factorial(i) for i in range(len(init_data))]
        
        if(check):
            try:
                aux = self.change_init_values(init_data[:n])
                self.__sequence = aux.__sequence
            except ValueError:
                raise ValueError("Bad error conditions in %s for equation %s" %(file.name,self.equation))
        else:
            self.__sequence = {i : data[i] for i in range(n)}

    def _to_command_(self):
        if(self.__name is None):
            return "%s.element(%s,%s)" %(command(self.parent()), _command_list(self.equation.coefficients()), self.init(self.order(),True))
        else:
            return "%s.element(%s,%s,name='%s')" %(command(self.parent()), _command_list(self.equation.coefficients()), self.init(self.order(),True),str(self.__name))
        
#####################################################
### Construction Functor for DD-Ring
#####################################################
class DDRingFunctor (ConstructionFunctor):
    def __init__(self, depth, base_field):
        if(depth <= 0):
            raise ValueError("Depth can not be lower than 1 (DDRingFunctor)")
        if(not (base_field in _Fields)):
            raise TypeError("The base field must be a field (DDRingFunctor")

        self.rank = 11 
        self.__depth = depth
        self.__base_field = base_field
        super(DDRingFunctor, self).__init__(_IntegralDomains,_IntegralDomains)
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        #if(isinstance(x, DDRing)):
        #    return x.base()
        return x
        
    def _apply_functor(self, x):
        return DDRing(x,self.__depth,self.__base_field)
        
    def _repr_(self):
        return "DDRing(*,%d,%s)" %(self.__depth, self.__base_field)
        
    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return ((other.__depth == self.__depth) and (other.__base_field == self.__base_field))

    def merge(self, other):
        '''
            Merging two DDRingFunctors or return None.

            For merging two DDRingFunctors, we need to be able to compute a common base field from both functors
            and then go to the highest depth. It is interesting to remark that this is not the same as composing
            two of these functors.
        '''
        if(other.__class__ == self.__class__):
            return DDRingFunctor(max(self.depth(), other.depth()), pushout(self.__base_field, other.__base_field))

        return None
        
    def depth(self):
        return self.__depth

    def base_field(self):
        return self.__base_field
        
class ParametrizedDDRingFunctor (DDRingFunctor):
    def __init__(self, depth, base_field, var = set([])):
        self.rank = 12 
        self.__vars = var
        super(ParametrizedDDRingFunctor, self).__init__(depth, base_field)
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        return x
        
    def _repr_(self):
        return "ParametrizedDDRing(*,%d,%s,%s)" %(self.depth(), self.coeff_field(),self.__vars)
        
    def _apply_functor(self, x):
        return ParametrizedDDRing(DDRing(x, depth = self.depth(), base_field = self.coeff_field), self.__vars)
        
    def merge(self, other):
        '''
            Merging ``self`` with another DDRingFunctor or return None.

            This method is able to merge the functor with a DDRingFunctor in addition with the standard ParametrizedDDRingFunctor.
            The merging goes as follows: getting a common base field, computing the union of the (possibly empty) set of parameters
            and going to the biggest depth provided in the functors
        '''
        if(isinstance(other, DDRingFunctor)):
            depth = max(self.depth(), other.depth())
            vars = self.__vars
            base_field = pushout(self.coeff_field(), other.coeff_field())
            if(isinstance(other, ParametrizedDDRingFunctor)):
                vars = vars.union(other.__vars)

            return ParametrizedDDRingFunctor(depth, base_field, vars)
        return None
        
#####################################################
### General Morphism for return to basic rings
#####################################################
class DDSimpleMorphism (Morphism):
    def __init__(self, domain, codomain):
        super(DDSimpleMorphism, self).__init__(domain, codomain)
        
    def _call_(self, p):
        if(isinstance(self.codomain(), DDRing)):
            try:
                return self.codomain().element([self.codomain().base()(coeff) for coeff in p.equation.coefficients()], p.init(p.equation.get_jp_fo()+1, True, True))
            except:
                raise ValueError("Impossible the coercion of element \n%s\n into %s" %(p, self.codomain()))
        if(p.is_constant()):
            return self.codomain()(p.init(0 ))
        
        raise ValueError("Impossible perform this coercion: non-constant element")

        
        
#####################################       
### Changes to fit the SAGE Categories Framework
#####################################
DDRing.Element = DDFunction

#####################################
### Extra public methods
#####################################
def zero_extraction(el):
    try:
        R = el.parent()
        if(isinstance(R, DDRing)):
            return el.zero_extraction
        elif(x in R.gens()):
            n = 0 
            val = el(**{'x':0 })
            while(el != R.zero() and val == 0 ):
                n += 1 
                el = R(el/x)
                val = el(**{'x':0 })
                
            return (n, el)
    except AttributeError:
        return (0,el)

###################################################################################################
### PRIVATE MODULE METHODS
###################################################################################################
def _is_polynomial_ring(ring, univariate=True, multivariate=True):
    '''
        Method that checks whether an object is a polynomial ring or not.

        This method checks if an object is a polynomial ring.

        The method allows the user also to check if the object is univariate, multivariate or both
        with the optional arguments ''univariate'' and ''multivariate''. By default, the method
        checks for both types together.
    '''
    return (univariate and is_PolynomialRing(ring)) or (multivariate and is_MPolynomialRing(ring))

def _is_polynomial(element, univariate=True, multivariate=True):
    r'''
        Method that checks whether an object is a polynomial or not disregarding exceptions.

        This method checks if the parent of the element is a polynomial ring. If the object has
        no parent (i.e., a Python object), then the method returns ''False''.

        The method allows the user also to check if the object is univariate, multivariate or both
        with the optional arguments ''univariate'' and ''multivariate''. By default, the method
        checks for both types together.
    '''
    try:
        return _is_polynomial_ring(element.parent(), univariate, multivariate)
    except AttributeError:
        return False


def _indices(string, sep):
    try:
        index = string.index(sep)
        return [index] + [el+index+len(sep) for el in _indices(string[index+len(sep):],sep)]
    except ValueError:
        return []

def _m_indices(string, *seps):
    ## We assume no possible overlapping can occur between elements in seps
    all_index = []
    for sep in seps:
        all_index += [(el,sep) for el in _indices(string,sep)]
    all_index.sort()
    
    return all_index

def _m_replace(string, to_replace, escape=("(",")")):
    ## Checking if there are scape characters
    if(not escape is None):
        pos_init = string.find(escape[0])
        if(pos_init >= 0 ):
            ## Escape initial character found, skipping outside the escape
            pos_end = len(string)
            pos_end = string.rfind(escape[1])
            if(pos_end <= pos_init):
                pos_end = len(string)
                
            return string[:pos_init+1] + _m_replace(string[pos_init+1 :pos_end], to_replace, None) + string[pos_end:]
    
    ## No escape characters: doing normal computation
    all_index = _m_indices(string, *to_replace.keys())
    res = ""
    current_index = 0 
    for el in all_index:
        res += string[current_index:el[0]] + to_replace[el[1]]
        current_index = el[0]+len(el[1])
    res += string[current_index:]
    return res
    
###################################################################################################
### COMMAND CONVERSION OF DD_FUNCTIONS
###################################################################################################
def command(e):
    try:
        return e._to_command_()
    except AttributeError:
        from sage.rings.polynomial import polynomial_ring as Uni_Polynomial
        from sage.rings.number_field.number_field import is_NumberField
        from sage.rings.fraction_field import is_FractionField
        if(e in _IntegralDomains):
            if(e is QQ):
                return "QQ"
            if(Uni_Polynomial.is_PolynomialRing(e)):
                return "PolynomialRing(%s, %s)" %(command(e.base()), [str(var) for var in e.gens()])
            if(is_NumberField(e)):
                poly = e.defining_polynomial(); gen = e.gen()
                return "NumberField(%s('%s'), %s)" %(command(poly.parent()), poly, str(gen))
            if(is_FractionField(e)):
                return "FractionField(%s)" %command(e.base())
        return str(e)
        
def _command_list(elements):
    res = "["
    for i in range(len(elements)-1 ):
        res += command(elements[i]) + ", "
    if(len(elements) > 0 ):
        res += command(elements[-1])
    res += "]"
    
    return res
    
###################################################################################################
### STANDARD PACKAGES VARIABLES & GETTERS
###################################################################################################

# Some global pre-defined DD-Rings
DFinite = None
try:
    from ajpastor.operator.oreOperator import w_OreOperator
    DFinite = DDRing(PolynomialRing(QQ,x), default_operator=w_OreOperator)
except ImportError:
    ## No ore_algebra package found
    warnings.warn("Package ore_algebra was not found. It is highly recommended to get this package by M. Kauers and M. Mezzarobba (https://github.com/mkauers/ore_algebra)", NoOreAlgebraWarning)
    DFinite = DDRing(PolynomialRing(QQ,x))
DDFinite = DDRing(DFinite)
DFiniteP = ParametrizedDDRing(DFinite, [var('P')])
DFiniteI = DDRing(PolynomialRing(NumberField(x**2+1, 'I'), ['x']),base_field=NumberField(x**2+1, 'I'))

def __get_recurrence(f):
    if(not f in DFinite):
        raise TypeError("The function must be holonomic")
    
    f = DFinite(f)
    
    op = f.equation
    m = max([el.degree() for el in op.coefficients()])
    bound = op.order() + m
    
    num_of_bck = bound - op.order()
    m = None
    for i in range(num_of_bck, 0 , -1 ):
        if(op.backward(i) != 0 ):
            m = -i
            break
    
    if(m is None):
        for i in range(op.order()+1 ):
            if(op.forward(i) != 0 ):
                m = i
                break
    
    n = op._Operator__polynomialRing.gens()[0]
    
    rec = [op.get_recursion_polynomial(i)(n=n+m) for i in range(m,op.forward_order + 1 )]
    rec_gcd = gcd(rec)
    rec = [el/rec_gcd for el in rec]
    
    return (rec, f.sequence(op.forward_order-m, True))
DFinite._DDRing__get_recurrence = __get_recurrence

###################################################################################################
### PACKAGE ENVIRONMENT VARIABLES
###################################################################################################
__all__ = [
    "is_DDRing", 
    "is_ParametrizedDDRing", 
    "is_DDFunction", 
    "DDRing", 
    "DDFunction",
    "DFinite", 
    "DDFinite", 
    "command", 
    "zero_extraction", 
    "ParametrizedDDRing", 
    "DFiniteP", 
    "DFiniteI"]
  

