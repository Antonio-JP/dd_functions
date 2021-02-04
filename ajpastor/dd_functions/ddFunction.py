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
    sage: f.getInitialValueList(10) == [1]*10
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
from functools import reduce

#SAGE imports 
from sage.all import (IntegralDomain, IntegralDomainElement, IntegralDomains, Fields, derivative,
                        QQ, ZZ, SR, NumberField, PolynomialRing, factorial, latex, randint, var, Expression,
                        cached_method, Matrix, vector, gcd, binomial, falling_factorial, bell_polynomial, 
                        sage_eval, log, BackslashOperator)
from sage.all_cmdline import x
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing
from sage.categories.all import Morphism
from sage.categories.pushout import pushout
from sage.categories.pushout import ConstructionFunctor

#ajpastor imports
from ajpastor.dd_functions.exceptions import DDFunctionError

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

#####################################################
### Definition of some exceptions
#####################################################
# class DevelopementError(NotImplementedError):
#     def __init__(self, name):
#         NotImplementedError.__init__(self, "Method %s still under construction. Please be patient and wait until it is finished." %name)

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
        Method that checks if an object is a DDRing. 

        This method provides a general function to check the class of an object without knowing 
        exactly the name of the basic class of the module. This is basically an alias for the command 
        ''sinstance(ring, DDRing)''.

        INPUT:
            * ''ring'' -- object to be checked.

        OUTPUT: 
            * ''True'' or ''False'' depending if ''ring'' is a ''DDRing'' or not.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: is_DDRing(DFinite)
            True
            sage: is_DDRing(DDRing(QQ))
            True
            sage: is_DDRing(QQ)
            False

        Also ''ParametrizedDDRing'' return ''True'' with this method::

            sage: is_DDRing(ParametrizedDDRing(DFinite, ['a']))
            True

        SEE ALSO:
            * :class:'DDRing'
    '''
    return isinstance(ring, DDRing)

class DDRing (Ring_w_Sequence, IntegralDomain, SerializableObject):
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
        '''
            Method that checks if two NumberField extensions are equivalent in SAGE. 
            
            We say that R~S if they have the same polynomials defining their elements
            and they have exactly the same name.
            
            If R or S are not an algebraic extension then the method returns R==S
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
        '''
            Static method that retrieves the complete list of a Parent object until the method gens returns nothing or `1`.

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
        '''
            Particular builder for DDRings. 

            This method do a special checking of uniqueness for two DDRings. It maps all the arguments provided by the user
            and transform them into a standard notation that will be hashable and will allow the system to recognize two
            exact DDRings.
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
        '''
            Class for Differentially Definable Rings (or DDRing).

            This class represents the Ring of Differentially Definable Functions with coefficients over a base ring. This rings contains all the functions
            (formal power series) that satisfy a linear differential equation with coefficients in a base ring.

            INPUT::
                - ``base`` -- an integral domain. Will provide the coefficients for the differential equations.
                - ``depth`` -- positive integer. Points how many iterations of this construction we want.
                - ``base_field`` -- a field. The elements of ``self`` will be formal power series over this field.
                - ``invertibility`` -- method. This method checks if an element of ``base`` is invertible or not.
                - ``derivation`` -- method. This method computes the derivative of elements in ``base``.
                - ``default_operator`` -- class. Class inheriting from ``ajpastor.operator.Operator`` for the differential equations.

            More formally, ``(base,derivation)`` is a Differential Integral Domain and ``(self, self.derivative)`` a Differential Extension.

            Note that this objects are unique, so calling the constructor with the same arguments retrieve the same object.

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
        ## Other attributes initialization
        self.__variables = None
        SerializableObject.__init__(self, base, depth, base_field, invertibility, derivation, default_operator)

        if(depth > 1 ):
            DDRing.__init__(self,DDRing(base, depth-1 , base_field, invertibility, derivation, default_operator), 1 , base_field, invertibility, derivation, default_operator)
        else:
            ### We call the builders of the superclasses
            Ring_w_Sequence.__init__(self, base, method = lambda p,n : self(p).getSequenceElement(n))
            IntegralDomain.__init__(self, base, category=_IntegralDomains)
            
            ### We assign the operator class
            if(default_operator is None):
                ## In this case we add an default Operator
                if(isinstance(base, DDRing)):
                    self.default_operator = FullLazyOperator
                else:
                    self.default_operator = DirectStepOperator
            elif(issubclass(default_operator, Operator)):
                self.default_operator = default_operator
            else:
                raise TypeError("Invalid type for Operators in this ring. Must inherit from class Operator.")
            
            ### In order to get Initial Values, we keep the original field base 
            # If the base ring is already a DDRing, we take the correspond ring from base
            if isinstance(base, DDRing):
                self.base_field = base.base_field
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
                        self.base_field = current.fraction_field()
                    else:
                        self.base_field = current
                        
                        
                else:
                    self.base_field = base_field
                self.__depth = 1
                self.__original = base
            
            ### Saving the invertibility criteria
            if(invertibility is None):
                try:
                    self_var = self.variables(True,False)[0]
                    self.base_inversionCriteria = lambda p : p(**{self_var : 0 }) == 0
                except IndexError:
                    self.base_inversionCriteria = lambda p : self.base()(p)==0
            else:
                self.base_inversionCriteria = invertibility
            
            ### Saving the base derivation
            if(derivation is None):
                try:
                    self_var = self.variables(True,False)[0]
                    self.base_derivation = lambda p : p.derivative(self.base()(self_var))
                except IndexError:
                    self.base_derivation = lambda p : 0
            else:
                self.base_derivation = derivation
            
            ### Setting the default "get_recurrence" method
            # self.__get_recurrence = None
            
            
            ### Setting new conversions
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
            Method to get the coerce map from the SAGE structure `S` (if possible).
            
            To allow the algebraic numbers, we use the method ``__get_gens__`` to compare how the ring `S` and
            the ring ``self`` where built. If at some point we can not use the behavior of the generators, we 
            will rely on the usual ``_coerce_map_from_`` with ``self.base()``.
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
        '''
            This method compute the pushout of 'self' with the parent class 'S'. This method returns None if it is not possible to get the pushout or a DDRing with all the properties required to include 'self' and 'S'.
            
            The method goes as follows:
                1 - Compute the simplest field over everything is based (let us call it 'F'). This will be 'QQ' or an algebraic extension of 'QQ' (see the class 'NumberField')
                2 - Compute the list of parameters involved. This will be the constant transcendent elements that will extend the ring 'F' as a rational function ring. Let 'B' be such extension.
                3 - Compute the list of variables involved. We usually expect just one variable but allow to have more of them. We will build 'R' the polynomial ring over 'F' with those variables.
                4 - Compute the depth required for include 'self' and 'S'. Then we build the corresponding DDRing of the appropriate depth. If we had parameters, we build the ParametrizedDDRing.
                
            INPUT:
                - A parent structure of SAGE 'S'.
                
            OUTPUT:
                - A DDRing or ParametrizedDDRing such that any element of 'self' and 'S' is in it.
                
            WARNINGS:
                - A warning will pop up if we merge rings with the same parameter names.
                
            ERRORS:
                - TypeError will be raised if a problem with the algebraic extension is found.
                - 
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
        '''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))
        
    def _element_constructor_(self, *args, **kwds):
        '''
            Implementation of _element_constructor_.

            This method describes how to interpret the arguments that a DDRing can received to cast one element to a DDFunction in ``self``.
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
                    return self.element([coeff for coeff in X.equation.getCoefficients()], X.getInitialValueList(X.equation.get_jp_fo()+1 ), name=X._DDFunction__name)
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
            raise TypeError("Cannot cast an element to a DD-Function of (%s):\n\tElement: %s (%s)\n\tReason: %s" %(self, X, type(X), e))
            
    def gens(self):
        '''
            Implementation of the method ``gens``.

            This method returns a list with all the generators of the ``DDRing``. This usually means nothing, although some ``DDRing`` can 
            retrieve some special variables or its parameter as genertors.

            OUTPUT::
                List of generators provided by this ``DDRing``.

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
        '''
            Return the number of generators of ``self``.

            General method for Parent structures that returns the number of generators required to generate ``self``.

            OUTPUT::
                Number of generators obtained by ``self.gens()``.

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
        '''
            Returns a functor that built the DDRing.

            Method that returns a functor `F` and an Integral Domain `R` such that ``self == F(R)``. This method allows the 
            coerce system in Sage to handle ``DDFunctions`` and ``DDRings`` appropriately.

            OUTPUT::
                - A DDRingFunctor `F`
                - An Integral Domain `R`
            Such that ``F(R) == self``. Moreover, ``R in IntegralDomains()`` and ``isinstance(DDRingFunctor, F)`` are both True.

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

            The functor for Parametrized DDRings works a bit differently: it adds the parameters to the appropriate DDRing
                sage: S = ParametrizedDDRing(DDFinite, ['a','b'])
                sage: F, R = S.construction()
                sage: F == ParametrizedDDRingFunctor(2, QQ, set([var('a'), var('b')]))
                True
                sage: R == QQ[x]
                True
        '''
        return (DDRingFunctor(self.depth(), self.base_field), self.__original)
        
    def __contains__(self, X):
        '''
            Decide if an element belongs to ``self``.

            The method is implemented in a very generic way, looking if the parent of the input is related or has a coercion
            with ``self``. In addition, we try to call the method ``_element_constructor_`` of ``self`` to build an element from the input X,
            whatever it is.

            See ``self._element_constructor_?``, and ``self._has_coerce_map_from?`` for further information.

            OUTPUT::
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
            if((X.parent() is self) or (self._has_coerce_map_from(X.parent()))):
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
            Hash method for DDRings.

            The hash is a shifted by the depth of the hash for the original ring of coefficients.
        '''
        return hash(self.original_ring())+self.depth()

    def __eq__(self, other):
        '''
            Method to check equality of this Parent structure

            We consider that a Parent structure is equal to another if there are coercion maps from both structures.

            INPUT::
                * ``other`` -- a Sage object.

            OUTPUT::
                ``True`` if ``self`` and ``other`` are the same parent structure.

            TESTS::
                sage: from ajpastor.dd_functions import *
                sage: DFinite == DFinite # implicit test
                True
                sage: DDFinite == DDFinite # implicit test
                True
                sage: DFinite == DDFinite # implicit test
                False
        '''
        if(isinstance(other, DDRing)):
            return self._has_coerce_map_from(other) and other._has_coerce_map_from(self)
        return False
     
    ## Other magic methods   
    def _repr_(self):
        '''
            Method implementing the __repr__ magic python method. 

            Returns a string telling that self is a DDRing and which Ring is its base.
        '''
        return "DD-Ring over (%s)" %(self.base())

    def _latex_(self):
        '''
            Method creating the LaTeX representation for a DDRing.

            Returns a valid LaTeX string in math mode to print the DDRing in appropriate notation
        '''
        return "\\text{D}\\left(%s\\right)" %latex(self.base())
        
    def _to_command_(self):
        '''
            Return the Sage command to create again the same DDRing

            This method returns a string that can be directly executed in Sage (once loaded the package) that
            can recreate the object DDRing.

            This methos is called by the more general methos ``command`` provided by ``ajpastor.dd_functions``.
        '''
        return "DDRing(%s)" %command(self.base())
            
    #################################################
    ### Integral Domain and Ring methods
    #################################################
    def _an_element_(self):
        '''
            Create the element `1` for this ring.

            Method inherited from Ring SAGE class. It returns an example of object that is in the DDRing. It simply returns the 1 element.        

            OUTPUT::
                A DDFunction representing the element `1` in ``self``.
        '''
        return self.one()
    
    def random_element(self,**kwds):
        '''
            Method to compute a random element in this ring. 

            This method relies in a random generator of the self.base() ring and a generator of elements of the ring self.base_ring().
            This method accepts different named arguments:
                * "min_order" -- minimal order for the equation we would get (default to 1)
                * "max_order" -- maximal order for the equation we would get (default to 3)
                * "simple" -- if True, the leading coefficient will always be one (default True)
        '''
        ## Getting the arguments values
        min_order = kwds.get("min_order", 1)
        max_order = kwds.get("max_order", 3)
        simple = kwds.get("simple", True)

        ## Checking the argument values
        min_order = max(min_order,0) ## Need at least order 1
        max_order = max(min_order, max_order) ## At least the maximal order must be equal to the minimal
        if(simple != True and simple != False):
            simple = False

        ## Computing the list of coefficients
        R = self.base()
        S = self.base_field
        coeffs = [R.random_element() for i in range(randint(min_order,max_order)+1)]
        
        init_values = [0]
        while(init_values[0] == 0):
            init_values[0] = S.random_element()

        ## If we want simple elements, we can compute the initial values directly
        if(simple):
            coeffs[-1] = R.one()
            init_values += [S.random_element() for i in range(len(coeffs)-2)]
            return self.element(coeffs,init_values)
        ## Otherwise, we need to know the initial value condition
        warnings.warn("Not-simple random element not implemented. Returning zero", DDFunctionWarning, stacklevel=2)

        return self.zero()

    def characteristic(self):
        '''
            Method inherited from the Ring SAGE class. It returns the characteristic of the coefficient ring.
        '''
        return self.base().characteristic()
        
    def base_ring(self):
        '''
            Return the base field for the coefficients of the elements.

            This is a required method for extending rings. In this case, we return the same as ``self.base_field``.

            EXAMPLES::
                sage: from ajpastor.dd_functions import *
                sage: DFinite.base_ring() is DFinite.base_field
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
                sage: R.base_ring() is R.base_field
                True

            In the case of ParametrizedDDRing, the base field contains the parameters::
                sage: S = ParametrizedDDRing(DFinite, ['a','b'])
                sage: pars = S.parameters()
                sage: S.base_ring() == FractionField(PolynomialRing(QQ, pars))
                True
        '''
        return self.base_field
        
    def original_ring(self):
        '''
            Return the original ring from which we build the iterative DDRing.

            This method returns the original ring from which `self` can be constructed iteratively as a DDRing. 
            See ``self.depth?`` for further information.

            OUTPUT::
                A integral domain `R` such that ``DDRing(R, depth=self.depth())`` is ``self``.

            EXAMPLES::
                sage: from ajpastor.dd_functions import *
                sage: DFinite.original_ring() == QQ[x]
                True
                sage: DDFinite.original_ring() == QQ[x]
                True

            As usual, the ParametrizedDDRing will include the parameters in the base field::
                sage: R = ParametrizedDDRing(DDFinite, ['a','b'])
                sage: vars = R.parameters()
                sage: R.original_ring() == FractionField(PolynomialRing(QQ, vars))[x]
                True
        '''
        return self.__original
        
    def depth(self):
        '''
            Return the depth on iteration of the construction of ``self`` as a Differentially Definable Ring.

            The method returns the depth of ``self`` as a DDRing. This is measure on how many times we iterate the
            process of building a differentially definable ring from ``self.original_field()``. See
            ``self.original_ring?`` for further information.

            OUTPUT::
                A (strictly) positive integer `n` such that ``DDRing(self.original_ring(), n)`` is ``self``.

            EXAMPLES::
                sage: from ajpastor.dd_functions import *
                sage: DFinite.depth()
                1
                sage: DDFinite.depth()
                2

            The ParametrizedDDRing will share the depth of the rings from where they are built::
                sage: ParametrizedDDRing(DDFinite, ['a','b']).depth()
                2
                sage: ParametrizedDDRing(DDRing(QQ[x], depth=10), ['a','b']).depth()
                10
        '''
        return self.__depth
        
    def to_depth(self, dest):
        return DDRing(self.original_ring(), 
        depth = dest, 
        base_field = self.base_field, 
        invertibility = self.base_inversionCriteria, 
        derivation = self.base_derivation, 
        default_operator = self.default_operator)
    
    def extend_base_field(self, new_field):
        return DDRing(pushout(self.original_ring(), new_field), 
        depth = self.depth(), 
        base_field = pushout(self.base_field, new_field), 
        invertibility = self.base_inversionCriteria, 
        derivation = self.base_derivation, 
        default_operator = self.default_operator)
        
    def is_field(self, **kwds):
        '''
            Generic method for checking if ``self`` is a field.

            As we always work on the Formal Ring of power series on ``self.base_ring()``, this is never a field

            OUTPUT::
                False

            TESTS::
                sage: from ajpastor.dd_functions import *
                sage: all(F.is_field() is False for F in [DFinite, DDFinite])
                True
        '''
        return False
        
    def is_finite(self, **kwds):
        '''
            Generic method for checking if ``self`` is finite.

            As we always work on the Formal Ring of power series on ``self.base_ring()``, this is never finite

            OUTPUT::
                False

            TESTS::
                sage: from ajpastor.dd_functions import *
                sage: all(F.is_finite() is False for F in [DFinite, DDFinite])
                True
        '''
        return False
        
    def is_noetherian(self, **kwds):
        '''
            Generic method for checking if ``self`` is noetherian.

            As we always work on the Formal Ring of power series on ``self.base_ring()``, this is always noetherian.

            OUTPUT::
                True

            TESTS::
                sage: from ajpastor.dd_functions import DFinite, DDFinite
                sage: all(F.is_noetherian() is True for F in [DFinite, DDFinite])
                True
        '''
        return True

    #################################################
    ### DDRings methods
    #################################################
    def invertible(self,x):
        '''
            Method to make easier call the invertibility criteria specified when a DDRing was created.
            
            INPUT:
                - ``x``: an element of self.
            OUTPUT:
                - True if ``x`` is in self and it is a unit.
                - False otherwise.
        '''
        return self.base_inversionCriteria(x)
        
    def element(self,coefficients=[],init=[],inhomogeneous=0 , check_init=True, name=None):
        '''
            Method to create a DDFunction contained in self with some coefficients, inhomogeneous term and initial values. This method just call the builder of DDFunction just puting the base argument as self.
        '''
        return DDFunction(self,coefficients,init,inhomogeneous, check_init=check_init, name=name)
        
    def eval(self, element, X=None, **input):
        if not element in self:
            raise TypeError('The element we want to evaluate (%s) is not an element of this ring (%s)'%(element,self))
        element = self(element)
            
        rx = X
        self_var = str(self.variables(True)[0])
        if((rx is None) and (self_var in input)):
            rx = input.pop(self_var)
        if not (rx is None):
            if(rx == 0 ):
                return element.getInitialValue(0 )
            elif(rx in self.base_field):
                return element.numerical_solution(rx,**input)[0]
            try:
                return element.compose(rx)
            except ValueError:
                pass
        elif(len(input) == 0 ):
            return element
        
        raise NotImplementedError("Not implemented evaluation of an element of this ring (%s) with the parameters %s and %s" %(self,repr(rx),input))
        
    def interlace_sequence(self, *functions):
        '''
            Method that computes a function in 'self' which sequence is the interlacing of the sequences 
            given as input in 'functions'. These functions must be contained in 'self' or an error will be
            raised.
            
            INPUT:
                - functions: list of function in 'self' which we want to interlace
            
            OUTPUT:
                - DDFunction 'f' in 'self' such that for all n
                    f.getSequenceElement(n) == functions[n%len(functions)].getSequenceElement(n//len(functions))
                    
            ERRORS:
                - TypeError is raised if any of the functions can not be casted to 'self'
        '''
        if(len(functions) == 1 and type(functions[0]) == list):
            functions = functions[0]
        
        ## Getting the main variable for the functions
        x = self.variables()[-1]
        n = len(functions)
        
        ## Computing the dilated functions
        functions = [self(el)(x=x**n) for el in functions]
        
        ## Returning the resulting function
        return sum(x**i*functions[i] for i in range(n))
        
    #def get_recurrence(self, *args, **kwds):
    #    if(self.__get_recurrence is None):
    #        raise NotImplementedError("Recurrence method not implemented for %s" %self)  
    #    return self.__get_recurrence(*args, **kwds)
    
    def variables(self, as_symbolic=False, fill = True):
        if(self.__variables is None):
            self.__variables = []
            current = self.base()
            while(current != self.base_field):
                self.__variables += [var(str(el)) for el in current.gens()]
                current = current.base()
            self.__variables = tuple(set(self.__variables))
        
        if(as_symbolic):
            if(len(self.__variables) == 0  and fill):
                return tuple([var(DDRing._Default_variable)])
            return self.__variables
        else:
            if(len(self.__variables) == 0  and fill):
                return tuple([self.base()(var(DDRing._Default_variable))])
            return tuple(self.base()(el) for el in self.__variables)
                
#############################################################################
###
### Ring class for Parametrized DD Functions
###
#############################################################################
def is_ParametrizedDDRing(ring):
    return isinstance(ring, ParametrizedDDRing)

class ParametrizedDDRing(DDRing):

    @staticmethod
    def __classcall__(cls, *args, **kwds):
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
        base_field = base_ddRing.base_field
        constructions = [base_ddRing.construction()] # Here is the DD-Ring operator
            
        while(constructions[-1][1] != base_field):
            constructions += [constructions[-1][1].construction()]
             
        new_basic_field = PolynomialRing(base_field, parameters).fraction_field()
        current = new_basic_field
        for i in range(1 ,len(constructions)):
            current = constructions[-i][0](current)
            
        if(constructions[0][0].depth() > 1 ):
            base_ring = ParametrizedDDRing(DDRing(base_ddRing.original_ring(),depth=constructions[0][0].depth()-1 ), parameters)
            ring = DDRing.__classcall__(cls, base_ring, 1 , base_field = new_basic_field, default_operator = base_ddRing.default_operator)
            Ring_w_Sequence.__init__(ring, base_ring, method = lambda p,n : ring(p).getSequenceElement(n))
            IntegralDomain.__init__(ring, base_ring, category=_IntegralDomains)
        else:
            ring = DDRing.__classcall__(cls, current, depth = constructions[0][0].depth(), base_field = new_basic_field, default_operator = base_ddRing.default_operator)
            
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
        coer = super(ParametrizedDDRing, self)._coerce_map_from_(S)
        if(not(coer)):
            coer = self.__baseDDRing._coerce_map_from_(S)
            
        return not(not(coer))
            
    def construction(self):
        return (ParametrizedDDRingFunctor(self.depth(), self.__baseDDRing.base_field, set(self.__parameters)), self.__baseDDRing._DDRing__original)
            
    def base_ddRing(self):
        '''
            Method that retrieves the original DDRing where this parametrized space is based on.
            
            OUTPUT:
                - DDRing where elements of ``self`` would be if we substitute the parameters by elements of the base ring.
        '''
        return self.__baseDDRing
        
    def _repr_(self):
        res = "(%s" %str(self.parameters()[0])
        for i in range(1 ,len(self.parameters())):
            res += ", " + str(self.parameters()[i])
        res += ")"
        
        if(len(self.parameters()) > 1 ):
            return "%s with parameters %s" %(self.base_ddRing(),res)
        else:
            return "%s with parameter %s" %(self.base_ddRing(),res)
    
    def parameter(self,input):
        if(input in ZZ):
            return self.parameters()[ZZ(input)]
        elif(isinstance(input, str)):
            return self.parameters()[([str(v) for v in self.parameters()]).index(input)]
        else:
            raise NotImplementedError("No parameter can be got with input %s" %input)
    
    @cached_method
    def parameters(self, as_symbolic = False):
        if(as_symbolic):
            return self.__parameters
        else:
            return [self.base_field(el) for el in self.__parameters]
            
    def gens(self):
        return self.parameters(True)
        
    def _first_ngens(self, n):
        return self.parameters(False)[:n]
        
    def ngens(self):
        return len(self.parameters())
                        
    # Override to_depth method from DDRing
    def to_depth(self, dest):
        return ParametrizedDDRing(self.base_ddRing().to_depth(dest), self.parameters(True))
    
    # Override extend_base_field method from DDRing
    def extend_base_field(self, new_field):
        return ParametrizedDDRing(self.base_ddRing().extend_base_field(new_field), self.parameters(True))
            
    # Override eval method from DDRing
    def eval(self, element, X=None, **input):
        rx = X
        self_var = str(self.variables(True)[0])
        if(X is None and self_var in input):
            rx = input.pop(self_var)
        ### If X is not None, then we evaluate the variable of the ring
        if(not (rx is None)):
            if(len(input) > 0 ):
                return self.eval(element, **input)(**{self_var:rx})
            else:
                return super(ParametrizedDDRing, self).eval(element, rx)
        elif(len(input) > 0 ):
            ### Otherwise, we evaluate the parameters
            element = self(element)
            
            ### Getting the final parameters
            original_parameters = set(str(el) for el in self.parameters())
            used_parameters = set(input.keys())
            got_parameters = reduce(lambda p,q : p.union(q), [set(str(el) for el in SR(value).variables()) for value in input.values()])
            
            destiny_parameters = (original_parameters - used_parameters).union(got_parameters)
                        
            if(self_var in destiny_parameters):
                raise TypeError("Parameters can only be evaluated to constants.\n\t- Got: %s" %(input))
            
            if(len(destiny_parameters) == 0 ):
                destiny_ring = self.base_ddRing()
            else:
                destiny_ring = ParametrizedDDRing(self.base_ddRing(), tuple(destiny_parameters))
                
            new_equation = destiny_ring.element([el(**input) for el in element.equation.getCoefficients()]).equation
            
            new_init = [el(**input) for el in element.getInitialValueList(new_equation.get_jp_fo()+1 )]
            new_name = None
            if(element._DDFunction__name is not None):
                new_name = m_dreplace(element._DDFunction__name, {key: str(input[key]) for key in input}, True)
            return destiny_ring.element(new_equation,new_init,name=new_name)
        return element
            
        
#####################################################
### Class for DD-Functions
#####################################################
def is_DDFunction(func):
    return isinstance(func, DDFunction)

class DDFunction (IntegralDomainElement, SerializableObject):
    r'''
        Class for DDFunctions. Element class for DDRing.
    '''
    #####################################
    ### Init and Interface methods
    #####################################
    def __init__(self, parent, input = 0 , init_values = [], inhomogeneous = 0 , check_init = True, name = None):
        '''
            Method to initialize a DD-Function inside the DD-Ring given in 'parent'
            
            The object will represent a function 'f' such that
                - input (f) = inhomogeneous
                - f^{(i)}(0) = init_values[i]
        '''        
        # We check that the argument is a DDRing
        if(not isinstance(parent, DDRing)):
            raise TypeError("A DD-Function must be an element of a DD-Ring")
        ### We call superclass builder
        IntegralDomainElement.__init__(self, parent)

        ## Initializing the serializable structure
        if(isinstance(input, Operator)):
            sinput = input.getCoefficients()
        else:
            sinput = input
        SerializableObject.__init__(self, parent, sinput, init_values=init_values, inhomogeneous=inhomogeneous, name=name)
        
        ## Checking we have some input (if not, we assume the input for zero)
        ## We take care of the following arguments
        ##     input -> equation
        ##     init_values -> init
        ##     inhomogeneous -> inhom
        zero = False
        if((type(input) == list and len(input) == 0 ) or input == 0 ):
            zero = True
        elif(type(input) == list and all(el == 0  for el in input)):
            zero = True
        elif((type(input) == list and len(input) == 1 ) or (isinstance(input, Operator) and input.getOrder() == 0 )):
            zero = (inhomogeneous == 0 )
            
        if(zero):
            ### The equation is zero, we need inhomogeneous equals to zero
            if(not inhomogeneous == 0 ):
                raise ValueError("Incompatible equation (%s) and inhomogeneous term (%s)" %(input, inhomogeneous))
            else:
            ### Also, all the initial values must be zero
                for el in init_values:
                    if (not el == 0 ):
                        raise ValueError("Incompatible equation (%s) and initial values (%s)" %(input, init_values))
                init = [0]
                equation = [0 ,1]
                inhom = 0 
        else:
            equation = input
            init = [el for el in init_values]
            inhom = inhomogeneous
        
        ### Cached elements
        self.__pows = {0 :1 , 1 :self} # Powers-cache
        self.__derivative = None # The derivative of a function
        
        ### Assigning the differential operator
        ### We will save the leading coefficient of the equation (lc) to future uses.
        # We create the operator using the structure given by our DDRing
        try:
            self.equation = self.__buildOperator(equation)
        except Exception as e:
            raise TypeError("The input for this operator is not valid", e)
            
        ### Managing the inhomogeneous term
        # We cast the inhomogeneous term to an element of self.parent()
        # If that is not zero, then we compute the new operator and initial values needed
        # to define the equation.
        if(inhom != 0 ):
            ## Getting the basic elements
            inhom = self.parent()(inhom)
            field = parent.base_field
            
            ## Getting the homogeneous differential equation
            new_eq = inhom.equation*self.equation
            
            ## Get the number of elements to check
            ## If init is too big, we use all the elements for a better checking
            n_init = new_eq.get_jp_fo()+1 
            to_check = max(n_init, len(init))
            
            ## Getting the matrix of the current equation
            M = Matrix(field, self.equation.get_recursion_matrix(to_check-1 -self.equation.forward_order))
            v = vector(field, inhom.getSequenceList(M.nrows()))
            
            ## Solving the system MX = v
            X = M * BackslashOperator() * v
            ker = M.right_kernel_matrix()
            
            ## Choosing a solution such X[i]==init[i]
            diff = vector(field, [init[i]-X[i] for i in range(len(init))])
            N = Matrix(field, [[v[i] for i in range(len(init))] for v in ker]).transpose()

            try:
                to_sum = N * BackslashOperator() * diff
            except Exception:
                raise ValueError("There is no function satisfying\n(%s)(f) == %s\nwith initial values %s" %(self.equation,inhom,init))
            
            ## Putting the new values for the equation and initial values
            init = X+sum([to_sum[i]*ker[i] for i in range(len(to_sum))])
            init = [init[i]*factorial(i) for i in range(len(init))]
            self.equation = new_eq
            
        
        ## After creating the original operator, we check we can not extract an "x" factor
        coeff_gcd = 1 
        if(is_PolynomialRing(self.parent().base())):
            l = []
            for el in self.equation.getCoefficients():
                l += el.coefficients(x)
            
            coeff_gcd = gcd(l)
            if(coeff_gcd == 0 ):
                coeff_gcd = 1 
        g = coeff_gcd*gcd(self.equation.getCoefficients())
        if(g != 1  and g != 0 ):
            coeffs = [coeff/g for coeff in self.equation.getCoefficients()]
            self.equation = self.__buildOperator(coeffs)
                
        ### Managing the initial values
        init = [self.parent().base_field(str(el)) for el in init]
        if(check_init):
            self.__calculatedSequence = {}
            if(len(init) > self.equation.get_jp_fo()):
                initSequence = [init[i]/factorial(i) for i in range(len(init))]
                M = self.equation.get_recursion_matrix(len(initSequence)-self.equation.forward_order-1 )
                if(M*vector(initSequence) == 0 ):
                    for i in range(len(initSequence)):
                        self.__calculatedSequence[i] = initSequence[i]
                else:
                    raise ValueError("There is no such function satisfying %s with initial values %s"%(self.equation,init))
            else:
                for i in range(len(init)):
                    try:
                        get_init = self.getInitialValue(i)
                        if(not (get_init == init[i])):
                            raise ValueError("There is no such function satisfying %s with such initial values (index %d:%s)"%(self.equation,i,init[i]))
                    except TypeError:
                        self.__calculatedSequence[i] = init[i]/factorial(i)
        else:
            self.__calculatedSequence = {i:init[i]/factorial(i) for i in range(len(init))}
        
        
        ### Other attributes for DDFunctions
        self.__name = name
        self.__built = None
        self.__zeros = None
        self.__singularities = None
            
    def __buildOperator(self, coeffs):
        if(isinstance(coeffs, self.parent().default_operator)):
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
                
        return self.parent().default_operator(self.parent().base(), coeffs, self.parent().base_derivation)
        
    def getOperator(self):
        '''
            Getter method for the Linear Differential operator associated with the DDFunction.
        '''
        return self.equation
        
    def getOrder(self):
        '''
            Getter method for the order of the equation that defines the DDFunction.
        '''
        return self.equation.getOrder()
        
    @derived_property
    def ps_order(self):
        if(self.is_null):
            return -1 
        else:
            i = 0 
            while(self.getInitialValue(i) == 0 ):
                i += 1 
            
            return i
        
    def getSequenceElement(self, n):
        try:
            ## If we have computed it, we just return
            return self.__calculatedSequence[n]
        except KeyError:                
            ## Otherwise, we compute such element
            
            
            if(n > self.equation.get_jp_fo()):
                ## If the required value is "too far" we can get quickly the equation
                rec = self.equation.get_recursion_row(n-self.equation.forward_order)
            else:
                ## Otherwise, we try to get as usual the value
                d = self.getOrder()
                i = max(n-d,0 )
                rec = self.equation.get_recursion_row(i)
                while(rec[n] == 0  and i <= self.equation.jp_value()):                   
                    i += 1 
                    rec = self.equation.get_recursion_row(i)
                if(rec[n] == 0 ):
                    raise TypeError("Impossible to compute recursively the required value")
                ## Checking that we only need previous elements
                for i in range(n+1 , len(rec)):
                    if(not (rec[i] == 0 )):
                        raise TypeError("Impossible to compute recursively the required value")
            
            ## We do this operation in a loop to avoid computing initial values 
            ## if they are not needed
            res = self.parent().base_field.zero()
            for i in range(n):
                if(not (rec[i] == 0 )):
                    res -= rec[i]*(self.getSequenceElement(i))
                    
            self.__calculatedSequence[n] = self.parent().base_field(res/rec[n])
            
        return self.__calculatedSequence[n]
        
    def getSequenceList(self, n):
        '''
            Extra method that returns the list of the first `n` initial coefficients of the power-series expansion of the function. If it is not possible to get so many values, the method DO NOT return an error. It returns just a truncated list.
        '''
        ### We check the argument is correct
        if n < 0 :
            raise ValueError("The argument must be a non-negative integer")
        
        res = []
        for i in range(n):
            try:
                res += [self.getSequenceElement(i)]
            except TypeError:
                break
        return res
        
    def getInitialValue(self, n):
        '''
            Getter method for an initial value.
                - ``n``: order of the initial value expected to obtain, i.e. the return will be `D^n(f)(0)`.
                
            This method can raise an error if the initial value has not been provided and it is impossible to get it.
        '''
        return self.getSequenceElement(n)*factorial(n)
        
    def getInitialValueList(self, n):
        '''
            Extra method that returns the list of the first `n` initial values for the function. If it is not possible to get so many values, the method DO NOT return an error. It returns just a truncated list.
        '''
        ### We check the argument is correct
        if n < 0 :
            raise ValueError("The argument must be a non-negative integer")
        
        res = []
        for i in range(n):
            try:
                res += [self.getInitialValue(i)]
            except TypeError:
                break
        return res
        
    @cached_method
    def size(self):
        to_sum = [self.getOrder()]
        if(isinstance(self.parent().base(), DDRing)):
            to_sum += [el.size() for el in self.equation.getCoefficients()]
        else:
            for coeff in self.equation.getCoefficients():
                try:
                    if(coeff != 0 ):
                        to_sum += [coeff.degree()]
                except Exception:
                    pass
        return sum(to_sum)
        
    def built(self):
        return self.__built
        
    def change_built(self, type, data):
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
                            
        self.__built = tuple([type,data])
        
    def change_name(self, new_name):
        self.__name = new_name
        
    def has_name(self):
        return not(self.__name is None)
            
    #####################################
    ### Arithmetic methods
    #####################################
    def scale_operator(self, r):
        r = self.parent().base()(r)
        
        return self.parent().element(r*self.getOperator(), self.getInitialValueList(self.getOrder()), check_init=False)
        
    def change_init_values(self,newInit,name=None):
        newElement = self.parent().element(self.getOperator(), newInit,name=name)
        
        ## Returning the new created element
        return newElement
        
    @derived_property
    def inverse(self):
        '''
            Method that compute and return a DD-Function `f` such `f*self == 1`, i.e. this method computes the multiplicative inverse of `self`.
        '''
        if(self.getInitialValue(0 ) == 0 ):
            raise ValueError("Can not invert a function with initial value 0 --> That is not a power series")
        
        coeffs = self.getOperator().getCoefficients()
        
        ### Computing the new name
        newName = None
        if(not(self.__name is None)):
            newName = DynamicString("1/(_1)",self.__name)
        if(self.getOrder() == 0 ):
            raise ZeroDivisionError("Impossible to invert the zero function")
        elif(self.getOrder() == 1 ):
            return self.parent().element([-coeffs[0],coeffs[1]], [1 /self.getInitialValue(0 )], check_init=False, name=newName)
        else:
            newDDRing = DDRing(self.parent())
            return newDDRing.element([self.derivative(), self], [1 /self.getInitialValue(0 )], check_init=False, name=newName)
    
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
        if(self.is_constant or other.is_constant):
            result = None
            if(self.is_constant and other.is_constant):
                parent = self.parent()
                newOperator = [0 ,1]
                newInit = [self(0 )+other(0 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
            elif(other.is_constant):
                parent = self.parent()
                newOperator = parent.element(self.equation, inhomogeneous=other(0 )*self.equation.getCoefficient(0 )).equation
                newInit = [self(0 )+other(0 )] + [self.getInitialValue(i) for i in range(1 ,newOperator.get_jp_fo()+1 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.change_built("polynomial", (PolynomialRing(self.parent().base_field,'x1')("x1+%s" %other(0 )), {'x1':self}))
            elif(self.is_constant):
                parent = other.parent()
                newOperator = parent.element(other.equation, inhomogeneous=self(0 )*other.equation.getCoefficient(0 )).equation
                newInit = [self(0 )+other(0 )] + [other.getInitialValue(i) for i in range(1 ,newOperator.get_jp_fo()+1 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.change_built("polynomial", (PolynomialRing(self.parent().base_field,'x1')("x1+%s" %self(0 )), {'x1':other}))
            return result
        
        ## We build the new operator
        if(self.equation == other.equation):
            newOperator = self.equation
        else:
            newOperator = self.equation.add_solution(other.equation)
            
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 
        
        ### Getting as many initial values as possible until the new order
        op1Init = self.getInitialValueList(needed_initial)
        op2Init = other.getInitialValueList(needed_initial)
        newInit = [op1Init[i] + op2Init[i] for i in range(min(len(op1Init),len(op2Init)))]
                   
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName)
        result.change_built("polynomial", (PolynomialRing(self.parent().base_field,['x1','x2'])('x1+x2'), {'x1':self, 'x2': other}))
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
        if(self.is_constant or other.is_constant):
            result = None
            if(self.is_constant and other.is_constant):
                parent = self.parent()
                newOperator = [0 ,1]
                newInit = [self(0 )-other(0 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
            elif(other.is_constant):
                parent = self.parent()
                newOperator = parent.element(self.equation, inhomogeneous=other(0 )*self.equation.getCoefficient(0 )).equation
                newInit = [self(0 )-other(0 )] + [self.getInitialValue(i) for i in range(1 ,newOperator.get_jp_fo()+1 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.change_built("polynomial", (PolynomialRing(self.parent().base_field,'x1')("x1-%s" %other(0 )), {'x1':self}))
            elif(self.is_constant):
                parent = other.parent()
                newOperator = parent.element(other.equation, inhomogeneous=self(0 )*other.equation.getCoefficient(0 )).equation
                newInit = [self(0 )-other(0 )] + [-other.getInitialValue(i) for i in range(1 ,newOperator.get_jp_fo()+1 )]
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.change_built("polynomial", (PolynomialRing(self.parent().base_field,'x1')("-x1+%s" %self(0 )), {'x1':other}))
            return result
           
        ## We build the new operator
        if(self.equation == other.equation):
            newOperator = self.equation
        else:
            newOperator = self.equation.add_solution(other.equation)
            
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 
        
        ### Getting as many initial values as possible until the new order
        op1Init = self.getInitialValueList(needed_initial)
        op2Init = other.getInitialValueList(needed_initial)
        newInit = [op1Init[i] - op2Init[i] for i in range(min(len(op1Init),len(op2Init)))]
                           
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName)
        result.change_built("polynomial", (PolynomialRing(self.parent().base_field,['x1','x2'])('x1-x2'), {'x1':self, 'x2': other}))
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
        elif(self.is_constant and other.is_constant):
            return self.getInitialValue(0 )*other.getInitialValue(0 )
        elif(self.is_constant):
            return other.scalar(self.getInitialValue(0 ))
        elif(other.is_constant):
            return self.scalar(other.getInitialValue(0 ))
            
        ### We build the new operator
        newOperator = self.equation.mult_solution(other.equation)
        
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 
               
        ### Getting as many initial values as possible until the new order
        op1Init = self.getInitialValueList(needed_initial)
        op2Init = other.getInitialValueList(needed_initial)
        newInit = [sum([binomial(i,j)*op1Init[j] * op2Init[i-j] for j in range(i+1 )]) for i in range(min(len(op1Init),len(op2Init)))]
        
        ### Computing the new name
        newName = None
        if(not(self.__name is None) and (not(other.__name is None))):
            newName = DynamicString("(_1)*(_2)", [self.__name, other.__name])
            
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName)
        result.change_built("polynomial", (PolynomialRing(self.parent().base_field,['x1','x2'])('x1*x2'), {'x1':self, 'x2': other}))
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
            init = self.getInitialValueList(n)
            
            if(isinstance(r, DDFunction)):
                r = r.getInitialValue(0 )
            
            ### Computing the new name
            newName = None
            if(not(self.__name is None)):
                if(r == -1 ):
                    newName = DynamicString("-(_1)" ,self.__name)
                else:
                    newName = DynamicString("(_1)*(_2)", [repr(r), self.__name])
                   
            result = self.parent().element(self.equation, [r*el for el in init], check_init=False, name=newName)
            result.change_built("polynomial", (PolynomialRing(self.parent().base_field,['x1'])('(%s)*x1' %repr(r)), {'x1':self}))
            return result
        else:
            return self.mult(self.parent()(r))
    
    @derived_property        
    def zero_extraction(self):
        if(self == self.parent().zero()):
            return (0 ,self)
        else:
            n = 0 
            while(self.getInitialValue(n) == 0 ):
                n = n+1 
                
            X = self.parent().variables()[0]
            if(n == 0 ):
                return (0 ,self)
            else:
                d = self.getOrder()
                coeffs = self.getOperator().getCoefficients()
                newEquation = self.parent().element([sum([coeffs[j+l]*(binomial(j+l, j)*falling_factorial(n,l)*X**(n-l)) for l in range(min(n,d-j)+1 )]) for j in range(d+1 )], check_init = False).equation
            newInit = [factorial(i)*self.getSequenceElement(i+n) for i in range(newEquation.get_jp_fo()+1 )]
            
            ### Computing the new name
            newName = None
            if(not(self.__name is None)):
                newName = DynamicString("(_1)/(_2^%d)" %n, [self.__name, repr(X)])
               
            result = self.parent().element(newEquation, newInit, check_init=False, name=newName)
            result.change_built("polynomial", (PolynomialRing(self.parent().base_field,[repr(X),'x1']).fraction_field()('x1/(%s^%d)' %(repr(X),n)), {repr(X):self.parent()(X),'x1':self}))
            return (n,result)
        
    def min_coefficient(self):
        '''
            Method that computes the first non-zero coefficient. IN case 'self' is zero, this method returns 0.
        '''
        return self.zero_extraction[1](0)
    
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
        if(other.is_constant):
            return self.scalar(1 /other.getInitialValue(0 ))
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
        
        return self.parent()(X**min(se[0],oe[0])*gcd(se[1].getInitialValue(0 ),oe[1].getInitialValue(0 )))
    
    #####################################
    ###
    ### Simple computations
    ###
    #####################################
    def simple_add(self, other):
        raise NotImplementedError("This method is not implemented")

    def simple_mult(self, other):
        raise NotImplementedError("This method is not implemented")

    def simple_derivative(self):
        raise NotImplementedError("This method is not implemented")

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
            
        return [el.compose_algebraic(p, lambda n : el.getSequenceElement(parts*n)*factorial(n)) for el in f]
    
    def interlace(self, *others):
        '''
            Method that computes a functions which sequence is the interlacing between 'self'
            and all the 'others' functions.
            
            See method 'interlace_sequence' on class DDRing for further information.
        '''
        ## Checking the argument so 'others' is a list of elements
        if(len(others) == 1 and type(others[0]) == list):
            others = [others[0]]
            
        ## Computing the common parent for all elements
        po = self.parent()
        for el in others:
            po = pushout(po, el.parent())
            
        ## Calling the method in the DDRing level
        return po.interlace_sequence([self]+list(others))
    
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
            if(self.is_constant):
                ### Special case: is a constant
                self.__derivative = self.parent()(0 )
            else:
                ### We get the new operator
                newOperator = self.equation.derivative_solution()
            
                ### We get the required initial values (depending of the order of the next derivative)
                initList = self.getInitialValueList(newOperator.get_jp_fo()+2 )
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
                self.__derivative.change_built("derivative",tuple([self]))
                
            
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
        newInit = [self.parent().base_field(constant)] + self.getInitialValueList(newOperator.get_jp_fo()+1 )
        
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
        if(self_var == other or self.is_constant):
            return self
            
        ## Checking that 'other' at zero is zero
        value = None
        try:
            value = other(**{str(self_var):0 })
        except Exception as e:
            warnings.warn("Be careful my friend!! Evaluation at zero were not possible!!\nElement %s" %other, DDFunctionWarning, stacklevel=2 )
            raise e
        if(value != 0 ):
            raise ValueError("Can not compose with a power series with non-zero constant term. Obtained: %s" %(other(**{str(self_var):0 })))
        
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
        equation = destiny_ring.element([coeff(**{str(self_var) : other}) for coeff in self.equation.getCoefficients()]).equation ## Equation with coefficients composed with 'other'
        g = destiny_ring.base()(other) ## Casting the element 'other' to the base ring
        
        new_equation = equation.compose_solution(g)
        
        ######################################
        ## Computing the new initial values
        ######################################
        required = new_equation.get_jp_fo()+1 
        ## Getting as many initial values as we can and need
        init_f = self.getInitialValueList(required)
        init_g = None
        try:
            init_g = g.getInitialValueList(required)
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
    ### Equality methods
    #####################################  
    @derived_property  
    def is_null(self): 
        '''
            Cached property to check whether self is zero in its ring or not.
            
            The method used is comparing the first initial values of the function and check they are zero. If some initial value can not be computed, then False is returned.
        '''
        return self.is_fully_defined and all(self.getInitialValue(i) == 0  for i in range(self.equation.get_jp_fo()+1 ))
        
    @derived_property
    def is_one(self):
        '''
            Cached property to check whether self is one on its ring or not.
            
            The method used is checking that the element is a constant and its first initial value is one.
        '''
        return (self.is_constant and self.getInitialValue(0 ) == 1 )
        
    @derived_property
    def is_constant(self):
        '''
            Cached property to check whether self is a constant or not.
            
            We check enough initial values to know (without computing the derivative) if it is zero or not.
        '''
        ### OPTION 1
        ## Test zero and if not, check if a constant can be solution
        try:
            if(not self.is_null):
                return self.equation[0] == 0  and all(self.getInitialValue(i) == 0  for i in range(1 , self.equation.get_jp_fo()+1 ))
            return True
        except TypeError:
            return False
        ### OPTION 2 (nor proved)
        ## Test only initial values for 'self'
        #try:
        #    return all(self.getInitialValue(i) == 0 for i in range(1,self.equation.get_jp_fo()+3))
        #except TypeError:
        #    return False
        ### OPTION 3 (too costly)
        ## Test the derivative
        #return self.derivative() == 0
        ### OPTION 4 (too costly)
        ## Test the difference with the constant term
        #return (self - self(0)) == 0
    
    @derived_property
    def is_fully_defined(self):
        '''
            Cached property yo check whether the function is fully defined or not.
            
            This means that, given some initial values and the differential equation, the solution of such problem is unique (True) or not (False)
        '''
        max_init = self.equation.get_jp_fo()+1 
        return len(self.getInitialValueList(max_init)) == max_init
        
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
            if(other.is_constant):
                return self.is_constant and self(0 ) == other(0 )
            elif(self.is_constant):
                return False
                
            if(not (self.is_fully_defined and other.is_fully_defined)):
                return (self.equation == other.equation) and (self.getInitialValueList(self.equation.get_jp_fo()+1 ) == other.getInitialValueList(other.equation.get_jp_fo()+1 ))
             
            ### THREE OPTIONS
            ## 1. Compare with the JP-Values of each function
            #m = self.equation.get_jp_fo()+other.equation.get_jp_fo()+1
            #if(not all(self.getInitialValue(i) == other.getInitialValue(i) for i in range(m))):
            #    return False
            
            ## 2. Substract and check zero equality
            return (self-other).is_null
            
            ## 3. Check adding orders and if they are equal, substract operators and check as many initial values as needed
            #m = self.getOrder()+other.getOrder()+1
            #if(not all(self.getInitialValue(i) == other.getInitialValue(i) for i in range(m))):
            #    return False
            #   
            #M = self.equation.add_solution(other.equation).get_jp_fo()+1
            #return all(self.getInitialValue(i) == other.getInitialValue(i) for i in range(m,M))
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
            return self.getInitialValueList(m) == other.getInitialValueList(m)
        except Exception:
            return False

    #####################################
    ### Analytic methods
    #####################################   
    def numerical_solution(self, value, delta=1e-10, max_depth=100 ):
        try:
            ## We try to delegate the computation to the operator (in case of OreOperators)
            if(self.equation.getCoefficients()[-1](0 ) != 0 ):
                sol = self.equation.operator.numerical_solution(self.getSequenceList(self.getOrder()), [0 ,value],delta)
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
            to_sum = self.getSequenceElement(step)*to_mult
            res += to_sum
            if(self.getSequenceElement(step) != 0  and abs(to_sum) < delta):
                find += 1 
            elif(self.getSequenceElement(step) != 0 ):
                find = 0 
            
            step += 1 
            to_mult *= value
        return float(res),float(abs(to_sum))
        
    def numeric_coefficient_comparison_asymptotics(self, other, max_depth=10000, step=100, verbose=False, comparison="quotient", sequence=False):
        r'''
            Method to compare the coefficient sequence of two power sequence. 

            This method compares two sequences via division or difference (see optional arguments) and 
            may provide empirical evidence of similarity in asymptotics between the sequences.

            INPUT::
                - other: the sequence with ''self'' is compared. If it is not a DDFunction it will be casted to one.
                - max_depth: element of the sequence it will be compared. 
                - step: step-jump between comparisons. As the sequences are created recursively, this avoids a recursion overflow in Python.
                - verbose: if set to True, the method will print the progress of the computation.
                - kwds: there are several extra options that can be provided with boolean values:
                    - comparison: the comparison can be "quotient" (''self.getSequenceElement(n)/other.getSequenceElement(n)'') 
                    or "difference" (''self.getSequenceElement(n) - other.getSequenceElement(n)'').
                    - sequence: the answer will be a list of comparisons in all the elements $0 (mod step)$. If not given, the answer will be just the last comparison.

            OUTPUT::
                A value with the appropriate comparison between the ''max_depth'' element of the sequences from ''self'' and ''other''.

            WARNING::
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
                result += [comp(self.getSequenceElement(next), other.getSequenceElement(next))]
            except KeyboardInterrupt:
                if(verbose): print("")
                break
            iteration+=1
            if(verbose): printProgressBar(iteration, total, suffix="(%s) %s" %(next, result[-1]))

        ## Finished loop: returning
        # Checking if the last iteration was made
        if(iteration*step >= max_depth):
            try:
                result += [comp(self.getSequenceElement(max_depth), other.getSequenceElement(max_depth))]
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
            if(self.is_constant):
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
                    lc = self.equation[self.equation.getOrder()]
                 
                # only the zeros of the leading coefficient
                self.__singularities = FiniteEnumeratedSet([root[0][0] for root in lc.roots()])
            else:
                d = self.getOrder()
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
            if(self.is_constant):
                return self.parent().base_field(self.getInitialValue(0))
            elif(is_DDRing(R)):
                coeffs = [el.to_simpler() for el in self.equation.getCoefficients()]
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
                
                return dR.element([dR.base()(el) for el in coeffs], self.getInitialValueList(self.equation.jp_value()+1), name=self.__name).to_simpler()
                        
            elif(is_PolynomialRing(R)):
                degs = [self[i].degree() - i for i in range(self.getOrder()+1)]
                m = max(degs)
                maxs = [i for i in range(len(degs)) if degs[i] == m]
                
                if(len(maxs) <= 1):
                    raise ValueError("2:Function %s is not a polynomial" %repr(self))
                
                x = R.gens()[0]
                pol = sum(falling_factorial(x,i)*self[i].lc() for i in maxs)

                root = max(root[0] for root in pol.roots() if (root[0] in ZZ and root[0] > 0))
                pol = sum(x**i*self.getSequenceElement(i) for i in range(root+1))

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
                - Elements in self.parent().base_field (to be done)
                - Other DDFunctions (with some conditions)
                
            The method works as follows:
                1 - Tries to compute integer or rational power.
                2 - If 'other' is neither in ZZ nor QQ, then try to cast 'other' to a DDFunction.
                3 - Check if self(0) != 0. If self(0) != 1, check log(self(0)) in self.parent().base_field and set f2 = self/self(0).
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
            elif(g in f.parent().base_field): # Constant case: need extra condition (f(0) != 0 and f(0)**g is a valid element
                g = f.parent().base_field(g)
                if(f0 == 0):
                    raise NotImplementedError("The powers for elements with f(0) == 0 is not implemented")
                try:
                    h0 = f0**g
                    if(not h0 in f.parent().base_field):
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
                if(log(f0) not in f.parent().base_field):
                    raise ValueError("Invalid value for log(f(0)). Need to be an element of %s, but got %s" %(f.parent().base_field, log(f0)))
                lf0 = f.parent().base_field(lf0)
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
                #        self.__pows[other] = newDDRing.element([(-other)*f.derivative(),f], [el**other for el in f.getInitialValueList(1 )], check_init=False)
                #        
                #        newName = None
                #        if(not(self.__name is None)):
                #            newName = DynamicString("(_1)^%s" %(other), self.__name)
                #        self.__pows[other].__name = newName
                #    except TypeError:
                #        raise TypeError("Impossible to compute (%s)^(%s) within the basic field %s" %(f.getInitialValue(0 ), other, f.parent().base_ring()))
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
        
    ### Magic use
    def __call__(self, X=None, **input):
        '''
            Method that return the value of the function in the point given. As the function as a power-series may not converge, this method only works if the argument is 0.
            Further implementation can be done for DDFunctions that we know about the convergence.
        '''
        if ((not(X is None)) and X == 0 ):
            return self.getInitialValue(0 )
        
        return self.parent().eval(self, X, **input)
        
    ### Magic representation
    def __hash__(self):
        '''
            Hash method for DDFunctions.

            Since several representations may be equal, we use the initial conditions as a mark for the hash.
        '''
        return sum(hash(el) for el in self.getInitialValueList(20))

    def __getitem__(self, key):
        r'''
            GetItem method for DDFunctions. It allows the user do ``self[i]`` for `i \geq -1`.
            
            INPUT:
                - ``key``: an integer.
            
            RETURN:
                - The result is the coefficient of `D^{key}(f)` on the equation.
        '''
        return self.getOperator().getCoefficient(key)

    def __missing__(self, key):
        '''
            Missing method for DDFunctions.
        '''
        return 0 
        
    def __str__(self, detail=True):
        '''
            String method for DDFunctions. It prints all information of the DDFunction.
        '''
        #if(self.is_constant):
        #    return (self.getInitialValue(0)).__str__()
            
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
        while ((j < self.getOrder()) and (self.getOperator().getCoefficient(j) == 0 )):
            j += 1 
        res += self.__get_line__(self.getOperator().getCoefficient(j), j, detail, True)
        for i in range(j+1 ,self.getOrder()+1 ):
            if(self.getOperator().getCoefficient(i) != 0 ):
                res += '\n'
                res += self.__get_line__(self.getOperator().getCoefficient(i), i, detail)

        res += '\n\t\t = 0 \n\t'

        res += '-- Initial values:\n\t'
        res += format(self.getInitialValueList(self.equation.get_jp_fo()+1 ))
        
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
        if(self.is_constant):
            return str(self.getInitialValue(0 ))
        if(self.__name is None):
            return "(%s:%s:%s)DD-Function in (%s)" %(self.getOrder(),self.equation.get_jp_fo(),self.size(),self.parent()) 
        else:
            return str(self.__name)
            
    def __critical_numbers__(self):
        return "(%d:%d:%d)" %(self.getOrder(),self.equation.get_jp_fo(),self.size())
    
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
        coeffs = [self[i] for i in range(self.getOrder()+1)]
        simpl = [(not is_DDRing(parent.base()))]*(self.getOrder()+1)
        sgn = ['+']*(self.getOrder()+1)
        for i in range(len(coeffs)):
            ## Computing the sign and string for the coefficient
            current = coeffs[i]
            
            if(not simpl[i] and current.is_constant): # Recursive and constant case
                current = current.getInitialValue(0) # Reduced to constant case
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
                res += ["%s(0) = %s" %(name,latex(self.getInitialValue(i)))]
            elif(i == 1):
                res += ["%s'(0) = %s" %(name,latex(self.getInitialValue(i)))]
            elif(i == 2):
                res += ["%s''(0) = %s" %(name, latex(self.getInitialValue(i)))]
            else:
                res += ["%s^{(%d)}(0) = %s" %(name, i,latex(self.getInitialValue(i)))]
        return ", ".join(res)

    ## Overriding the serializable method with an extra parameter
    def serialize(self, file, full=False):
        ## If asked for the full information
        if(full):
            ## We put the current list as argument for the initial conditions
            max_index = max(el for el in self.__calculatedSequence)
            aux = self.skwds()["init_values"]
            self.skwds()["init_values"] = self.getInitialValueList(max_index+1)

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
        
        n = max(self.equation.get_jp_fo(),max(el for el in self.__calculatedSequence))
        if((not (bound is None)) and (bound in ZZ) and (bound > 0)):
            n = min(bound, n)
        
        if(init):
            pdump(self.getInitialValueList(n+1), file)
        else:
            pdump(self.getSequenceList(n+1), file)
            
        if(is_str): file.close()

    def load_init(self, file, init=True, bin=True, check=True,bound=None):
        r'''
            Method to load the initial conditions for this function. 
            
            This method loads from ``file`` the initial conditions or the sequence
            of ``self`` using the method load from the package pickle.
            
            For a proper behavior of this function, only files created with 
            the method ``save_init`` should be used.
            
            INPUT::
                * file: an opened file object or a string with the Path to the file.
                * init: indicates if loading the initial values (``True``) or the sequence. 
                * bin: a flag indicating if load the object in text mode or binary mode.
                * check: a flag to check the data is valid for the equation.
                * bound: number of elements of the sequence to load.
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
                self.__calculatedSequence = aux.__calculatedSequence
            except ValueError:
                raise ValueError("Bad error conditions in %s for equation %s" %(file.name,self.equation))
        else:
            self.__calculatedSequence = {i : data[i] for i in range(n)}

    def _to_command_(self):
        if(self.__name is None):
            return "%s.element(%s,%s)" %(command(self.parent()), _command_list(self.getOperator().getCoefficients()), self.getInitialValueList(self.getOrder()))
        else:
            return "%s.element(%s,%s,name='%s')" %(command(self.parent()), _command_list(self.getOperator().getCoefficients()), self.getInitialValueList(self.getOrder()),str(self.__name))
        
    #####################################       
    ### Other methods
    #####################################    
    def __nonzero__(self):
        return not (self.is_null)
        
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
        return "ParametrizedDDRing(*,%d,%s,%s)" %(self.depth(), self.base_field(),self.__vars)
        
    def _apply_functor(self, x):
        return ParametrizedDDRing(DDRing(x, depth = self.depth(), base_field = self.base_field), self.__vars)
        
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
            base_field = pushout(self.base_field(), other.base_field())
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
                return self.codomain().element([self.codomain().base()(coeff) for coeff in p.equation.getCoefficients()], p.getInitialValueList(p.equation.get_jp_fo()+1 ))
            except:
                raise ValueError("Impossible the coercion of element \n%s\n into %s" %(p, self.codomain()))
        if(p.is_constant):
            return self.codomain()(p.getInitialValue(0 ))
        
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
        
# def polynomial_computation(poly, functions):
#     '''
#         Method that compute a polynomial operation over a set of DDFunctions.
        
#         INPUT:
#             - poly: a multivariate polynomial representing the operation we want to perform.
#             - functions: the set of functions related with the polynomial. 
#         OUTPUT:
#             A DDFunction in the corresponding DDRing.
            
#         WARNING:
#             We assume that for any pair of functions f,g in functions, there are not
#             constants c,d such that f = cg+d. Otherwise the result will still
#             be correct, but will be computed slower.
#     '''
#     ### Checking the argument 'poly'
#     if(not _is_polynomial(poly)):
#         raise TypeError("First argument require to be a polynomial.\n\t- Got: %s (%s)" %(poly, type(poly)))
#     parent_poly = poly.parent()
#     gens = parent_poly.gens()
        
#     ### Checking the argument 'functions'
#     tfunc= type(functions)
#     if(not ((tfunc is list) or (tfunc is set) or (tfunc is tuple))):
#         functions = [functions]
        
#     if(len(functions) < parent_poly.ngens()):
#         raise TypeError("Not enough functions given for the polynomial ring of the polynomial.")
    
#     ### Coercing all the functions to a common parent
#     parent = functions[0].parent()
#     for i in range(1,len(functions)):
#         parent = pushout(parent, functions[i].parent())
        
#     ### Base case: non-DDRing
#     if(not isinstance(parent, DDRing)):
#         return poly(**{str(gens[i]) : functions[i] for i in range(len(gens))})
        
#     functions = [parent(f) for f in functions]
        
#     ### Grouping the elements that are derivatives of each other
#     ### Using the assumption on the input functions, we have that for each
#     ###    chain of derivatives, we only need to check if the function is
#     ###    the derivative of the last or if the first element is the derivative
#     ###    of the function.
#     chains = []
#     for f in functions:
#         inPlace = False
#         for i in range(len(chains)):
#             if(f.derivative() == chains[i][0]):
#                 chains[i] = [f] + chains[i]
#                 inPlace = True
#                 break
#             elif(chains[i][-1].derivative() == f):
#                 chains[i] = chains[i] + [f]
#                 inPlace = True
#                 break
#         if(not inPlace):
#             chains += [[f]]
#     dics = {c[0] : [gens[functions.index(f)] for f in c] for c in chains}
            
#     ## We build the new operator
#     newOperator = None
#     if(len(dics) == 1):
#         if(hasattr(f.equation, "annihilator_of_polynomial")):
#             ## Reordering the variables
#             parent_poly2 = PolynomialRing(chains[0][0].parent().original_ring(), dics[chains[0][0]])
#             poly2 = parent_poly2(poly)
#             newOperator = f.equation.annihilator_of_polynomial(poly2)
#     if(newOperator is None):
#         newOperator = _get_equation_poly(poly, dics)
            
#     ### Getting the needed initial values for the solution
#     needed_initial = newOperator.get_jp_fo()+1 
        
#     ### Getting as many initial values as possible until the new order
    
#     newInit = [_get_initial_poly(poly, dics, i) for i in range(needed_initial)]
#     ## If some error happens, we delete all results after it
#     if(None in newInit):
#         newInit = newInit[:newInit.index(None)]
        
#     ## Computing the new name
#     newName = None
#     if(all(f.has_name() for f in functions)):
#         newName = DynamicString(_m_replace(str(poly), {str(gens[i]) : "_%d" %(i+1) for i in range(len(gens))}), [f._DDFunction__name for f in functions])
        
#     ## Building the element
#     result = parent.element(newOperator, newInit, check_init=False, name=newName)
#     result.change_built("polynomial", (poly, {str(gens[i]) : functions[i] for i in range(len(gens))}))

#     return result

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
        if(e in _IntegralDomains):
            if(e is QQ):
                return "QQ"
            if(Uni_Polynomial.is_PolynomialRing(e)):
                return "PolynomialRing(%s,%s)" %(command(e.base()), [str(var) for var in e.gens()])
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
    m = max([el.degree() for el in op.getCoefficients()])
    bound = op.getOrder() + m
    
    num_of_bck = bound - op.getOrder()
    m = None
    for i in range(num_of_bck, 0 , -1 ):
        if(op.backward(i) != 0 ):
            m = -i
            break
    
    if(m is None):
        for i in range(op.getOrder()+1 ):
            if(op.forward(i) != 0 ):
                m = i
                break
    
    n = op._Operator__polynomialRing.gens()[0]
    
    rec = [op.get_recursion_polynomial(i)(n=n+m) for i in range(m,op.forward_order + 1 )]
    rec_gcd = gcd(rec)
    rec = [el/rec_gcd for el in rec]
    
    return (rec, f.getSequenceList(op.forward_order-m))
DFinite._DDRing__get_recurrence = __get_recurrence

###################################################################################################
### PACKAGE ENVIRONMENT VARIABLES
###################################################################################################
__all__ = [
    "is_DDRing", 
    "is_ParametrizedDDRing", 
    "is_DDFunction", 
    "DDRing", 
    "DFinite", 
    "DDFinite", 
    "command", 
    "zero_extraction", 
    #"polynomial_computation", 
    "ParametrizedDDRing", 
    "DFiniteP", 
    "DFiniteI"]
  

