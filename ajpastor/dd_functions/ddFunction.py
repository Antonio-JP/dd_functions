
from sage.all_cmdline import *   # import sage library

_sage_const_1en10 = RealNumber('1e-10');

# Python imports
import warnings;

#SAGE imports 
from sage.rings.ring import IntegralDomain;
from sage.rings.polynomial.polynomial_element import is_Polynomial;
from sage.rings.polynomial.multi_polynomial import is_MPolynomial;
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing;
from sage.structure.element import IntegralDomainElement;
from sage.categories.integral_domains import IntegralDomains;
from sage.categories.pushout import pushout;
from sage.categories.pushout import ConstructionFunctor;

#ajpastor imports
from ajpastor.operator.operator import Operator;
from ajpastor.operator.oreOperator import w_OreOperator;
from ajpastor.operator.directStepOperator import DirectStepOperator;
from ajpastor.operator.fullLazyOperator import FullLazyOperator;

from ajpastor.misc.dinamic_string import *;
from ajpastor.misc.cached_property import derived_property;
from ajpastor.misc.ring_w_sequence import Ring_w_Sequence;
from ajpastor.misc.ring_w_sequence import Wrap_w_Sequence_Ring;
from ajpastor.misc.ring_w_sequence import sequence;

#####################################################
### Definition of some exceptions
#####################################################
class DevelopementError(NotImplementedError):
    def __init__(self, name):
        NotImplementedError.__init__(self, "Method %s still under construction. Please be patient and wait until it is finished." %name);

#####################################################
### Definition of the particular warnings we are interested to raise
#####################################################
class DDFunctionWarning(RuntimeWarning):
    pass;

class MergingRingWarning(DDFunctionWarning):
    pass;
    
class TooDeepWarning(DDFunctionWarning):
    pass;
    
class NoOreAlgebraWarning(DDFunctionWarning):
    pass;

warnings.simplefilter('always', DDFunctionWarning);
    

## Auxiliar derivative function
def _aux_derivation(p):
    try:
        R = p.parent();
        return derivative(p,R(x));
    except Exception:
        return 0 ;
        
#####################################################
### Class for DD-Rings
#####################################################
class DDRing (Ring_w_Sequence, IntegralDomain):
    Element = None;
    
    _Default_Base = PolynomialRing(QQ,x);
    _Default_Depth = 1 ;
    _Default_Base_Field = None;
    _Default_Invertibility = None;
    _Default_Derivation = None;
    _Default_Operator = None;
    _Default_Parameters = [
        ("base", _Default_Base),
        ("depth", _Default_Depth),
        ("base_field", _Default_Base_Field),
        ("invertibility", _Default_Invertibility),
        ("derivation", _Default_Derivation),
        ("default_operator", _Default_Operator)];
    
    _CACHED_DD_RINGS = {};
    
    _Default_variable = 'x';
    
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
        from sage.categories.pushout import AlgebraicExtensionFunctor as algebraic;
        const_S = S.construction(); const_R = R.construction();
        
        if(not(isinstance(const_S[0 ],algebraic) and isinstance(const_R[0 ], algebraic))):
            return R==S;
        
        if(const_S[1 ] != const_R[1 ]):
            return False;
        
        polys_R = const_R[0 ].polys; polys_S = const_S[0 ].polys;
        names_R = const_R[0 ].names; names_S = const_S[0 ].names;
        
        if(len(polys_R) != len(polys_S)):
            return False;
        
        for i in range(len(polys_R)):
            try:
                index = polys_S.index(polys_R[i]);
                if(names_R[i] != names_S[index]):
                    return False;
            except ValueError:
                return False;
        return True;
        
    @staticmethod
    def __get_gens__(parent):
        from sage.categories.pushout import AlgebraicExtensionFunctor as algebraic;
        from sage.categories.pushout import PolynomialFunctor as polynomial;
        from sage.categories.pushout import MultiPolynomialFunctor as multi_polynomial;
        from sage.categories.pushout import FractionField as fraction;
        
        current = parent; 
        const = parent.construction(); 
        gens = [el for el in parent.gens()];
        
        res = {'algebraic' : [], 'polynomial': [], 'other' : []};
        
        while((not(const is None)) and (not (1  in gens))):
            if(isinstance(current, DDRing) or isinstance(const[0 ], polynomial) or isinstance(const[0 ], multi_polynomial)):
                res['polynomial'] += list(current.gens());
            elif(isinstance(const[0 ], algebraic)):
                for i in range(len(const[0 ].polys)):
                    name = const[0 ].names[i];
                    found = None;
                    for gen in current.gens():
                        if(current(name) == gen):
                            found = gen;
                            break;
                    if(found is None):
                        raise TypeError("Impossible error: no generator for a name!!");
                    res['algebraic'] += [(found, const[0 ].polys[i], const[1 ])];
            elif(not isinstance(const[0 ], fraction)):
                res['other'] += list(current.gens());
                
            current = const[1 ];
            const = current.construction();
            
        ## Cleaning "1" from the result
        ## Put everything as tuples
        if(1  in res['algebraic']):
            raise TypeError("1 is a generator of an algebraic extension");
        res['algebraic'] = tuple(res['algebraic']);
        while(1  in res['polynomial']):
            res['polynomial'].remove(1 );
        res['polynomial'] = tuple(set(res['polynomial']));
        while(1  in res['other']):
            res['other'].remove(1 );
        res['other'] = tuple(set(res['other']));
            
        return res, current;
        
    #################################################
    ### Builder
    #################################################
    @staticmethod
    def __classcall__(cls, *args, **kwds):
        final_args = [];
                
        ## We first compile the parameters the user send
        current = 0 ;
        if(len(args) != 1  or args[0 ] != None):
            for i in range(len(args)):
                final_args += [[DDRing._Default_Parameters[i][0 ], args[i]]];
            current = len(args);
        
        for i in range(current, len(DDRing._Default_Parameters)):
            final_args += [[DDRing._Default_Parameters[i][0 ], kwds.get(DDRing._Default_Parameters[i][0 ],DDRing._Default_Parameters[i][1 ])]];
            
        ## Managing the depth over DDRings
        if(isinstance(final_args[0 ][1 ], DDRing)):
            final_args[1 ][1 ] = final_args[1 ][1 ]+final_args[0 ][1 ].depth();
            final_args[0 ][1 ] = final_args[0 ][1 ]._DDRing__original;
            
        ## Casting to tuple (so is hashable)
        to_hash = tuple(tuple(el) for el in final_args[:2 ]);
        final_args = tuple(tuple(el) for el in final_args);
        
        if(final_args[1 ][1 ] == 0 ):
            return final_args[0 ][1 ];
            
        if(not cls in DDRing._CACHED_DD_RINGS):
            DDRing._CACHED_DD_RINGS[cls] = {};
        if(not (to_hash in DDRing._CACHED_DD_RINGS[cls])):
            tmp = IntegralDomain.__new__(cls);
            DDRing.__init__(tmp,**dict(final_args));
            DDRing._CACHED_DD_RINGS[cls][to_hash] = tmp;
       
        return DDRing._CACHED_DD_RINGS[cls][to_hash];
    
    def __init__(self, base=_Default_Base, depth = _Default_Depth, base_field = _Default_Base_Field, invertibility = _Default_Invertibility, derivation = _Default_Derivation, default_operator = _Default_Operator):
        '''
            Class representing the Ring of Differentially Definable Functions with coefficients over a base ring. It can be built using different parameter configurations:
                - ``base``: is the ring where the coefficients of the differential equation will be. It is set by default as `\mathbb{Q}[x]`.
                - ``invertibility``: a function to decide if the argument is a unit in the ring we are building.
                - ``derivation``: a function to derivate elements in the coefficients ring.
                
            More formally, ``(base,derivation)`` should be a Differential Ring and the result (represented by this class) will be another Differential Ring which extends the original.
        '''
        ## Other attributes initialization
        self.__variables = None;
        
        if(depth > 1 ):
            DDRing.__init__(self,DDRing(base, depth-1 , base_field, invertibility, derivation, default_operator), 1 , base_field, invertibility, derivation, default_operator);
        else:
            ### We call the builders of the superclasses
            Ring_w_Sequence.__init__(self, base, method = lambda p,n : self(p).getSequenceElement(n));
            IntegralDomain.__init__(self, base, category=IntegralDomains());
            
            ### We assign the operator class
            if(default_operator is None):
                ## In this case we add an default Operator
                if(isinstance(base, DDRing)):
                    self.default_operator = FullLazyOperator;
                else:
                    self.default_operator = DirectStepOperator;
            elif(issubclass(default_operator, Operator)):
                self.default_operator = default_operator;
            else:
                raise TypeError("Invalid type for Operators in this ring. Must inherit from class Operator.");
            
            ### In order to get Initial Values, we keep the original field base 
            # If the base ring is already a DDRing, we take the correspond ring from base
            if isinstance(base, DDRing):
                self.base_field = base.base_field;
                self.__depth = base.__depth + 1 ;
                self.__original = base.__original;
            # Otherwise, we set this simplest ring as our current coefficient ring
            else:
                if(base_field is None):
                    from sage.categories.pushout import PolynomialFunctor, FractionField;
                    current = base;
                    const = base.construction();
                    while((not (const is None)) and (isinstance(const[0 ], PolynomialFunctor) or isinstance(const[0 ],FractionField))):
                        current = const[1 ];
                        const = current.construction();
                        
                    if(not current.is_field()):
                        self.base_field = current.fraction_field();
                    else:
                        self.base_field = current;
                        
                        
                else:
                    self.base_field = base_field;
                self.__depth = 1 ;
                self.__original = base;
            
            ### Saving the invertibility criteria
            if(invertibility is None):
                try:
                    self_var = self.variables(True,False)[0 ];
                    self.base_inversionCriteria = lambda p : p(**{self_var : 0 }) == 0 ;
                except IndexError:
                    self.base_inversionCriteria = lambda p : self.base()(p)==0 ;
            else:
                self.base_inversionCriteria = invertibility;
            
            ### Saving the base derivation
            if(derivation is None):
                try:
                    self_var = self.variables(True,False)[0 ];
                    self.base_derivation = lambda p : p.derivative(self.base()(self_var));
                except IndexError:
                    self.base_derivation = lambda p : 0 ;
            else:
                self.base_derivation = derivation;
            
            ### Setting the default "get_recurence" method
            self.__get_recurrence = None;
            
            
            ### Setting new conversions
            current = self.base();
            morph = DDSimpleMorphism(self, current);
            current.register_conversion(morph);
            while(not(current.base() == current)):
                current = current.base();
                morph = DDSimpleMorphism(self, current);
                current.register_conversion(morph);

    #################################################
    ### Coercion methods
    #################################################
    def _coerce_map_from_(self, S):
        '''
            Method to get the coerce map from the SAGE structure 'S' (if possible).
            
            To allow the agebraic numbers, we use the method '__get_gens__' to compare how the ring 'S' and the ring 'self' where built. If at some point we can not use the behaviour of the generators, we will rely on the usual _coerce_map_from_ with 'self.base()'.
        '''
        ## Checking the easy cases
        coer = None;
        if(isinstance(S, DDRing)):
            coer = self.base()._coerce_map_from_(S.base());
        elif(S == self.base()):
            coer = True;
        elif(isinstance(S, sage.symbolic.ring.SymbolicRing)):
            coer = True;
        else:
            coer = self.base()._coerce_map_from_(S);
            
        if(not(coer is False) and not(coer is None)):
            return True;
        #return None;
        ## If not coercion is found, we check deeper using generators
        gens_self, p_self = DDRing.__get_gens__(self);
        try:
            gens_S, pS = DDRing.__get_gens__(S);
        except RuntimeError:
            return None;
        
        ## Using the 'other' generators
        if(len(gens_S['other']) > 0 ):
            return self.base()._coerce_map_from_(S);
            
        ## Comparing the algebraic construction
        for i in range(len(gens_S['algebraic'])):
            looking = gens_S['algebraic'][i];
            found = False;
            for el in gens_self['algebraic']:
                if(el[1 ] == looking[1 ] and str(el[0 ]) == str(looking[0 ])):
                    found = True;
                    break;
            if(not found):
                return self.base()._coerce_map_from_(S);
                
        ## Comparing the parametric space
        if(any(str(el) not in [str(ob) for ob in gens_self['polynomial']] for el in gens_S['polynomial'])):
            return self.base()._coerce_map_from_(S);
            
        ## Comparing the depth of the structure S
        if(isinstance(S, DDRing)):
            return S.depth() <= self.depth();
        
    def __is_polynomial(self, S):
        from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isUniPolynomial;
        from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing as isMPolynomial;
        
        return isUniPolynomial(S) or isMPolynomial(S);
        
    def _pushout_(self, S):
        '''
            This method compute the pushout of 'self' with the parent class 'S'. This method returns None if it is not possible to get the pushout or a DDRing with all the properties required to include 'self' and 'S'.
            
            The method goes as follows:
                1 - Compute the simplest field over everything is based (let us call it 'F'). This will be 'QQ' or an algebraic extension of 'QQ' (see the class 'NumberField')
                2 - Compute the list of parameters involved. This will be the constant trascendent elements that will extend the ring 'F' as a rational function ring. Let 'B' be such extension.
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
        from sage.categories.integral_domains import IntegralDomains;
        
        if(isinstance(S, sage.symbolic.ring.SymbolicRing)):
            return None;
            
        ## We get a list of the generators of self and S with their types
        gens_self, pself = DDRing.__get_gens__(self);
        try:
            gens_S, pS = DDRing.__get_gens__(S);
        except RuntimeError:
            return None;
        
        if(len(gens_S['other']) > 0  or len(gens_self['other']) > 0 ):
            raise TypeError("Impossible to compute a pushout: generators not recognized found.\n\t- %s" %(list(gens_S['other']) + list(gens_self['other'])));
        
        ##########################################
        ## Compute the basic field F
        ##########################################
        ## Computing the original field
        F = None;
        try:
            F = pushout(pself, pS);
        except:
            pass;
        if(F is None):
            raise TypeError("Incompatible original structures:\n\t- %s\n\t- %s" %(pself, pS));
        
        if(not F in IntegralDomains()):
            raise TypeError("Pushout of the original structures is not an integral domain:\n\t- %s" %F);
        if(not F.is_field()):
            F = F.fraction_field();
            
        ## Extending the field with algebraic extensions
        polys = {str(el[0 ]):el[1 ] for el in gens_self['algebraic']}
        for el in gens_S['algebraic']:
            if(polys.get(str(el[0 ]), el[1 ]) != el[1 ]):
                raise TypeError("Incompatible names in algebraic extensions:\n\t- %s\n\t- %s" %(el,(el[0 ],polys[str(el[0 ])])));
            polys[str(el[0 ])] = el[1 ];
            
        sorted_names = sorted(polys);
        sorted_polys = [polys[el] for el in sorted_names];
        
        F = NumberField([PolynomialRing(F,x)(el) for el in sorted_polys], sorted_names);
        
        ##########################################
        ## Compute the list of parameters and variables
        ##########################################
        all_params = set(str(el) for el in (gens_S['polynomial']+gens_self['polynomial']));
        params = all_params - set([str(el) for el in self.variables(True)]);
        variables = all_params - params;
        
        ##########################################
        ## Compute the required depth
        ##########################################
        depth = self.depth();
        if(isinstance(S, DDRing)):
            depth = max(depth,S.depth());
        
        ##########################################
        ## Building the final DDRing
        ##########################################
        if(len(variables) > 0 ):
            F = PolynomialRing(F,[str(el) for el in variables]);
        R = DDRing(F, depth = depth);
        if(len(params) > 0 ):
            R = ParametrizedDDRing(R, params);
            
        return R;
        
    def _has_coerce_map_from(self, S):
        coer =  self._coerce_map_from_(S);
        return (not(coer is False) and not(coer is None));
        
    def _element_constructor_(self, *args, **kwds):
        el_class = self.element_class;
        if(len(args) < 1 ):
            raise ValueError("Impossible to build a lazy element without arguments");
        
        if(args[0 ] is self):
            X = args[1 ];
        else:
            X = args[0 ];
           
        try:
            if(isinstance(X, DDFunction)):
                if(X.parent() is self):
                    return X;
                else:
                    return self.element([coeff for coeff in X.equation.getCoefficients()], X.getInitialValueList(X.equation.get_jp_fo()+1 ), name=X._DDFunction__name);
            else:
                try:
                    try:
                        X = self.base()(X);
                    except TypeError as e:
                        try:
                            X = self.base()(str(X));
                        except:
                            raise e;
                    el = self.element([-self.base_derivation(X), X]);
                    name = str(X);
                    try:
                        name = X._DDFunction__name;
                    except:
                        pass;
                    return el.change_init_values([sequence(X,i)*factorial(i) for i in range(el.equation.get_jp_fo()+1 )], name=name);
                except AttributeError:
                    try:
                        return self.element([1 ],[], self.base()(X), name=str(X));
                    except Exception:
                        return self(str(element));
        except TypeError as e:
            raise TypeError("Cannot cast an element to a DD-Function of (%s):\n\tElement: %s (%s)\n\tReason: %s" %(self, X, type(X), e));
            
    def gens(self):
        return ();
    
    def ngens(self):
        return 0 ;
            
    def construction(self):
        return (DDRingFunctor(self.depth(), self.base_field), self.__original);
        
    def __contains__(self, X):
        try:
            if((X.parent() is self) or (self._has_coerce_map_from(X.parent()))):
                return True;
        except AttributeError:
            pass;
        try:
            self(X)
            return True;
        except Exception:
            return False;
    
    #################################################
    ### Magic python methods
    #################################################
    def __eq__(self, other):
        if(isinstance(other, DDRing)):
            return self._has_coerce_map_from(other) and other._has_coerce_map_from(self);
        return False;
     
    ## Other magic methods   
    def _repr_(self):
        '''
            Method implementing the __repr__ magic python method. Returns a string telling that self is a DDRing and which Ring is its base.
        '''
        return "DD-Ring over (%s)" %(self.base());
        
    def _to_command_(self):
        return "DDRing(%s)" %command(self.base());
            
    #################################################
    ### Integral Domain and Ring methods
    #################################################
    def _an_element_(self):
        '''
            Method inherited from Ring SAGE class. It returns an example of object that is in the DDRing. It simply returns the 1 element.        
        '''
        return self.one();
    
    def random_element(self,**kwds):
        '''
            Method to compute a random element in this ring. This method relies in a random generator of the self.base() ring and a generator of
            elements of the ring self.base_ring().
            This method accepts different named arguments:
		- "min_order": minimal order for the equation we would get (default to 1)
		- "max_order": maximal order for the equation we would get (default to 3)
		- "simple": if True, the leading coefficient will always be one (default True)
        '''
	## Getting the arguments values
	min_order = kwds.get("min_order", 1);
	max_order = kwds.get("max_order", 3);
	simple = kwds.get("simple", True);

	## Checking the argument values
	min_order = max(min_order,0); ## Need at least order 1
	max_order = max(min_order, max_order); ## At least the maximal order must be equal to the minimal
	if(simple != True and simple != False):
            simple = False;

        ## Computing the list of coefficients
	R = self.base(); S = self.base_field;
        coeffs = [R.random_element() for i in range(randint(min_order,max_order)+1)];
	
	init_values = [0];
	while(init_values[0] == 0):
            init_values[0] = S.random_element();

	## If we want simple elements, we can compute the initial values directly
	if(simple):
	    coeffs[-1] = R.one();
	    init_values += [S.random_element() for i in range(len(coeffs)-2)];
	    return self.element(coeffs,init_values);
	## Otherwise, we need to know the initial value condition
        equation = self.element(coeffs).equation;
        warnings.warn("Not-simple random element not implemented. Returning zero", DDFunctionWarning, stacklevel=2);

	return self.zero();

	
   
    def characteristic(self):
        '''
            Method inherited from the Ring SAGE class. It returns the characteristic of the coefficient ring.
        '''
        return self.base().characteristic();
        
    def base_ring(self):
        return self.base_field;
        
    def original_ring(self):
        return self.__original;
        
    def depth(self):
        return self.__depth;
        
    def to_depth(self, dest):
        return DDRing(self.original_ring(), depth = dest, base_field = self.base_field, invertibility = self.base_inversionCriteria, derivation = self.base_derivation, default_operator = self.default_operator);
        
    def is_field(self, **kwds):
        return False;
        
    def is_finite(self, **kwds):
        return False;
        
    def is_noetherian(self, **kwds):
        return True;

    #################################################
    ### DDRings methods
    #################################################
    def invertible(self,x):
        '''
            Method to make easier call the inversibility criteria specified when a DDRing was created.
            
            INPUT:
                - ``x``: an element of self.
            OUTPUT:
                - True if ``x`` is in self and it is a unit.
                - False otherwise.
        '''
        return self.base_inversionCriteria(x);
        
    def element(self,coefficients=[],init=[],inhomogeneous=0 , check_init=True, name=None):
        '''
            Method to create a DDFunction contained in self with some coefficients, inhomogeneous term and initial values. This method just call the builder of DDFunction just puting the base argument as self.
        '''
        return DDFunction(self,coefficients,init,inhomogeneous, check_init=check_init, name=name);
        
    def eval(self, element, X=None, **input):
        if not element in self:
            raise TypeError('The element we want to evaluate (%s) is not an element of this ring (%s)'%(element,self));
        element = self(element);
            
        rx = X;
        self_var = str(self.variables(True)[0 ]);
        if((rx is None) and (self_var in input)):
            rx = input.pop(self_var);
        if not (rx is None):
            if(rx == 0 ):
                return element.getInitialValue(0 );
            elif(rx in self.base_field):
                return element.numerical_solution(rx,**input)[0 ];
            try:
                return element.compose(rx);
            except ValueError:
                pass;
        elif(len(input) == 0 ):
            return element;
        
        raise NotImplementedError("Not implemented evaluation of an element of this ring (%s) with the parameters %s and %s" %(self,rx,input));
        
    def get_recurrence(self, *args, **kwds):
        if(self.__get_recurrence is None):
            raise NotImplementedError("Recurrence method not implemented for %s" %self);        
        return self.__get_recurrence(*args, **kwds);
    
    def variables(self, as_symbolic=False, fill = True):
        if(self.__variables is None):
            self.__variables = [];
            current = self.base();
            while(current != self.base_field):
                self.__variables += [var(str(el)) for el in current.gens()];
                current = current.base();
            self.__variables = tuple(set(self.__variables));
        
        if(as_symbolic):
            if(len(self.__variables) == 0  and fill):
                return tuple([var(DDRing._Default_variable)]);
            return self.__variables;
        else:
            if(len(self.__variables) == 0  and fill):
                return tuple([self.base()(var(DDRing._Default_variable))]);
            return tuple(self.base()(el) for el in self.__variables);
        
    #def getBaseMatrixSpace(self,nrows, ncols):
    #    '''
    #        Method to get a MatrixSpace with coefficients in the coefficient Ring of the current DDRing with an specified dimension.
    #        
    #        INPUT:
    #            - ``nrows``: number or rows of the new MatrixSpace.
    #            - ``rcols``: number of columns of the new MatrixSpace.
    #    '''
    #    return self.matrixSpace.matrix_space(nrows,ncols);
        
        
#############################################################################
###
### Ring class for Parametrized DD Functions
###
#############################################################################
class ParametrizedDDRing(DDRing):

    @staticmethod
    def __classcall__(cls, *args, **kwds):
        ## In order to call the __classcall__ of DDRing we treat the arguments received
        base_ddRing = args[0 ]; 
        if(len(args) > 1 ):
            parameters = args[1 ];
        else:
            parameters = kwds.get('parameters',None);
        names = kwds.get('names',None);
        
        ## Using the "names" approach of SAGE
        if(parameters is None and names is None):
            raise ValueError("Invalid parameters input format: no parameters given");
        elif(parameters is None):
            parameters = names;
        elif(not(names is None)):
            raise ValueError("Invalid syntax creating a ParametrizedDDRing. Use one of the following syntaxes:\n\t- D = ParametrizedDDRing(R,['a','b'])\n\t- D.<a,b> = ParametrizedDDRing(R)");
        
         ## First we get the new variables
        if ((not(type(parameters) == tuple)) and (not(type(parameters) == list)) and (not(type(parameters) == set))):
            parameters = [parameters];
        else:
            parameters = list(parameters);
        if(len(parameters) == 0 ):
            raise TypeError("The list of variables can not be empty");
        
        for i in range(len(parameters)):
            if(type(parameters[i]) == str):
                parameters[i] = var(parameters[i]);
            elif(type(parameters[i]) != sage.symbolic.expression.Expression):
                raise TypeError("All values of the second argument must be strings or SAGE symbolic variables");
        parameters = tuple(set(parameters));
        
        ## We consider not the case the base ring is already parametrized
        if(isinstance(base_ddRing, ParametrizedDDRing)):
            parameters = tuple(set(parameters).union(base_ddRing.parameters(True)));
            base_ddRing = base_ddRing.base_ddRing();
            
        ## We rebuild now the base ring for the DDRing operator
        base_field = base_ddRing.base_field;
        constructions = [base_ddRing.construction()]; # Here is the DD-Ring operator
            
        while(constructions[-1 ][1 ] != base_field):
            constructions += [constructions[-1 ][1 ].construction()];
             
        new_basic_field = PolynomialRing(base_field, parameters).fraction_field();  
        current = new_basic_field;
        for i in range(1 ,len(constructions)):
            current = constructions[-i][0 ](current);
            
        if(constructions[0 ][0 ].depth() > 1 ):
            base_ring = ParametrizedDDRing(DDRing(base_ddRing.original_ring(),depth=constructions[0 ][0 ].depth()-1 ), parameters);
            ring = DDRing.__classcall__(cls, base_ring, 1 , base_field = new_basic_field, default_operator = base_ddRing.default_operator);
            Ring_w_Sequence.__init__(ring, base_ring, method = lambda p,n : ring(p).getSequenceElement(n));
            IntegralDomain.__init__(ring, base_ring, category=IntegralDomains());
        else:
            ring = DDRing.__classcall__(cls, current, depth = constructions[0 ][0 ].depth(), base_field = new_basic_field, default_operator = base_ddRing.default_operator);
            
        ring.__init__(base_ddRing, parameters);
        return ring;
        
    def __init__(self, base_ddRing, parameters):
        '''
            This class represent a generilized concept of DDRing. If `R` is a domain of the power series space (`K[[x]]`), and `D(R)` is its associated DDRing, then we can consider new constants elements and consider `D(R)`  but with the basic field be `K(var_1,...,var_m)`
            
            INPUT:
                - base_ddRing: Base DDRing where this new ring will be based. This parameter can be got using method ``getBaRing``.
                - variables: a list of variables or strings which will be the names of the new variables.
        '''
        ## Checking the first argument
        if ((not(isinstance(base_ddRing, DDRing))) or (isinstance(base_ddRing, ParametrizedDDRing))):
            raise TypeError("Needed a DDRing as first argument for create a Parametrized DDRing");
        
        self.__parameters = tuple(set(parameters));
                    
        self.__baseDDRing = base_ddRing;
            
    def _coerce_map_from_(self, S):
        coer = super(ParametrizedDDRing, self)._coerce_map_from_(S);
        if(not(coer)):
            coer = self.__baseDDRing._coerce_map_from_(S);
            
        return not(not(coer));
            
    def construction(self):
        return (ParametrizedDDRingFunctor(self.depth(), self.base_field, set(self.__parameters)), self.__baseDDRing);
            
    def base_ddRing(self):
        '''
            Method that retrieves the original DDRing where this parametrized space is based on.
            
            OUTPUT:
                - DDRing where elements of ``self`` would be if we substitute the parameters by elements of the base ring.
        '''
        return self.__baseDDRing;
        
    def _repr_(self):
        res = "(%s" %str(self.parameters()[0 ]);
        for i in range(1 ,len(self.parameters())):
            res += ", " + str(self.parameters()[i]);
        res += ")";
        
        if(len(self.parameters()) > 1 ):
            return "%s with parameters %s" %(self.base_ddRing(),res);
        else:
            return "%s with parameter %s" %(self.base_ddRing(),res);
    
    @cached_method
    def parameters(self, as_symbolic = False):
        if(as_symbolic):
            return self.__parameters;
        else:
            return [self.base_field(el) for el in self.__parameters];
            
    def gens(self):
        return self.parameters(True);
        
    def _first_ngens(self, n):
        return self.parameters(False)[:n];
        
    def ngens(self):
        return len(self.parameters());
                        
    # Override to_depth method from DDRing
    def to_depth(self, dest):
        return ParametrizedDDRing(self.base_ddRing().to_depth(dest), self.parameters(True));
            
    # Override eval method from DDRing
    def eval(self, element, X=None, **input):
        rx = X;
        self_var = str(self.variables(True)[0 ]);
        if(X is None and self_var in input):
            rx = input.pop(self_var);
        ### If X is not None, then we evaluate the variable of the ring
        if(not (rx is None)):
            if(len(input) > 0 ):
                return self.eval(element, **input)(**{self_var:rx});
            else:
                return super(ParametrizedDDRing, self).eval(element, rx);
        elif(len(input) > 0 ):
            ### Otherwise, we evaluate the parameters
            element = self(element);
            
            ### Getting the final parameters
            original_parameters = set(str(el) for el in self.parameters());
            used_parameters = set(input.keys());
            got_parameters = reduce(lambda p,q : p.union(q), [set(str(el) for el in SR(value).variables()) for value in input.values()]);
            
            destiny_parameters = (original_parameters - used_parameters).union(got_parameters);
                        
            if(self_var in destiny_parameters):
                raise TypeError("Parameters can only be evaluated to constants.\n\t- Got: %s" %(input));
            
            if(len(destiny_parameters) == 0 ):
                destiny_ring = self.base_ddRing();
            else:
                destiny_ring = ParametrizedDDRing(self.base_ddRing(), tuple(destiny_parameters));
                
            new_equation = destiny_ring.element([el(**input) for el in element.equation.getCoefficients()]).equation;
            
            new_init = [el(**input) for el in element.getInitialValueList(new_equation.get_jp_fo()+1 )];
            new_name = None;
            if(element._DDFunction__name is not None):
                new_name = din_m_replace(element._DDFunction__name, {key: str(input[key]) for key in input}, True);
            return destiny_ring.element(new_equation,new_init,name=new_name);
        return element;
            
        
#####################################################
### Class for DD-Functions
#####################################################
class DDFunction (IntegralDomainElement):
    #####################################
    ### Init and Interface methods
    #####################################
    def __init__(self, parent, input = 0 , init_values = [], inhomogeneous = 0 , check_init = True, name = None):
        '''
            Method to initialize a DD-Function insade the DD-Ring given in 'parent'
            
            The object will represent a function 'f' such that
                - input (f) = inhomogeneous;
                - f^{(i)}(0) = init_values[i]
        '''        
        # We check that the argument is a DDRing
        if(not isinstance(parent, DDRing)):
            raise TypeError("A DD-Function must be an element of a DD-Ring");
        ### We call superclass builder
        IntegralDomainElement.__init__(self, parent);
        
        ## Checking we have some input (if not, we assume the input for zero)
        ## We take care of the following arguments
        ##     input -> equation
        ##     init_values -> init
        ##     inhomogeneous -> inhom
        zero = False;
        if((type(input) == list and len(input) == 0 ) or input == 0 ):
            zero = True;
        elif(type(input) == list and all(el == 0  for el in input)):
            zero = True;
        elif((type(input) == list and len(input) == 1 ) or (isinstance(input, Operator) and input.getOrder() == 0 )):
            zero = (inhomogeneous == 0 );
            
        if(zero):
            ### The equation is zero, we need inhomogeneous equals to zero
            if(not inhomogeneous == 0 ):
                raise ValueError("Incompatible equation (%s) and inhomogeneous term (%s)" %(input, inhomogeneous));
            else:
            ### Also, all the initial values must be zero
                for el in init_values:
                    if (not el == 0 ):
                        raise ValueError("Incompatible equation (%s) and initial values (%s)" %(input, init_values));
                init = [0 ];
                equation = [0 ,1 ];
                inhom = 0 ;
        else:
            equation = input;
            init = [el for el in init_values];
            inhom = inhomogeneous;
        
        ### Cached elements
        self.__pows = {0 :1 , 1 :self}; # Powers-cache
        self.__derivative = None; # The derivative of a function
        
        ### Assigning the differential operator
        ### We will save the leading coefficient of the equation (lc) to future uses.
        # We create the operator using the structure given by our DDRing
        try:
            self.equation = self.__buildOperator(equation);
        except Exception as e:
            print e;
            raise TypeError("The input for this operator is not valid");
            
        ### Managing the inhomogeneous term
        # We cast the inhomogeneous term to an element of self.parent()
        # If that is not zero, then we compute the new operator and initial values needed
        # to define the equation.
        if(inhom != 0 ):
            ## Getting the basic elements
            inhom = self.parent()(inhom);
            field = parent.base_field;
            
            ## Getting the homogeneous differential equation
            new_eq = inhom.equation*self.equation;
            
            ## Get the number of elements to check
            ## If init is too big, we use all the elements for a better checking
            n_init = new_eq.get_jp_fo()+1 ;
            to_check = max(n_init, len(init));
            
            ## Getting the matrix of the current equation
            M = Matrix(field, self.equation.get_recursion_matrix(to_check-1 -self.equation.forward_order));
            v = vector(field, inhom.getSequenceList(M.nrows()));
            
            ## Solving the system MX = v
            X = M * BackslashOperator() * v;
            ker = M.right_kernel_matrix();
            
            ## Choosing a solution such X[i]==init[i]
            diff = vector(field, [init[i]-X[i] for i in range(len(init))]);
            N = Matrix(field, [[v[i] for i in range(len(init))] for v in ker]).transpose();

            try:
                to_sum = N * BackslashOperator() * diff;
            except Exception:
                raise ValueError("There is no function satisfying\n(%s)(f) == %s\nwith initial values %s" %(self.equation,inhom,init)); 
            
            ## Putting the new values for the equation and initial values
            init = X+sum([to_sum[i]*ker[i] for i in range(len(to_sum))]);
            init = [init[i]*factorial(i) for i in range(len(init))];
            self.equation = new_eq;
            
        
        ## After creating the original operator, we check we can not extract an "x" factor
        coeff_gcd = 1 ;
        if(is_PolynomialRing(self.parent().base())):
            l = [];
            for el in self.equation.getCoefficients():
                l += el.coefficients(x);
            
            coeff_gcd = gcd(l);
            if(coeff_gcd == 0 ):
                coeff_gcd = 1 ;
        g = coeff_gcd*gcd(self.equation.getCoefficients());
        if(g != 1  and g != 0 ):
            coeffs = [coeff/g for coeff in self.equation.getCoefficients()];
            self.equation = self.__buildOperator(coeffs);
                
        ### Managing the initial values
        init = [self.parent().base_field(str(el)) for el in init];
        if(check_init):
            self.__calculatedSequence = {};
            if(len(init) > self.equation.get_jp_fo()):
                initSequence = [init[i]/factorial(i) for i in range(len(init))];
                M = self.equation.get_recursion_matrix(len(initSequence)-self.equation.forward_order-1 );
                if(M*vector(initSequence) == 0 ):
                    for i in range(len(initSequence)):
                        self.__calculatedSequence[i] = initSequence[i];
                else:
                    raise ValueError("There is no such function satisfying %s whith initial values %s"%(self.equation,init));
            else:
                for i in range(len(init)):
                    try:
                        get_init = self.getInitialValue(i);
                        if(not (get_init == init[i])):
                            raise ValueError("There is no such function satisfying %s whith such initial values (index %d:%s)"%(self.equation,i,init[i]));
                    except TypeError:
                        self.__calculatedSequence[i] = init[i]/factorial(i);
        else:
            self.__calculatedSequence = {i:init[i]/factorial(i) for i in range(len(init))};
        
        
        ### Other attributes for DDFunctions
        ### Setting up the name for the function
        self.__name = name;
        self.__built = None;
            
    def __buildOperator(self, coeffs):
        if(isinstance(coeffs, self.parent().default_operator)):
            return coeffs;
        elif(type(coeffs) == list):
            new_coeffs = [];
            for el in coeffs:
                try:
                    new_coeffs += [self.parent().base()(el)];
                except TypeError:
                    try:
                        new_coeffs += [self.parent().base()(str(el))];
                    except:
                        new_coeffs += [el];
            coeffs = new_coeffs;
                
        return self.parent().default_operator(self.parent().base(), coeffs, self.parent().base_derivation);
        
    def getOperator(self):
        '''
            Getter method for the Linear Differential operator associated with the DDFunction.
        '''
        return self.equation;
        
    def getOrder(self):
        '''
            Getter method for the order of the equation that defines the DDFunction.
        '''
        return self.equation.getOrder();
        
    @derived_property
    def ps_order(self):
        if(self.is_null):
            return -1 ;
        else:
            i = 0 ;
            while(self.getInitialValue(i) == 0 ):
                i += 1 ;
            
            return i;    
        
    def getSequenceElement(self, n):
        try:
            ## If we have computed it, we just return
            return self.__calculatedSequence[n];
        except KeyError:                
            ## Otherwise, we compute such element
            
            
            if(n > self.equation.get_jp_fo()):
                ## If the required value is "too far" we can get quickly the equation
                rec = self.equation.get_recursion_row(n-self.equation.forward_order);
            else:
                ## Otherwise, we try to get as usual the value
                d = self.getOrder();
                i = max(n-d,0 );                      
                rec = self.equation.get_recursion_row(i);
                while(rec[n] == 0  and i <= self.equation.jp_value):                   
                    i += 1 ;                           
                    rec = self.equation.get_recursion_row(i);
                if(rec[n] == 0 ):
                    raise TypeError("Impossible to compute recursively the required value");
                ## Checking that we only need previous elements
                for i in range(n+1 , len(rec)):
                    if(not (rec[i] == 0 )):
                        raise TypeError("Impossible to compute recursively the required value");
            
            ## We do this operation in a loop to avoid computing initial values 
            ## if they are not needed
            res = self.parent().base_field.zero();
            for i in range(n):
                if(not (rec[i] == 0 )):
                    res -= rec[i]*(self.getSequenceElement(i));
                    
            self.__calculatedSequence[n] = self.parent().base_field(res/rec[n]);
            
        return self.__calculatedSequence[n];
        
    def getSequenceList(self, n):
        '''
            Extra method that returns the list of the first `n` initial coefficients of the power-serie expansion of the function. If it is not possible to get so many values, the method DO NOT return an error. It returns just a truncated list.
        '''
        ### We check the argument is correct
        if n < 0 :
            raise ValueError("The argument must be a non-negative integer");
        
        res = [];
        for i in range(n):
            try:
                res += [self.getSequenceElement(i)];
            except TypeError:
                break;
        return res;
        
    def getInitialValue(self, n):
        '''
            Getter method for an initial value.
                - ``n``: order of the initial value expected to obtain, i.e. the return will be `D^n(f)(0)`.
                
            This method can raise an error if the initial value has not been provided and it is impossible to get it.
        '''
        return self.getSequenceElement(n)*factorial(n);
        
    def getInitialValueList(self, n):
        '''
            Extra method that returns the list of the first `n` initial values for the function. If it is not possible to get so many values, the method DO NOT return an error. It returns just a truncated list.
        '''
        ### We check the argument is correct
        if n < 0 :
            raise ValueError("The argument must be a non-negative integer");
        
        res = [];
        for i in range(n):
            try:
                res += [self.getInitialValue(i)];
            except TypeError:
                break;
        return res;
        
    @cached_method
    def size(self):
        to_sum = [self.getOrder()];
        if(isinstance(self.parent().base(), DDRing)):
            to_sum += [el.size() for el in self.equation.getCoefficients()];
        else:
            for coeff in self.equation.getCoefficients():
                try:
                    if(coeff != 0 ):
                        to_sum += [coeff.degree()]
                except Exception:
                    pass;           
        return sum(to_sum);
        
    def built(self):
        return self.__built;
        
    def change_built(self, type, data):
        if(type == "derivative"):
            ## Nothing to check
            pass;
        elif(type == "polynomial"):
            ## Check that the polynomial has appropriate variables
            polynomial, variables = data;
            vars_in_pol = None;
            if(polynomial.parent().is_field()):
                poly_ring = polynomial.parent().base();
                vars_in_pol = tuple(set(poly_ring(polynomial.numerator()).variables()).union(set(poly_ring(polynomial.denominator()).variables())));
            else:
                vars_in_pol = polynomial.variables();
                
            for var in vars_in_pol:
                if(not str(var) in variables):
                    raise TypeError("The variables in the polynomial does not appear in the given map.\n\t- Polynomial: %s\n\t- Map: %s" %(polynomial, variables));
                            
        self.__built = tuple([type,data]);
        
    def change_name(self, new_name):
        self.__name = new_name;
        
    def has_name(self):
        return not(self.__name is None);
            
    #####################################
    ### Arithmetic methods
    #####################################
    def scale_operator(self, r):
        r = self.parent().base()(r);
        
        return self.parent().element(r*self.getOperator(), self.getInitialValueList(self.getOrder()), check_init=False);
        
    def change_init_values(self,newInit,name=None):
        newElement = self.parent().element(self.getOperator(), newInit,name=name);
        
        ## Returning the new created element
        return newElement;
        
    @derived_property
    def inverse(self):
        '''
            Method that compute and return a DD-Function `f` such `f*self == 1`, i.e. this method computes the multiplicative inverse of `self`.
        '''
        if(self.getInitialValue(0 ) == 0 ):
            raise ValueError("Can not invert a function with initial value 0 --> That is not a power serie");
        
        coeffs = self.getOperator().getCoefficients();
        
        ### Computing the new name
        newName = None;
        if(not(self.__name is None)):
            newName = DinamicString("1/(_1)",self.__name);
        if(self.getOrder() == 0 ):
            raise ZeroDivisionError("Impossible to invert the zero function");
        elif(self.getOrder() == 1 ):
            return self.parent().element([-coeffs[0 ],coeffs[1 ]], [1 /self.getInitialValue(0 )], check_init=False, name=newName);
        else:
            newDDRing = DDRing(self.parent());
            return newDDRing.element([self.derivative(), self], [1 /self.getInitialValue(0 )], check_init=False, name=newName);
    
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
            return other;
        elif (other.is_null):
            return self;
                        
        ### Computing the new name
        newName = None;
        if(not(self.__name is None) and (not(other.__name is None))):
            if(other.__name[0 ] == '-'):
                newName = DinamicString("_1_2", [self.__name, other.__name]); 
            else:
                newName = DinamicString("_1+_2", [self.__name, other.__name]); 
                
        
        ## We check other simplifications: if the elements are constants
        if(self.is_constant or other.is_constant):
            result = None;
            if(self.is_constant and other.is_constant):
                parent = self.parent();
                newOperator = [0 ,1 ];
                newInit = [self(0 )+other(0 )];
                result = parent.element(newOperator, newInit, check_init = False, name=newName);
            elif(other.is_constant):
                parent = self.parent();
                newOperator = parent.element(self.equation, inhomogeneous=other(0 )*self.equation.getCoefficient(0 )).equation;
                newInit = [self(0 )+other(0 )] + [self.getInitialValue(i) for i in range(1 ,newOperator.get_jp_fo()+1 )];
                result = parent.element(newOperator, newInit, check_init = False, name=newName);
                result.change_built("polynomial", (PolynomialRing(self.parent().base_field,'x1')("x1+%s" %other(0 )), {'x1':self}));
            elif(self.is_constant):
                parent = other.parent();
                newOperator = parent.element(other.equation, inhomogeneous=self(0 )*other.equation.getCoefficient(0 )).equation;
                newInit = [self(0 )+other(0 )] + [other.getInitialValue(i) for i in range(1 ,newOperator.get_jp_fo()+1 )];
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.change_built("polynomial", (PolynomialRing(self.parent().base_field,'x1')("x1+%s" %self(0 )), {'x1':other}));
            return result;
        
        ## We build the new operator
        if(self.equation == other.equation):
            newOperator = self.equation;
        else:
            newOperator = self.equation.add_solution(other.equation);
            
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 ;
        
        ### Getting as many initial values as posible until the new order
        op1Init = self.getInitialValueList(needed_initial);
        op2Init = other.getInitialValueList(needed_initial);
        newInit = [op1Init[i] + op2Init[i] for i in range(min(len(op1Init),len(op2Init)))];
                   
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName);
        result.change_built("polynomial", (PolynomialRing(self.parent().base_field,['x1','x2'])('x1+x2'), {'x1':self, 'x2': other}));
        return result;
    
    def sub(self, other):
        '''
            Method that substract two DDFunctions.
            
            INPUT:
                - ``other``: a DDFunction which will be substracted to `self`.
                
            WARNING:
                - Whenever an error occurs, a NotImplemented error will be returned in order to Python can make the correspondent call to _rsub_ method of `other` if necessary.
        '''
        if(self.is_null):
            return -other;
        elif (other.is_null):
            return self;
            
            
        ### Computing the new name
        newName = None;
        if(not(self.__name is None) and (not(other.__name is None))):
            newName = DinamicString("_1-_2", [self.__name, other.__name]); 
        
        ## We check other simplifications: if the elements are constants
        if(self.is_constant or other.is_constant):
            result = None;
            if(self.is_constant and other.is_constant):
                parent = self.parent();
                newOperator = [0 ,1 ];
                newInit = [self(0 )-other(0 )];
                result = parent.element(newOperator, newInit, check_init = False, name=newName);
            elif(other.is_constant):
                parent = self.parent();
                newOperator = parent.element(self.equation, inhomogeneous=other(0 )*self.equation.getCoefficient(0 )).equation;
                newInit = [self(0 )-other(0 )] + [self.getInitialValue(i) for i in range(1 ,newOperator.get_jp_fo()+1 )];
                result = parent.element(newOperator, newInit, check_init = False, name=newName);
                result.change_built("polynomial", (PolynomialRing(self.parent().base_field,'x1')("x1-%s" %other(0 )), {'x1':self}));
            elif(self.is_constant):
                parent = other.parent();
                newOperator = parent.element(other.equation, inhomogeneous=self(0 )*other.equation.getCoefficient(0 )).equation;
                newInit = [self(0 )-other(0 )] + [-other.getInitialValue(i) for i in range(1 ,newOperator.get_jp_fo()+1 )];
                result = parent.element(newOperator, newInit, check_init = False, name=newName)
                result.change_built("polynomial", (PolynomialRing(self.parent().base_field,'x1')("-x1+%s" %self(0 )), {'x1':other}));
            return result;
           
        ## We build the new operator
        if(self.equation == other.equation):
            newOperator = self.equation;
        else:
            newOperator = self.equation.add_solution(other.equation);
            
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 ;
        
        ### Getting as many initial values as posible until the new order
        op1Init = self.getInitialValueList(needed_initial);
        op2Init = other.getInitialValueList(needed_initial);
        newInit = [op1Init[i] - op2Init[i] for i in range(min(len(op1Init),len(op2Init)))];
                           
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName);
        result.change_built("polynomial", (PolynomialRing(self.parent().base_field,['x1','x2'])('x1-x2'), {'x1':self, 'x2': other}));
        return result;
    
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
            return 0 ;
        if(self.is_one):
            return other;
        elif(other.is_one):
            return self;
        elif(self.is_constant and other.is_constant):
            return self.getInitialValue(0 )*other.getInitialValue(0 );
        elif(self.is_constant):
            return other.scalar(self.getInitialValue(0 ));
        elif(other.is_constant):
            return self.scalar(other.getInitialValue(0 ));
            
        ### We build the new operator
        newOperator = self.equation.mult_solution(other.equation);
        
        ### Getting the needed initial values for the solution
        needed_initial = newOperator.get_jp_fo()+1 ;
               
        ### Getting as many initial values as posible until the new order
        op1Init = self.getInitialValueList(needed_initial);
        op2Init = other.getInitialValueList(needed_initial);
        newInit = [sum([binomial(i,j)*op1Init[j] * op2Init[i-j] for j in range(i+1 )]) for i in range(min(len(op1Init),len(op2Init)))];
        
        ### Computing the new name
        newName = None;
        if(not(self.__name is None) and (not(other.__name is None))):
            newName = DinamicString("(_1)*(_2)", [self.__name, other.__name]); 
            
        result = self.parent().element(newOperator, newInit, check_init=False, name=newName);
        result.change_built("polynomial", (PolynomialRing(self.parent().base_field,['x1','x2'])('x1*x2'), {'x1':self, 'x2': other}));
        return result;
    
    def scalar(self, r):
        '''
            This method returns the original function multiplied by a constant, i.e. `D(k) = 0`. 
            
            INPUT:
                - ``k``: scalar from the coefficient ring of `self`. It MUST be a constant.
                
            OUTPUT:
                This method will raise TypeError if the value is not a constant. In order to do so, this method will cast the argument into the coefficient ring and try to derivate it. Just if the result is zero, the method will return a new DDFunction representing the function `k\cdot(self)`.
                
            INFO:
                - This method must return always true for the following statements:
                    - ``self.scalar(k) == self.mult(DDFunction.getConstantFunction(k))``.
        '''
        ### We first check if the scalar is zero, because the return is direct.
        if(r == 0 ):
            return self.parent().zero();

        ### Otherwise, we check that the element is a constant or not because the algorithm is 
        ### much easier
        r = self.parent().base()(r);
        if(self.parent().base_derivation(r) == 0 ):
            if(r == 1 ):
                return self;
            n = self.equation.get_jp_fo()+1 ;
            coeffs = self.getOperator().getCoefficients();
            init = self.getInitialValueList(n);
            
            if(isinstance(r, DDFunction)):
                r = r.getInitialValue(0 );
            
            ### Computing the new name
            newName = None;
            if(not(self.__name is None)):
                if(r == -1 ):
                    newName = DinamicString("-(_1)" ,self.__name);
                else:
                    newName = DinamicString("(_1)*(_2)", [repr(r), self.__name]);
                   
            result = self.parent().element(self.equation, [r*el for el in init], check_init=False, name=newName);
            result.change_built("polynomial", (PolynomialRing(self.parent().base_field,['x1'])('(%s)*x1' %repr(r)), {'x1':self}));
            return result;       
        else:
            return self.mult(self.parent()(r));
    
    @derived_property        
    def zero_extraction(self):
        if(self == self.parent().zero()):
            return (0 ,self);
        else:
            n = 0 ;
            while(self.getInitialValue(n) == 0 ):
                n = n+1 ;
                
            X = self.parent().variables()[0 ];
            if(n == 0 ):
                return (0 ,self);
            else:
                d = self.getOrder();
                coeffs = self.getOperator().getCoefficients();
                newEquation = self.parent().element([sum([coeffs[j+l]*(binomial(j+l, j)*falling_factorial(n,l)*X**(n-l)) for l in range(min(n,d-j)+1 )]) for j in range(d+1 )], check_init = False).equation;
            newInit = [factorial(i)*self.getSequenceElement(i+n) for i in range(newEquation.get_jp_fo()+1 )];
            
            ### Computing the new name
            newName = None;
            if(not(self.__name is None)):
                newName = DinamicString("(_1)/(_2^%d)" %n, [self.__name, repr(X)]); 
               
            result = self.parent().element(newEquation, newInit, check_init=False, name=newName);
            result.change_built("polynomial", (PolynomialRing(self.parent().base_field,[repr(X),'x1']).fraction_field()('x1/(%s^%d)' %(repr(X),n)), {repr(X):self.parent()(X),'x1':self}));
            return (n,result);
        
    def divide(self, other):
        if(self.is_null):
            return self.parent().zero();
        if(other.is_constant):
            return self.scalar(1 /other.getInitialValue(0 ));
            
        s_ze = self.zero_extraction;
        o_ze = other.zero_extraction;
        
        if(s_ze[0 ] >= o_ze[0 ]):
            result = self.parent()(x)**(s_ze[0 ]-o_ze[0 ])*(s_ze[1 ]*o_ze[1 ].inverse);
            
            ### Computing the new name
            newName=None;
            if(not(self.__name is None) and (not(other.__name is None))):
                newName = DinamicString("(_1)/(_2)", [self.__name, other.__name]);
                
            result.__name = newName;
            return result;
        else:
            raise ValueError("Impossible perform a division if the x factor of the denominator (%d) is greater than in the numerator (%d)"%(o_ze[0 ],s_ze[0 ]));
            
    def gcd(self, other):
        if(other in self.parent()):
            other = self.parent()(other);
        elif(self in other.parent()):
            return other.gcd(self);
        
        if(self.is_null):
            return other;
        elif(other.is_null):
            return self;
            
        X = self.parent().variables()[0 ];
        
        se = self.zero_extraction;
        oe = other.zero_extraction;
        
        return self.parent()(X**min(se[0 ],oe[0 ])*gcd(se[1 ].getInitialValue(0 ),oe[1 ].getInitialValue(0 )));
    
    #####################################
    ### Differential methods
    #####################################
    def derivative(self, *args):
        '''
        Method to get a DDFunction `g` that satisfies `D(self) = g`.
        
        INPUT:
            - ``args``: ignored input
        '''
        if(self.__derivative is None):
            if(self.is_constant):
                ### Special case: is a constant
                self.__derivative = self.parent()(0 );
            else:
                ### We get the new operator
                newOperator = self.equation.derivative_solution();
            
                ### We get the required initial values (depending of the order of the next derivative)
                initList = self.getInitialValueList(newOperator.get_jp_fo()+2 );
                newInit = [initList[i+1 ] for i in range(min(len(initList)-1 ,newOperator.get_jp_fo()+1 ))];
                
                ### Computing the new name
                newName = None;
                if(not(self.__name is None)):
                    if(self.__name[-1 ] == "'"):
                        newName = DinamicString("_1'", self.__name);
                    else:
                        newName = DinamicString("(_1)'", self.__name); 
                
                ### We create the next derivative with the equation, initial values
                self.__derivative = self.parent().element(newOperator, newInit, check_init=False, name=newName);
                self.__derivative.change_built("derivative",tuple([self]));
                
            
        return self.__derivative;
        
    def integrate(self, constant=0 ):
        '''
        Method to get a DDFunction `g` that satisfies `D(g) = self` and `g(0) = constant`.
        
        INPUT:
            - ``constant``: element which will define the initial value of the returned primitive.
        '''
        ### First we calculate the new linear differential operator
        newOperator = self.equation.integral_solution();
        
        ### We get the initial values for the integral just adding at the begining of the list the constant value
        # If not enough initial values can be given, we create the integral with so many initial values we have
        newInit = [self.parent().base_field(constant)] + self.getInitialValueList(newOperator.get_jp_fo()+1 );
        
        ### Computing the new name
        newName = None;
        if(not(self.__name is None)):
            if(constant == 0 ):
                newName = DinamicString("int(_1)", self.__name); 
            else:
                newName = DinamicString("int(_1) + _2", [self.__name, repr(constant)]);
        
        return self.parent().element(newOperator, newInit, check_init=False, name=newName);
        
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
        if(isinstance(other.parent(), sage.symbolic.ring.SymbolicRing)):
            try:
                other = self.parent().original_ring()(str(other));
            except Exception as e:
                raise TypeError("Impossible to perform a composition with a symbolic element. Try to cast (%s) to some field, polynomial ring or some DDRing" %(other));
            
        ## If we have the basic function we return the same element
        ## Also, if self is a constant, the composition is again the constant
        self_var = self.parent().variables(True)[0 ];
        if(self_var == other or self.is_constant):
            return self;
            
        ## Checking that 'other' at zero is zero
        value = None;
        try:
            value = other(**{str(self_var):0 });
        except Exception as e:
            warnings.warn("Be careful my friend!! Evaluation at zero were not possible!!\nElement %s" %other, DDFunctionWarning, stacklevel=2 );
            raise e;
        if(value != 0 ):
            raise ValueError("Can not compose with a power series with non-zero constant term. Obtained: %s" %(other(**{str(self_var):0 })));
        
        ######################################
        ## Computing the destiny ring
        ######################################
        destiny_ring = None;
        ## First, compute the pushout fo the parents
        from sage.categories.pushout import pushout;
        sp = self.parent(); op = other.parent();
        push = pushout(sp, op);
        
        ## Second, compute the final depth of the DDRing
        if(not isinstance(push, DDRing)):
            raise TypeError("A non DDRing obtained for the composition: that is impossible -- review method _pushout_ of DDRing class");
        if(isinstance(op, DDRing)):
            destiny_ring = push.to_depth(op.depth()+sp.depth());
        else:
            destiny_ring = push.to_depth(sp.depth());
            
        if(destiny_ring.depth() >= 3 ):
            warnings.warn("You are going too deep (depth=%d). The abyss of hell is closer than this function... This may not finish." %destiny_ring.depth(), TooDeepWarning, stacklevel=2 );
            
        ######################################
        ## Computing the new operator
        ######################################
        ## HERE IS THE MAIN RECURSION STEP
        equation = destiny_ring.element([coeff(**{str(self_var) : other}) for coeff in self.equation.getCoefficients()]).equation; ## Equation with coefficients composed with 'other'
        g = destiny_ring.base()(other); ## Casting the element 'other' to the base ring
        
        new_equation = equation.compose_solution(g);
        
        ######################################
        ## Computing the new initial values
        ######################################
        required = new_equation.get_jp_fo()+1 ;
        ## Getting as many initial values as we can and need
        init_f = self.getInitialValueList(required);
        init_g = None;
        try:
            init_g = g.getInitialValueList(required);
        except AttributeError:
            init_g = [0 ] + [factorial(n)*new_equation.base().sequence(g,n) for n in range(1 ,required)];
        ## Computing the new initial values
        new_init = [init_f[0 ]]+[sum([init_f[j]*bell_polynomial(i,j)(*init_g[1 :i-j+2 ]) for j in range(1 ,i+1 )]) for i in range(1 ,min(len(init_f), len(init_g), required))]; ## See Faa di Bruno's formula
        
        
        ######################################
        ## Computing the new name
        ######################################
        new_name = None;
        if(not(self.__name is None)):
            if(isinstance(other, DDFunction) and (not (other.__name is None))):
                new_name = din_m_replace(self.__name, {"x":other.__name}, True);
            elif(not isinstance(other, DDFunction)):
                new_name = din_m_replace(self.__name, {"x":repr(other)}, True);
        
        return destiny_ring.element(new_equation, new_init, name=new_name);
            
    #####################################
    ### Equality methods
    #####################################  
    @derived_property  
    def is_null(self): 
        '''
            Cached property to check whether self is zero in its ring or not.
            
            The method used is comparing the first initial values of the function and check they are zero. If some initial value can not be computed, then False is returned.
        '''
        return self.is_fully_defined and all(self.getInitialValue(i) == 0  for i in range(self.equation.get_jp_fo()+1 ));
        
    @derived_property
    def is_one(self):
        '''
            Cached property to check whether self is one on its ring or not.
            
            The metod used is checking that the element is a constant and its first initial value is one.
        '''
        return (self.is_constant and self.getInitialValue(0 ) == 1 );
        
    @derived_property
    def is_constant(self):
        '''
            Cached property to check whether self is a constant or not.
            
            We check enought initial values to know (without computing the derivative) if it is zero or not.
        '''
        ### OPTION 1
        ## Test zero and if not, check if a constant can be solution
        try:
            if(not self.is_null):
                return self.equation[0 ] == 0  and all(self.getInitialValue(i) == 0  for i in range(1 , self.equation.get_jp_fo()+1 ));
            return True;
        except TypeError:
            return False;
        ### OPTION 2 (nor proved)
        ## Test only initial values for 'self'
        #try:
        #    return all(self.getInitialValue(i) == 0 for i in range(1,self.equation.get_jp_fo()+3));
        #except TypeError:
        #    return False;
        ### OPTION 3 (too costly)
        ## Test the derivative
        #return self.derivative() == 0;
        ### OPTION 4 (too costly)
        ## Test the difference with the cosntant term
        #return (self - self(0)) == 0
    
    @derived_property
    def is_fully_defined(self):
        '''
            Cached property yo check whether the function is fully defined or not.
            
            This means that, given some initial values and the differential equation, the solution of such problem is unique (True) or not (False)
        '''
        max_init = self.equation.get_jp_fo()+1 ;
        return len(self.getInitialValueList(max_init)) == max_init;
        
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
                other = self.parent()(other);
            
            ## Quick check of initial values
            if(not self.quick_equals(other)):
                return False;
            
            ## Special case: trying equality with zero
            if(other.is_null):
                return self.is_null;
            elif(self.is_null):
                return False;
                
            ## Special case with constants
            if(other.is_constant):
                return self.is_constant and self(0 ) == other(0 );
            elif(self.is_constant):
                return False;
                
            if(not (self.is_fully_defined and other.is_fully_defined)):
                return (self.equation == other.equation) and (self.getInitialValueList(self.equation.get_jp_fo()+1 ) == other.getInitialValueList(other.equation.get_jp_fo()+1 ));
             
            ### THREE OPTIONS
            ## 1. Compare with the JP-Values of each function
            #m = self.equation.get_jp_fo()+other.equation.get_jp_fo()+1;
            #if(not all(self.getInitialValue(i) == other.getInitialValue(i) for i in range(m))):
            #    return False;
            
            ## 2. Substract and check zero equality
            return (self-other).is_null;
            
            ## 3. Check adding orders and if they are equal, substract operators and check as many initial values as needed
            #m = self.getOrder()+other.getOrder()+1;
            #if(not all(self.getInitialValue(i) == other.getInitialValue(i) for i in range(m))):
            #    return False;
            #   
            #M = self.equation.add_solution(other.equation).get_jp_fo()+1;
            #return all(self.getInitialValue(i) == other.getInitialValue(i) for i in range(m,M));
        except Exception:
            ### If an error occur, then other can not be substracted from self, so they can not be equals
            return False;
            
    def numerical_solution(self, value, delta=_sage_const_1en10 , max_depth=100 ):
        try:
            ## We try to delegate the computation to the operator (in case of OreOperators)
            if(self.equation.getCoefficients()[-1 ](0 ) != 0 ):
                sol = self.equation.operator.numerical_solution(self.getSequenceList(self.getOrder()), [0 ,value],delta);
                return sol.center(), sol.diameter();
            else:
                return self.__basic_numerical_solution(value, delta, max_depth);
        except AttributeError:
            ## The operator has no numerical solution method (i.e. it is not an OreOperator
            ## We compute the basic numerical approximation
            return self.__basic_numerical_solution(value, delta, max_depth);            
            
    def __basic_numerical_solution(self, value, delta,max_depth):
        res = 0 ;
        to_mult = 1 ;
        to_sum = 0 ;
        step = 0 ;
        find = 0 ;
        while(find < 5  and step < max_depth):
            to_sum = self.getSequenceElement(step)*to_mult;
            res += to_sum;
            if(self.getSequenceElement(step) != 0  and abs(to_sum) < delta):
                find += 1 ;
            elif(self.getSequenceElement(step) != 0 ):
                find = 0 ;
            
            step += 1 ;
            to_mult *= value;
        return float(res),float(abs(to_sum));
        
    def to_symbolic(self):
        evaluation = sage_eval(str(self.__name).replace("'", ".derivative()").replace("^", "**"), locals=globals());
        if(isinstance(evaluation, sage.symbolic.expression.Expression)):
            evaluation = evaluation.simplify_full();
            
        return evaluation;
            
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
                other = self.parent()(other);
                
            m = self.equation.get_jp_fo()+other.equation.get_jp_fo()+1 ;
            return self.getInitialValueList(m) == other.getInitialValueList(m);
        except Exception:
            return False
        
    #####################################
    ### Magic Python methods
    #####################################
    ### Magic arithmetic
    ## Special case for Simbolic Ring
    def __check_symbolic(self, other):
        try:
            if(other.parent() is SR):
                try:
                    return self.parent()(other);
                except:
                    return ParametrizedDDRing(self.parent(),other.variables())(other);
        except Exception as e:
            pass;
        return other;
    
    def __add__(self, other):
        return super(DDFunction,self).__add__(self.__check_symbolic(other));
        
    def __sub__(self, other):
        return super(DDFunction,self).__sub__(self.__check_symbolic(other));
        
    def __mul__(self, other):
        return super(DDFunction,self).__mul__(self.__check_symbolic(other));
        
    def __div__(self, other):
        return super(DDFunction,self).__div__(self.__check_symbolic(other));
        
    def __radd__(self, other):
        return super(DDFunction,self).__add__(self.__check_symbolic(other));
        
    def __rsub__(self, other):
        return super(DDFunction,self).__sub__(self.__check_symbolic(other));
        
    def __rmul__(self, other):
        return super(DDFunction,self).__mul__(self.__check_symbolic(other));
        
    def __rdiv__(self, other):
        return super(DDFunction,self).__div__(self.__check_symbolic(other));
        
    def __iadd__(self, other):
        return super(DDFunction,self).__add__(self.__check_symbolic(other));
        
    def __isub__(self, other):
        return super(DDFunction,self).__sub__(self.__check_symbolic(other));
        
    def __imul__(self, other):
        return super(DDFunction,self).__mul__(self.__check_symbolic(other));
        
    def __idiv__(self, other):
        return super(DDFunction,self).__div__(self.__check_symbolic(other));
    
    
    ## Addition
    
    def _add_(self, other):
        try:
            return self.add(other);
        except Exception:
            return NotImplemented;
            
    ## Substraction
    def _sub_(self, other):
        try:
            return self.sub(other);
        except Exception:
            return NotImplemented;
            
    ## Multiplication
    def _mul_(self, other):
        try:
            if(not isinstance(other, DDFunction)):
                return self.scalar(other);
                
            return self.mult(other);
        except Exception:
            return NotImplemented;
            
    def _div_(self, other):
        try:
            return self.divide(other);
        except ValueError:
            return NotImplemented;
  
    # Integer powering
    def __pow__(self, other):
        try:
            return self.__pows[other];
        except KeyError:
            f = self;
            if(f.is_null): ## Trivial case when order is 0
                self.__pows[other] = f;
            elif(other in ZZ): ## Trying integer power
                other = int(other);
                if(other >= 0 ):
                    a = other >> 1 ;
                    b = a+(other&1 );
                    self.__pows[other] = self.__pow__(a)*self.__pow__(b);
                    newName = None;
                    if(not(self.__name is None)):
                        newName = DinamicString("(_1)^%d" %(other), self.__name);
                    if(isinstance(self.__pows[other], DDFunction)):
                        self.__pows[other].__name = newName;
                else:
                    try:
                        inverse = self.inverse;
                    except Exception:
                        raise ZeroDivisionError("Impossible to compute the inverse");
                    return inverse.__pow__(-other);
            else: ## Trying a power on the basic field
                try:
                    newDDRing = DDRing(self.parent());
                    other = self.parent().base_ring()(other);
                    self.__pows[other] = newDDRing.element([(-other)*f.derivative(),f], [el**other for el in f.getInitialValueList(1 )], check_init=False);
                    
                    newName = None;
                    if(not(self.__name is None)):
                        newName = DinamicString("(_1)^%s" %(other), self.__name);
                    self.__pows[other].__name = newName;
                except TypeError:
                    raise TypeError("Impossible to compute (%s)^(%s) within the basic field %s" %(f.getInitialValue(0 ), other, f.parent().base_ring()));
                except ValueError:
                    raise NotImplementedError("Powering to an element of %s not implemented" %(other.parent()));
        return self.__pows[other];
        
            
    ### Magic equality
    def __eq__(self,other):
        if (other is self):
            return True;
        if((type(other) == sage.rings.integer.Integer or type(other) == int) and other == 0 ):
            return self.is_null;
        return self.equals(other);
        
    ### Magic use
    def __call__(self, X=None, **input):
        '''
            Method that return the value of the function in the point given. As the function as a power-serie may not converge, this method only works if the argument is 0.
            Further implementation can be done for DDFunctions that we know about the convergence.
        '''
        if ((not(X is None)) and X == 0 ):
            return self.getInitialValue(0 );
        
        return self.parent().eval(self, X, **input);
        
    ### Magic representation
    def __hash__(self):
        '''
            Hash method for DDFunctions.
        '''
        return sum(self.getInitialValueList(20));
        #return int("%d%d%d" %(self.getOrder(),self.equation.get_jp_fo(),self.size()));
        #return sum([hash(coeff) for coeff in self.getOperator().getCoefficients()]);

    def __getitem__(self, key):
        '''
            GetItem method for DDFunctions. It allows the user do ``self[i]`` for `i \geq -1`.
            
            INPUT:
                - ``key``: an integer.
            
            RETURN:
                - The result is the coefficient of `D^{key}(f)` on the equation.
        '''
        return self.getOperator().getCoefficient(key);

    def __missing__(self, key):
        '''
            Missing method for DDFuntions.
        '''
        return 0 ;
        
    def __str__(self, detail=True):
        '''
            String method for DDFunctions. It prints all information of the DDFunction.
        '''
        #if(self.is_constant):
        #    return (self.getInitialValue(0)).__str__();
            
        if(detail and (not(self.__name is None))):
            res = "%s %s in %s:\n" %(self.__critical_numbers__(),repr(self),self.parent());
        else:
            res = "%s" %(repr(self));
            if(res[0 ] != '('):
                res += " in %s" %(self.parent());
            res += ":\n";
        res += '-------------------------------------------------\n\t';
        res += '-- Equation (self = f):\n'
        j = 0 ;
        while ((j < self.getOrder()) and (self.getOperator().getCoefficient(j) == 0 )):
            j += 1 ;
        res += self.__get_line__(self.getOperator().getCoefficient(j), j, detail, True);
        for i in range(j+1 ,self.getOrder()+1 ):
            if(self.getOperator().getCoefficient(i) != 0 ):
                res += '\n';
                res += self.__get_line__(self.getOperator().getCoefficient(i), i, detail);

        res += '\n\t\t = 0 \n\t';

        res += '-- Initial values:\n\t'
        res += format(self.getInitialValueList(self.equation.get_jp_fo()+1 ));
        
        res += '\n-------------------------------------------------';
        
        return res;
        
    def __get_line__(self, element, der, detail, first = False):
        res = "";
        string = repr(element);
        crit = None;
        
        ## Getting the basic elements for the line
        if(isinstance(element, DDFunction) and (not(element.__name is None))):
            crit = element.__critical_numbers__();
        else:
            ind = string.find(")")+1 ;
            crit = string[:ind];
            string = string[ind:];
            
        ## Printing critical numbers if detail is required
        if(detail and len(crit) > 0 ):
            res += crit + "\t";
            if(len(res.expandtabs()) < len("\t\t".expandtabs())):
                res += "\t";
        else:
            res += "\t\t";
        
        ## Adding the arithmetic symbol
        if(not(first) and string[0 ] != '-'):
            res += '+ ';
        elif(string[0 ] == '-'):
            res += '- ';
            if(string[1 ] == '('):
                string = string[1 :-1 ];
            else:
                string = string[1 :];
        else:
            res += '  ';
            
        ## Adding the function (with its derivative if needed)
        if(der > 1 ):
            res += "D^%d(f) " %der;
        elif(der == 1 ):
            res += "  D(f) ";
        else:
            res += "    f  ";
        
        ## Adding the coefficient
        if(string != "1"):
            res += "* (%s)" %string;
        
        return res;
        
    def __repr__(self):
        '''
            Representation method for DDFunctions. It prints basic information of the DDFunction.
        '''
        if(self.is_constant):
            return str(self.getInitialValue(0 ));
        if(self.__name is None):
            return "(%s:%s:%s)DD-Function in (%s)" %(self.getOrder(),self.equation.get_jp_fo(),self.size(),self.parent());   
        else:
            return str(self.__name);
            
    def __critical_numbers__(self):
        return "(%d:%d:%d)" %(self.getOrder(),self.equation.get_jp_fo(),self.size());
    
    def _to_command_(self):
        if(self.__name is None):
            return "%s.element(%s,%s)" %(command(self.parent()), _command_list(self.getOperator().getCoefficients()), self.getInitialValueList(self.getOrder()));
        else:
            return "%s.element(%s,%s,name='%s')" %(command(self.parent()), _command_list(self.getOperator().getCoefficients()), self.getInitialValueList(self.getOrder()),str(self.__name));
        
    #####################################       
    ### Other methods
    #####################################    
    def __nonzero__(self):
        return not (self.is_null);
        
#####################################################
### Construction Functor for DD-Ring
#####################################################
class DDRingFunctor (ConstructionFunctor):
    def __init__(self, depth, base_field):
        self.rank = 11 ;
        self.__depth = depth;
        self.__base_field = base_field;
        super(DDRingFunctor, self).__init__(IntegralDomains(),IntegralDomains());
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()));
        if(isinstance(x, DDRing)):
            return x.base();
        return x;
        
    def _apply_functor(self, x):
        return DDRing(x,self.__depth,self.__base_field);
        
    def _repr_(self):
        return "DDRing(*,%d,%s)" %(self.__depth, self.__base_field);
        
    def depth(self):
        return self.__depth;
        
class ParametrizedDDRingFunctor (DDRingFunctor):
    def __init__(self, depth, base_field, var = set([])):
        self.rank = 12 ;
        self.__vars = var;
        super(ParametrizedDDRingFunctor, self).__init__(depth, base_field);
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()));
        return x;
        
    def _repr_(self):
        return "ParametrizedDDRing(*,%s)" %(self.__vars);
        
    def _apply_functor(self, x):
        return ParametrizedDDRing(x, self.__vars);
        
    def merge(self, other):
        if(isinstance(other, ParametrizedDDRingFunctor)):
            return ParametrizedDDRingFunctor(self.__vars.union(other.__vars));
        return None;
        
    def __repr__(self):
        return super(ParametrizedDDRingFunctor, self).__repr__() + " - " + repr(self.__vars);
        
#####################################################
### General Morphism for return to basic rings
#####################################################
class DDSimpleMorphism (sage.categories.map.Map):
    def __init__(self, domain, codomain):
        super(DDSimpleMorphism, self).__init__(domain, codomain);
        
    def _call_(self, p):
        if(isinstance(self.codomain(), DDRing)):
            try:
                return self.codomain().element([self.codomain().base()(coeff) for coeff in p.equation.getCoefficients()], p.getInitialValueList(p.equation.get_jp_fo()+1 ));
            except:
                raise ValueError("Impossible the coercion of element \n%s\n into %s" %(p, self.codomain()))
        if(p.is_constant):
            return self.codomain()(p.getInitialValue(0 ));
        
        raise ValueError("Impossible perform this coercion: non-constant element");

        
        
#####################################       
### Changes to fit the SAGE Categories Framework
#####################################
DDRing.Element = DDFunction;

#####################################
### Extra public methods
#####################################
def zero_extraction(el):
    try:
        R = el.parent();
        if(isinstance(R, DDRing)):
            return el.zero_extraction;
        elif(x in R.gens()):
            n = 0 ;
            val = el(**{'x':0 });
            while(el != R.zero() and val == 0 ):
                n += 1 ;
                el = R(el/x);
                val = el(**{'x':0 });
                
            return (n, el);
    except AttributeError as e:
        return (0 ,el);
        
def polynomial_computation(poly, functions):
    '''
        Method that compute a polynomial operation over a set of DDFunctions.
        
        INPUT:
            - poly: a multivariate polynomial representing the operation we want to perform.
            - functions: the set of functions related with the polynomial. 
        OUTPUT:
            A DDFunction in the corresponding DDRing.
            
        WARNING:
            We assume that for any pair of functions f,g in functions, there are not
            constants c,d such that f = cg+d. Otherwise the result will still
            be correct, but will be computed slower.
    '''
    ### Checking the argument 'poly'
    if(not (is_Polynomial(poly) or is_MPolynomial(poly))):
        raise TypeError("First argument require to be a polynomial.\n\t- Got: %s (%s)" %(poly, type(poly)));
    parent_poly = poly.parent(); gens = parent_poly.gens();
        
    ### Checking the argument 'functions'
    tfunc= type(functions);
    if(not ((tfunc is list) or (tfunc is set) or (tfunc is tuple))):
        functions = [functions];
        
    if(len(functions) < parent_poly.ngens()):
        raise TypeError("Not enough functions given for the polynomial ring of the polynomial.");
    
    ### Coarcing all the functions to a common parent
    parent = functions[0].parent();
    for i in range(1,len(functions)):
        parent = pushout(parent, functions[i].parent());
        
    ### Base case: non-DDRing
    if(not isinstance(parent, DDRing)):
        return poly(**{str(gens[i]) : functions[i] for i in range(len(gens))});
        
    functions = [parent(f) for f in functions];
        
    ### Grouping the elements that are derivatives of each other
    ### Using the assumption on the input functions, we have that for each
    ###    chain of derivatives, we only need to check if the function is
    ###    the derivative of the last or if the first element is the derivative
    ###    of the function.
    chains = [];
    for f in functions:
        inPlace = False;
        for i in range(len(chains)):
            if(f.derivative() == chains[i][0]):
                chains[i] = [f] + chains[i];
                inPlace = True;
                break;
            elif(chains[i][-1].derivative() == f):
                chains[i] = chains[i] + [f];
                inPlace = True;
                break;
        if(not inPlace):
            chains += [[f]];
    dics = {c[0] : [gens[functions.index(f)] for f in c] for c in chains};    
            
    ## We build the new operator
    newOperator = None;
    if(len(dics) == 1):
        if(hasattr(f.equation, "annihilator_of_polynomial")):
            ## Reordering the variables
            parent_poly2 = PolynomialRing(chains[0][0].parent().original_ring(), dics[chains[0][0]]);
            poly2 = parent_poly2(poly);
            newOperator = f.equation.annihilator_of_polynomial(poly2);
    if(newOperator is None):
        newOperator = _get_equation_poly(poly, dics);
            
    ### Getting the needed initial values for the solution
    needed_initial = newOperator.get_jp_fo()+1 ;
        
    ### Getting as many initial values as posible until the new order
    
    newInit = [_get_initial_poly(poly, dics, i) for i in range(needed_initial)];
    ## If some error happens, we delete all results after it
    if(None in newInit):
        newInit = newInit[:newInit.index(None)];
        
    ## Computing the new name
    newName = None;
    if(all(f.has_name() for f in functions)):
        newName = DinamicString(_m_replace(str(poly), {str(gens[i]) : "_%d" %(i+1) for i in range(len(gens))}), [f._DDFunction__name for f in functions]);
        
    ## Building the element
    result = parent.element(newOperator, newInit, check_init=False, name=newName);
    result.change_built("polynomial", (poly, {str(gens[i]) : functions[i] for i in range(len(gens))}));

    return result;

###################################################################################################
### PRIVAME MODULE METHODS
###################################################################################################
def _indices(string, sep):
    try:
        index = string.index(sep);
        return [index] + [el+index+len(sep) for el in _indices(string[index+len(sep):],sep)];
    except ValueError:
        return [];

def _m_indices(string, *seps):
    ## We assume no possible overlapping can occur between elements in seps
    all_index = [];
    for sep in seps:
        all_index += [(el,sep) for el in _indices(string,sep)];
    all_index.sort();
    
    return all_index;

def _m_replace(string, to_replace, escape=("(",")")):
    ## Checking if ther are scape characters
    if(not escape is None):
        pos_init = string.find(escape[0 ]);
        if(pos_init >= 0 ):
            ## Escape initial character found, skipping outside the escape
            pos_end = len(string);
            pos_end = string.rfind(escape[1 ]);
            if(pos_end <= pos_init):
                pos_end = len(string);
                
            return string[:pos_init+1 ] + _m_replace(string[pos_init+1 :pos_end], to_replace, None) + string[pos_end:];
    
    ## No escape characters: doing normal computation
    all_index = _m_indices(string, *to_replace.keys());
    res = ""; current_index = 0 ;
    for el in all_index:
        res += string[current_index:el[0 ]] + to_replace[el[1 ]];
        current_index = el[0 ]+len(el[1 ]);
    res += string[current_index:]
    return res;
    
def _get_equation_poly(poly, dic):  
    '''
        Method that computes the differential equation that the evaluation 
        of a polynomial over some functions satisfies.
        
        This procedure has 5 main steps:
            (1) Compute a vector space $W$ generated by a vector of generators $(g1,...,gk)$
            (2) Compute a derivation matrix $D$ for $W$ w.r.t. the generators
            (3) Compute a initial vector $v_0$ that represents poly in $W$.
            (4) Compute the ansatz system $S$
            (5) Solve the ansatz system
            
        The steps (1), (2), (3) can be done simultaneously in the method _get_derivation_matrix(poly,dic).
        The step (4) use the inductive formula $v_{i+1} = Dv_i + \partial v_i$. Then $S = (v0 | v1 | ...)$.
        The step (5) will be done using Bareiss Algorithm.
    '''
    ### Steps (1)-(3)
    D, v0 = _get_derivation_matrix(poly, dic);
    
    ### Step 4
    R = D[0][0].parent();
    if(sage.rings.fraction_field.is_FractionField(R)):
        R = R.base();
    F = R.fraction_field();
    
    v = [v0];
    for i in range(D.nrows()):
        v += [D*v[-1] + vector(F, [el.derivative() for el in v[-1]])];
        
    S = Matrix(F, v).transpose();
    
    ### Step 5
    ## TODO We rely on the system solver of the operator of the functions we are 
    ## plug-in to the polynomial.
    solution = dic.keys()[0].equation._get_element_nullspace(S);
    
    ## We create the final operator
    return dic.keys()[0].parent().element([el for el in solution]).equation;

def _get_derivation_matrix(poly, dic, simpl = False):
    '''
        Method that computes the derivation matrix of a vector space that
        contains the vector space generated by the evaluation of poly
        using the dictionary dic and a vector that represent poly into 
        that vector space.
        
        
        This method has a recursive structure:
            - If for any key in dic, dic[key][i] appears in poly for i > 0,
            then we simplify the polynomial so it only contains the variables
            dic[key][0]. We return the matrix obtained with that polyomial and 
            the associated vector.
            - If poly has multiple terms, we return the direct sum of the matrices
            for each term and the direct sum of the vectors.
            - If poly is a monomial with multiple variables, we return the Kronecker
            sum of the matrices of the result and the tensor product of the vectors.
            - If poly is a monomial with just one variable, we compute the
            Kronecker sum of the companion matrix associated with the function
            related with that variable degree times and return the vector (1,0,...,0).
        
        WARNING:
            - The argument simpl must never be called with True but within this method
            - The very base case can be improve using the fact that we are computing
            the power of an element.
    '''
    ## Simplification step
    #if(not simpl):
    #    non_simple = sum([dic[key][1:] for key in dic], []);
    #    if(any(var in poly.variables() for var in non_simple)):
    #        to_eval = {}
    #        for key in dic:
    #            current = dic[key];
    #            for i in range(1,len(current)):
    #                to_eval[str(current[i])] = current[0];
    #        D, v = _get_derivation_matrix(poly(**to_eval, dic, simpl=True);
    #        ## TODO
    #        raise DevelopementError("_get_derivation_matrix");
    
    ## From this point on, we can assume only simplified polynomials appears
    ## Case non-monomial
    if(not poly.is_monomial()):
        coeffs = poly.coefficients();
        sols = [_get_derivation_matrix(mon, dic, simpl=True) for mon in poly.monomials()];
        D = Matrix.block_diagonal(*[sol[1] for sol in sols]);
        v = vector(D[0][0].parent(), sum([[coeffs[i]*el for el in sols[i][2]] for i in range(len(sols))], []))
        
        return D,v;
    ## More than one variable
    elif(len(poly.variables()) > 1):
        var = poly.variables()[0];
        deg = poly.degree(var);
        oth = poly.parent()(poly/(var**deg));
        
        D1,v1 = _get_derivation_matrix(var**deg, dic);
        D2,v2 = _get_derivation_matrix(oth, dic);
        
        D = ajpastor.misc.Matrix.kronecker_sum(D1, D2);
        v = vector(v1.parent().base(), sum(([el for el in row] for row in v1.tensor_product(v2)), []));
        
        return D,v;
    ## A power of a variable (using Faa di Bruno's formula)
    elif(len(poly.variables()) == 1):
        var = poly.variables()[0];
        deg = poly.degree();
        ## Getting the function and the offset for the initial values
        func = None;
        for key in dic.keys():
            if(var in dic[key]):
                func = key;
                offset = dic[key].index(var);
                break;
        ## Checking the variable can be easily represent
        if(offset > func.getOrder()):
            raise DevelopementError("_get_derivation_matrix");
        ## TODO Go on from here
        
    
    raise DevelopementError("_get_derivation_matrix");

## TODO Saved function from the console
def get_sequences(a,b):
    M = [[tensor_power(get_vector_prime(n+1),i+1) for i in range(a)] for n in range(b)]
    return [[[list(M[i][j]).index(k^(j+1))+1 for k in [1] + [el for el in primes_first_n(i)]] for j in range(5)] for i in range(5)];

    
__CACHED_INIT_POLY = {};
def _get_initial_poly(poly, dic, m):    
    '''
        Method that computes the ith initial value of the polynomial
        given when evaluated using the dictionary dic.
    '''
    ## Constant case
    if(poly.is_constant()):
        #print "Calling (%s +++ %s +++ %d)" %(poly, dic, m);
        if(m > 0):
            return 0;
        return poly.parent().base()(poly);
    
    ## Non-constant polynomial
    ## Checking the Cache
    global __CACHED_INIT_POLY;
    if(not poly in __CACHED_INIT_POLY):
        __CACHED_INIT_POLY[poly] = [];
    
    found = False;
    for el in __CACHED_INIT_POLY[poly]:
        if(el[0] == dic):
            found = True;
            if(m in el[1]):
                #print "Calling (%s +++ %s +++ %d) -- CACHED" %(poly, dic, m);
                return el[1][m];
            break;
    if(not found):
        __CACHED_INIT_POLY[poly] += [(dic, {})];
    #print "Calling (%s +++ %s +++ %d)" %(poly, dic, m);
        
    result = None;
    ## General case (poly is not a monomial)
    if(not (poly.is_monomial())):
        c = poly.coefficients(); mo = poly.monomials();
        result = sum(c[j]*_get_initial_poly(mo[j],dic,m) for j in range(len(mo)));
        
    ## More than one variable
    elif(len(poly.variables()) > 1):
        var = poly.variables()[0];
        deg = poly.degree(var);
        oth = poly.parent()(poly/(var**deg));
        
        result = sum(binomial(m,k)*_get_initial_poly(var**deg, dic, k)*_get_initial_poly(oth, dic, m-k) for k in range(m+1));
    
    ## A power of a variable (using Faa di Bruno's formula)
    elif(len(poly.variables()) == 1):
        var = poly.variables()[0];
        deg = poly.degree();
        ## Getting the function and the offset for the initial values
        func = None;
        for key in dic.keys():
            if(var in dic[key]):
                func = key;
                offset = dic[key].index(var);
                break;
        
        init = lambda n : func.getInitialValue(offset+n);
        
        ## Computing the final result
        if(m > 0):
            result = sum(falling_factorial(deg,k)*(init(0)**(deg-k))*bell_polynomial(m,k)(*[init(j+1) for j in range(m-k+1)]) for k in range(min(deg,m)+1));
        else:
            result = init(0)**deg;
    
    if(not(result is None)):
        ## Saving the result
        for el in __CACHED_INIT_POLY[poly]:
            if(el[0] == dic):
                el[1][m] = result;
                break;
        return result;
    else:
        raise ValueError("An impossible point was reached");

###################################################################################################
### COMMAND CONVERSION OF DD_FUNCTIONS
###################################################################################################
def command(e):
    try:
        return e._to_command_();
    except AttributeError:
        from sage.rings.polynomial import polynomial_ring as Uni_Polynomial;
        if(e in IntegralDomains()):
            if(e is QQ):
                return "QQ";
            if(Uni_Polynomial.is_PolynomialRing(e)):
                return "PolynomialRing(%s,%s)" %(command(e.base()), [str(var) for var in e.gens()]);
        return str(e);
        
def _command_list(elements):
    res = "[";
    for i in range(len(elements)-1 ):
        res += command(elements[i]) + ", ";
    if(len(elements) > 0 ):
        res += command(elements[-1 ]);
    res += "]";
    
    return res;
    
###################################################################################################
### STANDARD PACKAGES VARIABLES & GETTERS
###################################################################################################

# Some global pre-defined DD-Rings
DFinite = None;
try:
    DFinite = DDRing(PolynomialRing(QQ,x), default_operator=w_OreOperator);
except ImportError:
    ## No ore_algebra package found
    warnings.warn("Package ore_algebra was not found. It is hightly recommended to get this package built by M. Kauers and M. Mezzaroba (http://marc.mezzarobba.net/code/ore_algebra-analytic/ or http://www.kauers.de/software.html)", NoOreAlgebraWarning);
    DFinite = DDRing(PolynomialRing(QQ,x));
DDFinite = DDRing(DFinite);
DFiniteP = ParametrizedDDRing(DFinite, [var('P')]);

def __get_recurrence(f):
    if(not f in DFinite):
        raise TypeError("The function must be holonomic");
    
    f = DFinite(f);
    
    op = f.equation;
    m = max([el.degree() for el in op.getCoefficients()]);
    bound = op.getOrder() + m;
    
    num_of_bck = bound - op.getOrder();
    m = None;
    for i in range(num_of_bck, 0 , -1 ):
        if(op.backward(i) != 0 ):
            m = -i;
            break;
    
    if(m is None):
        for i in range(op.getOrder()+1 ):
            if(op.forward(i) != 0 ):
                m = i;
                break;
    
    n = op._Operator__polynomialRing.gens()[0 ];
    
    rec = [op.get_recursion_polynomial(i)(n=n+m) for i in range(m,op.forward_order + 1 )];
    rec_gcd = gcd(rec);
    rec = [el/rec_gcd for el in rec];
    
    return (rec, f.getSequenceList(op.forward_order-m));
DFinite._DDRing__get_recurrence = __get_recurrence;

###################################################################################################
### PACKAGE ENVIRONMENT VARIABLES
###################################################################################################
__all__ = ["DDRing", "DFinite", "DDFinite", "command", "zero_extraction", "polynomial_computation", "ParametrizedDDRing", "DFiniteP"];
  

