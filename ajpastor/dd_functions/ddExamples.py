
from sage.all_cmdline import *   # import sage library

from sage.rings.polynomial.polynomial_ring import is_PolynomialRing;
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing;

from ajpastor.dd_functions.ddFunction import *;

from ajpastor.misc.dinamic_string import *;

_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_0 = Integer(0); _sage_const_6 = Integer(6);

### Global variables (PUBLIC)
#DFinite_examples = {};
#DDFinite_examples = {};
#
### Global variables (PRIVATE)
#__example_names = {};
#
##################################################################################
##################################################################################
###
### Predefined examples
###
##################################################################################
##################################################################################
#def DD_EXAMPLES_LOAD():
#    global DFinite_examples; global DDFinite_examples;
#    global __example_names;
#
#    s = DFinite.element([_sage_const_1 ,_sage_const_0 ,_sage_const_1 ],[_sage_const_0 ,_sage_const_1 ], name=DinamicString("sin(_1)", "x"));
#    c = DFinite.element([_sage_const_1 ,_sage_const_0 ,_sage_const_1 ],[_sage_const_1 ,_sage_const_0 ], name=DinamicString("cos(_1)", "x"));
#    sh = DFinite.element([-_sage_const_1 ,_sage_const_0 ,_sage_const_1 ],[_sage_const_0 ,_sage_const_1 ], name=DinamicString("sinh(_1)", "x"));
#    ch = DFinite.element([-_sage_const_1 ,_sage_const_0 ,_sage_const_1 ],[_sage_const_1 ,_sage_const_0 ], name=DinamicString("cosh(_1)", "x"));
#    ln = DFinite.element([_sage_const_1 ,_sage_const_0 ,(x+_sage_const_1 )],[_sage_const_0 ,_sage_const_1 ], name=DinamicString("log(_1-1)", "x"));
#    e = DFinite.element([-_sage_const_1 ,_sage_const_1 ],[_sage_const_1 ], name=DinamicString("exp(_1)", "x"));
#    tan = DDFinite.element([-_sage_const_2 ,_sage_const_0 ,c**_sage_const_2 ],[_sage_const_0 ,_sage_const_1 ], name=DinamicString("tan(_1)", "x"));
#    
#    ## Defining D-Finite Examples
#    DFinite_examples['e'] = e;
#    DFinite_examples['ln'] = ln;
#    DFinite_examples['sin'] = s;
#    DFinite_examples['cos'] = c;
#    DFinite_examples['sinh'] = sh;
#    DFinite_examples['cosh'] = ch;
#    P = DFiniteP.parameters()[_sage_const_0 ];
#    DFinite_examples['bessel'] = DFiniteP.element([x**2-P**2,x,x**2], name=DinamicString("bessel_J(_1,_2)", ["P","x"]));
#    DFinite_examples['struve'] = DFiniteP.element([(1-P)*x**2+P**2*(P+1),x*(x**2-P**2-P),(2-P)*x**2,x**3], name=DinamicString("pi*struve_H(_1,_2)", ["P","x"]));
#    DFinite_examples['legendre'] = DFiniteP.element([P*(P+_sage_const_1 ), -_sage_const_2 *x,_sage_const_1 -x**_sage_const_2 ], name=DinamicString("legendre_P(_1,_2)", ["P","x"]));
#    DFinite_examples['chebyshev1'] = DFiniteP.element([P**_sage_const_2 ,-x,(_sage_const_1 -x**_sage_const_2 )], name=DinamicString("chebyshev_T(_1,_2)", ["P","x"]));
#    DFinite_examples['chebyshev2'] = DFiniteP.element([P*(P+_sage_const_2 ),-_sage_const_3 *x,_sage_const_1 -x**_sage_const_2 ], name=DinamicString("chebyshev_U(_1,_2)", ["P","x"]));
#    
#    ## Defining DD-Finite Examples
#    DDFinite_examples['esin'] = DDFinite.element([_sage_const_1 ,-c], [_sage_const_1 ], name=DinamicString("exp(sin(_1))", "x"));
#    DDFinite_examples['sine'] = DDFinite.element([e**_sage_const_2 ,-_sage_const_1 ,_sage_const_1 ],[_sage_const_0 ,_sage_const_1 ], name=DinamicString("sin(exp(_1))", "x"));
#    DDFinite_examples['tan'] = [tan, DDFinite.element([_sage_const_0 ,-_sage_const_2 *s*c,c**_sage_const_2 ], [_sage_const_0 ,_sage_const_1 ], name=DinamicString("tan(_1)", "x"))];
#    DDFinite_examples['bernoulli'] = DDFinite.element([x*e-e+_sage_const_1 ,x*(e-_sage_const_1 )],[_sage_const_1 ,-_sage_const_1 /_sage_const_2 ,_sage_const_1 /_sage_const_6 ,_sage_const_0 ]);
#    
#    ## Defining some names
#    __example_names['exp'] = 'e';
#    __example_names['log'] = 'ln';
#    __example_names['sen'] = 'sin';
#    __example_names['tg'] = 'tan';
#
#def DFinite_example(input, n=_sage_const_0 ):
#    if(DFinite_examples.has_key(input)):
#        res = DFinite_examples[input];
#    elif (__example_names.has_key(input) and DFinite_examples.has_key(__example_names[input])):
#        res = DFinite_examples[__example_names[input]];
#    else:
#        raise ValueError('The DD-Function by name %s does not exist' %(input));
#        
#    if(type(res)==list):
#        return res[n];
#    else:
#        return res;
#    
#
#def DDFinite_example(input, n = _sage_const_0 ):
#    if(DDFinite_examples.has_key(input)):
#        res = DDFinite_examples[input];
#    elif (__example_names.has_key(input) and DDFinite_examples.has_key(__example_names[input])):
#        res = DDFinite_examples[__example_names[input]];
#    else:
#        raise ValueError('The DD-Function by name %s does not exist' %(input));
#        
#    if(type(res)==list):
#        return res[n];
#    else:
#        return res;
#    
#def DDFunction_example(input, n=_sage_const_0 ):
#    try:
#        return DFinite_example(input, n);
#    except Exception:
#        pass;
#    try:
#        return DDFinite_example(input, n);
#    except Exception:
#        pass;
#        
#    raise ValueError('No DD-Function by name %s exist' %(input));

def ddExamples(functions = False, names=False):
    '''
        Welcome to ddExamples documentation. Here we describe the functions
        available in this module. For further information on each function, 
        please access the documentation for that particular function.
        
        All the elements that are returned in this module are DDFunction, i.e.,
        formal power series defined with a linear differential equation and
        some appropriate initial values.
        
        When possible, the functions returned by this module are associated with
        the usual implementation of those functions in SAGE, so using the 
        method "to_symbolic()" returns the same object in the Symbolic Ring.
        
        The functions available in this module are the following:
        
        ** TRIGONOMETRIC FUNCTIONS
            - Sin
            - Cos
            - Tan
            - Sinh
            - Cosh
        ** EXPONENTIAL FUNCTIONS
            - Exp
            - Log
            - Log1
        ** BESSEL TYPE FUNCTIONS (see chapters 10, 11 in https://dlmf.nist.gov)
            - BesselD
            - StruveD
        ** ORTHOGONAL POLRNOMAILS
            - LegendreD (see chapter 14 in https://dlmf.nist.gov)
            - ChebyshevD (see chapter 18 in https://dlmf.nist.gov)
        ** HYPERGEOMETRIC FUNCTIONS (see chapters 15, 16 in https://dlmf.nist.gov)
            - HypergeometricFunction
            - GenericHypergeometricFunction
        ** MATHIEU TYPE FUNCTIONS (see chapter 28 in https://dlmf.nist.gov)
            - MathieuD
            - MathieuSin
            - MathieuCos
            - ModifiedMathieuD
            - ModifiedMathieuSin
            - ModifiedMathieuCos
            - HillD
        ** AIRY'S FUNCTIONS
            - AiryD
        ** PARABOLIC-CYLINDER TYPE FUNCTIONS
            - ParabolicCylinderD
        ** ELLIPTIC INTEGRALS (see chapter 19 in https://dlmf.nist.gov)
            - EllipticLegendreD
        ** SPHEROIDAL WAVE FUNCTIONS (see chapter 30 in https://dlmf.nist.gov)
            - CoulombSpheroidalFunctionD
            - SpheroidalWaveFunctionD
        ** HEUN'S FUNCTIONS (see chapter 31 in https://dlmf.nist.gov)
            - FuschianD
            - HeunD
        ** COULOMB WAVE FUNCTION (see chapter 33 in https://dlmf.nist.gov)
            - CoulombF
    '''
    if(not functions):
        print ddExamples.__doc__;
    else:
        funcs =  [Sin,Cos,Tan,Sinh,Cosh,Exp,Log,Log1,BesselD,StruvD,LegendreD,ChebyshevD,HypergeometricFunction,GenericHypergeometricFunction,MathieuD,MathieuSin,MathieuCos,ModifiedMathieuD,ModifiedMathieuSin,ModifiedMathieuCos,HillD,AiryD,ParabolicCylinderD,EllipticLegendreD,CoulombSpheroidalFunctionD,SpheroidalWaveFunctionD,FuschianD,HeunD,CoulombF];
        
        if(names):
            return [el.__name__ for el in funcs];
        return funcs;
    

##################################################################################
##################################################################################
###
### Trigonometric and Hyperbolic trigonometric Functions
###
##################################################################################
##################################################################################
@cached_function
def Sin(input, ddR = None):
    '''
        D-finite implementation of the Sine function (sin(x)).
        
        References:
            - http://mathworld.wolfram.com/Sine.html
            - https://en.wikipedia.org/wiki/Sine
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    
    if(is_DDFunction(input)):
        return Sin(x)(input);
    f,dR = __decide_parent(input, ddR);
    
    evaluate = lambda p : dR.getSequenceElement(p,_sage_const_0 );
    if(evaluate(f) != _sage_const_0 ):
        raise ValueError("Impossible to compute sin(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([df**_sage_const_3 ,-df2,df],[_sage_const_0 ,evaluate(df),evaluate(df2)], name=DinamicString("sin(_1)", newName)); 

@cached_function    
def Cos(input, ddR = None):
    '''
        D-finite implementation of the Cosine function (cos(x)).
        
        References:
            - http://mathworld.wolfram.com/Cosine.html
            - https://en.wikipedia.org/wiki/Cosine
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Cos(x)(input);
    f,dR = __decide_parent(input, ddR);
    
    evaluate = lambda p : dR.getSequenceElement(p,_sage_const_0 );
    if(evaluate(f) != _sage_const_0 ):
        raise ValueError("Impossible to compute cos(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([df**_sage_const_3 ,-df2,df],[_sage_const_1 ,_sage_const_0 ,-evaluate(df)**_sage_const_2 ], name=DinamicString("cos(_1)",newName)); 

@cached_function
def Tan(input, ddR = None):
    '''
        DD-finite implementation of the Tangent function (tan(x)).
        
        References:
            - http://mathworld.wolfram.com/Tangent.html
            - https://en.wikipedia.org/wiki/Tangent
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Tan(x)(input);
    if(input == x):
        return DDFinite_example('tan');
    g, dR = __decide_parent(input, ddR,_sage_const_2 );
    
    
    evaluate = lambda p : dR.getSequenceElement(p,_sage_const_0 );
    if(evaluate(g) != _sage_const_0 ):
        raise ValueError("Impossible to compute tan(f) with f(0) != 0");
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg);
    a = Cos(input)**_sage_const_2 ; b = dR.base().zero(); c = dR.base()(-_sage_const_2 );
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([dg**_sage_const_3 *c,dg**_sage_const_2 *b-ddg*a,dg*a]).equation;
        
    ### Now, we compute the initial values required
    required = newOperator.get_jp_fo()+_sage_const_1 ;
        
    init_tan = Tan(x).getInitialValueList(required);
    init_input = [factorial(i)*dR.base().getSequenceElement(g,i) for i in range(required)];
        
    newInit = [init_tan[_sage_const_0 ]]+[sum([init_tan[j]*bell_polynomial(i,j)(*init_input[_sage_const_1 :i-j+_sage_const_2 ]) for j in range(_sage_const_1 ,i+_sage_const_1 )]) for i in range(_sage_const_1 ,required)]; ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit);
    
    newName = repr(input);
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name;
    
    result._DDFunction__name = DinamicString("tan(_1)",newName);
    return result;

@cached_function    
def Sinh(input, ddR = None):
    '''
        DD-finite implementation of the Hyperbolic Sine function (sinh(x)).
        
        References:
            - http://mathworld.wolfram.com/HyperbolicSine.html
            - https://en.wikipedia.org/wiki/Hyperbolic_function
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Sinh(x)(input);
    f,dR = __decide_parent(input, ddR);
    
    evaluate = lambda p : dR.getSequenceElement(p,_sage_const_0 );
    if(evaluate(f) != _sage_const_0 ):
        raise ValueError("Impossible to compute sin(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([-df**_sage_const_3 ,-df2,df],[_sage_const_0 ,evaluate(df),evaluate(df2)], name=DinamicString("sinh(_1)",newName)); 

@cached_function    
def Cosh(input, ddR = None):
    '''
        DD-finite implementation of the Hyperbolic Cosine function (cosh(x)).
        
        References:
            - http://mathworld.wolfram.com/HyperbolicCosine.html
            - https://en.wikipedia.org/wiki/Hyperbolic_function
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Cosh(x)(input);
    f,dR = __decide_parent(input, ddR);
    
    evaluate = lambda p : dR.getSequenceElement(p,_sage_const_0 );
    if(evaluate(f) != _sage_const_0 ):
        raise ValueError("Impossible to compute cos(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([-df**_sage_const_3 ,-df2,df],[_sage_const_1 ,_sage_const_0 ,evaluate(df)**_sage_const_2 ], name=DinamicString("cosh(_1)", newName)); 

##################################################################################
##################################################################################
###
### Exponential and Logarithm Functions
###
##################################################################################
##################################################################################   
@cached_function  
def Log(input, ddR = None):
    '''
        DD-finite implementation of the Logarithm function (ln(x)).
        
        References:
            - http://mathworld.wolfram.com/Logarithm.html
            - https://en.wikipedia.org/wiki/Logarithm
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression such the evaluation x=0 gives 1.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must evaluate to 1 when the main variable is 0.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 1.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Log(x+_sage_const_1 )(input);
    f,dR = __decide_parent(input, ddR);
    
    evaluate = lambda p : dR.getSequenceElement(p,_sage_const_0 );
    if(evaluate(f) != _sage_const_1 ):
        raise ValueError("Impossible to compute ln(f) with f(0) != 1");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([_sage_const_0 ,df**_sage_const_2 -df2*f,df*f],[_sage_const_0 ,evaluate(df), evaluate(df2)-evaluate(df)**_sage_const_2 ], name=DinamicString("log(_1)",newName));
    
@cached_function 
def Log1(input, ddR = None):
    '''
        DD-finite implementation of the shifted Logarithm function (ln(x+1)). It is equivalent to Log(input+1).
        
        References:
            - http://mathworld.wolfram.com/Logarithm.html
            - https://en.wikipedia.org/wiki/Logarithm
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression such the evaluation x=0 gives 0.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must evaluate to 0 when the main variable is 0.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Log1(x)(input);
    f,dR = __decide_parent(input, ddR);
    
    evaluate = lambda p : dR.getSequenceElement(p,_sage_const_0 );
    if(evaluate(f) != _sage_const_0 ):
        raise ValueError("Impossible to compute cos(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    f1 = f+_sage_const_1 ;
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([_sage_const_0 ,df**_sage_const_2 -df2*f1,df*f1],[_sage_const_0 ,evaluate(df), evaluate(df2)-evaluate(df)**_sage_const_2 ], name=DinamicString("log(_1+1)", newName)); 
    
@cached_function 
def Exp(input, ddR = None):
    '''
        DD-finite implementation of the Exponential function (exp(x)).
        
        References:
            - http://mathworld.wolfram.com/ExponentialFunction.html
            - https://en.wikipedia.org/wiki/Exponential_function
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression such the evaluation x=0 gives 0.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must evaluate to 0 when the main variable is 0.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Exp(x)(input);
    f,dR = __decide_parent(input, ddR);
    
    evaluate = lambda p : dR.getSequenceElement(p,_sage_const_0 );
    if(evaluate(f) != _sage_const_0 ):
        raise ValueError("Impossible to compute exp(f) with f(0) != 0");
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
        
    return dR.element([-dR.base_derivation(f),_sage_const_1 ],[_sage_const_1 ], name=DinamicString("exp(_1)", newName));

##################################################################################
##################################################################################
###
### Special Functions
###
##################################################################################
##################################################################################    
##### BESSEL TYPE FUNCTIONS
### Bessel Functions
@cached_function 
def BesselD(input = 'P', kind = _sage_const_1 ):
    '''
        DD-finite implementation of the Bessel functions (J_n(x), Y_n(x)).
        
        References:
            - https://dlmf.nist.gov/10.2
            - https://en.wikipedia.org/wiki/Bessel_function
            - http://mathworld.wolfram.com/BesselFunction.html
            
        This method returns a function in the appropriate DD-Ring satisfying the differential equation
            x^2 f'' + xf' + (x^2-P^2)f = 0
        where 'x' is the variable and 'P' is a constant parameter (i.e. P' = 0).
        
        INPUT:
            - input: the parameter 'n' for the Bessel differential equation. Currently, only non-negative integer are allowed. If no value is given, then the symbolic Bessel function (only with an equation) is returned with parameter "P". The input can also be a string with a name for the parameter or a polynomial expression involving parameters.
            - kind: the kind of bessel function the user want to get (default 1). It can take tha values 1 or 2. Currently, only the first kind is fully implemented.
        
        WARNING:
            - For power series solution this function only have non-zero solutions when the argument 'input' is a non-negative integer. Hence, initial values will also be computed for the parameter values that have power series solutions.
            - The implementation will say that the symbolic Bessel function is the zero function for non-negative values of the parameter. In any case, the method 'to_symbolic' will return the appropriate SAGE function.
            - When evaluating parameters, the initial values will not update and must be set by hand.
    '''
    parent, par = __check_list([input], DFinite.variables());
    par = par[0];
        
    if(parent is QQ):
        parent = DFinite;
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
        par = parent.base()(par);
    x = parent.variables()[0];
        
    if(kind == _sage_const_1 ):
        func = parent.element([x**2-par**2, x, x**2], name=DinamicString("bessel_J(_1,_2)", [repr(par),"x"]));
        if(par in ZZ):
            alpha = ZZ(par);
            func = func.change_init_values([_sage_const_0  for i in range(alpha)] + [_sage_const_1 /_sage_const_2 **alpha, _sage_const_0 , -((alpha+_sage_const_2 )/(_sage_const_2 **(alpha+_sage_const_2 )))], name = func._DDFunction__name);
    elif(kind == _sage_const_2 ):
        func = parent.element([x**2-par**2, x, x**2], name=DinamicString("bessel_Y(_1,_2)", [repr(par),"x"]));
    else:
        raise ValueError("Impossible to manage Bessel functions of %sth kind" %(kind));
    
    return func;
    
### Struve's functions
@cached_function
def StruveD(mu='P',kind=1):
    '''
        DD-finite implementation of the Struve functions (J_n(x), Y_n(x)).
        
        References:
            - https://dlmf.nist.gov/11.2
            - https://en.wikipedia.org/wiki/Struve_function
            - http://mathworld.wolfram.com/StruveFunction.html
            
        Struve functions are the solutions for the inhomogeneous Bessel differential equation
        and have also a parameter 'P' involved:
            x^2 f'' + xf' + (x^2-P^2)f = (1/sqrt(pi)*gamma(P+1/2))*(x/2)^(P-1)
            
        This equation can be write as an homogeneous differential equation of order 3:
        (1-P)*x**2+P**2*(P+1),x*(x**2-P**2-P),(2-P)*x**2,x**3
            x^3f^(3) + (2-P)x^2f'' + x(x^2-P^2-P)f' + ((1-P)x^2 + P^3+ P^2)f = 0.
            
        Following the definition that we can find in the references above, we have that the Struve
        function only have power series solutions for integers parameters greater than -1. Then the first 
        non-zero value of the power serie has a factor of 'pi'. To avoid adding the element 'pi' to the
        coefficients, we work with the function f_mu(x) = pi*H_mu(x).
        
        INPUT:
            - input: the parameter 'mu' for the Struve differential equation. Currently, only integers greater than -2 are allowed. If 'None' is given, then the symbolic Struve function (only with an equation) is returned with parameter "P". The input can also be a string with a name for the parameter or a polynomial expression involving parameters.
            - kind: the kind of Struve function the user want to get (default 1). It can take the values 1 or 2. Currently, only the first kind is fully implemented.
        
        WARNING:
            - Initial values will also be computed for the parameter values that have power series solutions.
            - The implementation will say that the symbolic Bessel function is the zero function for non-negative values of the parameter. In any case, the method 'to_symbolic' will return the appropriate SAGE function.
            - When evaluating parameters, the initial values will not update and must be set by hand.
        
    '''
    parent, par = __check_list([mu], DFinite.variables());
    par = par[0];
    
    if(kind != 1):
        raise TypeError("Only struve_H functions are implemented");
        
    if(parent is QQ):
        parent = DFinite;
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    f = parent.element([(1-par)*x**2+par**2*(par+1),x*(x**2-par**2-par),(2-par)*x**2,x**3], name=DinamicString("pi*struve_H(_1,_2)", [repr(par),"x"]));
    if(par in ZZ and par >= 0):
        num = factorial(par+_sage_const_1)*pi*(_sage_const_1/_sage_const_2)**(par+_sage_const_1);
        den = gamma(_sage_const_3/_sage_const_2)*gamma(par+_sage_const_3/_sage_const_2);
        val = QQ(num/den);
        f = f.change_init_values([0 for i in range(par+1)] + [val], name=f._DDFunction__name);
    
    return f;


###### ORTHOGONAL POLYNOMIALS
### Legendre Polynomials 
__legendre_initials = [[_sage_const_1 ,_sage_const_0 ],[_sage_const_0 ,_sage_const_1 ]];   
@cached_function 
def LegendreD(input):
    '''
        D-finite implementation of the Legendre polynomials (P_n(x))
        
        References:
            - https://dlmf.nist.gov/18.3
            - https://en.wikipedia.org/wiki/Legendre_polynomials
            - http://mathworld.wolfram.com/LegendrePolynomial.html
            
        TODO
    '''
    global __legendre_initials;
    if(input is None):
        return DDFunction_example('legendre');

    try:
        n = ZZ(input);
        if(n < _sage_const_0 ):
            raise ValueError("Impossible to create a Legendre polynomial of negative index");
            
        P = DFiniteP.parameters()[_sage_const_0 ];  
        func = DDFunction_example('legendre')(**{str(P):n});
        for i in range(len(__legendre_initials), n+_sage_const_1 ):
            prev = __legendre_initials[-_sage_const_1 ];
            prev2 = __legendre_initials[-_sage_const_2 ];
            __legendre_initials += [[-(i-_sage_const_1 )*prev2[_sage_const_0 ]/i,((_sage_const_2 *i-_sage_const_1 )*prev[_sage_const_0 ] - (i-_sage_const_1 )*prev2[_sage_const_1 ])/i]];
        return func.change_init_values(__legendre_initials[n], name=DinamicString("legendre_P(_1,_2)", [str(input), "x"]));
    except TypeError as e:
        #raise TypeError("Impossible to create a Legendre polynomial of rational index");
        raise e;

### Chebyshev Polynomials        
__chebyshev_initials = [[],[[_sage_const_1 ,_sage_const_0 ],[_sage_const_0 ,_sage_const_1 ]],[[_sage_const_1 ,_sage_const_0 ],[_sage_const_0 ,_sage_const_2 ]]];
@cached_function    
def ChebyshevD(input, kind = _sage_const_1 ):
    '''
        D-finite implementation of the Chebyshev polynomials (T_n(x), U_n(x))
        
        References:
            - https://dlmf.nist.gov/18.3
            - https://en.wikipedia.org/wiki/Chebyshev_polynomials
            - http://mathworld.wolfram.com/ChebyshevPolynomialoftheFirstKind.html & http://mathworld.wolfram.com/ChebyshevPolynomialoftheSecondKind.html
            
        TODO
    '''
    global __chebyshev_initials;
    if(input is None):
        return DDFunction_example('chebyshev%d' %kind);

    try:
        n = ZZ(input);
        if(n < _sage_const_0 ):
            raise ValueError("Impossible to create a Legendre polynomial of negative index");
            
        P = DFiniteP.parameters()[_sage_const_0 ];
        ## Building the differential equation
        name = None;
        if(kind == _sage_const_1 ):
            func = DDFunction_example('chebyshev1')(**{str(P):n});
            name = DinamicString("chebyshev_T(_1,_2)", [str(input), "x"]);
        elif(kind == _sage_const_2 ):
            func = DDFunction_example('chebyshev2')(**{str(P):n});
            name = DinamicString("chebyshev_U(_1,_2)", [str(input), "x"]);
        else:
            raise ValueError("Impossible to manage Chebyshev polynomial of %d-th kind" %(kind));
            
        ## Computing initial values
        for i in range(len(__chebyshev_initials[kind]), n+_sage_const_1 ):
            prev = __chebyshev_initials[kind][-_sage_const_1 ];
            prev2 = __chebyshev_initials[kind][-_sage_const_2 ];
            __chebyshev_initials[kind] += [[-prev2[_sage_const_0 ], _sage_const_2 *prev[_sage_const_0 ]-prev2[_sage_const_1 ]]];
        return func.change_init_values(__chebyshev_initials[kind][n],name);
    except TypeError as e:
        raise e;    

###### HYPERGEOMETRIC FUNCTIONS
### Hypergeometric Functions
__CACHED_HYPERGEOMETRIC = {};

def HypergeometricFunction(a,b,c, init = _sage_const_1 ):
    '''
        D-finite implementation of the Gauss Hypergeometric function
        
        References:
            - https://dlmf.nist.gov/15
            - https://en.wikipedia.org/wiki/Hypergeometric_function
            - http://mathworld.wolfram.com/HypergeometricFunction.html
            
        TODO
    '''
    return GenericHypergeometricFunction([a,b],[c],init);

def GenericHypergeometricFunction(num=[],den=[],init=_sage_const_1 ):
    '''
        D-finite implementation of the Generalized Hypergeometric Functions qFp(a_1,...,a_q;b_1,...,b_m;x)
        
        References:
            - https://dlmf.nist.gov/16
            - https://en.wikipedia.org/wiki/Generalized_hypergeometric_function
            - http://mathworld.wolfram.com/GeneralizedHypergeometricFunction.html
            
        TODO
    '''
    ## Checking arguments: num
    if (not (isinstance(num,list) or isinstance(num,set) or isinstance(num,tuple))):
        num = [num];
    else:
        num = list(num);
    if (not (isinstance(den,list) or isinstance(den,set) or isinstance(den,tuple))):
        den = [den];
    else:
        den = list(den);
        
    parent, new_all = __check_list(num+den, [str(el) for el in DFinite.variables()]);
    num = new_all[:len(num)];
    den = new_all[len(num):];
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DFinite;
        
    ## Cleaning repeated values 
    i = _sage_const_0 ;
    while(i < len(num) and len(den) > _sage_const_0 ):
        if(num[i] in den):
            den.remove(num[i]);
            num.remove(num[i]);
        else:
            i += _sage_const_1 ;
    
    ## Sort list for cannonical input
    num.sort(); den.sort();
    
    ## Casting to tuples to have hash  
    num = tuple(num); den = tuple(den);
    
    ## Checking the function is cached
    global __CACHED_HYPERGEOMETRIC;
    if(not((num,den,init) in __CACHED_HYPERGEOMETRIC)):
        ## Building differential operator
        get_op = lambda p : destiny_ring.element(p).equation;
        op_num = x*prod(get_op([el,x]) for el in num);
        op_den = x*get_op([_sage_const_0 ,_sage_const_1 ])*prod(get_op([el-_sage_const_1 ,x]) for el in den);
        op = op_num - op_den;
        
        f = destiny_ring.element(op);
        
        initVals = [init];
        
        if(init == _sage_const_1 ):
            __CACHED_HYPERGEOMETRIC[(num,den,init)] = f.change_init_values([_sage_const_1 ],name=DinamicString("hypergeometric(_1,_2,_3)", [str(num),str(den),"x"]));
        else:
            __CACHED_HYPERGEOMETRIC[(num,den,init)] = f.change_init_values([init],name=DinamicString("%d*(hypergeometric(_1,_2,_3))", [str(num),str(den),"x"]));
        
    ## Return the cached element
    return __CACHED_HYPERGEOMETRIC[(num,den,init)];
    
###### MATHIEU TYPE FUNCTIONS
### Mathieu's Functions
@cached_function
def MathieuD(a=None,q=None,init=()):
    '''
        DD-finite implementation of the Matheiu function
        
        References:
            - https://dlmf.nist.gov/28.2
            - https://en.wikipedia.org/wiki/Mathieu_function
            - http://mathworld.wolfram.com/MathieuFunction.html
            
        TODO
    '''
    params =[];
    if(a is None):
        params += ['a'];
    if(q is None):
        params += ['q'];
    
    destiny_ring = DDFinite; ra = a; rq = q;
    if(len(params) > _sage_const_0 ):
        destiny_ring = ParametrizedDDRing(destiny_ring, params);
        if('a' in params):
            ra = destiny_ring.parameter('a');
        if('q' in params):
            rq = destiny_ring.parameter('q');
        
    return destiny_ring.element([ra-_sage_const_2 *rq*Cos(_sage_const_2 *x), _sage_const_0 , _sage_const_1 ], init, name=DinamicString("Mathieu(_1,_2;_3)(_4)", [repr(ra),repr(rq),str(list(init[:_sage_const_2 ])),"x"]));

@cached_function
def MathieuSin(a=None,q=None):
    '''
        DD-finite implementation of the Mathieu Sine function.
        
        References:
            - https://dlmf.nist.gov/28.2
            - https://en.wikipedia.org/wiki/Mathieu_function
            - http://mathworld.wolfram.com/MathieuFunction.html
            
        This is the sine function with the Mathieu equation (i.e., with initial values
        0 an 1). It is equivalent to MathieuD(a,q,(0,1)).
    '''
    return MathieuD(a,q,(_sage_const_0 ,_sage_const_1 ));
    
@cached_function
def MathieuCos(a=None,q=None):
    '''
        DD-finite implementation of the Mathieu Cosine function.
        
        References:
            - https://dlmf.nist.gov/28.2
            - https://en.wikipedia.org/wiki/Mathieu_function
            - http://mathworld.wolfram.com/MathieuFunction.html
            
        This is the cosine function with the Mathieu equation (i.e., with initial values
        1 an 0). It is equivalent to MathieuD(a,q,(1,0)).
    '''
    return MathieuD(a,q,(_sage_const_1 ,_sage_const_0 ));

### Modified Mathieu's Functions
@cached_function
def ModifiedMathieuD(a=None,q=None,init=()):
    '''
        DD-finite implementation of the Modified Matheiu functions.
        
        References:
            - hhttps://dlmf.nist.gov/28.20
            - https://en.wikipedia.org/wiki/Mathieu_function
            
        TODO
    '''
    params =[];
    if(a is None):
        params += ['a'];
    if(q is None):
        params += ['q'];
    
    destiny_ring = DDFinite; ra = a; rq = q;
    if(len(params) > _sage_const_0 ):
        destiny_ring = ParametrizedDDRing(destiny_ring, params);
        if('a' in params):
            ra = destiny_ring.parameter('a');
        if('q' in params):
            rq = destiny_ring.parameter('q');
        
    return destiny_ring.element([ra-_sage_const_2 *rq*Cosh(_sage_const_2 *x), _sage_const_0 , _sage_const_1 ], init, name=DinamicString("ModMathieu(_1,_2;_3)(_4)", [repr(ra),repr(rq),str(list(init[:_sage_const_2 ])),"x"]));

@cached_function
def ModifiedMathieuSin(a=None,q=None):
    '''
        DD-finite implementation of the Modified Matheiu functions.
        
        References:
            - hhttps://dlmf.nist.gov/28.20
            - https://en.wikipedia.org/wiki/Mathieu_function
            
        This is the sine function with the Mathieu equation (i.e., with initial values
        0 an 1). It is equivalent to ModifiedMathieuD(a,q,(0,1)).
    '''
    return ModifiedMathieuD(a,q,(_sage_const_0 ,_sage_const_1 ));
    
@cached_function
def ModifiedMathieuCos(a=None,q=None):
    '''
        DD-finite implementation of the Modified Matheiu functions.
        
        References:
            - hhttps://dlmf.nist.gov/28.20
            - https://en.wikipedia.org/wiki/Mathieu_function
            
        This is the cosine function with the Mathieu equation (i.e., with initial values
        1 an 0). It is equivalent to ModifiedMathieuD(a,q,(1,0)).
    '''
    return ModifiedMathieuD(a,q,(_sage_const_1 ,_sage_const_0 ));

### Hill's equation
@cached_function
def HillD(a=None,q=None,init=()):
    '''
        DD-finite implementation of the Hill equation.
        
        References:
            - https://dlmf.nist.gov/28.29
            - https://en.wikipedia.org/wiki/Hill_differential_equation
            - http://mathworld.wolfram.com/HillsDifferentialEquation.html
            
        TODO
    '''
    params =[];
    destiny_ring = DFinite;
    
    if(a is None):
        params += ['a'];
    if(q is None):
        params += ['q'];
    elif(isinstance(q.parent(), DDRing)):
        destiny_ring = q.parent().to_depth(q.parent().depth()+1);
    else:
        q,destiny_ring = __decide_parent(q);
        
    ra = a; rq = q;
    if(len(params) > _sage_const_0 ):
        destiny_ring = ParametrizedDDRing(destiny_ring, params);
        if('a' in params):
            ra = destiny_ring.parameter('a');
        if('q' in params):
            rq = destiny_ring.parameter('q');
        
    return destiny_ring.element([ra+rq, _sage_const_0 , _sage_const_1 ], init, name=DinamicString("HillEq(_1,_2;_3)(_4)", [repr(ra),repr(rq),str(list(init[:_sage_const_2 ])),"x"]));

###### AIRY TYPE FUNCTIONS
### Airy's functions
@cached_function
def AiryD(init=()):
    '''
        D-finite implementation of the Airy's functions (Ai(x), Bi(x)).
        
        References:
            - https://dlmf.nist.gov/9.2
            - https://en.wikipedia.org/wiki/Airy_function
            - http://mathworld.wolfram.com/AiryFunctions.html
            
        TODO
    '''
    name = None;
    if(len(init) >= 2): ## Complete Airy function, we can build the name
        ## Rejecting the zero case
        if(init[0] == init[1] and init[0] == 0):
            return DFinite.zero();
        
        ## Simplifying the name if there is zero coefficients
        if(init[0] != 0):
            name_a1 = "(3**(2/3)*gamma(2/3))*%s" %init[0];
            name_b1 = "(3**(1/3)*gamma(2/3))*%s" %init[0];
        else:
            name_a1 = "";
            name_b1 = "";
        if(init[1] != 0):
            name_a2 = "-(3**(1/3)*gamma(1/3))*%s" %init[1];
            name_b2 = "+(gamma(1/3))*%s" %init[1];
        else:
            name_a2 = "";
            name_b2 = "";
            
        ## Building the final name
        name = DinamicString("((%s%s)/2)*airy_ai(_1) + ((%s%s)/(2*3**(1/6)))*airy_bi(_1)" %(name_a1, name_a2, name_b1, name_b2), ["x"]);
    return DFinite.element([-x,0,1], init, name=name);


###### PARABOLIC-CYLINDER TYPE FUNCTIONS
### Parabolic Cylinder Functions
@cached_function
def ParabolicCylinderD(a=None,b=None,c=None, init=()):
    '''
        D-finite implementation of Parabolic Cylinder functions.
        
        References:
            - https://dlmf.nist.gov/12.2
            - https://en.wikipedia.org/wiki/Parabolic_cylinder_function
            - http://mathworld.wolfram.com/ParabolicCylinderDifferentialEquation.html
            
        TODO
    '''
    params =[];
    if(a is None):
        params += ['a'];
    if(b is None):
        params += ['b'];
    if(c is None):
        params += ['c'];
    
    destiny_ring = DFinite; ra = a; rb = b; rc = c;
    if(len(params) > _sage_const_0 ):
        destiny_ring = ParametrizedDDRing(DFinite, params);
        if('a' in params):
            ra = destiny_ring.parameter('a');
        if('b' in params):
            rb = destiny_ring.parameter('b');
        if('c' in params):
            rc = destiny_ring.parameter('c');
    return destiny_ring.element([(rc+rb*x+ra*x**2),0,1], init, name=DinamicString("ParabolicCylinder(_1,_2,_3;_4)", [repr(ra), repr(rb), repr(rc), "x"]));
    
###### ELLIPTIC INTEGRALS
## Legendre elliptic integrals
def EllipticLegendreD(kind,var='phi'):
    '''
        DD-finite implementation of the Legendre elliptic integrals (F(phi,k), E(phi,k), D(phi,k)
        
        References:
            - https://dlmf.nist.gov/19.2
            - https://en.wikipedia.org/wiki/Legendre_form
            - http://mathworld.wolfram.com/EllipticIntegraloftheFirstKind.html & http://mathworld.wolfram.com/EllipticIntegraloftheSecondKind.html & http://mathworld.wolfram.com/EllipticIntegraloftheThirdKind.html
            
        TODO
    '''
    if(kind not in [0,1,2]):
        raise ValueError("The kind of legendre elliptic integral is not valid. Required 0,1 or 2");
    if(str(var) not in ['m','phi']):
        raise ValueError("The variable for taking the equation must be 'm' or 'phi'");
        
    var = str(var);
    if(var == 'm'):
        if(kind == 1):
            name = DinamicString("(2/pi)*elliptic_f(pi/2,_1)", ["x"]);
            return DFinite.element([-x,(1-3*x**2), x*(1-x**2)],[1], name=name);
        elif(kind == 2):
            name = DinamicString("(2/pi)*elliptic_e(pi/2,_1)", ["x"]);
            return DFinite.element([x,(1-x**2), x*(1-x**2)],[1], name=name);
        else:
            return (EllipticLegendreD(1,var)-EllipticLegendreD(2,var))/x**2;
            
    if(var == 'phi'):
        DDFiniteP = DFiniteP.to_depth(2);
        P = DDFiniteP.parameters()[0];
        s = DFiniteP(Sin(x));
        c = DFiniteP(Cos(x));
        if(kind == 1):
            name = DinamicString("(2/pi)*elliptic_f(_2,_1)", [repr(P),"x"]);
            return DDFiniteP.element([0,-P**2*s*c,1-P**2*s**2], [0,1], name=name);
        elif(kind == 2):
            name = DinamicString("(2/pi)*elliptic_e(_2,_1)", [repr(P),"x"]);
            return DDFiniteP.element([0,P**2*s*c,1-P**2*s**2], [0,1], name=name);
        else:
            return (EllipticLegendreD(1,var)-EllipticLegendreD(2,var))/P**2;
        
###### SPHEROIDAL WAVE FUNCTIONS
## Generalized (or Coulomb) Spheroidal Differential Equation
@cached_function
def CoulombSpheroidalFunctionD(a=None, b=None, c=None, d=None, kind = 1, init=()):
    '''
        D-finite implementation of the Coulomb speroidal function 
        
        References:
            - https://dlmf.nist.gov/30.12
            
        TODO
    '''
    if(kind not in [1,2]):
        raise TypeValue("Generalized Spheroidal functions only allowed in two different generalizations (1 or 2). Got %s" %kind);
    params =[];
    if(a is None):
        params += ['a'];
    if(b is None):
        params += ['b'];
    if(c is None):
        params += ['c'];
    if(d is None):
        params += ['d'];
    
    destiny_ring = DFinite; ra = a; rb = b; rc = c; rd = d;
    if(len(params) > _sage_const_0 ):
        destiny_ring = ParametrizedDDRing(DFinite, params);
        if('a' in params):
            ra = destiny_ring.parameter('a');
        if('b' in params):
            rb = destiny_ring.parameter('b');
        if('c' in params):
            rc = destiny_ring.parameter('c');
        if('d' in params):
            rd = destiny_ring.parameter('d');
    
    coeffs = [ra*(1-x**2)**2-(rb*(1-x**2))**2-rc**2, -2*x*(1-x**2), (1-x**2)**2];
    if(kind == 1):
        coeffs[0] += rd*x*(1-x**2);
    else:
        coeffs = [el*x**2 for el in coeffs];
        coeffs[0] -= rd*(rd+1)*(1-x**2);
    return destiny_ring.element(coeffs, init, name=DinamicString("CoulombSpheroidal(_1,_2,_3,_4;%d;%s)(_5)" %(kind,init), [repr(ra), repr(rb), repr(rc), repr(rd), "x"]));

@cached_function
def SpheroidalWaveFunctionD(a=None, b=None, c=None, init=()):
    '''
        D-finite implementation of the spheroidal wave function.
        
        References:
            - https://dlmf.nist.gov/30.2
            - https://en.wikipedia.org/wiki/Spheroidal_wave_function
            - http://mathworld.wolfram.com/SpheroidalWaveFunction.html
            
        TODO
    '''
    params =[];
    if(a is None):
        params += ['a'];
    if(b is None):
        params += ['b'];
    if(c is None):
        params += ['c'];
    
    destiny_ring = DFinite; ra = a; rb = b; rc = c;
    if(len(params) > _sage_const_0 ):
        destiny_ring = ParametrizedDDRing(DFinite, params);
        if('a' in params):
            ra = destiny_ring.parameter('a');
        if('b' in params):
            rb = destiny_ring.parameter('b');
        if('c' in params):
            rc = destiny_ring.parameter('c');
    
    coeffs = [ra*(1-x**2)**2-(rb*(1-x**2))**2-rc**2, -2*x*(1-x**2), (1-x**2)**2];
    return destiny_ring.element(coeffs, init, name=DinamicString("SpheroidalWave(_1,_2,_3;%s)(_4)" %(str(init)), [repr(ra), repr(rb), repr(rc), "x"]));

###### HEUN FUNCTIONS
### Fuschian equation
def FuschianD(a = [], gamma = [], q = [], init=()):
    '''
        D-finite implementation of the Fuschian equation
        
        References:
            - https://dlmf.nist.gov/31.15
            
        TODO
    '''
    ## Checking parameters
    if (not (isinstance(a,list) or isinstance(a,set) or isinstance(a,tuple))):
        a = [a];
    if (not (isinstance(gamma,list) or isinstance(gamma,set) or isinstance(gamma,tuple))):
        gamma = [gamma];
    if (not (isinstance(q,list) or isinstance(q,set) or isinstance(q,tuple))):
        q = [q];
    if(len(a) == 0 or len(a) != len(gamma) or len(a) != len(q)):
        raise ValueError("The three arguments a, gamma and q must be non-empty lists of the same length");
    N = len(a);
    
    ## Getting the parameters
    parent, new_all = __check_list(a+gamma+q, [str(el) for el in DFinite.variables()]);
    
    a = new_all[:N];
    gamma = new_all[N:2*N];
    q = new_all[-N:];
    
    if(sum(q) != 0):
        raise ValueError("The q parameters must sum up zero. Got %s" %(sum(q)));
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DFinite;
        
    a = [destiny_ring.base()(el) for el in a];
    gamma = [destiny_ring.base()(el) for el in gamma];
    q = [destiny_ring.base()(el) for el in q];
    x = destiny_ring.variables()[0];
    ## Computing the differential equation
    P = prod([x-a[i] for i in range(N)]); R = P.parent();
    Q = [R(P/(x-a[i])) for i in range(N)];
    
    coeffs = [sum(q[i]*Q[i] for i in range(N)), sum(gamma[i]*Q[i] for i in range(N)), P];
    
    ## Returning the solution
    return destiny_ring.element(coeffs, init, name=DinamicString("Fuschian(_1;_2;_3;%s)(_4)" %(str(init)), [repr(a), repr(gamma), repr(q), "x"]));

### Heun's function
def HeunD(a=None,b=None,d=None,g=None,e=None,q=None):
    '''
        D-finite implementation of the Heun's functions.
        
        References:
            - https://dlmf.nist.gov/31.2
            - https://en.wikipedia.org/wiki/Heun_function
            - http://mathworld.wolfram.com/HeunsDifferentialEquation.html
            
        TODO
    '''
    pars = ["a","b","d","g","e","q"];
    args = [a,b,d,g,e,q];
    for i in range(len(args)):
        if(args[i] is not None):
            pars[i] = args[i];
        
    parent, new_all = __check_list(pars, [str(el) for el in DFinite.variables()]);
    ra,rb,rd,rg,re,rq = new_all;
        
    al = rg+rd+re-rb-1;
    f = FuschianD(a=[0,1,ra],gamma=[rd,rg,re],q=[-rq/ra,(rq-al*rb)/(ra-1), (rq/ra)-((rq-al*rb)/(ra-1))]);
    f._DDFunction__name = DinamicString("Heun(_1,_2,_3,_4,_5,_6)(_7)", [repr(ra),repr(rb),repr(rd),repr(rg),repr(re),repr(rq),"x"]);
    return f;

###### COULOMB FUNCTIONS
def CoulombF(m=None, l=None):
    '''
        D-finite implementation of the regular Coulomb wave function (F_l(mu,ro)).
        
        References:
            - https://dlmf.nist.gov/33.2
            - https://en.wikipedia.org/wiki/Coulomb_wave_function
            
        TODO
    '''
    params =[];
    if(m is None):
        params += ['m'];
    if(l is None):
        params += ['l'];
    destiny_ring = DFinite; rm = m; rl = l;
    if(len(params) > _sage_const_0 ):
        destiny_ring = ParametrizedDDRing(DFinite, params);
        if('m' in params):
            rm = destiny_ring.parameter('m');
        if('l' in params):
            rl = destiny_ring.parameter('l');
    x = destiny_ring.variables()[0];
    init = [];
    
    if(l in ZZ): ## Power series solution
        if(l in [-1,0]): ## Special cases
            init = [0,1];
        elif(l > 0):
            init = [0 for i in range(l+1)] + [1];
            
    return destiny_ring.element([x**2-2*rm*x-rl*(rl+1), 0, x**2], init=init, name=DinamicString("CoulombF(_1;_2)(_3)", [repr(rm), repr(rl), "x"]));

            
##################################################################################
##################################################################################
###
### Algebraic functions
###
##################################################################################
################################################################################## 
def DAlgebraic(polynomial, init=[], dR=None):
    '''
        Method that transform an algebraic function to a DD-Function.
                
        INPUT:
            - polynomial: the minimal polynomial of the function we want to transform.
            - init: the initial values that the function will have. Two options are 
            possible: a list is given, then we will use it directly to build the final 
            result, or a value is given an we will compute the others using the polynomial 
            equation.
            - dR: the ring where we want to include the result. If None, an automatic 
            destiny ring will be computed.
            
        OUTPUT:
            - A DDFunction in a particuar DDRing.
            
        WARNINGS:
            - There is no control about the irreducibility of the polynomial.
            
        ERRORS:
            - If the function can not be represented in dR a TypeError will be raised
            - If any error happens with the initial values, a ValueError will be raised
    '''
    ## Local imports
    from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isPolynomial;
    from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing as isMPolynomial;
    from sage.categories.pushout import FractionField;
    from ajpastor.misc.matrix import matrix_of_dMovement as move;
    
    ###############################################
    ## Dealing with the polynomial input
    ###############################################
    parent = polynomial.parent();
    if(not (isPolynomial(parent) or isMPolynomial(parent))):
        raise TypeError("The minimal polynomial is NOT a polynomial");
    
    base_ring = None;  
    F = None;  
    poly_ring = parent;
    if(isMPolynomial(parent)):
        base_ring = PolynomialRing(parent.base(),parent.gens()[:-_sage_const_1 ]);
        poly_ring = PolynomialRing(base_ring.fraction_field(), parent.gens()[-_sage_const_1 ]);
    else:
        if(isinstance(parent.base().construction()[_sage_const_0 ], FractionField)):
            base_ring = parent.base().base();
        else:
            base_ring = parent.base();
            if(not parent.base().is_field()):
                poly_ring = PolynomialRing(parent.base().fraction_field(), parent.gens()[-_sage_const_1 ]);
                
    F = poly_ring.base();
    y = poly_ring.gens()[-_sage_const_1 ];
    ## At this point we have the following
    ##   - F is a field
    ##   - y is a variable
    ##   - poly_ring == F[y]
    polynomial = poly_ring(polynomial); ## Now the structure is univariate
    if(polynomial.degree() == _sage_const_1 ):
        return -polynomial[_sage_const_0 ]/polynomial[_sage_const_1 ];
    elif(polynomial.degree() <= _sage_const_0 ):
        raise TypeError("Constant polynomial given for algebraic function: IMPOSSIBLE!!");
        
    #################################################
    ## Building and checking the destiny ring
    #################################################
    destiny_ring = None;
    if(dR is None):
        destiny_ring = DDRing(base_ring);
    else:
        destiny_ring = dR;
        coercion = destiny_ring._coerce_map_from_(base_ring);
        if((coercion is None) or (coercion is False)):
            raise TypeError("Incompatible polynomial with destiny ring:\n\t- Coefficients in: %s\n\t- Destiny Ring: %s" %(base_ring, destiny_ring));
            
    dest_var = repr(destiny_ring.variables()[_sage_const_0 ]);
    
    ##################################################
    ## Computing the differential equation
    ##################################################
    ## Computing the derivative
    dy = polynomial.derivative(y);
    
    ## Getting its gcd with the polynomial
    g,r,s = polynomial.xgcd(dy);
    if((g != _sage_const_1 ) or (not(g in poly_ring.base()))):
        raise ValueError("No irreducible polynomial given");
        
    ## Computing the coefficient-wise derivation of polynomial
    mon = poly_ring(_sage_const_1 );
    ky = poly_ring(_sage_const_0 );
    for i in range(polynomial.degree()+_sage_const_1 ):
        ky += (polynomial[i].derivative())*mon;
        mon *= y;
        
    ## Getting the polynomial expression of y', y'',..., y^{(deg(polynomial))}
    rows = [[_sage_const_0 ]*polynomial.degree()];
    mon = poly_ring(_sage_const_1 );
    for i in range(polynomial.degree()-_sage_const_1 ):
        rows += [((-(i+_sage_const_1 )*mon*s*ky)%polynomial).coefficients(False)];
        mon *= y;
        
    ## Building the derivation matrix of <1,y,y^2,...>
    M = Matrix(F, rows).transpose();
    ## Creating the vector representing y
    y_vector = vector(F, [_sage_const_0 ,_sage_const_1 ] + [_sage_const_0 ]*(polynomial.degree()-_sage_const_2 ));
    ## Building ans solving the system
    to_solve = move(M, y_vector, lambda p : p.derivative(), M.ncols()+_sage_const_1 );
    v = to_solve.right_kernel_matrix()[_sage_const_0 ];
    
    ## Cleaning denominators
    cleaning = lcm(el.denominator() for el in v);
    
    equation = destiny_ring.element([F.base()(el*cleaning) for el in v]).equation;
    
    ##################################################
    ## Getting the initial values
    ##################################################
    if(not (type(init) is list)):
        ## We try to compute the new initial values
        init = [init];
        go_on = True;
        for i in range(_sage_const_1 ,min(equation.get_jp_fo()+_sage_const_2 , to_solve.ncols())):
            try:
                init += [sum(to_solve[j,i](**{dest_var:_sage_const_0 })*init[_sage_const_0 ]**j for j in range(polynomial.degree()))];
            except ZeroDivisionError:
                go_on = False;
                break;
        
        if(go_on and (equation.get_jp_fo()+_sage_const_2  > to_solve.ncols())):
            extra = move(M, vector(F,[el[_sage_const_0 ] for el in to_solve[:,-_sage_const_1 ]]), equation.get_jp_fo()+_sage_const_2 -to_solve.ncols());
            init += [sum(extra[j,i](**{dest_var:_sage_const_0 })*init[_sage_const_0 ]**j for j in range(polynomial.degree())) for i in range(extra.ncols())];
    
    ##################################################
    ## Returning the DDFunction
    ##################################################
    return destiny_ring.element(equation, init);
  
##################################################################################
##################################################################################
###
### Private methods
###
##################################################################################
##################################################################################    
def __decide_parent(input, parent = None, depth = 1):
    '''            
        TODO
    '''
    if(parent is None):
        R = input.parent();
        if(isinstance(R, sage.symbolic.ring.SymbolicRing)):
            parameters = set([str(el) for el in input.variables()])-set(['x']);
            if(len(parameters) > 0 ):
                parent = ParametrizedDDRing(DDRing(DFinite, depth=depth), parameters);
            else:
                parent = DDRing(PolynomialRing(QQ,x), depth=depth);
        elif(is_MPolynomialRing(R) or is_PolynomialRing(R)):
            parameters = [str(gen) for gen in R.gens()[1:]];
            if(len(parameters) > 0):
                parent = ParametrizedDDRing(DDRing(PolynomialRing(QQ,R.gens()[0]), depth=depth), parameters);
            else:
                parent = DDRing(PolynomialRing(QQ,R.gens()[0]), depth = depth);
        else:
            try:
                parent = DDRing(R, depth = depth);
            except Exception:
                raise TypeError("The object provided is not in a valid Parent", e);
    
    return parent.base()(input), parent;

def __check_list(list_of_elements, invalid_vars=[]):
    '''
        TODO
    '''
    all_vars = [];
    for i in range(len(list_of_elements)):
        el = list_of_elements[i];
        if(el not in QQ):
            if(isinstance(el, str)):
                all_vars += [el];
            else:
                from sage.rings.fraction_field import is_FractionField;
                if(is_FractionField(el.parent())):
                    all_vars += [str(v) for v in el.numerator().variables()];
                    all_vars += [str(v) for v in el.denominator().variables()];
                else:
                    all_vars += [str(v) for v in el.variables()];
                list_of_elements[i] = str(el);
    
    if(any(el in all_vars for el in invalid_vars)):
        raise ValueError("An invalid variable detected in the list.\n\t- Got: %s\n\t- Invalid: %s" %(list_of_elements, invalid_vars));
    
    parent = QQ;
    if(len(all_vars) > 0):
        all_vars = list(set(all_vars));
        parent = PolynomialRing(QQ, all_vars).fraction_field();
        list_of_elements = [parent(el) for el in list_of_elements];
    
    return (parent, list_of_elements);
    
#### Usual running after defining everything
DD_EXAMPLES_LOAD();

