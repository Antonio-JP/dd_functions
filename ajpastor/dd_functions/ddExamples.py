
from sage.all_cmdline import *   # import sage library

from sage.rings.polynomial.polynomial_ring import is_PolynomialRing;
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing;

from ajpastor.dd_functions.ddFunction import *;

from ajpastor.misc.dinamic_string import *;

from ajpastor.misc.exceptions import *;

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
            - Tanh
            - Arcsin
            - Arccos
            - Arctan
            - Arcsinh
            - Arccosh
            - Arctanh
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
        ** RICCATI EQUATION (see https://en.wikipedia.org/wiki/Riccati_equation)
            - RiccatiD
        ** MATHIEU TYPE FUNCTIONS (see chapter 28 in https://dlmf.nist.gov)
            - MathieuD
            - MathieuSin
            - MathieuCos
            - MathieuH
            - MathieuSinh
            - MathieuCosh
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
            
        ** COMBINATORIAL FUNCTIONS
            - Catalan
            - Fibonacci
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
    
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(f) != 0):
        raise ValueError("Impossible to compute sin(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([df**3 ,-df2,df],[0,evaluate(df),evaluate(df2)], name=DinamicString("sin(_1)", newName)); 

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
    
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(f) != 0):
        raise ValueError("Impossible to compute cos(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([df**3 ,-df2,df],[1,0,-evaluate(df)**2 ], name=DinamicString("cos(_1)",newName)); 

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
    g, dR = __decide_parent(input, ddR,2 );
    
    
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute tan(f) with f(0) != 0");
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg);
    a = Cos(input)**2 ; b = dR.base().zero(); c = dR.base()(-2 );
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([dg**3 *c,dg**2 *b-ddg*a,dg*a]).equation;
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1];
    else:
        required = newOperator.get_jp_fo()+1;
            
        init_tan = Tan(x).getInitialValueList(required);
        init_input = [factorial(i)*dR.getSequenceElement(g,i) for i in range(required)];
            
        newInit = [init_tan[0]]+[sum([init_tan[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)]; ## See Faa di Bruno's formula
    
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
    
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(f) != 0):
        raise ValueError("Impossible to compute sin(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([-df**3 ,-df2,df],[0,evaluate(df),evaluate(df2)], name=DinamicString("sinh(_1)",newName)); 

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
    
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(f) != 0):
        raise ValueError("Impossible to compute cos(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([-df**3 ,-df2,df],[1,0,evaluate(df)**2 ], name=DinamicString("cosh(_1)", newName)); 

@cached_function
def Tanh(input, ddR = None):
    '''
        DD-finite implementation of the Tangent hyperbolic function (tanh(x)).
        
        References:
            - http://mathworld.wolfram.com/HyperbolicTangent.html 
            - https://en.wikipedia.org/wiki/Hyperbolic_function
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Tanh(x)(input);
    g, dR = __decide_parent(input, ddR,2 );
    
    
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute tan(f) with f(0) != 0");
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg);
    a = Cosh(input)**2 ; 
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([2*dg**3, -ddg*a, dg*a]).equation;
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1];
    else:
        required = newOperator.get_jp_fo()+1;
            
        init_tanh = Tanh(x).getInitialValueList(required);
        init_input = [factorial(i)*dR.getSequenceElement(g,i) for i in range(required)];
            
        newInit = [init_tanh[0]]+[sum([init_tanh[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)]; ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit);
    
    newName = repr(input);
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name;
    
    result._DDFunction__name = DinamicString("tanh(_1)",newName);
    return result;

@cached_function
def Arcsin(input, ddR = None):
    '''
        DD-finite implementation of the Arcsine function (arcsin(x)).
        
        References:
            - http://mathworld.wolfram.com/InverseSine.html
            - https://en.wikipedia.org/wiki/Inverse_trigonometric_functions
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Arcsin(x)(input);
    g, dR = __decide_parent(input, ddR);
        
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arcsin(f) with f(0) != 0");
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg);
    a = dR.base().zero(); b = -(ddg*(1-g**2) + g*dg**2); c = (1-g**2)*dg;
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([a,b,c]).equation;
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1];
    else:
        required = newOperator.get_jp_fo()+1;
            
        init_arcsin = Arcsin(x).getInitialValueList(required);
        init_input = [factorial(i)*dR.getSequenceElement(g,i) for i in range(required)];
            
        newInit = [init_arcsin[0]]+[sum([init_arcsin[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)]; ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit);
    newName = repr(input);
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name;
    
    result._DDFunction__name = DinamicString("arcsin(_1)",newName);
    
    return result;

@cached_function
def Arccos(input, ddR = None):
    '''
        DD-finite implementation of the Arccosine function (arccos(x)).
        
        References:
            - http://mathworld.wolfram.com/InverseCosine.html
            - https://en.wikipedia.org/wiki/Inverse_trigonometric_functions
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Arccos(x)(input);
    g, dR = __decide_parent(input, ddR);
    dR = ParametrizedDDRing(dR, 'pi'); pi = dR.parameter('pi');
        
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arccos(f) with f(0) != 0");
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg);
    a = dR.base().zero(); b = -(ddg*(1-g**2) + g*dg**2); c = (1-g**2)*dg;
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([a,b,c]).equation;
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [pi/Integer(2),-1];
    else:
        required = newOperator.get_jp_fo()+1;
            
        init_arccos = Arccos(x).getInitialValueList(required);
        init_input = [factorial(i)*dR.getSequenceElement(g,i) for i in range(required)];
            
        newInit = [init_arccos[0]]+[sum([init_arccos[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)]; ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit);
    newName = repr(input);
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name;
    
    result._DDFunction__name = DinamicString("arccos(_1)",newName);
    
    return result;

@cached_function
def Arctan(input, ddR = None):
    '''
        DD-finite implementation of the Arctangent function (arctan(x)).
        
        References:
            - http://mathworld.wolfram.com/InverseTangent.html
            - https://en.wikipedia.org/wiki/Inverse_trigonometric_functions
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Arctan(x)(input);
    g, dR = __decide_parent(input, ddR);
        
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arctan(f) with f(0) != 0");
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg);
    a = dR.base().zero(); b = (2*g*dg**2 - (1+g**2)*ddg); c = (1+g**2)*dg;
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([a,b,c]).equation;
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1];
    else:
        required = newOperator.get_jp_fo()+1;
            
        init_arctan = Arctan(x).getInitialValueList(required);
        init_input = [factorial(i)*dR.getSequenceElement(g,i) for i in range(required)];
            
        newInit = [init_arctan[0]]+[sum([init_arctan[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)]; ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit);
    
    newName = repr(input);
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name;
    
    result._DDFunction__name = DinamicString("arctan(_1)",newName);
    return result;

@cached_function 
def Arcsinh(input, ddR = None):
    '''
        DD-finite implementation of the hyperbolic Arcsine function (arcsinh(x)).
        
        References:
            - http://mathworld.wolfram.com/InverseHyperbolicSine.html
            - https://en.wikipedia.org/wiki/Inverse_hyperbolic_functions
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Arcsinh(x)(input);
    g, dR = __decide_parent(input, ddR);
        
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arcsinh(f) with f(0) != 0");
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg); a = g**2+1
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([dR.base().zero(),(g*dg**2 - ddg*a),dg*a]).equation;
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1];
    else:
        required = newOperator.get_jp_fo()+1;
            
        init_arcsinh = Arcsinh(x).getInitialValueList(required);
        init_input = [factorial(i)*dR.getSequenceElement(g,i) for i in range(required)];
            
        newInit = [init_arcsinh[0]]+[sum([init_arcsinh[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)]; ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit);
    newName = repr(input);
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name;
    
    result._DDFunction__name = DinamicString("arcsinh(_1)",newName);
    
    return result;

@cached_function
def Arccosh(input, ddR = None):
    '''
        DD-finite implementation of the hyperbolic Arccosine function (arccosh(x)).
        
        References:
            - http://mathworld.wolfram.com/InverseHyperbolicCosine.html
            - https://en.wikipedia.org/wiki/Inverse_hyperbolic_functions
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Arccosh(x)(input);
    g, dR = __decide_parent(input, ddR);
    dR = dR.extend_base_field(NumberField(x**2+1, name='I')); I = dR.base_field.gens()[0];
    dR = ParametrizedDDRing(dR, 'pi'); pi = dR.parameter('pi');
        
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arccosh(f) with f(0) != 0");
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg); a = g**2-1
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([dR.base().zero(),(g*dg**2 - ddg*a),dg*a]).equation;
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [I*pi/2,-I];
    else:
        required = newOperator.get_jp_fo()+1;
            
        init_arccosh = Arccosh(x).getInitialValueList(required);
        init_input = [factorial(i)*dR.getSequenceElement(g,i) for i in range(required)];
            
        newInit = [init_arccosh[0]]+[sum([init_arccosh[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)]; ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit);
    newName = repr(input);
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name;
    
    result._DDFunction__name = DinamicString("arccosh(_1)",newName);
    
    return result;

@cached_function 
def Arctanh(input, ddR = None):
    '''
        DD-finite implementation of the hyperbolic Arctangent function (arctanh(x)).
        
        References:
            - http://mathworld.wolfram.com/InverseHyperbolicTangent.html
            - https://en.wikipedia.org/wiki/Inverse_hyperbolic_functions
            
        This functions allows the user to fix the argument. The argument can be:
            - A symbolic expression: all variables but "x" will be considered as parameters. Must be a polynomial expression with x as a factor.
            - A polynomial: the first generator of the polynomial ring will be considered the variable to compute derivatives and the rest will be considered as parameters. The polynomial must be divisible by the main variable.
            - A DDFunction: the composition will be computed. The DDFunction must have initial value 0.
            
        This function can be converted into symbolic expressions.
    '''
    if(is_DDFunction(input)):
        return Arctanh(x)(input);
    g, dR = __decide_parent(input, ddR);
        
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(g) != 0):
        raise ValueError("Impossible to compute arctanh(f) with f(0) != 0");
    
    dg = dR.base_derivation(g); ddg = dR.base_derivation(dg); a = 1-g**2;
    
    ### First we compute the new linear differential operator
    newOperator = dR.element([dR.base().zero(), -(ddg*a + g*dg**2*2), dg*a]).equation;
        
    ### Now, we compute the initial values required
    if(input == x):
        newInit = [0,1];
    else:
        required = newOperator.get_jp_fo()+1;
            
        init_arctanh = Arctanh(x).getInitialValueList(required);
        init_input = [factorial(i)*dR.getSequenceElement(g,i) for i in range(required)];
            
        newInit = [init_arctanh[0]]+[sum([init_arctanh[j]*bell_polynomial(i,j)(*init_input[1:i-j+2 ]) for j in range(1,i+1)]) for i in range(1,required)]; ## See Faa di Bruno's formula
    
    result = dR.element(newOperator,newInit);
    
    newName = repr(input);
    if(hasattr(input, "_DDFunction__name") and (not(input._DDFunction__name is None))):
        newName = input._DDFunction__name;
    
    result._DDFunction__name = DinamicString("arctanh(_1)",newName);
    return result;

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
        return Log(x+1)(input-1);
    f,dR = __decide_parent(input, ddR);
    
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(f) != 1):
        raise ValueError("Impossible to compute ln(f) with f(0) != 1");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([0,df**2 -df2*f,df*f],[0,evaluate(df), evaluate(df2)-evaluate(df)**2 ], name=DinamicString("log(_1)",newName));
    
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
    
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(f) != 0):
        raise ValueError("Impossible to compute cos(f) with f(0) != 0");
    
    df = dR.base_derivation(f);
    df2 = dR.base_derivation(df);
    
    f1 = f+1;
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
    
    return dR.element([0,df**2 -df2*f1,df*f1],[0,evaluate(df), evaluate(df2)-evaluate(df)**2 ], name=DinamicString("log(_1+1)", newName)); 
    
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
    
    evaluate = lambda p : dR.getSequenceElement(p,0);
    if(evaluate(f) != 0):
        raise ValueError("Impossible to compute exp(f) with f(0) != 0");
    
    newName = repr(f);
    if(hasattr(f, "_DDFunction__name") and (not(f._DDFunction__name is None))):
        newName = f._DDFunction__name;
        
    return dR.element([-dR.base_derivation(f),1],[1], name=DinamicString("exp(_1)", newName));

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
def BesselD(input = 'P', kind = 1):
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
        
    if(kind == 1):
        func = parent.element([x**2-par**2, x, x**2], name=DinamicString("bessel_J(_1,_2)", [repr(par),"x"]));
        if(par in ZZ):
            alpha = ZZ(par);
            func = func.change_init_values([0 for i in range(alpha)] + [Integer(1)/Integer(2) **alpha, 0, -((alpha+Integer(2))/(Integer(2) **(alpha+2 )))], name = func._DDFunction__name);
    elif(kind == 2 ):
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
        num = factorial(par+1)*pi*(Integer(1)/Integer(2))**(par+1);
        den = gamma(Integer(3)/Integer(2))*gamma(par+Integer(3)/Integer(2));
        val = QQ(num/den);
        f = f.change_init_values([0 for i in range(par+1)] + [val], name=f._DDFunction__name);
    
    return f;


###### ORTHOGONAL POLYNOMIALS
### Legendre Polynomials 
def __init_value_associated_legendre(n,m,kind):
    S1_2 = Integer(1)/Integer(2);
    S2 = Integer(2);
    S1 = Integer(1);
    
    if(kind == 1):
        res = (2**m*sqrt(pi))/gamma((n-m)/S2 + S1)/gamma(S1_2-(n+m)/S2);
    else:
        res = -(S2**(m-S1)*sqrt(pi)*sin((S1_2)*(n+m)*pi))*gamma((n+m)/S2 + S1_2)/gamma((n-m)/S2 + S1);

    return res;

def __first_derivative_associated_legendre(n,m,kind):
    S1_2 = Integer(1)/Integer(2);
    S2 = Integer(2);
    S1 = Integer(1);
    
    if(kind == 1):
        res = -(S2**(m+S1)*sqrt(pi))/gamma((n-m)/S2 + S1_2)/gamma(-(n+m)/S2);
    else:
        res = (S2**m*sqrt(pi)*cos((S1_2)*(n+m)*pi))*gamma((n+m)/S2 + S1)/gamma((n-m)/S2 + S1_2);

    return res;

@cached_function 
def LegendreD(nu='n', mu = 0, kind=1):
    '''
        D-finite implementation of the Legendre functions (P_n(x) and Q_n(x))
        
        References:
            - https://dlmf.nist.gov/18.3 & https://dlmf.nist.gov/14.2
            - https://en.wikipedia.org/wiki/Legendre_polynomials
            - http://mathworld.wolfram.com/LegendrePolynomial.html & http://mathworld.wolfram.com/LegendreFunctionoftheSecondKind.html
            
        Legendre functions are the solutions to the differential equation:
            (1-x^2)f'' - 2xf' + n(n+1)f = 0
        
        This equation has a parameter 'n'. When 'n' takes non-negative integer
        values, it has polynomial solutions, the so called Legendre polynomials (P_n(x)). 
        This family of polynomials is a orthogonal set of polynomials. In particular
            \int_{-1}^{1} P_n(x)P_m(x) = (2/(2n+1))\delta_{m,n}
        This set of polynomials (as any orthogonal family of polynomials), also satisfies
        a recursive relation:
            (n+1)P_{n+1}(x) = (2n+1)xP_n(x) - nP_{n-1}(x)
        
        The other solution are the Legendre functions of second kind (Q_n(x)). They also 
        satisfy the same recurrence relation as the Legendre polynomials. They are power series
        that converges from x=-1 to x=1.
        
        There is an associated differential equation with an extra parameter:
            (1-x^2)^2f'' - 2x(1-x^2)f' + (n(n+1)(1-x^2) - m^2)f = 0
        that reduces to the original equation when m=0.
        
        This method allows the user to get the D-finite representation of the associated
        Legendre differential equation. 
        
        INPUT:
            - nu: the parameter 'n' on the assocaited differential equation. If not provided, ot takes the value 'n' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - mu: the parameter 'm' on the assocaited differential equation. If not provided, ot takes the value 0 by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - kind: the kind of the Legendre function the user want to get. It can take the values 1 and 2 (1 by default).
            
        WARNING:
            - Initial values will also be computed for the parameter values that have power series solutions. The second kind may have non-rational initial values and those will not be computed.
            - When evaluating parameters, the initial values will not update and must be set by hand.
    '''
    parent, par = __check_list([nu,mu], DFinite.variables());
    n = par[0]; m = par[1];
    
    ## Building the final parent
    if(parent is QQ):
        parent = DFinite;
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    
    ## Building the final name
    x = parent.variables()[0];
    if(m != 0):
        name = DinamicString("Legendre(_1,_2;_3)" [repr(n), repr(m), repr(x)]);
    elif(kind == 1):
        name = DinamicString("legendre_P(_1,_2)", [repr(n),repr(x)]);
    elif(kind == 2):
        name = DinamicString("legendre_Q(_1,_2)", [repr(n),repr(x)]);
    else:
        raise ValueError("Only Legendre functions of first and second kind are implemented. Got %s" %kind);
    
    ## Building the initial values
    init = [];
    if((m == 0) and (n in ZZ) and (n >= 0)):
        try:
            init = [__init_value_associated_legendre(n,m,kind), __first_derivative_associated_legendre(n,m,kind)];
            if(any(el not in parent.base_field for el in init)):
                init = [];
        except:
            pass;
    ## Building the coefficients of the equation
    if(m == 0):
        coeffs = [(n*(n+1)),-2*x,1-x**2];
    else:
        coeffs = [n*(n+1)*(1-x**2) - m**2, -2*x*(1-x**2), (1-x**2)**2];
     
    ## Returning the final element
    return parent.element(coeffs, init, name=name);        
   
### Chebyshev Polynomials        
@cached_function    
def ChebyshevD(input='n', kind = 1, poly=True):
    '''
        D-finite implementation of the Chebyshev polynomials (T_n(x), U_n(x))
        
        References:
            - https://dlmf.nist.gov/18.3
            - https://en.wikipedia.org/wiki/Chebyshev_polynomials
            - http://mathworld.wolfram.com/ChebyshevPolynomialoftheFirstKind.html & http://mathworld.wolfram.com/ChebyshevPolynomialoftheSecondKind.html
            
        The Chebyshev polynomials of the first kind T_n(x) are the polynomial solutions 
        to the differential equation
            (1-x^2)f'' - xf' + n^2f = 0
        with a parameter 'n'. The poylnomial solutions (with the appropriate normalization)
        form a orthogonal basis with the orthogonality relation:
            \int_{-1}^{1} (T_n(x)T_m(x))/(sqrt(1-x^2)) = \delta_{n,m}pi/(2-\delta_{0,n})
        
        The Chebyshev polynomials of the second kind U_n(x) are the polynomial solutions 
        to the differential equation
            (1-x^2)f'' - 3xf' + n(n+2)f = 0
        with a parameter 'n'. The poylnomial solutions (with the appropriate normalization)
        form a orthogonal basis with the orthogonality relation:
            \int_{-1}^{1} U_n(x)U_m(x))sqrt(1-x^2) = \delta_{n,m}pi/2
            
        The Chebyshev polynomials of the third kind V_n(x) are the polynomial solutions
        to the differential equation
            (1-x^2)f'' + (1-2x)f' + n(n+1)f = 0
            
        THe Chebyshev polynomials of the fourth kind W_n(x) are the polynomial solutions to
        the differential equation
            (1-x^2)f'' - (1+2x)f' + n(n+1)f = 0
            
        This method allows the user to get the D-finite representation of the associated
        Chebyshev differential equation. 
        
        INPUT:
            - input: the parameter 'n' on the differential equation. If not provided, it takes the value 'n' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - kind: the kind of the Chebyshev polynomials the user want to get. It can take the values 1, 2, 3 and 4 (1 by default).
            - poly: a boolean value that refer to the polynomial solution to the differential equation or the other power series solution. If False, the other power serie solution will be returned such that the Wronskian of this solution with the polynomial solution is 1. NOTE: when the parameter is not an integer, this parameter only makes a difference in the name of the function, adding a "P_" at the beginning.
            
        WARNING:
            - Initial values will also be computed for the integer parameter values.
            - When evaluating parameters, the initial values will not update and must be set by hand.
    '''
    parent, par = __check_list([input], DFinite.variables());
    n = par[0];
    
    ## Building the final parent
    if(parent is QQ):
        parent = DFinite;
    else:
        parent = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    
    ## Building the final name and the equation
    x = parent.variables()[0];
    name = "chebyshev";
    if(not poly):
        name = "P_" + name;
        
    if(kind == 1):
        coeffs = [n**2, -x, 1-x**2];
        name = DinamicString("%s_T(_1;_2)" %name, [repr(n), repr(x)]);
    elif(kind == 2):
        coeffs = [n*(n+2), -3*x, 1-x**2];
        name = DinamicString("%s_U(_1;_2)" %name, [repr(n),repr(x)]);
    elif(kind == 3):
        coeffs = [n*(n+1), 1-2*x, 1-x**2];
        name = DinamicString("%s_V(_1;_2)" %name, [repr(n),repr(x)]);
    elif(kind == 4):
        coeffs = [n*(n+1), -1-2*x, 1-x**2];
        name = DinamicString("%s_W(_1;_2)" %name, [repr(n),repr(x)]);
    else:
        raise ValueError("Only Chebyshev polynomials of first, second, third and fourth kind are implemented. Got %s" %kind);
    
    ## Building the initial values
    init = [];
    if(n in ZZ):
        if(n%2 == 0):
            n = n/2;
            if(poly):
                init = [(-1)**(n),0];
            else:
                init = [0, (-1)**(n)];
        else:
            n = (n-1)/2;
            if(kind == 1):
                init = [0, ((-1)**n)*(2*n+1)];
            else:
                init = [0, ((-1)**n)*(2*n+2)];   
            if(not poly):
                init = [-1/init[1], 0];
     
    ## Returning the final element
    return parent.element(coeffs, init, name=name);        

###### HYPERGEOMETRIC FUNCTIONS
### Hypergeometric Functions
__CACHED_HYPERGEOMETRIC = {};
@cached_function
def HypergeometricFunction(a='a',b='b',c='c', init = 1):
    '''
        D-finite implementation of the Gauss Hypergeometric function
        
        References:
            - https://dlmf.nist.gov/15
            - https://en.wikipedia.org/wiki/Hypergeometric_function
            - http://mathworld.wolfram.com/HypergeometricFunction.html
            
        The Gauss Hypergeometric function is a special function represented by the hypergeometric 
        series, that includes many other special functions as specific or limiting cases. It is a 
        solution of the second-order differential equation
            x(1-x)f'' + (c-(a+b+1)x)f' - abf = 0
            
        The associated sequence to this functions have the following expression:
            f_n = ((a)_n * (b)_n)/(n!*(c)_n)
        where (a)_n = a*(a+1)*...*(a+n-1). Hence, if a or b is a negative integer this is a polynomial.
        
        This is a particular case of the Generic Hypergeometric Function, 2F1(a,b;c;x), being equivalent
        to GenericHypergeometricFunction([a,b],[c],init).
        
        INPUT:
            - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - b: the parameter 'b' on the differential equation. If not provided, it takes the value 'b' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - c: the parameter 'c' on the differential equation. If not provided, it takes the value 'c' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - init: the initial value of the hypergeometric function. It is the first value of the hypergeometric sequence. If not provided, it takes the value 1 by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    '''
    return GenericHypergeometricFunction([a,b],[c],init);

def GenericHypergeometricFunction(num=[],den=[],init=1):
    '''
        D-finite implementation of the Generalized Hypergeometric Functions qFp(a_1,...,a_q;b_1,...,b_m;x)
        
        References:
            - https://dlmf.nist.gov/16
            - https://en.wikipedia.org/wiki/Generalized_hypergeometric_function
            - http://mathworld.wolfram.com/GeneralizedHypergeometricFunction.html
            
        The Generic Hypergeometric function is a special function denoted by qFp(a_1,...,a_p;b_1,...,b_q;x) represented 
        by the hypergeometric series
            f_n = ((a_1)_n * ... * (a_p)_n)/(n!*(b_1)_n * ... * (b_q)_n)
        where (a)_n = a*(a+1)*...*(a+n-1).
        
        This hypergeometric functions satisfies a linear differential equation of order max(p,q) that can be represented
        using the gauss differential operator D(f) = xf':
            (D(D+b_1-1)...(D+b_q-1) - x(D+a_1)...(D+a_p))(f) = 0
                
        INPUT:
            - num: a list with the parameters "a_i". It also can be just one element that will be consider as a list with that element. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
            - den: a list with the parameters "b_i". It also can be just one element that will be consider as a list with that element. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
            - init: the initial value of the hypergeometric function. It is the first value of the hypergeometric sequence. If not provided, it takes the value 1 by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
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
        
    parent, new_all = __check_list(num+den+[init], [str(el) for el in DFinite.variables()]);
    numerator = new_all[:len(num)];
    denominator = new_all[len(num):-1];
    initial = new_all[-1];
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DFinite;
        
    ## Cleaning repeated values 
    i = 0;
    while(i < len(numerator) and len(denominator) > 0):
        if(numerator[i] in denominator):
            denominator.remove(numerator[i]);
            numerator.remove(numerator[i]);
        else:
            i += 1;
    
    ## Sort list for cannonical input
    numerator.sort(); denominator.sort();
    
    ## Casting to tuples to have hash  
    numerator = tuple(numerator); denominator = tuple(denominator);
    
    ## Checking the function is cached
    global __CACHED_HYPERGEOMETRIC;
    if(not((numerator,denominator,initial) in __CACHED_HYPERGEOMETRIC)):
        ## Building differential operator
        # Lambda method to get the operator in the appropriate operator ring
        get_op = lambda p : destiny_ring.default_operator(destiny_ring.base(),p,destiny_ring.base_derivation); 
        
        ## Getting the operator for the numerator and for the denominator
        op_num = prod((get_op([el,x]) for el in numerator),x);
        op_den = prod((get_op([el-1,x]) for el in denominator), get_op([0,x]));
        
        op = op_num - op_den;
        
        f = destiny_ring.element(op);
        
        initVals = [initial];
        
        if(initial == 1):
            __CACHED_HYPERGEOMETRIC[(numerator,denominator,initial)] = f.change_init_values([1],name=DinamicString("hypergeometric(_1,_2,_3)", [str(numerator),str(denominator),"x"]));
        else:
            __CACHED_HYPERGEOMETRIC[(numerator,denominator,initial)] = f.change_init_values([initial],name=DinamicString("(_1)*(hypergeometric(_2,_3,_4))", [str(initial),str(numerator),str(denominator),"x"]));
        
    ## Return the cached element
    return __CACHED_HYPERGEOMETRIC[(numerator,denominator,initial)];
    
###### RICCATI DIFFERENTIAL EQUATION
### Basic Riccati differential equation
@cached_function
def RiccatiD(a,b,c,init=None, ddR = None, full = False, name="w"):
    '''
        Implementation using DDFunctions of the solutions for the Ricatti differential equation.
        
        References:
            - https://en.wikipedia.org/wiki/Riccati_equation
            
        The Riccati differential equation is a non-linear differential equation of order one of the shape
            u' = a + bu + cu^2
        
        In particular, this represent all the monomials of degree 2 or less. It can be shown that if
        a and b are Dn-finite and c is D(n-1)-finite, then u(x) will be the logarithmic derivative
        of a D(n+1)-finite function (w), and hence, it is D(n+2)-finite. More precisely:
            w'' - (b + c'/c) w' + acw = 0
            
        Given the initial condition u(0) is enough to determined all the coefficients of the solution.
        
        INPUT:
            - a: function to represent the constant term in the quadratic polynomial that is the derivative of u(x)
            - b: function to represent the linear term in the quadratic polynomial that is the derivative of u(x)
            - c: function to represent the leading term in the quadratic polynomial that is the dericative of u(x)
            - init: initial condition u(0) of the solution. None is also valid
            - ddR: basic DDRing where to put all the inputs a,b,c if they are not DDFunctions
            - full: if True, it returns also the function w used to build the solution in a tuple (solution, w)
            - name: name the system will give to the function w. By default this is "w"
    '''
    ## Considering the three parameters
    from sage.categories.pushout import pushout;
    
    if(is_DDFunction(a)):
        da, dRa = (a.parent().depth(), a.parent());
    else:
        a, dRa = __decide_parent(a, ddR); da = dRa.depth()-1;
    if(is_DDFunction(b)):
        db, dRb = (b.parent().depth(), b.parent());
    else:
        b, dRb = __decide_parent(b, ddR); db = dRb.depth()-1;
    if(is_DDFunction(c)):
        dc, dRc = (c.parent().depth(), c.parent());
    else:
        c, dRc = __decide_parent(c, ddR); dc = dRc.depth()-1;
        
    R = pushout(dRa, pushout(dRb, dRc));
    R = R.to_depth(max(da+1, db+1, dc+2));
    
    x = R.variables()[0];
    
    w = R.base().element([a*c, -b + c.derivative()/c,1], [1, -c(0)*init],name=DinamicString("_1(_2)", [name,repr(x)]));
    solution = -w.derivative()*(c*w).inverse;
    solution._DDFunction__name = DinamicString("Riccati(_1,_2,_3;_4)(_5)", [repr(a),repr(b),repr(c),str(init),repr(x)]);
    
    if(full):
        return solution,w;
    return solution;
    
    
    
###### MATHIEU TYPE FUNCTIONS
### Mathieu's Functions
@cached_function
def MathieuD(a='a',q='q',init=()):
    '''
        DD-finite implementation of the Matheiu function
        
        References:
            - https://dlmf.nist.gov/28.2
            - https://en.wikipedia.org/wiki/Mathieu_function
            - http://mathworld.wolfram.com/MathieuFunction.html
            
        The Mathieu functions are the solutions to the DD-finite differential equation
            f'' + (a - 2qcos(2x))f = 0.
            
        This is a generalization of the differential equation of the trigonometric functions
        sine and cosine (for q=0, a=1), and have several physical aplications.
        
        INPUT:
            - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - q: the parameter 'q' on the differential equation. If not provided, it takes the value 'q' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, new_all = __check_list([a,q] + list(init), [str(el) for el in DFinite.variables()]);
    ra = new_all[0]; rq = new_all[1]; rinit = new_all[2:];
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DDFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DDFinite;
    x = destiny_ring.variables()[0];
    
    return destiny_ring.element([ra-2 *rq*Cos(2 *x), 0, 1], rinit, name=DinamicString("Mathieu(_1,_2;_3)(_4)", [repr(ra),repr(rq),str(rinit[:2 ]),repr(x)]));

@cached_function
def MathieuSin(a='a',q='q'):
    '''
        DD-finite implementation of the Mathieu Sine function.
        
        References:
            - https://dlmf.nist.gov/28.2
            - https://en.wikipedia.org/wiki/Mathieu_function
            - http://mathworld.wolfram.com/MathieuFunction.html
            
        This is the sine function with the Mathieu equation (i.e., with initial values
        0 an 1). It is equivalent to MathieuD(a,q,(0,1)).
    '''
    return MathieuD(a,q,(0,1));
    
@cached_function
def MathieuCos(a='a',q='q'):
    '''
        DD-finite implementation of the Mathieu Cosine function.
        
        References:
            - https://dlmf.nist.gov/28.2
            - https://en.wikipedia.org/wiki/Mathieu_function
            - http://mathworld.wolfram.com/MathieuFunction.html
            
        This is the cosine function with the Mathieu equation (i.e., with initial values
        1 an 0). It is equivalent to MathieuD(a,q,(1,0)).
    '''
    return MathieuD(a,q,(1,0));

### Modified Mathieu's Functions
@cached_function
def MathieuH(a='a',q='q',init=()):
    '''
        DD-finite implementation of the Modified Matheiu functions.
        
        References:
            - https://dlmf.nist.gov/28.20
            - https://en.wikipedia.org/wiki/Mathieu_function
            
        The Modified Mathieu functions are the solutions to the DD-finite differential equation
            f'' - (a - 2qcosh(2x))f = 0.
            
        This is a generalization of the differential equation of the hyperbolic trigonometric functions
        sinh and cosh (for q=0, a=1), and have several physical aplications.
        
        INPUT:
            - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - q: the parameter 'q' on the differential equation. If not provided, it takes the value 'q' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, new_all = __check_list([a,q] + list(init), [str(el) for el in DFinite.variables()]);
    ra = new_all[0]; rq = new_all[1]; rinit = new_all[2:];
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DDFinite;
    x = destiny_ring.variables()[0];
    
    return destiny_ring.element([-ra-2 *rq*Cosh(2 *x), 0, 1], rinit, name=DinamicString("MathieuH(_1,_2;_3)(_4)", [repr(ra),repr(rq),str(rinit[:2 ]),repr(x)]));

@cached_function
def MathieuSinh(a='a',q='q'):
    '''
        DD-finite implementation of the Modified Matheiu functions.
        
        References:
            - https://dlmf.nist.gov/28.20
            - https://en.wikipedia.org/wiki/Mathieu_function
            
        This is the hyperbolic sine function with the Mathieu equation (i.e., with initial values
        0 an 1). It is equivalent to MathieuH(a,q,(0,1)).
    '''
    return MathieuH(a,q,(0,1));
    
@cached_function
def MathieuCosh(a='a',q='q'):
    '''
        DD-finite implementation of the Modified Matheiu functions.
        
        References:
            - https://dlmf.nist.gov/28.20
            - https://en.wikipedia.org/wiki/Mathieu_function
            
        This is the hyperbolic cosine function with the Mathieu equation (i.e., with initial values
        1 an 0). It is equivalent to MathieuH(a,q,(1,0)).
    '''
    return MathieuH(a,q,(1,0));

### Hill's equation
@cached_function
def HillD(a='a',q='q',init=()):
    '''
        DD-finite implementation of the Hill equation.
        
        References:
            - https://dlmf.nist.gov/28.29
            - https://en.wikipedia.org/wiki/Hill_differential_equation
            - http://mathworld.wolfram.com/HillsDifferentialEquation.html
            
        The Hill differential equation is defined as
            f'' + (a + q(x))f = 0
        where 'a' is a parameter and q(x) is a function on the variable 'x'. This generalize the
        Mathieu differential equation and the modified Mathieu differential equation (taking the
        corresponding value for the function q(x)).
        
        This method allows the user to get the representation of the Hill function with some particular
        initial values. The possible values for the function q(x) is any polynomial function with x and 
        any DDFunction of any depth.
        
        INPUT:
            - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - q: the parameter 'q' on the differential equation. If not provided, it takes the value 'q' by default. This argument can be any DDFunction, rational number or any polynomial expression, which all variables (except 'x') will be considered as parameters.
            - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    if(is_DDFunction(q)):
        destiny_ring = q.parent().to_depth(q.parent().depth());
        parent, new_all = __check_list([a] + list(init), [str(el) for el in DFinite.variables()]);
        
        if(not (parent is QQ)):
            destiny_ring = ParametrizedDDRing(base, [str(v) for v in parent.gens()]);
        ra = new_all[0]; rq = destiny_ring.base()(q); rinit = new_all[-len(init):];
    else:
        parent, new_all = __check_list([a,q] + list(init), []);
        ra = new_all[0]; rq = new_all[1]; rinit = new_all[-len(init):];
        
        if(parent is QQ):
            destiny_ring = DFinite;
        else:
            new_vars = [str(v) for v in parent.gens()];
            
            if('x' in new_vars):
                x = parent.gens()[new_vars.index('x')];
                if(x in ra.variables() or any(x in el.variables() for el in rinit)):
                    raise ValueError("The variable 'x' can not appear in the parameter 'a' or in the initial values.\n\t- a: %s\n\t- init: %s" %(ra,rinit));
                new_vars.remove('x');
            
            destiny_ring = ParametrizedDDRing(DFinite, new_vars);
            
    return destiny_ring.element([ra+rq, 0, 1], rinit, name=DinamicString("HillEq(_1,_2;_3)(_4)", [repr(ra),repr(rq),str(list(init[:2 ])),"x"]));

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
            
        The Airy functions are the solutions of the differential equation:
            f'' - xf = 0
        
        The classical Airy functions, denoted by Ai(x) and Bi(x), form a set of linearly independent
        solutions to the differential equations. The initial value of the classical Airy functions
        are
            Ai(0) = 1/(3^(2/3) * gamma(2/3)); Ai'(0) = -1/(3^(1/3) * gamma(1/3))
            Bi(0) = 1/(3^(1/6) * gamma(2/3)); Bi'(0) = (3^(1/6))/gamma(1/3)
            
        Due to this fact, the classical Airy functions do not have rational initial values. This is why
        this method can not retrieve te user with the functions Ai(x) or Bi(x). This method returns
        the solution of the Airy's differential equation with some particular initial value.
        
        The name of the returned function will show the linear combination of the function Ai(x) and Bi(x)
        using the gamma function and the transcendental value pi.
        
        INPUT:
            - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, rinit = __check_list(list(init), [str(el) for el in DFinite.variables()]);
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DFinite;
    x = destiny_ring.variables()[0];
    
    name = None;
    if(len(rinit) >= 2): ## Complete Airy function, we can build the name
        ## Rejecting the zero case
        if(rinit[0] == rinit[1] and rinit[0] == 0):
            return DFinite.zero();
        
        ## Simplifying the name if there is zero coefficients
        if(rinit[0] != 0):
            name_a1 = DinamicString("(3**(2/3)*gamma(2/3))*_1", [repr(rinit[0])]);
            name_b1 = DinamicString("(3**(1/3)*gamma(2/3))*_1", [repr(rinit[0])]);
        else:
            name_a1 = DinamicString("", []);
            name_b1 = DinamicString("", []);
        if(rinit[1] != 0):
            name_a2 = DinamicString("-(3**(1/3)*gamma(1/3))*_1", [repr(rinit[1])]);
            name_b2 = DinamicString("+(gamma(1/3))*_1", [repr(rinit[1])]);
        else:
            name_a2 = DinamicString("", []);
            name_b2 = DinamicString("", []);
            
        ## Building the final name
        name = DinamicString("((_1_2)/2)*airy_ai(_5) + ((_3_4)/(2*3**(1/6)))*airy_bi(_5)", [name_a1, name_a2, name_b1, name_b2,repr(x)]);
    else:
        name = DinamicString("airy(_1; _2)", [repr(x), repr(rinit)]);
    return destiny_ring.element([-x,0,1], rinit, name=name);


###### PARABOLIC-CYLINDER TYPE FUNCTIONS
### Parabolic Cylinder Functions
@cached_function
def ParabolicCylinderD(a='a',b='b',c='c', init=()):
    '''
        D-finite implementation of Parabolic Cylinder functions.
        
        References:
            - https://dlmf.nist.gov/12.2
            - https://en.wikipedia.org/wiki/Parabolic_cylinder_function
            - http://mathworld.wolfram.com/ParabolicCylinderDifferentialEquation.html
            
        The parabolic cylinder function is a solution to the differential equation:
            f'' + (c + bx + ax^2)f = 0
            
        INPUT:
            - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - b: the parameter 'b' on the differential equation. If not provided, it takes the value 'b' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - c: the parameter 'c' on the differential equation. If not provided, it takes the value 'c' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, new_all = __check_list([a,b,c]+list(init), [str(el) for el in DFinite.variables()]);
    ra = new_all[0]; rb = new_all[1]; rc = new_all[2]; rinit = new_all[-len(init):];
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DFinite;
    x = destiny_ring.variables()[0];
    
    return destiny_ring.element([(rc+rb*x+ra*x**2),0,1], rinit, name=DinamicString("ParabolicCylinder(_1,_2,_3;_4;_5)", [repr(ra), repr(rb), repr(rc), repr(rinit), repr(x)]));
    
###### ELLIPTIC INTEGRALS
## Legendre elliptic integrals
def EllipticLegendreD(kind,var='phi'):
    '''
        DD-finite implementation of the Legendre elliptic integrals (F(phi,k), E(phi,k), D(phi,k)
        
        References:
            - https://dlmf.nist.gov/19.2
            - https://en.wikipedia.org/wiki/Legendre_form
            - http://mathworld.wolfram.com/EllipticIntegraloftheFirstKind.html & http://mathworld.wolfram.com/EllipticIntegraloftheSecondKind.html & http://mathworld.wolfram.com/EllipticIntegraloftheThirdKind.html
            
        Given a function s(t) such that s^2 is a cubic or quartic polynomial in t and r(s,t) a rational function on s and t, 
        then the integral of r(s,t) w.r.t. t is calles an elliptic integral. The Legendre elliptic integral are obtained from
        the following functions:
        
            - First kind:
                s^2(t) = (1-t^2)(1-k^2t^2), r(s,t) = 1/s --> F(phi,k) = int_{0}^{sin(phi)} r(s,t).
            - Second kind:
                s^2(t) = (1-t^2)(1-k^2t^2), r(s,t) = s/(1-t^2) --> E(phi,k) = int_{0}^{sin(phi)} r(s,t).
            - Third kind:
                s^2(t) = (1-t^2)(1-k^2t^2), r(s,t) = t^2/s --> D(phi,k) = (F(phi,k)-E(phi,k))/k^2.
                
        These elliptic functions (called incomplete Legendre integrals) satisfies differential equations w.r.t. both k and phi.
        When phi=pi/2, they are called the complete Legendre integrals.
        
        This method allows the user to get the complete Legendre differential equations with respect to k (which are D-finite)
        or the incomplete differential equation with respect to phi (which is DD-finite). In the latter case, we consider k as a
        parameter for the differential equation.
        
        INPUT:
            - kind: determines the kind of the Legendre elliptic integral the user will get. Can only take the values 1,2 or 3 and MUST be provided.
            - var: the variable to consider. If str(var) is 'k', then the compelte Legendre elliptic integral is returned. If it is 'phi' (as it is by default) then the incomplete Legendre elliptic integral is returned with k as a parameter.
    '''
    if(kind not in [1,2,3]):
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
        DDFiniteK = ParametrizedDDRing(DDFinite, 'k');
        P = DDFiniteK.parameters()[0];
        s = DDFiniteK.to_depth(1)(Sin(x));
        c = DDFiniteK.to_depth(1)(Cos(x));
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
def CoulombSpheroidalFunctionD(a='a', b='b', c='c', d='d', kind = 1, init=()):
    '''
        D-finite implementation of the Coulomb speroidal function 
        
        References:
            - https://dlmf.nist.gov/30.12
            
        This method retrieves the Coulomb Spheroidal Wave function that is a generalization of the Spheroidal Wave 
        function (see documentation of SpheroidalWaveFunctionD). This function adds a new parameter (d). There are
        two kinds of generalizations (both catched vy this function with the argumen 'kind'). They satisfy 
        the following differential equation:
            - First kind:
                ((1-x^2)f')' + (a + dx + b^2(1-x^2) - c^2/(1-x^2))f = 0
            - Second kind:
                ((1-x^2)f')' + (a+ b^2(1-x^2) - d(d+1)/x^2 - c^2/(1-x^2))f = 0
                
        Both equations reduce to the Spheroidal Wave differential equation when d=0.
        
        INPUT:
            - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - b: the parameter 'b' on the differential equation. If not provided, it takes the value 'b' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - c: the parameter 'c' on the differential equation. If not provided, it takes the value 'c' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - d: the parameter 'd' on the differential equation. If not provided, it takes the value 'd' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - kind: the kind of Coulomb Spheroidal function. Currently this can take the value 1 or 2 (1 by default).
            - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    if(kind not in [1,2]):
        raise TypeValue("Generalized Spheroidal functions only allowed in two different generalizations (1 or 2). Got %s" %kind);
    parent, new_all = __check_list([a,b,c,d]+list(init), [str(el) for el in DFinite.variables()]);
    ra = new_all[0]; rb = new_all[1]; rc = new_all[2]; rd = new_all[3]; rinit = new_all[-len(init):];
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DFinite;
    x = destiny_ring.variables()[0];
    
    coeffs = [ra*(1-x**2)**2-(rb*(1-x**2))**2-rc**2, -2*x*(1-x**2), (1-x**2)**2];
    if(kind == 1):
        coeffs[0] += rd*x*(1-x**2);
    else:
        coeffs = [el*x**2 for el in coeffs];
        coeffs[0] -= rd*(rd+1)*(1-x**2);
    return destiny_ring.element(coeffs, init, name=DinamicString("CoulombSpheroidal(_1,_2,_3,_4;%d;%s)(_5)" %(kind,init), [repr(ra), repr(rb), repr(rc), repr(rd), "x"]));

@cached_function
def SpheroidalWaveFunctionD(a='a', b='b', c='c', init=()):
    '''
        D-finite implementation of the spheroidal wave function.
        
        References:
            - https://dlmf.nist.gov/30.2
            - https://en.wikipedia.org/wiki/Spheroidal_wave_function
            - http://mathworld.wolfram.com/SpheroidalWaveFunction.html
            
        The Spheroidal Wave functions are the solutions to the differential equation
            ((1-x^2)f')' + (a + b^2*(1-x^2) - c^2/(1-x^2))f = 0.
            
        This functions are related with the related Legendre functions (taking b = 0).
        
        This method allows to get the D-finite representation of the Spheroidal Wave functions
        with a set of initial values.
        
        INPUT:
            - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - b: the parameter 'b' on the differential equation. If not provided, it takes the value 'b' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - c: the parameter 'c' on the differential equation. If not provided, it takes the value 'c' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, new_all = __check_list([a,b,c]+list(init), [str(el) for el in DFinite.variables()]);
    ra = new_all[0]; rb = new_all[1]; rc = new_all[2]; rinit = new_all[-len(init):];
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DFinite;
    x = destiny_ring.variables()[0];
    
    coeffs = [ra*(1-x**2)**2-(rb*(1-x**2))**2-rc**2, -2*x*(1-x**2), (1-x**2)**2];
    
    return destiny_ring.element(coeffs, init, name=DinamicString("SpheroidalWave(_1,_2,_3;_4)(_5)", [repr(ra), repr(rb), repr(rc), repr(init), repr(x)]));

###### HEUN FUNCTIONS
### Fuschian equation
@cached_function
def FuschianD(a = (), gamma = (), q = (), init=()):
    '''
        D-finite implementation of the Fuschian equation
        
        References:
            - https://dlmf.nist.gov/31.15
            
        The Fuschian differential equation is defined using three list of parameters of the same length
        a,gamma and q with the following formula:
            f'' + (sum_j [gamma_j/(x-a_j)])f' + (sum_j [q_j/(x-a_j)])f = 0,
        where (sum_j [q_j]) == 0.
        
        This differential equation has finite singularities at a_j of exponent {0,1-gamma_j} and at
        infinity of exponents {alpha, beta} where they are the solutions to
            alpha+beta+1 = sum_j [gamma_j]
            alpha*beta = sum_j [a_jq_j]
            
        This differential equation is a generalization of the Heun differential equation (see documentation
        of method HeunD) when len(a) = 3, and the parameters are appropriately addapted.
        
        INPUT:
            - a: a TUPLE with the values for the singularity parameter. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
            - gamma: a TUPLE with the exponents values. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
            - q: a TUPLE with the accesory parameters for the equation. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
            - init: a TUPLE with the initial values for the function. Each element can be a string to create a variable, any rational number or any polynomial expression which variables will be considered as parameters (so 'x' is not allowed).
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
    parent, new_all = __check_list(list(a)+list(gamma)+list(q)+list(init), [str(el) for el in DFinite.variables()]);
    
    ra = new_all[:N];
    rgamma = new_all[N:2*N];
    rq = new_all[2*N:3*N];
    rinit = new_all[-len(init):];
    
    if(sum(q) != 0):
        raise ValueError("The q parameters must sum up zero. Got %s" %(sum(q)));
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DFinite;
        
    x = destiny_ring.variables()[0];
    ## Computing the differential equation
    P = prod([x-ra[i] for i in range(N)]); R = P.parent();
    Q = [R(P/(x-ra[i])) for i in range(N)];
    
    coeffs = [sum(rq[i]*Q[i] for i in range(N)), sum(rgamma[i]*Q[i] for i in range(N)), P];
    
    ## Returning the solution
    return destiny_ring.element(coeffs, rinit, name=DinamicString("Fuschian(_1;_2;_3;%s)(_4)" %(str(rinit)), [repr(ra), repr(rgamma), repr(rq), repr(x)]));

### Heun's function
def HeunD(a='a',b='b',d='d',g='g',e='e',q='q'):
    '''
        D-finite implementation of the Heun's functions.
        
        References:
            - https://dlmf.nist.gov/31.2
            - https://en.wikipedia.org/wiki/Heun_function
            - http://mathworld.wolfram.com/HeunsDifferentialEquation.html
            
        Heun functions are the solutions of the differential equation
            f'' + (g/x + d/(x-1) + e/(x-a))f' + (Abx - q)/(x(x-1)(x-a)) f = 0,
        where A = d+g+e-b-1.
        
        This equation ahs regualr singularities at 0, 1, a and infinity and captures all the possible
        differential equation of order two with four regular singularities.
        
        The parameter a is called "singularity parameter", A,b,g,d,e are called "exponent parameters" 
        and q is called the "accesory parameter".
        
        INPUT:
            - a: the parameter 'a' on the differential equation. If not provided, it takes the value 'a' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - b: the parameter 'b' on the differential equation. If not provided, it takes the value 'b' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - d: the parameter 'd' on the differential equation. If not provided, it takes the value 'd' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - g: the parameter 'g' on the differential equation. If not provided, it takes the value 'g' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - e: the parameter 'e' on the differential equation. If not provided, it takes the value 'e' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - q: the parameter 'q' on the differential equation. If not provided, it takes the value 'q' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            
        WARNING:
            - This method does not compute initial values for the solution of this differential equation as no power series solution is guaranteed due to the singularity at 0.
    '''
    parent, new_all = __check_list([a,b,d,g,e,q], [str(el) for el in DFinite.variables()]);
    ra,rb,rd,rg,re,rq = new_all;
        
    al = rg+rd+re-rb-1;
    f = FuschianD(a=[0,1,ra],gamma=[rd,rg,re],q=[-rq/ra,(rq-al*rb)/(ra-1), (rq/ra)-((rq-al*rb)/(ra-1))]);
    f._DDFunction__name = DinamicString("Heun(_1,_2,_3,_4,_5,_6)(_7)", [repr(ra),repr(rb),repr(rd),repr(rg),repr(re),repr(rq),"x"]);
    return f;

###### COULOMB FUNCTIONS
def CoulombF(m='m', l='l'):
    '''
        D-finite implementation of the regular Coulomb wave function (F_l(mu,ro)).
        
        References:
            - https://dlmf.nist.gov/33.2
            - https://en.wikipedia.org/wiki/Coulomb_wave_function
            
        The Coulomb Wave function is the solution to the differential equation
            f'' + (1-(2m)/x - (l(l+1))/x^2)f = 0
            
        If l is integer, there is a power serie solution of order l+1, and this function return that solution
        with first sequence element 1.
        
        INPUT:
            - m: the parameter 'm' on the differential equation. If not provided, it takes the value 'm' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
            - l: the parameter 'l' on the differential equation. If not provided, it takes the value 'l' by default. This argument can be any rational number or any polynomial expression, which variables will be considered as parameters (so 'x' is not allowed).
    '''
    parent, new_all = __check_list([m,l], [str(el) for el in DFinite.variables()]);
    rm, rl = new_all;
    
    if(parent != QQ):
        destiny_ring = ParametrizedDDRing(DFinite, [str(v) for v in parent.gens()]);
    else:
        destiny_ring = DFinite;
    x = destiny_ring.variables()[0];
    init = [];
    
    if(rl in ZZ): ## Power series solution
        if(rl in [-1,0]): ## Special cases
            init = [0,1];
        elif(rl > 0):
            init = [0 for i in range(rl+1)] + [1];
            
    return destiny_ring.element([x**2-2*rm*x-rl*(rl+1), 0, x**2], init=init, name=DinamicString("CoulombF(_1;_2)(_3)", [repr(rm), repr(rl), "x"]));

##################################################################################
##################################################################################
###
### Combinatorial functions
###
##################################################################################
################################################################################## 
@cached_function
def Catalan():
    return DFinite.element([2, 10*x-2, 4*x**2-x], [1,1]);

@cached_function
def Fibonacci(init=(1,1)):
    parent, rinit = __check_list([el for el in init], [str(el) for el in DFinite.variables()]);
    params = [str(v) for v in parent.gens()];
    pos = ord('a');
    if(len(init) < 2):
        if(len(init) < 1):
            while(chr(pos) in params):
                pos += 1;
            rinit = [chr(pos)];
        if(len(init) == 1):
            while(chr(pos) in params):
                pos += 1;
            rinit += [chr(pos)];
        return Fibonacci(tuple(rinit));
    
    if(parent is QQ):
        destiny_ring = DFinite;
    else:
        destiny_ring = ParametrizedDDRing(DFinite, params);
    
    x = destiny_ring.variables()[0];
    
    return destiny_ring(((rinit[1]-rinit[0])*x + rinit[0])/(1-x-x**2));
            
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
        base_ring = PolynomialRing(parent.base(),parent.gens()[:-1]);
        poly_ring = PolynomialRing(base_ring.fraction_field(), parent.gens()[-1]);
    else:
        if(isinstance(parent.base().construction()[0], FractionField)):
            base_ring = parent.base().base();
        else:
            base_ring = parent.base();
            if(not parent.base().is_field()):
                poly_ring = PolynomialRing(parent.base().fraction_field(), parent.gens()[-1]);
                
    F = poly_ring.base();
    y = poly_ring.gens()[-1];
    ## At this point we have the following
    ##   - F is a field
    ##   - y is a variable
    ##   - poly_ring == F[y]
    polynomial = poly_ring(polynomial); ## Now the structure is univariate
    if(polynomial.degree() == 1):
        return -polynomial[0]/polynomial[1];
    elif(polynomial.degree() <= 0):
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
            
    dest_var = repr(destiny_ring.variables()[0]);
    
    ##################################################
    ## Computing the differential equation
    ##################################################
    ## Computing the derivative
    dy = polynomial.derivative(y);
    
    ## Getting its gcd with the polynomial
    g,r,s = polynomial.xgcd(dy);
    if((g != 1) or (not(g in poly_ring.base()))):
        raise ValueError("No irreducible polynomial given");
        
    ## Computing the coefficient-wise derivation of polynomial
    mon = poly_ring(1);
    ky = poly_ring(0);
    for i in range(polynomial.degree()+1):
        ky += (polynomial[i].derivative())*mon;
        mon *= y;
        
    ## Getting the polynomial expression of y', y'',..., y^{(deg(polynomial))}
    rows = [[0]*polynomial.degree()];
    mon = poly_ring(1);
    for i in range(polynomial.degree()-1):
        rows += [((-(i+1)*mon*s*ky)%polynomial).coefficients(False)];
        mon *= y;
        
    ## Building the derivation matrix of <1,y,y^2,...>
    M = Matrix(F, rows).transpose();
    ## Creating the vector representing y
    y_vector = vector(F, [0,1] + [0]*(polynomial.degree()-2 ));
    ## Building ans solving the system
    to_solve = move(M, y_vector, lambda p : p.derivative(), M.ncols()+1);
    v = to_solve.right_kernel_matrix()[0];
    
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
        for i in range(1,min(equation.get_jp_fo()+2 , to_solve.ncols())):
            try:
                init += [sum(to_solve[j,i](**{dest_var:0})*init[0]**j for j in range(polynomial.degree()))];
            except ZeroDivisionError:
                go_on = False;
                break;
        
        if(go_on and (equation.get_jp_fo()+2  > to_solve.ncols())):
            extra = move(M, vector(F,[el[0] for el in to_solve[:,-1]]), equation.get_jp_fo()+2 -to_solve.ncols());
            init += [sum(extra[j,i](**{dest_var:0})*init[0]**j for j in range(polynomial.degree())) for i in range(extra.ncols())];
    
    ##################################################
    ## Returning the DDFunction
    ##################################################
    return destiny_ring.element(equation, init);
    
def polynomial_inverse(polynomial):
    '''
        Method that computes the functional inverse for a polynomial. As the functional
        inverse of a polynomial is an algebraic series, then it is D-finite.
        
        The polynomial provided must be univariate.
    '''
    ## Local imports
    from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isPolynomial;
    from ajpastor.misc.sequence_manipulation import inv_lagrangian;
    
    ###############################################
    ## Dealing with the polynomial input
    ###############################################
    parent = polynomial.parent();
    if(not (isPolynomial(parent) or isMPolynomial(parent))):
        raise TypeError("The minimal polynomial is NOT a polynomial");
        
    if(polynomial.constant_coefficient() != 0):
        raise ValueError("Non-invertible polynomial given: %s" %polynomial);
    
    ## Building the extra variable needed for algebraicity    
    x = parent.gens()[0];   
    y = str(x)+"_y";
    R = PolynomialRing(parent.fraction_field(), [y]);
    y = R.gens()[0];
    
    ## Building the initial conditions
    coeffs = polynomial.coefficients(False);
    inv = inv_lagrangian(lambda n : factorial(n)*coeffs[n]);
    init = [inv(i) for i in range(len(coeffs))];
    
    return DAlgebraic(polynomial(**{str(x):y})-x, init);
  
##################################################################################
##################################################################################
###
### Private methods
###
##################################################################################
##################################################################################    
def __decide_parent(input, parent = None, depth = 1):
    '''            
        This method is an auxiliary method that decides the parent associated
        with an input given some basic possible parent and depth.
        
        This method converst the input to the parent base or, in case that parent
        is not provided, computes the appropriate DDRing where the input can be consider
        as the coefficient of a differential equation.
        
        If 'parent' is None, then several considerations are made:
            - If 'input' is a Symbolic Expression, we take the variables of it, consider 
            everyone but 'x' as parameters and create the corresponding ParametrizedDDRing 
            of the depth given. The argument 'input' MUST be a polynomial in 'x' and a 
            rational function in any other variable.
            - If 'input' is a polynomial, then the first generator will be consider as the 
            variable of a DDRing and the others as parameters. Then we create the corresponding
            ParametrizedDDRing with the depth given.
            - Otherwise, we create the DDRing of the parent of 'input' of the given depth 
            and try to work with that ring.
    '''
    dR = parent;
    if(dR is None):
        R = input.parent();
        if(input in QQ):
            dR = DFinite.to_depth(depth);
        elif(isinstance(R, sage.symbolic.ring.SymbolicRing)):
            parameters = set([str(el) for el in input.variables()])-set(['x']);
            if(len(parameters) > 0 ):
                dR = ParametrizedDDRing(DDRing(DFinite, depth=depth), parameters);
            else:
                dR = DDRing(PolynomialRing(QQ,x), depth=depth);
        elif(is_MPolynomialRing(R) or is_PolynomialRing(R)):
            parameters = [str(gen) for gen in R.gens()[1:]];
            if(len(parameters) > 0):
                dR = ParametrizedDDRing(DDRing(PolynomialRing(R.base(),R.gens()[0]), depth=depth), parameters);
            else:
                dR = DDRing(PolynomialRing(R.base(),R.gens()[0]), depth = depth);
        else:
            try:
                dR = DDRing(R, depth = depth);
            except Exception:
                raise TypeError("The object provided is not in a valid Parent", e);
    
    return dR.base()(input), dR;

def __check_list(list_of_elements, invalid_vars=[]):
    '''
        This method computes a field of rational functions in several variables given a list of 
        elements, where all the elements can be casted into. This method also allows to ban some variables
        to appear in the elements, raising an error if that happens.
        
        The elements on the list can be:
            - A string: it will be consider as the name of a parameter.
            - Any element with attribute 'variables'. All the variables found will be add as parameters.
            - Elements of a FractionField. The base ring must provide the method 'variables'. All the variables found will be added as parameters.
            
        Once all the variables are computed, we checked that there are no invalid variables and then we 
        build the field of rational functions in the variables found. Then we return this field together 
        with the original list, now with all elements casted to this field.
        
    '''
    invalid_vars = [str(el) for el in invalid_vars];
    all_vars = [];
    parent = QQ;
    for i in range(len(list_of_elements)):
        el = list_of_elements[i];
        if(el in QQ):
            pass;
        elif(isinstance(el, str)):
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
