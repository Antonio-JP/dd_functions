   
from sage.all_cmdline import *   # import sage library

from sage.rings.polynomial.polynomial_ring import is_PolynomialRing; 
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing;
from sage.rings.fraction_field import is_FractionField;

from ajpastor.dd_functions.ddFunction import *;
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing;

from ajpastor.misc.matrix import matrix_of_dMovement;

################################################################################
###
### Second approach: use an infinite polynomial field
###
################################################################################
def is_InfinitePolynomialRing(parent):
    from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_dense as dense;                                                                 
    from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_sparse as sparse;                                
    
    return isinstance(parent, dense) or isinstance(parent, sparse);
    
def get_InfinitePolynomialRingGen(parent, var, with_number = False):
    for gen in parent.gens():
        spl = str(var).split(repr(gen)[:-1]);
        if(len(spl) == 2):
            if(with_number):
                return (gen, int(spl[1]));
            else:
                return gen;
    return None;
    
def get_InfinitePolynomialRingVaribale(parent, gen, number):
    return parent(repr(gen).replace("*", str(number)));
    
#### TODO: Review this function
def infinite_derivative(element, times=1, var=x):
    '''
        Method that takes an element and compute its times-th derivative
        with respect to the variable given by var.
        
        If the element is not in a InfinitePolynomialRing then the method
        'derivative' of the object will be called. Otherwise this method
        returns the derivative following the rules:
            - The coefficients of the polynomial ring are differentiated using
            a recursive call to this method (usually this leads to a call of the
            method '.derivative' of that coefficient).
            - Any variable "#_n" appearing in the InfinitePolynomialRing has
            as derivative the variable "#_{n+1}", i.e., the same name but with
            one higher index.
    '''
    if(not ((times in ZZ) and times >=0)):
        raise ValueError("The argument 'times' must be a non-negative integer");
    elif(times > 1): # Recursive call
        return infinite_derivative(infinite_derivative(element, times-1))
    elif(times == 0): # Empty call
        return element;
        
    ## Call with times = 1
    try:
        parent = element.parent();
    except AttributeError:
        return 0;
    
    ## Simple call: not an InfinitePolynomialRing
    if(not is_InfinitePolynomialRing(parent)):
        try:
            try:
                return element.derivative(var);
            except Exception:
                return element.derivative();
        except AttributeError:
            return parent.zero();
            
    ## IPR call
    ## Symbolic case?
    if(sage.symbolic.ring.is_SymbolicExpressionRing(parent.base())):
        raise TypeError("Base ring for the InfinitePolynomialRing not valid (found SymbolicRing)");
    ### Monomial case
    if(element.is_monomial()):
        ## Case of degree 1 (add one to the index of the variable)
        if(len(element.variables()) == 1 and element.degree() == 1):
            g,n = get_InfinitePolynomialRingGen(parent, element, True);
            return get_InfinitePolynomialRingVaribale(parent, g,n+1);
        ## Case of higher degree
        else:
            # Computing the variables in the monomial and their degrees (in order)
            variables = element.variables();
            degrees = [element.degree(v) for v in variables];
            variables = [parent(v) for v in variables]
            ## Computing the common factor
            com_factor = prod([variables[i]**(degrees[i]-1) for i in range(len(degrees))]);
            ## Computing the derivative of each variable
            der_variables = [infinite_derivative(parent(v)) for v in variables];
            
            ## Computing the particular part for each summand
            each_sum = [];
            for i in range(len(variables)):
                if(degrees[i] > 0):
                    part_prod = prod([variables[j] for j in range(len(variables)) if j != i]);
                    each_sum += [degrees[i]*infinite_derivative(parent(variables[i]))*part_prod];
            
            ## Computing the final result
            return com_factor*sum(each_sum);
    ### Non-monomial case
    else:
        coefficients = element.coefficients();
        monomials = [parent(el) for el in element.monomials()];
        return sum([infinite_derivative(coefficients[i])*monomials[i] + coefficients[i]*infinite_derivative(monomials[i]) for i in range(len(monomials))]);
    
def fromInfinityPolynomial_toFinitePolynomial(poly):
    if(not is_InfinitePolynomialRing(poly.parent())):
        return poly;
    
    gens = poly.variables();
    base = poly.parent().base();
    
    parent = PolynomialRing(base, gens);
    return parent(str(poly));

def fromFinitePolynomial_toInfinitePolynomial(poly):
    parent = poly.parent();
    if(is_InfinitePolynomialRing(poly) and (not is_MPolynomialRing(parent))):
        return poly;
    
    
    names = [str(el) for el in poly.parent().gens()];
    pos = names[0].rfind("_");
    if(pos == -1):
        return poly;
    prefix = names[0][:pos];
    if(not all(el.find(prefix) == 0 for el in names)):
        return poly;
    R = InfinitePolynomialRing(parent.base(), prefix);
    return R(str(poly));
    
def toDifferentiallyAlgebraic_Below(poly, _debug=False):
    '''
    Method that receives a polynomial with variables y_0,...,y_m with coefficients in some ring DD(R) and reduce it to a polynomial
    with coefficients in R.
    
    The optional input '_debug' allow the user to print extra information as the matrix that the determinant is computed.
    '''
    ### Preprocessing the input
    parent = poly.parent();
    if(not is_InfinitePolynomialRing(parent)):
        if(not is_MPolynomialRing(parent)):
            if(not is_PolynomialRing(parent)):
                raise TypeError("The input is not a valid polynomial. Obtained something in %s" %parent);
            if(not str(parent.gens()[0]).startswith("y_")):
                raise TypeError("The input is not a valid polynomial. Obtained %s but wanted something with variables y_*" %poly);
            parent = InfinitePolynomialRing(parent.base(), "y");
        else:
            gens = list(parent.gens());
            to_delete = [];
            for gen in gens:
                if(str(gen).startswith("y_")):
                    to_delete += [gen];
            if(len(to_delete) == 0):
                raise TypeError("The input is not a valid polynomial. Obtained %s but wanted something with variables y_*" %poly);
            for gen in to_delete:
                gens.remove(gen);
            parent = InfinitePolynomialRing(PolynomialRing(parent.base(), gens), "y");
    else:
        if(parent.ngens() > 1 or repr(parent.gen()) != "y_*"):
            raise TypeError("The input is not a valid polynomial. Obtained %s but wanted something with variables y_*" %poly);
    
    poly = parent(poly);
    
    ### Now poly is in a InfinitePolynomialRing with one generator "y_*" and some base ring.
    if(not isinstance(parent.base(), DDRing)):
        print "The base ring is not a DDRing. Returning the original polynomial (reached the bottom)";
        return fromInfinityPolynomial_toFinitePolynomial(poly);
    
    up_ddring = parent.base()
    dw_ddring = up_ddring.base();
    goal_ring = InfinitePolynomialRing(dw_ddring, "y");
    
    coefficients = poly.coefficients();
    monomials = poly.monomials();
    
    ## Arraging the coefficients and organize the vector-space notation
    dict_to_derivatives = {};
    dict_to_vectors = {};
    S = 0;
    for i in range(len(coefficients)):
        coeff = coefficients[i]; monomial = goal_ring(str(monomials[i]));
        if(coeff in dw_ddring):
            if(1 not in dict_to_vectors):
                S += 1;
                dict_to_vectors[1] = goal_ring.zero();
            dict_to_vectors[1] += dw_ddring(coeff)*monomial;
        else:
            used = False;
            for el in dict_to_derivatives:
                try:
                    index = dict_to_derivatives[el].index(coeff);
                    dict_to_vectors[el][index] += monomial;
                    used = True;
                    break;
                except ValueError:
                    pass;                  
            if(not used):
                list_of_derivatives = [coeff]; 
                for j in range(coeff.getOrder()-1):
                    list_of_derivatives += [list_of_derivatives[-1].derivative()];
                dict_to_derivatives[coeff] = list_of_derivatives;
                dict_to_vectors[coeff] = [monomial] + [0 for j in range(coeff.getOrder()-1)];
                S += coeff.getOrder();
    
    rows = [];
    for el in dict_to_vectors:
        if(el == 1):
            row = [dict_to_vectors[el]];
            for i in range(S-1):
                row += [infinite_derivative(row[-1])];
            rows += [row];
        else:
            C = el.equation.companion();
            C = Matrix(goal_ring.base(),[[goal_ring.base()(row_el) for row_el in row] for row in C]);
            rows += [row for row in matrix_of_dMovement(C, vector(goal_ring, dict_to_vectors[el]), infinite_derivative, S)];
        
    M = Matrix(rows);
    if(_debug): print M;
    return M.determinant().numerator();

def diff_to_diffalg(func, _debug=False):
    '''
        Method that compute an differentially algebraic equation for the obect func.
        This objet may be any element in QQ(x) or an element in some DDRing. In the first case
        the equation returned is the simple "y_0 - func". In the latter, we compute the differential
        equation using the linear differential representation of the obect.
        
        The result is always a polynomial with variables "y_*" where the number in the index
        represent the derivative.
    
        The optional argument _debug allows the user to see during execution more data of the computation.
    '''
    try:
        parent = func.parent();
    except AttributeError:
        return PolynomialRing(QQ,"y_0")("y_0 + %s" %func);
    
    if(isinstance(parent, DDRing)):
        R = InfinitePolynomialRing(parent.base(), "y");
        p = sum([R("y_%d" %i)*func[i] for i in range(func.getOrder()+1)], R.zero());
        for i in range(parent.depth()-1):
            p = toDifferentiallyAlgebraic_Below(p, _debug);
        return p;
    else:
        R = PolynomialRing(PolynomialRing(QQ,x).fraction_field, "y_0");
        return R.gens()[0] - func;
    
def inverse_DA(poly, vars=None):
    '''
        Method that computes the DA equation for the multiplicative inverse 
        of the solutions of a DA equation.
        
        We assume that the variables given by vars are the variables representing
        the solution, namely vars[i+1] = vars[i].derivative().
        If vars is not provided, we take all the variables from the polynomial
        that is given.
    '''
    ## Checking that poly is a polynomial
    
    parent = poly.parent();
    if(is_FractionField(parent)):
        parent = parent.base();
    if(is_InfinitePolynomialRing(parent)):
        poly = fromInfinityPolynomial_toFinitePolynomial(poly);
        return inverse_DA(poly, vars);
    if(not (is_PolynomialRing(parent) or is_MPolynomialRing(parent))):
        raise TypeError("No polynomial is given");
    poly = parent(poly);
    
    ## Getting the list of variables
    if(vars is None):
        g = list(poly.parent().gens()); g.reverse();
    else:
        if(any(v not in poly.parent().gens())):
            raise TypeError("The variables given are not in the polynomial ring");
        g = vars;
        
    ## Computing the derivative of the inverse using Faa di Bruno's formula
    derivatives = [1/g[0]] + [sum((falling_factorial(-1, k)/g[0]**(k+1))*bell_polynomial(n,k)(*g[1:n-k+2]) for k in range(1,n+1)) for n in range(1,len(g
))];
    
    ## Computing the final equation
    return poly(**{str(g[i]): derivatives[i] for i in range(len(g))}).numerator();

def func_inverse_DA(func, _debug=False):
    equation = fromFinitePolynomial_toInfinitePolynomial(diff_to_diffalg(func, _debug=_debug));
    
    if(_debug): print equation;
    
    parent = equation.parent();
    y = parent.gens()[0];
    
    n = len(equation.variables());
        
    quot = [FaaDiBruno_polynomials(i, parent)[0]/FaaDiBruno_polynomials(i,parent)[1] for i in range(n)];
    coeffs = [el(**{str(parent.base().gens()[0]) : y[0]}) for el in equation.coefficients()];
    monomials = [el(**{str(y[j]) : quot[j] for j in range(n)}) for el in equation.monomials()];
    
    if(_debug):
        print monomials;
        print coeffs;
    
    sol = sum(monomials[i]*coeffs[i] for i in range(len(monomials)));
    
    if(_debug): print sol;
    if(hasattr(sol, "numerator")):
        return parent(sol.numerator());
    return parent(sol);

def guess_DA_DDfinite(poly, init=[], bS=None, bd = None, all=True):
    '''
        Method that tries to compute a DD-finite differential equation
        for a DA-function with constant coefficients.
        
        It just tries all the possibilities. It uses the Composition class
        to get the possibilities of the orders for the coefficients.
        
        INPUT:
            - poly: polynomial with the differential equation we want to mimic with DD-finite elements
            - init: initial values of the solution of poly
            - bS: bound to the sum of orders in the DD-finite equation
            - db: bound to the order of the DD-finite equation
            - all: compute all the posibles equations
    '''
    if(not poly.is_homogeneous()):
        raise TypeError("We require a homogeneous polynomial");
    
    if(bS is None):
        S = poly.degree(); 
    else:
        S = bS;
    if(bd is None):
        d = S - poly.parent().ngens() + 2;
    else:
        d = bd;
    
    compositions = Compositions(S, length = d+1);
    coeffs = [["a_%d_%d" %(i,j) for j in range(S)] for i in range(d+1)];
    cInit = [["i_%d_%d" %(i,j) for j in range(S-1)] for i in range(d+1)];
    R = ParametrizedDDRing(DFinite, sum(coeffs, [])+sum(cInit,[]));
    R2 = R.to_depth(2);
    coeffs = [[R.parameter(coeffs[i][j]) for j in range(S)] for i in range(d+1)];
    cInit = [[R.parameter(cInit[i][j]) for j in range(S-1)] for i in range(d+1)];
    sols = [];
    
    for c in compositions:
        ## Building the parametrized guess
        e = [R.element([coeffs[i][j] for j in range(c[i])] + [1],cInit[i]) for i in range(d+1)];
        f = R2.element(e);
        if(len(init) > 0):
            try:
                f = f.change_init_values([init[i] for i in range(min(len(init), f.equation.jp_value+1))]);
            except ValueError:
                continue;
        
        ## Computing the DA equation
        poly2 = diff_to_diffalg(f);
        
        ###############################################
        ### Comparing the algebraic equations
        ## Getting a possible constant difference
        m = poly.monomials();
        m2 = poly2.monomials();
        eqs = [];
        C = None;
        for mon in m2:
            c2 = poly2.coefficient(mon);
            if(poly2.parent().base()(poly2.coefficient(mon)).is_constant()):
                C = poly.coefficient(poly.parent()(mon))/c2;
                break;
        if(C is None):
            C = 1;
        elif(C == 0):
            continue;
        
        ### Building all equations from the algebraic equation
        for mon in m2:
            c2 = poly2.coefficient(mon); c = poly.coefficient(poly.parent()(mon));
            eqs += [C*c2 - c];
        
        ##################################################
        ### Comparing the initial values
        for i in range(min(len(init), f.equation.jp_value+1),len(init)):
            try:
                eqs += [f.getInitialValue(i) - init[i]];
            except TypeError:
                break; ## Case when no initial value can be computed
            
        ##################################################
        ### Solving the system (groebner basis)
        P = R.base_field.base(); 
        fEqs = [];
        for el in eqs:
            if(el.parent().is_field()):
                fEqs += [P(str(el.numerator()))];
            else:
                fEqs += [P(str(el))];
                
        gb = ideal(fEqs).groebner_basis();
        if(1 not in gb):
            sols += [(f,gb)];
            if(not all):
                break;
        
        
    if(len(sols) > 0 and not all):
        return sols[0];
    
    return sols;

###################################################################################################
### FAA DI BRUNO functions
###################################################################################################
@cached_function
def FaaDiBruno_polynomials(n, parent):
    if(n < 0):
        raise ValueError("No Faa Di Bruno polynomial can be computed for negative index");
    elif(not(is_InfinitePolynomialRing(parent))):
        if((not(is_PolynomialRing(parent))) and (not(is_MPolynomialRing(parent)))):
            raise TypeError("The parent ring is not valid: needed polynomial rings or InfinitePolynomialRing");
        return FaaDiBruno_polynomials(n, InfinitePolynomialRing(parent, "y"));        
    
    if(parent.base().ngens() == 0 or parent.base().gens()[0] == 1):
        raise TypeError("Needed a inner variable in the coefficient ring");
        
        
    x = parent.base().gens()[0];
    y = parent.gens()[0];
    if(n == 0):
        return (parent(parent.base().gens()[0]), parent.one());
    if(n == 1):
        return (parent.one(), y[1]);
    else:
        prev = [FaaDiBruno_polynomials(k, parent) for k in range(n)];
        ele = -sum(prev[k][0]*bell_polynomial(n,k)(**{"x%d" %i : y[i+1] for i in range(n-k+1)})/prev[k][1] for k in range(1,n))/(y[1]**n);
        return (ele.numerator(), ele.denominator());
    S
####################################################################################################
#### PACKAGE ENVIRONMENT VARIABLES
####################################################################################################
__all__ = ["is_InfinitePolynomialRing", "get_InfinitePolynomialRingGen", "get_InfinitePolynomialRingVaribale", "infinite_derivative", "toDifferentiallyAlgebraic_Below", "diff_to_diffalg", "inverse_DA", "func_inverse_DA", "guess_DA_DDfinite", "FaaDiBruno_polynomials"];
