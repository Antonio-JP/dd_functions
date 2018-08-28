   
from sage.all_cmdline import *   # import sage library

from sage.rings.polynomial.polynomial_ring import is_PolynomialRing; 
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing;

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
    
def infinite_derivative(element, times=1):
    if(times in ZZ and times > 1):
        return infinite_derivative(infinite_derivative(element, times-1))
    try:
        parent = element.parent();
    except AttributeError:
        return 0;
    
    if(not is_InfinitePolynomialRing(parent)):
        try:
            return element.derivative();
        except AttributeError:
            return parent.zero();
    if(element.is_monomial()):
        if(len(element.variables()) == 1):
            return parent(repr(parent.gen()).replace("*", str(int(str(element).split("_")[-1])+1)));
        else:
            degrees = element.degrees();
            variables = [parent("y_%d" %i) for i in range(len(degrees))]; variables.reverse();
            print degrees;
            print variables;
            part = prod(variables[i]**(degrees[i]-1) for i in range(len(degrees)));
            return sum([degrees[i]*infinite_derivative(variables[i])*prod(variables[j] for j in range(len(variables)) if i != j) for i in range(len(variables))]);
    else:
        coefficients = element.coefficients();
        monomials = element.monomials();
        return sum([coefficients[i].derivative()*monomials[i] + coefficients[i]*infinite_derivative(parent(monomials[i])) for i in range(len(monomials))]);
    
def fromInfinityPolynomial_toFinitePolynomial(poly):
    if(not is_InfinitePolynomialRing(poly.parent())):
        return poly;
    
    gens = poly.variables();
    base = poly.parent().base();
    
    parent = PolynomialRing(base, gens);
    return parent(str(poly));
    
def toDifferentiallyAlgebraic_Below(poly):
    '''
    Method that receives a polynomial with variables y_0,...,y_m with coefficients in some ring DD(R) and reduce it to a polynomial
    with coefficients in R.
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
        coeff = coefficients[i]; monomial = goal_ring(monomials[i]);
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
                    dict_to_derivatives[el][index] += monomial;
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
            rows += [row for row in matrix_of_dMovement(el.equation.companion(), vector(goal_ring, dict_to_vectors[el]), infinite_derivative, S)];
        
    M = Matrix(goal_ring, rows);
    print M;
    
    return M.determinant();

def diff_to_diffalg(func):
    try:
        parent = func.parent();
    except AttributeError:
        return PolynomialRing(QQ,"y_0")("y_0 + %s" %func);
    
    if(isinstance(parent, DDRing)):
        R = InfinitePolynomialRing(parent.base(), "y");
        p = sum(func[i]*R("y_%d" %i) for i in range(func.getOrder()+1));
        for i in range(parent.depth()-1):
            p = toDifferentiallyAlgebraic_Below(p);
    else:
        R = PolynomialRing(PolynomialRing(QQ,x).fraction_field, "y_0");
        return R.gens()[0] - func;


################################################################################
###
### Special cases for diff_to_diffalg
###
################################################################################
## Polynomial in x case
#def diff_to_diffalg_poly(func):
#    base, is_x = __get_base_field(func.parent());
#    final_ring = PolynomialRing(base, ["x", "y0"], order='deglex');
#    x = final_ring.gens()[0];
#    y = final_ring.gens()[1];
#    return y - final_ring(func);
#    
## D-finite case
#def diff_to_diffalg_dfinite(func):
#    if(not (isinstance(func.parent(), DDRing) and func.parent().depth()==1)):
#        raise TypeError("diff_to_diffalg_dfinite called with a non-dfinite function");
#    if(func.is_constant):
#        return diff_to_diffalg(func(0));
#    order = func.getOrder();
#    base, is_x = __get_base_field(func.parent().base());
#            
#    name_vars = [];
#    if(is_x):
#        name_vars += ["x"];
#    name_vars += ["y%d" %i for i in range(order+1)];
#    final_ring = PolynomialRing(base, name_vars, order='deglex');
#    if(is_x):
#        x = final_ring.gens()[0];
#        y = final_ring.gens()[1:];
#    else:
#        y = final_ring.gens();
#    
#    return sum(y[i]*final_ring(func.equation[i]) for i in range(order+1));
#    
## DD-finite case
#def diff_to_diffalg_ddfinite(func):
#    if(not (isinstance(func.parent(), DDRing) and func.parent().depth()==2)):
#        raise TypeError("diff_to_diffalg_ddfinite called with a non-ddfinite function");
#    
#    base, is_x = __get_base_field(func.parent().base().base());
#        
#    polys = [diff_to_diffalg(coeff) for coeff in func.equation.getCoefficients()];
#    orders = [coeff.getOrder() for coeff in func.equation.getCoefficients()];
#    S = sum(orders);
#    name_vars = ["y%d" %i for i in range(S+func.getOrder())];
#    if(is_x):
#        name_vars = ["x"] + name_vars;
#    final_ring = PolynomialRing(base, name_vars, order='deglex');
#    x = None;
#    if(is_x):
#        x = final_ring.gens()[0];    
#        y = final_ring.gens()[1:];
#    else:
#        y = final_ring.gens();
#    first_row = [];
#    for i in range(len(orders)):
#        if(func.equation[i].getOrder() > 1 or polys[i].degree() > 1):
#            first_row += [[final_ring.one()] + [final_ring.zero() for j in range(1,orders[i])]];
#    first_row += [final_ring.zero()];
#    rows = [first_row];
#    
#    
#    for i in range(S):
#        # Each element is r[-1][a]'+r[-1][a-1]+r[-1][-1]*eq
#        # Part: r[-1][a]'
#        new_row = [[__get_derivative(el, [],[],y,x) for el in list] for list in rows[-1][:-1]] + [__get_derivative(rows[-1][-1], [],[],y,x)];
#        
#        # Part: r[-1][a-1]
#        for i in range(len(rows[:-1])):
#            for j in range(1, len(rows[-1][:-1][i])):
#                new_row[i][j] += rows[-1][i][j-1];
#            
#        # Part: r[-1][-1]*eq 
#        for i in range(len(new_row)-1):
#            for j in range(len(new_row[i])):
#                coeff = polys[i].coefficient({y[-1]:1});
#                new_row[i][j] -= polys[i].coefficient({y[j]:1})/coeff;
#                new_row[-1] -= polys[i].coefficients()[-1]/coeff;
#        
#        dens = sum([[el.denominator() for el in list] for list in new_row[:-1]],[]);
#        dens += [new_row[-1].denominator()]; 
#        new_lcm = lcm(dens);
#        fin_new_row = [[new_lcm*el for el in list] for list in new_row[:-1]];
#        fin_new_row += [new_lcm*new_row[-1]];
#        rows += [fin_new_row];
#        
#    mat = [sum(rows[i][:-1], []) + [rows[i][-1]] for i in range(len(rows))];
#    M = Matrix(mat);
#    return M.determinant();
#        
#@cached_function
#def diff_to_diffalg(func):
#    ## Particular imports for this method
#    from sage.categories.pushout import pushout;
#
#    ## Dificult case: diff. definable function
#    if(isinstance(func, DDRing.Element)):
#        order = func.getOrder();
#        base = func.parent().base();
#        
#        ########################################################################
#        ## Recursive-case
#        if(func.parent().depth() > 2):                        
#            # Main recursive step
#            coeff_poly = [diff_to_diffalg(coeff) for coeff in func.equation.getCoefficients()];
#            
#            # Building some data for getting the final polynomial ring
#            base = reduce(pushout, [poly.parent().base() for poly in coeff_poly]);
#            coeff_order = [];
#            is_x = False;
#            for i in range(order+1):
#                try:
#                    ## Case x in poly.parent()
#                    coeff_poly[i].parent()('x');
#                    coeff_order += [coeff_poly[i].parent().ngens()-2];
#                    is_x = True;
#                except:
#                    coeff_order += [coeff_poly[i].parent().ngens()-1];
#                    
#            # Getting the variables needed for the middle step
#            name_vars = ["z%d_%d" %(i,j) for i in range(order+1) for j in range(coeff_order[i],-1,-1)];
#            if(is_x):
#                name_vars += ["x"];
#            
#            exe = 0;
#            eqs = [];
#            while(True):    
#                max_order = 1+exe;#max(coeff_order)+exe;
#                               
#                # Building the middle polynomial ring
#                mon_order = [TermOrder('deglex', coeff_order[i]+1) for i in range(order+1)];
#                if(is_x):
#                    mon_order += [TermOrder('deglex', 1)];
#                mon_order += [TermOrder('lex', order+max_order+1)];
#                mon_order = reduce(lambda p,q : p + q, mon_order);
#                middle_ring = PolynomialRing(base, name_vars_f, order=mon_order);
#                
#                # Recovering the variables of the polynomial ring
#                gens = middle_ring.gens();
#                z = [];
#                j = 0;
#                for i in range(order+1):
#                    z += [list(gens[j:j+coeff_order[i]+1])]
#                    z[-1].reverse();
#                    j += coeff_order[i]+1;
#                if(is_x):
#                    x = gens[j];
#                    j += 1;
#                else:
#                    x = None;
#                y = list(gens[j:]); y.reverse();
#                            
#                # Computing all the required polynomials for the reduction
#                # We start with the equations from the coefficients
#                eqs = [middle_ring(el) for el in eqs];
#                for i in range(len(eqs),order+1):
#                    args = {"y%d" %j : z[i][j] for j in range(coeff_order[i]+1)};
#                    eqs += [coeff_poly[i](**args)];
#                
#                # We keep computing the derivatives from the equation of func
#                if(len(eqs) < order+2):
#                    eqs += [sum(y[i]*z[i][0] for i in range(order+1))];
#                for i in range(len(eqs), order+2+max_order):
#                    eqs += [__get_derivative(eqs[-1], eqs[:order+1], z,y,x)];
#                            
#                # Now we compute a Groebner-basis to eliminate all possible variables
#                # It is important to remark that the order of the variables were chosen
#                # so all possible variables are eliminated and the smallest possible
#                # polynomial equation remains.
#                gb = ideal(eqs).groebner_basis();
#                
#                # We get the final ring for the equation
#                final_vars = [str(y[i]) for i in range(len(y))];
#                if(is_x):
#                    final_vars = ["x"] + final_vars;
#                final_ring = PolynomialRing(base, final_vars, order='deglex');
#                try:
#                    return final_ring(str(gb[-1]));
#                except TypeError:
#                    print "The polynomial obtained has too many variables:\n\t- Expected: %s\n\t- Got: %s" %(final_ring.gens(), gb[-1]);
#                
#                exe += 1;
#            
#        ########################################################################
#        ## Basic cases
#        elif(func.parent().depth() == 2):
#            return diff_to_diffalg_ddfinite(func);
#        else:
#            return diff_to_diffalg_dfinite(func);
#            
#    ############################################################################
#    ## Base case: polynomial or non-diff_definable functions
#    return diff_to_diffalg_poly(func);
#    
#def __get_base_field(base):
#    ## Particular imports for this method
#    from sage.rings.polynomial.polynomial_ring import is_PolynomialRing;
#    from sage.misc.functional import is_field;
#    
#    ## Checking the case is R(x)
#    if(is_field(base) and not (base.base() == base)):
#        return __get_base_field(base.base());
#        
#    ## Checking the case is R[x]
#    is_x = False;
#    if(is_PolynomialRing(base) and str(base.gens()[0]) == 'x'):
#        base = base.base();
#        is_x = True;
#            
#    if(not base.is_field()):
#        base = base.fraction_field();
#        
#    return base, is_x;
#    
#__CACHE_OF_DICS = {};
#    
#def __get_derivative(poly, equations, z,y,x):
#    if(poly.is_constant()):
#        return 0;
#    global __CACHE_OF_DICS;
#    key = tuple([tuple(equations), tuple([tuple(row) for row in z]), tuple(y)]);
#    dic_of_derivatives = __CACHE_OF_DICS.get(key, {});
#    
#    coeffs = poly.coefficients(); monomials = poly.monomials();
#    gens = poly.parent().gens();
#    der_mon = [];
#    for mon in monomials:
#        degrees = mon.degrees();
#       basic = prod(gens[i]**max(0,degrees[i]-1) for i in range(len(gens)));
#        extra = poly.parent().zero();
#        for i in range(len(gens)):
#            if(degrees[i] > 0):
#                extra += degrees[i]*__get_variable_derivative(dic_of_derivatives, gens[i], equations, z, y ,x)*prod(gens[j] for j in range(len(gens)) if (j != i and degrees[j] > 0));
#        der_mon += [basic*extra];
#
#    __CACHE_OF_DICS[key] = dic_of_derivatives;
#
#    element = sum(coeffs[i]*der_mon[i] for i in range(len(coeffs)));
#    if(hasattr(element, "numerator")):
#        element = element.numerator();
#        
#    return element;
#    
#def __get_variable_derivative(cache, var, equations, z,y,x):
#    if(var not in cache):
#        if(var == x):
#            cache[var] = 1;
#        if(var in y):
#            cache[var] = y[y.index(var)+1];
#        else:
#            for i in range(len(z)):
#                if(var in z[i]):
#                    j = z[i].index(var);
#                    if(j < len(z[i])-1):
#                        cache[var] = z[i][j+1];
#                    else:
#                        # Computing derivative of z[i][-1]
#                        d = equations[i].degree(z[i][j]);
#                        alpha = [equations[i].coefficient({z[i][j]: k}) for k in range(d+1)];
#                        cache[var] = -sum(__get_derivative(alpha[i], equations,z,y,x)*z[i][-1]^i for i in range(d+1))/sum(alpha[i]*i*z[i][-1]^(i-1) for i in range(1,d+1));
#    return cache[var];
#    
####################################################################################################
#### PACKAGE ENVIRONMENT VARIABLES
####################################################################################################
__all__ = ["is_InfinitePolynomialRing", "get_InfinitePolynomialRingGen", "get_InfinitePolynomialRingVaribale", "infinite_derivative", "toDifferentiallyAlgebraic_Below", "diff_to_diffalg"];
