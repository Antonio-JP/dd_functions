r"""
Python file for DDFunctions as DA-Functions

This package provides functions to work with DDFunctions as differentially algebraic functions.

EXAMPLES::

    sage: from ajpastor.dd_functions import *
    sage: DFinite
    DD-Ring over (Univariate Polynomial Ring in x over Rational Field)
    
TODO::
    * Do the examples section of this documentation
    * Document this package
    * Review the functionality of this package

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
from functools import reduce
# Sage imports
from sage.all import (prod, PolynomialRing, QQ, ZZ, prod, Matrix, vector,
                     kronecker_delta, falling_factorial, bell_polynomial, Compositions,
                     ideal, cached_function, SR)

from sage.graphs.digraph import DiGraph

from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing
from sage.rings.fraction_field import is_FractionField

# ajpastor.dd_functions imports
from ajpastor.dd_functions import (is_DDRing, is_DDFunction, DDRing, ParametrizedDDRing,
                                   DFinite, Exp)
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing

from ajpastor.misc.matrix import matrix_of_dMovement
from ajpastor.misc.matrix import vector_derivative

################################################################################
###
### Utilities functions for InfinitePolynomialRings
###
################################################################################
def is_InfinitePolynomialRing(parent):
    from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_dense as dense                                                            
    from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_sparse as sparse
    
    return isinstance(parent, dense) or isinstance(parent, sparse)
    
def get_InfinitePolynomialRingGen(parent, var, with_number = False):
    for gen in parent.gens():
        spl = str(var).split(repr(gen)[:-1])
        if(len(spl) == 2):
            if(with_number):
                return (gen, int(spl[1]))
            else:
                return gen
    return None
    
#### TODO: Review this function
def infinite_derivative(element, times=1, derivation=None):
    r'''
        Method that computes the times-th derivative of a differential polynomial.

        Given a differential ring `(R,\partial)`, the ring of differential
        polynomials (denoted by `R\{y\}`) is the polynomial ring with infinitely
        many variables

        .. MATH::

            R[y_0, y_1, y_2, \ldots],

        where the derivation `\partial` is extended such that

        .. MATH::

            \partial(y_i) = y_{i+1}\quad \forall i \in \mathbb{N}.

        This method takes as an input a differential polynomial and it computes
        its derivative. The derivation on `R` will be assume with the 
        method ``derivative``. However, the user is allowed to force
        a particular derivation with the input ``derivation``.

        The output of this method is always a differential polynomial. If the 
        user wants the output to be considered as a multivariate polynomial
        (fixing the amount of variables), the method ``polynomial`` from
        the output do that job.

        INPUT:
            * ``element``: the differential polynomial we want to differentiate. 
              This object has to be a polynomial with infinitely many variables.
            * ``times``: a positive integer indicating the amount of derivations to compute.
            * ``derivation``: derivation of the coefficients. If set to ``None``, we use
              the derivation on the coefficients of the polynomial ring.

        OUTPUT:

            A polynomial with infinitely many variables on the same ring as ``element``
            representing the derivation of ``element``.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: R.<y> = InfinitePolynomialRing(QQ['a']); a = R('a')
            sage: infinite_derivative(y[2]^2 - a)
            2*y_2*y_3 - 1
            sage: infinite_derivative(a*y[1])
            a*y_2 + y_1
            sage: infinite_derivative(y[2]^2 - a, derivation=lambda p : 0)
            2*y_2*y_3
            sage: infinite_derivative(a*y[1], derivation=lambda p : 0)
            a*y_2
            sage: infinite_derivative(a*y[1], times = 2)
            a*y_3 + 2*y_2
            sage: infinite_derivative(y[5]^7, times = 0)
            y_5^7
            sage: infinite_derivative(R.base()(a))
            1
            sage: infinite_derivative(y[2]^2, times = -1)
            Traceback (most recent call last):
            ...
            ValueError: The argument 'times' must be a non-negative integer
            
    '''
    if(not ((times in ZZ) and times >=0)):
        raise ValueError("The argument 'times' must be a non-negative integer")
    elif(times > 1): # Recursive call
        return infinite_derivative(infinite_derivative(element, times-1, derivation), 1, derivation)
    elif(times == 0): # Empty call
        return element
        
    ## Call with times = 1
    parent = element.parent()
    
    ##Simple call: parent is a Fraction Field
    if(is_FractionField(parent)):
        parent = parent.base()
        n = parent(element.numerator()); dn = infinite_derivative(n,1,derivation)
        d = parent(element.denominator()); dd = infinite_derivative(d,1,derivation)
        return (dn*d - n*dd)/d**2
    
    ## Simple call: not an InfinitePolynomialRing
    if(not is_InfinitePolynomialRing(parent)):
        ## We assume that element is in a basic differential ring
        ## We use ``derivation`` or the usual derivative
        if(derivation is None):
            return element.derivative()
        return derivation(element)

    gens = parent.gens()
            
    ## IPR call
    ## Symbolic case?
    if(parent.base() == SR):
        raise TypeError("Base ring for the InfinitePolynomialRing not valid (found SymbolicRing)")
    ## Zero case
    if(element == 0):
        return 0
    ### Monomial case
    if(element.is_monomial()):
        if(len(element.variables()) == 1): ## Case of 1 variable
            v = element.variables()[0]
            g = [el for el in gens if str(v).startswith(repr(el)[:repr(el).rindex("_")])][0]
            n = int(str(v)[str(v).rfind("_")+1:])
            d = element.degree()
            
            return d*g[n]**(d-1)*g[n+1]
        
        else: ## Case of several variables
            # Computing the variables in the monomial and their degrees (in order)
            variables = element.variables()
            degrees = [element.degree(v) for v in variables]
            variables = [parent(v) for v in variables]

            ## Computing the common factor
            com_factor = prod([variables[i]**(degrees[i]-1) for i in range(len(degrees))])
            ## Computing the derivative of each variable
            der_variables = [infinite_derivative(parent(v),1,derivation) for v in variables]
            
            ## Computing the particular part for each summand
            each_sum = []
            for i in range(len(variables)):
                if(degrees[i] > 0):
                    part_prod = prod([variables[j] for j in range(len(variables)) if j != i])
                    each_sum += [degrees[i]*der_variables[i]*part_prod]
            
            ## Computing the final result
            return com_factor*sum(each_sum)
    ### Non-monomial case
    else:
        coefficients = element.coefficients()
        monomials = [parent(el) for el in element.monomials()]
        return sum(
            infinite_derivative(coefficients[i],1,derivation)*monomials[i] + 
            coefficients[i]*infinite_derivative(monomials[i],1,derivation) 
        for i in range(len(monomials)))
    
################################################################################
###
### Changes from and to InfinitePolynomialRings and MultivariatePolynomialRings
###
################################################################################
def fromInfinityPolynomial_toFinitePolynomial(poly):
    if(not is_InfinitePolynomialRing(poly.parent())):
        return poly
    
    gens = poly.variables()
    base = poly.parent().base()
    
    parent = PolynomialRing(base, gens)
    return parent(str(poly))

def fromFinitePolynomial_toInfinitePolynomial(poly):
    parent = poly.parent()
    if(is_InfinitePolynomialRing(poly) and (not is_MPolynomialRing(parent))):
        return poly
    
    
    names = [str(el) for el in poly.parent().gens()]
    pos = names[0].rfind("_")
    if(pos == -1):
        return poly
    prefix = names[0][:pos]
    if(not all(el.find(prefix) == 0 for el in names)):
        return poly
    R = InfinitePolynomialRing(parent.base(), prefix)
    return R(poly)
    
################################################################################
###
### Methods for computing Diff. Algebraic equations with simpler coefficients
###
################################################################################
def diffalg_reduction(poly, infinite=False, debug=False):
    '''
    Method that receives a polynomial 'poly' with variables y_0,...,y_m with coefficients in some ring DD(R) and reduce it to a polynomial
    'result' with coefficients in R where, for any function f(x) such that poly(f) == 0, result(f) == 0.
    
    The algorithm works as follows:
        1 - Collect all the coefficients and their derivatives
        2 - Perform the simplification to each pair of coefficients
        3 - Perform the simplification for the last derivatives of the remaining coefficients --> gens
        4 - Build the final derivation matrix for 'gens'
        5 - Create a vector v for represent 'poly' w.r.t. 'gens'
        6 - Build a square matrix --> M = (v | v' | ... | v^(n))
        7 - Return det(M)
    
    INPUT:
        - poly: a polynomial with variables y_0,...,y_m. Also an infinite polynomial with variable y_* is valid.
        - infinite: if True the result polynomial will be an infinite polynomial. Otherwise, a finite variable polynomial will be returned.
        - debug: if True, the steps of the algorithm will be printed.
    '''
    ## Processing the input infinite
    if(infinite):
        r_method = fromFinitePolynomial_toInfinitePolynomial
    else:
        r_method = fromInfinityPolynomial_toFinitePolynomial
        
    ### Preprocessing the input poly
    _, poly, dR = __check_input(poly, debug)
    
    if(not is_DDRing(dR)):
        raise TypeError("diffalg_reduction: polynomial is not over a DDRing")
    
    R = dR.base()
    
    ## Step 1: collecting function and derivatives
    __dprint("---- DEBUGGING PRINTING FOR diffalg_reduction", debug)
    __dprint("R: %s" %R, debug)
    __dprint("-- Starting step 1", debug)
    coeffs = poly.coefficients() # List of original coefficients
    __dprint("Coefficients: %s" %("["+reduce(lambda p,q : p+", "+q, [repr(coeff) for coeff in coeffs])+"]"), debug)            
        
    ocoeffs = coeffs # Extra variable with the same list
    monomials = poly.monomials() # List of monomials
    l_of_derivatives = [[f.derivative(times=i) for i in range(f.getOrder())] for f in coeffs] # List of derivatives for each coefficient
    
    ## Step 2: simplification of coefficients
    __dprint("-- Starting step 2", debug)
    graph = __simplify_coefficients(R, coeffs, l_of_derivatives, debug)
    maximal_elements = __digraph_roots(graph, debug)
    
    ## Detecting case: all coefficients are already simpler
    if(len(maximal_elements) == 1 and maximal_elements[0] == -1 and len(graph.outgoing_edges(-1)) == len(graph.edges())):
        __dprint("Detected simplicity: returning the same polynomial over the basic ring", debug)
        return r_method(InfinitePolynomialRing(R, names=["y"])(poly))
    
    # Reducing the considered coefficients
    coeffs = [coeffs[i] for i in maximal_elements if i != (-1)]
    l_of_derivatives = [l_of_derivatives[i] for i in maximal_elements if i != (-1)]
                
    ## Step 3: simplification with the derivatives
    __dprint("-- Starting step 3", debug)
    drelations = __simplify_derivatives(l_of_derivatives, debug)
    
    ## Building the vector of final generators
    gens = []
    if(-1 in maximal_elements):
        gens = [1]
    gens = sum([l_of_derivatives[i][:drelations[i][0]] for i in range(len(coeffs))], gens)
    S = len(gens)
    __dprint("Resulting vector of generators: %s" %gens, debug)
    
    ## Step 4: build the derivation matrix
    __dprint("-- Starting step 4", debug)
    C = __build_derivation_matrix(gens, coeffs, drelations, debug)
    cR = InfinitePolynomialRing(C.base_ring(), names=["y"])
    
    ## Step 5: build the vector v
    __dprint("-- Starting step 5", debug)
    v = __build_vector(ocoeffs, monomials, graph, drelations, cR, debug)
    
    ## Step 6: build the square matrix M = (v, v',...)
    __dprint("-- Starting step 6", debug)
    __dprint("Computing derivatives from the vector (step 5) using the matrix (step 4)", debug)
    derivative = infinite_derivative
    M = matrix_of_dMovement(C, v, derivative, S)
    
    __dprint("Vector of generators:\n\t%s" %gens, debug)
    __dprint("Final matrix (vector in rows):\n\t%s" %(str(M.transpose()).replace('\n', '\n\t')), debug)
    __dprint("Returning the determinant", debug)
    __dprint("---- DEBUGGING PRINTING FOR diffalg_reduction (finished)", debug)
    return r_method(M.determinant())

################################################################################
################################################################################
### Some private methods for diffalg_reduction
################################################################################
################################################################################

def __check_input(poly, debug=False):
    '''
    Method that check and cast the polynomial input accordingly to our standards.
    
    The element 'poly' must be a polynomial with variables y_0,...,y_m with coefficients in some ring
    '''
    parent = poly.parent()
    if(not is_InfinitePolynomialRing(parent)):
        if(not is_MPolynomialRing(parent)):
            if(not is_PolynomialRing(parent)):
                raise TypeError("__check_input: the input is not a valid polynomial. Obtained something in %s" %parent)
            if(not str(parent.gens()[0]).startswith("y_")):
                raise TypeError("The input is not a valid polynomial. Obtained %s but wanted something with variables y_*" %poly)
            parent = InfinitePolynomialRing(parent.base(), "y")
        else:
            gens = list(parent.gens())
            to_delete = []
            for gen in gens:
                if(str(gen).startswith("y_")):
                    to_delete += [gen]
            if(len(to_delete) == 0):
                raise TypeError("__check_input: the input is not a valid polynomial. Obtained %s but wanted something with variables y_*" %poly)
            for gen in to_delete:
                gens.remove(gen)
            parent = InfinitePolynomialRing(PolynomialRing(parent.base(), gens), "y")
    else:
        if(parent.ngens() > 1 or repr(parent.gen()) != "y_*"):
            raise TypeError("__check_input: the input is not a valid polynomial. Obtained %s but wanted something with variables y_*" %poly)
    
    poly = parent(poly)
    dR = parent.base()
    
    return (parent, poly, dR)

def __simplify_coefficients(base, coeffs, derivatives, debug=False):
    '''
    Method that get the relations for the coefficients within their derivatives. The list 'coeffs' is the list to simplify
    and ;derivatives' is a list of lists with the derivatives of each element of 'coeffs' that we will consider.
    
    It returns a pair (graph, relations) where:
        - graph: a forest of the points of minimal depth with all the relations
        - relations: a dictionary which tells for each i < j, how the ith coefficient is related with the jth coefficient
            (see __find_relation to know how that relation is expressed).
    '''
    # Checking the input
    n = len(coeffs)
    if(len(derivatives) < n):
        raise ValueError("__simplify_coefficients: error in size of the input 'derivatives'")
    
    E = range(n)
    R = []
    
    # Checking the simplest cases (coeff[i] in R)
    simpler = []
    for i in range(n):
        if(coeffs[i] in base):
            if((-1) not in E):
                E += [-1]
            R += [(-1,i,(0,0,coeffs[i]))]
            simpler += [i]
    
    __dprint("Simpler coefficients (related with -1): %s" %simpler, debug)
    # Starting the comparison
    for i in range(n):
        for j in range(i+1, n):
            # Checking (i,j)
            if(not(j in simpler)):
                rel = __find_relation(coeffs[j], derivatives[i], debug)
                if(not(rel is None)):
                    R += [(i,j,rel)]
                    continue
            # Checking (j,i)
            if(not(i in simpler)):
                rel = __find_relation(coeffs[i], derivatives[j], debug)
                if(not(rel is None)):
                    R += [(j,i,rel)]
    
    # Checking if the basic case will be used because of the relations
    if((-1) not in E and any(e[2][1][1] != 0 for e in R)):
        E += [-1]
    
    # Building the graph and returning
    __dprint("All relations: %s" %R, debug)
    graph = DiGraph([E,R])
    __dprint("Edges: %s" %graph.edges(), debug)
    
    # Deleting spurious relations and returning
    return __min_span_tree(graph, debug)

def __simplify_derivatives(derivatives, debug=False):
    '''
    Method to get the relations for the derivatives of the coefficients. The argument 'derivatives' contains a list of lists for which
    one we will see if the last elements have relations with the firsts.
    
    It returns a list of tuples 'res' where 'res[i][0] = k' if the kth function in 'derivatives[i]' is the first element on the list
    with relations with the previous elements and 'res[i][1]' is the relation found.
    If no relation is found, a tuple (None,None) is added to the list.
    '''
    res = []
    for i in range(len(derivatives)):
        to_add = (None,None)
        for k in range(len(derivatives[i])-1,0,-1):
            relation = __find_relation(derivatives[i][k], derivatives[i][:k-1], debug)
            if(not (relation is None)):
                to_add = (k,relation)
                break
        res += [to_add]
            
    __dprint("Found relations with derivatives: %s" %res, debug)
    return res
    
def __find_relation(g,df, debug=False):
    '''
    Method that get the relation between g and the list df. 
    
    It returns a tuple (k,res) where:
        - k: the first index which we found a relation
        - res: the relation (see __find_linear_relation to see how such relation is expressed).
        
    Then the following statement is always True:
        g == df[k]*res[0] + res[1]
    '''
    __dprint("** Checking relations between %s and %s" %(repr(g), df), debug)
    for k in range(len(df)):
        res = __find_linear_relation(g,df[k])
        if(not (res is None)):
            __dprint("Found relation:\n\t(%s) == [%s]*(%s) + [%s]" %(repr(g),repr(res[0]), repr(df[k]), repr(res[1])), debug)
            __dprint("*************************", debug)
            return (k,res)
    __dprint("Nothing found\n*************************", debug)
    
    return None
    
def __find_linear_relation(f,g):
    '''
    This method receives two DDFunctions and return two constants (c,d) such that f = cg+d. 
    None is return if those constants do not exist.
    '''
    if(not (is_DDFunction(f) and is_DDFunction(g))):
        raise TypeError("find_linear_relation: The functions are not DDFunctions")
    
    ## Simplest case: some of the functions are constants is a constant
    if(f.is_constant):
        return (f.parent().zero(), f(0))
    elif(g.is_constant):
        return None
    
    try:
        of = 1; og = 1
        while(f.getSequenceElement(of) == 0): of += 1
        while(g.getSequenceElement(og) == 0): og += 1
        
        if(of == og):
            c = f.getSequenceElement(of)/g.getSequenceElement(og)
            d = f(0) - c*g(0)
            
            if(f == c*g + d):
                return (c,d)
    except Exception:
        pass
    
    return None
    
def __min_span_tree(digraph, debug=False):
    '''
    Method that computes a forest from a directed graph containing all vertices and having the minimal depth.
    
    It is computed with a breadth first search.
    '''
    to_search = __digraph_roots(digraph, debug)
    i = 0
    done = []
    edges = []
    while(i < len(to_search)):
        v = to_search[i]
        if(not (v in done)):
            for e in digraph.outgoing_edges(v):
                if(not(e[1] in to_search)):
                    to_search += [e[1]]
                    edges += [e]
            done += [v]
        i += 1
    return DiGraph([digraph.vertices(),edges])

def __digraph_roots(digraph, debug=False):
    '''
    Method that computes the roots of a directed graph. We consider a vertex v to be a root if there
    are not edges (v,w) in the graph.
    '''
    return [v for v in digraph.vertices() if digraph.in_degree(v) == 0]
    
def __build_derivation_matrix(gens, coeffs, drelations, debug=False):
    '''
        Method to build a derivation matrix 'C' for the vector of generators 'gen'.
        
        All the information about the coefficients and their relations are given
        by the arguments 'coeffs' (list of basic elements for 'gens') and 
        'drelations' (relations between elements in 'coeffs' and the last derivative
        on 'gens').
        
        It could be that gens[0] == 1. This element must be treated in a specific
        way collecting all the relations on 'drelations'. 
    '''
    __dprint("Building derivation matrix for %s" %gens, debug)
    
    rows = [] # Variable for the rows of the matrix M
    
    constant = (gens[0] == 1) # Flag variable for gens[0] == 1
    coeff_order = [] # Collecting the real order of each coefficient in the vector space
    for i in range(len(coeffs)):
        if(drelations[i][0] is None):
            coeff_order += [coeffs[i].getOrder()]
        else:
            coeff_order += [drelations[i][0]]
    coeff_index = [0] # Variable for the index of coeff[i] in gens
    if(constant): coeff_index[0] = 1
    for i in range(1, len(coeffs)): coeff_index += [coeff_index[-1]+coeff_order[i-1]]
    
    __dprint("Is there constant: %s" %constant, debug)
    __dprint("Orders: %s\nIndices: %s" %(coeff_order, coeff_index), debug)
    
    ## Considering the case that gens[0] == -1
    if(constant):
        new_row = [0]
        for i in range(len(coeffs)):
            new_row += [0 for j in range(coeff_order[i])]
            if(not (drelations[i][1] is None)):
                new_row[-1] = drelations[i][1][1][1]
        rows += [new_row]
        
    ## Now we loop through all the coefficients in coeffs
    for i in range(len(coeffs)):
        com = coeffs[i].equation.companion()
        for j in range(coeff_order[i]):
            ## Building the jth row for coeff[i]
            new_row = [0 for k in range(coeff_index[i])] # First columns for the row
            
            ## Middle columns for the row
            new_row += [com[j][k] for k in range(coeff_order[i]-1)]
            if((not (drelations[i][0] is None)) and (drelations[i][1][0] == j)):
                new_row += [drelations[i][1][1][0]]
            else:
                new_row += [com[j][coeff_order[i]-1]]
            
            new_row += [0 for k in range(coeff_index[i]+coeff_order[i], len(gens))] # Last columns for the row
            
            ## Adding the resulting row
            rows += [new_row]
            
    rows = Matrix(rows)
    
    __dprint("** Matrix:\n%s\n*******" %rows, debug)
    
    return rows

def __build_vector(coeffs, monomials, graph, drelations, cR, debug=False):
    '''
        This method builds a vector that represent the polynomial generated by
        'coeffs' and 'monomials' using the relations contained in 'graph'
        and 'drelations' w.r.t. the vector 'gens'.
        
        The output vector v satisfies:
            sum(coeffs[i]*monomials[i]) == sum(v[j]*gens[j])
    '''
    # Computing important data for each coefficient
    maximal_elements = [el for el in __digraph_roots(graph) if el != -1]
    coeff_order = []
    for i in range(len(coeffs)):
        if(i in maximal_elements and (not (drelations[maximal_elements.index(i)][0] is None))):
            coeff_order += [drelations[maximal_elements.index(i)][0]]
        else:
            coeff_order += [coeffs[i].getOrder()]
    constant = (-1 in graph.vertices())
    
    __dprint("Is there constant: %s" %constant, debug)
    
    # Computing vectors and companion matrices for each element
    vectors = [vector(cR, [monomials[i]] + [0 for i in range(coeff_order[i]-1)]) for i in range(len(coeffs))]
    trans = []
    for i in range(len(coeffs)):
        if(i in maximal_elements and (not (drelations[maximal_elements.index(i)][0] is None))):
            relation = drelations[maximal_elements.index(i)]
            C = []
            for j in range(relation[0]):
                new_row = [el for el in coeffs[i].equation.companion()[j][:relation[0]-1]] + [0]
                if(j == relation[1][0]):
                    new_row[-1] = relation[1][1][0]
                C += [new_row]
            C = Matrix(C)
            trans += [(drelations[maximal_elements.index(i)][1][1][1], C)]
        else:
            trans += [(0, coeffs[i].equation.companion())]
            
    if(debug):
        print("--- Transitions to nodes:")
        for i in range(len(trans)):
            print("+++ %s --> Constant: %s; Matrix:\n%s" %(i, trans[i][0], trans[i][1]))
        print("-------------------------")
    
    const_val = 0
    # Doing a Tree Transversal in POstorder in the graph to pull up the vectors
    # Case for -1
    if(constant):
        maximal_elements = [-1] + maximal_elements
    #    const_val = sum(cR(coeffs[e[1]])*monomials[coeffs[e[1]]] for e in graph.outgoing_edges(-1))
    # we start with the reverse list of maximal_elements as stack
    stack = [maximal_elements[-(i+1)] for i in range(len(maximal_elements))]
        
    # Rest of the graph
    ready = []
    while(len(stack) > 0):
        current = stack[-1]
        if(current in ready):
            __dprint("Visiting node %s" %current, debug)
            if(not (current in maximal_elements)):
                # Visit the node: pull-up the vector
                edge = graph.incoming_edges(current)[0]
                cu_vector = vectors[current]
                
                ## Constant case; reducing to the constant term
                if(edge[0] == -1):
                    __dprint("** Reducing node %d to constant" %(current), debug)
                    __dprint("\t- Current vector: %s" %(cu_vector), debug)
                    __dprint("\t- Prev. constant: %s" %const_val, debug)
                    const_val += sum(cu_vector[i]*cR(coeffs[current].derivative(times=i)) for i in range(len(cu_vector)))
                    __dprint("\t- New constant: %s" %const_val, debug)
                
                ## General case
                else:                
                    de_vector = vectors[edge[0]]
                    relation = edge[2]
                    C = trans[edge[0]][1]
                    
                    __dprint("** Reducing node %d to %d" %(current, edge[0]), debug)
                    __dprint("\t- Current vector: %s" %(cu_vector), debug)
                    __dprint("\t- Destiny vector: %s" %(de_vector), debug)
                    __dprint("\t- Relation: %s" %(str(relation)), debug)
                    __dprint("\t- Matrix:\n\t\t%s" %(str(C).replace('\n','\n\t\t')), debug)
                    __dprint("\t- Prev. constant: %s" %const_val, debug)
                                
                    # Building vectors for all the required derivatives
                    ivectors = [vector(cR, [0 for i in range(relation[0])] + [1] + [0 for i in range(relation[0]+1,coeff_order[edge[0]])])]
                    extra_cons = [relation[1][1]]
                    
                    for i in range(len(cu_vector)):
                        extra_cons += [ivectors[-1][-1]*trans[edge[0]][0]]
                        ivectors += [vector_derivative(C, ivectors[-1], infinite_derivative)]
                    
                    vectors[edge[0]] = sum([vector(cR,[cu_vector[i]*ivectors[i][j] for j in range(len(ivectors[i]))]) for i in range(len(cu_vector))], de_vector)
                    const_val += sum([cu_vector[i]*extra_cons[i] for i in range(len(cu_vector))])
                    
                    __dprint("\t- New vector: %s" %vectors[edge[0]], debug)
                    __dprint("\t- New constant: %s" %const_val, debug)
                    __dprint("*************************", debug)
                
            # Getting out the element of the stack
            stack.pop()
        else:
            # Add the children and visit them
            ready += [current]
            for e in graph.outgoing_edges(current):
                stack.append(e[1])
        
    final_vector = []
    for i in maximal_elements:
        if(i == -1):
            final_vector += [const_val]
        else:
            final_vector += [el for el in vectors[i]]
            
    final_vector = vector(cR, final_vector)
    __dprint("Vector: %s" %final_vector, debug)
    
    return vector(final_vector)
    
    
################################################################################
################################################################################
################################################################################

def toDifferentiallyAlgebraic_Below(poly, infinite=False, debug=False):
    '''
    Method that receives a polynomial with variables y_0,...,y_m with coefficients in some ring DD(R) and reduce it to a polynomial
    with coefficients in R.
    
    The optional input 'debug' allow the user to print extra information as the matrix that the determinant is computed.
    '''
    ## Processing the input infinite
    if(infinite):
        r_method = fromFinitePolynomial_toInfinitePolynomial
    else:
        r_method = fromInfinityPolynomial_toFinitePolynomial
    
    ### Preprocessing the input
    parent = poly.parent()
    if(not is_InfinitePolynomialRing(parent)):
        if(not is_MPolynomialRing(parent)):
            if(not is_PolynomialRing(parent)):
                raise TypeError("The input is not a valid polynomial. Obtained something in %s" %parent)
            if(not str(parent.gens()[0]).startswith("y_")):
                raise TypeError("The input is not a valid polynomial. Obtained %s but wanted something with variables y_*" %poly)
            parent = InfinitePolynomialRing(parent.base(), "y")
        else:
            gens = list(parent.gens())
            to_delete = []
            for gen in gens:
                if(str(gen).startswith("y_")):
                    to_delete += [gen]
            if(len(to_delete) == 0):
                raise TypeError("The input is not a valid polynomial. Obtained %s but wanted something with variables y_*" %poly)
            for gen in to_delete:
                gens.remove(gen)
            parent = InfinitePolynomialRing(PolynomialRing(parent.base(), gens), "y")
    else:
        if(parent.ngens() > 1 or repr(parent.gen()) != "y_*"):
            raise TypeError("The input is not a valid polynomial. Obtained %s but wanted something with variables y_*" %poly)
    
    poly = parent(poly)
    
    ### Now poly is in a InfinitePolynomialRing with one generator "y_*" and some base ring.
    if(not isinstance(parent.base(), DDRing)):
        print("The base ring is not a DDRing. Returning the original polynomial (reached the bottom)")
        return r_method(poly)
    
    up_ddring = parent.base()
    dw_ddring = up_ddring.base()
    goal_ring = InfinitePolynomialRing(dw_ddring, "y")
    
    coefficients = poly.coefficients()
    monomials = poly.monomials()
    
    ## Arraging the coefficients and organize the vector-space notation
    dict_to_derivatives = {}
    dict_to_vectors = {}
    S = 0
    for i in range(len(coefficients)):
        coeff = coefficients[i]; monomial = goal_ring(str(monomials[i]))
        if(coeff in dw_ddring):
            if(1 not in dict_to_vectors):
                S += 1
                dict_to_vectors[1] = goal_ring.zero()
            dict_to_vectors[1] += dw_ddring(coeff)*monomial
        else:
            used = False
            for el in dict_to_derivatives:
                try:
                    index = dict_to_derivatives[el].index(coeff)
                    dict_to_vectors[el][index] += monomial
                    used = True
                    break
                except ValueError:
                    pass
            if(not used):
                list_of_derivatives = [coeff]
                for _ in range(coeff.getOrder()-1):
                    list_of_derivatives += [list_of_derivatives[-1].derivative()]
                dict_to_derivatives[coeff] = list_of_derivatives
                dict_to_vectors[coeff] = [monomial] + [0 for j in range(coeff.getOrder()-1)]
                S += coeff.getOrder()
    
    rows = []
    for el in dict_to_vectors:
        if(el == 1):
            row = [dict_to_vectors[el]]
            for i in range(S-1):
                row += [infinite_derivative(row[-1])]
            rows += [row]
        else:
            C = el.equation.companion()
            C = Matrix(goal_ring.base(),[[goal_ring.base()(row_el) for row_el in row] for row in C])
            rows += [row for row in matrix_of_dMovement(C, vector(goal_ring, dict_to_vectors[el]), infinite_derivative, S)]
        
    M = Matrix(rows)
    if(debug): print(str(M))
    return r_method(M.determinant().numerator())

def diff_to_diffalg(func, varname="y", constant=True, infinite=True, debug=False):
    '''
        Method that compute an differentially algebraic equation for the object ``func``.

        All *differentially definable* functions are also *differentially algebraic*. This
        method do the transformation from a linear differential equation with *difficult*
        coefficients into a non-linear equation with *simple* coefficients.

        TODO:
            * Improve this introdcution.
            * Link references to theory.

        INPUT: 
            * ``func``: rational function or :class:`~ajpastor.dd_functions.ddFunction.ddFunction`.
            * ``varname``: name of the variable of the output polynomial. This must be a string
              different from the name of the variable of ``func``.
            * ``constant``: whether to eliminate all non-constant coefficients or just
              the :class:`~ajpastor.dd_functions.ddFunction.ddRing`.
            * ``infinite``: whether the output would be in a InfinitePolynomialRing or not.
            * ``debug``: if set to True, the method print several useful information 
              during the execution of the algorithm.

        OUTPUT:
            
            A polynomial with variable names of the shape ``varname_*``, where ``varname`` is 
            the input ``varname`` and ``*`` is an integer representing the derivative of 
            the function ``func``.

        EXAMPLES::

            sage: from ajpastor.dd_functions import *
            sage: diff_to_diffalg(Exp(Exp(x)-1))
            -y_2*y_0 + y_1^2 + y_1*y_0
            sage: diff_to_diffalg(AiryD(('a','b')))
            y_3*y_0 - y_2*y_1 - y_0^2
            sage: diff_to_diffalg(AiryD(('a','b')), constant=False)
            y_2 + (-x)*y_0
            sage: R.<a,b> = QQ[]
            sage: diff_to_diffalg(a^2+3*b*a)
            (-2)*y_2 + 4
            sage: diff_to_diffalg(b*a^2 + 2)
            sage: diff_to_diffalg(AiryD(('a',1)), varname="a")
            Traceback (most recent call last):
            ...
            ValueError: The variable name 'a' is not valid for ...
            sage: diff_to_diffalg(Exp(Exp(x)-1), varname="x")
            Traceback (most recent call last):
            ...
            ValueError: The variable name 'x' is not valid for ...
            sage: diff_to_diffalg(SR(x))
            Traceback (most recent call last):
            ...
            TypeError: The type of the argument (x) is not valid. Required DDFunction or polynomial
    '''
    try:
        parent = func.parent()
    except AttributeError: # weird input -- we try to embed into QQ
        R = InfinitePolynomialRing(QQ,varname); y = R.gens()[0]
        result = y[0] - QQ(func)
        if(not infinite): 
            result = result.polynomial()
        return result

    ## Looking fot the field of constants
    if(is_DDRing(parent)):
        var = parent.variables(True)[0]
        F = parent.coeff_field
    elif(is_PolynomialRing(parent) or is_MPolynomialRing(parent)):
        ## In the case parent is a ring of polynomials, all variables except the first 
        ## are considered as parameters.
        var = parent.gens()[0]
        F = parent.remove_var(var)
        if(not F.is_field()):
            F = F.fraction_field()
    else:
        raise TypeError("The type of the argument (%s) is not valid. Required DDFunction or polynomial." %func)

    R = InfinitePolynomialRing(F, varname)
    Fv = PolynomialRing(F, var)
    S = InfinitePolynomialRing(Fv, varname); y = S.gens()[0]
    
    ## Checking the name of the variable
    if(varname in [str(var)] + [str(el) for el in F.gens()]):
        raise ValueError("The variable name '%s' is not valid for the function %s. The name is already taken." %(varname, func))

    if(is_DDRing(parent)):
        T = InfinitePolynomialRing(parent.base(), varname); y_aux = T.gens()[0]
        p = sum([y_aux[i]*func[i] for i in range(func.getOrder()+1)], T.zero())
        for i in range(parent.depth()-1):
            p = toDifferentiallyAlgebraic_Below(p, infinite=True, debug=debug)

        p = S(str(p))
    else:
        p = Fv(str(func.denominator()))*y[0] - Fv(str(func.numerator()))

    ## At this point we have guaranteed that p is a polynomial 
    ## with coefficients in F[var]. In case this var shows up
    ## we need to remove it.
    if(constant and any(el.degree() > 0 for el in p.coefficients())): # we need simplification
        coeffs = p.coefficients(); mons = [R(m) for m in p.monomials()]
        n = max(el.degree() for el in coeffs)
        v0 = vector(R, [sum(mons[i]*coeffs[i][j] for i in range(len(mons))) for j in range(n+1)])
        C = Matrix([[kronecker_delta(i+1, j)*(j) for j in range(n+1)] for i in range(n+1)])
        M = matrix_of_dMovement(C, v0, lambda p : infinite_derivative(p,1,lambda q : 0), n+1)
        p = M.determinant()
        p = R(str(p))

    try:
        R = p.parent(); F = R.base()
        p = R(prod(fac[0]**fac[1] for fac in p.factor() if not fac[0] in F))
    except Exception:
        pass

    if(not infinite):
        p = p.polynomial()

    return p
    
################################################################################
###
### Methods for computing Diff. Algebraic equation for inverses
### 
###     - Multiplicative inverse from DA equation
###     - Functional inverse from Dn-finite equation
###
################################################################################
def inverse_DA(poly, vars=None, infinite=False):
    '''
        Method that computes the DA equation for the multiplicative inverse 
        of the solutions of a DA equation.
        
        We assume that the variables given by vars are the variables representing
        the solution, namely vars[i+1] = vars[i].derivative().
        If vars is not provided, we take all the variables from the polynomial
        that is given.
    '''
    ## Processing the input infinite
    if(infinite):
        r_method = fromFinitePolynomial_toInfinitePolynomial
    else:
        r_method = fromInfinityPolynomial_toFinitePolynomial
        
    ## Checking that poly is a polynomial
    
    parent = poly.parent()
    if(is_FractionField(parent)):
        parent = parent.base()
    if(is_InfinitePolynomialRing(parent)):
        poly = fromInfinityPolynomial_toFinitePolynomial(poly)
        return inverse_DA(poly, vars, infinite=infinite)
    if(not (is_PolynomialRing(parent) or is_MPolynomialRing(parent))):
        raise TypeError("No polynomial is given")
    poly = parent(poly)
    
    ## Getting the list of variables
    if(vars is None):
        g = list(poly.parent().gens()); g.reverse()
    else:
        if(any(v not in poly.parent().gens() for v in vars)):
            raise TypeError("The variables given are not in the polynomial ring")
        g = vars
        
    ## Computing the derivative of the inverse using Faa di Bruno's formula
    derivatives = [1/g[0]] + [sum((falling_factorial(-1, k)/g[0]**(k+1))*bell_polynomial(n,k)(*g[1:n-k+2]) for k in range(1,n+1)) for n in range(1,len(g
))]
    
    ## Computing the final equation
    return r_method(poly(**{str(g[i]): derivatives[i] for i in range(len(g))}).numerator())

def func_inverse_DA(func, infinite=False, debug=False):
    '''
        TODO: Add documentation
    '''
    ## Processing the input infinite
    if(infinite):
        r_method = fromFinitePolynomial_toInfinitePolynomial
    else:
        r_method = fromInfinityPolynomial_toFinitePolynomial
        
    ## Computations
    equation = fromFinitePolynomial_toInfinitePolynomial(diff_to_diffalg(func, debug=debug))
    
    if(debug): print(str(equation))
    
    parent = equation.parent()
    y = parent.gens()[0]
    
    n = len(equation.variables())
        
    quot = [FaaDiBruno_polynomials(i, parent)[0]/FaaDiBruno_polynomials(i,parent)[1] for i in range(n)]
    coeffs = [el(**{str(parent.base().gens()[0]) : y[0]}) for el in equation.coefficients()]
    monomials = [el(**{str(y[j]) : quot[j] for j in range(n)}) for el in equation.monomials()]
    
    if(debug):
        print(str(monomials))
        print(str(coeffs))
    
    sol = sum(monomials[i]*coeffs[i] for i in range(len(monomials)))
    
    if(debug): print(str(sol))
    if(hasattr(sol, "numerator")):
        return parent(sol.numerator())
    return r_method(parent(sol))


################################################################################
###
### Methods for compute Dn-finite equations from DA-equations
###
################################################################################
def guess_Dnfinite(poly, init):
    ## TODO: Method not public
    res = guess_homogeneous_DNfinite(poly, init)
    if(is_DDFunction(res)):
        return res
    return guess_DA_DDfinite(poly, init)

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
            - all: compute all the possibles equations
    '''
    poly = fromInfinityPolynomial_toFinitePolynomial(poly)
    
    if(not poly.is_homogeneous()):
        raise TypeError("We require a homogeneous polynomial")
    
    if(bS is None):
        S = poly.degree()
    else:
        S = bS
    if(bd is None):
        d = S - poly.parent().ngens() + 2
    else:
        d = bd
    
    compositions = (el for el in Compositions().subset(S) if len(el) == d+1)
    coeffs = [["a_%d_%d" %(i,j) for j in range(S)] for i in range(d+1)]
    cInit = [["i_%d_%d" %(i,j) for j in range(S-1)] for i in range(d+1)]
    R = ParametrizedDDRing(DFinite, sum(coeffs, [])+sum(cInit,[]))
    R2 = R.to_depth(2)
    coeffs = [[R.parameter(coeffs[i][j]) for j in range(S)] for i in range(d+1)]
    cInit = [[R.parameter(cInit[i][j]) for j in range(S-1)] for i in range(d+1)]
    sols = []
    
    for c in compositions:
        ## Building the parametrized guess
        e = [R.element([coeffs[i][j] for j in range(c[i])] + [1],cInit[i]) for i in range(d+1)]
        f = R2.element(e)
        if(len(init) > 0):
            try:
                f = f.change_init_values([init[i] for i in range(min(len(init), f.equation.jp_value()+1))])
            except ValueError:
                continue
        
        ## Computing the DA equation
        poly2 = diff_to_diffalg(f)
        
        ###############################################
        ### Comparing the algebraic equations
        ## Getting a possible constant difference
        m2 = poly2.monomials()
        eqs = []
        C = None
        for mon in m2:
            c2 = poly2.coefficient(mon)
            if(poly2.parent().base()(c2).is_constant()):
                C = poly.coefficient(poly.parent()(mon))/c2
                break
        if(C is None):
            C = 1
        elif(C == 0):
            continue
        
        ### Building all equations from the algebraic equation
        for mon in m2:
            c2 = poly2.coefficient(mon); c = poly.coefficient(poly.parent()(mon))
            eqs += [C*c2 - c]
        
        ##################################################
        ### Comparing the initial values
        for i in range(min(len(init), f.equation.jp_value()+1),len(init)):
            try:
                eqs += [f.getInitialValue(i) - init[i]]
            except TypeError:
                break ## Case when no initial value can be computed
            
        ##################################################
        ### Solving the system (groebner basis)
        P = R.coeff_field.base()
        fEqs = []
        for el in eqs:
            if(el.parent().is_field()):
                fEqs += [P(str(el.numerator()))]
            else:
                fEqs += [P(str(el))]
                
        gb = ideal(fEqs).groebner_basis()
        if(1 not in gb):
            sols += [(f,gb)]
            if(not all):
                break
        
        
    if(len(sols) > 0 and not all):
        return sols[0]
    
    return sols

def guess_homogeneous_DNfinite(poly, init):
    '''
        Method that tries to compute a Dn-finite differential equation
        for a DA-function defined from an homogeneous equation.
        
        This method simplifies the equation supposing that the solution
        is of the form y(x) = exp(int(u(x))), getting a differential equation
        for u(x) of less order.
        
        If we end up with a linear equation, then we can return a Dn-finite function
        where n depends on how many iterations we needed.
        
        If the final algebraic equation is not linear, then we return this
        last equation together with the number of iterations done.
        
        INPUT:
            - poly: polynomial with the differential equation we want to mimic with DD-finite elements
            - init: initial values of the solution of poly (must be enough).
    '''
    new_poly, depth = simplify_homogeneous(poly)
    parent = new_poly.parent(); base = parent.base(); y = parent.gens()[0]
    
    order = max(get_InfinitePolynomialRingGen(parent, v, True)[1] for v in new_poly.variables())
    
    if(new_poly.degree() == 1 and new_poly.is_homogeneous()): ## We can build something
        coeffs = []
        for i in range(order+1):
            if(y[i] in new_poly.variables()):
                coeffs += new_poly.coefficients()[new_poly.monomials().index(y[i])]
            else:
                coeffs += [0]
        
        inhom = new_poly.constant_coefficient()
        if(is_DDRing(base)):
            base_field = base.coeff_field
            base = base.to_depth(base.depth()+1)
        else:
            base_field = base.fraction_field()
            base = DDRing(PolynomialRing(base_field, 'x'))
        
        ## We can build a D(depth+1)-finite function
        deep_init = build_initial_from_homogeneous(tuple(init), order, depth, base_field)
                
        res = base.element(coeffs, deep_init, inhomogeneous=inhom)
        for i in range(depth):
            res = Exp(res.integrate(0))
        return res
    
    else:
        return (new_poly, depth)
    

@cached_function
def build_initial_from_homogeneous(init, n, depth, base):
    ## Checking we have enough data
    if(len(init) < n+depth):
        raise TypeError("Not enough initial data was provided (required %d)" %(n+depth))
    elif(len(init) > n+depth):
        return build_initial_from_homogeneous(tuple(list(init)[:n+depth]), n, depth, base)
    
    ## Base case with depth = 0
    if(depth == 0):
        return init[:n]
    
    ## Casting the input to the desired ring
    init = [base(el) for el in init]
    
    ## Checking the initial condition init[0]
    if(init[0] == 0):
        raise ValueError("Initial condition is zero. Impossible to compute a solution of the form e(int(u(x)))")
    
    ## Computing the initial conditions for depth "depth-1"
    new_init = [init[1]/init[0]]
    
    parent = Exponential_polynomials(1,base).parent(); y = parent.gens()[0]
    
    for i in range(1,n+depth-1):
        poly = fromInfinityPolynomial_toFinitePolynomial(-(Exponential_polynomials(i+1, parent) - y[i]))
        new_init += [base(poly(**{str(y[j]) : new_init[j] for j in range(i)})) + init[i+1]/init[0]]
        
    ## Returning the recursive call with one less depth
    return build_initial_from_homogeneous(tuple(new_init), n, depth-1, base)

@cached_function
def simplify_homogeneous(poly, _stop_linear=True):
    '''
        Given an homogeneous differential polynomial 'poly', we reduce the order of the equation by 1
        using the change of variables y(x) = exp(int(u(x))).
        
        This leads to a differentially algebraic equation of order 1 less than 'poly'. If we obtain a 
        new homogeneous equation, we can iterate. The return of this function is this final result together
        with the number of steps performed.
    '''
    poly = fromFinitePolynomial_toInfinitePolynomial(poly)
    parent = poly.parent(); y = parent.gens()[0]
    
    if(not(poly.is_homogeneous()) or (_stop_linear and poly.degree() == 1)):
        return (poly,0)
    
    d = {str(y[0]) : parent.one()}
    for v in poly.variables():
        if(v != y[0]):
            d[str(v)] = Exponential_polynomials(get_InfinitePolynomialRingGen(parent, v, True)[1], parent)
                
    new_poly = poly(**d)
    result,n = simplify_homogeneous(new_poly)
    
    return (result, n+1)
    
###################################################################################################
### Polynomial functions
###################################################################################################
@cached_function
def FaaDiBruno_polynomials(n, parent):
    r'''
        TODO:
            * Add documentation
    '''
    if(n < 0):
        raise ValueError("No Faa Di Bruno polynomial can be computed for negative index")
    elif(not(is_InfinitePolynomialRing(parent))):
        if((not(is_PolynomialRing(parent))) and (not(is_MPolynomialRing(parent)))):
            raise TypeError("The parent ring is not valid: needed polynomial rings or InfinitePolynomialRing")
        return FaaDiBruno_polynomials(n, InfinitePolynomialRing(parent, "y"))
    
    if(parent.base().ngens() == 0 or parent.base().gens()[0] == 1):
        raise TypeError("Needed a inner variable in the coefficient ring")
        
        
    # x = parent.base().gens()[0]
    y = parent.gens()[0]
    if(n == 0):
        return (parent(parent.base().gens()[0]), parent.one())
    if(n == 1):
        return (parent.one(), y[1])
    else:
        prev = [FaaDiBruno_polynomials(k, parent) for k in range(n)]
        ele = -sum(prev[k][0]*bell_polynomial(n,k)(**{"x%d" %i : y[i+1] for i in range(n-k+1)})/prev[k][1] for k in range(1,n))/(y[1]**n)
        return (ele.numerator(), ele.denominator())

@cached_function
def Exponential_polynomials(n, parent):
    r'''
        Method to compute the `n`-th exponential polynomial.

        Assume that `f(x)` is a function that can be written in terms of the
        exponential function in the following way:

        .. MATH::

            f(x) = e^{\int_x u(t)dt}.

        Then we have that for any `n \in \mathbb{N}`, the `n`-th derivative of 
        `f(x)` can be written as

        .. MATH::

            f^{(n)}(x) = f(x) p_n(u),

        where `p_n \in \mathbb{Q}\{u\}`, i.e., `p_n` is a differential polynomial.
        This `p_n` is called the `n`-th exponential polynomial. This can be computed
        with a recursive formula:

        .. MATH::

            f^{(n)}(x) = (f^{(n-1)}(x))' = f(x)(p_1(u)p_{n-1}(u) + (p_n(u))')

        INPUT:
            * ``n``: positive integer
            * ``parent``: the resulting polynomial will be included into this parent structure. 

        OUTPUT:

            The `n`-th exponential polynomial in the corresponding ``parent`` structure.

        EXAMPLES::

            sage: from ajpastor.dd_functions include *
            sage: Exponential_polynomials(1,QQ)
            y_0
            sage: Exponential_polynomial(2, QQ)
            y_1 + y_0^2
            sage: parent(Exponential_polynomial(3, QQ))
            Infinite polynomial ring in y over Rational Field
            sage: parent(Exponential_polynomial(2, QQ[x]))
            Infinite polynomial ring in y over Univariate Polynomial Ring in x over Rational Field
            sage: Exponential_polynomial(0, QQ)
            1
            sage: Exponential_polynomial(-2,QQ)
            Traceback (most recent call last):
            ...
            ValueError: No Exponential polynomial can be computed for non-positive index
    '''
    if(n < 0):
        raise ValueError("No Exponential polynomial can be computed for non-positive index")
    elif(not(is_InfinitePolynomialRing(parent))):
        return Exponential_polynomials(n, InfinitePolynomialRing(parent, "y"))
    
    y = parent.gens()[0]
    
    if(n == 0):
        return parent.one()
    else:
        prev = Exponential_polynomials(n-1,parent)
        return infinite_derivative(prev, derivation=lambda p : 0) + y[0]*prev
    
@cached_function
def Logarithmic_polynomials(n, parent):
    r'''
        TODO:
            * Add this documentation
    '''
    if(n < 0):
        raise ValueError("No Logarithmic polynomial can be computed for non-positive index")
    elif(not(is_InfinitePolynomialRing(parent))):
        return Logarithmic_polynomials(n, InfinitePolynomialRing(parent, "y"))
    
    y = parent.gens()[0]
    
    if(n == 0):
        return y[1]/y[0]
    else:
        return infinite_derivative(Logarithmic_polynomials(n-1, parent), derivation = lambda p : 0)
    
def change_variable(poly, new_var):
    parent = poly.parent()
    if(not (new_var in parent.fraction_field())):
        raise TypeError("The new value must be in the same InfinitePolynomialRing")
    elif(not is_InfinitePolynomialRing(parent)):
        raise TypeError("The parent must be an InfinitePolynomialRing")
    
    gens = poly.polynomial().parent().gens()
        
    index = [get_InfinitePolynomialRingGen(parent, v, True)[1] for v in gens]; m = max(index)
    derivatives = [new_var]
    for i in range(m):
        derivatives += [infinite_derivative(derivatives[-1])]
    to_plug = [derivatives[i] for i in index]
    
    return parent.fraction_field()(poly.polynomial()(**{str(gens[i]) : to_plug[i] for i in range(len(gens))}))
    
def is_Riccati(poly):
    '''
        Method that checks if a non-linear differential equation is of Riccati type 
        and returns the change of coordinates and the linear differential equation in case
        we can.
    '''
    poly = fromFinitePolynomial_toInfinitePolynomial(poly)
    parent = poly.parent(); y = parent.gens()[0]
    var = poly.polynomial().parent().gens(); index = [get_InfinitePolynomialRingGen(parent, v, True)[1] for v in var]
    order = max(index)
    
    ## Checking the degree of y[0] is appropriate in the therm of y[order-1]
    try:
        if(not poly.degrees()[var.index(y[order-1])] == 1):
            raise ValueError("The degree of the function in the equation is not valid")
    except:
        raise TypeError("Error getting the degree of the function in the equation")
    
    C = poly.coefficient(y[order-1]*y[0])
    ## Simple case: no element inside or is not in the base field
    if(C == 0 or (not C in parent.base())):
        return False, poly
    
    ## The coefficient is in the appropriate place
    try:
        if(C.derivative(SR('x')) != 0):
            new_eq = change_variable(poly, y[0]/C)*C
            print("Recursion in Riccati, new equation: %s" %new_eq)
            return is_Riccati(new_eq)
    except:
        # Impossible to compute the derivative -- Assuming zero
        pass
    
    ## Computing the constant
    C = C/(order+1)
    
    to_plug = [Logarithmic_polynomials(i, parent)/C for i in index]
    
    new_poly = poly.polynomial()(**{str(var[i]): to_plug[i] for i in range(len(var))})
    
    if(is_FractionField(new_poly.parent())):
        new_poly = new_poly.numerator()
    if(is_InfinitePolynomialRing(new_poly.parent())):
        new_poly = new_poly.polynomial()
    
    var = new_poly.parent().gens(); min_degree = {v:new_poly.degree() for v in var}
    for m in new_poly.monomials():
        for v in var:
            d = m.degree(v)
            if(d < min_degree[v]):
                min_degree[v] = d
    gcd = prod([v**min_degree[v] for v in var], new_poly.parent().one())
    new_poly = new_poly.parent()(new_poly/gcd)
    
    if(new_poly.degree() == 1):
        return True, new_poly
    
    return False, new_poly
    
###################################################################################################
### Private functions
###################################################################################################
def __dprint(obj, debug):
    if(debug): print(str(obj))
    
####################################################################################################
#### PACKAGE ENVIRONMENT VARIABLES
####################################################################################################
__all__ = ["is_InfinitePolynomialRing", "get_InfinitePolynomialRingGen", "infinite_derivative", "diffalg_reduction", "toDifferentiallyAlgebraic_Below", "diff_to_diffalg", "inverse_DA", "func_inverse_DA", "guess_DA_DDfinite", "guess_homogeneous_DNfinite", "FaaDiBruno_polynomials", "Exponential_polynomials", "Logarithmic_polynomials", "is_Riccati", "change_variable"]

# Extra functions for debugging
def simplify_coefficients(base, coeffs, derivatives, debug=True):
    return __simplify_coefficients(base,coeffs,derivatives,debug)

def simplify_derivatives(derivatives, debug=True):
    return __simplify_derivatives(derivatives, debug)
    
def find_relation(g,df, debug=True):
    return __find_relation(g,df,debug)
    
def find_linear_relation(f,g):
    return __find_linear_relation(f,g)
    
def build_derivation_matrix(gens, coeffs, drelations, debug=True):
    return __build_derivation_matrix(gens, coeffs, drelations, debug)

def build_vector(coeffs, monomials, graph, drelations, cR, debug=True):
    return __build_vector(coeffs, monomials, graph, drelations, cR, debug)

__all__ += ["simplify_coefficients", "simplify_derivatives", "find_relation", "find_linear_relation", "build_derivation_matrix", "build_vector"]
