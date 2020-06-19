r"""
Python file for matrix operations and utilities

This module offers several methods to build matrices and operate with them in a very general fashion.
It also provides several method for differential linear algebra.

EXAMPLES::
    sage: from ajpastor.misc.matrix import *

TODO::
    * Complete the Examples section of this documentation
    * Document the package
    * Review the functionality of the package

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

# from sage.all import *   # import sage library
#Python imports
import sys
from functools import reduce

# Sage imports
from sage.all import (Matrix, MatrixSpace, vector, kronecker_delta, ZZ, floor, random, identity_matrix, randint)

####################################################################################
###
### MATRICES BUILDERS
###
### In this section we include some special constructor for matrices in order to 
###     be able to build matrices with more flexibility than before.
### The main functions here will be the diagonal_matrix and the block_matrix.
###
####################################################################################
def block_matrix(parent, rows, constant_or_identity = True):
    '''
        Method that build a matrix using as blocks the elements of rows. The first step is check that dimensions matches for each row and column assuming that non-matrices elements can be extended to a matrix.
        The way to extend that simple elements is marked by argument `constant_or_identity`: if it is False, then we put a constant matrix fullfilled with such element. Otherwise, we build a diagonal matrix with that element in the diagonal (i.e. it is the identity matrix times the element).
    '''
    ## we check that rows is a list of lists of the same size
    d = len(rows[0 ])
    for i in range(1 , len(rows)):
        if(d != len(rows[i])):
            raise ValueError("Te rows provided can not be seen as a matrix")
    
    ## We check the sizes
    rows_hights = [__check_row(row, parent) for row in rows]
    cols_widths = [__check_col([rows[i][j] for i in range(len(rows))], parent) for j in range(len(rows[0 ]))]
    
    rows_with_matrix = []
    for i in range(len(rows)):
        row_with_matrix = []
        for j in range(len(rows[0 ])):
            if(rows[i][j] in parent):
                if(constant_or_identity):
                    row_with_matrix += [Matrix(parent, [[rows[i][j]*kronecker_delta(k,l) for l in range(cols_widths[j])] for k in range(rows_hights[i])])]
                else:
                    row_with_matrix += [Matrix(parent, [[rows[i][j] for l in range(cols_widths[j])] for k in range(rows_hights[i])])]
            else:
                row_with_matrix += [Matrix(parent, rows[i][j])]
        rows_with_matrix += [row_with_matrix]
    final_rows = []
    for i in range(len(rows_with_matrix)):
        for j in range(rows_hights[i]):
            final_rows += [reduce(lambda p,q : p+q, [list(el[j]) for el in rows_with_matrix[i]])]
    return Matrix(parent, final_rows)
    
def diagonal_matrix(parent, *args, **kwds):
    '''
        Method that build a diagonal matrix in parent using the elements of args.
        
            - If args has more than 1 element, we take consider the list as input
            - If args has one element and it it a list, we build a diagonal matrix using such elements
            - If args has one element and it is not a list, we build a diagonal matrix using such element repeated `size` times.
    '''
    if(len(args) > 1 ):
        return diagonal_matrix(parent, args)
    
    if(len(args) == 1  and (not (type(args[0 ]) == list))):
        return diagonal_matrix(parent, [args[0 ] for i in range(kwds.get("size", 1 ))])
        
    list_of_elements = args[0 ]
    d = len(list_of_elements)
    rows = []
    for i in range(d):
        rows += [[0  for j in range(i)] + [list_of_elements[i]] + [0  for j in range(i+1 ,d)]]
        
    return block_matrix(parent, rows)
    
def vandermonde_matrix(parent, *args, **kwds):
    if(len(args) > 1 ):
        return vandermonde_matrix(parent, args, **kwds)
    else:
        casted = [parent(el) for el in args[0 ]]
        
    try:
        ncols = kwds["size"]
    except KeyError:
        try:
            ncols = kwds["ncols"]
        except KeyError:
            ncols = len(casted)
        
    rows = [[pow(casted[i], j) for j in range(ncols)] for i in range(len(casted))]
    return Matrix(parent, rows)
    
def random_matrix(parent, *args, **kwds):
    if(len(args) > 1 ):
        return random_matrix(parent, args, **kwds)
    else:
        casted = [int(el) for el in args[0 ]]
        
    try:
        ncols = kwds["size"]
        nrows = ncols
    except KeyError:
        try:
            ncols = kwds["ncols"]
            nrows = kwds["nrows"]
        except KeyError:
            if(len(casted) > 1 ):
                nrows = casted[0 ]
                ncols = casted[1 ]
            else:
                nrows = casted[0 ]
                ncols = casted[1 ]
            
    try:    
        min = kwds["min"]
    except KeyError:
        min = -sys.maxsize 
    try:
        max = kwds["max"]
    except KeyError:
        max = sys.maxsize
    
    if(min > max):
        raise ValueError("Can not create random numbers between %d and %d.\n\tReason: the minimal value is higher than the maximal value" %(min,max))
    
    return Matrix(parent, [[randint(min, max) for i in range(ncols)] for j in range(nrows)])
    
    
### Auxiliary (and private) methods
def __check_input(X, parent):
    if(isinstance(X.parent(), MatrixSpace) and parent.has_coerce_map_from(X.parent().base())):
        return True
    elif(isinstance(X, list)):
        try:
            is_matrix = True
            d = len(X[0 ])
            i = 1 
            while(is_matrix and i < len(X)):
                is_matrix = (is_matrix and d == len(X[i]))
                i += 1 
                
            if(is_matrix):
                return True
        except AttributeError:
            pass
    
    return False

def __cast_input(X, parent):
    if(__check_input(X,parent)):
        return Matrix(parent, X)
    
    raise TypeError("The input %s can not be seen as a matrix of %s" %(X,parent))

def __check_row(row,parent):
    hight = None
    for el in row:
        if(__check_input(el, parent)):
            if(hight is None):
                hight = __nrows(el)
            else:
                if(not (hight == __nrows(el))):
                    raise ValueError("The row has not the proper format -- different size")
        elif(not (el in parent)):
            raise ValueError("The row has not the proper format -- non-castable element")
    if(hight is None):
        return 1
    return hight

def __check_col(col,parent):
    width = None
    for el in col:
        if(__check_input(el, parent)):
            if(width is None):
                width = __ncols(el)
            else:
                if(not (width == __ncols(el))):
                    raise ValueError("The col has not the proper format -- different size")
        elif(not (el in parent)):
            raise ValueError("The col has not the proper format -- non-castable element")
                               
    if(width is None):
        return 1
    return width

def __ncols(X):
    try:
        try:
            return X.ncols()
        except AttributeError:
            return len(X[0 ])
    except Exception:
        raise TypeError("Impossible to compute the number of columns for element %s" %X)
        
def __nrows(X):
    try:
        try:
            return X.ncols()
        except AttributeError:
            return len(X)
    except Exception:
        raise TypeError("Impossible to compute the number of rows for element %s" %X)
        
def __rand(min, max):
    return ZZ(floor((random()*(max-min))+min))

####################################################################################
###
### MATRICES OPERATIONS
###
### In this section we include some functionality about matrices as the row/column
###     operations and the scalar product of some row/column.
### These operations are essentially those that are used to perform a Gauss-Jordan
###     algorithm over a Matrix. Such algorithm may be implemented in further 
###     versions of this file.
### We also include a simplify method that tries to simplify a matrix and, if some 
###     element can not be simplified, then returns the original matrix.
###
####################################################################################
def op_rows(M, s_r, d_r, el):
    try:
        ## We make a copy of the matrix
        new_rows = []
        for i in range(M.nrows()):
            new_rows += [[M[i][j] for j in range(M.ncols())]]
            
        ## We make the current operations
        for i in range(M.ncols()):
            new_rows[d_r][i] = M[d_r][i]-el*M[s_r][i]
            
        return Matrix(M.parent().base(), new_rows)
    except AttributeError:
        raise TypeError("First argument must be a matrix. Given %s" %M)
        
def op_cols(M, s_c, d_c, el):
    try:
        ## We make a copy of the matrix
        new_rows = []
        for i in range(M.nrows()):
            new_rows += [[M[i][j] for j in range(M.ncols())]]
            
        ## We make the current operations
        for i in range(M.nrows()):
            new_rows[i][d_c] = M[i][d_c]-el*M[i][s_c]
            
        return Matrix(M.parent().base(), new_rows)
    except AttributeError:
        raise TypeError("First argument must be a matrix. Given %s" %M)
        
def scal_row(M, d_r, el):
    try:
        ## We make a copy of the matrix
        new_rows = []
        for i in range(M.nrows()):
            new_rows += [[M[i][j] for j in range(M.ncols())]]
            
        ## We make the current operations
        for i in range(M.ncols()):
            new_rows[d_r][i] = el*M[d_r][i]
            
        return Matrix(M.parent().base(), new_rows)
    except AttributeError:
        raise TypeError("First argument must be a matrix. Given %s" %M)
        
def scal_col(M, d_c, el):
    try:
        ## We make a copy of the matrix
        new_rows = []
        for i in range(M.nrows()):
            new_rows += [[M[i][j] for j in range(M.ncols())]]
            
        ## We make the current operations
        for i in range(M.nrows()):
            new_rows[i][d_c] = el*M[i][d_c]
            
        return Matrix(M.parent().base(), new_rows)
    except AttributeError:
        raise TypeError("First argument must be a matrix. Given %s" %M)
        
def swap_rows(M, r1,r2):
    try:
        ## We make a copy of the matrix
        new_rows = []
        for i in range(M.nrows()):
            new_rows += [[M[i][j] for j in range(M.ncols())]]
            
        ## We make the current operations
        for i in range(M.ncols()):
            new_rows[r1][i] = M[r2][i]
            new_rows[r2][i] = M[r1][i]
            
        return Matrix(M.parent().base(), new_rows)
    except AttributeError:
        raise TypeError("First argument must be a matrix. Given %s" %M)
        
def swap_cols(M, c1,c2):
    try:
        ## We make a copy of the matrix
        new_rows = []
        for i in range(M.nrows()):
            new_rows += [[M[i][j] for j in range(M.ncols())]]
            
        ## We make the current operation
        for i in range(M.nrows()):
            new_rows[i][c1] = M[i][c2]
            new_rows[i][c2] = M[i][c1]
            
        return Matrix(M.parent().base(), new_rows)
    except AttributeError:
        raise TypeError("First argument must be a matrix. Given %s" %M)
        
def turn_matrix(M, vertical=False):
    if(vertical):
        new_rows = [[M[i][j] for j in range(M.ncols())] for i in range(-1 ,-M.nrows()-1 ,-1 )]
    else:
        new_rows = [[M[i][j] for j in range(-1 ,-M.ncols()-1 ,-1 )] for i in range(M.nrows())]
        
    return Matrix(M.parent().base(), new_rows)
        
def simplify_matrix(M):
    try:
        new_rows = [[M[i][j].simplify() for j in range(M.ncols())] for i in range(M.nrows())]
        return Matrix(M.parent().base(), new_rows)
    except AttributeError:
        pass
    return M
    
####################################################################################
###
### MATRIX OPERATIONS
###
### In this section we include functionality to compute some operations of 
### matrices.
###
####################################################################################
def direct_sum(*matrices):
    return Matrix.block_diagonal(*matrices)

def kronecker_sum(M,N):
    if(not (M.is_square() and N.is_square())):
        raise TypeError("Only square matrices for the Kronecker sum")
    
    n1 = M.nrows(); n2 = N.nrows()
    return M.tensor_product(identity_matrix(n2)) + identity_matrix(n1).tensor_product(N)
    
####################################################################################
###
### MATRICIAL D-MOVE
###
### In this section we include functionality to compute a differential movement 
###     using a matrix.
### A differential movement of v via M is the vector dm(v,M) = Mv + D(v) where D is
###     a derivative over the domain where the coefficients of v lives.
###
####################################################################################
def derivative_vector(v, D):
    parent = v.parent().base()
    
    return vector(parent, [D(a) for a in v])
    
def differential_movement(M, v, D):
    w = M*v+derivative_vector(v,D)
    return w
    
def __dm(M,v,D):
    return differential_movement(M,v,D)
    
def matrix_of_dMovement(M,v,D, cols):
    from sage.categories.pushout import pushout
    parent = pushout(M.parent().base(), v.parent().base())
    res = [v]
    for _ in range(1 ,cols):
        res += [__dm(M,res[-1 ],D)]
    return Matrix(parent, res).transpose()
    

