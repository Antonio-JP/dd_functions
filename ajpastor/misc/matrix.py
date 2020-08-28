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

# Local imports
from .exceptions import SizeMatrixError

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
        Method that build a matrix using as blocks the elements of rows. 
        
        This method allows the user to build a matrix defining its blocks. There are two options for the inputs:
            * A matrix (that will be directly used as a block
            * Elements alone: will build a constant matrix or a diagonal matrix depending on the argument ``constant_or_identity``.
            
        This method checks that the size of the input is correct, i.e., all rows have the same amount of columns and that all 
        matrices within a row provide the same amount of rows.

        INPUT:
            * ``parent``: the desired parent for the final matrix. All elements mast be inside this parent.
            * ``rows``: a list of arguments representing the rows of the matrix. Each row is another list
              where the elements may be matrices (indicating the number of rows for this block) or elements
              in ``parent`` that will create constant or diagonal matrices with such element.
            * ``constant_or_identity``: this argument decides whether the elements create a diagonal
              matrix (``True``) or a constant matrix (``False``).

        OUTPUT:
            A matrix with the corresponding struture. If any of the sizes does not match, a :class:`~ajpastor.misc.exceptions.SizeMatrixError`
            will be raised.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix(QQ,[[1,2],[3,4]]); I = identity_matrix(QQ, 3)
            sage: block_matrix(QQ,[[M,0],[0,I]])
            [1 2 0 0 0]
            [3 4 0 0 0]
            [0 0 1 0 0]
            [0 0 0 1 0]
            [0 0 0 0 1]
            sage: block_matrix(QQ, [[I, 1],[2, M]])
            [1 0 0 1 0]
            [0 1 0 0 1]
            [0 0 1 0 0]
            [2 0 0 1 2]
            [0 2 0 3 4]
            sage: block_matrix(QQ, [[I, 1],[2, M]], False)
            [1 0 0 1 1]
            [0 1 0 1 1]
            [0 0 1 1 1]
            [2 2 2 1 2]
            [2 2 2 3 4]

        This method also works with non-square matrices::

            sage: N = Matrix(QQ, [[1,2,3],[4,5,6]])
            sage: block_matrix(QQ, [[N,1],[0,M]])
            [1 2 3 1 0]
            [4 5 6 0 1]
            [0 0 0 1 2]
            [0 0 0 3 4]
            sage: block_matrix(QQ, [[N,M],[1,2]], False)
            [1 2 3 1 2]
            [4 5 6 3 4]
            [1 1 1 2 2]
        
        However, the sizes of the columns and rows has to fit::

            sage: block_matrix(QQ, [[N, 1], [M, 0]])
            Traceback (most recent call last):
            ...
            SizeMatrixError: The col has not the proper format -- different size

        This method also allows matrices in list format::

            sage: block_matrix(QQ, [[N, [[0, 1],[-1,0]]], [1, M]])
            [ 1  2  3  0  1]
            [ 4  5  6 -1  0]
            [ 1  0  0  1  2]
            [ 0  1  0  3  4]
            sage: block_matrix(QQ, [[N, [[0, 1],[1,0],[1,1]]],[1, M]])
            Traceback (most recent call last):
            ...
            SizeMatrixError: The row has not the proper format -- different size

        And also, if all entries are matrices, we do not need to have in the input all the 
        rows with the same length::

            sage: L = Matrix(QQ, [[5, 4, 3, 2, 1]])
            sage: block_matrix(QQ, [[M, N],[L]])
            [1 2 1 2 3]
            [3 4 4 5 6]
            [5 4 3 2 1]
            sage: block_matrix(QQ, [[N, I[:2]], [L,[[9]]]])
            [1 2 3 1 0 0]
            [4 5 6 0 1 0]
            [5 4 3 2 1 9]
            sage: block_matrix(QQ, [[N, I[:2]], [L]])
            Traceback (most recent call last):
            ...
            SizeMatrixError: The given rows have different column size
    '''
    ## We have two different ways of seeing the input: either all the provided rows are of the same size,
    ## allowing to have input in the parent ring, or the sizes must match perfectly between the rows.

    # Checking the first case: if any element is in parent
    if(any(any((el in parent) for el in row) for row in rows)):
        d = len(rows[0])
        for i in range(1, len(rows)):
            if(d != len(rows[i])):
                raise SizeMatrixError("The rows provided can not be seen as a matrix")
        
        ## We check the sizes
        rows_hights = [__check_row(row, parent) for row in rows]
        cols_widths = [__check_col([rows[i][j] for i in range(len(rows))], parent) for j in range(len(rows[0]))]
        
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
    else: # Second case: all elements are matrices, hence they must fit exactly
        ## We check the sizes
        rows_hights = [__check_row(row, parent) for row in rows]
        cols_widths = [sum(__ncols(el) for el in row) for row in rows]

        if(any(el != cols_widths[0] for el in cols_widths)):
            raise SizeMatrixError("The given rows have different column size")
        
        rows_with_matrix = []
        for i in range(len(rows)):
            row_with_matrix = []
            for j in range(len(rows[i])):
                row_with_matrix += [Matrix(parent, rows[i][j])]
            rows_with_matrix += [row_with_matrix]

    ## At this point the variable "row_with_matrix" has all the entries for the final matrix
    ## No checks are needed
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
        rows += [[0 for j in range(i)] + [list_of_elements[i]] + [0  for j in range(i+1 ,d)]]
        
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
    if(isinstance(X, list)):
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
    elif(isinstance(X.parent(), MatrixSpace) and parent.has_coerce_map_from(X.parent().base())):
        return True
    
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
                    raise SizeMatrixError("The row has not the proper format -- different size")
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
                    raise SizeMatrixError("The col has not the proper format -- different size")
        elif(not (el in parent)):
            raise ValueError("The col has not the proper format -- non-castable element")
                               
    if(width is None):
        return 1
    return width

def __ncols(X):
    try:
        try:
            return X.ncols()
        except AttributeError: # Case of input with lists
            return len(X[0])
    except Exception:
        raise TypeError("Impossible to compute the number of columns for element %s" %X)
        
def __nrows(X):
    try:
        try:
            return X.nrows()
        except AttributeError: # Case of input with lists
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
    

