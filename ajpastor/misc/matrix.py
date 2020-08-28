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

        Finally, this method also allows the user to create a Matrix in a normal fashion (providing each
        of its elements)::
            sage: block_matrix(QQ, [[1,2],[3,4]]) == M
            True
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
    r'''
        Method to build a diagonal matrix using the input given

        This method allows the user to create a diagonal shaped matrix where the elements
        on the diagonal can be not only elements of ``parent`` but also matrices that
        will be used as blocks.
        
        INPUT:
            * ``parent``: the desired ambient space for the final matrix.
            * ``args``: the list of elements that will be used as blocks for the diagonal
              of the final matrix.
            * ``kwds``: optional named parameters. The current valid arguments are the following:
                * ``"size"``: if the input has only one argument, the diagonal matrix with such
                  element ``size`` times will be created. This element has to be valid as 
                  an input.
        
        OUTPUT:
            A diagonal matrix with the corresponding structure.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix(QQ, [[1,2],[3,4]]); I = identity_matrix(QQ, 3); N = [[1,2,3],[4,5,6]]
            sage: diagonal_matrix(QQ, [I,I])
            [1 0 0 0 0 0]
            [0 1 0 0 0 0]
            [0 0 1 0 0 0]
            [0 0 0 1 0 0]
            [0 0 0 0 1 0]
            [0 0 0 0 0 1]
            sage: diagonal_matrix(QQ, M, I)
            [1 2 0 0 0]
            [3 4 0 0 0]
            [0 0 1 0 0]
            [0 0 0 1 0]
            [0 0 0 0 1]
            sage: diagonal_matrix(QQ, M, 9, N)
            [1 2 0 0 0 0]
            [3 4 0 0 0 0]
            [0 0 9 0 0 0]
            [0 0 0 1 2 3]
            [0 0 0 4 5 6]

        The extra argument ``size`` can be used to replicate the matrix in the diagonal a high number
        of times. This allow a simpler syntax when creating big matrices::

            sage: diagonal_matrix(QQ, M, size=2)
            [1 2 0 0]
            [3 4 0 0]
            [0 0 1 2]
            [0 0 3 4]
            sage: diagonal_matrix(QQ, M, M, M, M, M, M, M) == diagonal_matrix(QQ, M, size=7)
            True

        If the user forgets about putting at least one argument for the `\alpha_i`, we raise a ``TypeError``::
            sage: diagonal_matrix(ZZ, size=4)
            Traceback (most recent call last):
            ...
            ValueError: At least one element has to be provided
    '''
    if(len(args) == 0):
        raise ValueError("At least one element has to be provided")
    elif(len(args) > 1):
        return diagonal_matrix(parent, args)
    
    if(len(args) == 1  and __check_input(args[0], parent) or args[0] in parent):
        return diagonal_matrix(parent, [args[0] for i in range(kwds.get("size", 1 ))])
        
    ## We use the method block_matrix to build this diagonal. We need to create the zero
    ## gaps between the elements on the diagonal
    list_of_elements = args[0]
    d = len(list_of_elements)
    rows = []
    for i in range(d):
        rows += [[0 for j in range(i)] + [list_of_elements[i]] + [0  for j in range(i+1 ,d)]]
        
    return block_matrix(parent, rows)
    
def vandermonde_matrix(parent, *args, **kwds):
    r'''
        Method to create a Vandermonde matrix

        This method consider a list of elements from the ``parent`` ring and creates the corresponding Vandermonde Matrix.
        This matrix (see the `Wikipedia webpage <https://en.wikipedia.org/wiki/Vandermonde_matrix>`) is constructed
        by elements `\alpha_1,\ldots,\alpha_m` and a given a size `n` in the following way:
        
        .. MATH::

            V = \begin{pmatrix}
            1 & \alpha_1 & \ldots & \alpha_1^{n-1}\\
            1 & \alpha_2 & \ldots & \alpha_2^{n-1}\\
            \vdots & \vdots & \ddots & \vdots\\
            1 & \alpha_m & \ldots & \alpha_m^{n-1}
            \end{pmatrix}

        or, naming `v_{i,j}` the corresponding entry of the matrix, we have `v_{i,j} = \alpha_i^{j-1}`.

        INPUT:
            * ``parent``: the desired parent for the matrix. All elements will be casted into this parent structure.
            * ``args``: a list of elements in ``parent`` that will take the role of the `\alpha_i` in the definition.
            * ``kwds``: optional arguments to consider. The following values are allowed:
                * ``"size"`` or ``"ncols"``: the value for `n` in the definition. If not given, this value will be
                  the number of elements in the input (i.e., we build a square matrix).

        OUTPUT:
            The corresponding Vandermonde matrix with the desired size.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: vandermonde_matrix(QQ, 1,2,3)
            [1 1 1]
            [1 2 4]
            [1 3 9]
            sage: vandermonde_matrix(ZZ, 5, size=2)
            [1 5]
            sage: vandermonde_matrix(ZZ, [1,2,3], ncols=10)
            [    1     1     1     1     1     1     1     1     1     1]
            [    1     2     4     8    16    32    64   128   256   512]
            [    1     3     9    27    81   243   729  2187  6561 19683]
            sage: vandermonde_matrix(QQ, [1,2,3,4,5,6,7,8,9], size=3)
            [ 1  1  1]
            [ 1  2  4]
            [ 1  3  9]
            [ 1  4 16]
            [ 1  5 25]
            [ 1  6 36]
            [ 1  7 49]
            [ 1  8 64]
            [ 1  9 81]

        If the two possible optional arguments (``"size"`` and ``"ncols"``) are present, the value for
        ``"size"`` has preference::

            sage: vandermonde_matrix(QQ, [2,3], ncols=10, size=3)
            [1 2 4]
            [1 3 9]

        If the user forgets about putting at least one argument for the `\alpha_i`, we raise a ``TypeError``::
            sage: vandermonde_matrix(ZZ, size=4)
            Traceback (most recent call last):
            ...
            ValueError: At least one element has to be provided
            
    '''
    if(len(args) == 0):
        raise ValueError("At least one element has to be provided")
    elif(len(args) > 1 or (not (type(args[0]) in (list, tuple)))):
        return vandermonde_matrix(parent, args, **kwds)
    else:
        casted = [parent(el) for el in args[0]]
        
    ncols = kwds.get("size", kwds.get("ncols", len(casted)))
        
    rows = [[pow(casted[i], j) for j in range(ncols)] for i in range(len(casted))]
    return Matrix(parent, rows)
    
def random_matrix(parent, nrows, ncols = None, *args, **kwds):
    r'''
        Method to create a random matrix in a particular parent structure.

        This method uses the method ``random_element`` from a parent structure repeatively
        to create a full matrix. Since the arguments for creating this random elements may vary
        from different parent structures, the optional arguments ``args`` and ``kwds`` allows
        the user to fix them in each particular example.

        INPUT:
            * ``parent``: parent structure where we create the random matrix.
            * ``nrows``: the number of rows for the desired matrix.
            * ``ncols``: the number of columns for the desired matrix. If not given, we take
              the value of ``nrows`` as such number (i.e., the matrix is square)
            * ``args`` and ``kwds``: optional arguments passed to the method ``random_element``
              of the ``parent``.

        OUPUT:
            A random matrix with entries in ``parent`` and fixed size.
    '''
    nr = int(nrows)
    nc = nr if ncols is None else int(ncols)

    if(nr <= 0 or nc <= 0):
        raise ValueError("The size for a random matrix is not valid: negative size")

    return Matrix(parent, [[parent.random_element(**kwds) for j in range(nc)] for i in range(nr)])    
    
### Auxiliary (and private) methods
def __check_input(X, parent):
    try:
        if(isinstance(X, list)):
       
            is_matrix = True
            d = len(X[0 ])
            i = 1 
            while(is_matrix and i < len(X)):
                is_matrix = (is_matrix and d == len(X[i]))
                i += 1 
                
            if(is_matrix):
                return True
        elif(isinstance(X.parent(), MatrixSpace) and parent.has_coerce_map_from(X.parent().base())):
            return True
    except (AttributeError, TypeError):
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
    r'''
        Method for performing the row substraction in Gauss-Jordan elimination.

        This method takes a matrix `M`, two rows indices and an element from the 
        parent ring of `M` and returns a new matrix where the elements in the 
        second row have been "reduced" by the elements in the first row times
        such element.

        This is one of the basic steps while performing Gauss-Jordan elimination
        on a matrix to compute its determinant/nullspace/solution space/rank etc.

        INPUT:
            * ``M``: the original matrix with entries `m_{i,j}`.
            * ``s_r``: index of the row that will be used in the reduction.
            * ``d_r``: index of the row where the reduction will be performed.
            * ``el``: element in the base ring of ``M`` that will be used in the reduction.

        OUTPUT:
            A new matrix `\tilde{M}` with entries `\tilde{m}_{i,j}` such that:
                * If ``i != d_r``: `\tilde{m}_{i,j} = m_{i,j}`.
                * Else: `\tilde{m}_{d_r,j} = m_{d_r,j} - (el)m_{s_r,j}`.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix(QQ, [[1,2],[3,4]])
            sage: op_rows(M, 0, 1, 2)
            [1 2]
            [1 0]
            sage: op_rows(M, 1, 0, -1)
            [4 6]
            [3 4]
            sage: N = block_matrix(QQ, [[M, 0],[0, 1]])
            sage: op_rows(N, 2, 0, 10)
            [  1   2 -10]
            [  3   4   0]
            [  0   0   1]
            sage: op_rows(N, 1, 2, 1)
            [ 1  2  0]
            [ 3  4  0]
            [-3 -4  1]

        This method raises a ValueError when the indices are not valid::
            
            sage: op_rows(N, -1, 2, 1)
            Traceback (most recent call last):
            ...
            ValueError: The source row index is not valid
            sage: op_rows(N, 1, -2, 1)
            Traceback (most recent call last):
            ...
            ValueError: The destiny row index is not valid

        Also, if the input for the matrix is not such, the method raises a TypeError::

            sage: op_rows([[1,2,0],[3,4,0],[0,0,1]], 1, 2, 1)
            Traceback (most recent call last):
            ...
            TypeError: First argument must be a matrix. ...
    '''
    try:
        if(0 > s_r or s_r >= M.nrows()):
            raise ValueError("The source row index is not valid")
        if(0 > d_r or d_r >= M.nrows()):
            raise ValueError("The destiny row index is not valid")

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
    r'''
        Method for performing the column substraction in Gauss-Jordan elimination.

        This method takes a matrix `M`, two column indices and an element from the 
        parent ring of `M` and returns a new matrix where the elements in the 
        second column have been "reduced" by the elements in the first column times
        such element.

        This is one of the basic steps while performing Gauss-Jordan elimination
        on a matrix to compute its determinant/nullspace/solution space/rank etc.

        INPUT:
            * ``M``: the original matrix with entries `m_{i,j}`.
            * ``s_c``: index of the column that will be used in the reduction.
            * ``d_c``: index of the column where the reduction will be performed.
            * ``el``: element in the base ring of ``M`` that will be used in the reduction.

        OUTPUT:
            A new matrix `\tilde{M}` with entries `\tilde{m}_{i,j}` such that:
                * If ``j != d_c``: `\tilde{m}_{i,j} = m_{i,j}`.
                * Else: `\tilde{m}_{i,d_c} = m_{i,d_c} - (el)m_{i,s_c}`.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix(QQ, [[1,2],[3,4]])
            sage: op_cols(M, 0, 1, 2)
            [ 1  0]
            [ 3 -2]
            sage: op_cols(M, 1, 0, -1)
            [3 2]
            [7 4]
            sage: N = block_matrix(QQ, [[M, 0],[0, 1]])
            sage: op_cols(N, 2, 0, 10)
            [  1   2   0]
            [  3   4   0]
            [-10   0   1]
            sage: op_cols(N, 1, 2, 1)
            [ 1  2 -2]
            [ 3  4 -4]
            [ 0  0  1]

        This method raises a ValueError when the indices are not valid::
            
            sage: op_cols(N, -1, 2, 1)
            Traceback (most recent call last):
            ...
            ValueError: The source column index is not valid
            sage: op_cols(N, 1, -2, 1)
            Traceback (most recent call last):
            ...
            ValueError: The destiny column index is not valid

        Also, if the input for the matrix is not such, the method raises a TypeError::

            sage: op_cols([[1,2,0],[3,4,0],[0,0,1]], 1, 2, 1)
            Traceback (most recent call last):
            ...
            TypeError: First argument must be a matrix. ...

        It is interesting to remark that this method is equivalent to the application of the 
        method :func:`op_rows` on the transposed matrix::

            sage: op_cols(N, 2, 0, 10) == (op_rows(N.transpose(), 2, 0, 10)).transpose()
            True
    '''
    try:
        if(0 > s_c or s_c >= M.ncols()):
            raise ValueError("The source column index is not valid")
        if(0 > d_c or d_c >= M.ncols()):
            raise ValueError("The destiny column index is not valid")

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
    r'''
        Method for performing the rescale of a row in Gauss-Jordan elimination.

        This method takes a matrix `M`, a row index and an element from the 
        parent ring of `M` and returns a new matrix where the elements in the 
        row have been scaled by the element.

        This is one of the basic steps while performing Gauss-Jordan elimination
        on a matrix to compute its determinant/nullspace/solution space/rank etc.

        INPUT:
            * ``M``: the original matrix with entries `m_{i,j}`.
            * ``d_r``: index of the row where the scaling will be performed.
            * ``el``: element in the base ring of ``M`` that will be used in the scaling.

        OUTPUT:
            A new matrix `\tilde{M}` with entries `\tilde{m}_{i,j}` such that:
                * If ``i != d_r``: `\tilde{m}_{i,j} = m_{i,j}`.
                * Else: `\tilde{m}_{d_r,j} = (el)m_{d_r,j}`.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix(QQ, [[1,2],[3,4]])
            sage: scal_row(M, 0, 2)
            [2 4]
            [3 4]
            sage: scal_row(M, 1, -1)
            [ 1  2]
            [-3 -4]
            sage: N = block_matrix(QQ, [[M, 0],[0, 1]])
            sage: scal_row(N, 2, 10)
            [ 1  2  0]
            [ 3  4  0]
            [ 0  0 10]
            sage: scal_row(N, 1, 1)
            [1 2 0]
            [3 4 0]
            [0 0 1]

        This method raises a ValueError when the index is not valid::
            
            sage: scal_row(N, -1, 1)
            Traceback (most recent call last):
            ...
            ValueError: The row index is not valid
            sage: scal_row(N, 10, 1)
            Traceback (most recent call last):
            ...
            ValueError: The row index is not valid

        Also, if the input for the matrix is not such, the method raises a TypeError::

            sage: scal_row([[1,2,0],[3,4,0],[0,0,1]], 2, 10)
            Traceback (most recent call last):
            ...
            TypeError: First argument must be a matrix. ...

        It is interesting to remark that this method is equivalent to the application of the 
        method :func:`op_rows` with the same destiny and source indices and the element
        being ``-element+1``::

            sage: scal_row(N, 2, 10) == op_rows(N, 2, 2, -9)
            True
    '''
    try:
        if(0 > d_r or d_r >= M.nrows()):
            raise ValueError("The row index is not valid")

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
    r'''
        Method for performing the rescale of a column in Gauss-Jordan elimination.

        This method takes a matrix `M`, a column index and an element from the 
        parent ring of `M` and returns a new matrix where the elements in the 
        column have been scaled by the element.

        This is one of the basic steps while performing Gauss-Jordan elimination
        on a matrix to compute its determinant/nullspace/solution space/rank etc.

        INPUT:
            * ``M``: the original matrix with entries `m_{i,j}`.
            * ``d_c``: index of the column where the scaling will be performed.
            * ``el``: element in the base ring of ``M`` that will be used in the scaling.

        OUTPUT:
            A new matrix `\tilde{M}` with entries `\tilde{m}_{i,j}` such that:
                * If ``j != d_c``: `\tilde{m}_{i,j} = m_{i,j}`.
                * Else: `\tilde{m}_{i,d_c} = (el)m_{i,d_c}`.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix(QQ, [[1,2],[3,4]])
            sage: scal_col(M, 0, 2)
            [2 2]
            [6 4]
            sage: scal_col(M, 1, -1)
            [ 1 -2]
            [ 3 -4]
            sage: N = block_matrix(QQ, [[M, 0],[0, 1]])
            sage: scal_col(N, 2, 10)
            [ 1  2  0]
            [ 3  4  0]
            [ 0  0 10]
            sage: scal_col(N, 1, 1)
            [1 2 0]
            [3 4 0]
            [0 0 1]

        This method raises a ValueError when the index is not valid::
            
            sage: scal_col(N, -1, 1)
            Traceback (most recent call last):
            ...
            ValueError: The column index is not valid
            sage: scal_col(N, 10, 1)
            Traceback (most recent call last):
            ...
            ValueError: The column index is not valid

        Also, if the input for the matrix is not such, the method raises a TypeError::

            sage: scal_col([[1,2,0],[3,4,0],[0,0,1]], 2, 10)
            Traceback (most recent call last):
            ...
            TypeError: First argument must be a matrix. ...

        It is interesting to remark that this method is equivalent to the application of the 
        method :func:`op_cols` with the same destiny and source indices and the element
        being ``-element+1``::

            sage: scal_col(N, 2, 10) == op_cols(N, 2, 2, -9)
            True
    '''
    try:
        if(0 > d_c or d_c >= M.ncols()):
            raise ValueError("The column index is not valid")
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
    r'''
        Method for performing the swap of two rows in Gauss-Jordan elimination.

        This method takes a matrix `M`, two row indices and returns a new matrix where
        the elements in the rows have been swapped.

        This is one of the basic steps while performing Gauss-Jordan elimination
        on a matrix to compute its determinant/nullspace/solution space/rank etc.

        INPUT:
            * ``M``: the original matrix with entries `m_{i,j}`.
            * ``r1``: first index of the column to be swapped.
            * ``r2``: second index of the column to be swapped.

        OUTPUT:
            A new matrix where the elements of the columns indexed by ``r1`` and ``r2``
            have been exchanged.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix(QQ, [[1,2],[3,4]])
            sage: swap_rows(M, 0, 1)
            [3 4]
            [1 2]
            sage: N = block_matrix(QQ, [[M, 0],[0, 1]])
            sage: swap_rows(N, 0, 1)
            [3 4 0]
            [1 2 0]
            [0 0 1]
            sage: swap_rows(N, 1, 2)
            [1 2 0]
            [0 0 1]
            [3 4 0]

        This method raises a ValueError when the index is not valid::
            
            sage: swap_rows(N, -1, 1)
            Traceback (most recent call last):
            ...
            ValueError: The first row index is not valid
            sage: swap_rows(N, 1, 10)
            Traceback (most recent call last):
            ...
            ValueError: The second row index is not valid

        Also, if the input for the matrix is not such, the method raises a TypeError::

            sage: swap_rows([[1,2,0],[3,4,0],[0,0,1]], 2, 10)
            Traceback (most recent call last):
            ...
            TypeError: First argument must be a matrix. ...
    '''
    try:
        if(0 > r1 or r1 >= M.ncols()):
            raise ValueError("The first row index is not valid")
        if(0 > r2 or r2 >= M.ncols()):
            raise ValueError("The second row index is not valid")

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
    r'''
        Method for performing the swap of two columns in Gauss-Jordan elimination.

        This method takes a matrix `M`, two column indices and returns a new matrix where
        the elements in the columns have been swapped.

        This is one of the basic steps while performing Gauss-Jordan elimination
        on a matrix to compute its determinant/nullspace/solution space/rank etc.

        INPUT:
            * ``M``: the original matrix with entries `m_{i,j}`.
            * ``c1``: first index of the column to be swapped.
            * ``c2``: second index of the column to be swapped.

        OUTPUT:
            A new matrix where the elements of the columns indexed by ``c1`` and ``c2``
            have been exchanged.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix(QQ, [[1,2],[3,4]])
            sage: swap_cols(M, 0, 1)
            [2 1]
            [4 3]
            sage: N = block_matrix(QQ, [[M, 0],[0, 1]])
            sage: swap_cols(N, 0, 1)
            [2 1 0]
            [4 3 0]
            [0 0 1]
            sage: swap_cols(N, 1, 2)
            [1 0 2]
            [3 0 4]
            [0 1 0]

        This method raises a ValueError when the index is not valid::
            
            sage: swap_cols(N, -1, 1)
            Traceback (most recent call last):
            ...
            ValueError: The first column index is not valid
            sage: swap_cols(N, 1, 10)
            Traceback (most recent call last):
            ...
            ValueError: The second column index is not valid

        Also, if the input for the matrix is not such, the method raises a TypeError::

            sage: swap_cols([[1,2,0],[3,4,0],[0,0,1]], 2, 10)
            Traceback (most recent call last):
            ...
            TypeError: First argument must be a matrix. ...
    '''
    try:
        if(0 > c1 or c1 >= M.ncols()):
            raise ValueError("The first column index is not valid")
        if(0 > c2 or c2 >= M.ncols()):
            raise ValueError("The second column index is not valid")

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
    r'''
        Method that turns a matrix either horizontally or vertically.

        This method takes a matrix and compute its reverse matrix in one direction: 
        horizontally, changing the position of the columns, or vertically, changing
        the position of the rows.

        If we do both turnings, we obtain the transpose matrix.

        INPUT:
            * ``M``: a matrix to be turned
            * ``vertical``: whether the turn is vertically or not. If not given, we
              always perform a horizontal turn.

        OUTPUT: 
            The corresponding turned matrix.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix([[1, 2],[3, 4]])
            sage: turn_matrix(M)
            [2 1]
            [4 3]
            sage: N = block_matrix(QQ, [[M, 0],[0, 1]])
            sage: turn_matrix(N)
            [0 2 1]
            [0 4 3]
            [1 0 0]
            sage: turn_matrix(N, True)
            [0 0 1]
            [3 4 0]
            [1 2 0]
    '''
    if(vertical):
        new_rows = [[M[i][j] for j in range(M.ncols())] for i in range(-1 ,-M.nrows()-1 ,-1 )]
    else:
        new_rows = [[M[i][j] for j in range(-1 ,-M.ncols()-1 ,-1 )] for i in range(M.nrows())]
        
    return Matrix(M.parent().base(), new_rows)
        
def simplify_matrix(M):
    r'''
        Method to simplify the entries of a matrix.

        This method computes an equivalent matrix to that given in the input and
        call the method ``simplify`` of the entries in that matrix to try and
        simplify it.

        If this simplification method does not exist, this method **DO NOT** raise an
        error. It just simply assumes that there is no simplification and return 
        the original matrix.

        INPUT:
            * ``M``: a matrix that will be simplified.

        OUTPUT:
            A matrix `\tilde{M}` such that is equal to `M`.
    '''
    try:
        return Matrix(M.parent().base(), [[el.simplify() for el in row] for row in M])
    except AttributeError:
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
    r'''
        Method to compute the direct sum of several matrices.

        This method computes the direct sum of several matrices, i.e., it computes a diagonal
        matrix where the elements in the diagonal are the matrices that we have as input.

        This method is just a generic alias for the method :func:`diagonal_matrix`. However,
        it performs the checking of compatibility between the parents of the matrices.
    '''
    from sage.categories.pushout import pushout
    #Computation of a common parent
    try:
        R = reduce(lambda p, q : pushout(p,q), [el.parent().base() for el in matrices])
    except AttributeError:
        raise TypeError("All the elements must be matrices")
    return diagonal_matrix(R, matrices)

def kronecker_sum(M,N):
    r'''
        Method that computes the Kronecker sum of two matrices.

        Given two square matrices `M` and `N` of sizes `m` and `n` the Kronecker sum is defined, using the tensor
        product between matrices, as:

        .. MATH::

            M \boxplus N = M \otimes I_n + I_m \otimes N

        This method simply computes the Kronecker sum of two square matrices.

        INPUT:
            * ``M``: first operand of the Kronecker sum
            * ``N``: second operand of the Kronecker sum

        OUTPUT:
            The matrix ``M \boxplus N``.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = Matrix([[1,2],[3,4]]); N = Matrix([[1,0,2],[0,3,0],[4,0,5]])
            sage: kronecker_sum(M,N)
            [2 0 2 2 0 0]
            [0 4 0 0 2 0]
            [4 0 6 0 0 2]
            [3 0 0 5 0 2]
            [0 3 0 0 7 0]
            [0 0 3 4 0 9]

        The Kroenecker sum, when one of the operands is just one element, can be seen as the addition
        of the corresponding diagonal matrix::

            sage: kronecker_sum(M, Matrix([[1]]))
            [2 2]
            [3 5]
            sage: kronecker_sum(Matrix([[7]]), N)
            [ 8  0  2]
            [ 0 10  0]
            [ 4  0 12]
    '''
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
def kappa_v(v, D):
    r'''
        Methot that apply a derivation to each component of a vector.

        When we have a vector space `V` over a differential field `(F,D)`, we can define
        "derivations" over `V` as those maps `\partial: V \rightarrow V` such that for all `v, w \in V`
        and all `f \in F`:
            * `\partial(v+w) = \partial(v) + \partial(w)`.
            * `\partial(fv) = D(f)v + f\partial(v)`.

        It can be shown (see Appendix A of the thesis by the author of the file) that, fixed a basis,
        this derivation is uniquely determined by a matrix `M` in such a way that, for all `v \in V`,
        the derivation can be computed with a matrix-vector multiplication:

        .. MATH::

            \partial(v) = Mv + \kappa_D(v),

        where this `\kappa_D` is the terminwise derivation of the coordinates.

        This method computes, given the derivation `D`, the value of `\kappa_D(v)` for a given vector.

        INPUT:
            * ``v``: vector we want to manipulate.
            * ``D``: derivation over the ground field.
        
        OUPUT:
            The vector `w = \kappa_D(v)`.
        
        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: D = lambda p : p.derivative(x); v = vector(QQ[x], [1+x, 1, x^2])
            sage: kappa_v(v, D)
            (1, 0, 2*x)
    '''
    return vector(v.parent().base(), [D(a) for a in v])
    
def vector_derivative(M, v, D):
    r'''
        Method to compute the derivative of a vector.

        When we have a vector space `V` over a differential field `(F,D)`, we can define
        "derivations" over `V` as those maps `\partial: V \rightarrow V` such that for all `v, w \in V`
        and all `f \in F`:
            * `\partial(v+w) = \partial(v) + \partial(w)`.
            * `\partial(fv) = D(f)v + f\partial(v)`.

        It can be shown (see Appendix A of the thesis by the author of the file) that, fixed a basis,
        this derivation is uniquely determined by a matrix `M` in such a way that, for all `v \in V`,
        the derivation can be computed with a matrix-vector multiplication:

        .. MATH::

            \partial(v) = Mv + \kappa_D(v),

        where this `\kappa_D` is the terminwise derivation of the coordinates.

        This method takes the matrix `M`, a vector `v` and the corresponding derivation `D` and computes
        the derivation of the vector `v`.

        INPUT:
            * ``M``: the matrix defining the derivation under the current basis.
            * ``v``: the vector (expressed in the current basis) that we want to derivate
            * ``D``: the derivation over the ground field.

        OUTPUT:
            A vector `w` such that `w = \partial(v)` for the derivation `\partial` defined from `D`
            and `M`.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = vandermonde_matrix(QQ[x], [1,x,x^2]); v = vector(QQ[x], [1+x, 1, x^2])
            sage: D = lambda p : p.derivative(x)
            sage: vector_derivative(M, v, D)
            (x^2 + x + 3, x^4 + 2*x + 1, x^6 + x^2 + 3*x + 1)

        We can see that the columns of `M` are exactly the derivatives of the trivial basis::

            sage: vector_derivative(M, vector(QQ[x],[1,0,0]), D)
            (1, 1, 1)
            sage: vector_derivative(M, vector(QQ[x],[0,1,0]), D)
            (1, x, x^2)
            sage: vector_derivative(M, vector(QQ[x],[0,0,1]), D)
            (1, x^2, x^4)
    '''
    return M*v+kappa_v(v,D)
    
def matrix_of_dMovement(M,v,D, cols):
    r'''
        Method to construct a matrix where the columns are iterative derivations of a vector.

        When we have a vector space `V` over a differential field `(F,D)`, we can define
        "derivations" over `V` as those maps `\partial: V \rightarrow V` such that for all `v, w \in V`
        and all `f \in F`:
            * `\partial(v+w) = \partial(v) + \partial(w)`.
            * `\partial(fv) = D(f)v + f\partial(v)`.

        It can be shown (see Appendix A of the thesis by the author of the file) that, fixed a basis,
        this derivation is uniquely determined by a matrix `M` in such a way that, for all `v \in V`,
        the derivation can be computed with a matrix-vector multiplication:

        .. MATH::

            \partial(v) = Mv + \kappa_D(v),

        where this `\kappa_D` is the terminwise derivation of the coordinates.

        This method computes several derivations of a particular vector and arrange the return as a matrix
        where these derivatives are in the columns of the matrix.

        INPUT:
            * ``M``: matrix defining the specific derivation for the fixed basis.
            * ``v``: starig vector which will be derivated several times.
            * ``D``: derivation over the ground field.
            * ``cols``: number of columns (i.e., derivations) that we will return.

        OUTPUT:
            A matrix `N=(n_{i,j})` where the columns are the derivations of `v`, i.e.,
            `(n_{0,j},n_{1,j},\ldots) = \partial^j(v)`.

        EXAMPLES::

            sage: from ajpastor.misc.matrix import *
            sage: M = vandermonde_matrix(QQ[x], [1,x,x^2]); v = vector(QQ[x], [1+x, 1, x^2])
            sage: D = lambda p : p.derivative(x)
            sage: matrix_of_dMovement(M, v, D, 3)
            [                                               x + 1                                          x^2 + x + 3                          x^6 + x^4 + 2*x^2 + 8*x + 6]
            [                                                   1                                        x^4 + 2*x + 1            x^8 + x^5 + x^4 + 7*x^3 + 4*x^2 + 2*x + 5]
            [                                                 x^2                                  x^6 + x^2 + 3*x + 1 x^10 + 2*x^6 + 9*x^5 + x^4 + 2*x^3 + 2*x^2 + 3*x + 6]

        We can check that the second column of that matrix is the derivative of the vector `v`::

            sage: [matrix_of_dMovement(M, v, D, 3)[i][1] for i in range(3)] == [el for el in vector_derivative(M, v, D)]
            True
    '''
    from sage.categories.pushout import pushout
    parent = pushout(M.parent().base(), v.parent().base())
    res = [v]
    for _ in range(1 ,cols):
        res += [vector_derivative(M,res[-1 ],D)]
    return Matrix(parent, res).transpose()
    

