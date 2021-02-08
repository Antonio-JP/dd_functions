r"""
Python file for an implementation of Bareiss' algorithm

This module offers an implementation of Hermite Normal Form computation. This algorithm can later be used to
solve linear system within Euclidean domains.

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

from sage.all import identity_matrix, Matrix

def hermite_form(A, div, xgcd):
    if(A.ncols()<A.nrows()):
        raise TypeError("We need more columns than rows")

    A = Matrix(A.parent().base(), A.rows()) # we create a copy
    U = identity_matrix(A.parent().base(), A.nrows())
    ## Step 1: initialize
    r = 0; c = 0 # we are looking from (r,c)
    while(r < A.nrows() and c < A.ncols()):
        ir,ic = find_pivot(A, r,c)
        if(ir != None): # we found a pivot
            if(ir != r): # swapping rows
                A.swap_rows(r, ir); U.swap_rows(r,ir)
            if(ic != c): # swapping cols
                A.swap_cols(c,ic); U.swap_cols(c,ic)
            
            # We reduce in each row
            for m in range(r+1, A.nrows()):
                if(A[m][c] != 0):
                    g, t, s = xgcd(A[r][c], A[m][c])
                    p,_ = div(A[r][c],g); q,_ = div(A[m][c],g)

                    Ar = A.row(r); Am = A.row(m)
                    Ur = U.row(r); Um = U.row(m)

                    A.set_row(r,t*Ar + s*Am); U.set_row(r,t*Ur + s*Um)
                    A.set_row(m,q*Ar - p*Am); U.set_row(m,q*Ur - p*Um)
        r += 1; c+= 1
    return A, U
    
def find_pivot(A, r,c):
    for j in range(c,A.ncols()):
        for i in range(c, A.nrows()):
            if(A[i][j] != 0):
                return i,j
    return None, None

    

