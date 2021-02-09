r"""
Python file for an implementation of Bareiss' algorithm

This module offers an implementation of Hermite Normal Form computation. This algorithm can later be used to
solve linear system within Euclidean domains.

This is an adaptation of method described in https://www.ams.org/journals/mcom/1996-65-216/S0025-5718-96-00766-1/
for computing the Hermite Normal Form in Dedekind domains. Since Euclidean Domains are, in particular, Dedekind
domains, we use the corresponding and adapted method.

The main differences with the algorithm described in that paper is that we do a row echelon form and 
that we do not force the diagonal to have 1. Moreover, we do not need to have maximal rank, obtaining zero
rows in the end of the matrix.

Given a matrix `M` with `n` rows and `m` columns, a Hermite normal form (or HNF) is a matrix `H` equivalent
to `M` (i.e., there is a unimodular matrix `U` such that `UM = H`, also called *transformation matrix*)
such that every element below the main diagonal is zero. This is similar to computing the echelon
form as in a Gauss-Jordan elimination, but all operations stays in the same ring as the elements of 
`M` belong (given that it is an Euclidean domain).

AUTHORS:

    - Antonio Jimenez-Pastor (2021-02-08): initial version

"""

# ****************************************************************************
#  Copyright (C) 2021 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.all import identity_matrix, Matrix

def hermite_form(A, div, xgcd, is_zero):
    r'''
        Main method for computing the HNF
        
        TODO:
            * Fill the documentation
            * Add examples in several domains
    '''
    if(A.ncols()<A.nrows()):
        raise TypeError("We need more columns than rows")

    A = Matrix(A.parent().base(), A.rows()) # we create a copy
    U = identity_matrix(A.parent().base(), A.nrows())
    ## Step 1: initialize
    r = 0; c = 0 # we are looking from (r,c)
    while(r < A.nrows() and c < A.ncols()):
        ir,ic = find_pivot(A, r,c, is_zero)
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
    
def find_pivot(A, r,c, is_zero):
    r'''
        Method to find the next valid pivot.

        TODO:
            * Fill documentation
            * Add example
    '''
    for j in range(c,A.ncols()):
        for i in range(r, A.nrows()):
            if(not is_zero(A[i][j])):
                return i,j
    return None, None

    

