r"""
Python file for a tests using chebyshev polynomials

This module test the equalities referring to the Chebyshev Polynomials.

EXAMPLES::
    sage: from ajpastor.tests.dd_functions.chebyshev import *

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

from sage.all_cmdline import *   # import sage library

_sage_const_2 = Integer(2); _sage_const_20 = Integer(20); _sage_const_0 = Integer(0); _sage_const_1 = Integer(1)########################################################################
###
### File for testing the definition of Chebyshev polynomials
###
### Here we will check several identities of the Chebyshev polynomials
### for different values of the parameter $n$.
###
########################################################################

from timeit import default_timer as timer;

from ajpastor.dd_functions import *;
from ajpastor.misc.verbose import *;

def run():
    __MIN_N = _sage_const_2 ;
    __MAX_N = _sage_const_20 ;

    __LEVEL = -_sage_const_2 ; ## Verbose level (-2 print loops, -1 print test, 0 print global data, greater print nothing

    __PREV_LEVEL = sverbose.get_level();

    sverbose.set_level(__LEVEL);
    __deep_wrap = sverbose.get_deep_wrapper();
    sverbose.set_deep_wrapper(-__LEVEL);
    sverbose("Running test over the Chebyshev polynomials using dd_functions package");
    sverbose("");
    sverbose("Author: Antonio Jimenez");
    sverbose("Date: 12-07-2017");
    sverbose("");
    sverbose("All values of the parameter will run from %d to %d" %(__MIN_N, __MAX_N));
    sverbose.increase_depth();

    ## Starting execution
    t = timer();

    try:
        ### Checking the recursive equality
        sverbose("Recursion formula: p_{n+1} = 2xp_n - p_{n-1}");
        sverbose.increase_depth();
        sverbose.start_iteration(__MAX_N-__MIN_N, True, True);
        for n in range(__MIN_N, __MAX_N):
            ch1 = [ChebyshevD(n+_sage_const_1 ),ChebyshevD(n),ChebyshevD(n-_sage_const_1 )];
            ch2 = [ChebyshevD(n+_sage_const_1 ,_sage_const_2 ),ChebyshevD(n,_sage_const_2 ),ChebyshevD(n-_sage_const_1 ,_sage_const_2 )];
            is_true = [(ch1[_sage_const_0 ] == _sage_const_2 *x*ch1[_sage_const_1 ] - ch1[_sage_const_2 ]),(ch2[_sage_const_0 ] == _sage_const_2 *x*ch2[_sage_const_1 ] - ch2[_sage_const_2 ])];
            if(not is_true[_sage_const_0 ]):
                raise ValueError("Error with the recurrence equality for Chebyshev of first kind (%d)" %n);
            if(not is_true[_sage_const_1 ]):
                raise ValueError("Error with the recurrence equality for Chebyshev of second kind (%d)" %n);
            sverbose.next_iteration();
            
        sverbose.decrease_depth();

        sverbose("Finished test");

        ### Checking Pell's equation
        sverbose("Pell's equation: T_n^2 - (x^2-1)U_{n-1}^2 = 1");
        sverbose.increase_depth();
        sverbose.start_iteration(__MAX_N-__MIN_N, True, True);
        for n in range(__MIN_N, __MAX_N):
            T = ChebyshevD(n,_sage_const_1 ); U = ChebyshevD(n-_sage_const_1 ,_sage_const_2 );
            if(not (T**_sage_const_2 -(x**_sage_const_2 -_sage_const_1 )*U**_sage_const_2  == _sage_const_1 )):
                raise ValueError("Error with the Pell's equation for n=%d" %n);
            sverbose.next_iteration();
            
        sverbose.decrease_depth();

        ### Derivation properties
        sverbose("Derivative equations");
        sverbose.increase_depth();
        sverbose.start_iteration(__MAX_N-__MIN_N, True, True);
        for n in range(__MIN_N, __MAX_N):
            T = [ChebyshevD(n,_sage_const_1 ),ChebyshevD(n+_sage_const_1 ,_sage_const_1 )]; U = [ChebyshevD(n,_sage_const_2 ),ChebyshevD(n-_sage_const_1 ,_sage_const_2 )];
            if(not (T[_sage_const_0 ].derivative() == n*U[-_sage_const_1 ])):
                raise ValueError("Error with the derivate of $T_%d$" %n);
            if(not (U[_sage_const_0 ].derivative() == ((n+_sage_const_1 )*T[_sage_const_1 ] - x*U[_sage_const_0 ]).divide(DFinite(x**_sage_const_2 -_sage_const_1 )))):
                raise ValueError("Error with the derivate of $U_%d$" %n);
            sverbose.next_iteration();
            
        sverbose.decrease_depth();

        sverbose("Finished test");      
    except (Exception, KeyboardInterrupt) as e:
        sverbose.reset_depth();
        sverbose.set_deep_wrapper(__deep_wrap);
        sverbose.set_level(__PREV_LEVEL);
        raise e;

    sverbose.decrease_depth();
    sverbose("Finished all tests over the Chebyshev polynomials");
    t = timer() - t;
    sverbose("Chebyshev polynomials tests finished successfully --> %s" %(t));
    sverbose.set_deep_wrapper(__deep_wrap);
    sverbose.set_level(__PREV_LEVEL);

