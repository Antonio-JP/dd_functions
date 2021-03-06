r"""
Python file for a tests using bessel functions

This module test the equalities referring to the Bessel Functions.

EXAMPLES::
    sage: from ajpastor.tests.dd_functions.bessel import *

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

_sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_20 = Integer(20); _sage_const_4 = Integer(4)########################################################################
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
    __MIN_N = _sage_const_1 ;
    __MAX_N = _sage_const_20 ;

    __LEVEL = -_sage_const_2 ; ## Verbose level (-2 print loops, -1 print test, 0 print global data, greater print nothing
    __PREV_LEVEL = sverbose.get_level();

    sverbose.set_level(__LEVEL);
    __deep_wrap = sverbose.get_deep_wrapper();
    sverbose.set_deep_wrapper(-__LEVEL);
    sverbose("Running tests over Bessel Functions using the package dd_functions");
    sverbose("");
    sverbose("Author: Antonio Jimenez");
    sverbose("Date: 12-02-2018");
    sverbose("");
    sverbose("The values of the parameters will run from %d to %d" %(__MIN_N, __MAX_N));
    sverbose.increase_depth();

    ## Starting execution
    t = timer();

    try:
        sverbose("Checking 2nxJ_n(x) = J_{n-1}(x)+J_{n+1}(x)");
        sverbose.increase_depth();
        sverbose.start_iteration(__MAX_N-__MIN_N, True, True);
        for n in range(__MIN_N, __MAX_N):
            f = BesselD(n); fp = BesselD(n+_sage_const_1 ); fm = BesselD(n-_sage_const_1 );
            if(not _sage_const_2 *n*f == (fm+fp)*x):
                raise ValueError("Error with the equality of 0F0(;;z) with initial value %d" %n);
            sverbose.next_iteration();
            
        sverbose.decrease_depth();
        sverbose("Finished test");
        
        sverbose("Checking 2xJ_n'(x) = J_{n-1}(x)-J_{n+1}(x)");
        sverbose.increase_depth();
        sverbose.start_iteration(__MAX_N-__MIN_N, True, True);
        for n in range(__MIN_N, __MAX_N):
            f = BesselD(n); fp = BesselD(n+_sage_const_1 ); fm = BesselD(n-_sage_const_1 );
            if(not _sage_const_2 *f.derivative() == (fm-fp)):
                raise ValueError("Error with the equality of 0F0(;;z) with initial value %d" %n);
            sverbose.next_iteration();
            
        sverbose.decrease_depth();
        sverbose("Finished test");
        
        sverbose("Checking J_n(x) = ((x/2)^n/(n!))*0F1(;n+1;-x^2/4)");
        sverbose.increase_depth();
        sverbose.start_iteration(__MAX_N-__MIN_N, True, True);
        for n in range(__MIN_N, __MAX_N):
            sverbose.increase_depth();
            f = BesselD(n);
            g = GenericHypergeometricFunction((),(n+_sage_const_1 ),_sage_const_1 )(-x**_sage_const_2 /_sage_const_4 );
            if(not f == ((x/_sage_const_2 )**n/factorial(n))*g):
                raise ValueError("Error with the equality of 0F0(;;z) with initial value %d" %n);
            sverbose.decrease_depth();
            sverbose.next_iteration();
            
        sverbose.decrease_depth();
        sverbose("Finished test");
    except (Exception, KeyboardInterrupt) as e:
        sverbose.reset_depth();
        sverbose.set_deep_wrapper(__deep_wrap);
        sverbose.set_level(__PREV_LEVEL);
        raise e;

    sverbose.decrease_depth();
    sverbose("Finished all tests over the Generic Hypergeometric functions");
    t = timer() - t;
    sverbose("Parametric tests finished successfully --> %s" %(t));
    sverbose.set_deep_wrapper(__deep_wrap);
    sverbose.set_level(__PREV_LEVEL);

