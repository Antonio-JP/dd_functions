r"""
Python file for a tests using hypergeometric functions

This module test the equalities referring to the Hypergeometric Functions.

EXAMPLES::
    sage: from ajpastor.tests.dd_functions.hypergeometric import *

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

_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_10 = Integer(10); _sage_const_4 = Integer(4)########################################################################
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
    __MAX_N = _sage_const_10 ;

    __LEVEL = -_sage_const_2 ; ## Verbose level (-2 print loops, -1 print test, 0 print global data, greater print nothing
    __PREV_LEVEL = sverbose.get_level();

    sverbose.set_level(__LEVEL);
    __deep_wrap = sverbose.get_deep_wrapper();
    sverbose.set_deep_wrapper(-__LEVEL);
    sverbose("Running test over the Generic Hypergeometric Functions using dd_functions package");
    sverbose("");
    sverbose("Author: Antonio Jimenez");
    sverbose("Date: 01-08-2017");
    sverbose("");
    sverbose("All values of the parameters will run from %d to %d" %(__MIN_N, __MAX_N));
    sverbose.increase_depth();

    ## Starting execution
    t = timer();

    try:
        sverbose("Identity for 0F0");
        sverbose.increase_depth();
        sverbose.start_iteration(__MAX_N-__MIN_N, True, True);
        for n in range(__MIN_N, __MAX_N):
            f = GenericHypergeometricFunction((),(),n);
            g = n*Exp(x);
            if(not f == g):
                raise ValueError("Error with the equality of 0F0(;;z) with initial value %d" %n);
            sverbose.next_iteration();
            
        sverbose.decrease_depth();

        sverbose("Finished test");

        sverbose("Identity for 1F0");
        sverbose.increase_depth();

        sverbose.start_iteration((__MAX_N-__MIN_N)**_sage_const_2 , True, True);
        for a in range(__MIN_N, __MAX_N):
            for n in range(__MIN_N, __MAX_N):
                f = GenericHypergeometricFunction((a),(),n);
                g = DFinite.element([-a,_sage_const_1 -x],[n]);
                if(not f == g):
                    raise ValueError("Error with the equality of 1F0(%d;;z) with initial value %d" %(a,n));
                sverbose.next_iteration();
            
        sverbose.decrease_depth();

        sverbose("Finished test");

        sverbose("Identity for 0F1");
        sverbose.increase_depth();
        sverbose.start_iteration((__MAX_N-__MIN_N)**_sage_const_2 , True, True);
        for a in range(__MIN_N, __MAX_N):
            for n in range(__MIN_N, __MAX_N):
                f = GenericHypergeometricFunction((),(a),n);
                g = DFinite.element([-_sage_const_1 ,a,x],[n]);
                if(not f == g):
                    raise ValueError("Error with the equality of 1F0(;%d;z) with initial value %d" %(a,n));
                sverbose.next_iteration();
            
        sverbose.decrease_depth();

        sverbose("Finished test");

        sverbose("Identity for 1F1");
        sverbose.increase_depth();
        sverbose.start_iteration((__MAX_N-__MIN_N)**_sage_const_3 , True, True);
        for a in range(__MIN_N, __MAX_N):
            for b in range(__MIN_N, __MAX_N):
                for n in range(__MIN_N, __MAX_N):
                    f = GenericHypergeometricFunction((a),(b),n);
                    g = DFinite.element([-a,(b-x),x],[n]);
                    if(not f == g):
                        raise ValueError("Error with the equality of 1F1(%d;%d;z) with initial value %d" %(a,b,n));
                    sverbose.next_iteration();
            
        sverbose.decrease_depth();

        sverbose("Finished test");

        sverbose("Identity for 2F1 (Usual Hypergeometric function)");
        sverbose.increase_depth();
        sverbose("Test for derivative of hypergeometric function and its contiguous functions");
        f = HypergeometricFunction(); P = f.parent(); a = P.parameter('a'); b = P.parameter('b'); c = P.parameter('c');
        g = a*b/c * HypergeometricFunction(a+1,b+1,c+1);
        if(not f.derivative() == g):
            raise ValueError("Error with the equality of 2F1(a,b;c;z)");
        sverbose
        sverbose.start_iteration((__MAX_N-__MIN_N)**_sage_const_4 , True, True);
        for a in range(__MIN_N, __MAX_N):
            for b in range(__MIN_N, __MAX_N):
                for c in range(__MIN_N, __MAX_N):
                    for n in range(__MIN_N, __MAX_N):
                        f = HypergeometricFunction(a,b,c,n);
                        g = DFinite.element([-a*b,c-(a+b+_sage_const_1 )*x, x*(_sage_const_1 -x)],[n]);
                        if(not f == g):
                            raise ValueError("Error with the equality of 2F1(%d,%d;%d;z) with initial value %d" %(a,b,c,n));
                        sverbose.next_iteration();
            
        sverbose.decrease_depth();

        sverbose("Finished test");

        ### Clausen's formula
        sverbose("Clausen's formula");
        sverbose.increase_depth();
        sverbose.start_iteration((__MAX_N-__MIN_N)**_sage_const_2 , True, True);
        for c in range(__MIN_N, __MAX_N):
            for s in range(__MIN_N, __MAX_N):
                        f = GenericHypergeometricFunction((_sage_const_2 *c-_sage_const_2 *s-_sage_const_1 ,_sage_const_2 *s,c-_sage_const_1 /_sage_const_2 ),(_sage_const_2 *c-_sage_const_1 ,c));
                        g = GenericHypergeometricFunction((c-s-_sage_const_1 /_sage_const_2 ,s),(c))
                        if(not f == g**_sage_const_2 ):
                            raise ValueError("Error with the Clausen's formula for parameters c=%d and s=%d" %(c,s));
                        sverbose.next_iteration();
            
        sverbose.decrease_depth();

        sverbose("Finished test");
    except (Exception, KeyboardInterrupt) as e:
        sverbose.reset_depth();
        sverbose.set_level(__PREV_LEVEL);
        raise e;

    sverbose.decrease_depth();
    sverbose("Finished all tests over the Generic Hypergeometric functions");
    t = timer() - t;
    sverbose("Hypergeometric function tests finished successfully --> %s" %(t));
    sverbose.set_deep_wrapper(__deep_wrap);
    sverbose.set_level(__PREV_LEVEL);


