r"""
Python file for a tests on identities

This module test several identities with DDFunctions.

EXAMPLES::
    sage: from ajpastor.tests.dd_functions.identities import *

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

_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_10 = Integer(10); _sage_const_0 = Integer(0)
import sys, traceback;
from timeit import default_timer as timer;

from ajpastor.misc.verbose import *;
from ajpastor.dd_functions import *;


def run():
    __MIN_N = _sage_const_2 ;
    __MAX_N = _sage_const_10 ;
    __DIFF = __MAX_N - __MIN_N;

    __LEVEL = -_sage_const_2 ; ## Verbose level (-2 print loops, -1 print test, 0 print global data, greater print nothing
    __PREV_LEVEL = sverbose.get_level();

    def assert_initial(func, symbolic, size, name):
        for i in range(size):
            func_val = func.getInitialValue(i);
            real_val = symbolic.derivative(i)(x=_sage_const_0 );
            assert (func_val == real_val), "Error in the %d initial value of the function %s: expected %s but got %s"%(i,name,real_val,func_val);
            
    def random_polynomial(min=-_sage_const_10 ,max=_sage_const_10 ,degree=_sage_const_3 ):
        R = PolynomialRing(QQ,x);
        p = R(_sage_const_1 );
        while(p.degree() == _sage_const_0 ):
            p = R([randint(min,max) for i in range(degree+_sage_const_1 )])
        
        return p;


    ####################################################################################

    sverbose.set_level(__LEVEL);
    __deep_wrap = sverbose.get_deep_wrapper();
    sverbose.set_deep_wrapper(-__LEVEL);
    sverbose("Running tests over identities of DDFunctions");
    sverbose("");
    sverbose("Author: Antonio Jimenez");
    sverbose("Date: 13-02-2018");
    sverbose("");
    sverbose.increase_depth();
              

    ##Starting execution
    t = timer();
    #########################################
    ### TESTS FOR STRUCTURES DDRing and DDFunction
    #########################################
    try:
        
        sverbose("Checking trigonometric equalities");
        sverbose.increase_depth();
        sverbose("sin^2(x)+cos^2(x) = 1");
        assert Sin(x)**_sage_const_2 +Cos(x)**_sage_const_2  == _sage_const_1 , "Error with sin^2(x)+cos^2(x) = 1";
        sverbose("sin(2x) = 2sin(x)cos(x)");
        assert Sin(_sage_const_2 *x) == _sage_const_2 *Sin(x)*Cos(x) , "Error with sin(2x) = 2sin(x)cos(x)";
        sverbose("cos(2x) = cos^2(x) - sin^2(x)");
        assert Cos(_sage_const_2 *x) == Cos(x)**_sage_const_2  - Sin(x)**_sage_const_2 , "Error with cos(2x) = cos^2(x) - sin^2(x)";
        sverbose("tan(x) = sin(x)/cos(x)");
        sverbose.increase_depth();
        assert Tan(x) == Sin(x)/Cos(x), "Error with tan(x) = sin(x)/cos(x)";
        sverbose.decrease_depth();
        sverbose("tan'(x) = 1 + tan^2(x)");
        ## Including the sine and cosine in the system of DFinite
        R = Tan(x).equation._FullLazyOperator__conversion;
        #assert R(Sin(x))^2+R(Cos(x))^2 == 1, "Error with sin^2(x)+cos^2(x) = 1 in the Lazy Ring";
        sverbose.increase_depth();
        assert Tan(x).derivative() ==  Tan(x)**_sage_const_2 + _sage_const_1  , "Error with tan'(x) = 1 + tan^2(x)";
        sverbose.decrease_depth();
        
        sverbose.decrease_depth();
        sverbose("Checking some parametric equalities");
        sverbose.increase_depth();
        sverbose("Matheiu Wronskian");
        f = MathieuCos(); g = MathieuSin();
        sverbose.increase_depth();
        assert f*g.derivative()-g*f.derivative() == _sage_const_1 , "Error with the Mathieu's Wronskian";
        sverbose.decrease_depth();
        sverbose.decrease_depth();
        sverbose("Finished tests");
        
    except (Exception, KeyboardInterrupt) as e:
        sverbose.reset_depth();
        sverbose.set_level(__PREV_LEVEL);
        print("Error found during tests: %s" %(e));
        raise e;
        
    sverbose.decrease_depth();
    sverbose("Finished all the tests on the examples");
    t = timer() - t;
    sverbose("Example tests finished successfully --> %s" %(t));
    sverbose.set_deep_wrapper(__deep_wrap);
    sverbose.set_level(__PREV_LEVEL);


