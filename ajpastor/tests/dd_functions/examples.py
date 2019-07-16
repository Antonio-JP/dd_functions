r"""
Python file for a tests the module ajpastor.dd_functions.ddExamples

This module test the examples provided in ajpastor.dd_functions.ddExamples that are not covered in other tests.

EXAMPLES::
    sage: from ajpastor.tests.dd_functions.examples import *

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

_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_0 = Integer(0); _sage_const_4 = Integer(4); _sage_const_8 = Integer(8); _sage_const_10 = Integer(10)
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
        while(p.degree() <= _sage_const_0 ):
            p = R([randint(min,max) for i in range(degree+_sage_const_1 )])
        
        return p;


    ####################################################################################

    sverbose.set_level(__LEVEL);
    __deep_wrap = sverbose.get_deep_wrapper();
    sverbose.set_deep_wrapper(-__LEVEL);
    sverbose("Running tests over the example functions of DDRings");
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
        
        sverbose("Checking built-in functions");
        sverbose.increase_depth();
        sverbose.start_iteration(_sage_const_8 +_sage_const_4 *__DIFF, True, True);
        sverbose.increase_depth();
        assert_initial(Exp(x), exp(x), _sage_const_10 , "exp(x)");
        sverbose.decrease_depth();    
        sverbose.next_iteration();
        sverbose.increase_depth();
        assert_initial(Sin(x), sin(x), _sage_const_10 , "sin(x)");
        sverbose.decrease_depth();    
        sverbose.next_iteration();
        sverbose.increase_depth();
        assert_initial(Cos(x), cos(x), _sage_const_10 , "cos(x)");
        sverbose.decrease_depth();    
        sverbose.next_iteration();
        sverbose.increase_depth();
        assert_initial(Sinh(x), sinh(x), _sage_const_10 , "sinh(x)");
        sverbose.decrease_depth();    
        sverbose.next_iteration();
        sverbose.increase_depth();
        assert_initial(Cosh(x), cosh(x), _sage_const_10 , "cosh(x)");
        sverbose.decrease_depth();    
        sverbose.next_iteration();
        sverbose.increase_depth();
        assert_initial(Tan(x), tan(x), _sage_const_10 , "Tan(x)");
        sverbose.decrease_depth();    
        sverbose.next_iteration();
        sverbose.increase_depth();
        assert_initial(Log(x+_sage_const_1 ), log(x+_sage_const_1 ), _sage_const_10 , "log(x+1)");
        sverbose.decrease_depth();    
        sverbose.next_iteration();
        sverbose.increase_depth();
        assert_initial(Log1(x), log(x+_sage_const_1 ), _sage_const_10 , "log(x+1)(v2)");
        sverbose.decrease_depth();    
        sverbose.next_iteration();
        sverbose.increase_depth();
        for n in range(__MIN_N, __MAX_N):
            assert_initial(BesselD(n), bessel_J(n,x), _sage_const_10 , "bessel_J(%d,x)" %n);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
        for n in range(__MIN_N, __MAX_N):
            assert_initial(LegendreD(n), legendre_P(n,x), _sage_const_10 , "legendre_P(%d,x)" %n);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
        for n in range(__MIN_N, __MAX_N):
            assert_initial(ChebyshevD(n,_sage_const_1 ), chebyshev_T(n,x), _sage_const_10 , "chebyshev_T(%d,x)" %n);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
        for n in range(__MIN_N, __MAX_N):
            assert_initial(ChebyshevD(n,_sage_const_2 ), chebyshev_U(n,x), _sage_const_10 , "chebyshev_U(%d,x)" %n);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            
        sverbose.decrease_depth();    
        sverbose.decrease_depth();
        sverbose("Finished tests");
        
        sverbose("Checking built-in functions with polynomial input");
        sverbose.increase_depth();
        sverbose.start_iteration(_sage_const_8 *__DIFF, True, True);
        sverbose.increase_depth();
        for i in range(__MIN_N, __MAX_N):
            p = x*random_polynomial();
            assert_initial(Exp(p), exp(p), _sage_const_10 , "exp(%s)" %p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert_initial(Sin(p), sin(p), _sage_const_10 , "sin(%s)" %p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert_initial(Cos(p), cos(p), _sage_const_10 , "cos(%s)" %p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert_initial(Sinh(p), sinh(p), _sage_const_10 , "sinh(%s)" %p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert_initial(Cosh(p), cosh(p), _sage_const_10 , "cosh(%s)" %p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert_initial(Tan(p), tan(p), _sage_const_10 , "Tan(%s)" %p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert_initial(Log(p+_sage_const_1 ), log(p+_sage_const_1 ), _sage_const_10 , "log(%s)" %(p+_sage_const_1 ));
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert_initial(Log1(p), log(p+_sage_const_1 ), _sage_const_10 , "log(%s)(v2)" %(p+_sage_const_1 ));
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            
        sverbose.decrease_depth();    
        sverbose.decrease_depth();
        sverbose("Finished tests");
        
        sverbose("Checking composition of functions with polynomials");
        sverbose.increase_depth();
        sverbose.start_iteration(_sage_const_8 *__DIFF, True, True);
        sverbose.increase_depth();
        for i in range(__MIN_N, __MAX_N):
            p = x*random_polynomial();
            assert Exp(p) == Exp(x)(p), "Error checking the composition of 'Exp' with %s" %(p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert Sin(p) == Sin(x)(p), "Error checking the composition of 'Sin' with %s" %(p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert Cos(p) == Cos(x)(p), "Error checking the composition of 'Cos' with %s" %(p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert Sinh(p) == Sinh(x)(p), "Error checking the composition of 'Sinh' with %s" %(p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert Cosh(p) == Cosh(x)(p), "Error checking the composition of 'Cosh' with %s" %(p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert Tan(p) == Tan(x)(p), "Error checking the composition of 'Tan' with %s" %(p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert Log(p+_sage_const_1 ) == Log(x+_sage_const_1 )(p), "Error checking the composition of 'Log' with %s" %(p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            assert Log1(p) == Log1(x)(p), "Error checking the composition of 'Log'(v2) with %s" %(p);
            sverbose.decrease_depth();    
            sverbose.next_iteration();
            sverbose.increase_depth();
            
        sverbose.decrease_depth();    
        sverbose.decrease_depth();
        sverbose("Finished tests");
        
    except (Exception, KeyboardInterrupt) as e:
        sverbose.reset_depth();
        sverbose.set_deep_wrapper(__deep_wrap);
        sverbose.set_level(__PREV_LEVEL);
        print "\nError found during tests: %s" %(e);
        raise e;
        
    sverbose.decrease_depth();
    sverbose("Finished all the tests on the examples");
    t = timer() - t;
    sverbose("Example tests finished successfully --> %s" %(t));
    sverbose.set_deep_wrapper(__deep_wrap);
    sverbose.set_level(__PREV_LEVEL);

