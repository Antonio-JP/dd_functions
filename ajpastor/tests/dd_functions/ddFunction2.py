r"""
Python file for a tests using DDFunctions

This module test the construction of DDRings.

EXAMPLES::
    sage: from ajpastor.tests.dd_functions.ddFunction2 import *

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

_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_9 = Integer(9); _sage_const_0 = Integer(0)
import sys, traceback, warnings;
from timeit import default_timer as timer;

from ajpastor.misc.verbose import *;
from ajpastor.dd_functions import *;
from ajpastor.dd_functions.ddFunction import DDFunctionWarning;

def run():
    __LEVEL = -_sage_const_2 ; ## Verbose level (-2 print loops, -1 print test, 0 print global data, greater print nothing
    __PREV_LEVEL = sverbose.get_level();

    ##########################################
    ### AUXILIARY FUNCTIONS
    ##########################################
    def assert_initial(func, symbolic, size, name):
        for i in range(size):
            func_val = func.init(i);
            real_val = symbolic.derivative(i)(x=_sage_const_0 );
            assert (func_val == real_val), "Error in the %d initial value of the function %s: expected %s but got %s"%(i,name,real_val,func_val);

    ####################################################################################

    sverbose.set_level(__LEVEL);
    __deep_wrap = sverbose.get_deep_wrapper();
    sverbose.set_deep_wrapper(-__LEVEL);
    sverbose("Running advanced tests over the implementation of DDRings and their functions");
    sverbose("");
    sverbose("Author: Antonio Jimenez");
    sverbose("Date: 14-02-2018");
    sverbose("");
    sverbose.increase_depth();
              

    ##Starting execution
    warnings.simplefilter('ignore',DDFunctionWarning);
    t = timer();
    #########################################
    ### TESTS FOR STRUCTURES DDRing and DDFunction
    #########################################
    try:
        
        ## Creation for the DDRing get the same object
        sverbose("Test for checking the uniqueness of DDRings");
        sverbose.increase_depth();
        sverbose("Iteration vs. Direct");
        assert DDRing(DDFinite) is DDRing(PolynomialRing(QQ,x), depth=_sage_const_3 ), "Error building DDRing. Not uniqueness detected from iteration against the direct step";
        assert DDRing(DFinite, depth=_sage_const_2 ) is DDRing(PolynomialRing(QQ,x), depth=_sage_const_3 ), "Error building DDRing. Not uniqueness detected from a semi-direct step against the direct step";
        
        sverbose("P. DDRings with Symbols vs. P. DDRings with strings");
        assert ParametrizedDDRing(DFinite, 'a') is ParametrizedDDRing(DFinite, var('a')), "Error building parameters. Not uniqueness from string or symbol";
        
        sverbose("Order on the parameters");
        assert ParametrizedDDRing(DFinite, ['a','q']) is ParametrizedDDRing(DFinite, ['q', 'a']), "Error building parameters. Not uniqueness with the order of parameters";
        
        sverbose("Adding parameters vs. Create parameters");
        assert ParametrizedDDRing(DFinite, ['a','q']) is ParametrizedDDRing(ParametrizedDDRing(DFinite, 'a'), 'q'), "Error building parameters. Not uniqueness adding variables instead of creating them";
        
        sverbose("Checking repeated parameters");
        assert ParametrizedDDRing(ParametrizedDDRing(DFinite, 'a'), 'a') is ParametrizedDDRing(DFinite, 'a'), "Error building parameters. Not uniqueness when adding the same parameter";
        assert ParametrizedDDRing(DFinite, ['a', 'q']) is ParametrizedDDRing(ParametrizedDDRing(DFinite, 'a'), ['a', 'q']), "Error building parameters. Not uniqueness when adding some repeated parameters";
        
        sverbose("Checking depth with parameters");
        assert ParametrizedDDRing(DDFinite, ['a','q']).base() is ParametrizedDDRing(DFinite, ['a','q']), "Error building parameters. Not uniqueness in P(DD,var).base() and P(D,var)";
        assert ParametrizedDDRing(DDFinite, 'P').base() is DFiniteP, "Error building parameters. Not uniqueness in P(DD,var).base() and P(D,var)";
        sverbose.decrease_depth();
        
        sverbose("Testing pushouts for parameters with D(QQ[x])");
        sverbose.increase_depth();
        sverbose.start_iteration(_sage_const_9 , True, True);
        
        from sage.categories.pushout import pushout;
        DDFiniteP = ParametrizedDDRing(DDFinite, 'P');
        DDFiniteA = ParametrizedDDRing(DDFinite, 'a');
        DFiniteA = DDFiniteA.base();
        DDFiniteQ = ParametrizedDDRing(DDFinite, 'q');
        DFiniteQ = DDFiniteQ.base();
        DDFiniteAQ = ParametrizedDDRing(DDFinite, ['a','q']);
        DFiniteAQ = DDFiniteAQ.base();
        DDFiniteAP = ParametrizedDDRing(DDFinite, ['a','P']);
        DFiniteAP = DDFiniteAP.base();
        DDFiniteAQP = ParametrizedDDRing(DDFinite, ['a','q','P']);
        DFiniteAQP = DDFiniteAQP.base();
        
        assert DFiniteP is pushout(DFinite, DFiniteP), "Error in pushouts: D - D(P) -- D(P)";
        sverbose.next_iteration();
        assert DDFiniteP is pushout(DFinite, DDFiniteP), "Error in pushouts: D - DD(P) -- DD(P)";
        sverbose.next_iteration();
        assert DDFiniteP is pushout(DDFinite, DFiniteP), "Error in pushouts: DD - D(P) -- DD(P)";
        sverbose.next_iteration();
        assert DDFiniteAQ is pushout(DDFiniteA, DDFiniteQ), "Error in pushouts: DD(a) - DD(q) -- DD(a,q)";
        sverbose.next_iteration();
        assert DDFiniteAQ is pushout(DFiniteA, DDFiniteQ), "Error in pushouts: D(a) - DD(q) -- DD(a,q)";
        sverbose.next_iteration();
        assert DDFiniteAQ is pushout(DFiniteA, DDFiniteAQ), "Error in pushouts: D(a) - DD(a,q) -- DD(a,q)";
        sverbose.next_iteration();
        assert DFiniteAQ is pushout(DFiniteA, DFiniteQ), "Error in pushouts: D(a) - D(q) -- D(a,q)";
        sverbose.next_iteration();
        assert DDFiniteAQP is pushout(DFiniteP, DDFiniteAQ), "Error in pushouts: D(p) - DD(a,q) -- DD(a,q,P)";
        sverbose.next_iteration();
        assert DDFiniteAQP is pushout(DFiniteAP, DDFiniteAQ), "Error in pushouts: D(a,P) - D(a,q) -- D(a,q,P)";
        sverbose.next_iteration();
        sverbose.decrease_depth();
        
    except (Exception, KeyboardInterrupt) as e:
        sverbose.reset_depth();
        sverbose.set_deep_wrapper(__deep_wrap);
        sverbose.set_level(__PREV_LEVEL);
        print("\nError found during tests: %s" %(e));
        raise e;
        
    sverbose.decrease_depth();
    sverbose("Finished all the advanced tests");
    t = timer() - t;
    sverbose("Advanced tests finished successfully --> %s" %(t));
    warnings.simplefilter('always',DDFunctionWarning);
    sverbose.set_deep_wrapper(__deep_wrap);
    sverbose.set_level(__PREV_LEVEL);

