r"""
Python file for a tests the DDFunctions

This module test the basic properties and methods of DDFunctions.

EXAMPLES::
    sage: from ajpastor.tests.dd_functions.ddFunction import *

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

_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_0 = Integer(0); _sage_const_6 = Integer(6); _sage_const_4 = Integer(4); _sage_const_8 = Integer(8); _sage_const_10 = Integer(10); _sage_const_16 = Integer(16); _sage_const_32 = Integer(32)
import sys, traceback;
from timeit import default_timer as timer;

from ajpastor.misc.verbose import *;
from ajpastor.dd_functions import *;


def run():
    __LEVEL = -_sage_const_2 ; ## Verbose level (-2 print loops, -1 print test, 0 print global data, greater print nothing
    __PREV_LEVEL = sverbose.get_level();

    ##########################################
    ### AUXILIARY FUNCTIONS
    ##########################################
    def assert_initialValues(func, values, name):
        for i in range(len(values)):
            aux = func.init(i);
            assert (aux == values[i]), "Error in the %d initial value of the function %s: expected %s but got %s"%(i,name,values[i],aux);

    def assert_coefficients(func, values, name):
        aux = func.equation.coefficients()
        assert (aux == values), "Error in the coefficients of the function %s: expected %s but got %s"%(name,values,aux);  

    ####################################################################################

    sverbose.set_level(__LEVEL);
    __deep_wrap = sverbose.get_deep_wrapper();
    sverbose.set_deep_wrapper(-__LEVEL);
    sverbose("Running basic tests over the implementation of DDRings and their functions");
    sverbose("");
    sverbose("Author: Antonio Jimenez");
    sverbose("Date: 12-02-2018");
    sverbose("");
    sverbose.increase_depth();
              

    ##Starting execution
    t = timer();
    #########################################
    ### TESTS FOR STRUCTURES DDRing and DDFunction
    #########################################
    try:
        
        _aux = None;    # Auxiliar variable for useless assigments
        
        ## Creation and Initial Values tests
        sverbose("Test for creation and initial values computation");
        sin = Sin(x);
        assert_coefficients(sin, [_sage_const_1 ,_sage_const_0 ,_sage_const_1 ], 'sin');
        assert_initialValues(sin, [_sage_const_0 , _sage_const_1 , _sage_const_0 , -_sage_const_1 , _sage_const_0 , _sage_const_1 ], 'sin');

        # Inhomogeneous tests
        sverbose("Test for inhomogeneous creation of elements");
        b = DFinite.element([_sage_const_1 ], inhomogeneous = x**_sage_const_3 +_sage_const_1 )
        assert_coefficients(b, [-_sage_const_3 *x**_sage_const_2 ,(x**_sage_const_3 +_sage_const_1 )], '3x^2 + 1');

        # Differential tests
        sverbose("Test for constant checking");
        a=DFinite.element([_sage_const_0 ,_sage_const_1 ], [_sage_const_1 ]);
        assert_initialValues(a, [_sage_const_1 ,_sage_const_0 ,_sage_const_0 ,_sage_const_0 ,_sage_const_0 ,_sage_const_0 ], 'constant=1');

        #Derivation
        sverbose("Test for derivation of elements");
        _aux = a.derivative();
        assert_coefficients(_aux, [_sage_const_0 ,_sage_const_1 ], 'constant=0');
        assert_initialValues(_aux, [_sage_const_0 ,_sage_const_0 ,_sage_const_0 ,_sage_const_0 ,_sage_const_0 ,_sage_const_0 ], 'constant=0');

        cos = sin.derivative();
        assert_coefficients(cos, [_sage_const_1 ,_sage_const_0 ,_sage_const_1 ], 'cos');
        assert_initialValues(cos, [_sage_const_1 , _sage_const_0 , -_sage_const_1 , _sage_const_0 , _sage_const_1 , _sage_const_0 ], 'cos');

        #Integration
        sverbose("Test for integration of elements");
        _aux = a.integrate();
        assert_coefficients(_aux, [_sage_const_0 ,_sage_const_0 ,_sage_const_1 ], 'x');
        assert_initialValues(_aux, [_sage_const_0 ,_sage_const_1 ,_sage_const_0 ,_sage_const_0 ,_sage_const_0 ,_sage_const_0 ], 'x');

        _aux = sin.integrate(-_sage_const_1 );
        assert_coefficients(_aux, [_sage_const_0 ,_sage_const_1 ,_sage_const_0 ,_sage_const_1 ], '-cos');
        assert_initialValues(_aux, [-_sage_const_1 , _sage_const_0 , _sage_const_1 , _sage_const_0 , -_sage_const_1 , _sage_const_0 ], '-cos');

        # Summation, multiplication and scalar tests
        # Summation
        sverbose("Test for addition of elements (exp(x) + exp(x))");
        e = Exp(x);
        _aux = e.add(e)
        assert_coefficients(_aux, [-_sage_const_1 ,_sage_const_1 ], '2exp(x)');
        assert_initialValues(_aux, [_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ], '2exp(x)');

        #Multiplication
        sverbose("Test for product of elements (exp(x) * exp(x))");
        _aux = e.mult(e)
        assert_coefficients(_aux, [-_sage_const_2 ,_sage_const_1 ], 'exp(2x)');
        assert_initialValues(_aux, [_sage_const_1 ,_sage_const_2 ,_sage_const_4 ,_sage_const_8 ,_sage_const_16 ,_sage_const_32 ], 'exp(2x)');

        #Scalar
        sverbose("Test for scalar product of elements (6*exp(x))");
        _aux = e.scalar(_sage_const_6 )
        assert_coefficients(_aux, [-_sage_const_1 ,_sage_const_1 ], '6exp(x)');
        assert_initialValues(_aux, [_sage_const_6 ,_sage_const_6 ,_sage_const_6 ,_sage_const_6 ,_sage_const_6 ,_sage_const_6 ], '6exp(x)');

        # Zero and Equality methods
        # Simple equalities (f == f)
            # f == f
        sverbose("Test for equality 1 (reflexiveness)");
        assert e.equals(e), "Error with self-equality";

            # 2*f == f+f
        sverbose("Test for equality 2 (exp(x)+exp(x) == 2*exp(x))");
        assert e.add(e).equals(e.scalar(_sage_const_2 )), "Error with the equality 2e == e+e";

            # Different representations
        sverbose("Test for equality 3 (same function with different representations)");
        _aux = DFinite.element([_sage_const_0 ,_sage_const_0 ,_sage_const_1 ,-_sage_const_1 ], [_sage_const_1 ,_sage_const_1 ,_sage_const_1 ]);
        assert e.equals(_aux), 'Error with the equality from different representations for same function';

            #sin^2+cos^2 = 1
        sverbose("Test for equality 4 (cos^2(x)+sin^2(x) == 1)");
        unity = DFinite(_sage_const_1 );
        assert unity.equals(sin.mult(sin).add(cos.mult(cos))), 'Error with sin^2 + cos^2 == 1 using basic operations';

            #sin(2x) = 2sin(x)cos(x)
        sverbose("Test for equality 5 (sin(2x) == 2sin(x)cos(x))");
        sin2 = DFinite.element([_sage_const_4 ,_sage_const_0 ,_sage_const_1 ], [_sage_const_0 ,_sage_const_2 ]);
        assert sin2.equals(sin.mult(cos).scalar(_sage_const_2 )), 'Error with sin(2x) == 2sin(x)cos(x) using basic operations';

            #cos(2x) = cos^2(x)-sin^2(x)
        sverbose("Test for equality 6 (cos(2x) = cos^2(x)-sin^2(x))");
        cos2 = DFinite.element([_sage_const_4 ,_sage_const_0 ,_sage_const_1 ], [_sage_const_1 ,_sage_const_0 ]);
        assert cos2.equals(cos.mult(cos).sub(sin.mult(sin))), 'Error with cos(2x) == cos^2(x)-sin^2(x) using basic operations';

        # Python user friendly methods tests
        sverbose("Test for magic Python methods");
        sverbose.increase_depth();
        # Object methods
        try:
            b[-_sage_const_1 ];
            assert False, "Error getting position (-1). Previously, this meant inhomogeneous term. Now is nothing."
        except IndexError:
            pass;
        # Python user friendly methods tests
        sverbose("Direct arithmetic");
        _aux = DFinite.element([x,-_sage_const_1 ],[_sage_const_1 ]);
        assert (-sin).equals(sin.scalar(-_sage_const_1 )), 'Error checking unary -';
        assert (sin+_aux).equals(sin.add(_aux)), 'Error checking + for DFinite';
        assert (cos-e).equals(cos.sub(e)), 'Error checking - for DFinite';
        assert (sin*sin).equals(sin.mult(sin)), 'Error checking * for DFinite';
        assert (sin**_sage_const_2 ).equals(sin.mult(sin)), 'Error checking ** with value 2 for DFinite';
        assert DFinite(_sage_const_1 ).equals(sin**_sage_const_0 ), 'Error checking ** with value 0 for DFinite';
        assert (cos**_sage_const_3 ).equals(cos.mult(cos.mult(cos))), 'Error checking ** with value 3 for DFinite';
        try:
            aux = sin**cos;
            assert False, "Error catching a NotImplementedError for method __pow__";
        except (NotImplementedError, TypeError):
            pass;
        try:
            aux = pow(sin, -_sage_const_3 );
            assert False, "Error catching a ZeroDivisionError for method __pow__";
        except ZeroDivisionError:
            pass;
            
        sverbose("In-place arithmetic");
        inPlace = sin;
        inPlace += e;
        assert inPlace.equals(sin+e), 'Error checking inplace + for DFinite';
        inPlace = sin;
        inPlace -= cos;
        assert inPlace.equals(sin-cos), 'Error checking inplace - for DFinite';
        inPlace = cos;
        inPlace *= sin;
        assert inPlace.equals(sin.mult(cos)), 'Error checking inplace * for DFinite';
        inPlace = sin;
        inPlace **= _sage_const_2 ;
        inPlace += cos**_sage_const_2 ;
        assert inPlace.equals(DFinite(_sage_const_1 )), 'Error checking implace ** for DFinite';
        
        sverbose("Python equality (==)");
        assert (sin**_sage_const_2 +cos**_sage_const_2  == _sage_const_1 ), 'Error checking equality sin^2+cos^2 == 1';
        assert (not (cos2 == (sin*cos).scalar(_sage_const_2 ))), 'Error checking the inequality cos(2x) != 2sin(x)cos(x)';
        assert (sin2 == (sin*cos).scalar(_sage_const_2 )), 'Error checking equality sin(2x) = 2sin(x)cos(x)';
        assert (cos2 == cos**_sage_const_2 -sin**_sage_const_2 ), 'Error checking equality cos(2x) == cos^2(x)+sin^2(x)';
        _aux=DFinite(_sage_const_3 *x**_sage_const_2 +x+_sage_const_1 );
        assert (_aux.derivative() == _sage_const_6 *x+_sage_const_1 ), 'Error checking equality D(3x^2+x+1) == 6x+1';
        sverbose.decrease_depth();
        
        sverbose("Test over initial values required");
        # Impossible get initial values -- Giving more than expected
        try:
            f1 = DFinite.element([-_sage_const_4 *x**_sage_const_3 ,_sage_const_1 ,-x], [_sage_const_0 ,_sage_const_0 ,_sage_const_2 ]);
            f2 = DFinite.element([-_sage_const_1 -x,x], [_sage_const_0 ,_sage_const_1 ]);
            f1*f2;
        except Exception:
            assert False, "Error with DD-Function with more initial values than needed";

        # Impossible get initial values -- Giving less than expected
        _aux = DFinite.element([x,-_sage_const_1 ]);
        _aux = e*_aux;
        assert_coefficients(_aux, [-(x+_sage_const_1 ),_sage_const_1 ], 'e^x*e^(-x^2/2)');
        assert (_aux.init(_sage_const_10, True) == []), "Error getting initial values: expected [] but got %s"%(_aux.init(_sage_const_10, True));
    except (Exception, KeyboardInterrupt) as e:
        sverbose.reset_depth();
        sverbose.set_deep_wrapper(__deep_wrap);
        sverbose.set_level(__PREV_LEVEL);
        print("Error found during tests: %s" %(e));
        raise e;
        
    sverbose.decrease_depth();
    sverbose("Finished all the basic tests");
    t = timer() - t;
    sverbose("Basic tests finished successfully --> %s" %(t));
    sverbose.set_deep_wrapper(__deep_wrap);
    sverbose.set_level(__PREV_LEVEL);

