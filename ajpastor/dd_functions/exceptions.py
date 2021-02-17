r"""
    Python file for exceptions in the package dd_functions

    This file contains all the different exceptions that we need in the computations
    with DDFunctions and similar structures. These exceptions allows a better control
    of the errors through the package.

    These exceptions are available publicly, but need to be imported explicitly (i.e.,
    these exception are not directly imported with the package ``ajpastor.dd_function``)

    EXAMPLES::

        sage: from ajpastor.dd_functions.exceptions import *
        sage: raise InitValueError("error with initial values")
        Traceback (most recent call last):
        ...
        InitValueError: error with initial values
        sage: raise ZeroValueRequired()
        Traceback (most recent call last):
        ...
        ZeroValueRequired: required a zero value

    AUTHORS:

        - Antonio Jimenez-Pastor (2020-05-01): initial version

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

class InitValueError(ValueError):
    r'''
        Exception due to an error in initial values of a DDFunction

        This error is provoke because a DDFunction needs a different type
        of initial condition that the one given. This could be because
        the user is imposing an impossible value for a derivative, an 
        unexpected error on computations or composing two DDFunctions with
        incompatible initial conditions.

        TODO:
            * Look and substitute for this error
    '''
    pass

class ZeroValueRequired(InitValueError):
    r'''
        Particular exception for requiring a zero initial condition.

        This error is a particular case of :class:`InitValueError` (see its documentation
        for further information) where the problem is that `0` was required as the
        first initial condition.

        Two different type of errors can be build: with one or two arguments. The 
        message is adapted to the type of error.

        EXAMPLE::

            sage: from ajpastor.dd_functions.exceptions import ZeroValueRequired
            sage: raise ZeroValueRequired()
            Traceback (most recent call last):
            ...
            ZeroValueRequired: required a zero value
            sage: raise ZeroValueRequired("f(x)")
            Traceback (most recent call last):
            ...
            ZeroValueRequired: required a zero value for f(x)
            sage: raise ZeroValueRequired("f(x)", "cos(f(x))")
            Traceback (most recent call last):
            ...
            ZeroValueRequired: required a zero value for f(x) in cos(f(x))
            sage: raise ZeroValueRequired("f(x)", "cos(f(x))", "useless argument")
            Traceback (most recent call last):
            ...
            ZeroValueRequired: required a zero value for f(x) in cos(f(x))

        TODO:
            * Look and substitute for this error
    '''
    def __init__(self, *args):
        if(len(args) == 0):
            super(ZeroValueRequired, self).__init__("required a zero value")
        elif(len(args) == 1):
            super(ZeroValueRequired, self).__init__("required a zero value for %s" %args[0])
        else:
            super(ZeroValueRequired, self).__init__("required a zero value for %s in %s" %(args[0], args[1]))

class NoValueError(TypeError):
    r'''
        Error when computing initial values.

        Whenever a :class:`~ajpastor.dd_functions.ddFunction.DDFunction` can not compute
        an initial value, this type of exception is raised, distinguishing it from other
        Python errors.
    '''
    def __init__(self, n):
        super(NoValueError,self).__init__("Impossible to compute recursively the %s-th coefficient" %(n))

class DDFunctionError(Exception):
    r'''
        Generic error for the package ``dd_functions``.

        This error has no specific value but allows to control errors within the package.
        Use the message argument to convey specific meanings to the exception.
    '''
    pass