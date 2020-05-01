r"""
Python file for general exceptions

This module offers several Exceptions for general purposes.

EXAMPLES::
    sage: from ajpastor.misc.exceptions import *
    sage: raise DebugError("testing error")
    Traceback (most recent call last):
    ...
    DebugError: Debug Error found (testing error): we are working in fixing it. Please be patient.
    FIXING TIME!

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

class DebugError(RuntimeError):
    r'''
        Error meaning an unexpected error in the code. Future versions should fix it.
    '''
    def __init__(self, message):
        super(DebugError, self).__init__("Debug Error found (%s): we are working in fixing it. Please be patient.\nFIXING TIME!" %message)
