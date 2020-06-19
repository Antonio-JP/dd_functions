r"""
Python file for general exceptions

This module offers several Exceptions for general purposes.

EXAMPLES::
    sage: from ajpastor.misc.exceptions import *

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

class DebugError(RuntimeError):
    '''
        Error meaning an unexpected error in the code. Future versions should fix it.
    '''
    def __init__(self, message):
        RuntimeError.__init__(self, "Debug Error found (%s): we are working in fixing it. Please be patient.\nFIXING TIME!" %message)
