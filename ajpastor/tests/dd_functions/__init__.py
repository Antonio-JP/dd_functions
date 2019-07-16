r"""
Package dd_functions

This package provides the tests for the package ajpastor.dd_functions. The user can run all the tests in a row
using the provided function ``run`` in this package. Otherwise, the user must import each of the modules and execute
the ``run``method on each of them.

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

def run():
    __LIST_OF_FILES = ["ddFunction", "ddFunction2", "examples", "identities", "hypergeometric", "chebyshev", "bessel"];
    
    import importlib;
    for file_name in __LIST_OF_FILES:
        module = importlib.import_module(__package__+"."+file_name);
        print '###############################################################################'
        print "### Testing file %s" %file_name;
        module.run();
        print '###############################################################################'    
