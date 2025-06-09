r"""
Package dd_functions

In this package the user may find the following subpackages:
* ddFunctions: ddFunctions and ddRings
* ddExamples: examples of DDFunctions
* symbolic: code for treating with Symbolic Expressions
* toDiffAlgebraic: include methods for treat with algebraic properties of DDFunctions
* lazyDDRing: and implementation of a DDRing with lazy elements

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

try:
    from .ddFunction import *
except Exception:
    print("Error loading module dd_functions.ddFunction")
try:
    from .ddExamples import *
except Exception:
    print("Error loading module dd_functions.ddExamples")
try:
    from .symbolic import *
except Exception:
    print("Error loading module dd_functions.symbolic")
try:
    from .toDiffAlgebraic import *
except Exception:
    print("Error loading module dd_functions.toDiffAlgebraic")
try:
    from .lazyDDRing import *
except Exception:
    print("Error loading module dd_functions.lazyDDRing")

from pkgutil import extend_path
__path__ = extend_path(__path__, __name__)

