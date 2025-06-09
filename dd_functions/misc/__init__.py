r"""
Package for miscellaneous functionality

In this package the user may find the following subpackages:

* :mod:`~ajpastor.misc.linear_solver`: a generic class for solving linear systems. In particular, we have two specific implementations:

    * :mod:`~ajpastor.misc.hermite`: linear solver whose echelon form is the Hermite Normal form. Useful to solve 
      inhomogeneous liner systems within an Euclidean domain. 
    * :mod:`~ajpastor.misc.bareiss`: linear solver that uses Bareiss' algorithm to perform elimination. Useful to get
      nullspaces in Integral domains.

* :mod:`~ajpastor.misc.cached_property`: implementation of a decorator to declared derived attributes of objects
* :mod:`~ajpastor.misc.dynamic_string`: implementation of an enhanced string where it can be built from different pieces
* :mod:`~ajpastor.misc.exceptions`: basic Exceptions for general use
* :mod:`~ajpastor.misc.matrix`: basic operations and utilities with matrices and differential linear algebra
* :mod:`~ajpastor.misc.ring_w_sequence`: implementation of a Ring class where their elements define a sequence
* :mod:`~ajpastor.misc.sequence_manipulation`: module with method to manipulate sequences in black-box format
* :mod:`~ajpastor.misc.serializable`: basic interface for objects that can be serialize
* :mod:`~ajpastor.misc.sets`: implementation of enumerated sets (*still in progress*)

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
from pkgutil import extend_path
__path__ = extend_path(__path__, __name__)

