r"""
Package ''misc''

In this package the user may find the following subpackages:
* ''bareiss'': an implementation of the Bareiss algorithm for getting nullspaces of matrices over Integral Domains
* ''cached_property'': implementation of a decorator to declared derived attributes of objects
* ''dynamic_string'': implementation of an enhanced string where it can be built from different pieces
* ''exceptions'': basic Exceptions for general use
* ''matrix'': basic operations and utilities with matrices and linear algebra
* ''ring_w_sequence'': implementation of a Ring class where their elements define a sequence
* ''sequence_manipulation'': module with method to manipulate sequences in black-box format
* ''verbose'': an implementation of a verbose system for debugging or control

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

