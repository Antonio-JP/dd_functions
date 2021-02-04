r"""
Python file for implementing enumerated sets

This module offers several functionalities to handle sets that are enumerated with a
countable parameter. This is an extension of the ideas from the Sage category
:class:`~sage.categories.enumerated_sets.EnumeratedSets` in order to fit
the utilities and features required on this package.

AUTHORS:

    - Antonio Jimenez-Pastor (2021-02-04): initial version

TODO:
    * Implement the classes for these sets
    * Implement the union of these sets
    * Implement a nice printing for these sets
    * Implement the methods:
        - ``cardinality``
        - ``iter``
        - ``list``
        - ``rank``
        - ``first``
        - ``next``
        - ``random_element``
"""

# ****************************************************************************
#  Copyright (C) 2021 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************
class EnumeratedSet():
    pass

class FiniteEnumeratedSet(EnumeratedSet):
    pass

class EmptySet(FiniteEnumeratedSet):
    pass

class InfiniteEnumeratedSet(EnumeratedSet):
    pass

class UnionEnumeratedSet(EnumeratedSet):
    pass