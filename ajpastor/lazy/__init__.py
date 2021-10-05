r"""
Package lazy

In this package the user may find the following subpackages:
* conversion: definition of a ConversionSystem
* lazyToPoly: conversion system based on a variable Polynomial Ring
* lazyRing: conversion system based on a ring using the basics of lazyToPoly
* lazyIDElements: the element class for lazyRing
* lazyFracField: conversion system based on a Fraction Field using the basics of lazyToPoly

TODO::
    * Review the import statements of this package

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

from .lazyToPoly import LazyToPoly

from pkgutil import extend_path
__path__ = extend_path(__path__, __name__)
