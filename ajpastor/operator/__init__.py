r"""
Package operator

In this package the user may find the following subpackages:
* operator: basic class for linear differential operators
* listOperator: abstract class of operator based on a list structure
* oreOperator: class of operator wrapping the operators in ore_alebra
* twoStepsOperator: abstract class of listOperator that performed operations in two steps
* directStepOperator: implementation of twoStepsOperator
* lazyStepOperator: implementation of twoStepsOperator (to review)
* fullLazyOperator: implementation of twoStepsOperator with all operations lazily performed
* polynomialLazyOperator: implementation of twoStepsOperator (to review)

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

from .operator import Operator;
from .oreOperator import w_OreOperator as OreOperator;
from .directStepOperator import DirectStepOperator;
from .polynomialLazyOperator import PolynomialLazyOperator;

from pkgutil import extend_path;
__path__ = extend_path(__path__, __name__);
