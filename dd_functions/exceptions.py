r'''
    Module for exceptions related with the `dd_functions` package.

    This moduel provide simple implementations and names for specific errors for the module `dd_functions` with specific semantics.

    AUTHORS::

        - Antonio Jimenez-Pastor (2025-06-11): initial version

'''

# ****************************************************************************
#  Copyright (C) 2025 Antonio Jimenez-Pastor <antonio.jimenezp@upm.es>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

### Exception for Future implementation
class ToBeImplementedError(NotImplementedError):
    r'''
        Exception raised when a feature is not implemented yet.
    
        This exception is used to indicate that a certain functionality or method
        is planned for future implementation but is not available in the current version.
    '''
    def __init__(self, message="This feature is planned for future implementation."):
        super().__init__(message)

### Exception for the case where univariate operators are needed
class NotUnivariateError(TypeError):
    r'''
        Exception raised when a univariate operator is expected but a multivariate one is provided.
    
        This exception is used to indicate that the operation requires a univariate operator,
        but the provided operator is multivariate.
    '''
    def __init__(self, message="This operation requires a univariate operator."):
        super().__init__(message)

### Exception for the case when an algorithm requires a field to compute properly
class FieldRequiredError(TypeError):
    r'''
        Exception raised when a field is required for an algorithm to compute properly.
    
        This exception is used to indicate that the algorithm cannot proceed without a specified field.
    '''
    def __init__(self, message="This algorithm requires a field to compute properly."):
        super().__init__(message)