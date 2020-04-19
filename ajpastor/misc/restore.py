"""
Python file for linear restoring the system

This module provides a bunch of methods to save and restore the state of the Python session.

EXAMPLES::
    sage: from ajpastor.misc.restore import *

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

##########################################
###
### RESTORING SESSION METHODS
###
##########################################
from ajpastor.misc.verbose import *;

## Data structure
class __SystemState(object):
    def __init__(self,global_dict, local_dict):
        self.__globals = global_dict;
        self.__locals = local_dict;
        self.__exceptions = [];
        
    @wverbose
    def add_exceptions(self,*input):
        if(len(input) == 1 and isinstance(input[0],list)):
            sverbose("Only a list gives as argument. Using it as parameter...");
            input = input[0];
        for element in input:
            if(isinstance(element, str)):
                if(element not in self.__exceptions):
                    self.__exceptions += [element];
                else:
                    sverbose("A repeated element given as exception");
            else:
                sverbose("A non-string element given as exception. Skipping it...");
    
    @wverbose
    def remove_exceptions(self,*input):
        if(len(input) == 1 and isinstance(input[0],list)):
            sverbose("Only a list gives as argument. Using it as parameter...");
            input = input[0];
        for element in input:
            if(isinstance(element, str)):
                if(element in self.__exceptions):
                    self.__exceptions.remove(element);
                else:
                    sverbose("A non-existing element given as exception");
            else:
                sverbose("A non-string element given as non-exception. Skipping it...");
                
    def _restore_from_local(self,other_dict):
        if(self.__locals is not None):
            self.__restore_dictionary(other_dict, self.__locals);
    
    def _restore_from_global(self,other_dict):
        self.__restore_dictionary(other_dict, self.__globals);
        
    def __restore_dictionary(self, target, source):
        if(target is not None and source is not None):
            if(isinstance(target, dict), isinstance(source, dict)):
                ## Deleting the new variables (except those that are exceptions)
                keys = [el for el in target];
                for key in keys:
                    if(not key in self.__exceptions):
                        if(not key in source):
                            del target[key];
                ## Restoring the old variables (except those that are exceptions)
                keys = [el for el in target];
                for key in keys:
                    if(not key in self.__exceptions):
                        target[key] = source[key];
                        
    def __repr__(self):
        n = 1;
        if(self.__locals is not None):
            n = 2;
        return "Dictionary state with %d dictionaries" %n;
        
    def __str__(self):
        res = repr(self);
        if(len(self.__exceptions) > 0):
            res += "\n  - Exceptions: %s" %self.__exceptions;
        
        return res;
                
                
## Main functions
def get_state(global_dict, local_dict = None):
    '''
        Method that save the current state of the program. It gets two dictionaries that are 
        considered the global and the local variables.
        
        There are two recommended usages of this function:
            - get_state(globals(),locals()): save the state of the global and the local variables
            - get_state(globals()): only consider the global variables.
            
        Also other dictionaries can be given, and then they state will be saved.    
    '''
    ## Checking arguments
    if(not isinstance(global_dict, dict)):
        raise TypeError("The global argument must be a dictionary");
    if((not (local_dict is None)) and (not isinstance(local_dict, dict))):
        raise TypeError("The local argument must be None or a dictionary");
    
    ## Returning the saved state
    local_copy = None;
    if(local_dict is not None):
        local_copy = local_dict.copy();
    return __SystemState(global_dict.copy(), local_copy);
    
def restore_state(state, global_dict, local_dict=None):
    '''
        Restore a saved state to the dictionaries given as arguments. It considers the first 
        (required) as global variables and the second (optional) as the local variables.
        
        There are two recommended usages of this function:
            - restore_state(state,globals(),locals()): restore the state of the global and the local variables
            - restore_state(state,globals()): only restore the global variables.
            
        Also other dictionaries can be given, and they will be restore to the state saved.
    '''
    ## Checking arguments
    if(not isinstance(global_dict, dict)):
        raise TypeError("The global argument must be a dictionary");
    if((not (local_dict is None)) and (not isinstance(local_dict, dict))):
        raise TypeError("The local argument must be None or a dictionary");
    if(not isinstance(state, __SystemState)):
        raise TypeError("The state argument must be a value obtained by 'get_state' method");
    
    if(local_dict is not None):
        state._restore_from_local(local_dict);
    state._restore_from_global(global_dict);
        
    
## Package variables
__all__ = ["get_state", "restore_state"];
