r"""
Python file for a dynamic string

This module offers an implementation of a class (DinamicString) that behaves like a string 
but can be built using different common pieces so it is possible to perform simultaneos
substitutions on the string.

EXAMPLES::
    sage: from ajpastor.misc.dinamic_string import *

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

################################################################################
### Class DinamicString
class DinamicString(object):

    ### Static methods and elements
    @staticmethod
    def is_string(obj):
        '''Method that check if `obj` is str or DinamicString'''
        return type(obj) == str or isinstance(obj, DinamicString)
        
    @staticmethod
    def is_list(obj):
        '''Method that check if `obj` is list, set or tuple'''
        return type(obj) == list or type(obj) == tuple or type(obj) == set

    ### Initialization methods
    def __init__(self, template, arguments, escape="_"):
        '''
            Initialization of a DinamicString. This method checks that all the arguments are correct.
            
            INPUT:
                - template: a string (type(template) == str) with the basic text of the DinamicString.
                - arguments: the arguments for this DinamicString. They will be replace in the positions of 'template' with 'escape' characters.
                    'arguments' can be a single string or DinamicString or a list of them.
                - escape: main escape character. This character followed by the number i will be use to replace in 'template' the string given by 'arguments[i]'.
                
            OUTPUT:
                - Can raise a TypeError if 'template' is not a string.
                - Can raise a TypeError if 'escape' is not a string or a character.
                - Can raise a TypeError if the elements in 'arguments' are not strings.
        '''
        ## Assign template and escape
        if(not (type(template) == str)):
            raise TypeError("The template argument must be of type 'str'. Received: %s" %(type(template)))
        self.__template = template
        if(not (type(escape) == str or type(escape) == chr)):
            raise TypeError("The escape character must be of type 'str' or 'chr'. Received %s" %(type(escape)))
        self.__escape = escape
        
        ## Checking the arguments for the string
        self.__arguments = None
        if(DinamicString.is_string(arguments)):
            self.__arguments = [arguments]
        elif(DinamicString.is_list(arguments)):
            self.__arguments = list(arguments)
        if(any(not DinamicString.is_string(el) for el in self.__arguments)):
            raise TypeError("No valid arguments for a DinamicString: only strings and DinamicStrings are valid.")
        
        ## Computing the first representation of the DinamicString
        self.__real = None
        self.real()
        
    ### Getters and setters
    def real(self):
        '''
            Get the current representation of the DinamicString. This method replace simultaneously the patters "'escape'i" for the string in 'arguments[i]'.
            
            This is a cached method: calling it several times in row returns the same string directly. To reset the string, call the method 'change_argument'.
        '''
        if(self.__real is None):
            self.__real = din_m_replace(self.__template, {"%s%d" %(self.__escape, i+1) : str(self.__arguments[i]) for i in range(len(self.__arguments))})
        
        return self.__real
        
    def change_argument(self, new_argument, index=0):
        '''
            Method to change the arguments of the DinamicString. This method has two different syntaxes:
                - 'self.change-argument(self, list)' will change completely the arguments of 'self' to the new list.
                - 'self.change_argument(self, element, index)' will change only the ith argument to element.
            
            In any case, this method reset the variable self.__real, so the method self.real() will recompute the final string.
            
            INPUT:
                - new_argument: a list or a string or a DinamicString. Depending of the type of the parameter, this method will perform different actions (see above).
                - index: in case 'new_argument' is not a list, this will be the index of the argument to change.
                
            OUTPUT:
                - Can raise a TypeError exception if 'new_argument' is not a list nor a string.
                - Can raise a IndexError exception if 'index' is not valid for 'self.__arguments'.
        '''
        if(DinamicString.is_list(new_argument)):
            self.__arguments = list(new_argument)
        elif(DinamicString.is_string(new_argument)):
            self.__arguments[index] = new_argument
        else:
            raise TypeError("The argument 'new_argument' must be a list or a 'str' o a DinamicString")
            
        self.__real = None
        
    ### Implementation of 'str' methods
    def replace(self, pattern, out, deep=False):
        '''
            Method equivalent to the replace method of the 'str' class but using DinamicString 
            in order to have an improved representation of the strings.
            
            See documentation 'str.replace?'.
            
            INPUT:
                - pattern: the string we want to change in 'self'.
                - out: the new string to put where 'pattern' is found.
                - deep: deep=True implies only replacements in the arguments of 'self' will be performed. Otherwise, we will also change the template.
                
            OUTPUT:
                - A new DinamicString such that 'result.real() == self.real().replace(pattern, str(out))'.
        '''
        new_arguments = [din_replace(el, pattern,out, deep) for el in self.__arguments]
        new_template = self.__template
        if(not deep):
            new_template = new_template.replace(pattern, out)
            
        return DinamicString(new_template, new_arguments, self.__escape)
    
    ### Extra methods
    def m_replace(self, to_replace, deep=False):
        '''
            Method to perform several replacements simultaneously. This method do exactly the same as 'self.replace(key, value) for all (key,value) in to_replace but all at once.
            
            INPUT:
                - to_replace: dictionary with the pairs (pattern, out) to replace in 'self'.
                - deep: deep=True implies only replacements in the arguments of 'self' will be performed. Otherwise, we will also change the template.
                
            OUTPUT:
                - A new DinamicString where all the appearances of the keys of 'to_replace' have been changed to their values.
        '''
        new_arguments = [din_m_replace(el, to_replace, deep) for el in self.__arguments]
        new_template = self.__template
        if(not deep):
            new_template = din_m_replace(new_template, to_replace, False)
            
        return DinamicString(new_template, new_arguments, self.__escape)
        
    ### Magic Python methods
    def __repr__(self):
        '''Magic Python 'repr' implementation'''
        return self.real()
        
    def __str__(self):
        '''Magic Python 'str' implementation'''
        return self.real()
        
    def __getitem__(self, key):
        '''Magic Python implementation for 'self[key]' ''' 
        return self.real()[key]
        
    ## Implementing concatenation
    def __add__(self, other):
        '''Magic Python implementation for '+' (i.e. concatenation)'''
        if(type(other) == str):
            return str(self) + other
        elif(isinstance(other, DinamicString)):
            ## Changing arguments of other
            other_template = din_m_replace(other.__template, {"%s%d" %(other.__escape, i) : "%s%d" %(self.__escape, i+len(self.__arguments)) for i in range(len(other.__arguments))})
            
            return DinamicString(self.__template + other_template, self.__arguments + other.__arguments)
            
        return NotImplemented
    
    def __radd__(self, other):
        '''Magic Python implementation for '+' (i.e. concatenation)'''
        if(type(other) == str):
            return other + str(self)
        elif(isinstance(other, DinamicString)):
            return other.__add__(self)
            
        return NotImplemented

################################################################################
################################################################################
################################################################################
### Utility methods combining 'str' and DinamicString
    
def din_replace(element, pattern, out, deep=False):
    '''
        Enhaced 'replace' method. This function is equivalent to the 'replace' method of
        the 'str' class when both element and out are strings.
        
        This method combines the string functionality with the new DinamicString class.
        
        INPUT:
            - element: 'str' or DinamicString where we want to replace 'pattern'.
            - pattern: 'str' with the pattern to replace in 'element'.
            - out: 'str' or DinamicString that will be put in the places where 'pattern' appears in 'element'.
            - deep: in case 'element' is a DinamicString, deep=True implies the replacement is only performed in the arguments. Otherwise this argument is irrelevant.
            
        OUTPUT:
            If 'element' and 'out' are of type 'str', this method return a new 'str' equivalent
            to 'element.replace(pattern, out)'.
            
            Otherwise, this method returns a new DinamicString where 'pattern' has been replaced by 
            'out'.
            
            - Can raise an error if 'element' is not a 'str' neither a DinamicString.
    '''
    if(isinstance(element, DinamicString)):
        return element.replace(pattern, out, deep)
    elif(type(element) == str):
        if(isinstance(out, DinamicString)):
            return DinamicString(element.replace(pattern, "_1"), out)
        return element.replace(pattern, out)
    
    raise TypeError("No string given. Impossible to replace string")

def din_m_replace(element, to_replace, deep=False):
    '''
        Method that replace simultaneously in 'element' the strings in 'to_replace.keys()' with the corresponding string.
        
        In case element and the values of 'to_replace' are all of type 'str', this method 
        will return a new 'str'. Otherwise a new DinamicString will be returned.
        
        In case 'element' is a DinamicString, 'deep' marks wether the replacement must be done only
        in the arguments or in the whole string.
        
        INPUT:
            - element: 'str' or DinamicStrign where perform the replacement.
            - to_replace: dictionary with the structure 'pattern : out'. This method will wubstitute the patterns in 'to_replace' by their corresponding 'out'.
            - deep: in case 'element' is a DinamicString, deep=True implies the replacement is only performed in the arguments. Otherwise this argument is irrelevant.
            
        OUTPUT:
            If 'element' and 'out' are of type 'str', this method return a new 'str' where all the patterns in 'to_replace' have been replaced simultaneously.
            Otherwise, this method returns a new DinamicString.
            
            - Can raise an error if 'element' is not a 'str' neither a DinamicString.
    '''
    if(isinstance(element, DinamicString)):
        return element.m_replace(to_replace, deep)
    elif(type(element) == str):
        real_replace = {}
        to_dinam = []
        for k,v in to_replace.items():
            if(isinstance(v, DinamicString)):
                to_dinam += [v]
                real_replace[k] = "_%d" %(len(to_dinam))
            else:
                real_replace[k] = v
        all_index = _din_m_indices(element, *real_replace.keys())
        res = ""; current_index = 0
        for el in all_index:
            res += element[current_index:el[0]] + real_replace[el[1]]
            current_index = el[0]+len(el[1])
        res += element[current_index:]
        
        if(len(to_dinam) > 0):
            return DinamicString(res, to_dinam)
        else:
            return res
    
    raise TypeError("No string given. Impossible to replace multiple strings")

def _din_indices(string, sep):
    '''
        Private method for this module. Return a list of indices where the string 'sep' appears on 'string'.
        
        This method relies in the fact that both 'string' and 'sep' are of type 'str'.
    '''
    try:
        index = string.index(sep)
        return [index] + [el+index+len(sep) for el in _din_indices(string[index+len(sep):],sep)]
    except ValueError:
        return []

def _din_m_indices(string, *seps):
    '''
        Private method for this module. Return a sorted list of pairs of (index, element) such
        that the string 'element' starts in 'string[index]'. This method list all the apparitions 
        of the strings in 'seps' within 'string'.
        
        
        This method relies in the fact that both 'string' and the elements of 'seps' are of type 'str'.
    '''
    ## We assume no possible overlapping can occur between elements in seps
    all_index = []
    for sep in seps:
        all_index += [(el,sep) for el in _din_indices(string,sep)]
    all_index.sort()
    
    return all_index
    
################################################################################
################################################################################
################################################################################
### Module variables
    
__all__ = ["DinamicString", "din_replace", "din_m_replace"]
