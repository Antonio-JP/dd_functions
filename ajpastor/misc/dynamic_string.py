r"""
Python file for a dynamic string

This module offers an implementation of a class (DynamicString) that behaves like a string 
but can be built using different common pieces so it is possible to perform simultaneos
substitutions on the string.

EXAMPLES::
    sage: from ajpastor.misc.dynamic_string import *

TODO:
    * Complete the Examples section of this documentation

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

# Python imports
import re # for regex searches

################################################################################
### Methods from the module
def is_string(element):
    r'''
        Method that checks whether an object can be considered a string.

        This method check that the type of the input is either ``str`` 
        or a :class:`DynamicString` so it is valid for use for the latter class.

        INPUT:
            * ``element``: the object to be checked

        EXAMPLES::

            sage: from ajpastor.misc.dynamic_string import *
            sage: is_string(1)
            False
            sage: is_string("%d" %1)
            True
            sage: is_string(DynamicString("_1 + _2", ['a', 'b']))
            True
    '''
    return isinstance(element, (str, DynamicString))

### Private method for the module
def _is_list(element):
    r'''
        Method to check if an object is a list or similar

        This method checks whether the argument is an iterable object valid for the
        class :class:`DynamicString`. Currently this would mean to be an instance of
        ``list``, ``tuple`` or ``set``.

        INPUT:
            * ``element``: the object to be checked.
        
        EXAMPLES::

            sage: from ajpastor.misc.dynamic_string import _is_list
            sage: _is_list([1,2,3])
            True
            sage: _is_list({1:1})
            False
            sage: _is_list(QQ[x].gens())
            True
            sage: _is_list(1)
            False
    '''
    return isinstance(element, (list, set, tuple))

### Class DynamicString
class DynamicString(object):
    r'''
        Class for dynamic strings, developed to make easier the substitution of elements through the string.

        This class allows the user to manage strings dynamically, which means, being able to make substitutions
        through the whole string simultaneously, or iterated substitutions in a simple and consistent manner.

        For doing so, this string works with "templates". The string is defined as a main structure for the 
        main message where some escape characters may be used to mark where the substitutions will be made.

        For example, if we have the name of a function ``exp(x) + 7x^2 - sin(x)``, we may want to compute 
        a composition with ``3ysin(y)``. Then we could create a ``DynamicString`` with the command

            ``DymanicString("exp(_1) + 7_1^2 - sin(_1)", ["x"])``

        This command creates the object that can be read as the first name. However, substituing the ``x`` by the 
        new name, is easy, since we have marked where ``x`` appeared originally.

        INPUT:
            * ``template``: a string with the main structure for the Dynamic String. This string may contain
              the escape character (see below) followed by integers to mark where each of the arguments will be replaced.
            * ``arguments``: a list or tuple containing the arguments for this DynamicString. A ``ValueError``
              is raised if the number of arguments is too small.
            * ``escape``: a character to mark how the arguments are introduced. By default, it takes the value ``'_'``.

        EXAMPLES::

            sage: from ajpastor.misc.dynamic_string import *
            sage: s = DynamicString("_1 + _2_1", ["a","b"]); s
            a + ba
            sage: s.replace('a', 'c')
            c + bc
            sage: t = DynamicString("+1 - +2", [s, 'x'], '+'); t
            a + ba - x
            sage: t + s # concatenation
            a + ba - xa + ba
            sage: (t+s).replace('a', 'x')
            x + bx - xx + bx
            
        This class does not allow a as escape character anything but strings of length 1::

            sage: DynamicString("##1 + ##2##1", ['a','b'], escape='##')
            Traceback (most recent call last):
            ...
            TypeError: The escape character must be of type 'str' with length 1 or 'chr'. Received <class 'str'>: ##
            sage: DynamicString("11 + 12", ['a','b'], escape=1)
            Traceback (most recent call last):
            ...
            TypeError: The escape character must be of type 'str' with length 1 or 'chr'. Received <class 'sage.rings.integer.Integer'>: 1

        Although numbers can be used as escape characterers if set as strings:

            sage: DynamicString("11 + 12", ['a','b'], escape='1')
            a + b

        The method also checks that the number of arguments are enough to perform the substitution::

            sage: DynamicString("_3 + _1", ['a','b'])
            Traceback (most recent call last):
            ...
            ValueError: Invalid number of arguments: required at least 3, provided 2
    '''
    ### Initialization methods
    def __init__(self, template, arguments, escape="_"):
        ## Assign template and escape
        if(not (type(template) == str)):
            raise TypeError("The template argument must be of type 'str'. Received: %s" %(type(template)))
        self.__template = template
        if(not ((type(escape) == str and len(escape) == 1) or type(escape) == chr)):
            raise TypeError("The escape character must be of type 'str' with length 1 or 'chr'. Received %s: %s" %(type(escape), escape))
        self.__escape = escape
        
        ## Checking the arguments for the string
        if(is_string(arguments)):
            arguments = [arguments]
        elif(_is_list(arguments)):
            arguments = list(arguments)
        self.__nargs = max([0] + [int(el[1:]) for el in re.findall(re.escape(escape) + r'\d+', template)])
        if(self.nargs() > len(arguments)):
            raise ValueError("Invalid number of arguments: required at least %d, provided %d" %(self.nargs(), len(arguments)))
        if(any(not is_string(el) for el in arguments[:self.nargs()])):
            raise TypeError("No valid arguments for a DynamicString: only strings and DynamicStrings are valid")
        self.__arguments = arguments[:self.nargs()]
        
        ## Computing the first representation of the DynamicString
        self.__real = None
        self.real()
        ## Variable for auxiliary computations
        self.__real_arguments = [str(el) for el in self.__arguments]

    def nargs(self):
        r'''
            Getter for the number of arguments for a DynamicString.

            This method returns the exact amount of arguments that this DynamicString has. This method does not iterate
            through inner DynamicStrings since the substitution is independent in each case.

            EXAMPLES::

                sage: from ajpastor.misc.dynamic_string import *
                sage: DynamicString("exp(x)",[]).nargs()
                0
                sage: DynamicString("exp(_1)", ['x']).nargs()
                1
                sage: DynamicString("_1 + _2", [DynamicString("exp(_1)", ["x"]), "a"]).nargs()
                2
                sage: (DynamicString("_1", ["exp(x)"]) + DynamicString("_1", ["y"])).nargs()
                2
        '''
        return self.__nargs
        
    ### Getters and setters
    def real(self):
        r'''
            Method to compute the current representation of the DynamicString

            This method computes the actual string object that the Dynamic String is currently representing.
            This method is cached, so calling it several times will not repeat the computations. However, the user
            can call the method :func:`clean` for removing the cached result.

            This cached result is also cleaned automatically when using the method :func:`change_argument`.

            EXAMPLES::

                sage: from ajpastor.misc.dynamic_string import *
                sage: s = DynamicString("exp(_1)", ["x"]); s.real()
                'exp(x)'
                sage: s.change_argument("y"); s.real()
                'exp(y)'
                sage: s.real() # no computations done
                'exp(y)'

            This method is not affected by the method :func:`replace`::

                sage: s.replace("x", "l")
                elp(y)
                sage: s.real()
                'exp(y)'

            This method returns always the same as casting the elemtn to a string::

                sage: str(s) == s.real()
                True
        '''
        if(self.__real is None or [str(el) for el in self.__arguments] != self.__real_arguments):
            self.__real_arguments = [str(el) for el in self.__arguments]
            self.__real = m_dreplace(self.__template, {"%s%d" %(self.__escape, i+1) : self.__real_arguments[i] for i in range(len(self.__arguments))})
        
        return self.__real
        
    def change_argument(self, new_argument, index=1):
        r'''
            Method to change the arguments of a :class:`DynamicString`.

            This method allows the user to set a new value for a particular argument. The user must provide
            the new value (that has to be valid for an argument, see :class:`DynamicString`) and an index
            that has to be bounded in the number of required.

            The method also allows a list of new arguments that has to be long enough to be valid. Then the argument
            ``index`` will be ignored and all arguments will be changed.
                       
            This method clean the cache for the method :func:`real`.
            
            INPUT:
                * ``new_argument``: a valid argument or a list (long enough) for all the arguments
                * ``index``: index of the argument that will be changed. Ignored if ``new_argument`` is a list. By defualt
                  its value is "1"
                
            EXAMPLES::

                sage: from ajpastor.misc.dynamic_string import *
                sage: s = DynamicString("exp(_1) + cos(_1_2)", ['x','y']); s
                exp(x) + cos(xy)
                sage: s.change_argument("a"); s
                exp(a) + cos(ay)
                sage: s.change_argument(["x","b"]); s
                exp(x) + cos(xb)

            The new argument can be a DynamicString::

                sage: t = DynamicString("exp(_1)", ["c"])
                sage: s.change_argument(t, 2); s
                exp(x) + cos(xexp(c))

            However, changing the argument of ``s`` will not change the arguments of the inner String::

                sage: s.change_argument("y"); s                
                exp(y) + cos(yexp(c))
                sage: t.change_argument("t"); s
                exp(y) + cos(yexp(t))

            Providing a string that is not valid (see method :func:`is_string`) will cause a ``TypeError``::

                sage: s.change_argument(1, 2)
                Traceback (most recent call last):
                ...
                TypeError: No valid argument for a DynamicString: only strings and DynamicStrings are valid
                sage: s.change_argument([x, "t"])
                Traceback (most recent call last):
                ...
                TypeError: No valid arguments for a DynamicString: only strings and DynamicStrings are valid

            Also, a bad number of arguments or index will raise a ``ValueError``::

                sage: s.change_argument(["1","2","3"]); s
                exp(1) + cos(12)
                sage: s.change_argument(["x"])
                Traceback (most recent call last):
                ...
                ValueError: Invalid number of arguments: required at least 2, provided 1
                sage: s.change_argument("x", 3)
                Traceback (most recent call last):
                ...
                ValueError: Invalid index: the index has to be between 1 and 2. Got: 3
                sage: s.change_argument("x", 0)
                Traceback (most recent call last):
                ...
                ValueError: Invalid index: the index has to be between 1 and 2. Got: 0
                sage: s.change_argument("x", -1)
                Traceback (most recent call last):
                ...
                ValueError: Invalid index: the index has to be between 1 and 2. Got: -1
        '''
        if(_is_list(new_argument)):
            new_argument = list(new_argument)
            if(len(new_argument) < self.nargs()):
                raise ValueError("Invalid number of arguments: required at least %d, provided %d" %(self.nargs(), len(new_argument)))
            if(any(not is_string(el) for el in new_argument[:self.nargs()])):
                raise TypeError("No valid arguments for a DynamicString: only strings and DynamicStrings are valid")
            self.__arguments = new_argument[:self.nargs()]
        else:
            if(not is_string(new_argument)):
                raise TypeError("No valid argument for a DynamicString: only strings and DynamicStrings are valid")
            if(index < 1 or index > self.nargs()):
                raise ValueError("Invalid index: the index has to be between 1 and %d. Got: %d" %(self.nargs(), index))
            self.__arguments[index-1] = new_argument
        
        self.__real = None
        
    ### Implementation of 'str' methods
    def replace(self, pattern, out, deep=False):
        '''
            Replacing method for DynamicStrings

            This method performs a similar operation as the method :func:`str.replace`. However, 
            this method splits the string into the template and the arguments perfoming the substitution
            in both separately and then combining them together into a final DynamicString.

            If the required pattern includes the escape character, the method will raise an error.
            
            INPUT:
                - ``pattern``: the string we want to change in ``self``.
                - ``out``: the new string to put where ``pattern`` is found.
                - ``deep``: extra argument that allows the user to only perform substitutions within the 
                  arguments. The default value is ``False``.
                
            EXAMPLES::

                sage: from ajpastor.misc.dynamic_string import *
                sage: s = DynamicString("_1 and _2", ["a", "b"])
                sage: s.replace('a', 'x')
                x xnd b
                sage: s.replace('a', 'x', True)
                x and b
                sage: t = DynamicString("exp(_1, _2) - a", ["A", "a"])
                sage: s.change_argument(t, 2); s
                a and exp(A, a) - a
                sage: s.replace("a", "P")
                P Pnd exp(A, P) - P
                sage: s.replace("a", "P", True)
                P and exp(A, P) - a
        '''
        new_arguments = [dreplace(el, pattern,out, deep) for el in self.__arguments]
        new_template = self.__template
        if(not deep):
            new_template = new_template.replace(pattern, out)
            
        return DynamicString(new_template, new_arguments, self.__escape)
    
    ### Extra methods
    def m_replace(self, to_replace, deep=False):
        '''
            Method to perform several replacements simultaneously. 
            
            This method do exactly the same as 'self.replace(key, value) for all (key,value) in to_replace but all at once, avoiding that one
            substitution affects the next one. This method returns always a new DynamicString with the replacements already done.
            
            INPUT:
                * ``to_replace``: dictionary with the pairs (pattern, out) to replace in ``self``.
                * ``deep``: this do the same as the argument ``deep`` on :func:`replace`.
                
            EXAMPLES::

                sage: from ajpastor.misc.dynamic_string import *
                sage: s = DynamicString("_1 + exp(_2) - _3", ["x","y","e"])
                sage: s.m_replace({"x": "y", "y": "x"})
                y + eyp(x) - e
                sage: s.replace("x", "y").replace("y", "x")
                x + exp(x) - e
                sage: s.m_replace({"x": "y", "y": "x"}, True)
                y + exp(x) - e
        '''
        new_arguments = [m_dreplace(el, to_replace, deep) for el in self.__arguments]
        new_template = self.__template
        if(not deep):
            new_template = m_dreplace(new_template, to_replace, False)
            
        return DynamicString(new_template, new_arguments, self.__escape)
        
    ### Magic Python methods
    def __repr__(self):
        r'''
            Magic Python 'repr' implementation
        '''
        return self.real()
        
    def __str__(self):
        r'''
            Magic Python 'str' implementation
        '''
        return self.real()
        
    def __getitem__(self, key):
        r'''
            Magic Python implementation for ``self[key]`` 
        ''' 
        return self.real()[key]
        
    ## Implementing concatenation
    def __add__(self, other):
        r'''
            Magic Python implementation for `+` (i.e. concatenation)

            This method computes the concatenation of Dynamic Strings creating a new DynamicString that contains the same amount of
            arguments than ``self`` and ``other``, adding the arguments of ``other`` as new arguments with shifted indexes.

            If ``other`` is a string, we treat it as a new DynamicString that is just template with no arguments. This can be risky
            if the string contains scape characters. In those cases, a manual creation of the DynamicString is recommended.

            EXAMPLES::

                sage: from ajpastor.misc.dynamic_string import *
                sage: s = DynamicString("_1 + _2", ["a","b"]); t = DynamicString("exp(_1)", ["x"])
                sage: s + t
                a + bexp(x)
                sage: (s + t).nargs() == s.nargs() + t.nargs()
                True
                sage: s + " exp(x)"
                a + b exp(x)
                sage: (s + " exp(x)").nargs() == s.nargs()
                True

            The user has to be careful of not using the escape character in a raw string::

                sage: s + "exp(_1)"
                a + bexp(a)
                sage: s + "_2_1"
                a + bba
                sage: s + "_3"
                Traceback (most recent call last):
                ...
                ValueError: Invalid number of arguments: required at least 3, provided 2
        '''
        if(type(other) == str):
            return DynamicString(self.__template + other, self.__arguments, self.__escape)
        elif(isinstance(other, DynamicString)):
            ## Changing arguments of other
            other_template = m_dreplace(other.__template, 
                                            {"%s%d" %(other.__escape, i) : "%s%d" %(self.__escape, i+len(self.__arguments)) for i in range(1,len(other.__arguments)+1)})
            
            return DynamicString(self.__template + other_template, self.__arguments + other.__arguments, self.__escape)
            
        return NotImplemented
    
    def __radd__(self, other):
        r'''
            Magic Python implementation for inverse '+' (i.e. concatenation)

            See method :func:`__add__` for further information.
        '''
        if(type(other) == str):
            return DynamicString(other + self.__template, self.__arguments, self.__escape)
        elif(isinstance(other, DynamicString)):
            return other.__add__(self)
            
        return NotImplemented

################################################################################
################################################################################
################################################################################
### Utility methods combining 'str' and DynamicString
    
def dreplace(element, pattern, out, deep=False):
    r'''
        Enhanced "replace" method. 
        
        This function is equivalent to the ``replace`` method of the ``str`` class when 
        both ``element`` and ``out`` are strings. However, this method mix together the use
        of :class:`DynamicString` and strings.
                
        INPUT:
            * ``element``: a string or :class:`DynamicString` where we want to replace ``pattern``.
            * ``pattern``: a string with the pattern to replace in ``element``.
            * ``out``: a string or ``DynamicString`` that will be put in the places where ``pattern`` appears in ``element``.
            * ``deep``: in case ``element`` is a :class:`DynamicString`, this argument is equivalent to that in method :func:`DynamicString.replace`.
            
        OUTPUT:
            * If ``element`` and ``out`` are both strings, then the method return the equivalent string
              after the replacement.
            * Otherwise, this method returns a :class:`DynamicString`.
        
        EXAMPLES::

            sage: from ajpastor.misc.dynamic_string import *
            sage: s = DynamicString("exp(_1)", ["x"])
            sage: t = dreplace("testing string", "string", s); t
            testing exp(x)
            sage: isinstance(t, DynamicString)
            True
            sage: u = dreplace("testing string", "s", " a "); u
            'te a ting  a tring'
            sage: isinstance(u, DynamicString)
            False
            sage: v = dreplace(s, "x", "y"); v
            eyp(y)
            sage: str(v) == str(s.replace("x", "y"))
            True

        This method raise an error if ``element`` is not a string or a :class:`DynamicString`::

            sage: dreplace(123, "1", "2")
            Traceback (most recent call last):
            ...
            TypeError: No string given. Impossible to replace string
    '''
    if(isinstance(element, DynamicString)):
        return element.replace(pattern, out, deep)
    elif(type(element) == str):
        if(isinstance(out, DynamicString)):
            return DynamicString(element.replace(pattern, "_1"), out)
        return element.replace(pattern, out)
    
    raise TypeError("No string given. Impossible to replace string")

def m_dreplace(element, to_replace, deep=False):
    r'''
        Method that replace simultaneously patters in a string.
        
        This method perfoms a simoultanously substitution on ``element`` (if it is either a string or 
        a :class:`DynamicString`) patterns that can be found in ``to_replace``. This is equivalent,
        in the case of :class:`DynamicString`, to the method :func:`DynamicString.m_replace`.
        
        INPUT:
            * ``element``: string or :class:`DynamicString` to perform the replacement.
            * ``to_replace``: dictionary with entries ``(pattern : out)`` to be replaced.
            * ``deep``: see argument ``deep`` in method :func:`DynamicString.replace`.
            
        OUTPUT:
            * If ``element`` and all the entries in ``to_replace`` are strings, this method returns a
              string object after performing the substitution.
            * Otherwise, this method returns a new DynamicString.

        EXAMPLES::

            sage: from ajpastor.misc.dynamic_string import *
            sage: s = DynamicString("exp(_1)", ["a"])
            sage: t = "a + b"
            sage: u = m_dreplace(t, {"a": "b", "b" : "a"}); u
            'b + a'
            sage: isinstance(u, DynamicString)
            False
            sage: v = m_dreplace(s, {"a":"b", "x": "y"}); v
            eyp(b)
            sage: isinstance(v, DynamicString)
            True
            sage: v.nargs()
            1
            sage: m_dreplace(s, {"a":"b", "x": "y"}, True)
            exp(b)

        This method raise an error if ``element`` is not a string or a :class:`DynamicString`::

            sage: m_dreplace(123, {"1": "2", "2": "3"})
            Traceback (most recent call last):
            ...
            TypeError: No string given. Impossible to replace multiple strings
    '''
    if(isinstance(element, DynamicString)):
        return element.m_replace(to_replace, deep)
    elif(type(element) == str):
        real_replace = {}
        to_dinam = []
        for k,v in to_replace.items():
            if(isinstance(v, DynamicString)):
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
            return DynamicString(res, to_dinam)
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
    
__all__ = ["DynamicString", "dreplace", "m_dreplace", "is_string"]
