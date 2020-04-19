"""
Python file for verbose system

This module offers a verbose system for helping debugging, tracking procceses or whatever the user want to 
print. It provides an indentation system, depth of printing and many other utilities.

EXAMPLES::
    sage: from ajpastor.misc.verbose import *

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

from sage.all import *   # import sage library

####################################################################
###
### verbose.py
###
### Code for perform an easy conditional printing.
###
### Version 0.0 (12-07-2017)
###
### Version 1.0 (06-10-2017)
###     - Changed the main system of verbose
###     - Private class __verbose_session created
###     - Visible instance sverbose created
###     - To print with the sverbose session, use the call method ``sverbose(text)``
###     - To change the configuration of the sverbose, call the public methods of the class
###     - Added a decorator to easily set up a function to verbose
###
### Version 1.1 (18-06-2018)
###     - Move file from .sage to .py
###
####################################################################

import sys;
from functools import wraps;

class __verbose_session(object):
    def __init__(self):
        self.__time = True;
        self.__current_depth = 0 ;
        self.__level = 1 ;
        self.__default_beg = "";
        self.__begs = ["** ","## ","-- ","%% ","&& ","@@ "];
        self.__end = "\n";
        self.__deep_wrapper = 0 ;
        
        self.__n_iterations = 0 ;
        self.__perc = False;
        self.__inline = True;
        self.__current_iteration = 0 ;
        
    ## Basic call method
    def __call__(self,string, end=None):
        if(self.__level+self.__current_depth <= get_verbose()):
            to_print = "";
            if(self.__time):
                from datetime import datetime as time;
                to_print += "|"+str(time.now())+"|";
            for i in range(self.__current_depth):
                to_print += "\t";
            if(self.__current_depth > 0 ):
                to_print += str(self.__begs[(self.__current_depth-1 )%len(self.__begs)]);
            else:
                to_print += str(self.__default_beg);
            
            to_print += string;
            if(not(end is None)):
                to_print += end;
            else:
                to_print += str(self.__end);
                
            print(to_print);
        return;
        
    ## Changing level of verbose for the session
    def get_level(self):
        return self.__level;
        
    def set_level(self, level):
        self.__level = level;
        
    ## Changing the time printing
    def set_time(self, time):
        self.__time = time;
        
    def get_time(self, time):
        return self.__time;
            
    ## Changing depth methods
    def reset_depth(self):
        self.__current_depth = 0 ;
    
    def change_depth(self,amount):
        self.__current_depth = max(0 , self.__current_depth+amount);
        
    def increase_depth(self,amount = 1 ):
        if(amount < 0 ):
            raise ValueError("To increase the tab depth it is needed a positive number, not %d" %amount);
        self.change_depth(amount);
        
    def decrease_depth(self,amount = 1 ):
        if(amount < 0 ):
            raise ValueError("To decrease the tab depth it is needed a positive number, not %d" %amount);
        self.change_depth(-amount);
        
    ## Changing the wrapper behavior
    def get_deep_wrapper(self):
        return self.__deep_wrapper;
        
    def set_deep_wrapper(self, new_deep):
        self.__deep_wrapper = new_deep;
        
    ## Changing default beginning
    def get_default_beginning(self):
        return self.__default_beginning;
        
    def set_default_beginning(self, beg):
        self.__default_beginning = beg;
        
    ## Iteration helping system variables
    def get_n_iterations(self):
        return self.__n_iterations;
    def set_n_iterations(self, n_iterations):
        self.__n_iterations = n_iterations;
        
    def get_perc(self):
        return self.__perc;
    def set_perc(self, perc):
        self.__perc = perc;
        
    def get_inline(self):
        return self.__inline;
    def set_inline(self, inline):
        self.__inline = inline;
        
    def get_current_iteration(self):
        return self.__current_iteration;
    def set_current_iteration(self, current_iteration):
        self.__current_iteration = current_iteration;
        
    def get_iteration_state(self):
        return {'n': self.__n_iterations, 'perc' : self.__perc, 'inline' : self.__inline, 'current' : self.__current_iteration};
        
    def set_iteration_state(self, state):
        try:
            self.__n_iterations = state['n'];
            self.__perc = state['perc'];
            self.__inline = state['inline'];
            self.__current_iteration = state['current'];
        except KeyError:
            pass;
            
    ## Iteration helping system
    def start_iteration(self,iterations, percentage = False, in_line = True):
        self.__n_iterations = iterations;
        self.__perc = percentage;
        self.__inline = in_line;
        self.__current_iteration = 1 ;
        
    def next_iteration(self):
        msg = "Performed %d-th iteration " %self.__current_iteration;
         
        if(self.__perc and self.__n_iterations > 0 ):
            msg += "(%.2f %%)" %(self.__current_iteration*100 /self.__n_iterations);
        else:
            msg += "(%d/%d)" %(self.__current_iteration, self.__n_iterations);
            
        if(self.__inline and self.__current_iteration < self.__n_iterations):
            end = "\r";
        else:
            end = None;
            
        self(msg, end);
        self.__current_iteration += 1 ;
    
## Conditional definition of the verbose variables
sverbose = __verbose_session();

class VerboseError(RuntimeError):
    def __init__(self):
        pass;

#@wraps
def wverbose(func):
    ## Creating the wrapped function
    def wrapped_function(*args, **kwds):
        try:
            sverbose.increase_depth(sverbose.get_deep_wrapper());
            sverbose("Calling method %s" %(func.__name__));
            state = sverbose.get_iteration_state();
            sverbose.increase_depth();
        except Exception:
            raise VerboseError();
            
        e = None;
        try:
            output = func(*args,**kwds);
        except Exception as e:
            pass;
        except KeyboardInterrupt as e:
            pass;
        sverbose.decrease_depth();
        sverbose.set_iteration_state(state);
        
        if(not e is None):
            sverbose("Exception raised in method %s" %(func.__name__));
            sverbose.decrease_depth(sverbose.get_deep_wrapper());
            raise e;
        else:
            sverbose("Finished method %s" %(func.__name__));
            sverbose.decrease_depth(sverbose.get_deep_wrapper());
            return output;
        
    ## Setting up the other attributes for the wrapped function
    wrapped_function.__doc__ = getattr(func, '__doc__');
    
    return wrapped_function;
    
#@wraps
def wverbose_w_data(func):
    ## Creating the wrapped function
    def wrapped_function(*args, **kwds):
        try:
            sverbose.increase_depth(sverbose.get_deep_wrapper());
            sverbose("Calling method %s" %(func.__name__));
            sverbose("Arguments:");
            if(len(args) > 0 ):
                sverbose("%s" %(str(args)));
            if(len(kwds)> 0 ):
                sverbose("%s" %(str(kwds)));
            state = sverbose.get_iteration_state();
            sverbose.increase_depth();
        except Exception:
            raise VerboseError();
        
        e = None;
        try:
            output = func(*args,**kwds);
        except Exception as e:
            pass;
        except KeyboardInterrupt as e:
            pass;
        sverbose.decrease_depth();
        sverbose.set_iteration_state(state);
        
        if(not e is None):
            sverbose("Exception raised in method %s" %(func.__name__));
            sverbose.decrease_depth(sverbose.get_deep_wrapper());
            raise e;
        else:
            sverbose("Finished method %s" %(func.__name__));
            sverbose("Output: %s" %(str(output)));
            sverbose.decrease_depth(sverbose.get_deep_wrapper());
            return output;
        
    ## Setting up the other attributes for the wrapped function
    wrapped_function.__doc__ = getattr(func, '__doc__');
    
    return wrapped_function;


# Print iterations progress
def printProgressBar (iteration, total, prefix = '', suffix = '', decimals = 1, length = 100, fill = '#'):
    """
    Call in a loop to create terminal progress bar
    @params:
        iteration   - Required  : current iteration (Int)
        total       - Required  : total iterations (Int)
        prefix      - Optional  : prefix string (Str)
        suffix      - Optional  : suffix string (Str)
        decimals    - Optional  : positive number of decimals in percent complete (Int)
        length      - Optional  : character length of bar (Int)
        fill        - Optional  : bar fill character (Str)
    """
    percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
    filledLength = int(length * iteration // total)
    bar = fill * filledLength + '-' * (length - filledLength)
    print("\r%s |%s| %s%% %s\r" % (prefix, bar, percent, suffix));
    # Print New Line on Complete
    if iteration == total: 
        print("");
    sys.stdout.flush();

__all__ = ["sverbose", "wverbose", "wverbose_w_data", "printProgressBar"];

__VERBOSE_LEVEL = None;
try:
    set_verbose(get_verbose());
except Exception:
    __VERBOSE_LEVEL = 0 ;
    def set_verbose(level):
        global __VERBOSE_LEVEL;
        __VERBOSE_LEVEL = max(0 , level);
        if(__VERBOSE_LEVEL >= 1 ):
            print("-- Changed verbose level to %d" %(__VERBOSE_LEVEL));
    
    def get_verbose():
        global __VERBOSE_LEVEL;
        return __VERBOSE_LEVEL;
        
    __all__ += ["set_verbose", "get_verbose"];
