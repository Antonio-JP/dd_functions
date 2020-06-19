r"""
Python file for serializable objects

This package provides a class for characterize serializable elements providing methods 
to save the object into a file and loading it from the same place.

The user only needs to inherit from this class and use appropiately the method
set_args while building the object.

EXAMPLES::

AUTHORS::

    - Antonio Jimenez-Pastor (2019-08-23): initial version

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

class InitSequenceSerializable:
    r'''
        Auxiliary class to detect the beginning of a sequence in a serializable argument.
    '''
    pass

class FinishSequenceSerializable:
    r'''
        Auxiliary class to detect the ending of a sequence in a serializable argument.
    '''
    pass

class SerializableObject:
    r'''
        Class for serializable objects. This class provides the functionality required
        for serialize objects into a binary file
    '''
    ### Class methods to load an object from a file
    @classmethod
    def unserialize(cls, file):
        '''
            Method to load an object of the class ``cls``.

            This methods reads from a file (it opens it if it is given as a string) an object and build the 
            corresponding object using the constructor for the class ``cls``.

            This method relies on the package ``pickle`` for those objects that are not serializable. Otherwise, it will
            use a recursive serialization procedure to get the final object.
        '''
        from pickle import load as pload

        ## Auxiliar method for the recursive loading procedure
        def rec_load(ctype, file):
            if(issubclass(ctype, SerializableObject)):
                return ctype.unserialize(file)
            elif(issubclass(ctype, list) or issubclass(ctype, tuple)):
                # Reading the starting mark
                pload(file)

                # Starting the empty collection
                res = []

                # Reading each element
                current = pload(file)
                while(current != FinishSequenceSerializable):
                    # If it is not over, current is the type for the next element
                    res += [rec_load(get_class(current), file)]
                    current = pload(file)

                # Return the appropriate type of collection
                return ctype(res)
            elif(issubclass(ctype, dict)):
                # Reading the starting mark
                pload(file)

                # Starting the empty collection
                res = {}

                # Reading each element
                current = pload(file)
                while(current != FinishSequenceSerializable):
                    # If it is not over, current is the type for the next key
                    key = rec_load(get_class(current), file)
                    v_type = pload(file)
                    value = rec_load(get_class(v_type), file)
                    res[key] = value

                    current = pload(file)

                return res
            else:
                return pload(file)

        def get_class(ctype):
            if(ctype is None):
                return type(ctype)
            return ctype

        is_str = (type(file) == str)
        if(is_str): file = open(file, "rb")

        ## Reading the first object: a list of classes
        args_types = pload(file)
        ## Reading for each element in args the 
        args = [rec_load(get_class(ctype), file) for ctype in args_types]

        ## Reading the dictionary of names and types
        kwds_types = pload(file)
        ## Building the actual dictionary of keywords
        kwds = {ctype[0]: rec_load(get_class(ctype[1]), file) for ctype in kwds_types}

        if(is_str): file.close()

        ## Returning the final object
        return cls(*args, **kwds)

    ## Builder method to initialize variables
    def __init__(self, *args, **kwds):
        # Initializing the two 
        if(len(args) > 0):
            self.__args = args
        else:
            self.__args = []
        if(len(kwds) > 0):
            self.__kwds = kwds
        else:
            self.__kwds = {}

    ## Setter and getter for the arguments of the builder
    def set_sargs(self, *args, **kwds):
        r'''
            Setter for the arguments of the serializable object
        '''
        self.__args = args
        self.__kwds = kwds

    def sargs(self):
        r'''
            Setter for the first arguments of the serializable object
        '''
        return self.__args

    def skwds(self):
        r'''
            Setter for the named arguments of the serializable object
        '''
        return self.__kwds

    ## Serializable method
    def serialize(self, file):
        r'''
            Method to dump an object into a file.

            This methods writes to a file (it opens it if it is given as a string) an object.

            This method relies on the package ``pickle`` for those objects that are not serializable. Otherwise, it will
            use a recursive serialization procedure to write the whole object.
        '''
        from pickle import dump as pdump
        from sage.all import Expression

        ## Auxiliar method for the recursive loading procedure
        def rec_dump(obj, file):
            if(isinstance(obj, SerializableObject)):
                obj.serialize(file)
            elif(isinstance(obj, Expression)):
                pdump(str(obj), file)
            elif(isinstance(obj, list) or isinstance(obj, tuple)):
                pdump(InitSequenceSerializable, file)
                for el in obj:
                    pdump(get_class(el), file)
                    rec_dump(el, file)
                pdump(FinishSequenceSerializable,file)
            elif(isinstance(obj, dict)):
                pdump(InitSequenceSerializable, file)
                for key in obj:
                    pdump(get_class(key), file)
                    rec_dump(key, file)
                    pdump(get_class(obj[key]), file)
                    rec_dump(obj[key], file)
                pdump(FinishSequenceSerializable,file)
            else:
                pdump(obj,file)

        def get_class(obj):
            if(obj is None):
                return None
            return obj.__class__

        # Checking the file is opened
        is_str = (type(file) == str)
        if(is_str): file = open(file, "wb+")

        # Serializing the list of types for args
        pdump([get_class(obj) for obj in self.sargs()], file)

        # Serializing the arguments
        for obj in self.sargs():
            rec_dump(obj, file)

        # Serializing the list of named arguments
        pdump([(key, get_class(self.skwds()[key])) for key in self.skwds()], file)

        # Serializing the arguments
        for key in self.skwds():
            rec_dump(self.skwds()[key],file)

        # Closing the file if we opened it
        if(is_str): file.close()
