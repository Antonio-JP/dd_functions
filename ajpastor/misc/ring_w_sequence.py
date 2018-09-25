
from sage.all import *   # import sage library

########################################################

from sage.rings.ring import Ring;

class Ring_w_Sequence (UniqueRepresentation, Ring):
    def __init__(self, base, method = None, category = None):
        Ring.__init__(self, base, category=category);
        self.__method = method;
        
    def sequence(self, el, n):
        return self.getSequenceElement(el,n);
        
    def getSequenceElement(self, el, n):
        if(el in self):
            return self.__method(el,n);
        raise TypeError("Can not compute a sequence for an element which is not in the ring");    

class Wrap_w_Sequence_Ring (Ring_w_Sequence):
    def __init__(self, base, method = None):
        super(Wrap_w_Sequence_Ring, self).__init__(base, method=method, category=base.category());

    def _coerce_map_from_(self, S):
        return self.base()._coerce_map_from_(S);

    def _has_coerce_map_from(self, S):
        return self.base()._has_coerce_map_from(S);

    def __call__(self, *args, **kwds):
        return self.base()(*args, **kwds);
    
    def __getattribute__(self, name):
        ## Avoiding infinite recursion
        if(name == "base"):
            return super(Ring_w_Sequence,self).__getattribute__(name);
        
        ## Now that base is not the attribute
        try:
            ## Trying to have the attribute f the base ring
            attr = self.base().__getattribute__(name);
            if(attr is None):
                raise AttributeError;
            return attr;
        except AttributeError:
            ## No attribute for the ring, searching for this ring
            attr = super(Ring_w_Sequence, self).__getattribute__(name);
            if(attr is None):
                raise AttributeError;
            return attr;
            
        raise AttributeError("'%s' object has no attribute '%'" %(self.__class__, name));
        
    def __repr__(self):
        return "(SR)" + repr(self.base());

    def __str__(self):
        return "(SR)" + str(self.base());

    def getSequenceElement(self, el, n):
        self_gen = 'x';
        try:
            self_gen = self.base().gens()[-1 ];
        except:
            pass;
            
        if(self_gen == 1 ):
            if(n > 0 ):
                return 0 ;
            elif(n==0 ):
                return el;
            else:
                raise ValueError("Impossible get negative element of the sequence");
        if(el in self):
            res = el;
            for i in range(n):
                try:
                    res = derivative(res,self_gen);
                except AttributeError:
                    ## Not derivative possible. Considering a constant
                    if(n == 0 ):
                        return res;
                    return 0 ;
            try:
                return res(**{repr(self_gen):0 })/factorial(n);
            except TypeError:
                ## Not callable element. Returning the element without evaluation
                return res/factorial(n);
        else:
            raise TypeError("Element not in `self` to compute the sequence.");
#####################################################################

def sequence(el, n):
    R = el.parent();
    if(sage.symbolic.ring.is_SymbolicExpressionRing(R)):
        variable = el.variables()[0];
        return el.derivative(variable,n)(**{str(variable):0})/factorial(n);
    if(not isinstance(R, Ring_w_Sequence)):
        R = Wrap_w_Sequence_Ring(R);
        
    return R.getSequenceElement(el,n);

