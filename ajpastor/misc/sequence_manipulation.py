from sage.functions.other import factorial;
from sage.combinat.combinat import bell_polynomial;
from sage.arith.misc import falling_factorial;
from sage.misc.cachefunc import cached_function

################################################################################
################################################################################
################################################################################
## Sequence operations
def addition(f,g):
    return lambda n : f(n)+g(n);

def hadamard_product(f,g):
    return lambda n : f(n)*g(n);

def cauchy_product(f,g):
    return lambda n : sum(f(m)*g(n-m) for m in range(n+1));

def standard_derivation(f):
    return lambda n : (n+1)*f(n+1);

def shift(f):
    return lambda n : f(n+1);
        
def composition(f,g):   
    if(g(0) != 0):                     
        raise ValueError("Impossible compose with g(0) != 0");
    @cached_function
    def _composition(n):                                     
        if(n == 0):                                                                
            return f(0);
        result = 0; 
        current = g; 
        for k in range(1,n+1):
            result += f(k)*current(n);
            current = cauchy_product(current, g)
        return result; 
    return _composition;

def egf_ogf(f):       
    '''
        Method that receives a sequence in the form of a black-box function
        and return a sequence h(n) such that egf(f) = ogf(h).
        
        Then h(n) = f(n)/factorial(n)
    '''
    return lambda n: f(n)/factorial(n);

def ogf_egf(f):       
    '''
        Method that receives a sequence in the form of a black-box function
        and return a sequence h(n) such that egf(h) = ogf(f).
        
        Then h(n) = f(n)*factorial(n)
    '''
    return lambda n: f(n)*factorial(n);

def inv_lagrangian(f):
    if(f(0) != 0):
        raise ValueError("Power serie not invertible");
    if(f(1) == 0):
        raise NotImplementedError("Case with order higher than 1 not implemented");
    f = ogf_egf(f);
    @cached_function
    def _inverse_egf(n):
        if(n == 0):
            return 0;
        elif(n == 1):
            return 1/f(1);
        else:
            result = 0;
            for k in range(1,n):
                poly = bell_polynomial(n-1,k);
                #print poly;
                variables = poly.variables();
                extra = ((-1)**k)*falling_factorial(n+k-1, k);
                if(k == n-1):
                    evaluation = poly(x=f(2)/2/f(1));
                else:
                    evaluation = poly(**{"x%d" %(i) : f(i+2)/(i+2)/f(1) for i in range(n-k)});
                
                result += extra*evaluation;
                
            return (1/(f(1)**n)) * result;
    return egf_ogf(_inverse_egf);

