
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
        
def composition(f,g):   
    if(g(0) != 0):                     
        raise ValueError("Impossible compose with g(0) != 0");
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
    '''
    return lambda n: f(n)/factorial(n);

def ogf_egf(f):       
    '''
        Method that receives a sequence in the form of a black-box function
        and return a sequence h(n) such that egf(h) = ogf(f).
    '''
    return lambda n: f(n)*factorial(n);

def inv_lagrangian(f):
    if(f(0) != 0):
        raise ValueError("Power serie not invertible");
    if(f(1) == 0):
        raise NotImplementedError("Case with order higher than 1 not implemented");
    f = egf_ogf(f);
    def _inverse(n):
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
                #print variables;
                extra = (-1)^k*falling_factorial(n+k-1,k);
                result += extra*poly(**{str(variables[i]):f(i+1)/((i+1)*f(1)) for i in range(len(v
ariables))});
            return (1/((f(1)^n)*factorial(n))) * result;
    return ogf_egf(_inverse);

