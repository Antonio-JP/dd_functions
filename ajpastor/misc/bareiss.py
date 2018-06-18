
from sage.all import *   # import sage library

from ajpastor.misc.matrix import swap_rows;
from ajpastor.misc.matrix import swap_cols;

from ajpastor.misc.cached_property import derived_property;

from ajpastor.misc.verbose import *;

from sage.rings.polynomial.polynomial_ring import is_PolynomialRing as isUniPolynomial;
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing as isMPolynomial;

class BareissAlgorithm(object):
    ### Initialization method
    def __init__(self, parent, M, method=None, relations = []):
        '''
            This class represent the application of the Bareiss Algorithm over a matrix with polynomial coefficients.
            This class receives several parameters:
                - `parent`: the polynomial ring where the operations will be done. A fraction field is allowed if the base domain is a polynomial ring.
                - `M`: the matrix we want to treat with the Algorithm
                - `method`: a Boolean function such that I = {g in parent | method(g) == True}
                
            This algorithm also works in a quotient of the polynomial ring (K[X]/I) and the method provided must be a method to check if some polynomial is in the ideal I.
        '''
        ## Checking the parent parameter
        if(parent.is_field()):
            parent = parent.base();
        if(not (isUniPolynomial(parent) or isMPolynomial(parent))):
            raise TypeError("The parent for this algorithm must be a polynomial ring.\n\t Got: %s" %parent);
        self.__parent = parent;
            
        ## Checking the matrix input
        self.base_matrix = Matrix(self.parent(), M);
        
        self.change_of_columns = Permutation(range(1 ,self.base_matrix.ncols()));
        
        ## Storing the checking method
        self.__in_ideal = method;
        
        ## Cached elements
        self.__steps = None;
        self.__actions = None;
        self.__gb = ideal(self.parent(), relations).groebner_basis();
        self.__echelon = None;
        
        
    ### Getter methods
    def parent(self):
        '''
            Method to have the same interface that the majority of objects of SAGE. Returns the polynomial ring where the matrix have its coefficients.
        '''
        return self.__parent;
        
    #################################################
    ### Linear algebra methods
    #################################################
    #@wverbose
    def echelon_form(self):
        '''
            Method to compute the right echelon form of the matrix self.base_matrix.

            This method store the result for future callings in a private variable.
        '''
        if(self.__echelon is None):
            self.__compute_echelon();
        return self.__echelon;
        
    #@wverbose
    def __compute_echelon(self):
        '''
            Method to really compute the right echelon form of self.base_matrix. This method
            is private and it is not recommended to be called by the user.
        '''
        #sverbose("Computing the echelon form of a matrix of size %dx%d" %(self.base_matrix.nrows(), self.base_matrix.ncols()));
        
        self.__actions = [("base")];
        self.__steps = [self.base_matrix];
        
        ## If we have initial relations, we perform the first reduction
        if(self.__have_ideal(self.__gb)):
            #sverbose("Initial reduction of the matrix"); ## Verbose
            self.__steps += [self.__simplify_matrix(self.__steps[-1 ])];
            self.__actions += [("f_reduce", self.__gb)];
        
        tr = self.__steps[-1 ].nrows(); tc = self.__steps[-1 ].ncols();
        cr = 0 ; cc = 0 ; i = -1 ;
        
        #sverbose("Starting the iterations");
        #sverbose.start_iteration(min(tr,tc)+1 , True, False);
        while(i < min(tr,tc)):
            i = i + 1 ;
            
            #sverbose.increase_depth();
            
            pivot = self.__choose_pivot(self.__steps[-1 ], i,i);
            
            cr,cc = pivot[0 ];
            new_rels = pivot[2 ];
            
            ## If there are new relations, we simplify the matrix
            if(len(new_rels) > 0 ):
                #sverbose("New relations found looking for a pivot");
                #sverbose("\t%s" %new_rels);
                self.__gb = ideal(self.parent(), tuple(new_rels) + tuple(self.__gb)).groebner_basis();
                self.__steps += [self.__simplify_matrix(self.__steps[-1 ])];
                self.__actions += [("reduce", new_rels)];
                #sverbose("New reductions applied");
                    
            ## If no pivot was found, we finish
            if(cr == -1  or cc == -1 ):
                #sverbose("No pivot found.");
                #sverbose.decrease_depth();
                #sverbose.next_iteration();
                break;
                    
            ## If we have a new pivot, we moved everythin so it is in the proper position
            swap_actions = pivot[1 ];
            for action in swap_actions:
                if(action[0 ] == "sw_r"):
                    self.__steps += [swap_rows(self.__steps[-1 ], action[1 ],action[2 ])];
                elif(action[0 ] == "sw_c"):
                    self.__steps += [swap_cols(self.__steps[-1 ], action[1 ],action[2 ])];
                    self.change_of_columns = Permutation((action[1 ]+1 ,action[2 ]+1 ))*self.change_of_columns;
                    
                self.__actions += [action];
                
            ## One the pivot is in position, we proceed with the Bareiss elimination
            M = self.__steps[-1 ];
            
                
            ## We save the new matrix and go on
            self.__steps += [self.__bareiss(self.__steps[-1 ], i)];
            self.__actions += [("bareiss", i)];
            
            #sverbose.decrease_depth();
            #sverbose.next_iteration();
            
        #sverbose("Performing gcd simplification");
        gcds = [gcd(row) for row in self.__steps[-1 ]];
        for i in range(len(gcds)):
            if(gcds[i] == 0 ):
                gcds[i] = 1 ;
        self.__steps += [Matrix(self.parent(), [[el/gcds[i] for el in self.__steps[-1 ][i]] for i in range(self.__steps[-1 ].nrows())])];
        self.__actions += [("gcd_simpl")];
            
        self.__echelon = self.__steps[-1 ];
        #sverbose("Finished computation of echelon form");
                                
        return;
        
    @derived_property
    def rank(self):
        '''
            Method to compute the property "rank" of self.base_matrix. This method
            uses the right echelon form of the matrix and check how many
            rows are all zeros.
        '''
        for i in range(self.base_matrix.nrows()):
            if(any((el != 0 ) for el in self.echelon_form()[-(i+1 )])):
                return self.base_matrix.nrows()-i;
                
    def relations(self):
        '''
            Method to get the realtions between the variables found in the matrix.

            A relation is a polynomial p in self.parent() such that self.is_in_ideal(p) is True.
            We return a Groebner basis of all the relations found while computing the echelon
            form of the matrix.

            WARNING: It is important to remark that this method does not return the basis
            of the ideal that self.is_in_ideal() defines. This is because only found relations
            are taking into account at this step.
        '''
        self.echelon_form();
        return self.__gb;
                
    @cached_method
    def right_kernel_matrix(self):
        '''
            Method to compute the right kernel matrix of self.base_matrix.

            This method computes the echelon form of the matrix and then starts a
            simple computation to clean denominator and obtain a basis formed with 
            elements of the integral domain self.parent().
        '''
        sol_dimension = self.base_matrix.ncols()-self.rank;        
        M = self.echelon_form();
        
        if(sol_dimension > 0 ):
            ## Compute the product of the nice diagonal
            A = self.__get_lcm([M[i][i] for i in range(self.rank)]);
            to_mult = [-A/M[i][i] for i in range(self.rank)];
        
            ker_basis = [vector(self.parent(), [to_mult[j]*M[j][i+self.rank] for j in range(self.rank)] + [0  for j in range(i)] + [A] + [0  for j in range(i+1 , sol_dimension)]) for i in range(sol_dimension)];
            
            ch = self.change_of_columns;
            ## If there were a change of columns (i.e. ch is not the trivial permutation) 
            ## we swap the result
            if(Permutation(range(1 ,self.base_matrix.ncols())) != ch):
                ch = ch.inverse();
                rows = [[0  for i in range(M.ncols())] for j in range(len(ker_basis))];
                for j in range(M.ncols()):
                    new_col = ch(j+1 )-1 ;
                    for i in range(len(ker_basis)):
                        rows[i][new_col] = ker_basis[i][j];
                
                ker_basis = [vector(self.parent(), row) for row in rows];            
            
            return ker_basis;
        else:
            return [vector(self.parent(), [0  for i in range(M.ncols())])];
        
    #################################################
    ### Other cached methods
    #################################################
    @cached_method
    def is_in_ideal(self, p):
        '''
            Method that defines the ideal over this algorithm is working on.

            This method is a boolean method (returns True or False) in such a way that
            I = {g in self.parent() : self.is_in_ideal(g) == True} is an ideal
            of self.parent().
        '''
        p = self.parent()(p);
        
        try:
            return self.__in_ideal(p) is True;
        except Exception:
            return False;
          
    @cached_method
    def steps(self):
        '''
            This method returns a list of pairs with the matrices obtained during the proccess and the steps taken.
        '''
        self.echelon_form();
        
        return [(self.__steps[i],self.__actions[i]) for i in range(len(self.__steps))];
        
    #################################################
    ### Private methods for Bareiss Algorithm 
    #################################################
    #@wverbose
    def __choose_pivot(self, M, ir, ic):
        '''
            This method computes the next pivot element for the algorithm and returns the information to prepare the matrix for the next step.
            The ir and ic are parameters to begin the search from the position (ir,ic)

            A valid pivot is any element on the matrix with position strictly greater than (ir,ic)
            (i.e., both coordinates must be greater or equal to those) and must not be in the
            ideal defined by self.is_in_ideal().

            INPUT:
                - M: the current matrix we are choosing the pivot.
                - ir: initial index for the rows.
                - ic: initial index fot the columns.
            OUTPUT:
                This method returns a tuple of 4 elements:
                    - A pair (fr,fc) for the position of the chosen pivot. 
                        (-1,-1) means no pivot was found.
                    - A tuple of actions to transform M in order to put
                    the pivot in the appropriate position.
                    - A set of new relations found during this pivot chosing.
        '''
        
        #sverbose("Looking for a new pivot from position (%d,%d)" %(ir,ic));
        relations = set();
        actions = [];
        end = False;
        fc = -1 ; fr = -1 ;
        ## Checking rows
        for cc in range(ic, M.ncols()):
            ## Checking columns
            for cr in range(ir, M.nrows()):
                #sverbose("Checking if position (%d,%d) is zero (%s)" %(cr,cc, M[cr][cc]));
                to_check = M[cr][cc];
                if(len(relations) > 0 ):
                    #sverbose("Reducing the selected element with the found relations");
                    to_check = M[cr][cc].reduce(relations);
                    #sverbose("New element to check: %s" %(to_check));
                    
                if(not to_check == self.parent().zero()):
                    if(not self.is_in_ideal(to_check)):
                        #sverbose("Non-zero element found. Pivot found");
                        end = True;
                        fr = cr;
                        break;
                    else:
                        #sverbose("Non trivial zero found. New relation: %s" %(to_check));
                        relations.add(to_check);
            
            if(end):
                fc = cc;
                break;
        
        if(fc != -1  and fc != ic):
            actions += [("sw_c", ic, cc)];
            for i in range(1 ,(min(cc-ic, M.ncols()-cc))):
                actions += [("sw_c", ic+i, M.ncols()-i)];
        
        if(fr != -1  and fr != ir):
            actions += [("sw_r", ir, cr)];
            
        #sverbose("Finished search of pivot: (%s,%s)" %(fr,fc));
                
        return ((fr,fc), tuple(actions), relations);
        
    def __bareiss(self, M, i):
        '''
            Method that applies a Bareiss reduction to the matrix M on the position (i,i).
            This method assumes that M[i][i] is a valid pivot for this reduction.

            The output matrix will preserve the structure of M for positions (j,k) with 
            j,k < i and will create zeros on the i-th column.

            A final reduction with gcds for each column is performed to keep the degrees
            of the polynomials as small as possible.

            These computations are not in-place, so the resulting matrix needs more
            memory allocation to be computed.

            INPUT:
                - M: matrix where we want perform the Bareiss reduction.
                - i: position where we have a pivot.
        '''
        rows = [];
        ## Reduction of the rows before i
        for j in range(i):
            if(M[j][i] != 0 ):
                rows += [[M[j][k]*M[i][i]-M[j][i]*M[i][k] for k in range(M.ncols())]];
            else:
                rows += [[M[j][k] for k in range(M.ncols())]];

        ## The i-th row remains the same as before
        rows += [[M[i][k] for k in range(M.ncols())]];

        ## Reduction of the rows after i
        for j in range(i+1 , M.nrows()):
            if(M[j][i] != 0 ):
                rows += [[M[j][k]*M[i][i]-M[j][i]*M[i][k] for k in range(M.ncols())]];
            else:
                rows += [[M[j][k] for k in range(M.ncols())]];
        
        ## GCD simplification of the rows
        try:
            gcds = [gcd(row) for row in rows];
            rows = [[el/gcd[i] for el in rows[i]] for i in range(len(rows))];
        except Exception:
            pass;
            
        return Matrix(self.parent(), rows);
        
    def __have_ideal(self, basis):
        '''
            Auxiliar method to know if some relation have been already found.

            This method returns True if the current Groebner basis we have computed
            gives some non-trivial ideal.
        '''
        if(len(basis) == 1 ):
            return basis[0 ] != 0 ;
        return len(basis) > 0 ;
        
    def __simplify_matrix(self, M):
        '''
            Method to simplify a polynomial matrix using the relations found.

            INPUT:
                - M: the matrix to simplify.
            OUTPUT:
                A matrix N such that N[i][j] is the reduction via the current
                Groebner basis (self.relations()) of M[i][j].
        '''
        rows = [[el for el in row] for row in M];
        if(self.__have_ideal(self.__gb)):
            rows = [[el.reduce(self.__gb) for el in row] for row in rows];
        
        return Matrix(self.parent(), rows);
        
    def __get_lcm(self, input):
        '''
            Auxiliar method for computing the lcm of a sequence.
        '''
        try:
            return lcm(input);
        except AttributeError:
            ## No lcm for this class, implementing a general lcm
            try:
                ## Relying on gcd
                p = self.__parent;
                res = p(1 );
                for el in input:
                    res = p((res*el)/gcd(res,el));
                return res;
            except AttributeError:
                ## Returning the product of everything
                return prod(input);
        
        

