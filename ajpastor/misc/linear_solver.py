r"""
Python file for an implementation of linear solver.

This module offers an abstract class that represents a solver for a linear system. This
class stablish a common interface for all the linear solvers that can be used. 

This module also includes one toy implementation that uses Sage solving methods to compute
the solutions to a linear system with coefficients in integral domains (since we build the
field of fractions).

AUTHORS:

    - Antonio Jimenez-Pastor (2021-02-09): initial version

"""

# ****************************************************************************
#  Copyright (C) 2021 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************
from sage.all import Matrix, vector, ideal, cached_method
import sage.structure.element as SAGE_element
from sage.categories.pushout import pushout

from ajpastor.misc.ring_w_sequence import Wrap_w_Sequence_Ring

class NoSolutionError(ValueError):
    pass

class LinearSystemSolver():
    r'''
        Generic class for solving a linear system.

        The methods described in this class are an interface that all
        the subclasses must implement. This allow the user to change between 
        algorithms very easily since all the information that can be extracted
        has always the same format.

        A linear system is always given in the form

        .. MATH::

            A \alpha = \mathbf{b},

        where `A` is a matrix of size `n\times m` with coefficients in a ring `R`,
        `\mathbf{b}` is the inhomogeneous term, i.e., a column vector of size `n` also 
        with entries in the ring `R`) and `\alpha` a column vector of size `m` that
        represents the unknowns of the system.
    '''
    def __init__(self, parent, matrix, inhomogeneous, is_zero=lambda p : False, relations=[]):
        ## Checking the input of matrix and vector
        if(not SAGE_element.is_Matrix(matrix)):
            matrix = Matrix(matrix)
        
        if(not SAGE_element.is_Vector(inhomogeneous)):
            inhomogeneous = vector(inhomogeneous)

        if(isinstance(parent, Wrap_w_Sequence_Ring)):
            parent = parent.base()
        
        ## Building the parent of the matrix and the vector
        pmatrix = matrix.parent().base()
        pinhom = inhomogeneous.parent().base()

        ## Setting the variables for the matrix, the parent and the vector
        self.__parent = pushout(pmatrix, pinhom)
        self.__matrix = matrix.change_ring(self.__parent)
        self.__inhomogeneous = inhomogeneous.change_ring(self.__parent)

        ## Setting the parent for the solutions
        if(not pushout(parent, self.__parent) == parent):
            try:
                self.__matrix = self.__matrix.change_ring(parent)
                self.__inhomogeneous = self.__inhomogeneous.change_ring(parent)
                self.__parent = parent
            except:
                raise TypeError("The parent for the solutions must be an extension of the parent for the input")
        self.__solution_parent = parent

        ## Setting other variables
        if(relations is None):
            relations = []
        self.__relations = [self.__parent(el) for el in relations]
        try:
                self.__gb = ideal(self.parent(), self.__relations).groebner_basis()
        except AttributeError:
            try:
                self.__gb = [ideal(self.parent(), self.__relations).gen()]
            except:
                self.__gb = [0]

        self.__is_zero = is_zero

        ## Creating the variables for the echelon form
        self.__echelon = None
        self.__transformation = None

        ## Creating the variables for the solutions
        self.__solution = None
        self.__syzygy = None

    def parent(self):
        r'''
            Method that returns the ring `R` where the system is defined.

            The matrix `A` and the vector `\mathbf{b}` have their coefficients in a 
            common ring (or at least in rings where Sage can compute the *pushout*). This
            method returns such ring. This ring may be different from the ring where we look for 
            solutions to the system `A\alpha = \mathbf{b}`, but it will always be included
            in it.

            In order to know the ring where the solutions are searched, see the method 
            :func:`~LinearSystemSolver.solution_parent`. 
        '''
        return self.__parent

    def solution_parent(self):
        r'''
            Method that returns the ring where the solutions to the system are searched.

            The matrix `A` and the vector `\mathbf{b}` have their coefficients in a 
            common ring (or at least in rings where Sage can compute the *pushout*). This 
            ring may be different from the ring where we look for 
            solutions to the system `A\alpha = \mathbf{b}`, but it will always be included
            in it. This method returns that ring where we look for solutions.

            In order to know the ring of the matrix `A` and vector `\mathbf{b}`, see the method 
            :func:`~LinearSystemSolver.parent`. 
        '''
        return self.__solution_parent

    def system_matrix(self):
        r'''
            Method that returns the matrix of the linear system.

            This method returns the original matrix provided to present the linear 
            system. 
        '''
        return self.__matrix

    def inhomogeneous(self):
        r'''
            Method that returns the inhomogeneous vector of the linear system.

            This method returns the original inhomogeneous vector provided to present the linear 
            system. 
        '''
        return self.__inhomogeneous

    def relations(self):
        r'''
            Method to get the current known relations in the ring.
        '''
        return self.__gb

    def have_ideal(self):
        r'''
            Auxiliary method to know if some relation have been already found.

            This method returns ``True`` if the current Groebner basis we have computed
            gives some non-trivial ideal.
        '''
        if(len(self.__gb) == 1):
            return self.__gb[0] != 0
        return len(self.__gb) > 0

    def echelon_form(self):
        r'''
            Method that returns the echelon form of the system matrix.

            This method returns the echelon form computed by the current algorithm in order to solve
            the linear system. The structure of this matrix is highly dependent on the algorithm
            and it can be upper-triangular, lower-triangular, diagonal, etc.
        '''
        if(self.__echelon is None):
            self.__echelon, self.__transformation = self._compute_echelon()
        return self.__echelon

    def transformation_matrix(self):
        r'''
            Method that returns the transformation matrix of the system

            This method returns a square matrix `U` that transforms the linear system
            matrix into the echelon form. This means that if `H` is the echelon form
            of the system matrix `A`, then
            
            .. MATH::

                UA = H

            This matrix is computed simultaneously to the echelon form of the system.
        '''
        if(self.__transformation is None):
            self.__echelon, self.__transformation = self._compute_echelon()
        return self.__transformation
        
    @cached_method
    def rank(self):
        r'''
            Method that returns the rank of the system matrix.

            This methods returns the rank of the system matrix. This rank is the maximal number of rows
            of the system that are linearly independent. This number usually defines the dimension
            of the solution space of the system.
        '''
        for i in range(self.H.nrows()):
            if(all(self.is_zero(el) for el in self.H.row(i))):
                return i
        return self.H.nrows()

    def is_homogeneous(self):
        r'''
            Method that return whether the system is homogeneous or not.

            This method checks if all the elements in the vector `\mathbf{b}` are zero.
            This checking may lead to more relations on the system considered and will be added, 
            as expected, in the relation ideal that the algorithm have.
        '''
        are_zero = (self.is_zero(el) for el in self.inhomogeneous())
        return all(are_zero)

    def solution(self):
        r'''
            Method that returns a particular solution to the linear system.

            This method computes a particular vector `\alpha` that solves 
            the linear system `A\alpha = \mathbf{b}` in the parent given
            by :func:`LinearSystemSolver.solution_parent`. 
        '''
        if(self.__solution is None):
            self.__solution, self.__syzygy = self._compute_solution()
        return self.__solution

    def syzygy(self):
        r'''
            Method that returns the solution space for the homogeneous system.

            Given a linear system `A\alpha = \mathbf{b}`, it is clear that 
            for any two solutions `\alpha_1,\alpha_2` we have that its difference
            is a solution to the homogeneous linear system `A\beta = \mathbf{0}`.

            This method computes the solution space of the homogeneous system and
            return it as a matrix `S` of size `m\times p` where `m` is the number
            of columns of `A` and `p` the dimension of the solution space. Hence, 
            any solution to the original system can be written as

            .. MATH::

                \alpha_0 + S\beta

            where `\alpha_0` is a particular solution to the linear system `A\alpha_0 = \mathbf{b}`
            and `\beta` is any vector with entries in the parent for the solutions.
        '''
        if(self.__solution is None):
            self.__solution, self.__syzygy = self._compute_solution()
        return self.__syzygy

    @cached_method
    def is_zero(self, el):
        r'''
            Method to check whether an element is the zero element or not.

            This method computes the real value of ``el`` and checks if it is zero
            or not regardless of its representation. In case the elements was not
            trivial, we add it to the ideal of relations and update the Gröbner basis.
        '''
        el = self.simplify(el) #simplify el (if needed)

        ## Trivial checking
        if(el == 0):
            return True

        if(self.__is_zero(el)): ## If it is zero, we update the relations
            self.__relations += [el]
            try:
                self.__gb = ideal(self.parent(), self.__relations).groebner_basis()
            except AttributeError:
                try:
                    self.__gb = [ideal(self.parent(), self.__relations).gen()]
                except:
                    self.__gb = [0]
            return True
        return False

    def simplify(self, obj):
        r'''
            Method to simplify an object using the relations found.

            This method simplifies an object (either an element, vector, list, tuple or matrix)
            using the relations that we found during the computation of the solutions of this linear
            system.

            WARNING: repeated executions of this method may return different outputs since we may have
            found more relations.
        '''
        if(SAGE_element.is_Matrix(obj)):
            return Matrix(obj.parent().base(), [[self.simplify(el) for el in row] for row in obj])
        elif(SAGE_element.is_Vector(obj)):
            return vector(obj.parent().base(), [self.simplify(el) for el in obj])
        elif(isinstance(obj, list)):
            return [self.simplify(el) for el in obj]
        elif(isinstance(obj, tuple)):
            return tuple([self.simplify(el) for el in obj])
        elif(self.have_ideal()):
            return obj.reduce(self.__gb)
        return obj
    ## Alias properties
    @property
    def A(self):
        r'''
            Alias for :func:`~LinearSystemSolver.system_matrix`
        '''
        return self.system_matrix()
    
    @property
    def b(self):
        r'''
            Alias for :func:`~LinearSystemSolver.inhomogeneous`
        '''
        return self.inhomogeneous()

    @property
    def H(self):
        r'''
            Alias for :func:`~LinearSystemSolver.echelon_form`
        '''
        return self.echelon_form()
    
    @property
    def U(self):
        r'''
            Alias for :func:`~LinearSystemSolver.transformation_matrix`
        '''
        return self.transformation_matrix()

    ## ABSTRACT METHODS
    def _compute_echelon(self):
        r'''
            Method that actually computes the echelon matrix and the transformation matrix.
        '''
        raise NotImplementedError("Abstract method not implemented in %s" %self.__class__)

    def _compute_solution(self):
        r'''
            Method that actually computes the solution space of the linear system.
        '''
        raise NotImplementedError("Abstract method not implemented in %s" %self.__class__)

    ## PRIVATE METHODS
class SageSolver(LinearSystemSolver):
    r'''
        Toy implementation of a :class:`LinearSystemSolver`.

        This class is a simple example on how to implement specific classes
        for :class:`LinearSystemSolver`. This class uses Sage method to compute
        the solutions, the echelon form, etc.

        WARNING (:trac:`23715`): sometimes, the 
        method echelon_form ignore the transformation argument, so the output
        is None.
    '''
    def __init__(self, parent, matrix, inhomogeneous):
        if(not(parent.is_field())):
            parent = parent.fraction_field()
        super().__init__(parent, matrix, inhomogeneous)

    def _compute_echelon(self):
        solution = self.A.echelon_form(transformation=True)
        if(isinstance(solution,tuple)):
            return solution[0],solution[1]
        return solution, None

    def _compute_solution(self):
        if(self.is_homogeneous()):
            solution = vector(self.solution_parent(), self.A.ncols()*[0])
        else:
            try:
                solution = self.A.solve_right(self.b).change_ring(self.solution_parent())
            except ValueError: #There is no solution
                raise NoSolutionError("The system has no solutions")
        syzygy = self.A.right_kernel_matrix().change_ring(self.solution_parent())
        return solution, syzygy.transpose()
