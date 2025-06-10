from __future__ import annotations
r'''
    Module implementing ore operators in the context of :mod:`dalgebra`.

    Let `(R, (d_1,\ldots,d_n))` be a ring with operations `d_1,\ldots,d_n`, where `d_i` are differential, difference or skewed operations. Then we can consider the ring of ore operators `R[d_1,\ldots,d_n]`. These operators can be seen as multivariate non-commutative polynomials with coefficients in `R` and they can be applied in a natural way over any extension of `R`.

    The classical example is when `d_i` is a differential operator. In that case, we have the commutation rule `d_i \cdot f = f \cdot d_i + d_i(f)`, where `f` is an element in `R`. Another classical example are shift operators, leading to `d_i \cdot f = d_i(f) d_i`.

    This module will provide an implementation of ore operators in the context of :mod:`dalgebra`, allowing to build the ring of ore operators directly from the ring `R` and the operations that are already included in `R`. This module will also take care of other important aspects, such as the conversion between ore operators and different structures in SageMath, the application of operators to elements in `R` and some extension, and the creation of a Category and Parent structure suited for this types of operators.

    .. EXAMPLES::

        sage: from dd_functions.operators.doperators import DOperators
        sage: from dalgebra import *
        sage: R = DMonomial(DifferentialRing(QQ), (x,), (1,))
        sage: x = R.gen()
        sage: DR.<D> = DOperators(R)
        sage: D*x == x*D + 1
        True
        sage: R = DifferenceRing(DifferentialRing(QQ[x]), (1,)), ("x+1", ))
        sage: DSR.<D,S> = DOperators(R)
        sage: D*x == x*D + 1
        True
        sage: S*x == (x+1)*S
        True
        sage: D*S == S*D
        True
'''

import logging

from dalgebra.dring import AdditiveMap, DRings
from dalgebra.dpolynomial.dpolynomial import DPolynomial, DPolynomialRing_Monoid   

from sage.arith.misc import GCD as gcd
from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.functions.other import binomial
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.misc.misc_c import prod
from sage.rings.infinity import Infinity as oo
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection, Iterator

_DRings = DRings.__classcall__(DRings)


#####################################
### FACTORY CLASS
#####################################
class DOperatorsFactory (UniqueFactory):
    r'''
        Factory for creating ore operators in the context of :mod:`dalgebra`.

        This factory will create a :class:`DOperators` instance ensuring (with different criteria) that we only create one ring of operators for each ring `R` and the operations `d_1,\ldots,d_n`.
    '''
    def create_key(self, ring: Parent, *args: str, names: tuple[str] = None, category = None) -> tuple:
        r'''
            Create a key for the factory.

            For this factory, only the ring is necessary for the kay as well as the names we want to use for the operators.
            The arguments can be given as a tuple (in the keyword argument ``names``) or as a unnamed list of strings.
        '''
        # We check that the ring has operations
        if not ring in _DRings:
            raise ValueError(f"The ring {ring} is not a valid differential ring or difference ring.")
        elif isinstance(ring, DOperatorsRing):
            raise ValueError(f"The ring {ring} is already a ring of ore operators. Use the `change_ring` method to change its base ring.")
        
        # We normalize the input of names:
        # 1. If "names" is not given, we use the "args" as names.
        # 2. Otherwise, we omit the names given in "args" and use *only* the names given in "names".
        if names is None:
            names = args

        names = tuple(str(name) for name in names) # converting everything into string and ensuring a tuple
        if len(names) != ring.noperators():
            raise ValueError(f"The number of names {len(names)} does not match the number of operators {ring.noperators()} in the ring {ring}.")
        
        return (ring, names, category)
    
    def create_object(self, _, key) -> DOperatorsRing:
        ring, names, category = key
        return DOperatorsRing(ring, names, category=category)
    

DOperators = DOperatorsFactory("dd_functions.operators.doperators.DOperatorsFactory")

#####################################
### ELEMENT CLASS
#####################################
class DOperator (Element):
    r'''
        Class for ore operators in the context of :mod:`dalgebra`.

        This class is, essentially a sparse multivariate polynomial but with a non-commutative multiplication rule.
        We store the data as a sparse polynomial, i.e., we keep a dictionary with the non-zero coefficients and their corresponding monomial, where the monomial is represented as a tuple of integers indicating the order of each operator in the polynomial.
    '''
    def __init__(self, parent: DOperatorsRing, coefficients: dict[tuple[int], Element]):
        super().__init__(parent) # initialize the element class

        if not isinstance(coefficients, dict):
            raise TypeError(f"Coefficients must be a dictionary, got {type(coefficients)}.")
        
        # we make sure of format and remove zero coefficients
        coefficients = {tuple(int(i) for i in k): parent.base()(v) for (k, v) in coefficients.items() if v != 0}

        if any(len(mon) != parent.ngens() or any(e < 0 for e in mon) for mon in coefficients.keys()):
            raise ValueError(f"Monomial keys must be tuples of non-negative integers with length {parent.ngens()}, got {coefficients.keys()}.")
        self.__coefficients = coefficients  # Store the coefficients as a dictionary

    ## Getter and attribute methods
    def order(self, gen: str | int | DOperator = None) -> int:
        r'''
            Return the order of the operator.
            This is the maximum order of the operators in the coefficients.
        '''
        if gen is not None:
            if isinstance(gen, str):
                gen = self.parent().names().index(gen)
            elif isinstance(gen, DOperator):
                if gen.is_gen():
                    gen = self.parent().gens().index(gen)
                else:
                    raise ValueError(f"Cannot get the order of a non-generator operator {gen}.")
            if gen < 0 or gen >= self.parent().ngens():
                raise IndexError(f"Index {gen} out of range for operators in {self.parent()}.")
            return max((mon[gen] for mon in self.__coefficients.keys()), default=-oo)
        return max((sum(mon) for mon in self.__coefficients.keys()), default=-oo)
    
    @cached_method
    def monomials(self) -> tuple[DOperator]:
        r'''
            Return the monomials of the operator.
            This is a tuple of :class:`DOperator` instances, each representing a monomial in the operator.
        '''
        return tuple(self.parent().element_class(self.parent(), {mon: 1}) for mon in sorted(self.__coefficients.keys(), key=lambda x : (sum(x), x)))
    
    @cached_method
    def coefficient(self, monomial: tuple[int] | DOperator) -> Element:
        r'''
            Return the coefficient of the given monomial.
            If the monomial is not in the operator, it returns zero.
        '''
        if isinstance(monomial, DOperator):
            if not monomial.is_monomial():
                raise ValueError(f"Cannot get the coefficient of a non-monomial operator {monomial}.")
            monomial = next(iter(monomial.__coefficients.keys()))

        if len(monomial) != self.parent().ngens():
            raise ValueError(f"Monomial must be a tuple of length {self.parent().ngens()}, got {monomial}.")
        if any(i < 0 for i in monomial):
            raise ValueError(f"Monomial must be a tuple of non-negative integers, got {monomial}.")
        
        return self.__coefficients.get(monomial, self.parent().base().zero())
    
    @cached_method
    def coefficients(self) -> tuple[Element]:
        r'''
            Return the coefficients of the operator.
            This is a tuple of elements in the base ring, corresponding to the coefficients of the monomials in the operator.
        '''
        return tuple(self.coefficient(monomial) for monomial in self.monomials())

    def leading_coefficient(self) -> Element:
        r'''
            Return the leading coefficient of the operator.
            This is the coefficient of the monomial with the highest order.
            If there are no coefficients, it returns zero.
        '''
        if not self.__coefficients:
            return self.parent().base().zero()
        
        return self.coefficient(self.monomials()[-1])

    def constant_coefficient(self) -> Element:
        r'''
            Return the constant coefficient of the operator.
            This is the coefficient of the monomial with all orders zero.
            If there is no constant term, it returns zero.
        '''
        return self.coefficient(tuple(0 for _ in range(self.parent().ngens())))

    lc = leading_coefficient # Alias for leading_coefficient
    cc = constant_coefficient # Alias for constant_coefficient

    def __getitem__(self, monomial: tuple[int] | DOperator) -> Element:
        # slides are not allowed
        if monomial in ZZ and self.parent().ngens() == 1:
            monomial = (monomial,)
        return self.coefficient(monomial)

    def is_zero(self) -> bool:
        return not self.__coefficients

    def is_one(self) -> bool:
        r'''
            Check if the operator is the identity element.
            This is True if the operator has only one non-zero coefficient and that coefficient is 1.
        '''
        return self.is_monomial() and self.order() == 0

    def is_monomial(self) -> bool:
        return len(self.__coefficients) == 1 and next(iter(self.__coefficients.values())) == 1

    def is_gen(self) -> bool:
        r'''
            Check if the operator is a generator.
            This is True if the operator has only one non-zero coefficient and that coefficient is 1.
        '''
        return self.order() == 1 and self.is_monomial()

    def is_monic(self) -> bool:
        r'''
            Check if the operator is monic.
            This is True if the leading coefficient is 1.
        '''
        return self.lc() == 1
    
    def is_primitive(self) -> bool:
        r'''
            Checks whether an operator is primitive, i.e., it has no common factor with the base ring.
        '''
        return self.factor()[0] == 1

    def primitive(self) -> DOperator:
        r'''
            Returns the primitive part of the operator, i.e., the operator without common factors with the base ring.
        '''
        c, A, d = self.factor()
        return A * d

    def content(self) -> Element:
        r'''
            Returns the content of the operator, i.e., the greatest common divisor of the coefficients.
            This is a non-zero element in the base ring.
        '''
        return self.factor()[0]

    @cached_method
    def as_polynomial(self) -> Element:
        R = PolynomialRing(self.parent().base().to_sage(), self.parent().names())
        gens = R.gens()
        return sum(
            (coeff.to_sage() * prod(gens[i] ** mon[i] for i in range(len(mon))) for (mon, coeff) in self.__coefficients.items()),
            start=R.zero()
        )

    def to_sage(self) -> Element:
        raise NotImplementedError("Conversion to SageMath element is not implemented yet.")
    
    def conditions_to_zero(self) -> tuple[tuple[DOperator,Element]]:
        r'''
            Return the conditions that make the operator zero.
            This is a tuple of pairs (operator, condition) where the operator is the operator that must be applied to the element and the condition is the condition that must be satisfied for the operator to be zero.
        '''
        return tuple((m, c.to_sage()) for (m,c) in zip(self.monomials(), self.coefficients()))
    
    def lcm(self, *others: DOperator) -> DOperator:
        r'''
            Compute the least common multiple of the operator with other operators.
            This is not implemented yet, as it depends on the specific implementation of the base ring.
        '''
        raise NotImplementedError("The method lcm is not implemented yet.")
    
    ## Arithmetic methods
    def _add_(self, other: DOperator) -> DOperator:
        new_dict = self.__coefficients.copy()
        for (mon, coeff) in other.__coefficients.items():
            new_dict[mon] = coeff + new_dict[mon] if mon in new_dict else coeff

        return self.parent().element_class(self.parent(), new_dict) # this takes care of the zero coefficients
    
    def _neg_(self) -> DOperator:
        return self.parent().element_class(self.parent(), {mon: -coeff for (mon, coeff) in self.__coefficients.items()})
    
    def _sub_(self, other: DOperator) -> DOperator:
        return self + (-other)
    
    def _mul_(self, other: DOperator) -> DOperator:
        r'''
            Method that computes ``self * other`` for two ore operators.

            The multiplication is not commutative, so the order of multiplication matters. The rules for 
            computing the product is as follows:

            * If an operation is an homomorphism: `d \cdot f = d(f) \cdot d`.
            * If an operation is a derivation: `d \cdot f = f \cdot d + d(f)`.

            Hence we can apply these rules to compute the product of two operators where we put a coefficient 
            from the left and the monomial of operators to the right.    
        '''
        if self.is_zero() or other.is_zero():
            return self.parent().zero()
        elif self.is_one():
            return other
        elif other.is_one():
            return self

        output = dict() # dictionary to keep the coefficients of the output
        for (m1, a) in self.__coefficients.items():
            for (m2, b) in other.__coefficients.items():
                # we compute `a*m1 * b*m2 = a*((b))* ((m3))*m2`
                # so we first compute the part (m1*b)
                mons = tuple([(b,tuple())])
                for i,otype in enumerate(self.parent().operator_types()): # we iterate through the operations
                    new_mons = []    
                    if otype == "derivation":
                        for (c,m) in mons:
                            for j in range(m1[i]+1):
                                new_mons.append((binomial(m1[i], j)*c.operation(i, j), m+(m1[i] - j,)))
                    elif otype == "homomorphism":
                        for (c,m) in mons:
                            new_mons.append((c.operation(i, m1[i]), m+(m1[i],)))
                    elif otype == "skew":
                        raise NotImplementedError("The method _mul_ is not implemented for skew operators yet.")
                    else:
                        raise ValueError(f"Unknown operator type {otype} in {self.parent()}.")
                    mons = tuple(el for el in new_mons if el[0] != 0)

                # now we multiply the coefficients by `a` and the monomials by `m2`
                for (c, m3) in mons:
                    new_mon = tuple(m3[i] + m2[i] for i in range(len(m2)))
                    output[new_mon] = output[new_mon] + a*c if new_mon in output else a*c
                       
        return self.parent().element_class(self.parent(), output)
    
    @cached_method
    def __pow__(self, power: int) -> DOperator:
        if power == 0:
            return self.parent().one()
        elif power == 1:
            return self
        elif power < 0:
            raise ValueError(f"Negative powers are not allowed for operators, got {power}.")
        else:
            return self ** (power//2 + power %2) * self**(power//2)    

    def _div_(self, other: DOperator) -> DOperator:
        try:
            return self.exact_div(other)
        except (NotImplementedError,ValueError):
            return NotImplemented

    def exact_div(self, other: DOperator) -> DOperator:
        if self.parent().noperators() != 1:
            raise NotImplementedError("The method _div_ is not implemented for rings with more than one operator.")
        ## Case with 1 operation
        if self.parent().base().is_field():
            q, r = self.quo_rem(other)
            if r.is_zero():
                return q
            else:
                raise ValueError(f"Cannot divide {self} by {other} in {self.parent()}. The remainder is not zero: {r}.")
        else:
            m,q,r = self.pseudo_quo_rem(other)
            if not r.is_zero():
                raise ValueError(f"Cannot divide {self} by {other} in {self.parent()}. The pseudo-remainder is not zero: {r}.")
            elif q.content() % m != 0:
                raise ValueError(f"Cannot divide {self} by {other} in {self.parent()}. The pseudo-quotient is not divisible by the content {m}.")
            else:
                ## We do the exact division on the coefficients
                return self.parent().element_class(self.parent(),
                    {
                        mon : coeff // m # we are guaranteed this division is exact
                        for (mon, coeff) in q.__coefficients.items()
                    }
                )

    def _floordiv_(self, other: DOperator) -> DOperator:
        try:
            return self.floor_div(other)
        except (NotImplementedError, ValueError):
            return NotImplemented
    
    def _mod_(self, other: DOperator) -> DOperator:
        try:
            return self.mod(other)
        except NotImplementedError:
            return NotImplemented

    def floor_div(self, other: DOperator) -> DOperator:
        if self.parent().noperators() != 1:
            raise NotImplementedError("The method _div_ is not implemented for rings with more than one operator.")
        ## Case with 1 operation
        if self.parent().base().is_field():
            return self.quo_rem(other)[0]
        else:
            m,q,_ = self.pseudo_quo_rem(other)
            if q.content() % m != 0:
                raise ValueError(f"Cannot divide {self} by {other} in {self.parent()}. The pseudo-quotient is not divisible by the content {m}.")
            
            else:
                ## We do the exact division on the coefficients
                return self.parent().element_class(self.parent(),
                    {
                        mon : coeff // m # we are guaranteed this division is exact
                        for (mon, coeff) in q.__coefficients.items()
                    }
                )
            
    def mod(self, other: DOperator) -> DOperator:
        if self.parent().noperators() != 1:
            raise NotImplementedError("The method _div_ is not implemented for rings with more than one operator.")
        ## Case with 1 operation
        if self.parent().base().is_field():
            return self.quo_rem(other)[1]
        else:
            m,_,r = self.pseudo_quo_rem(other)
            if r.content() % m != 0:
                raise ValueError(f"Cannot divide {self} by {other} in {self.parent()}. The pseudo-quotient is not divisible by the content {m}.")
            
            else:
                ## We do the exact division on the coefficients
                return self.parent().element_class(self.parent(),
                    {
                        mon : coeff // m # we are guaranteed this division is exact
                        for (mon, coeff) in r.__coefficients.items()
                    }
                )

    def quo_rem(self, other: DOperator) -> tuple[DOperator, DOperator]:
        if self.parent().noperators() != 1 or (not self.parent().base().is_field()): 
            raise NotImplementedError("The method quo_rem is not implemented for non-field rings or rings with more than one operator.")

        ## Checking arguments
        if self.is_zero():
            return (self.parent().zero(), self)
        elif other.is_zero():
            raise ZeroDivisionError(f"Cannot divide by zero operator {other} in {self.parent()}.")
        elif other.is_one():
            return (self, self.parent().zero())
        
        ## Usual Euclidean algorithm
        b = other.lc()
        D = self.parent().gen(0)
        q, r = self.parent().zero(), self
        while r.order() >= other.order():
            to_add = r.lc()/b * D**(r.order() - other.order()) # division allowed since we are in a field
            r -= to_add * other # This reduces the order of r at least by one
            q += to_add # we update the quotient

        return (q,r) # Return the quotient and the remainder

    def pseudo_quo_rem(self, other: DOperator) -> tuple[Element, DOperator, DOperator]:
        r'''
            Computes the pseudo-quotient and remainder of the operator with respect to another operator.

            This method computes the pseudo-quotient and remainder of the operator ``self`` with respect to the operator ``other``. The pseudo quotient is an operator `Q` such that `m*self = Q*other + R` where `R` (the pseudo-remainder) is an operator with lower order than `other`. On the other hand, `m` is an element in the base ring.
        '''
        if self.parent().noperators() != 1:
            raise NotImplementedError("The method pseudo_quo_rem is not implemented for rings with more than one operator.")
        
        if self.parent() != other.parent():
            R = pushout(self.parent(), other.parent())
            return R(self).pseudo_quo_rem(R(other))

        ## Checking the arguments
        if self.is_zero():
            return (self.parent().base().zero(), self, self)
        elif other.is_zero():
            raise ZeroDivisionError(f"Cannot divide by zero operator {other} in {self.parent()}.")
        elif other.is_one():
            return (self.parent().base().one(), self, self.parent().zero())
        elif other.order() > self.order():
            return (self.parent().base().one(), self.parent().one(), self)
        
        D = self.parent().gen(0)  
        alphas = [self.content()]
        lc_R = []
        R = self.primitive()
        orders = []
        gamma = 0
        
        while R.order() >= other.order():
            lc_R.append(R.lc()) 
            orders.append(R.order() - other.order()) # orders[-1] >= 0
            T = other.lc()*R - lc_R[-1]*D**orders[-1] * other
            alphas.append(T.content())
            R = T.primitive()
            gamma += 1
        
        return (other.lc()**gamma, 
                sum(other.lc()**(gamma-i-1) * alphas[i]*lc_R[i]*D**orders[i] for i in range(len(orders))), 
                prod(alphas)*R
        )
    
    def gcrd(self, other: DOperator) -> DOperator:
        r'''
            Method to compute the greatest common right divisor of two ore operators.

            The greatest common right divisor (gcrd) of two ore operators `self` and `other` is the operator `g` such that `g` divides both `self` and `other`, and any other operator that divides both `self` and `other` also divides `g`. This is computed using the pseudo-quotient and remainder method.
        '''
        if self.parent().noperators() != 1:
            raise NotImplementedError("The method gcrd is not implemented for rings with more than one operator.")
        
        if self.parent() != other.parent():
            R = pushout(self.parent(), other.parent())
            return R(self).gcrd(R(other))

        if self.is_zero():
            return other
        elif self.order() < other.order():
            return other.gcrd(self)
        else:
            r = (self.quo_rem(other) if self.parent().base().is_field() else self.pseudo_quo_rem(other))[-1]
            if r.is_zero():
                return other
            return other.gcrd(r)

    @cached_method
    def factor(self) -> tuple[Element, DOperator, DOperator]:
        r'''
            Computes a simple factorization of the operator in the form `c * A * d`

            This method computes a simple factorization of the operator ``self`` in the form `c * A * d`, where
            * `c` is an element of self.parent().base().
            * `A` is an :class:`DOperator` with constant coefficient different from zero
            * `d` is a monomial operator.
        ''' 
        # Getting the value for `c`
        c = gcd(self.__coefficients.values())

        # Getting the operator `d`
        d_tuple = tuple(min(m[i] for m in self.__coefficients.keys() for i in range(self.parent().ngens())))
        d = self.parent().element_class(self.parent(), {d_tuple: 1})

        # Computing the operator `A`
        A = self.parent().element_class(self.parent(),
                                        {
                                            tuple(m[i] - d_tuple[i] for i in range(self.parent().ngens())): coeff // c
                                            for (m, coeff) in self.__coefficients.items()
                                        })
        
        return (c, A, d)
    
    def __eq__(self, other: DOperator) -> DOperator:
        return (self - other).is_zero()
    def __ne__(self, other: DOperator) -> DOperator:
        return not (self == other)
    
    ## Functional methods
    def __hash__(self) -> int:
        return hash(tuple(sorted(self.__coefficients.items(), key=lambda x: (sum(x[0]), x[0]))))
        
    def __call__(self, element: Element) -> DOperator:
        return sum(
            (coeff * element.operations(mon) for (mon, coeff) in self.__coefficients.items()),
            start=self.parent().zero()
        )
    
    ## Representation methods
    def __repr__(self) -> str:
        return repr(self.as_polynomial())

    def _latex_(self) -> str:
        return latex(self.as_polynomial())

#####################################
### PARENT CLASS
#####################################
class DOperatorsRing (Parent):
    Element = DOperator

    def _set_categories(self, base : Parent, category=None) -> list[Category]:
        return [_DRings, Algebras(base)] + ([category] if category is not None else [])
    
    def __init__(self, base: Parent, names: tuple[str] = None, category=None):
        if not base in _DRings: # Ensure the base is a valid differential or difference ring
            raise ValueError(f"The base {base} is not a valid differential ring or difference ring.")
        elif len(names) != base.noperators():
            raise ValueError(f"The number of names {len(names)} does not match the number of operators {base.noperators()} in the base ring {base}.")
        
        ## Caller the super __init__ to stablish the categories and the main attributes
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        ## Variables for cached attributes
        self.__names = tuple(str(name) for name in names)  # Ensure names are strings
        self.__gens = None
        self.__operators = None
        
        self._initialize_operators()

    def _initialize_operators(self):
        r'''
            Initialize the operators for this ring.
            This will create the operators as elements of the ring.
        '''
        self.__operators = tuple(AdditiveMap(self, lambda x : self.gen(i) * x) for i in range(len(self.__names)))
    
    ## Attribute methods
    @cached_method
    def names(self) -> tuple[str]:
        return tuple(self.__names)

    def gens(self) -> tuple[DOperator]:
        r'''
            Return the generators of the ring of ore operators.
            These are the operators defined in the ring.
        '''
        if self.__gens is None:
            self.__gens = tuple(
                self.element_class(
                    self, 
                    {
                        tuple(1 if i == j else 0 for j in range(self.ngens())): 1 
                    }
                )
                for i in range(self.ngens())
            )
        return self.__gens
    
    def gen(self, name: str | int) -> DOperator:
        r'''
            Return the operator with the given name or index.
            If the name is not found, it raises a KeyError.
        '''
        if isinstance(name, int):
            if name < 0 or name >= len(self.__names):
                raise IndexError(f"Index {name} out of range for operators in {self}.")
        elif isinstance(name, str):
            if name not in self.__names:
                raise KeyError(f"Operator '{name}' not found in {self}.")
            name = self.__names.index(name)
        else:
            raise TypeError(f"Name must be a string or an integer, got {type(name)}.")
        return self.gens()[name]
    
    def ngens(self) -> int:
        r'''
            Return the number of generators (operators) in the ring.
        '''
        return len(self.__names)

    def one(self) -> DOperator:
        r'''
            Return the identity element of the ring of ore operators.
            This is the operator with all coefficients zero except for the constant term.
        '''
        return self.element_class(self, {(0 for i in range(len(self.__names))): 1})
    
    def zero(self) -> DOperator:
        r'''
            Return the zero element of the ring of ore operators.
            This is the operator with all coefficients zero.
        '''
        return self.element_class(self, dict())
    
    def is_field(self) -> bool:
        r'''
            Check if the ring of ore operators is a field.
            This is always False for ore operators, as they are not fields.
        '''
        return False
    
    def is_integral_domain(self) -> bool:
        r'''
            Check if the ring of ore operators is an integral domain.
            This depends directly from the base ring, since the ore operators are a domain if and only if their coefficients are an integral domain.
        '''
        return self.base().is_integral_domain() 
    
    ## Coercion methods
    def _coerce_map_from_base_ring(self) -> DOp_BaseToParent:
        r'''
            Coercion from the base ring to the ring of ore operators.
            This is not implemented yet, as it depends on the specific implementation of the base ring.
        '''
        return DOp_BaseToParent(self)
    
    def construction(self) -> tuple[ConstructionFunctor, Parent]:
        r'''
            Return the functor that creates the ring of ore operators and the base ring.
            This is used to create the ring of ore operators from the base ring and the operations.
        '''
        return DOperatorsFunctor(self.__names), self.base()
    
    def fraction_field(self) -> None:
        raise TypeError("The ring of ore operators does not have a fraction field.")

    def change_ring(self, new_base: Parent) -> DOperatorsRing:
        r'''
            Change the base ring of the ring of ore operators.
            This will create a new ring of ore operators with the same operators but with the new base ring.
        '''
        if not new_base in _DRings:
            raise ValueError(f"The new base {new_base} is not a valid differential ring or difference ring.")
        
        new_ring = DOperators(new_base, names=self.__names, category=self.category())
        # coercion new -> old
        coercion = self.base().coerce_map_from(new_base)
        if coercion is not None:
            self.register_coercion(DOp_BetweenBases(new_ring, self, coercion))
        # coercion old -> new
        coercion = new_ring.base().coerce_map_from(self.base())
        if coercion is not None:
            new_ring.register_coercion(DOp_BetweenBases(self, new_ring, coercion))
        # conversion new -> old
        conversion = self.base().convert_map_from(new_base)
        if conversion is not None:
            self.register_conversion(DOp_BetweenBases(new_ring, self, conversion))
        # conversion old -> new
        conversion = new_ring.base().convert_map_from(self.base())
        if conversion is not None:
            new_ring.register_conversion(DOp_BetweenBases(self, new_ring, conversion))
        
        return new_ring

    # Representation methods
    def __repr__(self) -> str:
        r'''
            Return a string representation of the ring of ore operators.
            This will include the base ring and the names of the operators.
        '''
        return f"Ore Operators of {self.base()} with operators {self.__names}"
    
    def _latex_(self) -> str:
        r'''
            Return a LaTeX representation of the ring of ore operators.
            This will include the base ring and the names of the operators.
        '''
        return f"{self.base().to_sage()._latex_()}\\langle{','.join(self.__names)}\\rangle"
    
    # DRing category methods
    def operators(self) -> Collection[AdditiveMap]:
        return self.__operators
    
    def operator_types(self) -> tuple[str]:
        r'''
            Return the types of the operators in the ring.
        '''
        return self.base().operator_types()
    
    def add_constants(self, *new_constants: str) -> DOperatorsRing:
        r'''
            Add new constant coefficients to the ring of ore operators.
            This will create a new ring of ore operators with the new constants.
        '''
        new_base = self.base().add_constants(*new_constants)
        return self.change_ring(new_base)

    def constant_ring(self, operation: int = 0) -> Parent:
        return self.base().constant_ring(operation)
    
    def linear_operator_ring(self) -> DOperatorsRing:
        r'''
            Return the ring of linear operators.
        '''
        return self
    
    def to_sage(self) -> Parent:
        r'''
            Return the SageMath parent of the ring of ore operators.
            This is used to convert the ring to a SageMath structure.
        '''
        raise NotImplementedError("Conversion to SageMath parent is not implemented yet.")

#####################################
### FUNCTOR CLASS
#####################################
class DOperatorsFunctor (ConstructionFunctor):
    r'''
        Class for a functor that creates the ring of ore operators given a ring with operations.

        It receives the names for the operators (i.e., the variables of the ore operators) as a tuple of strings.
    '''
    def __init__(self, names: tuple[str]):
        super().__init__(_DRings, _DRings)

        self.rank = 12 # same as DPolyRingFunctor

        self.__names = names

    def _apply_functor(self, x: Parent) -> DOperatorsRing:
        return DOperators(x, names=self.__names)
    
    def _repr_(self) -> str:
        return f"DOreOperators(*, names={self.__names})"
    
    def __eq__(self, other: DOperatorsFunctor) -> bool:
        if not isinstance(other, DOperatorsFunctor):
            return False
        return set(self.__names) == set(other.__names)


#####################################
### MORPHISM CLASSES
#####################################
### COERCIONS / CONVERSIONS MORPHISMS
class DOp_ParentToBase (Morphism):
    r'''
        Conversion from the :class:`DOperatorsRing` to its base ring.
    '''
    def __init__(self, domain: DOperatorsRing):
        super().__init__(domain, domain.base())

    def _call_(self, element: DOperator) -> Element:
        if not element.order() == 0:
            raise ValueError(f"Cannot convert a non-zero order operator {element} to its base ring {self.codomain()}.")
        
        return element.constant_coefficient()
    

class DOp_BaseToParent (Morphism):
    r'''
        Coercion from the base ring to the :class:`DOperatorsRing`.
    '''
    def __init__(self, codomain: DOperatorsRing):
        super().__init__(codomain.base(), codomain)

    def _call_(self, element: Element) -> DOperator:
        return self.codomain().element_class(self.codomain(), {(0 for _ in range(self.codomain().ngens())): element})


class DOp_OperatorsToPolynomials(Morphism): 
    r'''
        Coercion from the :class:`DOperatorsRing` to a ring of DPolynomials (see :class:`dalgebra.dpolynomial.dpolynomial.DPolynomial`)
    '''
    def __init__(self, domain: DOperatorsRing, codomain: DPolynomialRing_Monoid, op_var: str = None):
        self.__v = domain.gen(op_var) if op_var is not None else domain.gens()[0]
        self.__coeff_map = codomain.base().coerce_map_from(domain.base())

        super().__init__(domain, domain, codomain)

    def _call_(self, element: DOperator) -> DPolynomial:
        return sum(
            (self.__coeff_map(coef) * self.__v[i] for (i, coef) in element.items()),
            start=self.codomain().zero()
        )


class DOp_PolynomialsToOperators(Morphism):
    r'''
        Conversion from a ring of DPolynomials (see :class:`dalgebra.dpolynomial.dpolynomial.DPolynomial`) to the :class:`DOperatorsRing`.
    '''
    def __init__(self, domain: DPolynomialRing_Monoid, codomain: DOperatorsRing, op_var: str = None):
        self.__v = domain.gen(op_var) if op_var is not None else domain.gens()[0]
        self.__coeff_map = codomain.base().coerce_map_from(domain.base())

        super().__init__(domain, codomain)

    def _call_(self, element: DPolynomial) -> DOperator:
        if not element.degree(self.__v) == 1:
            raise ValueError(f"Cannot convert a non-linear operator {element} to the DOperatorsRing {self.codomain()}.")
        
        raise NotImplementedError("Conversion from DPolynomials to DOperatorsRing is not implemented yet.")


class DOp_BetweenBases(Morphism):
    r'''
        Conversion between two :class:`DOperatorsRing` instances with different base rings.
    '''
    def __init__(self, domain: DOperatorsRing, codomain: DOperatorsRing, base_map: Morphism = None):
        super().__init__(domain, codomain)

        self.__base_map = codomain.base().coerce_map_from(domain.base()) if base_map is None else base_map
    
    def _call_(self, element: DOperator) -> DOperator:
        return self.codomain().element_class(
            self.codomain(),
            {
                mon: self.__base_map(coeff)
                for (mon, coeff) in element._DOperator__coefficients.items()
            }
        )
            

__all__ = ["DOperators", "DOperator"]