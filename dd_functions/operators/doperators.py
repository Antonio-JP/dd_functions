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

from dalgebra import DRings
from dalgebra.dpolynomial.dpolynomial import DPolynomial, DPolynomialRing_Monoid   

from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

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
        return DOperatorsFactory(ring, names, category=category)
    

DOperators = DOperatorsFactory("dd_functions.operators.doperators.DOperatorsFactory")

#####################################
### ELEMENT CLASS
#####################################
class DOperator (Element):
    pass


#####################################
### PARENT CLASS
#####################################
class DOperatorsRing (Parent):
    Element = DOperator

    def _set_categories(self, base : Parent, category=None) -> list[Category]:
        return [_DRings, Algebras(base)] + ([category] if category is not None else [])
    

#####################################
### FUNCTOR CLASS
#####################################
class DOperatorsFunctor (ConstructionFunctor):
    pass


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
        raise NotImplementedError("Coercion from base ring to DOperatorsRing is not implemented yet.")


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
        raise NotImplementedError("Conversion between two DOperatorsRing instances is not implemented yet.")
    

__all__ = ["DOperators", "DOperator"]