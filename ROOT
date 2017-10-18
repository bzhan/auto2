chapter AUTO2

session HOL_Base = HOL +
  description {*
    Theories in HOL needed by AUTO2.
  *}
  theories
    "../src/HOL/Library/Multiset"
    "../src/HOL/Imperative_HOL/Imperative_HOL"

session AUTO2 = HOL_Base +
  description {*
    AUTO2 definitions.
  *}
  theories
    "HOL/Auto2_Test"
    "HOL/Pelletier"

session Primes = AUTO2 +
  description {*
    Examples in number theory.
  *}
  theories
    "HOL/Primes_Ex"

session Hoare = AUTO2 +
  description {*
    Examples in Hoare logic.
  *}
  theories
    "HOL/Hoare/Hoare_Exp"
    "HOL/Hoare/Hoare_Equiv"
    "HOL/Hoare/Hoare_Rules"

session SepLogic_Base = AUTO2 +
  description {*
    Base of separation logic.
  *}
  theories
    "HOL/SepLogic/Hoare_Triple"

session SepLogic_BasicStr = SepLogic_Base +
  description {*
    Separation logic: basic data structures.
  *}
  theories
    "HOL/SepLogic/LinkedList"
    "HOL/SepLogic/BST_Impl"

session SepLogic_Arrays = SepLogic_Base +
  description {*
    Separation logic: algorithms on arrays.
  *}
  theories
    "HOL/SepLogic/Reverse"
    "HOL/SepLogic/Quicksort"

session SepLogic_Rectinter = SepLogic_Arrays +
  description {*
    Separation logic: rectangle intersection.
  *}
  theories
    "HOL/SepLogic/Rect_Intersect_Impl"

session SepLogic_RBT = SepLogic_Base +
  description {*
    Separation logic: red-black tree.
  *}
  theories
    "HOL/SepLogic/RBT_Impl"

session SepLogic_UnionFind = SepLogic_Base +
  description {*
    Union-find and applications.
  *}
  theories
    "HOL/SepLogic/Percolation"

session SepLogic_Graph = SepLogic_Base +
  description {*
    Graph theory.
  *}
  theories
    "HOL/SepLogic/Dijkstra"

session Auto2_FOL = FOL +
  description {*
    Example in first order logic.
  *}
  theories
    "FOL/Pelletier"
    "FOL/BigProd"
    "FOL/WellOrder"
    "FOL/SetSum"
    "FOL/Coset"
    "FOL/Abs"
    "FOL/Finite"
    "FOL/Divides"
    "FOL/Rat"
    "FOL/Lattice"

session FOL_Real = Auto2_FOL +
  description {*
    Real numbers in first order logic.
  *}
  theories
    "FOL/Real"

session FOL_Topology = FOL_Real +
  description {*
    Topology in first order logic.
  *}
  theories
    "FOL/Closure"
    "FOL/RealTopology"

session FOL_Homotopy = FOL_Topology +
  description {*
    Homotopy theory.
  *}
  theories
    "FOL/FundamentalGroup"

session FOL_Algebra = Auto2_FOL +
  description {*
    Abstract algebra.
  *}
  theories
    "FOL/Module"

session FOL_Arrow = Auto2_FOL +
  description {*
    Arrow's theorem.
  *}
  theories
    "FOL/ArrowImpossibility"
