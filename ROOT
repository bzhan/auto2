chapter AUTO2

session HOL_Base = HOL +
  description {*
    Theories in HOL needed by AUTO2.
  *}
  sessions
    "HOL-Library"
    "HOL-Imperative_HOL"
  theories
    "HOL-Library.Multiset"
    "HOL-Imperative_HOL.Imperative_HOL"

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

session DataStrs_Basic = AUTO2 +
  description {*
    Functional data structures.
  *}
  theories
    "HOL/DataStrs/Arrays_Ex"
    "HOL/DataStrs/BST"
    "HOL/DataStrs/Interval"
    "HOL/DataStrs/Lists_Ex"
    "HOL/DataStrs/Mapping_Str"
    "HOL/DataStrs/Partial_Equiv_Rel"
    "HOL/DataStrs/Union_Find"

session DataStrs_Advanced = DataStrs_Basic +
  description {*
    Functional data structures, advanced.
  *}
  theories
    "HOL/DataStrs/Connectivity"
    "HOL/DataStrs/Dijkstra"
    "HOL/DataStrs/Interval_Tree"
    "HOL/DataStrs/Quicksort"
    "HOL/DataStrs/Indexed_PQueue"
    "HOL/DataStrs/RBTree"
    "HOL/DataStrs/Rect_Intersect"

session DataStrs_FW = AUTO2 +
  description {*
    Floyd-Warshall algorithm.
  *}
  theories
    "HOL/DataStrs/Floyd_Warshall"

session SepLogic = DataStrs_Advanced +
  description {*
    Separation logic.
  *}
  theories
    "HOL/SepLogic/Sep_Examples"

session Auto2_FOL = FOL +
  description {*
    Example in first order logic.
  *}
  theories
    "FOL/Pelletier"
    "FOL/BigProd"
    "FOL/Cardinal"
    "FOL/SetSum"
    "FOL/Coset"
    "FOL/Abs"
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
    "FOL/MetricSpaces"

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
