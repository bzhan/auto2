chapter AUTO2

session Auto2_HOL = HOL +
  description {*
    Instantiation of Auto2 for Isabelle/HOL.
  *}
  sessions
    "HOL-Library"
    "HOL-Imperative_HOL"
  theories
    "HOL/Auto2_Test"
    "HOL/Pelletier"
    "HOL/Primes_Ex"
  document_files
    "root.tex"

session DataStrs = Auto2_HOL +
  description {*
    Functional data structures.
  *}
  sessions
    "Auto2_HOL"
  theories
    "HOL/DataStrs/BST"
    "HOL/DataStrs/Lists_Ex"
    "HOL/DataStrs/Connectivity"
    "HOL/DataStrs/Dijkstra"
    "HOL/DataStrs/Interval_Tree"
    "HOL/DataStrs/Quicksort"
    "HOL/DataStrs/Indexed_PQueue"
    "HOL/DataStrs/RBTree"
    "HOL/DataStrs/Rect_Intersect"
  document_files
    "root.tex"

session SepLogic = DataStrs +
  description {*
    Separation logic.
  *}
  sessions
    "DataStrs"
  theories
    "HOL/SepLogic/Sep_Examples"
  document_files
    "root.tex"

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
    "FOL/BigSet"
    "FOL/Module"
    "FOL/ArrowImpossibility"
  document_files
    "root.tex"

session FOL_Topology = Auto2_FOL +
  description {*
    Real numbers and topology in first order logic.
  *}
  sessions
    "Auto2_FOL"
  theories
    "FOL/Topology/Closure"
    "FOL/Topology/MetricSpaces"
  document_files
    "root.tex"

session FOL_Homotopy = FOL_Topology +
  description {*
    Homotopy theory.
  *}
  sessions
    "FOL_Topology"
  theories
    "FOL/Homotopy/FundamentalGroup"
  document_files
    "root.tex"
