chapter AUTO2

session Auto2_HOL = HOL +
  description {*
    Instantiation of Auto2 for Isabelle/HOL.
  *}
  sessions
    "HOL-Library"
    "HOL-Imperative_HOL"
  theories [document = false]
    (* Core setup *)
    "HOL/Auto2_Test"

  theories
    (* Simple examples *)
    "HOL/Pelletier"
    "HOL/Primes_Ex"

    (* Functional programs *)
    "HOL/DataStrs/BST"
    "HOL/DataStrs/Lists_Ex"
    "HOL/DataStrs/Connectivity"
    "HOL/DataStrs/Dijkstra"
    "HOL/DataStrs/Interval_Tree"
    "HOL/DataStrs/Quicksort"
    "HOL/DataStrs/Indexed_PQueue"
    "HOL/DataStrs/RBTree"
    "HOL/DataStrs/Rect_Intersect"

    (* Imperative programs *)
    "HOL/SepLogic/GCD_Impl"
    "HOL/SepLogic/LinkedList"
    "HOL/SepLogic/BST_Impl"
    "HOL/SepLogic/RBTree_Impl"
    "HOL/SepLogic/Quicksort_Impl"
    "HOL/SepLogic/Connectivity_Impl"
    "HOL/SepLogic/Dijkstra_Impl"
    "HOL/SepLogic/Rect_Intersect_Impl"

  theories [document = false]
    "HOL/SepLogic/Sep_Examples"

  document_files
    "root.tex"
    "root.bib"

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
