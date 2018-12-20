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

session Auto2_Imperative_HOL = Auto2_HOL +
  description {*
    Application of auto2 to verify functional and imperative programs.
  *}
  theories
    (* Functional programs *)
    "HOL/Functional/BST"
    "HOL/Functional/Lists_Ex"
    "HOL/Functional/Connectivity"
    "HOL/Functional/Dijkstra"
    "HOL/Functional/Interval_Tree"
    "HOL/Functional/Quicksort"
    "HOL/Functional/Indexed_PQueue"
    "HOL/Functional/RBTree"
    "HOL/Functional/Rect_Intersect"

    (* Imperative programs *)
    "HOL/Imperative/GCD_Impl"
    "HOL/Imperative/LinkedList"
    "HOL/Imperative/BST_Impl"
    "HOL/Imperative/RBTree_Impl"
    "HOL/Imperative/Quicksort_Impl"
    "HOL/Imperative/Connectivity_Impl"
    "HOL/Imperative/Dijkstra_Impl"
    "HOL/Imperative/Rect_Intersect_Impl"

  theories [document = false]
    "HOL/Imperative/Sep_Examples"

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
