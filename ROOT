chapter AUTO2

session Auto2_HOL in HOL = HOL +
  description \<open>
    Instantiation of Auto2 for Isabelle/HOL.
  \<close>
  sessions
    "HOL-Library"
    "HOL-Imperative_HOL"
  theories [document = false]
    (* Core setup *)
    "Auto2_Test"

  theories
    (* Simple examples *)
    "Pelletier"
    "Primes_Ex"

session Auto2_Imperative_HOL in "HOL/Program_Verification" = Auto2_HOL +
  description \<open>
    Application of auto2 to verify functional and imperative programs.
  \<close>
  directories
    "Functional"
    "Imperative"
  theories
    (* Functional programs *)
    "Functional/BST"
    "Functional/Lists_Ex"
    "Functional/Connectivity"
    "Functional/Dijkstra"
    "Functional/Interval_Tree"
    "Functional/Quicksort"
    "Functional/Indexed_PQueue"
    "Functional/RBTree"
    "Functional/Rect_Intersect"

    (* Imperative programs *)
    "Imperative/GCD_Impl"
    "Imperative/LinkedList"
    "Imperative/BST_Impl"
    "Imperative/RBTree_Impl"
    "Imperative/Quicksort_Impl"
    "Imperative/Connectivity_Impl"
    "Imperative/Dijkstra_Impl"
    "Imperative/Rect_Intersect_Impl"

  theories [document = false]
    "Imperative/Sep_Examples"

  document_files (in "../../document")
    "root.tex"
    "root.bib"

session Auto2_FOL in FOL = FOL +
  description \<open>
    Example in first order logic.
  \<close>
  theories
    "Pelletier"
    "BigProd"
    "Cardinal"
    "SetSum"
    "Coset"
    "Abs"
    "Divides"
    "Rat"
    "Lattice"
    "BigSet"
    "Module"
    "ArrowImpossibility"
  document_files (in "../document")
    "root.tex"
               
session FOL_Topology in "FOL/Topology" = Auto2_FOL +
  description \<open>
    Real numbers and topology in first order logic.
  \<close>
  theories
    "Closure"
    "MetricSpaces"
  document_files (in "../../document")
    "root.tex"

session FOL_Homotopy in "FOL/Homotopy" = FOL_Topology +
  description \<open>
    Homotopy theory.
  \<close>
  theories
    "FundamentalGroup"
  document_files (in "../../document")
    "root.tex"
