chapter AUTO2

session AUTO2 = HOL +
  description {*
    AUTO2 definitions.
  *}
  theories
    Auto2_Test

session Primes = AUTO2 +
  description {*
    Examples in number theory.
  *}
  theories
    Primes_Ex

session RBT = AUTO2 +
  description {*
    Examples in lists, trees, and red-black tree.
  *}
  theories
    "DataStrs/BST_Func"
    "DataStrs/RBT_Func"

session Hoare = AUTO2 +
  description {*
    Examples in Hoare logic.
  *}
  theories
    "Hoare/Hoare_Exp"
    "Hoare/Hoare_Equiv"
    "Hoare/Hoare_Rules"

session Real = AUTO2 +
  description {*
    Real analysis.
  *}
  theories
    "Analysis/Real_Auto2"

session Rat_Ex = AUTO2 +
  description {*
    Examples on rational numbers.
  *}
  theories
    "Analysis/Complex_Auto2"
    "Analysis/Sums"

session Arrow = AUTO2 +
  description {*
    Arrow's impossibility theorem.
  *}
  theories
    "Arrow_Ex/Arrow_Order_Ex"

session Algebra = AUTO2 +
  description {*
    Abstract algebra.
  *}
  theories
    "Algebra_Ex/Coset"

session SepLogic_Base = AUTO2 +
  description {*
    Base of separation logic.
  *}
  theories
    "SepLogic/Hoare_Triple"

session SepLogic_BasicStr = SepLogic_Base +
  description {*
    Separation logic: basic data structures.
  *}
  theories
    "SepLogic/LinkedList"
    "SepLogic/BinaryTree"
    "SepLogic/DynamicArray"
    "SepLogic/ArrayMap"

session SepLogic_Arrays = SepLogic_Base +
  description {*
    Separation logic: algorithms on arrays.
  *}
  theories
    "SepLogic/Reverse"
    "SepLogic/Quicksort"

session SepLogic_RBT = SepLogic_Base +
  description {*
    Separation logic: red-black tree.
  *}
  theories
    "SepLogic/RBT"

session SepLogic_PQueue = SepLogic_BasicStr +
  description {*
    Separation logic: priority queue (using array heap).
  *}
  theories
    "SepLogic/IndexedPriorityQueue"
