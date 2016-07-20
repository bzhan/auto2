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
    RBT_Ex

session Hoare = AUTO2 +
  description {*
    Examples in Hoare logic.
  *}
  theories
    "Hoare/Hoare_Exp"
    "Hoare/Hoare_Equiv"
    "Hoare/Hoare_Rules"

session Imp_Array = AUTO2 +
  description {*
    Verification in imperative HOL, arrays.
  *}
  theories
    "Imp_Ex/Imp_Ex_Reverse"
    "Imp_Ex/Imp_Ex_Quicksort"

session Imp_LinkedList = RBT +
  description {*
    Verification in imperative HOL, linked lists.
  *}
  theories
    "Imp_Ex/Imp_Ex_Linked_Lists"

session Imp_BinaryTree = RBT +
  description {*
    Verification in imperative HOL, binary trees.
  *}
  theories
    "Imp_Ex/Imp_Ex_Binary_Trees"

session Real = AUTO2 +
  description {*
    Real analysis.
  *}
  theories
    "Analysis/Real_Auto2"

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
