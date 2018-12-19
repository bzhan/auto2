(*
  File: Sep_Examples.thy
  Author: Bohua Zhan

  Overall directory of examples in SepLogic.
*)

theory Sep_Examples

imports

(* Tutorial *)

  GCD_Impl

(* Inductive data structures *)

  (* Linked lists *)
  LinkedList
  
  (* Binary search tree *)
  BST_Impl
  
  (* Red-black tree *)
  RBTree_Impl

(* Array algorithms *)

  (* Standard procedure on arrays *)
  Arrays_Impl
  
  (* Dynamic array *)
  DynamicArray
  
  (* Quicksort *)
  Quicksort_Impl
  
  (* Indexed priority queue *)
  Indexed_PQueue_Impl
  
  (* Union-find *)
  Union_Find_Impl

(* Applications *)

  (* Connectivity on graphs *)
  Connectivity_Impl
  
  (* Dijkstra's algorithm *)
  Dijkstra_Impl
  
  (* Rectangular intersection *)
  Rect_Intersect_Impl

begin

end
