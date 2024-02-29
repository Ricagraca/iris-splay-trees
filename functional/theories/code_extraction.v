Require Extraction.
Require Import ST.SplayTree.
Require Import Coq.Structures.OrderedTypeEx.

Module Nat_Tree := SplayTree(OrderedTypeEx.Nat_as_OT).

Export Nat_Tree.

Recursive Extraction splay.

Extraction "SplayTree" splay.

