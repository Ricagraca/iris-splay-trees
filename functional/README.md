
## Functional implementation

To compile all .v files successfully, use the given MakeFile. Used coqc 8.11.0 to compile.


#### Lemma splay_node_not_nil : forall a t1 n t2,
 ```
 splay a <| t1, n, t2 |> <> <| |>.
 ```
- [x] 

#### Theorem splay_leaf_iff : forall a t,
  ```
  splay a t = <| |> <-> t = <| |>.
  ```
- [x] 

#### Theorem splay_max_leaf_iff : forall t,
 ```
 splay_max t = <| |> <-> (t = <| |>).
 ```
- [x]  

#### Lemma size_splay : forall t a,
  ```
  size (splay a t) = size t.     
  ```        
- [x]   

#### Lemma size_if_splay : forall a t l u r,
  ```
  eq_tree (splay a t) (<| l, u, r |>) -> size t = size l + size r + 1.
  ```
- [x]   

#### Lemma splay_not_leaf : forall t a,
  ```
  t <> <| |> -> exists l x r, splay a t = <| l, x, r |>.
  ```
- [x]   

#### Lemma set_splay : forall a t,
  ```
  NatSet.Equal (set_tree (splay a t)) (set_tree t).
  ```
- [x]   

#### Lemma splay_bstL : forall t a l e r x,
  ```
  bst t -> eq_tree (splay a t) (<| l, e, r |>) -> XSet.In x (set_tree l) -> x < a.
  ```
- [x]   

#### Lemma splay_bstR : forall t a l e r x,
  ```
  bst t -> eq_tree (splay a t) (<| l, e, r |>) -> XSet.In x (set_tree r) -> a < x.
  ```
- [x]   

#### Theorem bst_splay : forall a t , 
  ```
  bst t -> bst (splay a t).
  ```
- [x]   

#### Theorem splay_to_root : forall t a t',
  ```
  bst t -> eq_tree (splay a t) t' ->
  (XSet.In a (set_tree t) <-> (exists l r, t' = <| l, a, r |>)).
  ```
- [x]   

#### Lemma is_root_splay : forall t a,
  ```
  bst t ->
  (is_root a (splay a t) <-> XSet.In a (set_tree t)).
  ```
- [x]   

#### Lemma set_insert : forall a t,
  ```
  XSet.Equal (set_tree (insert a t)) (XSet.union (XSet.singleton a) (set_tree t)).
  ``` 
- [x]   

#### Lemma bst_insert : forall a t,
  ```
  bst t -> bst (insert a t).
  ```
- [x]   

#### Lemma size_splay_max : forall t,
  ```
  size (splay_max t) = size t.
  ```
- [x]   

#### Lemma size_if_splay_max : forall t l u r,
  ```
  splay_max t = <| l, u, r |> -> size t = size l + size r + 1.
  ```
- [x]   

#### Lemma set_splay_max : forall t,
  ```
  XSet.Equal (set_tree (splay_max t)) (set_tree t)
  ```
- [x]   

#### Lemma bst_splay_max : forall t,
  ```
  bst t -> bst (splay_max t).
  ```
- [x]   

#### Lemma splay_max_leaf : forall t l a r,
  ```
  splay_max t = <| l, a, r |> -> r =  <| |>.
  ```
- [x]   

#### Lemma splay_max_eq_splay : forall t a,
  ```
  bst t -> (forall x, XSet.In x (set_tree t) -> x < a \/ x == a) ->
  splay_max t = splay a t.
  ```
- [x]   

#### Lemma splay_max_eq_splay_ex : forall t (e : o.t),
  ```
  bst t -> (exists a, splay_max t = splay a t).
  ```
- [x]   

#### Lemma set_delete : forall t a,
  ```
  bst t -> XSet.Equal (set_tree (delete a t)) (XSet.remove a (set_tree t)).
  ```
- [x]   

#### Lemma bst_delete : forall t a,
  ```
  bst t -> bst (delete a t).
  ```
- [x]

### Distinguish between what was done

#### Lemma bst_splay_insert_delete_star : forall t l,
```
  bst t -> all_tree_in_list_are_bst (splay_insert_delete_star t l).
```
- [x]

#### Lemma bst_splay_insert_delete_star_on_empty : forall l,
``` 
  all_tree_in_list_are_bst (splay_insert_delete_star <||> l).
```
- [x]


### Extract code haskell polimorphic
``` 
    Require Extraction.
    Require Import ST.SplayTree.
    Require Import Coq.Structures.OrderedTypeEx.
    Module Nat_Tree := SplayTree(OrderedTypeEx.Nat_as_OT).
    Export Nat_Tree.
    Recursive Extraction splay.
    Extraction "SplayTree" splay.
```