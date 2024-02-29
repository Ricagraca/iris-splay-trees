

# Pointer based implementation

To compile all .v files successfully, use the given MakeFile. Used coqc 8.11.0 to compile.
We enumerate some of the most relevant theorem/lemmas that we have proven for each module.

## STorientation

#### Module which contains the definition of orientation for a binary search tree.

The type of an orientation is either LEFT or RIGHT. This works for binary search trees! For other type of trees with a different branching factor we would need to either add new constructors for each to distinguish between each branch,  or we could generalize it somehow without the need to add a new constructor if we want to increase the branching factor.
```
Inductive orientation := 
  |LEFT
  |RIGHT.
```

We then defined a invert function which is pretty simple, if the input orientation is LEFT,  then the output is RIGHT, and if the input orientation is RIGHT, then the output is RIGHT.

```
  Definition invert_orientation (o : orientation) :=
    match o with
    | LEFT  => RIGHT
    | RIGHT => LEFT
    end.
```

Then, we can easily prove that the invert function applied to the orientation is involutive, i.e., applying it twice is equal to applying the identity function. 
```
Lemma involutive_invert : forall o,
      invert_orientation (invert_orientation o) = o.
```
In a binary search tree, if we have a node with value $v$, all nodes to its left are of lesser  value than **v** and all nodes to its right are of greater value than $v$. To generalize this, we use a orientation operation and try to generalize all lemmas by using this operation! As seen in the bellow snippet, if orientation is LEFT, then the orientation operation is > (Z.gt) and if it is RIGHT, then the orientation operation is < (Z.lt) (Z is the integer set).
```
  Definition orientation_op (o : orientation) :=
    match o with
    | LEFT  => Z.gt
    | RIGHT => Z.lt
    end.
```
With this definition of orientation operation, we can deduce that we cannot have different orientation for the same input numbers, i.e., assuming a < b and b < a we can conclude any proposition P (including False). 
```
  Lemma invert_orientation_diff : forall o a b P,
      orientation_op o a b ->
      orientation_op (invert_orientation o) a b ->
      P.
```

## STpredicate
In the splay tree predicate module, we define the predicates and invariants that form a binary search tree. The predicates that we use are for a normal graph: a domain $D$ that is a set predicate of all node (pointers) from the graph (if we have $D \ x$ then $x \in D$) , an edge set $F$ that contains all the edges from the graph ($F \ x \ y \ o$ says that we have a connection from $x$ to $y$ with orientation $o$), a value function $V$ that maps a node from domain $D$ to a value of integer type $\mathbb{Z}$ and a weight function $W$ that maps a node from domain $D$ to an arbitrary positive integer value. The invariants for a binary search tree are enumerated:

Inv $p$ $D$ $F$ $V$ $W$  $\equiv$
* $\text{finite} \ D \equiv \exists l, (\forall x, x \in D \longrightarrow \text{mem} \ x \ l)$
* $\text{rootisindomain} \ p \ D \equiv  p \in D$
* $\text{confined} \ D \ F \equiv \forall \ x \ y \ o, \ F \ x \ y \ o \longrightarrow (x \in D \wedge  y \in D)$
* $\text{binarytree} \ F \equiv \forall \ x \ y \ z \ u \ o, y \neq z \longrightarrow \ F \ x \ y \ u \longrightarrow F \ x \ z \ o \longrightarrow u \neq o$
* $\text{isroot} \ D \ F \ p \equiv \forall \ x \ o , x \in D \longrightarrow \neg (F \ x \ p \ o) \wedge \text{path} \ F \ p \ x$
* $\text{searchtree} \ F \ V \equiv  \forall \ x \ y \ z \ o, \  (F \ x \ y\ o \wedge \text{path} \ F \ y \ z) \longrightarrow op \ o \ (V x) \ (V y) \wedge op \ o \ (V x) \ (V z)$
* $\text{positivefunction} \ W \equiv \forall \ x,\  W \ x \ > \ 0$

The **finite** invariant, tells that the set of node element is finite, i.e., there exists a finite object (a list) that represents domain $D$. The **rootisindomain** invariant is just a proposition that tells that there exists a root element $p$ in the tree. If we have no root in the tree, then any splay method applied to such NULL tree is trivial and we can easily discard thoses cases. Bellow follows the proof of the splay tree method applied to a NULL tree, which is pretty straight-forward (only requiring a total of three lines. This lemma says that if we give as input a NULL pointer, then the result of the splay method on key $k$ is a NULL pointer as well! However, to fully prove that the splay algorithm is correct, we need a lot more work!
```
  Lemma splay_on_empty : forall (pp p : loc) k,
    {{{ pp ↦ NULL }}}
      splay_tree_splay #pp #k
    {{{ RET #() ; pp ↦ NULL }}}.
  Proof.
    intros. iIntros "Hpp Hf".
    wp_rec. wp_pures. wp_load. wp_pures.
    iApply "Hf". iFrame.
  Qed.
```
The **confined** property mentioned, states that all elements from edge set $F$ belong to domain $D$, i.e., edge set $F$ is confined by domain $D$. This is quite useful to resrict edge set to elements of $D$ and in consequence to limit (as a finite number) the size of edge set $F$. The **isroot** propertie states that $p$ is a root, i.e., there is no edge from some element in $D$ connected to $p$ and that there exists a path from root element $p$ to any other element in $D$. One of the main properties for a binary search tree is the **searchtree** property that states that for any element, all nodes to its left are of lesser value and all nodes to its right are of greater value. This property is useful to prove much of the lemmas that we will prove (e.g., absence of cycles in tree). Finally the **positivefunction** invariant, tells that the weight function provided always returns a positive value.

For the memory model, we have then used a generalized map $M$ to map a pointer to the value that it holds. A pointer points to a set of values, the key (modeled as an integer) and two pointers for the left and right child. Therefore, each pointer from domain $D$ can hold one of the four following values:

* $\text{NodeB} \ v \ n_l \ n_r$ : A node which holds value $v$, left child $nl$ and right child $nr$  
* $\text{NodeL} \ v \ n$ : A node which holds value $v$ and left child $nl$
* $\text{NodeR} \ v \ nr$ : A node which holds value $v$ and right child $nr$
* $\text{NodeN} \ v$ : A node which holds value $v$ with no children

Then, we have created the memory predicate which translates the map $M$ to components such as edges and values, e.g., if we have that a pointer $p$ holds value $\text{NodeB} \ v \ n_l \ n_r$ in map $M$, then we have edges $F \ p \ n_l \ \text{LEFT}$ and $F \ p \ n_r \ \text{RIGHT}$ and we have that $V p = v$ as well! 

This predicate is defined as following: 

```
  Definition Mem (D : LibSet.set elem)
             (F : elem -> elem -> orientation -> Prop)
             (V : elem -> Z) 
             (M : gmap elem content) : Prop :=
    forall x, x \in D ->
	match M!!x with
	| Some (NodeB v p1 p2) => F x p1 LEFT  /\ F x p2 RIGHT /\ V x = v
	| Some (NodeL v p1)    => F x p1 LEFT  /\ ¬(exists y, F x y RIGHT) /\ V x = v
        | Some (NodeR v p2)    => F x p2 RIGHT /\ ¬(exists y, F x y  LEFT) /\ V x = v
        | Some (NodeN v)       => ¬(exists y, F x y RIGHT) /\ ¬(exists y, F x y  LEFT) /\ V x = v
        | None => False
    end.
```

Finally, to finish the splay tree predicate, we need ownership of all of these pointers in order to manipulate these and access them. The ownership of these pointers is given by the following definition:

```
  Definition mapsto_M (M : gmap elem content) : iProp Σ :=
    ([∗ map] l ↦ c ∈ M, from_option (mapsto l 1) False (val_of_content c))%I.
```

With the these three last mentioned definitions: Inv, Mem and mapsto_M we have created the splay tree predicate:

```
  Definition ST R D V W : iProp Σ :=
    (∃ F M,
        ⌜ Inv R D F V W ⌝ ∗
        ⌜ Mem D F V M ⌝ ∗
        mapsto_M M 
    ).
```

## STdomain

In the domain module, we have defined the descendants definition 

$\text{descendants} \ F \ r \ \equiv \{ x \ | \ \text{path} \ F \ r \ x \}.$ 

which returns all the descendants of a given node. If the structure where we apply this definition is a tree, then it returns a sub-tree with root $r$.

We can then prove, some useful lemmas, e.g., if a binary search tree is finite (which is the case), then the set of descendants of a node in this tree is also finite:

```
Lemma descendants_finite_if_bst : forall F x,
      Inv p D F V W ->
      x \in D ->
      let D' := descendants F x in
      finite (D').
```
This can be easily proven with the finite set inclusion lemma:

$\forall \ E \ F, E \subseteq F \longrightarrow \text{finite} \ F \longrightarrow \text{finite} \ E$

## STlink
In this module, we prove any lemma related with links (edges). Such as, there is no edge from an element to itself: $\forall \ x \ o,  ¬(F \ x \ x \ o)$. We also prove that if we have edge from $x$ to $y$ with orientation $o$, $F \ x \ y \ o$ and we have also with orientation $u$, $F \ x \ y \ u$, then $u$ and $o$ have the same orientation. If this orientation was different then we would have, with the **searchtree** property, $V \ x < \ V \ y$ and $V \ y < \ V \ x$ which is a contradiction! The proofs to these are followed respectively:

``` 
  Lemma cant_point_to_itself_if_bst : forall F p' o, 
      Inv p D F V W ->
      ~ (F p' p' o).
  Proof.
    intros F p' o Inv. intro N.
    inversion Inv. unfold is_bst in *.
    destruct Inv_bst as
        [confined [rootisindomain [isroot [[searchleft searchright] [binarytree finite]]]]].
    destruct o.
    + assert (F p' p' LEFT /\ path F p' p') as FPp'l.
      split ; auto using path_refl.
      apply searchleft in FPp'l. lia.
    + assert (F p' p' RIGHT /\ path F p' p') as FPp'r.
      split ; auto using path_refl.
      apply searchright in FPp'r. lia.
  Qed.
``` 
```
  Lemma unique_direction_if_bst : forall F x y u o,
      Inv p D F V W ->    
      F x y o ->
      F x y u ->
      u = o.
  Proof.
    intros F x y u o Inv E1 E2.
    destruct u, o ; auto.
    - pose proof (edge_value_left_if_bst F x y Inv E2).
      pose proof (edge_value_right_if_bst F x y Inv E1).
      lia.
    - pose proof (edge_value_left_if_bst F x y Inv E1).
      pose proof (edge_value_right_if_bst F x y Inv E2).
      lia.
  Qed.
``` 
## STpath
A path is a reflexive and transitive closure on edge set $F$.  The path rules for these closures are well enumerated bellow.

* $\textbf{once} \ \equiv \ \forall \ F \ x \ y \ o, \ F \ x \ y \ o \longrightarrow \text{path} \ F \ x \ y$
* $\textbf{reflexivity} \ \equiv \ \forall \ F \ x, \text{path} \ F \ x \ x$
* $\textbf{transitivity} \ \equiv \ \forall \ F x \ y \ z, \text{path} \ F \ x \ y \longrightarrow \text{path} \ F \ y \ z \longrightarrow \text{path} \ F \ x \ z$

### Absence of cycles in a binary search tree

To prove the absence of cycles in a binary search tree, we have extended this path inductive type so it can store the size of the path. We then prove that if we have a path from one node $x$ to itself, then the path itself is of size 0, i.e., there are no paths from one node to itself where a step is taken! The $c$ variable in **path\_count** is the size of the path, i.e., the number of edges of that are in the path. The following proved lemma proves the absence of cycles in a binary search tree.

$\text{Inv} \ p \ D \ F \ V \ W \longrightarrow \ \text{path\_count} \ F \ x \ x \ c \longrightarrow c = 0$


### Unicity of parent of a node

We then were able to prove that a node has an unique parent. However, before proving it, we had to prove that for any path between two nodes are always the same. 

``` 
Lemma only_one_parent_if_bst : forall F p1 p2 x o u, 
    Inv p D F V W ->
    F p1 x o ->
    F p2 x u ->
    p1 = p2.
``` 


### Unicity of path between two nodes in a binary search tree

Nevertheless, both **path** and **path\_count** do not have all the needed information about the path, i.e., they only have information that such path exists from a beggining point to an ending point. However, we have created a new inductive type **path\_memory** that keeps track of the nodes that creates such path. This inductive type is defined as following:

* $\textbf{once} \ \equiv \ \forall \ F \ x \ y \ o, \ F \ x \ y \ o \longrightarrow \text{path\_memory} \ F \ x \ y \ [x]$
* $\textbf{reflexivity} \ \equiv \ \forall \ F \ x, \text{path\_memory} \ F \ x \ x\ [ \ ]$
* $\textbf{transitivity} \ \equiv \ \forall \ F \ x \ y \ z \ l, F \ x \ y \ o \longrightarrow \text{path\_memory} \ F \ y \ z \ l \longrightarrow 
    \text{path\_memory} \ F \ x \ z \ (x :: l)$


We then were able to prove the following:
```
Lemma path_must_be_equal_if_bst : forall F x y l1 l2,
    Inv p D F V W ->
    path_memory F x y l1 ->
    path_memory F x y l2 ->
    l1 = l2.
```

This is intuitive, because if there are more than one path between two nodes, then in one of the nodes there must exist a divergence which is impossible because it then contradicts the searchtree property mentioned in the splay tree predicate!

### Path finiteness
We then also prove the finiteness of any path in a binary search tree. This can be achieved with the finite property and the searchtree property. The path size between two nodes is always bounded by the size of the domain! If the size of the path is bigger than the size of the domain $D$, then the witness for such path must repeat at least one time. This repetition means that there exists a path from a node $x$ to itself with at least size 1. This is a contradiction to the **absence of cycles in a binary seach tree** that we have proven above. 

```
Lemma path_memory_size_le_card_domain : forall p F x y l,
      Inv p D F V W ->
      path_count F x y c ->
      c <= card D.
```

## STedgeset
In this module, we show how we update the edge set predicate in order to remove/add edges to it. We start off with the simple method operations, such as add and remove.

To add an edge to our predicate, we simply use the $\lor$ logical connective.

        F            (x,y,o)            F \/ (x,y,o)

        x               x                     x
       /                 \ o                 / \o
      z - y    \/     z   y      =          z   y
      \                                      \
        w               w                     w


The coq definition for such operation is the expected:

```
Definition add_edge F x  y  o :=
    fun x' y' o' => F x' y' o'  \/ (x' = x /\ y' = y /\ o' = o).
```

The remove operation is similar to the add edge, but instead of using the $\lor$ logical connective, we have used the $\wedge$ connective! 


        F            (x,y,o)            F /\ ¬ (x,y,o)

        x               x                     x
       / \               \ o                 / 
      z - y    /\ ¬   z   y      =          z   y
      \                                      \
        w               w                     w

Furthermore, we have also created other operations such as update\_edge which redirects an edge on a graph,. union\_edge which performs the union between two edge sets $F_1$ and $F_2$ and other more operations that are useful to model the rotation operations of the splay tree algorithm. We also have operations that remove edges which endpoints do/not belong to a certain domain $D'$. These last are useful to retrieve the sub-trees of a binary seach tree!

### Child of root is a binary search tree
Using these operations, we have proven some useful lemmas, such as that the child of a root of a binary search tree is also a binary search tree! This statement is well reflected by the following lemma that we were able to prove!

```
Theorem child_if_inv : forall F x o,
    Inv p D F V W ->
    F p x o ->
    let D' := (descendants F x) in 
    let F' := (remove_edge_that_are_not_in_D F D') in 
    Inv x D' F' V W.  
```

### Join on mutation of sub-tree

We have proven also, that updating the sub-tree of the child of a root to another binary search tree, then the total tree is also a binary search tree. This lemma is useful, with the use of the **child\_if\_inv**, that we have proven above,  if we want to perform some update on one of the sub-trees and mantain the properties of the splay tree predicate!

```
Theorem join_if_inv : (*$\forall$*) F F' x z o,
    Inv p D F V W ->
    F p x o ->
    let D' := (descendants F x) in
    let FC' := (remove_edge_that_are_in_D F D') in
    Inv z D' F' V W ->
    let F'' := (add_edge (union_edge F' FC') p z o) in
    Inv p D F'' V W.
```

## STpathcount
We have also defined a path find count predicate which retrieves, in a binary search tree, the path from the root of the tree to the node element for which we are searching for with key $k$. Not always this key may be present in the tree, however, if such key is not present in the tree, this search will also stop at a given leaf of the tree.

We have successfully proven that the search tree algorithm will eventually stop! To prove this, we have first proven that given that such algorithm does not stop, then we can have a path of any size in a binary search tree:

```
Lemma no_ending_path_then_exists_a_path_with_every_size : forall p F z,
      ¬(exists x n, path_find_count F V p x z n ENDED) ->
      forall n, (exists x, path_find_count F V p x z (S n) GOING).
```
 
Therefore, if we assume that there is no ending (ENDED) to such algorithm then there is a path with any given size in the binary search tree. However, if there is a path with any size, then there is a path with size bigger than domain $D$, which contradicts the lemma that we have proven that the size of the path cannot be greater than  $|D|$ (path_memory_size_le_card_domain). Therefore, we have successfully proven the following lemma:

```
Theorem exists_find_count_path_if_inv : forall p F z,
      Inv p D F V W ->
      (exists x n, path_find_count F V p x z n ENDED).
``` 
 i.e., the find algorithm eventually ends!

## STrotation

The first operations of the splay tree algorithm that we have proven were the rotation operations: rotate\_left and rotate\_right. In the splay tree algorithm of the GCC implementation, we observe that these rotation operations are used on the root of the tree or on one of the children of the root, therefore we only focus on these. 
We first have proved that the rotations on the root would preserve the invariants of the binary search tree. Nonetheless, there exist two cases that we must consider: if internal grandchildren exist and if internal grandchildren do not exist, i.e., a node with opposite orientation to the child of the root.

We have successfully proven that these updates on the edge set that model the rotations of the splay tree method preserve the splay tree invariants! 

We have first proven for the case where there exists an internal node $z$:

```
Theorem rotate_XI_if_bst : forall F x z o, 
    Inv p D F V W ->
    F p x o ->
    F x z (invert_orientation o) ->
    let F' := (update_edge F p x z o) in
    let F'' := (update_edge F' x z p (invert_orientation o)) in
    Inv x D F'' V W.
``` 

And then with no internal node:

```
Theorem rotate_XE_if_bst : forall F x o, 
      Inv p D F V W ->
      F p x o ->
      ¬(exists y, F x y (invert_orientation o)) ->
      let F' := (remove_edge F p x) in
      let F'' := (add_edge F' x p (invert_orientation o)) in
      Inv x D F'' V W.
```

Afterwards, we were able to prove the correctness of the heap-lang code for the rotations: rotate\_left and rotate_right for the possible combinations of the state of the binary search tree. 

For the root rotations, we only need information related to two nodes, the root and its child (In the snippet we have root $p$ and child $p_1$).
```
Lemma rotate_left_BB_st' (pp p p1 p2 p3 p4 : loc) (vp vp1 : Z) :
    let F'' :=  (update_edge (update_edge F p1 p4 p RIGHT) p p1 p4 LEFT) in
    let M' := (<[p:=NodeB (V p) p4 p2]> (<[p1:=NodeB vp1 p3 p]> M)) in 
    M !! p  = Some (NodeB vp p1 p2) ->
    M !! p1 = Some (NodeB vp1 p3 p4) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      rotate_left #pp #p #p1
    {{{ RET #() ; pp ↦ #p1 ∗ ⌜Inv p1 D F'' V W⌝ ∗ ⌜Mem D F'' V M'⌝ ∗  mapsto_M M' }}}.
```
However, to perform a rotation on a child, we had to have knowledge of three pointer: the root, the child and the granchild! (In the snippet we have root $p$, child $p_2$ and grandchild $p_3$) 

```
Lemma rotate_left_child_RBB_r_st (pp p p2 p3 p4 p5 p6 : loc) (vp vp2 vp4 : Z) :
    let D' := descendants F p2 in    
    let FC' := (remove_edge_that_are_in_D F D') in
    let F' := (remove_edge_that_are_not_in_D F D') in 
    let F'' := (update_edge F' p3 p6 p2 STorientation.RIGHT) in
    let F''' := (update_edge F'' p2 p3 p6 STorientation.LEFT) in
    let F'''' := (add_edge (union_edge F''' FC') p p3 STorientation.RIGHT) in 
    let M' := (<[p:=NodeR (V p) p3]> (<[p2:=NodeB (V p2) p6 p4]> (<[p3:=NodeB (V p3) p5 p2]> M))) in
    M !! p  = Some (NodeR vp p2) ->
    M !! p2 = Some (NodeB vp2 p3 p4) ->
    M !! p3 = Some (NodeB vp4 p5 p6) ->
    {{{ pp ↦ #p ∗ ⌜Inv p D F V W⌝ ∗  ⌜Mem D F V M⌝ ∗ mapsto_M M }}}
      let: "tmp" := ref #p2 in 
      rotate_left ("tmp") #p2 (left_child #p2) ;;
      #p <- SOME (value #p, (left_child #p, !"tmp"))
    {{{ RET #() ; pp ↦ #p ∗ ⌜Inv p D F'''' V W⌝ ∗ ⌜Mem D F'''' V M'⌝ ∗ mapsto_M M'}}}.
```

## STir

The predicate, $\text{bw\_ir} \ F \ V \ p \ x \ k \ n \ F' \ s$, says that if we have edge set $F$ and value function $V$, and we perform the splay tree method on root $p$ with key $k$, then $n$ rotations are required to get to edge set $F'$ with root $x$ and state $s$. The state of the splay tree method can be either GOING or ENDED. If it is in state ENDED, then the splay tree method terminated successfully, otherwise it is in state GOING which means that it needs to perform another loop of the splay tree iterative method. This inductive predicate, fw\_ir, that models the heap-lang GCC's splay tree method, holds a total of 15 rules. 

The rules that are GOING, i.e., for the double rotations are pretty big. Most of the lines are for the updates on the edge set $F$ to obtain a new edge set $F_2$ that is the edge set after a cycle of the splay tree method. 
```
bw_ir_oo_child_nlgc : forall (F : EdgeSet) V p x y z o,
      (orientation_op o) (V p) z -> 
      F p x o ->
      (orientation_op o) (V x) z ->
      F x y o -> 
      ¬(exists t, F y t (invert_orientation o)) ->
      (* rotation on children *)
      let D' := (descendants F x) in
      let F' := (remove_edge_that_are_not_in_D F D') in 
      let FC' := (remove_edge_that_are_in_D F D') in
      let F'' := (remove_edge F' x y) in
      let F''' := (add_edge F'' y x (invert_orientation o)) in
      (*Edgeset after first rotation*)
      let Fafr := (add_edge (union_edge F''' FC') p y o) in 
      (* rotation on root *)
      let F1 := (update_edge Fafr p y x o) in 
      let F2 := (update_edge F1 y x p (invert_orientation o)) in 
      bw_ir F V p y z 2 F2 GOING     
```
The rule mentioned above describes the case where we are searching for key $z$ on tree $F$ with root $p$. And the transformation is a zig-zig bottom down (performing a double rotation):

             F                           F2
    	
             p                           y
            / \o                        / \
           Tp  x                       p  Ty
              / \o                    / \
             Tx  y                   Tp  x
                / \                     / \
              NULL Ty                  Tx NULL

The first thing that we have proven, is that after the splay tree method ended on a binary search tree, then the binary search tree invariant would be preserved! The lemma stating this is the following:

```
Lemma fw_ir_inv : forall p F x n z F' s,
    Inv p D F V W ->
    fw_ir F V p x z n F' s ->
    Inv x D F' V W.
```
## STsplay

Afterwards, we have proven that the bw inductive predicate implements the splay tree method! This is amazing! And we also have proven that after splaying on key $k$, then all elements to the left of the root of the now splayed tree are of lesser value than the root value and all nodes to the right are of greater value than the root value.

``` 
    bw_ir F V p p' k n F' ENDED ->
    Inv p D F V W ->
    Mem D F V M -> 
    {{{ pp ↦ #p ∗ mapsto_M M }}}
      splay_tree_splay #pp #k
    {{{ M' F' (p' : loc) , RET #() ;
        pp ↦ #p' ∗
           ⌜Inv p' D F' V W⌝ ∗
           ⌜Mem D F' V M'⌝ ∗
            mapsto_M M' ∗
           ⌜ (forall y y', F' p' y o -> y' \in descendants F' y -> (orientation_op o) k (V y')) ⌝
      }}}.
```
Nonetheless, to end this specification we need to show that the splay tree method ends, i.e., that for any given binary search tree, applying the splay tree method ends. This can be described by the following proposition:

$\exists \ p' \ n \ F', \text{fw\_ir} \ F \ V \ p \ p' \ k \ n \ F' \ \text{ENDED}$

However, we have not been able to prove such proposition. Nevertheless, we have reduced this proof (which is obviously true for a finite tree) to the following lemma which states that after $4$ rotations, the length of the path from the root node to the element for which we are searching for is reduced by at least on level! We have done a simple brute-force analysis on the possible cases and verified that this is indeed true! We must only consider the case where two double rotations are performed. In our analysis we see that a zig-zag operation decreases the level of the node for which we are searching for by at least one. Nonetheless, the zig-zig case could not decrease its level: However, if it does not decreases its level, then the next double rotation that will be performed is a zig-zag rotation which decreases its level as we have stated before!

``` 
Lemma path_find_count_ir_constant_4 : forall p F F' x x' z n,
    Inv p D F V W -> 
    path_find_count F V p x z (4+n) ENDED ->
    fw_ir F V p x' z 4 F' GOING ->
    (exists m y, (m < 4+n) /\ path_find_count F' V x' y z m ENDED).
``` 

Assuming this lemma, we have then proved the specification of the splay tree method 
```
Lemma splay_st (p pp : elem) (D : set elem) (V W : elem -> Z) (k : Z) :
    {{{ pp ↦ #p ∗ ST p D V W }}}
      splay_tree_splay #pp #k 
    {{{ (p' : elem) ,  RET #() ; pp ↦ #p' ∗ ST p' D V W }}}.
```

