
# Iris Splay Trees

## Introduction 


When real-world applications crash or start to lack in performance, they can bring tremendous costs to the involving parties. Therefore, it is important to ensure that these applications do not fail. Testing is useful in practice as it can be used to show the presence of bugs. However, it cannot be used to prove their absence.

On the other hand, formal verification can be used to prove that a program fully meets a given specification.However, formal verification of real-world code, which normally manipulates mutable and non-trivial data structures, is a difficult task. In the last few years, many advances have been made in formal verification, but there are still many opportunities to verify real-world code. 

In this project, we explore Coq and the Iris framework to verify the functional correctness of the pointer-based implementation of Splay Trees which is used by the GNU Compiler Collection (GCC) in the Offloading and Multi Processing Runtime Library (libgomp). In the process, we also verify  a  functional  implementation  of  the  splay  tree  algorithm  for  a  generalized  ordered datatype using the interactive proof assistant Coq. To the best of our knowledge, we provide the most complete formally verified pointer-based implementation of Splay Trees.

### Work objectives

* Verify a functional implementation of the splay tree algorithm for a generalized ordered datatype using the interactive proof assistant Coq.
* Verify a real-world imperative, pointer-based implementation of the splay tree algorithm using the interactive proof assistant Coq.
  *  Translate GCC's pointer-based implementation written in the C language to a language that allow us to reason in Iris' framework, heap-lang.
  *  Create a predicate for the splay tree that holds the predicates and invariants for a binary search tree and for the memory that is modeled with a generalized map.
  *  Specify and verify the correctness of the lemmas related to the splay tree methods.



## Content
We have successfully proved a functional implementation of the splay tree algorithm.
This implementation is a translation of Nipkows Isabelle implementation. 

* functional  
  *  theories
     *  SplayTree.v (Holds the proofs of the correctness of the splay tree methods).
     *  XSet.v (Extension of the MSets  coq library over ordered types).
     *  ListTree.v (Function of transformation of tree to list and list to tree).
* gcc_iris
	* Code.v (The translation of the gcc splay tree implementation to heap-lang)
	* Predicate.v (Splay tree predicate)
	* STorientation.v (Orientation proofs related to the binary tree {LEFT, RIGHT})
	* STdomain.v (Proofs related to the domain of the  binary search tree)
	* STlink.v (Proofs related to edges of the binary search tree)
		* Uniqueness of orientation for each edge
		* Uniqueness of edge with same orientation 
	* STpath.v (Proofs on paths in a binary search tree) 
		* Absence of cycles 
		* Unicity of parent of a node 
		* Unicity of path between two nodes in a binary search tree
		* Path finiteness
	 * STedgeset.v (Definition and proofs of manipulation of the Edge Set predicate F)
		 * Add edge 
		 * Remove edge 
		 * Update edge
		 * Union edge
		 * Remove edge over a domain 
		 * Child of root is a binary search tree
		 * Join on mutation of sub-tree
	*  STpathcount.v (Definition of the path find count inductive type and proofs)
		* Path find count termination 
	*  STedgesetrotateroot.v 
		* rotate_XI_if_bst
		* rotate_XE_if_bst
	*  STtrotateleftcasesroot.v (The 8 possible cases proved for the rotate left on the root)
		* rotate_left_BB_st'
		* rotate_left_BL_st'
		* rotate_left_BR_st'
		* rotate_left_BN_st'
		* rotate_left_LB_st'
		* rotate_left_LL_st'
		* rotate_left_LR_st'
		* rotate_left_LN_st'
	*  STtrotaterightcasesroot.v (The 8 possible cases proved for the rotate right on the root)
		* rotate_right_BB_st'
		* rotate_right_BL_st'
		* rotate_right_BR_st'
		* rotate_right_BN_st'
		* rotate_right_RB_st'
		* rotate_right_RL_st'
		* rotate_right_RR_st'
		* rotate_right_RN_st'
	*  STtrotaterightcaseschild.v (The 32 possible cases proved for the rotate right on the child)
	*   STtrotateleftcaseschild.v (The 32 possible cases proved for the rotate left on the child)
	*  STir.v (Proof over the inductive type fw_ir (bw_ir) that models the same behaviour as the splay tree method of the GCC implementation).
		* TODO: Prove of termination!
	*  STsplay.v (Proof of the correctness of the splay tree method) We have divided this proof into several files with the prefix STsplaycases. 
	*  STinsert.v (Proof of the correctness of the insert method for the case where the key does not belong to the tree)


## TODO

Unproven lemma:

### Lemma path_find_count_ir : forall p F F' x x' z n,
```
    Inv p D F V W -> 
      path_find_count F V p x z (4+n) ENDED ->
      bw_ir F V p x' z 4 F' GOING ->
      (exists m y, (m < 4+n)%nat /\ path_find_count F' V x' y z m ENDED).
```

This lemma as been proven informally, however, this proof, without any automatization process, requires a lot of effort, a proof total of 49 subcases which are not trivial since they reason on the transformation of a path!
