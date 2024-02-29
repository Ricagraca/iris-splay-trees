From iris_time.heap_lang Require Import notation lib.assert.
From iris_time.heap_lang Require Import proofmode.
From iris_time.heap_lang Require Import proofmode.

Section code.
  
Context `{!heapG Σ}.
Notation iProp := (iProp Σ).
Implicit Types l : loc.

Definition create_node : val :=
  λ: "v", ref (SOME ("v", (NONE, NONE))).

Definition right_child : val :=
  λ: "v",
  match: !"v" with
    NONE     => NONE
  | SOME "p" =>
    Snd (Snd "p")
  end.

Definition left_child : val :=
  λ: "v",
  match: !"v" with
    NONE     => NONE
  | SOME "p" =>
    Fst (Snd "p")
  end.

Definition value : val :=
  λ: "v",
  match: !"v" with
    NONE     => NONE
  | SOME "p" =>
    Fst "p"
    end. 

Definition rotate_left : val :=
   λ: "pp" "p" "n",
   let: "tmp" := (right_child "n") in
   "n" <- (SOME (value "n", (left_child "n", "p"))) ;;
   "p" <- (SOME (value "p", ("tmp", right_child "p")));;
   "pp" <- "n".

Definition rotate_right : val :=
   λ: "pp" "p" "n",
   let: "tmp" := (left_child "n") in
   "n" <- (SOME (value "n", ("p", right_child "n"))) ;;
   "p" <- (SOME (value "p", (left_child "p", "tmp")));;
   "pp" <- "n".

Definition splay_compare : val :=
  λ: "k" "k'",
  if: "k" = "k'" then
    #0
  else
    if: "k" < "k'" then
      #(-1)
    else
      #1
.
  
Definition splay_tree_while_loop : val :=
  rec: "func" "sp'" "key" :=
    let: "n" := !"sp'" in
    let: "cmp1" := splay_compare "key" (value ("n")) in
    if: "cmp1" = #0 then
      #()
    else (
        let: "c" := (
             if: "cmp1" < #0 then
               ( left_child  ("n") )
             else
               ( right_child ("n") )
           ) in 
        if: ("c" = NONE) then
          #()
        else
          let: "cmp2" := splay_compare "key" (value "c") in 
          if: ("cmp2" = #0)
              || (("cmp2" < #0) && ((left_child  "c") = NONE))
              || ((#0 < "cmp2") && ((right_child "c") = NONE)) then
            (
              if: ("cmp1" < #0) then 
                rotate_left  "sp'" "n" "c"
              else
                rotate_right "sp'" "n" "c"
            ) ;; #()
          else (
              if: ("cmp1" < #0) && ("cmp2" < #0) then
                (let: "tmp" := (ref "c") in 
                 rotate_left ("tmp") "c" (left_child "c") ;;
                 "n" <- SOME (value "n", (!"tmp", right_child "n"))) ;;
                rotate_left ("sp'") "n" (left_child "n")
              else if: (#0 < "cmp1") && (#0 < "cmp2") then
                     (let: "tmp" := (ref "c") in 
                      rotate_right ("tmp") "c" (right_child "c") ;;
                      "n" <- SOME (value "n", (left_child "n", !"tmp"))) ;; 
                     rotate_right ("sp'") "n" (right_child "n")
                   else if: ("cmp1" < #0) && (#0 < "cmp2") then
                          (let: "tmp" := (ref "c") in 
                           rotate_right ("tmp") "c" (right_child "c") ;;
                           "n" <- SOME (value "n", (!"tmp", right_child "n"))) ;; 
                          rotate_left ("sp'") "n" (left_child "n")
                        else if: (#0 < "cmp1") && ("cmp2" < #0) then
                               (let: "tmp" := (ref "c") in 
                                rotate_left ("tmp") "c" (left_child "c") ;;
                                "n" <- SOME (value "n", (left_child "n", !"tmp"))) ;; 
                               rotate_right ("sp'") "n" (right_child "n")
                             else
                               #()
            ) ;;
               "func" "sp'" "key"
      ).
                          
Definition splay_tree_splay : val :=
  λ: "sp" "key",
  if: !"sp" = NONE then
    #()
  else
    splay_tree_while_loop "sp" "key"
.

Definition splay_tree_insert : val :=
  λ: "sp" "n",
  splay_tree_splay "sp" (value "n") ;;
  let: "comparison" := (
       if: !"sp" ≠ NONE then
         splay_compare (value (!"sp")) (value "n")
       else
         #0
     ) in
  if: (!"sp" ≠ NONE) && ("comparison" = #0) then
    #()
  else (
    if: (!"sp" = NONE) then
      "n" <- SOME(value "n", (NONE, NONE))
    else if: ("comparison" < #0) then
      "n" <- SOME(value "n", (!"sp",right_child "n")) ;;
      "n" <- SOME(value "n", (left_child "n", right_child (left_child "n"))) ;;
      (left_child "n") <- SOME(value (left_child "n"), (left_child (left_child "n"),NONE))
    else
      "n" <- SOME(value "n", (left_child "n", !"sp")) ;;
      "n" <- SOME(value "n", (left_child (right_child "n"), right_child "n")) ;;
      (right_child "n") <- SOME(value (right_child "n"), (NONE,right_child (right_child "n")))
  ) ;;
  "sp" <- "n"     
.

  
Definition splay_tree_remove : val :=
  λ: "sp" "key",
  splay_tree_splay "sp" "key" ;;
  if: (!"sp" ≠ NONE) && ((splay_compare (value(!"sp")) "key") = #0) then (
    let: "left" := ref (left_child (!"sp")) in 
    let: "right" := ref (right_child (!"sp")) in 
    if: (!"left" ≠ NONE) then (
      "sp" <- !"left" ;;
      if: (!"right" ≠ NONE) then
        (
          rec: "func" "left'" :=
            if: (right_child (!"left'") ≠ NONE) then
              "left" <- (right_child (!"left")) ;;
              "func" "left'"
            else #()
        ) "left" ;;
        !"left" <- SOME(value !"left", (left_child !"left", !"right"))
      else #()
    )
    else
      "sp" <- !"right"
  )
  else #()
.

Definition splay_tree_lookup : val :=
  λ: "sp" "key",
  splay_tree_splay "sp" "key" ;;
  if: (!"sp" ≠ NONE) && (splay_compare (value !"sp") "key" = #0) then
    "key"
  else
    NONE
.

Definition splay_tree_foreach_internal : val :=
  rec: "func" "n" "f" :=
  if: ("n" = NONE) then
    #()
  else
    "n" <- SOME("f" (value "n"), (left_child "n", right_child "n"));;
    "func" (left_child "n") "f" ;;
    "func" (right_child "n") "f"
.

Definition splay_tree_foreach : val := 
  λ: "sp" "f",
  splay_tree_foreach_internal (!"sp") "f"
.                              
  
End code.
