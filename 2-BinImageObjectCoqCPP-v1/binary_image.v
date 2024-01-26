(** In this script, binary immages are defined as a list of pixels, few basic functions, such as
  colour equality, are also defined. *)

Require Export List.
Require Export Arith.
Require Export Bool.

(*Binary color*)
Inductive color: Type:=
 | white: color
 | black: color
 | blurr: color.

(*Pixel of a binary images*)
Inductive pixel: Type :=
 | Pixel (r c: nat) (col: color).

Notation "B{ r , c , col }" := (Pixel r c col).
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : list_scope.

Fixpoint pixcol (r c: nat) (img: list pixel) : color :=
 match img with
 | nil => blurr (*default*)
 | B{r',c',col'}::tl => if (r' =? r) && (c' =? c) then col' else pixcol r c tl
 end.

Notation "C{ r ! c ! img }" := (pixcol r c img). 

Definition coleq (c1 c2: color) : bool :=
 match c1, c2 with
 | black, black => true
 | white, white => true
 | blurr, blurr => true
 | _, _ => false
 end. 

(*Checks if two pixels are equal upto their colors*)
Definition colpixEq (p q: pixel) : bool :=
 match p, q with
 | B{pr,pc,pcol}, B{qr,qc,qcol} => coleq pcol qcol
 end. 


(*******************************Grayscale image ***********************)

(*Pixel of grayscale image*)
Inductive gspixel: Type :=
 | GSPixel (r c v: nat). 

(*Gray scaleimage*)
Definition gsimage := list gspixel.

Notation "G{ r , c , v }" := (GSPixel r c v).

(*Creates grayscale image (as defined in Coq) from the grayscal matrix image*)
Fixpoint createimage (matrix: list nat) (row: nat) (col: nat) (maxcol: nat): gsimage :=
 match matrix with 
 | nil => nil
 | cons gray m => 
      match row, col with
      | O, O => [G{row, col, gray}] 
      | S r, O => (createimage m r maxcol maxcol) ++ [G{row, col, gray}]
      | O, S c => (createimage m row c maxcol) ++ [G{row, col, gray}]
      | S r, S c => (createimage m row c maxcol) ++ [G{row, col, gray}]
      end 
 end.

(************** Axillary Lemmas ***********************)

Theorem plus_S : forall n:nat, n + 1 = S n.
 Proof.
  intros.
  induction n as [| n' IHn'].  
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
 Qed.

Lemma sub_n_o: forall n, n - 0 = n. 
Proof. 
 intro. 
 induction n; simpl; auto.
Qed. 

Lemma bool_dec: forall b:bool, (b = true) \/ (b = false).
Proof. 
 intro.
 induction b; simpl; auto.
Qed.

Lemma gtb_true_S: forall n m, S n <? m = true ->  n <? m = true. 
Proof. 
 intros.
 rewrite Nat.ltb_lt in *. 
 induction H; simpl; auto.
Qed.

Lemma and_b_true: forall b, b && true = b.
Proof. 
 intro.
 destruct b; simpl; auto.
Qed. 

Lemma and_comm: forall b1 b2, b1 && b2 = b2 && b1.
Proof. 
 intros. 
 destruct b1, b2; simpl; auto. 
Qed. 
