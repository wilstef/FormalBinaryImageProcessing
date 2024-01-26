
Require Import Lia.
Require Import PeanoNat.

Definition validpair (p: nat*nat) : bool := (fst p <=? snd p).
Definition samesize (p1 p2: nat*nat) : bool := (snd p1 - fst p1) =? (snd p2 - fst p2).

Definition group (sn: nat) (maxlimit maxsn: nat) : (nat*nat) := 
  ((sn*(maxlimit/maxsn)-(maxlimit/maxsn-1)), sn*(maxlimit/maxsn)).

Lemma lgroups: forall sn1 sn2 avg,
  sn1 < sn2 -> 
  avg <> 0 ->
  sn1 * avg < sn2 * avg - (avg - 1).
Proof.
  intros. nia.
Qed.

Lemma lneqb_neq n: (n =? 0 = false) -> n <> 0.
 Proof.
  intros.
  induction n. 
  + inversion H.
  + red;auto. intro. inversion H0.
 Qed.

Lemma neq_lneqb: forall n,  n <> 0  -> (n =? 0 = false).
 Proof.
 intros n H.
 destruct (Nat.eqb_spec n 0).
 + contradiction.  
 + reflexivity.
Qed. 

Lemma lgroupsbool: forall sn1 sn2 avg,
  sn1 * avg < sn2 * avg - (avg - 1) ->
  (sn1 * avg <? sn2 * avg - (avg - 1) = true).
Proof.
  intros. rewrite -> PeanoNat.Nat.ltb_lt. auto.  
Qed.

Lemma mdivn_non_zero: forall m n, 
  n <=? m = true ->
  n =? 0 = false ->
  (Nat.div m n =? 0) = false.
Proof.
  intros. 
  rewrite PeanoNat.Nat.leb_le in H.
  rewrite neq_lneqb. auto.
  assert (n <> 0). apply lneqb_neq. auto.
  destruct H0.
  pose proof (PeanoNat.Nat.div_str_pos m n).
  lia.
Qed.

Lemma webmaxbysnmax_non_zero: forall webmax snmax, 
  snmax <=? webmax = true ->
  (snmax =? 0) = false ->
  (webmax / snmax =? 0) = false.
Proof.
  intros. 
  apply mdivn_non_zero. auto. auto.
Qed.

Lemma groupmintrue: forall (sn1 sn2 webmax snmax:nat),
  let g1 := group sn1 webmax snmax in
  let g2 := group sn2 webmax snmax in
  snmax <=? webmax = true ->  (*total entities must be greather the total groups.*)
  snmax =? 0 = false ->
  sn1 =? 0 = false ->     (*Serial numbers can't be 0*)
  sn2 =? 0 = false -> 
  sn1 <> sn2 -> 
  ((sn1 < sn2 -> snd g1 <? fst g2 = true) \/
   (sn2 < sn1 -> snd g2 <? fst g1 = true)). 
Proof.
  intros.
  left. 
  intro.
  simpl.
  induction sn1.
  + simpl in *. inversion H1.
  + induction sn2.
    - simpl in *. inversion H2.
    - rewrite PeanoNat.Nat.ltb_lt. eapply lgroups. apply H4.
      apply lneqb_neq.
     apply webmaxbysnmax_non_zero. apply H.
     auto.
Qed. 
