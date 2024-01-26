(** In this file, neighbours 8 of a pixel, path between any two pixel, connectivity of
 any two pixels in an image are defined. Furthermore, it is proved that the connectivity
 relation is an equivalence relation by proving it is relfexive, commutative and transitive *)

Require Export pixel_connectivity_4_equiv.

(*eight neighbours of a pixel. Every pixel has eight neighbours located
  on the left, right, up and down and at the diagonals. *)
Definition neighbours_8 (r c: nat) (p: pixel) (img: list pixel): list pixel := 
 match p with
  | B{r', c', col} => if (r' <?  r ) && 
                         (c' <?  c)  then
    match r', c' with  
    | 0, 0 => [B{1,0,C{1!0!img}};B{0,1,C{0!1!img}};B{1,1,C{1!1!img}}]
    | 0, c => [B{1,c,C{1!c!img}};B{1,c-1,C{1!c-1!img}};B{1,c+1,C{1!c+1!img}};
               B{0,c+1,C{0!c+1!img}};B{0,c-1,C{0!c-1!img}}]
    | r, 0 => [B{r+1,0,C{r+1!0!img}};B{r+1,1,C{r+1!1!img}};B{r-1,0,C{r-1!0!img}};
               B{r-1,1,C{r-1!1!img}};B{r,1,C{r!1!img}}]
    | _, _ => [B{r'+1,c',C{r'+1!c'!img}};B{r'+1,c'-1,C{r'+1!c'-1!img}};B{r',c'-1,C{r'!c'-1!img}};
               B{r'-1,c'-1,C{r'-1!c'-1!img}};B{r'-1,c',C{r'-1!c'!img}};B{r'-1,c'+1,C{r'-1!c'+1!img}};
               B{r',c'+1,C{r'!c'+1!img}};B{r'+1,c'+1,C{r'+1!c'+1!img}}]
    end
   else []
end.

(*Path between any two pixels p and q.
 - a pixel has a path with itself
 - if a pixel q is in neighbours of pixel p, then there is a path 
   from p to q.
 - if there is a path from p to q and q to r, then there is a path from
   p to r.*)
Inductive path_8: pixel -> pixel -> list pixel -> Prop :=
 | path_8_self: forall p img, path_8 p p img
 | path_8_neigh: forall r c qr qc pr pc p q img, r > 0 -> c > 0->
   p = B{pr,pc,C{pr!pc!img}} ->
   q = B{qr,qc,C{qr!qc!img}} ->
   C{pr!pc!img} = C{qr!qc!img} ->
   List.In q (WF_neighbours r c ( neighbours_8 r c p img)) -> path_8 p q img
 | path_8_trans: forall p q r img, path_8 p q img -> path_8 q r img -> path_8 p r img.

(*Two pixels are connected, if there is a path between them.*)
Inductive connected_8: pixel -> pixel -> list pixel -> Prop:=
 | Connected_8: forall p q img, path_8 p q img -> connected_8 p q img.

(**************************Boolean path and connected*********************************)

Definition pixcolpix(p: pixel): color:=
 match p with
 | B{r,c,col} => col
 end. 

Definition pixeq (p q: pixel) : bool :=
 match p, q with
 | B{pr,pc,pcol}, B{qr,qc,qcol} => (pr =? qr) && (pc =? qc) && coleq pcol qcol
 end.

(*Removes blurred pixels from the list of pixels (image).*)
Fixpoint removeblurN (img: list pixel) : list pixel :=
 match img with
 | nil => nil
 | B{nqr,nqc,blurr}::tl => removeblurN tl 
 | h::tl =>  h::(removeblurN tl)
 end.

(*Sets the color of a pixel at coordinates r,c in image img to col*)
Fixpoint setColourPix (r c: nat) (col: color) (img: list pixel) : list pixel :=
 match img with
 | nil => nil
 | B{pr,pc,pcol}::tl => if (pr =? r) && (pc =? c) then B{pr,pc,col}::tl
                        else  B{pr,pc,pcol}::(setColourPix r c col tl)
 end.

(*Sets the color of the pixel p to col in image image img.*)
Definition setColourPixImg (p: pixel) (col: color) (img: list pixel) : list pixel :=
 match p with
 | B{pr,pc,pcol} => (setColourPix pr pc col img)
 end.

(*removes those pixels from the image which have different color than the pixel p*)
Fixpoint removeDiffCol (p: pixel) (img: list pixel) : list pixel :=
 match img with
 | nil => nil
 | hd::tl => if colpixEq p hd then hd::(removeDiffCol p tl)
             else removeDiffCol p tl
 end.

(*Checks if pixel p has a path to pixel q. r and c are the dimension of the image, size is 
  the number of pixels in the image and nbr is the neighbours of q (initially set to nil) and
  img is the image. 
  In iteration, pixels p and q are tested to have the same colours. *)
Fixpoint path_8_b (r c size: nat) (p q: pixel) (nbr: list pixel) (img: list pixel): bool :=
 match size with
 | O => false 
 | S size' => (colpixEq p q) &&  (*p and q should have the same colors*)
 if (pixeq p q) then true else
  let Nq :=  removeblurN (removeDiffCol q (WF_neighbours r c (neighbours_8 r c q img))) ++ nbr in 
  match Nq with
  | nil => false
  | nq::tl' => if colpixEq nq q then 
                path_8_b r c size' p nq tl' (setColourPixImg q blurr img)
               else false 
   end
  end.

(*two pixels p and q are connected if there is a path from p to q*)
Definition connected_8_b (row col: nat) (p q: pixel) (object: list pixel) := 
   path_8_b row col (row*col) p q nil object. 

(*checks if a pixel 'pix' is connected to every other pixel of the object 'obj'. *)
Fixpoint connected_8_b_pix_obj (row col: nat) (pix: pixel) (rem: list pixel) (object: list pixel) :=
  match rem with
 | nil => true
 | p::tl => (connected_8_b row col pix p object) && 
             connected_8_b_pix_obj row col pix tl object
 end.  

(*checks if every pixel of the object is connected to every other pixel of the object. *)
Fixpoint connected_8_all_b (row col: nat) (rem: list pixel) (object: list pixel) : bool :=
 match rem with
 | nil => true 
 | p::tl => (connected_8_b_pix_obj row col p object object) && 
             connected_8_all_b row col tl object
 end. 

(*Well-formed object: an image object is well-formed if all the pixels of the object are 
  connected to every other pixel. *)
Definition WF_object_8_b (row col: nat) (obj: list pixel) : bool := 
        connected_8_all_b row col obj obj.

(********************************************************)
(************ Proof of image properties *****************)
(********************************************************)

(*If p is neighbour of q, then q is neighbout of p*)
Lemma neighbouts8_comm: forall (r c: nat) (p q: pixel) (pr pc qr qc: nat) (img: list pixel), 
   r > 0 ->
   c > 0 ->
   p = B{pr,pc,C{pr!pc!img}} ->
   q = B{qr,qc,C{qr!qc!img}} ->
     List.In p (WF_neighbours r c (neighbours_8 r c q img)) -> 
     List.In q (WF_neighbours r c (neighbours_8 r c p img)).
Proof. 
 intros r c p q pr pc qr qc img H H0 Hp Hq H1.
 rewrite Hp, Hq in *.
 assert ( 0 <? r = true) as Hr by try (apply Nat.ltb_lt; auto).
 assert ( 0 <? c = true) as Hc by try (apply Nat.ltb_lt; auto).
 destruct pr as [ | pr']; destruct pc as [ | pc']; 
 destruct qr as [ | qr']; destruct qc as [ | qc'].
 + (*Case 1: p is at (0,0) and q is at (0,0) *)
  simpl in *.
  rewrite Hr, Hc in *; simpl in *.
  assert ((1 <? r) = true \/ (1 <? r) = false) by apply bool_dec.
  destruct H2 as [ Hgtr | Hngtr].
  - rewrite Hgtr, Hc in H1; simpl in *.
    assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
    destruct H2 as [ Hgtc | Hngtc].
    * rewrite Hgtc, Hr in H1; simpl in *.
      inversion H1. inversion H2.
      inversion H2. inversion H3.
      inversion H3. inversion H4.
      inversion H4.
    * rewrite Hngtc, Hr in H1; simpl in *.
      inversion H1. inversion H2. inversion H2.
   - rewrite Hngtr in H1; simpl in *.
     assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
     destruct H2 as [ Hgtc | Hngtc].
     * rewrite Hgtc, Hr in H1; simpl in *.
       inversion H1. inversion H2.
       inversion H2.
     * rewrite Hngtc, Hr in H1; simpl in *.
       inversion H1.
 + (*Case 2: p is at (0,0) and q is at (0,c) *)
  simpl in *.
  rewrite Hr, Hc in *; simpl in *.
  assert (S qc' <? c = true \/ S qc' <? c = false) as HgtbcS 
    by apply bool_dec; destruct HgtbcS as [HgtcS | HngtcS].    
  - rewrite HgtcS in H1; simpl in *.
    rewrite HgtcS in H1.
    assert ((1 <? r) = true \/ (1 <? r) = false) by apply bool_dec.
    destruct H2 as [ Hgtr1 | Hngtr1].
    * rewrite Hgtr1 in H1; simpl in *. 
      rewrite sub_n_o in *.
      rewrite plus_S in *. 
      assert (qc' <? c = true \/ qc' <? c = false) as Hgtcb 
       by apply bool_dec; destruct Hgtcb as [Hgtc | Hngtc].    
      { rewrite Hgtc in H1; simpl in *.
        assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
         by apply bool_dec; destruct HgtbcSS as [HgtcSS | HngtcSS].    
       { rewrite HgtcSS, Hr in H1; simpl in *.
        inversion H1. inversion H2. inversion H2.
        inversion H3. inversion H3. inversion H4.
        inversion H4. inversion H5.
        inversion H5. inversion H6.
        { rewrite H8 in *.
          rewrite Hc, HgtcS, Hgtr1; simpl.
          right. rewrite Hr; simpl.
          left; auto.
        }
        inversion H6.
       }
       rewrite HngtcSS in H1.
       rewrite Hr in H1; simpl in *.
       inversion H1.
       { inversion H2. } inversion H2. inversion H3.
       inversion H3. 
       { inversion H4.
        rewrite H6, Hr, Hc in *; simpl in *.
        rewrite Hgtr1; simpl. 
        right. rewrite HgtcS. simpl; left; auto.
       } 
       inversion H4.
      }
      rewrite Hngtc, Hr, Hc in *; simpl in *. 
      assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
         by apply bool_dec; destruct HgtbcSS as [HgtcSS | HngtcSS].    
       { rewrite HgtcSS in H1; simpl in *.
         inversion H1. inversion H2. inversion H2.  inversion H3.
         inversion H3. inversion H4. inversion H4.
       }
       rewrite HngtcSS in H1.
       inversion H1. inversion H2. inversion H2.
     * rewrite Hr in H1; simpl in *.
       rewrite Hngtr1 in H1; simpl in *.
       rewrite Hngtr1, Hc, plus_S in *; simpl in *.
       assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
         by apply bool_dec; destruct HgtbcSS as [HgtcSS | HngtcSS].    
       { rewrite HgtcSS in H1; simpl in *.
         rewrite sub_n_o in H1.
         assert (qc' <? c = true) as Hgtc by (try apply gtb_true_S; auto); 
          rewrite Hgtc in H1; simpl.
         inversion H1. inversion H2. inversion H2.
         { inversion H3.
           rewrite H5 in *. 
           rewrite Hr, HgtcS; simpl. left; auto.
         }
         inversion H3.
        }
        rewrite HngtcSS, Hr, sub_n_o in *; simpl in *.
         assert (qc' <? c = true) as Hgtc by (try apply gtb_true_S; auto); 
          rewrite Hgtc in H1; simpl.
        inversion H1. inversion H2.
        { rewrite H4 in *.
          rewrite HgtcS. left; auto.
        }
        inversion H2.
      - rewrite HngtcS, Hc in *; simpl in *.
        inversion H1.
 + (*Case 3: p is at (0,0) and q is at (c,0) *)
   simpl in *.
   rewrite Hr, Hc in *; simpl in *.
   assert (S qr' <? r = true \/ S qr' <? r = false) as HgtbrS 
    by apply bool_dec; destruct HgtbrS as [HgtrS | HngtrS].
   - rewrite HgtrS in H1; simpl in *.
     rewrite Hc in *.
     rewrite HgtrS in H1.
     rewrite sub_n_o in *.
     rewrite plus_S in *.
     assert (S (S qr') <? r = true \/ S (S qr') <? r = false) as HgtbrSS 
         by apply bool_dec; destruct HgtbrSS as [HgtrSS | HngtrSS].    
     * rewrite HgtrSS in H1; simpl in *.
       assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
       destruct H2 as [ Hgtc1 | Hngtc1].
       { rewrite Hgtc1 in H1; simpl in *.    
         assert (qr' <? r = true) as Hgtr by (try apply gtb_true_S; auto); 
         rewrite Hgtr in H1; simpl in *.
         inversion H1. inversion H2.
         inversion H2. inversion H3.
         inversion H3.
         { inversion H4.
           rewrite H6 in *.
           assert ((1 <? r) = true \/ (1 <? r) = false) by apply bool_dec.
           destruct H5 as [ Hgtr1 | Hngtr1].
           { rewrite Hgtr1; simpl.
             rewrite Hr, Hgtc1; simpl. 
             left; auto.
           }
           rewrite Hngtr1; simpl.
           rewrite HgtrS in Hngtr1. inversion Hngtr1. 
         }
         inversion H4. inversion H5.
         inversion H5. inversion H6.
         inversion H6.
       }
       rewrite Hngtc1 in H1.
       assert (qr' <? r = true) as Hgtr by try (apply gtb_true_S; auto).
       rewrite Hgtr in H1; simpl in *.
       inversion H1. inversion H2.
       inversion H2. inversion H3.
       rewrite H5 in *.
       rewrite HgtrS, Hr, Hngtc1; simpl.
       left; auto.
       inversion H3. 
     * rewrite HngtrSS in H1; simpl in *. 
       assert (qr' <? r = true) as Hgtr by try (apply gtb_true_S; auto).
       rewrite Hgtr in H1; simpl in *.
       assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
       destruct H2 as [ Hgtc1 | Hngtc1].
       { rewrite Hgtc1 in H1; simpl.
         inversion H1. inversion H2.
         { rewrite H4 in *.
           rewrite HgtrS, Hr, Hgtc1; simpl.
           left; auto.
         }
         inversion H2. inversion H3.
         inversion H3. inversion H4.
         inversion H4.
       }
       rewrite Hngtc1 in H1.
       inversion H1. inversion H2.
       { rewrite H4 in *.
         rewrite HgtrS; simpl. 
         left; auto.
       }
       inversion H2.
    - rewrite HngtrS in H1; simpl in *.
      inversion H1.
 + (*Case 4: p is at (0,0) and q is at (c,r) *)
   simpl in *.
   rewrite Hr, Hc in *; simpl in *.
   assert (S qr' <? r = true \/ S qr' <? r = false) as HgtbrS 
    by apply bool_dec. 
   assert (S qc' <? c = true \/ S qc' <? c = false) as HgtbcS 
    by apply bool_dec. 
   destruct HgtbrS as [HgtrS | HngtrS]; destruct HgtbcS as [HgtcS | HngtcS].
   * rewrite Hc, HgtrS, HgtcS in *; simpl in *.
     rewrite HgtrS in H1.
     rewrite HgtcS in H1.
     rewrite sub_n_o in *.
     rewrite plus_S in *.
     assert (S (S qr') <? r = true \/ S (S qr') <? r = false) as HgtbrSS 
         by apply bool_dec; destruct HgtbrSS as [HgtrSS | HngtrSS].    
     - rewrite HgtrSS in H1; simpl in *.
       assert (qc' <? c = true) as Hgtc by try (apply gtb_true_S; auto).
       rewrite Hgtc in H1; simpl in *.
       rewrite sub_n_o in *.
       assert (qr' <? r = true) as Hgtr by try (apply gtb_true_S; auto).
       rewrite Hgtr in H1; simpl in *.
       rewrite plus_S in *.
       assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
         by apply bool_dec; destruct HgtbcSS as [HgtcSS | HngtcSS].    
       { rewrite HgtcSS in H1.
         inversion H1. inversion H2.
         inversion H2. inversion H3.
         inversion H3. inversion H4.
         inversion H4. inversion H5.
         { rewrite H7, H8 in *. 
           rewrite HgtrS, Hr, HgtcS; simpl. 
           right. right; left; auto.
         }
         inversion H5. inversion H6.
         inversion H6. inversion H7.
         inversion H7. inversion H8.
         inversion H8. inversion H9.
         inversion H9.
       }
       rewrite HngtcSS in H1. 
       inversion H1. inversion H2.
       inversion H2. inversion H3.
       inversion H3. inversion H4.
       inversion H4. inversion H5.
       { rewrite H7, H8, Hr in *; simpl in *.
         rewrite HgtrS; simpl. 
         right. rewrite HgtcS; simpl. 
         right; left; auto.
       }
       inversion H5.
       inversion H6.
       inversion H6.
    - rewrite HngtrSS in H1; simpl in *.  
      assert (qc' <? c = true) as Hgtc by try (apply gtb_true_S; auto).
      rewrite Hgtc in H1; simpl in *.
      rewrite sub_n_o in *.
      assert (qr' <? r = true) as Hgtr by try (apply gtb_true_S; auto).
      rewrite Hgtr in H1; simpl in *.
      rewrite plus_S in *.
      assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
         by apply bool_dec; destruct HgtbcSS as [HgtcSS | HngtcSS].
      { rewrite HgtcSS in H1.
        inversion H1. inversion H2.
        inversion H2. inversion H3.
        rewrite H5, H6 in *.
        rewrite HgtrS, Hr, HgtcS; simpl. 
        right; right; left; auto.
        inversion H3. inversion H4.
        inversion H4. inversion H5.
        inversion H5. inversion H6.
        inversion H6.
      }
      rewrite HngtcSS in H1.
      inversion H1. inversion H2.
      inversion H2. inversion H3.
      { rewrite H5, H6 in *; simpl in *.
        rewrite HgtrS, Hr, HgtcS; simpl. 
        right; right; left; auto.
      }
      inversion H3. inversion H4.
      inversion H4.
   * rewrite HgtrS, HngtcS in H1; simpl in *.
     inversion H1.
   * rewrite HngtrS, HgtcS in H1; simpl in *.
     inversion H1.
   * rewrite HngtrS, HngtcS in H1; simpl in *.
     inversion H1.
 + (*Case 5: p is at (0,r) and q is at (0,0) *)
   simpl in *.
   rewrite Hr, Hc in *; simpl in *.
   rewrite Hc, sub_n_o, plus_S in *.
   assert ((1 <? r) = true \/ (1 <? r) = false) by apply bool_dec.
   destruct H2 as [ Hgtr1 | Hngtr1].
   - rewrite Hgtr1, Hr in H1; simpl in *.
     assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
     destruct H2 as [ Hgtc1 | Hngtc1].
     { rewrite Hgtc1 in H1.
       inversion H1. inversion H2.
       inversion H2. inversion H3.
       { rewrite <- H5 in *.
         rewrite Hgtc1; simpl.
         rewrite Hgtr1, Hgtc1, Hc; simpl. 
         right; right.
         assert ((2 <? c) = true \/ (2 <? c) = false) by apply bool_dec.
         destruct H4 as [ Hgtc2 | Hngtc2].
         rewrite Hgtc2, Hr; simpl.
         right; right; left; auto.
         rewrite Hngtc2, Hr; simpl. left; auto.
       }
       inversion H3. inversion H4. 
       inversion H4.
     }
     rewrite Hngtc1 in H1.
     inversion H1. inversion H2. inversion H2.
    - rewrite Hngtr1 in H1; simpl in *.
      assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
      destruct H2 as [ Hgtc1 | Hngtc1].
      { rewrite Hr, Hgtc1 in H1; simpl in *.
        inversion H1. inversion H2.
        { rewrite <- H4 in *.
          rewrite Hgtc1; simpl. 
          rewrite Hngtr1, Hgtc1; simpl. 
          assert ((2 <? c) = true \/ (2 <? c) = false) by apply bool_dec.
          destruct H3 as [ Hgtc2 | Hngtc2].
          { rewrite Hr, Hgtc2, Hc; simpl.
            right; left; auto. 
          }
          rewrite Hngtc2, Hr, Hc; simpl.
          left; auto. 
        } 
        inversion H2. 
      }
      rewrite Hr, Hngtc1 in H1; simpl in *.
      inversion H1.
 + (*Case 6: p is at (0,r) and q is at (0,c) *)
   simpl in *.
   rewrite Hr in *; simpl in *.
   rewrite sub_n_o, plus_S in *.
   assert (S qc' <? c = true \/ S qc' <? c = false) as HgtbcS 
    by apply bool_dec. 
   destruct HgtbcS as [HgtbcS | HngtbcS].
   - rewrite HgtbcS in *; simpl in *.
   assert ((1 <? r) = true \/ (1 <? r) = false) by apply bool_dec.
   destruct H2 as [ Hgtr1 | Hngtr1].
   * rewrite Hgtr1, HgtbcS in H1; simpl in *.
     assert (qc' <? c = true) as Hgtc by try (apply gtb_true_S; auto).
     rewrite Hgtc in H1; simpl in *.
     assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
         by apply bool_dec; destruct HgtbcSS as [HgtcSS | HngtcSS].
     { rewrite HgtcSS, Hr in H1; simpl in *.
       inversion H1. inversion H2.
       inversion H2. inversion H3.
       inversion H3. inversion H4.
       inversion H4. inversion H5.
       { rewrite H7 in *; simpl in *.
         rewrite HgtcSS; simpl.
         rewrite Hgtr1, HgtcSS; simpl.
         right; simpl. 
         rewrite HgtbcS.
         assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbcSS 
         by apply bool_dec; destruct HgtbcSS as [HgtcSSp | HngtcSSp].
         { rewrite HgtcSSp; simpl. 
           right. right. 
           rewrite Hr; simpl. 
           right; left; auto.
         }
         rewrite HngtcSSp, Hr; simpl.
         right; left; auto.
       }
       inversion H5. inversion H6.
       rewrite H8 in *; simpl in *.
       rewrite Hgtc; simpl. 
       rewrite Hgtr1, Hgtc; simpl. 
       right. 
       assert (pc' <? c = true) as Hgtcp by try (apply gtb_true_S; auto).
       rewrite Hgtcp; simpl in *. right.
       rewrite HgtbcS, Hr; simpl. 
       right; left; auto.
       inversion H6.
     }
     rewrite HngtcSS, Hr in H1; simpl in *.
     inversion H1. inversion H2.
     inversion H2. inversion H3.
     inversion H3. inversion H4. 
     { rewrite H6 in *.
       rewrite Hgtc; simpl. 
       rewrite Hgtr1, Hgtc; simpl. right.
       assert (pc' <? c = true) as Hgtcp by try (apply gtb_true_S; auto).
       rewrite Hgtcp; simpl in *. right.
       rewrite HgtbcS. rewrite Hr; simpl. 
       right; left; auto.
     }
     inversion H4.
   * rewrite HgtbcS, Hngtr1 in H1; simpl in *.
     assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
         by apply bool_dec; destruct HgtbcSS as [HgtcSSp | HngtcSSp].
     { rewrite HgtcSSp, Hr in H1; simpl in *.
       assert (qc' <? c = true) as Hgtcq by try (apply gtb_true_S; auto).
       rewrite Hgtcq in H1; simpl in *. 
       inversion H1. inversion H2.
       { rewrite H4 in *.
         rewrite HgtcSSp; simpl. 
         rewrite Hngtr1; simpl. 
         assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbcSS 
         by apply bool_dec; destruct HgtbcSS as [HgtcSS | HngtcSS].
         { rewrite HgtcSS, Hr; simpl. 
           right; rewrite HgtbcS; simpl; left; auto.
         }
         rewrite HngtcSS, Hr; simpl.
         rewrite HgtbcS; simpl; left; auto.
       }
       inversion H2. inversion H3.
       { rewrite H5 in *.
         rewrite Hgtcq; simpl. 
         rewrite Hngtr1; simpl. 
         rewrite Hr, HgtbcS; simpl. 
         left; auto. 
       }
       inversion H3.
     }
     rewrite HngtcSSp, Hr in H1; simpl in *.
     assert (qc' <? c = true) as Hgtcq by try (apply gtb_true_S; auto).
     rewrite Hgtcq in H1; simpl in *.
     inversion H1. inversion H2.
     { rewrite H4 in *.
       rewrite Hgtcq; simpl. 
       rewrite Hngtr1; simpl. 
       rewrite Hr, HgtbcS; simpl. 
       left; auto.
     } inversion H2.
  - rewrite HngtbcS in H1; simpl in *.
    inversion H1.
 + (*Case 7: p is at (0,c) and q is at (r,0) *)
   simpl in *.
   rewrite Hr, Hc in *; simpl in *.
   rewrite sub_n_o, plus_S in *.
   assert (S qr' <? r = true \/ S qr' <? r = false) as HgtbrS 
    by apply bool_dec. 
   destruct HgtbrS as [HgtbrS | HngtbrS].
   - rewrite HgtbrS in *; simpl in *. rewrite Hc in *.
     assert (S (S qr') <? r = true \/ S (S qr') <? r = false) as HgtbrSS 
         by apply bool_dec; destruct HgtbrSS as [HgtrSSq | HngtrSSq].
     * rewrite HgtrSSq in H1; simpl in *.
       assert (qr' <? r = true) as Hgtrq by try (apply gtb_true_S; auto).
       rewrite Hgtrq in H1; simpl in *.
       assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
       destruct H2 as [ Hgtc1 | Hngtc1].
       { rewrite Hgtc1 in *; simpl in *.
         rewrite HgtbrS in H1; simpl in *.
         inversion H1. inversion H2.
         inversion H2. inversion H3.
         inversion H3. inversion H4.
         inversion H4. inversion H5.
         { rewrite H7, Hgtc1 in *; rewrite <- H8 in *; simpl in *.
           rewrite HgtbrS, Hgtc1; simpl. right.
           rewrite Hc; simpl. left; auto.
         }
         inversion H5. inversion H6. inversion H6.
       }
       rewrite Hngtc1 in H1; simpl in *.
       rewrite HgtbrS in H1; simpl in *.
       inversion H1. inversion H2.
       inversion H2. inversion H3. inversion H3.
     * rewrite HngtrSSq in H1; simpl in *.
       assert (qr' <? r = true) as Hgtrq by try (apply gtb_true_S; auto).
       rewrite Hgtrq in H1; simpl in *.
       assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
       destruct H2 as [ Hgtc1 | Hngtc1].
       { rewrite Hgtc1 in H1.
         rewrite HgtbrS in H1; simpl in *.
         inversion H1. inversion H2.
         inversion H2. inversion H3.
         { rewrite H5, Hgtc1 in *; rewrite <- H6 in *; simpl in *.
           rewrite HgtbrS, Hgtc1, Hc; simpl.
           right; left; auto.
         }
         inversion H3. inversion H4. inversion H4.
       }
       rewrite Hngtc1 in H1; simpl in *. 
       rewrite HgtbrS in H1; simpl in *.
       inversion H1. inversion H2. inversion H2.
    - rewrite HngtbrS in H1; simpl in *. inversion H1.
 + (*Case 8: p is at (0,c) and q is at (r,c) *)
  simpl in *.
  rewrite Hr in *; simpl in *.
  assert (S qr' <? r = true \/ S qr' <? r = false) as HgtbrS 
   by apply bool_dec. 
  assert (S qc' <? c = true \/ S qc' <? c = false) as HgtbcS 
   by apply bool_dec. 
   destruct HgtbrS as [HgtbrS | HngtbrS]; destruct HgtbcS as [HgtbcS | HngtbcS].
   - rewrite HgtbcS, HgtbrS, sub_n_o, plus_S in H1; simpl in *. 
     assert (S (S qr') <? r = true \/ S (S qr') <? r = false) as HgtbrSS 
      by apply bool_dec. 
     destruct HgtbrSS as [HgtbrSS | HngtbrSS]. 
     * rewrite HgtbrSS, HgtbcS in H1; simpl in *.
       assert (qc' <? c = true) as Hgtcq by try (apply gtb_true_S; auto).
       rewrite Hgtcq in H1; simpl in *.
       rewrite HgtbrS, sub_n_o, plus_S in H1; simpl in *.
       assert (qr' <? r = true) as Hgtrq by try (apply gtb_true_S; auto).
       rewrite Hgtrq in H1; simpl in *.
       assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
        by apply bool_dec. 
       destruct HgtbcSS as [HgtbcSS | HngtbcSS].
       { rewrite HgtbcSS in H1; simpl in *.
         inversion H1. inversion H2.
         inversion H2. inversion H3.
         inversion H3. inversion H4.
         inversion H4. inversion H5.
         { rewrite H7, H8, sub_n_o, plus_S in *.
           rewrite Hgtcq; simpl. 
           rewrite HgtbrS, Hgtcq; simpl.
           right. 
           assert (pc' <? c = true) as Hgtcp by try (apply gtb_true_S; auto).
           rewrite Hgtcp; simpl. right.
           rewrite HgtbcS, Hr; simpl. 
           left; auto.
         }
         inversion H5. inversion H6.
         { rewrite H8, H9, sub_n_o, plus_S in *; simpl in *.
           rewrite HgtbcS; simpl. 
           rewrite  HgtbrS, HgtbcS; simpl. left; auto. 
         }
         inversion H6. 
         { inversion H7.
           rewrite H9, H10 in *; simpl in *. 
           rewrite HgtbcSS; simpl.
           rewrite HgtbrS, HgtbcSS; simpl.  right. 
           rewrite sub_n_o, plus_S. 
           rewrite HgtbcS; simpl. left; auto. 
         }
         inversion H7.  inversion H8. 
         inversion H8.  inversion H9. inversion H9.
       }
       rewrite HngtbcSS in H1; simpl in *.
       inversion H1. inversion H2. 
       inversion H2.  inversion H3. 
       inversion H3.  inversion H4. 
       inversion H4.  inversion H5. 
       { rewrite H7, H8 in *. 
         rewrite  Hgtcq, sub_n_o, plus_S; simpl. 
         rewrite HgtbrS, Hgtcq; simpl. right. 
         assert (pc' <? c = true) as Hgtcp by try (apply gtb_true_S; auto).
         rewrite Hgtcp; simpl. right. 
         rewrite HgtbcS; simpl. left; auto. 
       }
       inversion H5.  inversion H6.
       { rewrite H8, H9 in *; simpl in *.
         rewrite HgtbcS; simpl. 
         rewrite HgtbrS, HgtbcS; simpl. left; auto. 
       } inversion H6. 
    * rewrite HngtbrSS, sub_n_o, plus_S in H1; simpl in *. 
      assert (qc' <? c = true) as Hgtcq by try (apply gtb_true_S; auto).
      rewrite HgtbrS, Hgtcq in H1; simpl in *. 
      assert (qr' <? r = true) as Hgtrq by try (apply gtb_true_S; auto).
      rewrite Hgtrq in H1; simpl in *. 
      rewrite HgtbcS in H1; simpl in *.
      assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
        by apply bool_dec. 
      destruct HgtbcSS as [HgtbcSS | HngtbcSS].
      { rewrite HgtbcSS in H1; simpl in *.
        inversion H1. inversion H2. 
        inversion H2. inversion H3. 
        rewrite H5, H6 in *; simpl in *.
        rewrite Hgtcq, sub_n_o, plus_S; simpl in *. 
        rewrite HgtbrS, Hgtcq; simpl. right. 
        assert (pc' <? c = true) as Hgtcp by try (apply gtb_true_S; auto).
        rewrite Hgtcp; simpl in *. right. 
        rewrite HgtbcS; simpl. left; auto.
        inversion H3. inversion H4. 
        rewrite H6, H7 in *.  
        rewrite HgtbcS; simpl. 
        rewrite HgtbrS, HgtbcS, sub_n_o, plus_S; simpl.  left; auto. 
        inversion H4. inversion H5. 
        rewrite H7, H8 in *.  
        rewrite HgtbcSS; simpl. 
        rewrite HgtbrS, HgtbcSS, sub_n_o, plus_S; simpl. right. 
        rewrite HgtbcS; simpl. left; auto. 
        inversion H5.  inversion H6. inversion H6. 
      }
      rewrite HngtbcSS in H1; simpl in *. 
      inversion H1. inversion H2. 
      inversion H2. inversion H3. 
      { rewrite H5, H6 in *; simpl in *. 
        rewrite Hgtcq; simpl. 
        rewrite HgtbrS, Hgtcq; simpl. right. 
        rewrite sub_n_o, plus_S; simpl. 
        assert (pc' <? c = true) as Hgtcp by try (apply gtb_true_S; auto).
        rewrite Hgtcp; simpl in *. right. 
        rewrite HgtbcS; simpl. left; auto. 
      }
      inversion H3. inversion H4. 
      rewrite H6, H7, sub_n_o, plus_S in *; simpl in *.
      { rewrite HgtbcS; simpl. 
        rewrite HgtbrS, HgtbcS; simpl. 
        left; auto. 
      } inversion H4. 
    - rewrite HngtbcS, HgtbrS in H1; simpl in *. inversion H1. 
    - rewrite HngtbrS, HgtbcS in H1; simpl in *. inversion H1.
    - rewrite HngtbcS, HngtbrS in H1; simpl in *. inversion H1.
 + (*Case 9: p is at (r,0) and q is at (0,0) *)
  simpl in *.
  rewrite Hr, Hc in *; simpl in *. 
  rewrite Hc in *; simpl in *. 
  assert ((1 <? r) = true \/ (1 <? r) = false) by apply bool_dec.
  destruct H2 as [ Hgtr1 | Hngtr1].
  - rewrite Hgtr1 in H1; simpl in *. 
    assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
    destruct H2 as [ Hgtc1 | Hngtc1].
    * rewrite Hgtc1, Hr in H1; simpl in *. 
      inversion H1. inversion H2. 
      { rewrite <- H4 in *; rewrite Hgtr1; simpl. 
        rewrite Hc. 
        assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
        destruct H3 as [ Hgtr2 | Hngtr2].
        { rewrite Hgtr2; simpl. right. 
          rewrite Hgtc1; simpl. right. 
          rewrite Hr; simpl. 
          left; auto. 
        }
        rewrite Hngtr2; simpl.
        rewrite Hr; simpl. 
        left; auto. 
      }
      inversion H2. inversion H3.
      inversion H3. inversion H4.
      inversion H4.
    * rewrite Hngtc1, Hr, sub_n_o, plus_S in *; simpl in *.
      inversion H1. inversion H2.
      { rewrite <- H4 in *; rewrite Hgtr1; simpl in *. 
        assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
        destruct H3 as [ Hgtr2 | Hngtr2].
        { rewrite Hgtr2, Hc, Hngtc1; simpl.
          right. rewrite Hr; simpl. 
          left; auto. 
        }
        rewrite Hngtr2, Hc, Hngtc1; simpl. 
        rewrite Hr; simpl. 
        left; auto. 
      } inversion H2. 
   - rewrite Hngtr1 in H1; simpl in *. 
     rewrite Hr in H1.
     assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
     destruct H2 as [ Hgtc1 | Hngtc1].
     * rewrite Hgtc1 in H1; simpl in *. 
       inversion H1. inversion H2. inversion H2. 
     * rewrite Hngtc1 in H1; simpl in *. inversion H1.   
+ (*Case 10: p is at (r,0) and q is at (0,c) *)
  simpl in *.
  rewrite Hr in *; simpl in *. 
  assert (S qc' <? c = true \/ S qc' <? c = false) as HgtbcS 
  by apply bool_dec.
  destruct HgtbcS as [HgtbcS | HgtbcS].
 - rewrite HgtbcS, sub_n_o, plus_S in H1 ;simpl in *.
   assert ((1 <? r) = true \/ (1 <? r) = false) by apply bool_dec.
   * destruct H2 as [ Hgtr1 | Hngtr1].
     rewrite Hgtr1,HgtbcS in H1.
     assert ( qc' <? c = true \/  qc' <? c = false) as Hgtbc 
     by apply bool_dec.
     destruct Hgtbc  as [ Hgtbc | Hgtbc].
     { rewrite Hgtbc in H1;simpl in *.
      assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbqcSS 
      by apply bool_dec. 
      destruct HgtbqcSS  as [HgtbqcSS  | HngtbqcSS].
      { rewrite HgtbqcSS,Hr in H1; simpl in *. 
        inversion H1.
        {  inversion H2. 
        }
         inversion H2. 
         { inversion H3.
          rewrite H6 in *. rewrite  <- H5 in *;simpl in *.
          rewrite Hgtr1,Hc ;simpl in *.
          assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
          destruct H4 as [ Hgt1 | Hngt1].
          rewrite Hgt1, Hgtbc,HgtbcS,Hr  ;simpl in *.
          right;right;right;left. auto.
          rewrite Hngt1,Hc ,HgtbcS,Hr ,Hgtr1;simpl in *.
          right;left;auto. 
         }
          inversion H3. inversion H4. inversion H4. 
          inversion H5. inversion H5. inversion H6.
           inversion H6.
      } 
        assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtqcSS 
        by apply bool_dec. 
        destruct HgtqcSS  as [HgtqcSS  | HngtqcSS].
       { rewrite HgtqcSS,Hr in H1; simpl in *.
         inversion H1.
         {  inversion H2. 
         }
         inversion H2. inversion H3.
        { rewrite Hgtr1,Hc,plus_S,sub_n_o; simpl in *.
         assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
         destruct H4 as [ Hgtr2 | Hngtr2]. 
         rewrite Hgtr2,Hc,Hr; simpl in *.
         assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
         destruct H4 as [ Hgtc1 | Hngtc1].
         rewrite Hgtc1,Hgtr1; simpl in *.
         right;right;right;left. auto. 
         rewrite Hngtc1,Hgtr1; simpl in *.
         rewrite H6 in HngtbqcSS,HgtqcSS.
         rewrite HgtqcSS in HngtbqcSS.
         inversion HngtbqcSS.
         rewrite Hngtr2,Hc,Hr; simpl in *.
         assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
         destruct H4 as [ Hgtc1 | Hngtc1].
         rewrite Hgtc1,Hgtr1; simpl in *.
         right;left. auto. rewrite H6 in *.
         rewrite HgtqcSS in HngtbqcSS .
         inversion HngtbqcSS.
        }
     inversion H3. inversion H4. inversion H4.    
     inversion H5. inversion H5. inversion H6.
     inversion H6.
     }
    rewrite HngtqcSS,Hr in *; simpl in *.   
    inversion H1. inversion H2. inversion H2. 
    inversion H3. rewrite H6 in *.
    rewrite Hgtr1,Hc in *; simpl in *.
    assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
    destruct H4 as [ Hgtr2 | Hngtr2]. 
    rewrite Hgtr2,Hc,HgtbcS,Hr ; simpl in *.
    right;right;right;left. auto.
    rewrite Hngtr2,Hc,Hr,HgtbcS,Hgtr1; simpl in *.
    right;left. auto.
    inversion H3. inversion H4.
    inversion H4.
  }
   rewrite Hgtbc in *.
   assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
   by apply bool_dec. 
   destruct HgtbcSS as [HgtbcSS | HngtbcSS].
   rewrite HgtbcSS,Hr in H1; simpl in *.
   inversion H1. inversion H2. inversion H2. 
   inversion H3. inversion H3. inversion H4.
   inversion H4.
   rewrite HngtbcSS,Hr  in H1; simpl in *.
   inversion H1. inversion H2. inversion H2.
   rewrite Hngtr1,HgtbcS,Hr  in H1; simpl in *.
   assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
   by apply bool_dec. 
   destruct HgtbcSS as [HgtbcSS | HngtbcSS].
   rewrite HgtbcSS in H1.
   assert ( qc' <? c = true \/  qc' <? c = false) as Hgtbc 
   by apply bool_dec. destruct Hgtbc  as [ Hgtbc | Hgtbc].
   rewrite Hgtbc in H1.
   inversion H1. inversion H2. inversion H2. 
   inversion H3. inversion H3. rewrite Hgtbc in H1.
   inversion H1. inversion H2. inversion H2.
   rewrite HngtbcSS in H1; simpl in *. 
   assert ( qc' <? c = true \/  qc' <? c = false) as Hgtbc 
   by apply bool_dec.
   destruct Hgtbc  as [ Hgtbc | Hgtbc].
   rewrite Hgtbc in H1. inversion H1. inversion H2.
   inversion H2. rewrite Hgtbc in H1. inversion H1.
 - rewrite HgtbcS  in H1.
   inversion H1.

+ (*Case 11: p is at (r,0) and q is at (r,0) *)
  simpl in *.
 rewrite Hc in *; simpl in *. 
 assert (S qr' <? r = true \/ S qr' <? r = false) as HgtbcS 
 by apply bool_dec;
 destruct HgtbcS as [HgtbcSt | HgtbcSf].
  - rewrite HgtbcSt,sub_n_o, plus_S in H1;simpl in *.
    assert (S (S qr') <? r = true \/ S (S qr') <? r = false) as HgtqrSS 
    by apply bool_dec ;destruct HgtqrSS as [HgtqrSSt | HgtqrSSf].
    rewrite HgtqrSSt,Hc in H1.
    assert ( qr' <? r = true \/  qr' <? r = false) as Hgtq 
    by apply bool_dec ;destruct Hgtq as [Hgtq1 | Hgtq2].
    rewrite Hgtq1 in H1.
     assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec ;
    destruct H2 as [H21 | Hg21].
    rewrite H21,HgtbcSt in H1; simpl in *. 
 
 *   inversion H1. inversion H2. 
    rewrite H4 in *.
    { rewrite HgtqrSSt, sub_n_o, plus_S; simpl in *.
     assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbrSS 
      by apply bool_dec; 
      destruct HgtbrSS  as [HgtbrSSt  | HngtbcSSf].
      { rewrite HgtbrSSt,Hc,H21,HgtqrSSt,HgtbcSt; simpl in *. 
      right;right;left; auto. 
      }
      rewrite HngtbcSSf,Hc,H21,HgtqrSSt,HgtbcSt; simpl in *. 
      left. eauto. 
    } 
     inversion H2. inversion H3. inversion H3.
     inversion H4. rewrite H6 in *.  
     rewrite Hgtq1,plus_S,sub_n_o; simpl in *. 
    rewrite HgtbcSt,Hc,H21; simpl in *. 
    left;auto. inversion H4. inversion H5.
    inversion H5. inversion H6.
    inversion H6. 
  * rewrite Hg21 ,HgtbcSt in H1; simpl in *.
   inversion H1. inversion H2. rewrite  H4 in *.
   { rewrite HgtqrSSt, plus_S, sub_n_o; simpl in *. 
     assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbrSS 
     by apply bool_dec; destruct HgtbrSS  as [HgtbrSSt  | HngtbcSSf].
     rewrite HgtbrSSt,Hc,Hg21,HgtbcSt,HgtqrSSt;
     simpl in *.
     { right;left;auto. 
     }
     { rewrite HngtbcSSf,Hc,Hg21,HgtbcSt,HgtqrSSt;
     left. auto. 
     }
   }
    inversion H2. inversion H3. rewrite  <- H5 .
    rewrite Hgtq1,  plus_S, sub_n_o; simpl in *.
    rewrite  <-  H5 . rewrite HgtbcSt,Hc,Hg21 .
    assert ( pr' <? r = true \/  pr' <? r = false) as Hgtq 
    by apply bool_dec  ;destruct Hgtq as [Hgtqt1 | Hgtqf2].
    rewrite Hgtqt1,Hgtq1; simpl in *. left; auto.
    rewrite Hgtqf2. left;auto. inversion H3.
 * rewrite Hgtq2 in H1.
   assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec ;
   destruct H2 as [H21 | Hg21].  rewrite H21,HgtbcSt in H1.
   { inversion H1. inversion H2. rewrite H4 in *.
     rewrite HgtqrSSt,plus_S, sub_n_o; simpl in *.
     assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbrSS 
     by apply bool_dec; destruct HgtbrSS  as [HgtbrSSt  | HngtbcSSf].
     rewrite HgtbrSSt,Hc,H21,HgtbcSt.
     right; right;left;auto. 
     rewrite HngtbcSSf,Hc,H21,HgtbcSt,HgtqrSSt.
     simpl in *. left;auto. inversion H2. inversion H3.
     inversion H3. inversion H4. inversion H4.
   }
     rewrite Hg21,HgtbcSt in H1. inversion H1. 
   { inversion H2. rewrite H4 in *.
   rewrite HgtqrSSt,plus_S, sub_n_o; simpl in *.
   assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbrSS 
   by apply bool_dec; destruct HgtbrSS  as [HgtbrSSt  | HngtbcSSf].
   rewrite HgtbrSSt,Hc,Hg21,HgtbcSt.
   right;left;auto. 
   rewrite HngtbcSSf,Hc,Hg21,HgtbcSt,HgtqrSSt.
   left;auto.
   }
   inversion H2.
* assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec ;
  destruct H2 as [H21 | Hg21].
  { assert ( qr' <? r = true \/  qr' <? r = false) as Hgtq 
  by apply bool_dec ;destruct Hgtq as [Hgtq1 | Hgtq2].
   { rewrite H21,HgtbcSt,HgtqrSSf,Hc,Hgtq1 in H1. 
     inversion H1.
    { inversion H2. rewrite H4 in *.
      rewrite Hgtq1,plus_S, sub_n_o; simpl in *.
      rewrite HgtbcSt,Hc,H21.
      assert ( pr' <? r = true \/  pr' <? r = false) as Hgtq 
      by apply bool_dec ;destruct Hgtq as [Hgtp1 | Hgtp2].
       { rewrite Hgtp1 . left;auto. 
       }
      rewrite Hgtp2,Hgtq1. left;auto.
    }
      inversion H2. 
       { inversion H3.
       }   
      inversion H3. 
      inversion H4. inversion H4.
   } 
   rewrite Hgtq2 in H1.
   rewrite HgtqrSSf,Hc,H21 in H1.
   rewrite HgtbcSt in H1.
   inversion H1.
   { inversion H2.
   }   
   inversion H2.
 }
   rewrite Hg21,HgtqrSSf,Hc in H1.
   assert ( qr' <? r = true \/  qr' <? r = false) as Hgtq 
   by apply bool_dec ; destruct Hgtq as [Hgtp1 | Hgtp2].
   { rewrite Hgtp1,HgtbcSt in H1.
     inversion H1.
    { inversion H2. rewrite <- H4 in *.
      rewrite Hgtp1,plus_S, sub_n_o; simpl in *.
      rewrite <- H4 in *. rewrite HgtbcSt,Hc,Hg21.
      assert ( pr' <? r = true \/  pr' <? r = false) as Hgtq 
      by apply bool_dec ;destruct Hgtq as [Hgtpt | Hgtpf].
      { rewrite Hgtp1,Hgtpt .
        left;auto.
      }
        left;auto.
    }
       inversion H2.
  }
   rewrite Hgtp2,HgtbcSt in H1.
   inversion H1.
 - rewrite HgtbcSf in H1.
   inversion H1.

+ (*Case 12: p is at (r,0) and q is at (r,c) *)
  simpl in *.
   assert (S qr' <? r = true \/ S qr' <? r = false) as HgtbrS 
    by apply bool_dec. 
   assert (S qc' <? c = true \/ S qc' <? c = false) as HgtbcS 
    by apply bool_dec. 
   destruct HgtbrS as [HgtrS | HngtrS]; destruct HgtbcS as [HgtcS | HngtcS].
   * rewrite Hc, HgtrS, HgtcS in *; simpl in *.
     rewrite HgtrS in H1.
     rewrite HgtcS in H1.
     rewrite sub_n_o in *.
     rewrite plus_S in *.
     assert (S (S qr') <? r = true \/ S (S qr') <? r = false) as HgtbrSS 
     by apply bool_dec; destruct HgtbrSS as [HgtrSS | HngtrSS].    
    - rewrite HgtrSS in H1; simpl in *.
      rewrite sub_n_o in *.
      rewrite plus_S in *.
      assert (qc' <? c = true) as Hgtc by try (apply gtb_true_S; auto).
      rewrite Hgtc in H1; simpl in *.
      assert (qr' <? r = true) as Hgtr by try (apply gtb_true_S; auto).
      rewrite Hgtr in H1; simpl in *.
      assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
      by apply bool_dec; destruct HgtbcSS as [HgtcSS | HngtcSS].
     { rewrite HgtcSS in H1.
       inversion H1. 
       { inversion H2.
       } 
        inversion H2.
      { inversion H3.
        rewrite <- H6 in *. rewrite H5 in *.
        rewrite HgtrSS ; simpl.
        assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtprSS 
        by apply bool_dec; 
        destruct HgtprSS   as [HgtprSS   | HngtprSS ].
       { rewrite HgtprSS,Hgtc.
        assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
        destruct H4 as [ Hgtc1 | Hngtc1].
        { assert (pr' <? r = true) as Hgtcp by try (apply gtb_true_S; auto).
         rewrite HgtcS,Hgtcp; simpl. 
         right; right; right; left; auto.
        }
       rewrite HgtcS. rewrite <- H5 in *. rewrite H6 in *. 
       rewrite HgtrS,HgtrSS; simpl in *.
       right; right; right; left; auto.
      }
     assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtqrSS 
     by apply bool_dec; destruct HgtqrSS as [HgtqrSS | HngtqrSS].    
     rewrite HgtqrSS; simpl in *. 
     rewrite Hc,HgtrS,HgtcS; simpl in *.
     right; right; right; left; auto.
     rewrite HngtqrSS,HgtcS,HgtrS ; simpl in *. 
     rewrite Hc,HgtrSS; simpl in *.
     right; left; auto.
   }
    inversion H3. 
   { inversion H4. rewrite H6 in *. rewrite H7 in *.
      rewrite HgtrS; simpl in *.
      assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtqrSS 
      by apply bool_dec; destruct HgtqrSS as [HgtqrSS | HngtqrSS].    
      { rewrite HgtqrSS,Hgtc,HgtrS,Hgtr,HgtcS; simpl in *.
        right; right; right; right; left; auto. 
      }
    rewrite HngtqrSS,Hc,HgtrS, HgtcS,Hgtr; simpl in *.
    right; right; left; auto.
   } 
    inversion H4.
   { inversion H5. rewrite H7 in *. rewrite H8 in *.
    rewrite Hgtr; simpl in *.
    rewrite HgtrS,HgtcS,Hgtc.
    assert (pr' <? r = true) as Hgtcp by try (apply gtb_true_S; auto).
    rewrite Hgtcp,Hgtr; simpl in *.
      right; left; auto. 
   }
    assert (S pr' <? r = true \/ S pr' <? r = false) as HgtprS 
    by apply bool_dec.
    destruct HgtprS as [HgtbrS | HngtrS].
    { rewrite HgtbrS; simpl in *.
      assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtqrSS 
     by apply bool_dec; destruct HgtqrSS as [HgtqrSS | HngtqrSS].    
     { rewrite HgtqrSS,Hc.
      assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
      destruct H6 as [ Hgtc1 | Hngtc1].
      {  inversion H5. { inversion H6. }  inversion H6.
         { inversion H7. }
          { inversion H7.
           { inversion H8. } { inversion H8. { inversion H9. }
             inversion H9. } } } 
      inversion H5. { inversion H6. } 
      inversion H6. { inversion H7. }
        inversion H7.
         { inversion H8. }
          { inversion H8.
           { inversion H9. }
            { inversion H9. } } }
  inversion H5.
  { inversion H6. }
   { inversion H6.
    { inversion H7. } 
     { inversion H7.
      { inversion H8. }
       { inversion H8.
        { inversion H9. }
         inversion H9. } } } }
  inversion H5. 
   {  inversion H6. }
      inversion H6.
    {  inversion H7. } 
     { inversion H7.
      { inversion H8. }
       { inversion H8. 
        { inversion H9. } inversion H9. } } }
  
  rewrite HngtcSS in H1.
  inversion H1. 
  { inversion H2. }
      inversion H2. 
   { inversion H3. 
    { rewrite H6 in *. rewrite H5 in *.
   rewrite HgtrSS; simpl in *.
   assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtqrSS 
   by apply bool_dec; destruct HgtqrSS as [HgtqrSS | HngtqrSS].    
    { rewrite HgtqrSS; simpl in *. 
    rewrite HgtcS,Hgtc,HgtrS; simpl in *.
    right; right; right; left. auto. 
    }
    rewrite HngtqrSS,HgtrS,Hgtc,HgtcS; simpl in *.
    right; left. auto. 
   }
  }
 inversion H3.
  { inversion H4.
   { rewrite H6 in *. rewrite H7 in *.
  rewrite HgtrS; simpl in *.  
  rewrite HgtrSS,Hgtc ,HgtcS,HgtrS,Hgtr; simpl in *.
  right; right; right;  right; left. auto.
   }
  }
 inversion H4.
  { inversion H5.
    rewrite <- H7 in *. rewrite H8 in *.
    rewrite Hgtr ; simpl in *.
    rewrite HgtrS , Hgtc,HgtcS ; simpl in *.
    right; left. auto. 
  }
  inversion H5.
  {  inversion H6. }
  inversion H6.

- rewrite HngtrSS in H1; simpl in *.
  rewrite sub_n_o, plus_S in *.
  assert (qc' <? c = true) as Hgtc by try (apply gtb_true_S; auto).
  rewrite Hgtc in H1; simpl in *.
  assert (qr' <? r = true) as Hgtr by try (apply gtb_true_S; auto).
  rewrite Hgtr in H1; simpl in *.
  assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtqcSS 
  by apply bool_dec; destruct HgtqcSS as [HgtqcSS | HngtqcSS].    
  rewrite HgtqcSS in H1; simpl in *.
  { inversion H1.
   { inversion H2.
    rewrite H4 in *. rewrite H5 in *.
    rewrite HgtrS; simpl in *.
    rewrite HngtrSS,Hc,HgtcS,Hgtr,HgtrS; simpl in *.
    right; right; left. auto.
   }
   inversion H2.
   { inversion H3.
   rewrite H5 in *. rewrite H6 in *.
   rewrite Hgtr; simpl in *.
   rewrite HgtrS,HgtcS,Hgtc; simpl in *.
   right; left. auto.
  }
 inversion H3.
  { inversion H4. }
   { inversion H4.
    { inversion H5. }
       inversion H5.
      { inversion H6. }
     inversion H6. } }
  rewrite HngtqcSS in H1.
  inversion H1. 
  { inversion H2.
    rewrite H4 in *. rewrite H5 in *.
    rewrite HgtrS; simpl in *.
    rewrite HngtrSS,Hgtr,HgtrS,HgtcS,Hc  ; simpl in *.
   right; right; left. auto.
  }
  inversion H2.
  { inversion H3.
  rewrite H5 in *. rewrite H6 in *.
  rewrite Hgtr; simpl in *.
  rewrite Hgtr, HgtrS,Hc,HgtcS; simpl in *.
  right; left. auto.
  }
  inversion H3. 
  { inversion H4. }
    inversion H4. 
 * simpl in *.
  rewrite HgtrS,HngtcS in H1; simpl in *.
   inversion H1.
 * simpl in *.
  rewrite HngtrS,HgtcS, 
  sub_n_o,  plus_S in H1; simpl in *.
  inversion H1.
 * simpl in *.
  rewrite HngtrS,HngtcS in H1; simpl in *.
  inversion H1.

+ (*Case 13: p is at (r,c) and q is at (0,0) *)
 simpl in *. rewrite Hr,Hc in *;
 simpl in *.
 assert ((1 <? r) = true \/ (1 <? r) = false) by apply bool_dec.
   destruct H2 as [ Hgtr | Hngtr].
 * assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
   destruct H2 as [ Hgtc | Hngtc].
  { rewrite Hgtr, Hgtc,Hc,Hr in H1; simpl in *.
   inversion H1. inversion H2.
   inversion H2. inversion H3.
   inversion H3. inversion H4. (*pr'=0 ,pc'=0*)
   rewrite <- H7 in *. rewrite <-H6 in *.
   rewrite Hgtr,Hgtc,sub_n_o, plus_S 
   ; simpl in *.
   rewrite Hgtc,Hc.
   assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
   destruct H5 as [ Hgtr2 | Hngtr2].
   { rewrite Hgtr2,Hgtr,Hr; simpl in *.
     right; right; right;left. auto. 
   }
  rewrite Hngtr2 ,Hr,Hgtr; simpl in *.
  right;left. auto. inversion H4. 
 }
  rewrite Hgtr,Hngtc,Hc,Hr in H1; simpl in *.
  inversion H1. inversion H2. inversion H2.

 * rewrite Hr,Hc,Hngtr in H1.
   assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
   destruct H2 as [ Hgtc | Hngtc].
   { rewrite Hgtc in H1; simpl in *.
   inversion H1. inversion H2.
  inversion H2. }
  rewrite Hngtc in H1;simpl in *.
  inversion H1.

 + simpl in *.
  rewrite Hr in *.
  assert (S qc' <? c = true \/ S qc' <? c = false) as HgtbcS 
  by apply bool_dec. 
  destruct HgtbcS as [HgtbcS | HntbcS]. 
  { rewrite HgtbcS in H1;simpl in *.
   assert ((1 <? r) = true \/ (1 <? r) = false) by apply bool_dec.
   destruct H2 as [ Hgtr | Hngtr].
   { rewrite Hgtr,Hr,sub_n_o,plus_S ,HgtbcS in H1.
    assert (qc' <? c = true) as Hgtcq by try (apply gtb_true_S; auto).
    rewrite Hgtcq in H1; simpl in *.
    assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
    by apply bool_dec. 
    destruct HgtbcSS as [HgtbcSS | HngtbcSS].
    { rewrite HgtbcSS in H1.
     inversion H1. inversion H2.
     rewrite H5 in *. rewrite <- H4 in *.
     rewrite Hgtr,HgtbcS ,sub_n_o,  plus_S 
     ; simpl in *.
     assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
     { destruct H3 as [ Hgtr2 | Hngtr2].
     rewrite Hgtr2,Hgtcq,Hgtr,Hr,HgtbcS; simpl in *.
     right; right;right;right ;left. auto. 
     rewrite Hngtr2,HgtbcS,Hgtcq,Hgtr,Hr,plus_S ; simpl in *.
     right;right ;left. auto. 
    }
     inversion H2. inversion H3. 
     rewrite H6 in *. rewrite <- H5 in *.
     rewrite Hgtr,Hgtcq,plus_S ,sub_n_o; simpl in *.
     assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
     destruct H4 as [ Hgtr2 | Hngtr2].
     { rewrite Hgtcq,Hgtr2.
     assert (pc' <? c = true) as Hgtpc by try (apply gtb_true_S; auto).
     rewrite Hgtpc,Hgtr,Hr,plus_S,HgtbcS; simpl in *.
     right;right;right;right;right ;left. auto. 
     }
     rewrite Hngtr2,Hgtcq,Hgtr. 
     assert (pc' <? c = true) as Hgtc by try (apply gtb_true_S; auto).
     rewrite Hgtc,Hr,plus_S,HgtbcS ; simpl in *.
     right;right;right;left. auto. 
     inversion H3.
     { inversion H4. (*S qc' = pc'  pr'=0*)
     rewrite H7 in *. rewrite <- H6 in *.
     rewrite Hgtr,plus_S,sub_n_o,HgtbcSS; simpl in *.
     assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
     destruct H5 as [ Hgtr2 | Hngtr2].
      { rewrite Hgtr2,HgtbcSS,HgtbcS,Hgtr,Hr; simpl in *.
       right;right;right;left. auto. 
      }
     rewrite Hngtr2,HgtbcSS,HgtbcS,Hgtr,plus_S,Hr; simpl in *.
     assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
     by apply bool_dec. 
     destruct HgtbpSS as [HgtbpcSS | HngtbpcSS].
      { rewrite HgtbpcSS. right;left. auto. }
     rewrite HngtbpcSS. right;left. auto.
    }
   inversion H4.
    {  inversion H5. }
       inversion H5. 
      { inversion H6. }
        inversion H6. }
   rewrite HngtbcSS in H1.
  inversion H1. 
  { inversion H2. rewrite H5 in *.
    rewrite <- H4 in *.
    rewrite Hgtr,HgtbcS,plus_S,sub_n_o; simpl in *.
    assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
    destruct H3 as [ Hgtr2 | Hngtr2].
    { rewrite Hgtr2,HgtbcS,Hgtcq,Hgtr,Hr; simpl in *.
      right;right;right;right;left. auto. 
    }
   rewrite Hngtr2,HgtbcS,Hgtcq,Hgtr,Hr; simpl in *.
   right;right;left. auto.
  }
  inversion H2.
  { inversion H3.
   rewrite H6 in *. rewrite <-H5 in *.
   rewrite Hgtr,Hgtcq,plus_S,sub_n_o; simpl in *.
   assert ((2 <? r) = true \/ (2 <? r) = false) by apply bool_dec.
   destruct H4 as [ Hgtr2 | Hngtr2].
    { rewrite Hgtr2,Hgtcq.
     assert (pc' <? c = true) as Hgtcp by try (apply gtb_true_S; auto).
     rewrite Hgtcp,Hgtr,Hr,plus_S,HgtbcS ; simpl in *.
     right;right;right;right;right;left. auto. 
    }
   rewrite Hngtr2,Hgtcq .
   assert (pc' <? c = true) as Hgtcp by try (apply gtb_true_S; auto).
   rewrite Hgtcp,Hgtr,Hr,plus_S,HgtbcS ; simpl in *.
   right;right;right;left. auto. 
   }
   inversion H3.
   { inversion H4. }
     inversion H4. 
 }
  rewrite Hngtr,HgtbcS,sub_n_o in H1.
  assert (qc' <? c = true) as Hgtcp by try (apply gtb_true_S; auto).
  rewrite Hgtcp,plus_S,Hr in H1. 
  assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbpSS 
  by apply bool_dec. 
  destruct HgtbpSS as [HgtbpcSS | HngtbpcSS].
   { rewrite HgtbpcSS in H1; simpl in *.
     inversion H1. 
     { inversion H2. }
       inversion H2. 
      { inversion H3. }
        inversion H3. }
       {  simpl in *. rewrite HngtbpcSS in H1.
         inversion H1.
        { inversion H2. }
          inversion H2. } }
  rewrite HntbcS in H1;simpl in *.
  inversion H1. 
  
+ (*Case 14: p is at (r,c) and q is at (r,0) *)
 simpl in *.
 assert (S qr' <? r = true \/ S qr' <? r = false) as HgtbcS 
 by apply bool_dec. 
 destruct HgtbcS as [HgtbcS | HntbcS]. 
 - rewrite HgtbcS,Hc,plus_S,sub_n_o in  * ;
   simpl in *.
   assert (S (S qr') <? r = true \/ S (S qr') <? r = false) as HgtbpSS 
   by apply bool_dec. 
   destruct HgtbpSS as [HgtbpcSS | HngtbpcSS].
  * rewrite HgtbpcSS,Hc in H1.
    assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
    destruct H2 as [ Hgtr | Hngtr].
    { rewrite Hgtr in H1.
     assert (qr' <? r = true) as Hgtcp by try (apply gtb_true_S; auto).
     rewrite Hgtcp,HgtbcS in H1;simpl in *.
     inversion H1. 
     { inversion H2. }
      inversion H2.
      { inversion H3. 
       rewrite H5 in *. rewrite <- H6 in *.
       rewrite HgtbpcSS,Hgtr,plus_S,sub_n_o ;simpl in *.
       assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbpSS 
       by apply bool_dec. 
       destruct HgtbpSS as [HgtbprSS | HngtbprSS].
        { rewrite Hgtr,HgtbprSS,Hc,HgtbpcSS.
          assert ((2 <? c) = true \/ (2 <? c) = false) by apply bool_dec.
          destruct H4 as [ Hgtr2 | Hngtr2].
         { rewrite Hgtr2,HgtbcS ;simpl in *.
           right;right;right;left. auto. 
         }
          rewrite HgtbcS;simpl in *.
          right;right;right;left. auto.
       }
       { rewrite HngtbprSS,Hgtr,Hc,HgtbpcSS.
         assert ((2 <? c) = true \/ (2 <? c) = false) by apply bool_dec.
        destruct H4 as [ Hgtr2 | Hngtr2].
        { rewrite Hgtr2,HgtbcS;simpl in *.
          right;left. auto.
        }
        rewrite Hngtr2,HgtbcS;simpl in *.
        right; left. auto.
       }
     }
   inversion H3. 
    { inversion H4. }
   inversion H4.
    { inversion H5. 
      rewrite H7 in *. rewrite <-H8 in *.
      rewrite Hgtcp,Hgtr,plus_S,sub_n_o ;simpl in *.
      rewrite HgtbcS,Hgtr,Hc,Hgtcp.
      assert (pr' <? r = true) as Hgtpr by try (apply gtb_true_S; auto).
      rewrite Hgtpr.
      assert ((2 <? c) = true \/ (2 <? c) = false) by apply bool_dec.
      destruct H6 as [ Hgtr2 | Hngtr2].
       { rewrite Hgtr2;simpl in *. right;left. auto. 
       }
    right;left. auto.
   }
   inversion H5. 
    { inversion H6. 
      rewrite H8 in *. rewrite <- H9 in *.
      rewrite HgtbcS,Hgtr,plus_S,sub_n_o ;simpl in *.
      rewrite HgtbpcSS,Hc,Hgtr,HgtbcS;simpl in *.
      right;right;left. auto. 
   }  
   inversion H6. 
 }
    rewrite Hngtr,HgtbcS in H1;simpl in *.
    assert (qr' <? r = true) as Hgtpr by try (apply gtb_true_S; auto).
    rewrite Hgtpr in H1;simpl in *.
    inversion H1. 
     { inversion H2. }
       inversion H2.
       {  inversion H3. }
       inversion H3.
    * rewrite HngtbpcSS,Hc in H1.
      assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
      destruct H2 as [ Hgtr | Hngtr].
      { rewrite Hgtr in H1.
       assert (qr' <? r = true) as Hgtpr by try (apply gtb_true_S; auto).
       rewrite Hgtpr,HgtbcS in H1;simpl in *.
        inversion H1. 
        { inversion H2. }
          inversion H2.
        {  inversion H3.
         rewrite H5 in *. rewrite <- H6 in *.
         rewrite Hgtpr, Hgtr,plus_S,sub_n_o  ;simpl in *.
         rewrite HgtbcS,Hgtr,Hc,Hgtpr.
         assert (pr' <? r = true \/  pr' <? r = false) as HgtprS 
         by apply bool_dec. 
         destruct HgtprS as [HgtprS | HntprS].
         { simpl in *. right;left. auto. }
           { simpl in *. right;left. auto. 
           }
         }
      inversion H3. 
       { inversion H4.
        { rewrite H6 in *. rewrite <- H7 in *.
         rewrite HgtbcS,Hgtr,plus_S,sub_n_o ;simpl in *.
         rewrite HngtbpcSS,Hgtr,Hc,HgtbcS,Hgtpr ;simpl in *.
         assert ((2 <? c) = true \/ (2 <? c) = false) by apply bool_dec.
         destruct H5 as [ Hgtr2 | Hngtr2].
          {  left. auto. }
            rewrite Hngtr2. left . auto.
        }
       }
     inversion H4.
   }
    rewrite Hngtr in H1.
  assert (qr' <? r = true) as Hgtpr by try (apply gtb_true_S; auto).
  rewrite Hgtpr,HgtbcS in H1;simpl in *.
  inversion H1. 
   { inversion H2. }
  inversion H2.
 - rewrite HntbcS,Hc ,sub_n_o in H1;simpl in *.
   inversion H1.
+ (*Case 15: p is at (r,c) and q is at (r,c) *)
 simpl in *.
 assert (S qr' <? r = true \/ S qr' <? r = false) as HgtbcS 
 by apply bool_dec. 
 assert (S qc' <? c = true \/ S qc' <? c = false) as HgtbqcS 
 by apply bool_dec; 
 destruct HgtbcS as [HgtbcS | HntbcS];
 destruct HgtbqcS  as [HgtbqcS | HntbqcS].
 - rewrite HgtbqcS,HgtbcS ,plus_S,sub_n_o in H1;simpl in *.
   assert (S (S qr') <? r = true \/ S (S qr') <? r = false) as HgtbqSS 
   by apply bool_dec. 
   destruct HgtbqSS as [HgtbqcSS | HngtbqcSS].
  * rewrite HgtbqcSS,HgtbqcS in H1.
    assert (qc' <? c = true) as Hgtqc by try (apply gtb_true_S; auto).
    rewrite Hgtqc,HgtbcS,plus_S,sub_n_o in H1;simpl in *. 
    assert (qr' <? r = true) as Hgtqr by try (apply gtb_true_S; auto).
    rewrite Hgtqr in H1. 
    assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbqSS 
    by apply bool_dec;simpl in *. 
    destruct HgtbqSS  as [HgtbqcSSt | HngtbqcSSf].
   {   rewrite HgtbqcSSt  in H1.
      inversion H1. 
     {  inversion H2. (* S qr' = pr' , qc' = pc'*)
       rewrite H4 in *. rewrite  H5 in *.
       rewrite HgtbqcSS,HgtbqcS,plus_S,sub_n_o;simpl in *. 
       assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbpSS 
       by apply bool_dec;simpl in *. 
       destruct HgtbpSS  as [HgtbpcSS | HngtbpcSS].
       { rewrite HgtbpcSS,HgtbqcS,Hgtqc,HgtbqcSS,sub_n_o,HgtbcS;simpl in *. 
         right;right;right;right;left. auto. 
       }
        rewrite HngtbpcSS,HgtbqcS,Hgtqc,HgtbqcSS,
        sub_n_o,HgtbcS ,plus_S,HgtbqcSSt;simpl in *. 
        right;right;left. auto. 
     }
     inversion H2. 
  { inversion H3.  (*  S qr' = pr'  qc' = S pc'*)
      rewrite H5 in *. rewrite <- H6 in *.
      rewrite HgtbqcSS,Hgtqc,plus_S ,sub_n_o;simpl in *.
      assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbpSS 
      by apply bool_dec.  
      destruct HgtbpSS  as [HgtbpcSS | HngtbpcSS].
       { rewrite HgtbpcSS ,Hgtqc ,HgtbqcSS. 
         assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
         by apply bool_dec.
         destruct Hgtpc  as [Hgtpc | Hntpc].
        { rewrite Hgtpc ;simpl in *. 
         rewrite sub_n_o, HgtbcS;simpl in *.
         rewrite plus_S ;simpl in *.
         assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
         by apply bool_dec;simpl in *.
          destruct HgtbpSS  as [HgtpcSS | HngtpcSS].
          { rewrite HgtpcSS. simpl in *.
            rewrite <- H6.
           right;right;right;right;right;left. auto. 
          }
           rewrite HngtpcSS in *. rewrite <- H6 in HngtpcSS. 
           rewrite HgtbqcS in HngtpcSS.
          inversion HngtpcSS. 
        }
         rewrite Hntpc,sub_n_o,HgtbcS;simpl in *.
          rewrite plus_S.
         assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
         by apply bool_dec.  
         destruct HgtbpSS  as [HgtbpcSSt | HngtbpcSS].
         { rewrite HgtbpcSSt. rewrite  H6 in *. rewrite <- H5 in *.
        right;right;left. auto. } rewrite HngtbpcSS.
        rewrite <- H6 in HngtbpcSS. rewrite HgtbqcS in HngtbpcSS.
        inversion HngtbpcSS.
       }
       rewrite HngtbpcSS,Hgtqc.
       assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc by apply bool_dec.
       destruct Hgtpc  as [Hgtpc | Hntpc].
       { rewrite Hgtpc,HgtbqcSS,sub_n_o,HgtbcS,plus_S;simpl in *.
         assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
        by apply bool_dec.  
        destruct HgtbpSS  as [HgtbpcSSt | HngtbpcSSf].
        { rewrite HgtbpcSSt.
          rewrite  H6. right;right;right;left. auto.
       }
       rewrite HngtbpcSSf. simpl in *.
       rewrite  <- H6 in HngtbpcSSf. rewrite HgtbqcS in HngtbpcSSf.
       inversion HngtbpcSSf. 
       }
       rewrite Hntpc,HgtbqcSS,sub_n_o,HgtbcS,plus_S;simpl in *.
       assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
       by apply bool_dec.  
       destruct HgtbpSS  as [HgtbpcSSt | HngtbpcSSf].
       { rewrite HgtbpcSSt. rewrite H6. right;left. auto. }
       rewrite HngtbpcSSf. rewrite <- H6 in HngtbpcSSf.
       rewrite HgtbqcS in HngtbpcSSf. inversion HngtbpcSSf.
   } 
    inversion H3. inversion H4. (* qr' = pr'  qc' = S pc'*)
    assert (S pr' <? r = true \/ S pr' <? r = false) as HgtbprS 
    by apply bool_dec. 
    assert (S pc' <? c = true \/ S pc' <? c = false) as HgtbpcS 
    by apply bool_dec.
  { destruct HgtbprS  as [HgtbprS | HntbcS];
     destruct HgtbpcS  as [HgtbpcS | HntbpcS]. 
     { rewrite HgtbprS , HgtbpcS,plus_S;simpl in *.
        assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbpSS 
        by apply bool_dec.  
       { destruct HgtbpSS  as [HgtbpcSSt | HngtbpcSSf].
         rewrite HgtbpcSSt,HgtbpcS,sub_n_o.
         assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
         by apply bool_dec.
         destruct Hgtpc  as [Hgtpc | Hntpc].
        { rewrite Hgtpc,HgtbprS,sub_n_o.
            assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
            by apply bool_dec.
            destruct Hgtpr  as [Hgtpr | Hntpr].
           { rewrite Hgtpr,plus_S;simpl in *.
               assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
               by apply bool_dec.  
               destruct HgtbpSS  as [HgtbpcSS | HngtbpcSS].
              { rewrite HgtbpcSS. simpl.
                   right;right;right;right;right;right;left. auto.
              } 
                  rewrite <- H7 in HngtbpcSS. rewrite HgtbqcS in HngtbpcSS.
                  inversion HngtbpcSS. 
             }
                rewrite Hntpr,plus_S;simpl in *.
                rewrite <- H7. rewrite HgtbqcS;simpl in *.
                right;right;right;left. auto.
         }
         rewrite Hntpc,HgtbprS,sub_n_o;simpl in *.
         assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
         by apply bool_dec.
         destruct Hgtpr  as [Hgtpr | Hntpr].
          { rewrite Hgtpr,plus_S;simpl in *.
            assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
            by apply bool_dec.  
            destruct HgtbpSS  as [HgtbpcSS | HngtbpcSS].
            { rewrite HgtbpcSS. simpl. right;right;right;left. auto.
            }
              rewrite HngtbpcSS. simpl. rewrite <- H7 in HngtbpcSS.
              rewrite HgtbqcS in HngtbpcSS. inversion HngtbpcSS.
           }
           rewrite Hntpr,plus_S;simpl in *.
           assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
           by apply bool_dec.  
           destruct HgtbpSS  as [HgtbpcSS | HngtbpcSS].
            { rewrite HgtbpcSS. simpl. right;left. auto.
            }
            rewrite HngtbpcSS. rewrite <- H7 in HngtbpcSS.
            rewrite HgtbqcS in HngtbpcSS. inversion HngtbpcSS.
            rewrite HngtbpcSSf ,HgtbpcS,sub_n_o.
            assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
            by apply bool_dec.
            destruct Hgtpc  as [Hgtpc | Hntpc].
             { rewrite Hgtpc,HgtbprS,sub_n_o.
               assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
               by apply bool_dec.
               destruct Hgtpr  as [Hgtpr | Hntpr].
               { rewrite Hgtpr,plus_S;simpl in *.
                 assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
                 by apply bool_dec.  
                 destruct HgtbpSS  as [HgtbpcSS | HngtbpcSS].
                   { rewrite HgtbpcSS . simpl. right;right;right;right;
                     left. auto. 
                   } 
                  rewrite HngtbpcSS. simpl. rewrite <- H7 in HngtbpcSS.
                  rewrite HgtbqcS in HngtbpcSS. inversion HngtbpcSS.
                }
                rewrite Hntpr, plus_S;simpl in *.
                rewrite <- H7. rewrite HgtbqcS. simpl.
                right;left. auto.
              }

             rewrite Hntpc,HgtbprS,sub_n_o,plus_S;simpl in *.
             assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
             by apply bool_dec.
             destruct Hgtpr  as [Hgtpr | Hntpr].
             { assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpSS 
               by apply bool_dec.  
               destruct HgtbpSS  as [HgtbpcSS | HngtbpcSS].
                { rewrite Hgtpr,HgtbpcSS;simpl in *.
                  right;right;left. auto. 
                }
                rewrite Hgtpr,HngtbpcSS;simpl in * . 
                rewrite <- H7 in HngtbpcSS . 
                rewrite HgtbqcS in HngtbpcSS. 
                inversion HngtbpcSS.  
              }
                rewrite Hntpr.
                assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtbpcSS 
                by apply bool_dec.  
                destruct HgtbpcSS  as [HgtbpcSS | HngtbpcSS].
                { rewrite HgtbpcSS;simpl in *.
                  left. auto. 
                }
                  rewrite <- H7 in HngtbpcSS . 
                  rewrite HgtbqcS in HngtbpcSS. 
                  inversion HngtbpcSS.
       }
      }
         rewrite HgtbprS,HntbpcS;simpl in *.
         rewrite <- H7 in HntbpcS.
         rewrite Hgtqc in HntbpcS.
          { inversion HntbpcS. 
          }
          { rewrite HntbcS,HgtbpcS,plus_S;simpl in *.
            rewrite  <- H6 in HntbcS. rewrite HgtbcS in HntbcS.
            inversion HntbcS.
           }
          rewrite HntbcS,HntbpcS ,plus_S;simpl in *.
          rewrite  <- H6 in HntbcS. rewrite HgtbcS in HntbcS.
          inversion HntbcS. 
    } 
        inversion H4. 
     { inversion H5.  (* qr' = S pr'  qc' = S pc' *)
       rewrite <- H7 in *. rewrite <- H8 in *.
       rewrite Hgtqr,Hgtqc,plus_S,sub_n_o;simpl in *. (* here*)
       rewrite <- H7. rewrite HgtbcS,Hgtqc.
       assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
       by apply bool_dec.
       assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
       by apply bool_dec.
       destruct Hgtpr  as [Hgtpr | Hntpr];
       destruct Hgtpc  as [Hgtpc | Hntpc].
        { rewrite Hgtpc,Hgtqr,sub_n_o,Hgtpr,plus_S ;simpl in *.
          rewrite <- H8,HgtbqcS.
          right;right;right;right;right;right;right;left. auto. 
        }
        { simpl. rewrite Hntpc,Hgtqr,sub_n_o,plus_S,Hgtpr. simpl.
          rewrite <- H8 . rewrite HgtbqcS . simpl.
          right;right;right;right;left. auto. 
        }
        { rewrite Hgtpc,Hgtqr,sub_n_o,Hntpr,plus_S;simpl in *.
          rewrite <- H8 ,HgtbqcS. simpl.
          right;right;right;right;left. auto. 
        }
         rewrite Hntpc,Hgtqr,sub_n_o,Hntpr,plus_S;simpl in *.
         rewrite <- H8 . rewrite HgtbqcS . simpl.
         right;right;left. auto. 
     }
  inversion H5.
    { inversion H6. (* qr' = S pr'  qc' = pc' *)
      rewrite <- H8 . rewrite <- H9 .
      rewrite HgtbqcS ,Hgtqr ,plus_S,sub_n_o.
      rewrite <- H8 ,sub_n_o,plus_S;simpl in *.
      rewrite HgtbcS,HgtbqcS,Hgtqc,Hgtqr;simpl in *.
      left. auto. 
    }
  inversion H6. 
   { inversion H7. (* qr' = S pr'  S qc' = pc' *)
     rewrite <- H9. rewrite H10. 
     assert (S pc' <? c = true \/ S pc' <? c = false) as HgtbpcS 
     by apply bool_dec.
     destruct HgtbpcS as [HgtbpcS | HntbpcS].
      { rewrite HgtbpcS,Hgtqr,plus_S,sub_n_o;simpl in *.
        rewrite <- H9. rewrite HgtbcS ,HgtbpcS.
        assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
        by apply bool_dec.
     destruct Hgtpc  as [Hgtpc | Hntpc].
      { rewrite Hgtpc,Hgtqr,sub_n_o;simpl in *.
        right;left. auto. 
      }
     rewrite <- H10 in Hntpc .
     rewrite HgtbqcS in Hntpc.
     inversion Hntpc.
     }
     rewrite <- H10 in HntbpcS.
     rewrite HgtbqcSSt in HntbpcS.
     inversion HntbpcS. 
  }
  inversion H7.
  { inversion H8. (* qr' = pr' S qc' = pc' *)
     rewrite <- H10. 
     rewrite HgtbcS,HgtbqcSSt,plus_S,sub_n_o;simpl in *.
     rewrite HgtbqcSS,HgtbqcSSt,HgtbqcS,HgtbcS;simpl in *.
     right;right;left. auto. 
  }
   inversion H8.
   { inversion H9. (* S qr' = pr' S qc' = pc' *)
    rewrite HgtbqcSSt ,HgtbqcSS,plus_S,sub_n_o;simpl in *.
    rewrite H11.
    assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbpSS 
    by apply bool_dec. 
    destruct HgtbpSS  as [HgtbpSS | HngtbpSS].
    { rewrite HgtbpSS,HgtbqcSSt,HgtbqcS.
     assert (S pr' <? r = true \/ S pr' <? r = false) as HgtbprS 
     by apply bool_dec.
     destruct HgtbprS as [HgtbpcS | HntbpcS].
     { rewrite HgtbpcS;simpl in *.
       assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
       by apply bool_dec.
       destruct Hgtpr  as [Hgtpr | Hntpr].
       {  rewrite Hgtpr;simpl in *.
         right;right;right;left. auto. 
       }
     rewrite Hntpr ,plus_S ;simpl in *.
     rewrite <- H11 in Hntpr.
     rewrite HgtbcS in Hntpr.
     inversion Hntpr. 
   }
    rewrite <- H11 in HntbpcS.
    rewrite HgtbqcSS in HntbpcS.
    inversion HntbpcS. 
    }
    rewrite HngtbpSS,HgtbqcSSt,HgtbqcS. 
    rewrite <- H11,HgtbqcSS,HgtbcS;simpl in *.
    right; left. auto. 
 }
     inversion H9. 
  }
 rewrite HngtbqcSSf in *.
  inversion H1. 
 { inversion H2. (* S qr' = pr'  qc' = pc' *)
   rewrite H4 in *. rewrite <- H5 in *.
   rewrite HgtbqcS ,HgtbqcSS,plus_S,sub_n_o;simpl in *.
   assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbpSS 
   by apply bool_dec.  
   destruct HgtbpSS  as [HgtbpcSS | HngtbpcSS].
   { rewrite HgtbpcSS,HgtbqcS,Hgtqc,HgtbqcSS,plus_S,sub_n_o;simpl in *.
    rewrite HgtbcS.  simpl in *.
    right;right;right;right;left. auto. 
   }
   rewrite HngtbpcSS,HgtbqcS ,Hgtqc,HgtbqcSS,
   sub_n_o;simpl in *. rewrite HgtbcS;simpl in *.
   right;right;left. auto. 
 }
 inversion H2.
 { inversion H3. (* S qr' = pr'  qc' = S pc' *)
  rewrite <- H6,HgtbqcSS,Hgtqc,plus_S,sub_n_o;simpl in *.
  rewrite Hgtqc. rewrite H5.
  assert (S (S pr') <? r = true \/ S (S pr') <? r = false) as HgtbpSS 
  by apply bool_dec.  
  destruct HgtbpSS  as [HgtbpcSS | HngtbpcSS].
  { assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
    by apply bool_dec.
    destruct Hgtpc  as [Hgtpc | Hntpc].
   { rewrite Hgtpc,HgtbpcSS .
     assert (S pr' <? r = true \/ S pr' <? r = false) as HgtbprS 
     by apply bool_dec.
     assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
     by apply bool_dec.
     destruct HgtbprS  as [HgtbprS | HntbcS];
     destruct Hgtpr  as [Hgtpr | Hntpr].
     { rewrite HgtbprS,Hgtpr.
     rewrite plus_S;simpl in *.
     rewrite <- H6,HgtbqcS;simpl in *.
     right;right;right;right;right;left. auto. 
    } 
  { rewrite HgtbprS,Hntpr,plus_S;simpl in *.
    rewrite <- H6,HgtbqcS;simpl in *.
    rewrite <- H5 in Hntpr .
    rewrite HgtbcS in Hntpr.
    inversion Hntpr. 
  }
  { rewrite <- H5 in HntbcS .
    rewrite HgtbqcSS in HntbcS.
    inversion HntbcS. 
  }
  rewrite <- H5 in HntbcS .
  rewrite HgtbqcSS in HntbcS.
  inversion HntbcS. 
  }
  rewrite HgtbpcSS,Hntpc.
  rewrite <- H5,HgtbqcSS,HgtbcS,plus_S;simpl in *.
  rewrite <- H6,HgtbqcS ;simpl in *.
  right;right;left. auto.
  }
 rewrite HngtbpcSS.
 assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
  by apply bool_dec.
 destruct Hgtpc  as [Hgtpc | Hntpc].
 { rewrite Hgtpc.
  rewrite <- H5,HgtbqcSS,HgtbcS,plus_S;simpl in *.
  rewrite <- H6,HgtbqcS. simpl.
  right;right;right;left. auto. 
 }
  rewrite Hntpc;simpl in *.
  rewrite <- H5 in HngtbpcSS.
  rewrite <- H5,HgtbqcSS,HgtbcS,plus_S;simpl in *.
  rewrite <- H6,HgtbqcS;simpl in *.
  right;left. auto. 
 } 
 inversion H3. inversion H4. (* qr' = pr'  qc' = S pc' *)
 { rewrite <- H7,Hgtqc.
   rewrite <- H6,HgtbcS,plus_S,sub_n_o;simpl in *.
   rewrite HgtbqcSS,Hgtqc.
   assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
   by apply bool_dec.
   destruct Hgtpc  as [Hgtpc | Hntpc].
   { rewrite Hgtpc,HgtbcS,sub_n_o,Hgtqr,plus_S;simpl in *.
    rewrite <- H7,HgtbqcS. simpl.
    right;right;right;right;right;right;left. auto. }
   rewrite Hntpc,HgtbcS ,sub_n_o, Hgtqr ;simpl in *.
   rewrite plus_S.
   rewrite <- H7,HgtbqcS;simpl in *.
   right;right;right;left. auto. 
 }
 inversion H4.
 {  inversion H5. (*qr' = S pr' qc' = S pc' *)
    rewrite <- H7. rewrite <- H8.
   rewrite Hgtqr,Hgtqc,plus_S,sub_n_o;simpl in *.
   rewrite <- H7,HgtbcS,Hgtqc. rewrite H8.
  assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
  by apply bool_dec.
  destruct Hgtpc  as [Hgtpc | Hntpc].
  { rewrite Hgtpc,Hgtqr,sub_n_o;simpl in *.
   assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
  by apply bool_dec.
  destruct Hgtpr  as [Hgtbpr | Hntbpr].
   { rewrite Hgtbpr,plus_S;simpl in *.
    rewrite <- H8,HgtbqcS;simpl in *.
    right;right;right;right;right;right;
    right;left. auto. 
   }
    rewrite Hntbpr,plus_S ;simpl in *.
    rewrite <- H8,HgtbqcS;simpl in *.
    right;right;right;right;left. auto. 
  }
  rewrite Hntpc,Hgtqr,sub_n_o;simpl in *.
  assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
  by apply bool_dec.
  destruct Hgtpr  as [Hgtbpr | Hntbpr].
  { rewrite Hgtbpr,plus_S;simpl in *.
  rewrite <- H8,HgtbqcS;simpl in *.
  right;right;right;right;left. auto.
  }
 rewrite Hntbpr,plus_S ;simpl in *.
 rewrite <- H8,HgtbqcS;simpl in *.
 right;right;left. auto. 
 } 
 inversion H5. 
  { inversion H6.
 rewrite <- H8 .
 rewrite <- H9.  rewrite HgtbqcS ,Hgtqr,
 plus_S;simpl in *.
 rewrite <- H8 ,HgtbcS,HgtbqcS,
 sub_n_o,Hgtqc;simpl in *.
 left. auto.
 } 
 inversion H6. 
 * rewrite HngtbqcSS,HgtbqcS,HgtbcS,sub_n_o,
   plus_S in H1;simpl in *.
  assert (qc' <? c = true) as Hgtc by try (apply gtb_true_S; auto).
  assert (qr' <? r = true) as Hgtr by try (apply gtb_true_S; auto).
  rewrite Hgtc,Hgtr in H1; simpl in *.
  assert (S (S qc') <? c = true \/ S (S qc') <? c = false) as HgtbcSS 
  by apply bool_dec. 
  destruct HgtbcSS as [HgtbcSS | HngtbcSS].
  { rewrite HgtbcSS in H1.
  inversion H1. 
   { inversion H2.
   rewrite <- H5 in *. rewrite <- H4 in *.
  rewrite HgtbcS ,Hgtc,plus_S; simpl in *.
  rewrite HngtbqcSS,Hgtc,sub_n_o,HgtbcS; simpl in *.
  assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
  by apply bool_dec.
  destruct Hgtpc  as [Hgtpc | Hntpc].
   { rewrite Hgtpc,sub_n_o,Hgtr,plus_S.
    assert (S (S pc') <? c = true \/ S (S pc') <? c = false) as HgtpcSS 
    by apply bool_dec. 
   destruct HgtpcSS  as [HgtpcSS | HngtpcSS].
    { rewrite HgtpcSS; simpl in *.
      rewrite H5.
     right;right;right;right;left. auto.
   }
    rewrite <- H5 in HngtpcSS.
   rewrite HgtbqcS in HngtpcSS.
   inversion HngtpcSS.
  }
  rewrite Hntpc,sub_n_o,Hgtr,plus_S.
  rewrite <- H5,HgtbqcS; simpl in *.
  right;right;left. auto.
  }
 inversion H2. 
  { inversion H3. (*qr' = S pr' qc' = S pc' *)
  rewrite <- H6. rewrite <- H5.
  rewrite Hgtr,Hgtc,plus_S.
  rewrite <- H5 ,sub_n_o; simpl in *.
  rewrite HgtbcS,Hgtc.
  assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
  by apply bool_dec.
  destruct Hgtpc  as [Hgtpc | Hntpc].
  { rewrite Hgtpc,Hgtr,sub_n_o.
    assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
    by apply bool_dec.
    destruct Hgtpr  as [Hgtpr | Hntpr].
    { rewrite Hgtpr,plus_S; simpl in *.
      rewrite <- H6,HgtbqcS ; simpl in *.
      right;right;right;right;right;right;right;left. auto.
     } 
     rewrite Hntpr,plus_S; simpl in *.
     rewrite <- H6,HgtbqcS; simpl in *.
     right;right;right;right;left. auto. 
  }
  
    rewrite Hntpc,Hgtr,sub_n_o; simpl in *.
    assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
    by apply bool_dec.
    destruct Hgtpr  as [Hgtpr | Hntpr].
     { rewrite Hgtpr,plus_S;simpl in *.
       rewrite <- H6 ,HgtbqcS; simpl in *.
       right;right;right;right;left. auto. 
     }
   rewrite Hntpr,plus_S; simpl in *.
   rewrite <- H6  ,HgtbqcS; simpl in *.
   right;right;left. auto.
   }
  inversion H3. 
   {  inversion H4.
     rewrite  <- H6 . 
     assert (S pc' <? c = true \/ S pc' <? c = false) as HgtbpcS 
     by apply bool_dec.
     destruct HgtbpcS as [HgtbpcS | HntbpcS]. 
     { rewrite HgtbpcS,Hgtr,plus_S.
       rewrite <- H6; simpl in *.
       rewrite HgtbcS,HgtbpcS,sub_n_o; simpl in *.
       assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
       by apply bool_dec.
       destruct Hgtpc  as [Hgtpc | Hntpc].
     { rewrite Hgtpc,Hgtr,sub_n_o.
       assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
       by apply bool_dec.
       destruct Hgtpr  as [Hgtpr | Hntpr].
        rewrite Hgtpr; simpl in *.
       left. auto.
       rewrite Hntpr,plus_S; simpl in *.
       left. auto.
     }
    rewrite Hntpc,Hgtr,sub_n_o .
    left. auto.
    }
  rewrite <- H7 in HntbpcS.
  rewrite HgtbqcS in HntbpcS.
  inversion HntbpcS.
  }
  inversion H4.
  {  inversion H5.
     rewrite <- H7,Hgtr. rewrite  H8.
    assert (S pc' <? c = true \/ S pc' <? c = false) as HgtbpcS 
    by apply bool_dec.
   destruct HgtbpcS as [HgtbpcS | HntbpcS].
    { rewrite HgtbpcS,plus_S .
      rewrite <- H7 ,sub_n_o; simpl in *.
      rewrite HgtbpcS,HgtbcS; simpl in *.
      rewrite <- H8,HgtbqcS,Hgtr; simpl in *.
      right;left. auto.
   }
   rewrite <- H8 in HntbpcS. rewrite HgtbcSS in HntbpcS.
   inversion HntbpcS.
  }
  inversion H5.
  {  inversion H6.
     rewrite HgtbcSS. rewrite <- H8,HgtbcS,plus_S; simpl in *.
     rewrite HngtbqcSS,HgtbcSS; simpl in *.
     rewrite HgtbcS,HgtbqcS,sub_n_o,Hgtr; simpl in *.
    left. auto. 
  }
 inversion H6. 
 }
 rewrite HngtbcSS in H1.
 inversion H1. inversion H2.
 rewrite <- H5.
 rewrite <- H4,HgtbcS,Hgtc,plus_S; simpl in *.
 rewrite HngtbqcSS,Hgtc,HgtbcS,sub_n_o; simpl in *.
 assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
 by apply bool_dec.
 destruct Hgtpc  as [Hgtpc | Hntpc].
  { rewrite Hgtpc,sub_n_o,Hgtr,plus_S.
    rewrite <- H5,HgtbqcS ; simpl in *.
    right;right;right;right;left. auto. }
    rewrite Hntpc,sub_n_o,Hgtr,plus_S; simpl in *.
    rewrite <- H5,HgtbqcS; simpl in *.
    right;right;left. auto. 
    inversion H2. inversion H3.
    rewrite <- H5. 
    rewrite <- H6,Hgtc,Hgtr,plus_S; simpl in *.
    rewrite <- H5,HgtbcS,Hgtc,sub_n_o.
    assert (pc' <? c = true \/  pc' <? c = false) as Hgtpc 
    by apply bool_dec.
    destruct Hgtpc  as [Hgtpc | Hntpc].
     { rewrite Hgtpc,Hgtr,sub_n_o;simpl in *.
       assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
       by apply bool_dec.
      destruct Hgtpr  as [Hgtpr | Hntpr].
      { rewrite Hgtpr,plus_S;simpl in *.
        rewrite <- H6,HgtbqcS ;simpl in *.
        right;right;right;right;right;right;right;left. auto.
      }
     rewrite Hntpr,plus_S;simpl in *.
     rewrite <- H6,HgtbqcS ;simpl in *.
     right;right;right;right;left. auto. 
     }
  rewrite Hntpc,Hgtr,sub_n_o.
  assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
  by apply bool_dec.
  destruct Hgtpr  as [Hgtpr | Hntpr].
   { rewrite Hgtpr,plus_S; simpl in *.
  rewrite <- H6,HgtbqcS;simpl in *.
  right;right;right;right;left. auto. 
   }
  rewrite Hntpr,plus_S; simpl in *.
  rewrite <- H6,HgtbqcS; simpl in *.
  right;right;left. auto.
 inversion H3.
  {  inversion H4.
     rewrite <- H6. rewrite <- H7.
     rewrite HgtbqcS,Hgtr,plus_S.
     rewrite <- H6; simpl in *.
     rewrite HgtbcS,HgtbqcS,sub_n_o,Hgtc,Hgtr,
     sub_n_o.
    assert (pr' <? r = true \/  pr' <? r = false) as Hgtpr 
    by apply bool_dec.
    destruct Hgtpr  as [Hgtpr | Hntpr].
     { rewrite Hgtpr,plus_S,HngtbcSS ; simpl in *.
       left. auto. 
     }
   rewrite Hntpr,plus_S,HngtbcSS; simpl in *.
   left. auto.
   }
    inversion H4.
 - rewrite HgtbcS,HntbqcS,plus_S,sub_n_o
  in H1; simpl in *.
  inversion H1.
 - rewrite HntbcS,HgtbqcS in H1; simpl in *.
  inversion H1.
 - rewrite HntbcS,HntbqcS in H1; simpl in *.
  inversion H1.
Qed. 

(*the path relation is commutative. if p has path to q then q has a path to p*)
Lemma path_8_comm: forall p q (img: list pixel), 
    path_8 p q img -> path_8 q p img.
Proof.
 intros.
 induction H as [?p ?img | ?r ?c ?pr ?pc ?qr ?qc ?p ?q ?img Hr Hc Hp Hq Hn | ?p ?q ?r ?img ?Hpr ? ?Hrq].
 + apply path_8_self.
 + apply path_8_neigh with (r:= r) (c:= c) (pr:= pr) (pc:= pc) (qr:=qr) (qc:=qc); auto. 
   apply neighbouts8_comm with (pr:= pr) (pc:= pc) (qr:=qr) (qc:=qc); auto. 
 + apply path_8_trans with (q:= q); auto.
Qed. 

(**************************************************************)
(*********** Proof of Equivalence of Connectivity *************)
(**************************************************************)

(*any pixel p is connected with itself.*)
Lemma connected_8_refl: forall p img, connected_8 p p img.
Proof. 
 intros.
 apply Connected_8.
 apply path_8_self.
Qed.

(*if p is connected to q, then q is connected p as well*)
Lemma connected_8_comm: forall p q img, connected_8 p q img -> connected_8 q p img.
Proof. 
 intros. 
 induction H. 
 apply Connected_8.
 apply path_8_comm; auto.
Qed.

(*if p is connected to q and q is connected to r, then 
  p is connected to r as well*)
Lemma connected_8_assoc: forall p q r img, 
      connected_8 p q img -> connected_8 q r img -> connected_8 p r img. 
Proof. 
 intros. 
 induction H.
 induction H0 as [q r].
 apply Connected_8.
 apply path_8_trans with (q:= q); auto.
Qed. 

(***************************************************************)
