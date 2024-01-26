(** In this file, neighbours 4 of a pixel, path between any two pixel, connectivity of
 any two pixels in an image are defined. Furthermore, it is proved that the connectivity
 relation is an equivalence relation by proving it is relfexive, commutative and transitive *)

Require Export binary_image. 

(*Four neighbours of a pixel. Every pixel has four neighbours located
  on the left, right, up and down (but not at the diagonals). *)
Definition neighbours_4 (r c: nat) (p: pixel) (img: list pixel) : list pixel := 
 match p with
  | B{r', c', col} => if (r' <?  r ) &&
                         (c' <?  c)  then
    match r', c' with  
    | 0, 0 => [B{1,0,C{1!0!img}};B{0,1,C{0!1!img}}]
    | 0, c => [B{1,c,C{1!c!img}};B{0,c+1,C{0!c+1!img}};B{0,c-1,C{0!c-1!img}}]
    | r, 0 => [B{r+1,0,C{r+1!0!img}};B{r-1,0,C{r-1!0!img}};B{r,1,C{r!1!img}}]
    | _, _ => [B{r'+1,c',C{r'+1!c'!img}};B{r'-1,c',C{r'-1!c'!img}};
               B{r',c'+1,C{r'!c'+1!img}};B{r',c'-1,C{r'!c'-1!img}}]
    end
   else []
end.

(*Exclude neighbours outside the image boundary. Only neighbours located
 inside the image (this is constrained by the image dimensizion/size 
 row (r) and column (c) values) are considered. *)
Fixpoint WF_neighbours (r c: nat) (lp: list pixel) : list pixel :=
  match lp with 
 | nil => nil 
 | h::tl => match h with
   | B{r',c',col} => if (r'<? r) && (c'<? c) then 
                        h::(WF_neighbours r c tl)
                     else WF_neighbours r c tl
   end
 end.

(*Path between any two pixels p and q.
 - a pixel has a path with itself
 - if a pixel q is in neighbours of pixel p, then there is a path 
   from p to q.
 - if there is a path from p to q and q to r, then there is a path from
   p to r.*)
Inductive path_4: pixel -> pixel -> list pixel -> Prop :=
 | path_4_self: forall p img, path_4 p p img
 | path_4_neigh: forall r c qr qc pr pc p q img, r > 0 -> c > 0->
   p = B{pr,pc,C{pr!pc!img}} ->
   q = B{qr,qc,C{qr!qc!img}} ->
   C{pr!pc!img} = C{qr!qc!img} ->
   List.In q (WF_neighbours r c ( neighbours_4 r c p img)) -> path_4 p q img
 | path_4_trans: forall p q r img, path_4 p q img -> path_4 q r img -> path_4 p r img.

(*Two pixels are connected, if there is a path between them.*)
Inductive connected_4: pixel -> pixel -> list pixel -> Prop:=
 | Connected_4: forall p q img, path_4 p q img -> connected_4 p q img.

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
Fixpoint path_4_b (r c size: nat) (p q: pixel) (nbr: list pixel) (img: list pixel): bool :=
 match size with
 | O => false
 | S size' => (colpixEq p q) &&  (*p and q should have the same colors*)
 if (pixeq p q) then true else
  let Nq :=  removeblurN (removeDiffCol q (WF_neighbours r c (neighbours_4 r c q img))) ++ nbr in 
  match Nq with
  | nil => false
  | nq::tl' => if colpixEq nq q then 
                path_4_b r c size' p nq tl' (setColourPixImg q blurr img)
               else false 
   end
  end.

(*two pixels p and q are connected if there is a path from p to q*)
Definition connected_4_b (row col: nat) (p q: pixel) (object: list pixel) := 
   path_4_b row col (row*col) p q nil object. 

(*checks if a pixel 'pix' is connected to every other pixel of the object 'obj'. *)
Fixpoint connected_4_b_pix_obj (row col: nat) (pix: pixel) (rem: list pixel) (object: list pixel) :=
  match rem with
 | nil => true
 | p::tl => (connected_4_b row col pix p object) && 
             connected_4_b_pix_obj row col pix tl object
 end.  

(*checks if every pixel of the object is connected to every other pixel of the object. *)
Fixpoint connected_4_all_b (row col: nat) (rem: list pixel) (object: list pixel) : bool :=
 match rem with
 | nil => true 
 | p::tl => (connected_4_b_pix_obj row col p object object) && 
             connected_4_all_b row col tl object
 end. 

(*Well-formed object: an image object is well-formed if all the pixels of the object are 
  connected to every other pixel. *)
Definition WF_object_4_b (row col: nat) (obj: list pixel) : bool := 
        connected_4_all_b row col obj obj.

(********************************************************)
(************ Proof of image properties *****************)
(********************************************************)

(*If p is neighbour of q, then q is neighbout of p*)
 Lemma neighbouts4_comm: forall (r c: nat) (p q: pixel) (pr pc qr qc: nat) (img: list pixel), 
   r > 0 ->
   c > 0 ->
   p = B{pr,pc,C{pr!pc!img}} ->
   q = B{qr,qc,C{qr!qc!img}} ->
     List.In p (WF_neighbours r c (neighbours_4 r c q img)) -> 
     List.In q (WF_neighbours r c (neighbours_4 r c p img)).
 Proof. 
 intros r c p q pr pc qr qc img H H0 Hp Hq H1.
 rewrite Hp, Hq in *. 
 destruct pr as [ | pr']. destruct pc as [ | pc'] .
 destruct qr as [ | qr'].  destruct qc as [ | qc'].

 + (*Case 1: p = (0,0), q = (0,0)*)
  simpl in *. 
  assert ( 0 <? r = true). apply Nat.ltb_lt; auto. 
  assert ( 0 <? c = true). apply Nat.ltb_lt; auto. 
  assert (ifc1 : ((0 <? r) && (0 <? c))= true). rewrite H2, H3; simpl; auto.  
  rewrite ifc1 in *. 
  unfold WF_neighbours in *.
  rewrite H3 in *. rewrite and_b_true in *.
  rewrite H2 in *. rewrite and_comm in *. rewrite and_b_true in *. destruct ifc1.
  destruct (1 <? r); simpl in *.
  * inversion H1.  inversion H4. 
    destruct (1 <? c). {inversion H4.  inversion H5.  inversion H5. }
    inversion H4. 
  * destruct (1 <? c). 
    {inversion H1. inversion H4. inversion H4. }
    inversion H1. 
  
 + (*Case 2: p = (0,0), q = (0,c)*) 
   destruct qc' as [ | qc''].
   - (*sub case: qc = 0 , means q is at (0,1). the conclusion is provable. *)
     unfold neighbours_4 in *. simpl in *.  
     assert ( 0 <? r = true). apply Nat.ltb_lt; auto. 
     assert ( 0 <? c = true). apply Nat.ltb_lt; auto.  
     assert (ifc1 : ((0 <? r) && (0 <? c))= true). rewrite H2, H3; simpl; auto.  
     rewrite ifc1.
     simpl in *. 
     rewrite H2 in *. 
     rewrite H3 in *. 
     rewrite and_comm in *.
     rewrite and_b_true in *.
     destruct (1 <? c). 
     * unfold WF_neighbours in *. destruct ifc1.   
       assert (ifc1 : ((0 <? r) && (0 <? c))= true). rewrite H2, H3; simpl; auto.
       rewrite ifc1 in *.
       rewrite H2 in *; simpl in *.  
       destruct ((1 <? r) && (1 <? c)).
       inversion H1. inversion H4. 
       destruct (2 <? c). 
       { inversion H4. inversion H5. 
         inversion H5. inversion H6. destruct (1 <? r). simpl. right. left; auto.    
         simpl; left; auto. inversion H6. }
       inversion H4. inversion H5. destruct (1 <? r). simpl. right. left; auto. 
       simpl; left; auto. inversion H5. 
       destruct (2 <? c).
       {inversion H1. inversion H4. inversion H4. inversion H5. 
        destruct (1 <? r). simpl.  right. left; auto. 
        simpl. left; auto. inversion H5. }
       { inversion H1. inversion H4. destruct (1 <? r). simpl. right. left; auto.
         simpl. left; auto. inversion H4. } 
     * inversion H1. 
   - simpl in *.
     assert ( 0 <? r = true). apply Nat.ltb_lt; auto. 
     assert ( 0 <? c = true). apply Nat.ltb_lt; auto. 
     assert (ifc1 : ((0 <? r) && (0 <? c))= true). rewrite H2, H3; simpl; auto. 
     rewrite ifc1.
     rewrite H2 in *. 
     rewrite and_comm in *.
     rewrite and_b_true in *.
     destruct (S (S qc'') <? c). 
     * unfold WF_neighbours in H1.
       rewrite H2 in *. 
       destruct ((1 <? r) && (S (S qc'') <? c)). 
       { destruct ((S (S (qc'' + 1)) <? c)); simpl in *.
         { destruct (S qc'' <? c). 
           { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5.
             inversion H6. inversion H6. }
         {inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. }
         }
        { destruct (S qc'' <? c). 
          { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. }
          { inversion H1. inversion H4. inversion H4. }
        }
      }
     {destruct (S (S (qc'' + 1)) <? c); simpl in *. 
        destruct (S qc'' <? c).
         { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. }
         { inversion H1. inversion H4. inversion H4. }
      { destruct (S qc'' <? c). 
        { inversion H1. inversion H4. inversion H4. } 
        { inversion H1. }
      }
      }
    * inversion H1. 
+ (*Case 3: p = (0,0), q = (>0,c)*)
 destruct qc as[ | qc']. 
  * simpl in *.  
    assert ( 0 <? r = true). apply Nat.ltb_lt; auto. 
    assert ( 0 <? c = true). apply Nat.ltb_lt; auto. 
    assert (ifc1 : ((0 <? r) && (0 <? c))= true). rewrite H2, H3; simpl; auto. 
    rewrite ifc1.
    rewrite H3 in H1; simpl in *. 
    rewrite and_b_true in *.
    rewrite H2.
    rewrite H3. 
    rewrite and_b_true in *.
    destruct qr' as [ | qr'']. 
    - destruct (1 <? r); simpl in *. 
      { rewrite H3 in *; simpl in *. 
        rewrite and_b_true in *.
        destruct (2 <? r).
        { rewrite H2 in H1; simpl in *.
          destruct ((1 <? r) && (1 <? c)). 
          { inversion H1. inversion H4. inversion H4. inversion H5. left; auto. 
            inversion H5. inversion H6. inversion H6. 
          }
          inversion H1. inversion H4. inversion H4. inversion H5. left; auto. inversion H5.
        }
        rewrite H2 in *; simpl in *. 
        destruct ((1 <? r) && (1 <? c)). 
        { inversion H1. inversion H4. left; auto. inversion H4. inversion H5. inversion H5. 
        }
        inversion H1. inversion H4. left; auto. inversion H4. 
      }
     inversion H1. 
    - destruct (S (S qr'') <? r); simpl in *. 
      { rewrite H3 in *; simpl in *. 
        destruct ((S (S (qr'' + 1)) <? r)); simpl in *. 
        { destruct ((S qr'' <? r)); simpl in *. 
          { destruct ((S (S qr'') <? r) && (1 <? c)); simpl in *. 
            {inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
             inversion H6. inversion H6. 
            }
          inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
          }
          destruct ((S (S qr'') <? r) && (1 <? c)); simpl in *. 
          { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. } 
          inversion H1. inversion H4. inversion H4. 
        }
       destruct ((S qr'' <? r)); simpl in *. 
       { destruct ((S (S qr'') <? r) && (1 <? c)). 
         { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5.  }
         inversion H1. inversion H4. inversion H4.  
       }
       destruct ((S (S qr'') <? r) && (1 <? c)). 
       { inversion H1. inversion H4. inversion H4. }
       inversion H1. 
      }
     inversion H1. 
   * simpl in *.  
     assert ( 0 <? r = true). apply Nat.ltb_lt; auto. 
     assert ( 0 <? c = true). apply Nat.ltb_lt; auto. 
    assert (ifc1 : ((0 <? r) && (0 <? c))= true). rewrite H2, H3; simpl; auto. 
    rewrite ifc1.
    destruct ((S qr' <? r) && (S qc' <? c)); simpl in *. 
    { destruct ((S (qr' + 1) <? r) && (S qc' <? c)).
      { destruct ((qr' - 0 <? r) && (S qc' <? c)). 
        { destruct ((S qr' <? r) && (S (qc' + 1) <? c)). 
          { destruct ((S qr' <? r) && (qc' - 0 <? c)). 
            { inversion H1. inversion H4. 
              inversion H4. inversion H5. inversion H5. inversion H6. inversion H6.
              inversion H7. inversion H7. 
            }
           inversion H1. inversion H4. inversion H4. inversion H5. inversion H5.
           inversion H6. inversion H6.
          }
        destruct ((S qr' <? r) && (qc' - 0 <? c)). 
        { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. inversion H6.
          inversion H6. 
        }
        inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
       }
      destruct ((S qr' <? r) && (S (qc' + 1) <? c)). 
      { destruct ((S qr' <? r) && (qc' - 0 <? c)). 
        { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. inversion H6. 
          inversion H6.
        }
       inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
      }
     destruct ((S qr' <? r) && (qc' - 0 <? c)). 
     { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. }
     inversion H1. inversion H4. inversion H4. 
    } 
   destruct ((qr' - 0 <? r) && (S qc' <? c)). 
   { destruct ((S qr' <? r) && (S (qc' + 1) <? c)). 
    { destruct ((S qr' <? r) && (qc' - 0 <? c)). 
      { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. inversion H6.
        inversion H6. 
      }
      inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
    }
   destruct ((S qr' <? r) && (qc' - 0 <? c)). 
   { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. }
   inversion H1. inversion H4. inversion H4. 
   }
   destruct ((S qr' <? r) && (S (qc' + 1) <? c)). 
   { destruct ((S qr' <? r) && (qc' - 0 <? c)). 
     { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. }
     inversion H1. inversion H4. inversion H4. 
   }
   destruct ((S qr' <? r) && (qc' - 0 <? c)). 
   { inversion H1. inversion H4. inversion H4. }
   inversion H1. 
  }
  inversion H1. 
+ (*Case 4: p = (0,>0), q = (r,c)*)
 destruct qr as [ | qr']; destruct qc as [ | qc']. 
 * (*Case: p is at (0,>0) and q is at (0, 0). should close by contradiction.*)
   destruct pc' as [ | pc'']. 
   - simpl in *. 
    assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
    assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
    assert (ifc1 : ((0 <? r) && (0 <? c))= true). rewrite H2, H3; simpl; auto. 
    rewrite ifc1 in *.
    rewrite H2; simpl in *.
    rewrite H3 in *; simpl in *.   
    destruct (1 <? r); simpl in *.
    { rewrite H2 in *; simpl in *.  
    - destruct (1 <? c); simpl in *. 
     { destruct ((1 <? r) && (1 <? c)). 
       { rewrite H2; simpl. 
         destruct (2 <? c). 
         { rewrite H3. right. simpl. right. left. 
           inversion H1. inversion H4. inversion H4. inversion H5. auto. 
           inversion H5. 
         }
         rewrite H3. right. 
         simpl. left. 
         inversion H1. inversion H4. inversion H4. inversion H5. auto. inversion H5. 
       }
       rewrite H2; simpl. 
       rewrite H3; simpl. 
       destruct (2 <? c). simpl. 
       right. left. 
       inversion H1. 
       inversion H4; auto. 
       inversion H4. inversion H5; auto. inversion H5. 
       simpl. left. 
       inversion H1. 
       inversion H4. inversion H4. inversion H5. auto. inversion H5. 
     }
     inversion H1. inversion H4. inversion H4. 
    } 
    rewrite H2 in *; simpl in *. 
    destruct (1 <? c). 
    { simpl. rewrite H2; rewrite H3; simpl. 
      destruct ((1 <? r) && (1 <? c)). 
      { destruct (2 <? c). 
        { simpl. right. right. left. 
          inversion H1. inversion H4; auto. inversion H4. 
        }
        simpl. right. left. inversion H1. inversion H4; auto. inversion H4. 
      }
      destruct (2 <? c). 
      { simpl. right. left. inversion H1. inversion H4; auto. inversion H4.  }
      simpl. left. inversion H1. inversion H4; auto. inversion H4. 
     }
     inversion H1. 
    - simpl in *. 
     assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
     assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
     assert (ifc1 : ((0 <? r) && (0 <? c))= true). rewrite H2, H3; simpl; auto. 
     rewrite ifc1 in *.
     rewrite H2; simpl in *.
     rewrite H3 in *; simpl in *. 
     destruct (1 <? r); simpl in *. 
     { rewrite H2 in H1; simpl in *.  
       destruct (1 <? c). 
       { destruct (S (S pc'') <? c). 
         { simpl. 
           destruct ((1 <? r) && (S (S pc'') <? c)). 
           { rewrite H2; simpl. 
             destruct (S (S (pc'' + 1)) <? c). 
             { destruct (S pc'' <? c). 
               { simpl in *.
                 inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
               }
               inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
             }
             destruct (S pc'' <? c ). 
             { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. }
             inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
          }
          rewrite H2; simpl. 
          destruct (S (S (pc'' + 1)) <? c). 
          { destruct (S pc'' <? c). 
            { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. }
            inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
          }
          destruct (S pc'' <? c). 
          { inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. }
          inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
         }
        inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
       }
       inversion H1. inversion H4. inversion H4. 
      } 
      rewrite H2 in H1; simpl in *. 
      destruct (1 <? c).
      { inversion H1. inversion H4. inversion H4. }
      inversion H1. 
  *  (*Case: p is at (0,>0) and q is at (0, >0). should close by contradiction.*)
   simpl in *. 
   assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
   rewrite H2 in *; simpl; auto. 
   assert ((S qc' <? c) = true \/ (S qc' <? c) = false) by apply bool_dec. 
   destruct H3 as [Hgt1 | Hngt1]. 
   - rewrite Hgt1 in H1; simpl in H1.  
     { rewrite H2 in *; simpl in *. rewrite sub_n_o in *. 
       rewrite Hgt1 in H1; simpl in *.
       assert (1 <? r = true \/ 1 <? r = false) by apply bool_dec.
       destruct H3 as [Hgt2 | Hngt2].
       { rewrite Hgt2 in H1; simpl in *.
         { assert (S pc' <? c = true \/ S pc' <? c = false) by apply bool_dec.
           destruct H3 as [Hgt3 | Hngt3]. 
           { rewrite Hgt3.  
             assert (S (qc' + 1) <? c = true \/ S (qc' + 1) <? c = false) by apply bool_dec.
             destruct H3 as [Hgt4 | Hngt4].
             { rewrite Hgt4 in H1.    
               assert (qc' <? c = true \/ qc' <? c = false) by apply bool_dec.
               destruct H3 as [Hgt5 | Hngt5].
               { rewrite Hgt5 in H1. 
                 inversion H1. inversion H3. 
                 inversion H3.
                 { inversion H4.
                   rewrite <- H6 in *.
                   simpl. rewrite H2 in *; simpl.
                   rewrite Hgt2; rewrite Hgt3; simpl.    
                   assert (S (qc' + 1 + 1) <? c = true \/ S (qc' + 1 + 1) <? c = false) by apply bool_dec.
                   destruct H5 as [Hgt6 | Hngt6].
                   { rewrite Hgt6; simpl.  
                     rewrite plus_S.  
                     rewrite Hgt1. 
                     right. right. simpl. left; auto. 
                   } 
                   rewrite Hngt6; simpl. 
                   rewrite plus_S.
                   rewrite Hgt1. right. simpl; left; auto.
                 }
                 inversion H4. inversion H5. 
                 { simpl. rewrite Hgt2; rewrite Hgt3; simpl. 
                   rewrite plus_S in *.
                   rewrite H7 in Hgt1.
                   rewrite H2; rewrite Hgt1; simpl.
                   right. left; auto. 
                 }
                 inversion H5.
               }
               rewrite Hngt5 in H1. 
               inversion H1. inversion H3.  
               inversion H3.
               { inversion H4. rewrite <- H6 in *.  
                 rewrite plus_S in *.
                 inversion Hgt1.
                 assert (qc' <? c = true) as Hgtc.
                 apply gtb_true_S; auto.
                 rewrite Hngt5 in Hgtc. inversion Hgtc. 
               }
              inversion H4.
              }
              rewrite Hngt4 in H1.
              assert (qc' <? c = true) as Hgtc. apply gtb_true_S; auto.
              rewrite Hgtc in H1. 
              inversion H1. inversion H3. inversion H3.
              { inversion H4. 
                rewrite plus_S in *.
                simpl. 
                rewrite Hgt2; rewrite Hgt3; simpl. 
                rewrite H6 in Hgt1.
                rewrite H2; rewrite Hgt1; simpl. 
                right. left; auto. 
              }
              inversion H4. 
            }
            rewrite Hngt3. 
            simpl. 
            assert (S (qc' + 1) <? c = true \/ S (qc' + 1) <? c = false) by apply bool_dec.
            destruct H3 as [Hgt4 | Hngt4].
            { rewrite Hgt4 in H1; simpl in *.
              assert (qc' <? c = true) as Hgtc. apply gtb_true_S; auto.
              rewrite Hgtc in H1. 
              inversion H1. inversion H3. inversion H3.
              inversion H4. 
              rewrite plus_S in *.
              rewrite <- H6 in Hngt3.
              rewrite Hngt3 in Hgt4. inversion Hgt4. 
              inversion H4. inversion H5.
              rewrite plus_S in *.
              rewrite H7 in Hgtc. 
              rewrite Hngt3 in Hgtc. inversion Hgtc.
              inversion H5. 
             }
             rewrite Hngt4 in H1.   
             assert (qc' <? c = true) as Hgtc. apply gtb_true_S; auto.
             rewrite Hgtc in H1. 
             inversion H1. inversion H3. inversion H3.
             inversion H4. 
             rewrite H6 in *. 
             rewrite Hngt3 in Hgtc. inversion Hgtc.
             inversion H4. 
           }  
          }
          rewrite Hngt2 in H1; simpl in *.
          assert (S (qc' + 1) <? c = true \/ S (qc' + 1) <? c = false) by apply bool_dec.
          destruct H3 as [Hgt3 | Hngt3]. 
           { rewrite Hgt3 in H1.  
             assert (qc' <? c = true) as Hgtc. apply gtb_true_S; auto.
             rewrite Hgtc in H1. 
             inversion H1.
             { inversion H3. 
               rewrite <- H5 in *.
               rewrite plus_S in *.
               rewrite Hgt3. simpl. 
               rewrite Hngt2; simpl. 
               assert ((S (S (qc' + 1)) <? c) = true \/ (S (S (qc' + 1)) <? c) = false) by apply bool_dec.
               destruct H4 as [Hgt4 | Hngt4].
               { rewrite Hgt4; rewrite H2; simpl. 
                 rewrite Hgt1.
                 right.
                 simpl. left; auto. 
               }
               rewrite H2; rewrite Hngt4; simpl in *.
               rewrite Hgt1. simpl. 
               left; auto.
             }
             inversion H3. 
             { inversion H4. 
               rewrite H6 in *.
               rewrite Hgtc. 
               simpl. 
               rewrite Hngt2; simpl. 
               rewrite plus_S in *.
               rewrite Hgt1; rewrite H2; simpl.
               left; auto.
              }
             inversion H4.
            }
            rewrite Hngt3 in H1.
            assert (qc' <? c = true) as Hgtc. apply gtb_true_S; auto.
            rewrite Hgtc in H1. 
            inversion H1. inversion H3.
            { rewrite H5 in *.
              rewrite Hgtc. simpl. 
              rewrite Hngt2; simpl. 
              rewrite plus_S in *.
              rewrite Hgt1; rewrite H2; simpl.
              left; auto. 
            }
            inversion H3. 
          }
         -
         rewrite Hngt1 in H1; simpl in *. inversion H1.  
   * (*Case: p is at (0,>0) and q is at (>0, 0). should close by contradiction.*)
    simpl in *.
    assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
    assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
    rewrite H2 in H1; rewrite H3 in *; simpl in *. 
    assert ((S qr' <? r) = true \/ (S qr' <? r) = false) by apply bool_dec.
    destruct H4 as [Hgt1 | Hngt1]. 
    - rewrite Hgt1 in H1; simpl in *.
      assert ((S (qr' + 1) <? r) = true \/ (S (qr' + 1) <? r) = false) by apply bool_dec.
      destruct H4 as [Hgt2 | Hngt2].
      { rewrite H2 in H1. rewrite Hgt2 in H1; simpl in *. 
        rewrite sub_n_o in *. 
        assert (qr' <? r = true) as Hgtr. apply gtb_true_S; auto.
        rewrite Hgtr in H1; simpl in *.
        rewrite plus_S in *.
        rewrite Hgt1 in H1. 
        assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
        destruct H4 as [Hgt3 | Hngt3].
        { rewrite Hgt3 in H1; simpl in *. 
          inversion H1. inversion H4.
          inversion H4. inversion H5. 
          inversion H5. inversion H6. inversion H6.
        }
        rewrite Hngt3 in H1; simpl in *.
        inversion H1. 
        inversion H4.
        inversion H4. inversion H5. inversion H5. 
      }
      rewrite Hngt2 in H1; simpl in *. 
      rewrite plus_S in *.   
      rewrite sub_n_o in *.
      assert (qr' <? r = true) as Hgtr. apply gtb_true_S; auto.
      rewrite Hgtr in H1. rewrite H2 in H1. simpl in *.
      rewrite Hgt1 in H1.
      assert ((1 <? c) = true \/ (1 <? c) = false) by apply bool_dec.
      destruct H4 as [Hgt3 | Hngt3].
      { rewrite Hgt3 in H1; simpl in *.
        inversion H1. 
        inversion H4.
        inversion H4. 
        inversion H5. inversion H5.
      }
      rewrite Hngt3 in H1; simpl in *.
      inversion H1. inversion H4. inversion H4. 
     - rewrite Hngt1 in H1; simpl in *. inversion H1. 
   * (*Case: p is at (0,>0) and q is at (>0, >0). should close by contradiction.*)
    simpl in *.
    assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
    assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
    rewrite H3 in *; simpl in *. 
    assert ((S qr' <? r) = true \/ (S qr' <? r) = false) by apply bool_dec.
    assert ((S qc' <? c) = true \/ (S qc' <? c) = false) by apply bool_dec.
    destruct H4 as [Hgtr1 | Hngtr1];  destruct H5 as [Hgtc1 | Hngtc1].
    - rewrite Hgtr1 in H1; rewrite Hgtc1 in H1; simpl in *.
      rewrite Hgtc1 in H1.       
      assert ((S (qr' + 1) <? r) = true \/ (S (qr' + 1) <? r) = false) by apply bool_dec.
      destruct H4 as [Hgtr2 | Hngtr2]. 
      { rewrite Hgtr2 in H1; simpl in *.
        do 2 rewrite sub_n_o in H1.
        assert (qr' <? r = true) as Hgtr. apply gtb_true_S; auto.
        rewrite Hgtr in H1; simpl in *.
        rewrite Hgtr1 in H1; simpl in *.
        assert (S (qc' + 1) <? c = true \/ S (qc' + 1) <? c = false) by apply bool_dec.
        destruct H4 as [Hgtc2 | Hngtc2].
        { rewrite Hgtc2 in H1.  
         assert (qc' <? c = true) as Hgtc. apply gtb_true_S; auto.
         rewrite Hgtc in H1.
         inversion H1. inversion H4. 
         inversion H4. 
         { inversion H5. 
           rewrite H7 in *.
           rewrite H8 in *.
           rewrite Hgtc1. simpl.
           rewrite Hgtr1. rewrite Hgtc1; simpl. 
           rewrite H3; rewrite Hgtc2; simpl. 
           rewrite sub_n_o.
           rewrite Hgtc; simpl. left; auto.
         }
         inversion H5. inversion H6. inversion H6. inversion H7. inversion H7.
        }
        rewrite Hngtc2 in H1; simpl in *. 
        assert (qc' <? c = true) as Hgtc. apply gtb_true_S; auto.
        rewrite Hgtc in H1.
        inversion H1.
        inversion H4. 
        inversion H4. inversion H5.
        { assert (S pc' <? c = true \/ S pc' <? c = false) by apply bool_dec.
          destruct H6 as [Hgtc3 | Hngtc3].
         { rewrite Hgtc3; simpl.
           rewrite H7 in *. rewrite H8 in *. 
           rewrite sub_n_o.
           rewrite Hgtr1; rewrite Hgtc3; simpl.  
           rewrite Hngtc2; rewrite H3; simpl in *.
           left; auto.
         }
         rewrite H7 in *; rewrite H8 in *; rewrite plus_S in *.
         rewrite Hgtc1 in Hngtc3. inversion Hngtc3. 
         }
         inversion H5. inversion H6. inversion H6. 
        } 
        rewrite Hngtr2 in H1; simpl in *.  
        do 2 rewrite sub_n_o in *. 
        assert (qr' <? r = true) as Hgtr. apply gtb_true_S; auto.
        rewrite Hgtr in H1; simpl in *.
        rewrite Hgtr1 in H1. 
        assert (S (qc' + 1) <? c = true \/ S (qc' + 1) <? c = false) by apply bool_dec.
        destruct H4 as [Hgtc3 | Hngtc3].
        { rewrite Hgtc3 in H1; simpl in *.
          assert (qc' <? c = true) as Hgtc. apply gtb_true_S; auto.
          rewrite Hgtc in H1; simpl in *.
          inversion H1.
          { inversion H4.
            rewrite H6 in *. rewrite H7 in *; simpl in *. 
            rewrite Hgtc1.
            simpl. 
            rewrite Hgtr1; rewrite Hgtc1; simpl.
            left; auto. 
          }
          inversion H4. inversion H5. inversion H5. inversion H6. 
          inversion H6. 
         } 
         rewrite Hngtc3 in H1; simpl in *.   
         assert (qc' <? c = true) as Hgtc. apply gtb_true_S; auto.
         rewrite Hgtc in H1; simpl in *.
         inversion H1.
         { inversion H4.
           rewrite H6 in *. rewrite H7 in *.
           rewrite plus_S in *.
           rewrite Hgtc1. 
           simpl. 
           rewrite Hgtr1. rewrite Hgtc1; simpl.
           left; auto. 
         }
         inversion H4. inversion H5. inversion H5.
      - rewrite Hgtr1 in H1.  rewrite Hngtc1 in H1; simpl in *.
        inversion H1. 
      - rewrite Hgtc1 in H1; rewrite Hngtr1 in H1; simpl in *. 
        inversion H1. 
      - rewrite Hngtr1 in H1; simpl in *. inversion H1.
+ (*Case 5: p = (>0,pc), q = (qr,qc)*)  
  destruct pc as [ | pc']; destruct qr as [ | qr']; destruct qc as [ | qc'].
  * (*sub-case 0: p is (>0, 0), q is (0,0)*)
   simpl in *. 
   assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
   assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
   rewrite H2 in *; rewrite H3 in H1; simpl in *.
   rewrite H2 in H1; rewrite plus_S in *; simpl in *.
   rewrite sub_n_o.   
   rewrite H3 in H1; simpl in *. 
   assert (1 <? c = true \/ 1 <? c = false) by apply bool_dec.
   destruct H4 as [Hgtc | Hngtc]. 
   - rewrite Hgtc in H1; simpl in *.
     assert (1 <? r = true \/ 1 <? r = false) by apply bool_dec.
     destruct H4 as [Hgtr | Hngtr].
     { rewrite Hgtr in H1; simpl in *. 
       inversion H1. inversion H4. 
       rewrite Hgtr; simpl.
       rewrite H2.  
       assert (2 <? r = true \/ 2 <? r = false) by apply bool_dec.
       destruct H5 as [Hgtr' | Hngtr'].
       { rewrite Hgtr'; simpl. rewrite H3; simpl. 
       right. left; auto. 
       }  
       rewrite Hngtr'; simpl. rewrite H3; simpl. 
       left; auto. 
       inversion H4. inversion H5. inversion H5. 
     }
     rewrite Hngtr in H1; simpl in *.
     inversion H1. inversion H4. inversion H4.
   - 
    rewrite Hngtc in H1; simpl in *.
    assert (1 <? r = true \/ 1 <? r = false) by apply bool_dec.
    destruct H4 as [Hgtr | Hngtr]. 
    { rewrite Hgtr in H1; simpl in *. 
      inversion H1. inversion H4. 
      rewrite <- H6 in *.
      { rewrite Hgtr; simpl. 
        assert (2 <? r = true \/ 2 <? r = false) by apply bool_dec.
        destruct H5 as [Hgtr' | Hngtr'].
        { rewrite Hgtr'; rewrite H2; simpl. 
          rewrite H3; simpl. right. left; auto. 
        }
        rewrite Hngtr'; simpl. 
        rewrite H3; rewrite H2; simpl. 
        left; auto. 
      }
      inversion H4. 
    }
    rewrite Hngtr in H1; simpl in *. inversion H1. 
  * (*sub-case 0: p is (>0, 0), q is (0,>0)*)
   simpl in *. 
   assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
   assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
   rewrite H3 in H1; simpl in *.
   rewrite H2; rewrite plus_S in *; simpl in *.
   rewrite sub_n_o in *.   
   assert (S qc' <? c = true \/ S qc' <? c = false) by apply bool_dec.
   destruct H4 as [Hgtc | Hngtc].
   { rewrite Hgtc in H1. 
     simpl in *.
     rewrite Hgtc in H1.  
     assert (1 <? r = true \/ 1 <? r = false) by apply bool_dec.
     destruct H4 as [Hgtr | Hngtr].
     { rewrite Hgtr in H1; simpl in *.
       rewrite H3 in H1.  
       assert (S (S qc') <? c = true \/ S (S qc') <? c = false) by apply bool_dec.
       destruct H4 as [Hgtc1 | Hngtc1].
       { rewrite Hgtc1 in H1; simpl in *.
         assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
         rewrite Hgtc2 in H1; simpl in *.
         inversion H1. 
         inversion H4.
         inversion H4. inversion H5. inversion H5. inversion H6. inversion H6. 
       }
       rewrite Hngtc1 in H1; simpl in *.
       assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
       rewrite Hgtc2 in H1; simpl in *.
       inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
      }
      rewrite Hngtr in H1; simpl in *.
      rewrite H3 in H1.    
      assert (S (S qc') <? c = true \/ S (S qc') <? c = false) by apply bool_dec.
      destruct H4 as [Hgtc1 | Hngtc1].
      { rewrite Hgtc1 in H1; simpl in *.
        assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
        rewrite Hgtc2 in H1; simpl in *.
        inversion H1. inversion H4. inversion H4. inversion H5. inversion H5. 
      } 
      rewrite Hngtc1 in H1; simpl in *. 
      assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
      rewrite Hgtc2 in H1; simpl in *.
      inversion H1. inversion H4. inversion H4. 
     }
     rewrite Hngtc in H1; simpl in *. inversion H1. 
   * simpl in *. 
     assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
     assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
     rewrite H2 in H1; simpl in *.
     rewrite H2; rewrite plus_S in *; simpl in *.
     rewrite sub_n_o in *.   
     assert (S qr' <? r = true \/ S qr' <? r = false) by apply bool_dec.
     destruct H4 as [Hgtr | Hngtr].
     { rewrite Hgtr in H1; simpl in *.
       rewrite H2 in H1.  
       assert (S (S qr') <? r = true \/ S (S qr') <? r = false) by apply bool_dec.
       destruct H4 as [Hgtr1 | Hngtr1].
       { rewrite Hgtr1 in H1; simpl in *.
         assert (qr' <? r = true) as Hgtr2. apply gtb_true_S; auto.
         rewrite Hgtr2 in H1; simpl in *.
         rewrite Hgtr in H1. 
         assert (1 <? c = true \/ 1 <? c = false) by apply bool_dec.
         destruct H4 as [Hgtc | Hngtc].
         { rewrite Hgtc in H1; simpl in *.
           inversion H1. inversion H4. 
           rewrite <- H6 in *.
           rewrite Hgtr1; simpl.  
           assert ((S (S (S qr')) <? r) = true \/ (S (S (S qr')) <? r) = false) by apply bool_dec.
           { destruct H5 as [Hgtr3 | Hngtr3].
             { rewrite Hgtr3; rewrite H2; simpl. 
               rewrite Hgtr; simpl. right. left; auto. 
             }
             rewrite Hngtr3; simpl. 
             rewrite Hgtr; rewrite H2; simpl. 
             left; auto. 
            }
            inversion H4.
            { inversion H5.
              rewrite H7 in Hgtr2. 
              rewrite Hgtr2; simpl. 
              rewrite H7 in Hgtr. 
              rewrite Hgtr; rewrite H2; simpl.
              left; auto.
            }
           inversion H5. inversion H6. inversion H6. 
          }
          rewrite Hngtc in H1; simpl in *. 
          inversion H1.
          { inversion H4.
            rewrite Hgtr1; simpl. 
            assert ((S (S (S qr')) <? r) = true \/ (S (S (S qr')) <? r) = false) by apply bool_dec.
            { destruct H5 as [Hgtr3 | Hngtr3].
              { rewrite Hgtr3; rewrite H2; simpl. 
                rewrite Hgtr; simpl. 
                rewrite Hngtc; rewrite Hgtr1; simpl.
                right. left; auto. 
              }   
              rewrite Hngtr3; simpl. 
              rewrite Hgtr; rewrite H2; simpl. 
              left; auto. 
             }
           }
          inversion H4. 
          inversion H5. 
          rewrite H7 in *. rewrite Hgtr2; simpl. 
          rewrite Hgtr; rewrite H2; simpl. 
          assert (pr' <? r = true) as Hgtr3. apply gtb_true_S; auto.
          rewrite Hgtr3; simpl in *. left; auto. 
          inversion H5. 
          }
          rewrite Hngtr1 in H1; simpl in *. 
          assert (qr' <? r = true) as Hgtr1. apply gtb_true_S; auto.
          rewrite Hgtr1 in H1; simpl in *.
          inversion H1.
          { inversion H4.
            rewrite H6 in *.
            rewrite Hgtr1; simpl. 
            rewrite Hgtr; rewrite H2; simpl.
            assert (pr' <? r = true) as Hgtr3. apply gtb_true_S; auto.
            rewrite Hgtr3; simpl in *. left; auto. 
          }
          rewrite Hgtr in H4; simpl in *. 
          assert (1 <? c = true \/ 1 <? c = false) by apply bool_dec.
          destruct H5 as [Hgtc | Hngtc].
          { rewrite Hgtc in H4; simpl in *. 
            inversion H4. inversion H5. inversion H5. 
          }
          rewrite Hngtc in H4. inversion H4. 
         }
        rewrite Hngtr in H1; simpl in *. inversion H1.  
        * simpl in *. 
         assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
         rewrite H2; simpl in *.
         rewrite plus_S in *. rewrite sub_n_o in *; simpl in *.
         assert (S qr' <? r = true \/ S qr' <? r = false) by apply bool_dec.
         assert (S qc' <? c = true \/ S qc' <? c = false) by apply bool_dec.
         destruct H3 as [Hgtr | Hngtr]; destruct H4 as [Hgtc | Hngtc].
         - rewrite Hgtr in H1; rewrite Hgtc in H1; simpl in *. 
          rewrite Hgtc in H1; simpl in *. 
          assert ((S (S qr') <? r) = true \/ (S (S qr') <? r) = false) by apply bool_dec.
          destruct H3 as [Hgtr1 | Hngtr1].
          { rewrite Hgtr1 in H1; simpl in *. 
           assert (qr' <? r = true) as Hgtr2. apply gtb_true_S; auto.
           rewrite Hgtr2 in H1; simpl in *.
           rewrite plus_S in *. rewrite sub_n_o in *; simpl in *.
           assert ((S (S qc') <? c) = true \/ (S (S qc') <? c) = false) by apply bool_dec.
           destruct H3 as [Hgtc1 | Hngtc1].
           { rewrite Hgtr in H1; rewrite Hgtc1 in H1; simpl in *. 
             assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
             rewrite Hgtc2 in H1; simpl in *.
             inversion H1. inversion H3. 
             inversion H3. inversion H4. 
             inversion H4. inversion H5. 
             inversion H5. inversion H6. 
             rewrite H9 in *; rewrite H8 in *; simpl in *.
             rewrite Hgtr; simpl. 
             rewrite H2; rewrite Hgtr1; simpl. 
             rewrite Hgtr2; simpl. 
             right. right. 
             rewrite Hgtr; simpl. 
             rewrite Hgtc; simpl. 
             left; auto. 
             inversion H6. 
            }
           rewrite Hngtc1 in H1; rewrite Hgtr in H1; simpl in *.
           assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
           rewrite Hgtc2 in H1; simpl in *.
           inversion H1. inversion H3. 
           inversion H3. inversion H4. 
           inversion H4. inversion H5.
           rewrite H8 in *; rewrite H7 in *; simpl in *. 
           rewrite Hgtr; simpl. 
           rewrite Hgtr1; rewrite H2; simpl. 
           rewrite Hgtr2; simpl.   
           right. right. 
           rewrite Hgtr; simpl. 
           rewrite Hgtc. simpl; left; auto. 
           inversion H5. 
           }
           rewrite Hngtr1 in H1; simpl in *.  
           assert (qr' <? r = true) as Hgtr1. apply gtb_true_S; auto.
           rewrite Hgtr1 in H1; simpl in *.
           rewrite plus_S in *. rewrite sub_n_o in *; simpl in *.
           rewrite Hgtr in H1. 
           assert ((S (S qc') <? c) = true \/ (S (S qc') <? c) = false) by apply bool_dec.
           destruct H3 as [Hgtc1 | Hngtc1].
           { 
            rewrite Hgtc1 in H1; simpl in *. 
            assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
            rewrite Hgtc2 in H1; simpl in *.
            { inversion H1. inversion H3. 
              inversion H3. inversion H4. 
              inversion H4. inversion H5. 
              { rewrite H8 in *; rewrite H7 in *; simpl in *.
                rewrite Hgtr; simpl. 
                rewrite H2; rewrite Hngtr1; simpl. 
                rewrite Hgtr1; simpl. 
                right.
                rewrite Hgtc; rewrite Hgtr; simpl. left; auto. 
               }
              inversion H5. 
             }
           }
          rewrite Hngtc1 in H1; simpl in *. 
          inversion H1. inversion H3. 
          assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
          rewrite Hgtc2 in H3; simpl in *.
          inversion H3. inversion H4. 
          { rewrite H6 in *; rewrite H7 in *; simpl in *. 
            rewrite Hgtr; simpl. 
            rewrite H2; rewrite Hngtr1; simpl. 
            rewrite Hgtr1; simpl. 
            right. 
            rewrite Hgtr; rewrite Hgtc; simpl. 
            left; auto. 
          }
          inversion H4. 
         - rewrite Hngtc in H1; rewrite Hgtr in H1; simpl in *.
           inversion H1. 
         - rewrite Hngtr in H1; rewrite Hgtc in H1; simpl in *. 
           inversion H1. 
         - rewrite Hngtr in H1; rewrite Hngtc in H1; simpl in *. 
           inversion H1. 
        * simpl in *. 
          assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
          assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
          rewrite H2 in H1; rewrite H3 in H1; simpl in *.
          rewrite plus_S in *. rewrite sub_n_o in *; simpl in *.
          rewrite H2 in *.  
          assert (1 <? r = true \/ 1 <? r = false) by apply bool_dec. 
          destruct H4 as [Hgtr | Hngtr].
          { rewrite Hgtr in H1; simpl in *.
            rewrite H3 in H1. 
            assert (1 <? c = true \/ 1 <? c = false) by apply bool_dec. 
            destruct H4 as [Hgtc | Hngtc].
            { rewrite Hgtc in H1; simpl in *.
              inversion H1. inversion H4. inversion H4. 
              inversion H5. inversion H5. 
            }
            rewrite Hngtc in H1; simpl in *. 
            inversion H1. inversion H4. inversion H4. 
          }
          rewrite Hngtr in H1; simpl in *. 
          assert (1 <? c = true \/ 1 <? c = false) by apply bool_dec. 
          destruct H4 as [Hgtc | Hngtc].
          { rewrite Hgtc in H1; rewrite H3 in *; simpl in *.
            inversion H1. inversion H4. inversion H4. 
          }
          rewrite H3 in H1; rewrite Hngtc in H1; simpl in *.
          inversion H1. 
        * simpl in *. 
          assert ( 0 <? r = true). apply Nat.ltb_lt; auto.
          rewrite H2 in H1.
          assert (S qc' <? c = true \/ S qc' <? c = false) by apply bool_dec.
          destruct H3 as [Hgtc | Hngtc]. 
          { rewrite Hgtc in H1; simpl in *. 
            assert ( 1 <? r = true \/ 1 <? r = false) by apply bool_dec.
            assert (S qc' <? c = true \/ S qc' <? c = false) by apply bool_dec.
            destruct H3 as [Hgtr | Hngtr]; destruct H4 as [Hgtc1 | Hngtc1].
            { rewrite Hgtr in H1; rewrite Hgtc1 in H1; simpl in *.
              rewrite plus_S in *. rewrite sub_n_o in *; simpl in *.
              rewrite H2 in H1.
              assert (S (S qc') <? c = true \/ S (S qc') <? c = false) by apply bool_dec.
              destruct H3 as [Hgtc2 | Hngtc2].
              { rewrite Hgtc2 in H1; simpl in *.
                assert (qc' <? c = true) as Hgtc3. apply gtb_true_S; auto.
                rewrite Hgtc3 in H1; simpl in *.
                inversion H1. 
                { inversion H3.
                  rewrite H6 in *; rewrite H5 in *; simpl in *.
                  rewrite Hgtr; rewrite Hgtc; simpl. 
                  rewrite Hgtc.  
                  assert (S (S pr') <? r = true \/ S (S pr') <? r = false) by apply bool_dec.
                  destruct H4 as [Hgtr1 | Hngtr1].
                  { rewrite Hgtr1; simpl in *.
                    rewrite H2; simpl. 
                    right. left.  auto.
                  }
                  rewrite Hngtr1; simpl.
                  rewrite H2; simpl. left; auto.
                 }
                inversion H3. inversion H4. inversion H4. inversion H5.
                inversion H5.
               }
               rewrite Hngtc2 in H1; simpl in *.
               assert (qc' <? c = true) as Hgtc3. apply gtb_true_S; auto.
               rewrite Hgtc3 in H1; simpl in *.
               inversion H1. inversion H3.
               { rewrite H6 in *; rewrite <- H5 in *.
                 rewrite plus_S in *; rewrite sub_n_o in *; simpl in *.
                 rewrite Hgtr; rewrite Hgtc; simpl.
                 assert ( 2 <? r = true \/ 2 <? r = false) by apply bool_dec.
                 destruct H4 as [Hgtr1 | Hngtr1].
                 { rewrite Hgtr1; rewrite Hgtc1; simpl.
                   rewrite H2; simpl. right.
                   left; auto.
                 }
                 rewrite Hngtr1; simpl.
                 rewrite H2; rewrite Hgtc; simpl. left; auto.
               }
               inversion H3. inversion H4. inversion H4.
              }
              rewrite Hgtr in H1; rewrite Hngtc1 in H1; simpl in *.
              rewrite plus_S in *; rewrite sub_n_o in *; simpl in *.
              rewrite H2 in H1. 
              assert (S (S qc') <? c = true \/ S (S qc') <? c = false) by apply bool_dec.
              destruct H3 as [Hgtc2 | Hngtc2]. 
              { rewrite Hgtc2 in H1; simpl in *.
                assert (qc' <? c = true) as Hgtc3. apply gtb_true_S; auto.
                rewrite Hgtc3 in H1; simpl in *.
                inversion H1. inversion H3. inversion H3.
                inversion H4. inversion H4.
               }
               rewrite Hngtc2 in H1; simpl in *.
               assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
               rewrite Hgtc2 in H1; simpl in *.
               inversion H1. inversion H3. inversion H3.
              - rewrite Hgtc in H1; rewrite Hngtr in H1; simpl in *.
                rewrite H2 in H1. 
                rewrite plus_S in *; rewrite sub_n_o in *; simpl in *.
                assert (S (S qc') <? c = true \/ S (S qc') <? c = false) by apply bool_dec.
                destruct H3 as [Hgtc2 | Hngtc2].
                { rewrite Hgtc2 in H1.
                  assert (qc' <? c = true) as Hgtc3. apply gtb_true_S; auto.
                  rewrite Hgtc3 in H1; simpl in *.
                  inversion H1. inversion H3. inversion H3.
                  inversion H4. inversion H4.
                }
                rewrite Hngtc2 in H1. 
                assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
                rewrite Hgtc2 in H1; simpl in *.
                inversion H1. inversion H3. inversion H3.
               - rewrite Hngtr in H1; rewrite Hngtc1 in H1; simpl in *.
                 rewrite plus_S in *; rewrite sub_n_o in *; simpl in *.
                 assert (S (S qc') <? c = true \/ S (S qc') <? c = false) by apply bool_dec.
                 destruct H3 as [Hgtc2 | Hngtc2].
                 rewrite H2 in H1; rewrite Hgtc2 in H1; simpl in *. 
                 assert (qc' <? c = true) as Hgtc3. apply gtb_true_S; auto.
                 rewrite Hgtc3 in H1; simpl in *.
                 inversion H1. inversion H3. inversion H3. inversion H4.
                 inversion H4.
                 rewrite H2 in H1; rewrite Hngtc2 in H1; simpl in *.
                 assert (qc' <? c = true) as Hgtc3. apply gtb_true_S; auto.
                 rewrite Hgtc3 in H1; simpl in *.
                 inversion H1. inversion H3. inversion H3.
             }
           rewrite Hngtc in H1; simpl in *.
           inversion H1. 
     * simpl in *.
       assert ( 0 <? c = true). apply Nat.ltb_lt; auto.
       rewrite H2 in H1.
       assert (S qr' <? r = true \/ S qr' <? r = false) by apply bool_dec.
       destruct H3 as [Hgtr | Hngtr].
       { rewrite Hgtr in H1; simpl in *.
         rewrite H2 in H1.
         rewrite plus_S in *; rewrite sub_n_o in *; simpl in *.
         assert (S (S qr') <? r = true \/ S (S qr') <? r = false) by apply bool_dec.
         destruct H3 as [Hgtr1 | Hngtr1].
         { rewrite Hgtr1 in H1; simpl in *.
           assert (qr' <? r = true) as Hgtr2. apply gtb_true_S; auto.
           rewrite Hgtr2 in H1; simpl in *.
           rewrite Hgtr in H1.
           assert ( 1 <? c = true \/ 1 <? c = false) by apply bool_dec.
           destruct H3 as [Hgtc | Hngtc].
           { rewrite Hgtc in H1; simpl in *.
             inversion H1. 
             inversion H3.
             inversion H3. inversion H4.
             inversion H4. inversion H5.
             { rewrite <- H8 in *; rewrite H7 in *; simpl in *.
               rewrite Hgtr; rewrite Hgtc; simpl.
               rewrite Hgtr1; rewrite Hgtc; simpl.
               right.
               rewrite Hgtr2; simpl. 
               right.
               rewrite Hgtr. 
               assert ( 2 <? c = true \/ 2 <? c = false) by apply bool_dec.
               destruct H6 as [Hgtc1 | Hngtc1].
               { rewrite Hgtc1; simpl. 
                 right. 
                 rewrite H2. simpl; left; auto.
               }
               rewrite Hngtc1; simpl. 
               rewrite H2. 
               simpl; left; auto.
              }
             inversion H5.
           }
           rewrite Hngtc in H1; simpl in *.
           inversion H1. inversion H3. 
           inversion H3. inversion H4. inversion H4.
          }
          rewrite Hgtr in H1; rewrite Hngtr1 in H1; simpl in *.
          assert (qr' <? r = true) as Hgtr2. apply gtb_true_S; auto.
          rewrite Hgtr2 in H1; simpl in *.
          assert ( 1 <? c = true \/ 1 <? c = false) by apply bool_dec.
          destruct H3 as [Hgtc1 | Hngtc1].
          { rewrite Hgtc1 in H1; simpl.
            inversion H1. inversion H3.
            inversion H3. inversion H4. 
            { rewrite <- H7 in *; rewrite H6 in *; simpl in *.
              rewrite Hgtr; rewrite Hgtc1; simpl.
              rewrite Hngtr1; rewrite Hgtc1; simpl.
              rewrite Hgtr2; simpl. 
              right.
              rewrite Hgtr. 
              assert ( 2 <? c = true \/ 2 <? c = false) by apply bool_dec.
              destruct H5 as [Hgtc2 | Hngtc2].
              { rewrite Hgtc2; simpl. 
                right. 
                rewrite H2.
                simpl; left; auto.
              }
              rewrite Hngtc2; simpl. 
              rewrite H2.
              simpl; left; auto.
            }
            inversion H4.
           }
           rewrite Hngtc1 in H1.
           inversion H1. inversion H3. inversion H3.
          }
         rewrite Hngtr in H1; simpl in *.
         inversion H1.
       * simpl in *.
         assert (S qr' <? r = true \/ S qr' <? r = false) by apply bool_dec.
         assert (S qc' <? c = true \/ S qc' <? c = false) by apply bool_dec.
         destruct H2 as [Hgtr | Hngtr]; destruct H3 as [Hgtc | Hngtc].
         - rewrite Hgtr in H1; rewrite Hgtc in H1; simpl in *.
           rewrite plus_S in *; rewrite sub_n_o in *; simpl in *.
           rewrite Hgtc in H1.
           assert (S (S qr') <? r = true \/ S (S qr') <? r = false) by apply bool_dec.
           destruct H2 as [Hgtr1 | Hngtr1].
           { rewrite Hgtr1 in H1; simpl in *.
             assert (qr' <? r = true) as Hgtr2. apply gtb_true_S; auto.
             rewrite Hgtr2 in H1; simpl in *.
             rewrite plus_S in *; rewrite sub_n_o in *; simpl in *.
             rewrite Hgtr in H1.
             assert (S (S qc') <? c = true \/ S (S qc') <? c = false) by apply bool_dec.
             destruct H2 as [Hgtc1 | Hngtc1].
             { rewrite Hgtc1 in H1; simpl in *.
               assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
               rewrite Hgtc2 in H1; simpl in *.
               inversion H1.
               inversion H2.
               { rewrite H5 in *; rewrite <- H4 in *; simpl in *.
                 rewrite Hgtc; rewrite Hgtr1; simpl. 
                 rewrite Hgtc.
                 assert (S (S (S qr')) <? r = true \/ S (S (S qr')) <? r = false) by apply bool_dec.
                 destruct H3 as [Hgtr3 | Hngtr3].
                 { rewrite Hgtr3; simpl. 
                   right.
                   rewrite Hgtr; simpl.  
                   left; auto.
                 }
                 rewrite Hngtr3; simpl.
                 rewrite Hgtr; simpl. left; auto.
               }
               inversion H2. 
               { inversion H3.
                 rewrite H6 in *; rewrite H5 in *; simpl in *.
                 rewrite Hgtc; rewrite Hgtr2; simpl.  
                 rewrite Hgtc; rewrite Hgtr; simpl. 
                 left; auto.
               }
               inversion H3.
               inversion H4.
               rewrite <- H7 in *; rewrite H6 in *; simpl in *.
               rewrite Hgtr; rewrite Hgtc1; simpl. 
               rewrite Hgtr1; rewrite Hgtc1; simpl. 
               rewrite Hgtr2; simpl. 
               right. right.
               rewrite Hgtr.
               assert (S (S (S qc')) <? c = true \/ S (S (S qc')) <? c = false) by apply bool_dec.
               destruct H5 as [Hgtc3 | Hngtc3].
               { rewrite Hgtc3; simpl.
                 right. 
                 rewrite Hgtc.
                 simpl; left; auto.
               }
               rewrite Hngtc3; simpl. 
               rewrite Hgtc.
               simpl; left; auto.
               inversion H4. inversion H5.
               { rewrite H8 in *; rewrite H7 in *; simpl in *.
                 rewrite Hgtr; rewrite Hgtc2; simpl. 
                 rewrite Hgtr1; rewrite Hgtc2; simpl. 
                 right.
                 rewrite Hgtr2; simpl. 
                 right.
                 rewrite Hgtr; rewrite Hgtc; simpl. 
                 left; auto.
                }
                inversion H5. 
              }
             rewrite Hngtc1 in H1; simpl in *.
             assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
             rewrite Hgtc2 in H1; simpl in *.
             inversion H1.
             inversion H2. 
             { rewrite H5 in *; rewrite <- H4 in *; simpl in *.
               rewrite Hgtr1; rewrite Hgtc; simpl. 
               assert (S (S (S qr')) <? r = true \/ S (S (S qr')) <? r = false) by apply bool_dec.
               destruct H3 as [Hgtr3 | Hngtr3].
               { rewrite Hgtr3; rewrite Hgtc; simpl. 
                 right. 
                 rewrite Hgtr; simpl. 
                 left; auto. 
               }
               rewrite Hngtr3; simpl. 
               rewrite Hgtr; rewrite Hgtc; simpl. 
               left; auto.
              }
              inversion H2. 
              inversion H3. 
              { rewrite H6 in *; rewrite H5 in *; simpl in *. 
                rewrite Hgtr2; rewrite Hgtc; simpl.
                rewrite Hgtr; rewrite Hgtc; simpl. 
                left; auto.
              }
              inversion H3. inversion H4.
              rewrite H7 in *; rewrite H6 in *; simpl in *.
              rewrite Hgtr; rewrite Hgtc2; simpl. 
              rewrite Hgtr1; rewrite Hgtc2; simpl. 
              right. 
              rewrite Hgtr2; simpl. 
              right. 
              rewrite Hgtr; rewrite Hgtc; simpl. 
              left; auto.
              inversion H4.
            }
            rewrite Hngtr1 in H1; simpl in *.
            assert (qr' <? r = true) as Hgtr1. apply gtb_true_S; auto.
            rewrite Hgtr1 in H1; simpl in *.
            rewrite plus_S in *; rewrite sub_n_o in *; simpl in *.
            rewrite Hgtr in H1. 
            assert (S (S qc') <? c = true \/ S (S qc') <? c = false) by apply bool_dec.
            destruct H2 as [Hgtc1 | Hngtc1].
            { rewrite Hgtc1 in H1; simpl in *.
              assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
              rewrite Hgtc2 in H1; simpl in *.
              inversion H1.
              inversion H2.
              { rewrite H5 in *; rewrite H4 in *; simpl in *.
                rewrite Hgtr1; rewrite Hgtc; simpl in *.
                rewrite Hgtr; rewrite Hgtc;  simpl. 
                left; auto.
              }
              inversion H2. 
              inversion H3.
              { rewrite <- H6 in *; rewrite H5 in *; simpl in *.
                rewrite Hgtr; rewrite Hgtc1; simpl. 
                rewrite Hngtr1; rewrite Hgtc1; simpl. 
                rewrite Hgtr1; simpl. 
                right. 
                assert (S (S (S qc')) <? c = true \/ S (S (S qc')) <? c = false) by apply bool_dec.
                destruct H4 as [Hgtr2 | Hngtr2].
                { rewrite Hgtr2; rewrite Hgtr; simpl.
                  right.
                  rewrite Hgtc. simpl; left; auto.
                }
                rewrite Hngtr2; rewrite Hgtr; simpl.
                rewrite Hgtc; simpl. 
                left; auto.
               }
               inversion H3. inversion H4.
               { rewrite H7 in *; rewrite H6 in *; simpl in *.
                 rewrite Hgtr; rewrite Hgtc2; simpl. 
                 rewrite Hngtr1; rewrite Hgtc2; simpl. 
                 rewrite Hgtr1; simpl. right. 
                 rewrite Hgtr; rewrite Hgtc; simpl. 
                 left; auto. 
                }
               inversion H4. 
              }
              rewrite Hngtc1 in H1; simpl in *.
              assert (qc' <? c = true) as Hgtc2. apply gtb_true_S; auto.
              rewrite Hgtc2 in H1; simpl in *.
              inversion H1. inversion H2.
              { rewrite H5 in *; rewrite H4 in *; simpl in *.
                rewrite Hgtr1; rewrite Hgtc; simpl. 
                rewrite Hgtr; rewrite Hgtc; simpl. 
                left; auto. 
               }
              inversion H2. 
              inversion H3. 
              rewrite H6 in *; rewrite H5 in *; simpl in *. 
              rewrite Hgtr; rewrite Hgtc2; simpl. 
              rewrite Hngtr1; rewrite Hgtc2; simpl. 
              rewrite Hgtr1; simpl. right.
              rewrite Hgtr; rewrite Hgtc; simpl. 
              left; auto.
              inversion H3. 
            - rewrite Hngtc in H1; rewrite Hgtr in H1; simpl in *. 
              inversion H1. 
            - rewrite Hgtc in H1; rewrite Hngtr in H1; simpl in *.
              inversion H1. 
            - rewrite Hngtc in H1; rewrite Hngtr in H1; simpl in *.
              inversion H1. 
Qed.

(*the path relation is commutative. if p has path to q then q has a path to p*)
Lemma path_4_comm: forall p q (img: list pixel), 
    path_4 p q img -> path_4 q p img.
Proof.
 intros.
 induction H as [?p ?img | ?r ?c ?pr ?pc ?qr ?qc ?p ?q ?img Hr Hc Hp Hq Hn | ?p ?q ?r ?img ?Hpr ? ?Hrq].
 + apply path_4_self.
 + apply path_4_neigh with (r:= r) (c:= c) (pr:= pr) (pc:= pc) (qr:=qr) (qc:=qc); auto. 
   apply neighbouts4_comm with (pr:= pr) (pc:= pc) (qr:=qr) (qc:=qc); auto. 
 + apply path_4_trans with (q:= q); auto.
Qed. 

(**************************************************************)
(*********** Proof of Equivalence of Connectivity *************)
(**************************************************************)

(*any pixel p is connected with itself.*)
Lemma connected_4_refl: forall p img, connected_4 p p img.
Proof. 
 intros.
 apply Connected_4.
 apply path_4_self.
Qed.

(*if p is connected to q, then q is connected p as well*)
Lemma connected_4_comm: forall p q img, connected_4 p q img -> connected_4 q p img.
Proof. 
 intros. 
 induction H. 
 apply Connected_4.
 apply path_4_comm; auto.
Qed.

(*if p is connected to q and q is connected to r, then 
  p is connected to r as well*)
Lemma connected_4_assoc: forall p q r img, 
      connected_4 p q img -> connected_4 q r img -> connected_4 p r img. 
Proof. 
 intros. 
 induction H.
 induction H0 as [q r].
 apply Connected_4.
 apply path_4_trans with (q:= q); auto.
Qed. 

(***************************************************************)
 