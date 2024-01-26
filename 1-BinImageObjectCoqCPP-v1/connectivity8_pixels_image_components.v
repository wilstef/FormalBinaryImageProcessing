Require Import pixel_connectivity_8_equiv. 

(*Tool generated grayscale image matrix*)
Definition coqmatriximg := 
[255;252;255;255;0;3;0;1;254;255;253;255;255;251;255;255;255;251;254;255;
255;255;0;0;2;0;5;0;0;0;255;252;255;255;250;255;254;255;253;253;
252;255;0;1;2;0;0;0;5;0;255;255;254;255;250;255;255;253;255;255;
255;0;4;0;1;0;0;4;0;0;0;255;254;255;255;254;254;254;255;255;
255;3;0;2;0;0;4;0;4;0;5;253;254;255;255;254;255;255;254;253;
255;0;1;0;0;0;0;4;0;3;0;255;0;0;0;0;0;0;255;255;
255;255;0;1;0;4;5;0;3;0;255;252;0;4;3;0;4;0;253;254;
254;254;0;1;0;1;0;2;0;1;255;255;1;0;0;2;0;0;255;254;
255;253;255;255;0;2;0;3;255;254;255;255;2;0;1;2;0;0;255;254;
254;255;255;255;255;255;255;253;252;255;255;252;0;2;1;0;4;0;253;254;
255;249;255;252;255;250;255;255;255;255;250;255;8;0;2;0;0;0;255;255;
253;255;255;255;254;255;255;254;254;253;255;253;249;254;252;255;255;255;254;253;
255;255;255;0;1;0;252;255;255;255;255;254;255;255;255;253;254;254;255;255;
255;254;1;0;0;4;2;255;254;255;255;255;255;255;255;252;255;253;255;255;
255;254;1;0;0;2;0;0;255;255;251;255;252;255;254;255;254;255;252;253;
255;254;0;1;0;0;4;1;0;255;255;252;255;255;253;255;255;250;254;255;
254;255;1;2;0;0;3;0;1;255;254;253;254;255;255;255;255;255;255;255;
253;253;0;1;3;0;0;1;0;253;255;255;255;252;255;253;255;255;255;255;
255;255;255;1;0;3;0;0;255;255;255;252;255;255;252;255;255;255;255;255;
255;254;252;255;255;255;254;255;255;255;254;255;253;254;251;255;255;255;255;255].

(*Tool generated Coq definition of grayscale image*)
Definition coqgsimage := 
[G{0,0,255};G{0,1,252};G{0,2,255};G{0,3,255};G{0,4,0};G{0,5,3};G{0,6,0};G{0,7,1};G{0,8,254};G{0,9,255};G{0,10,253};G{0,11,255};G{0,12,255};G{0,13,251};G{0,14,255};G{0,15,255};G{0,16,255};G{0,17,251};G{0,18,254};G{0,19,255};
G{1,0,255};G{1,1,255};G{1,2,0};G{1,3,0};G{1,4,2};G{1,5,0};G{1,6,5};G{1,7,0};G{1,8,0};G{1,9,0};G{1,10,255};G{1,11,252};G{1,12,255};G{1,13,255};G{1,14,250};G{1,15,255};G{1,16,254};G{1,17,255};G{1,18,253};G{1,19,253};
G{2,0,252};G{2,1,255};G{2,2,0};G{2,3,1};G{2,4,2};G{2,5,0};G{2,6,0};G{2,7,0};G{2,8,5};G{2,9,0};G{2,10,255};G{2,11,255};G{2,12,254};G{2,13,255};G{2,14,250};G{2,15,255};G{2,16,255};G{2,17,253};G{2,18,255};G{2,19,255};
G{3,0,255};G{3,1,0};G{3,2,4};G{3,3,0};G{3,4,1};G{3,5,0};G{3,6,0};G{3,7,4};G{3,8,0};G{3,9,0};G{3,10,0};G{3,11,255};G{3,12,254};G{3,13,255};G{3,14,255};G{3,15,254};G{3,16,254};G{3,17,254};G{3,18,255};G{3,19,255};
G{4,0,255};G{4,1,3};G{4,2,0};G{4,3,2};G{4,4,0};G{4,5,0};G{4,6,4};G{4,7,0};G{4,8,4};G{4,9,0};G{4,10,5};G{4,11,253};G{4,12,254};G{4,13,255};G{4,14,255};G{4,15,254};G{4,16,255};G{4,17,255};G{4,18,254};G{4,19,253};
G{5,0,255};G{5,1,0};G{5,2,1};G{5,3,0};G{5,4,0};G{5,5,0};G{5,6,0};G{5,7,4};G{5,8,0};G{5,9,3};G{5,10,0};G{5,11,255};G{5,12,0};G{5,13,0};G{5,14,0};G{5,15,0};G{5,16,0};G{5,17,0};G{5,18,255};G{5,19,255};
G{6,0,255};G{6,1,255};G{6,2,0};G{6,3,1};G{6,4,0};G{6,5,4};G{6,6,5};G{6,7,0};G{6,8,3};G{6,9,0};G{6,10,255};G{6,11,252};G{6,12,0};G{6,13,4};G{6,14,3};G{6,15,0};G{6,16,4};G{6,17,0};G{6,18,253};G{6,19,254};
G{7,0,254};G{7,1,254};G{7,2,0};G{7,3,1};G{7,4,0};G{7,5,1};G{7,6,0};G{7,7,2};G{7,8,0};G{7,9,1};G{7,10,255};G{7,11,255};G{7,12,1};G{7,13,0};G{7,14,0};G{7,15,2};G{7,16,0};G{7,17,0};G{7,18,255};G{7,19,254};
G{8,0,255};G{8,1,253};G{8,2,255};G{8,3,255};G{8,4,0};G{8,5,2};G{8,6,0};G{8,7,3};G{8,8,255};G{8,9,254};G{8,10,255};G{8,11,255};G{8,12,2};G{8,13,0};G{8,14,1};G{8,15,2};G{8,16,0};G{8,17,0};G{8,18,255};G{8,19,254};
G{9,0,254};G{9,1,255};G{9,2,255};G{9,3,255};G{9,4,255};G{9,5,255};G{9,6,255};G{9,7,253};G{9,8,252};G{9,9,255};G{9,10,255};G{9,11,252};G{9,12,0};G{9,13,2};G{9,14,1};G{9,15,0};G{9,16,4};G{9,17,0};G{9,18,253};G{9,19,254};
G{10,0,255};G{10,1,249};G{10,2,255};G{10,3,252};G{10,4,255};G{10,5,250};G{10,6,255};G{10,7,255};G{10,8,255};G{10,9,255};G{10,10,250};G{10,11,255};G{10,12,8};G{10,13,0};G{10,14,2};G{10,15,0};G{10,16,0};G{10,17,0};G{10,18,255};G{10,19,255};
G{11,0,253};G{11,1,255};G{11,2,255};G{11,3,255};G{11,4,254};G{11,5,255};G{11,6,255};G{11,7,254};G{11,8,254};G{11,9,253};G{11,10,255};G{11,11,253};G{11,12,249};G{11,13,254};G{11,14,252};G{11,15,255};G{11,16,255};G{11,17,255};G{11,18,254};G{11,19,253};
G{12,0,255};G{12,1,255};G{12,2,255};G{12,3,0};G{12,4,1};G{12,5,0};G{12,6,252};G{12,7,255};G{12,8,255};G{12,9,255};G{12,10,255};G{12,11,254};G{12,12,255};G{12,13,255};G{12,14,255};G{12,15,253};G{12,16,254};G{12,17,254};G{12,18,255};G{12,19,255};
G{13,0,255};G{13,1,254};G{13,2,1};G{13,3,0};G{13,4,0};G{13,5,4};G{13,6,2};G{13,7,255};G{13,8,254};G{13,9,255};G{13,10,255};G{13,11,255};G{13,12,255};G{13,13,255};G{13,14,255};G{13,15,252};G{13,16,255};G{13,17,253};G{13,18,255};G{13,19,255};
G{14,0,255};G{14,1,254};G{14,2,1};G{14,3,0};G{14,4,0};G{14,5,2};G{14,6,0};G{14,7,0};G{14,8,255};G{14,9,255};G{14,10,251};G{14,11,255};G{14,12,252};G{14,13,255};G{14,14,254};G{14,15,255};G{14,16,254};G{14,17,255};G{14,18,252};G{14,19,253};
G{15,0,255};G{15,1,254};G{15,2,0};G{15,3,1};G{15,4,0};G{15,5,0};G{15,6,4};G{15,7,1};G{15,8,0};G{15,9,255};G{15,10,255};G{15,11,252};G{15,12,255};G{15,13,255};G{15,14,253};G{15,15,255};G{15,16,255};G{15,17,250};G{15,18,254};G{15,19,255};
G{16,0,254};G{16,1,255};G{16,2,1};G{16,3,2};G{16,4,0};G{16,5,0};G{16,6,3};G{16,7,0};G{16,8,1};G{16,9,255};G{16,10,254};G{16,11,253};G{16,12,254};G{16,13,255};G{16,14,255};G{16,15,255};G{16,16,255};G{16,17,255};G{16,18,255};G{16,19,255};
G{17,0,253};G{17,1,253};G{17,2,0};G{17,3,1};G{17,4,3};G{17,5,0};G{17,6,0};G{17,7,1};G{17,8,0};G{17,9,253};G{17,10,255};G{17,11,255};G{17,12,255};G{17,13,252};G{17,14,255};G{17,15,253};G{17,16,255};G{17,17,255};G{17,18,255};G{17,19,255};
G{18,0,255};G{18,1,255};G{18,2,255};G{18,3,1};G{18,4,0};G{18,5,3};G{18,6,0};G{18,7,0};G{18,8,255};G{18,9,255};G{18,10,255};G{18,11,252};G{18,12,255};G{18,13,255};G{18,14,252};G{18,15,255};G{18,16,255};G{18,17,255};G{18,18,255};G{18,19,255};
G{19,0,255};G{19,1,254};G{19,2,252};G{19,3,255};G{19,4,255};G{19,5,255};G{19,6,254};G{19,7,255};G{19,8,255};G{19,9,255};G{19,10,254};G{19,11,255};G{19,12,253};G{19,13,254};G{19,14,251};G{19,15,255};G{19,16,255};G{19,17,255};G{19,18,255};G{19,19,255}].

(*Tool generated Coq definition of binary image*)
Definition coqbinaryimage := 
[B{0,0,white};B{0,1,white};B{0,2,white};B{0,3,white};B{0,4,black};B{0,5,black};B{0,6,black};B{0,7,black};B{0,8,white};B{0,9,white};B{0,10,white};B{0,11,white};B{0,12,white};B{0,13,white};B{0,14,white};B{0,15,white};B{0,16,white};B{0,17,white};B{0,18,white};B{0,19,white};
B{1,0,white};B{1,1,white};B{1,2,black};B{1,3,black};B{1,4,black};B{1,5,black};B{1,6,black};B{1,7,black};B{1,8,black};B{1,9,black};B{1,10,white};B{1,11,white};B{1,12,white};B{1,13,white};B{1,14,white};B{1,15,white};B{1,16,white};B{1,17,white};B{1,18,white};B{1,19,white};
B{2,0,white};B{2,1,white};B{2,2,black};B{2,3,black};B{2,4,black};B{2,5,black};B{2,6,black};B{2,7,black};B{2,8,black};B{2,9,black};B{2,10,white};B{2,11,white};B{2,12,white};B{2,13,white};B{2,14,white};B{2,15,white};B{2,16,white};B{2,17,white};B{2,18,white};B{2,19,white};
B{3,0,white};B{3,1,black};B{3,2,black};B{3,3,black};B{3,4,black};B{3,5,black};B{3,6,black};B{3,7,black};B{3,8,black};B{3,9,black};B{3,10,black};B{3,11,white};B{3,12,white};B{3,13,white};B{3,14,white};B{3,15,white};B{3,16,white};B{3,17,white};B{3,18,white};B{3,19,white};
B{4,0,white};B{4,1,black};B{4,2,black};B{4,3,black};B{4,4,black};B{4,5,black};B{4,6,black};B{4,7,black};B{4,8,black};B{4,9,black};B{4,10,black};B{4,11,white};B{4,12,white};B{4,13,white};B{4,14,white};B{4,15,white};B{4,16,white};B{4,17,white};B{4,18,white};B{4,19,white};
B{5,0,white};B{5,1,black};B{5,2,black};B{5,3,black};B{5,4,black};B{5,5,black};B{5,6,black};B{5,7,black};B{5,8,black};B{5,9,black};B{5,10,black};B{5,11,white};B{5,12,black};B{5,13,black};B{5,14,black};B{5,15,black};B{5,16,black};B{5,17,black};B{5,18,white};B{5,19,white};
B{6,0,white};B{6,1,white};B{6,2,black};B{6,3,black};B{6,4,black};B{6,5,black};B{6,6,black};B{6,7,black};B{6,8,black};B{6,9,black};B{6,10,white};B{6,11,white};B{6,12,black};B{6,13,black};B{6,14,black};B{6,15,black};B{6,16,black};B{6,17,black};B{6,18,white};B{6,19,white};
B{7,0,white};B{7,1,white};B{7,2,black};B{7,3,black};B{7,4,black};B{7,5,black};B{7,6,black};B{7,7,black};B{7,8,black};B{7,9,black};B{7,10,white};B{7,11,white};B{7,12,black};B{7,13,black};B{7,14,black};B{7,15,black};B{7,16,black};B{7,17,black};B{7,18,white};B{7,19,white};
B{8,0,white};B{8,1,white};B{8,2,white};B{8,3,white};B{8,4,black};B{8,5,black};B{8,6,black};B{8,7,black};B{8,8,white};B{8,9,white};B{8,10,white};B{8,11,white};B{8,12,black};B{8,13,black};B{8,14,black};B{8,15,black};B{8,16,black};B{8,17,black};B{8,18,white};B{8,19,white};
B{9,0,white};B{9,1,white};B{9,2,white};B{9,3,white};B{9,4,white};B{9,5,white};B{9,6,white};B{9,7,white};B{9,8,white};B{9,9,white};B{9,10,white};B{9,11,white};B{9,12,black};B{9,13,black};B{9,14,black};B{9,15,black};B{9,16,black};B{9,17,black};B{9,18,white};B{9,19,white};
B{10,0,white};B{10,1,white};B{10,2,white};B{10,3,white};B{10,4,white};B{10,5,white};B{10,6,white};B{10,7,white};B{10,8,white};B{10,9,white};B{10,10,white};B{10,11,white};B{10,12,black};B{10,13,black};B{10,14,black};B{10,15,black};B{10,16,black};B{10,17,black};B{10,18,white};B{10,19,white};
B{11,0,white};B{11,1,white};B{11,2,white};B{11,3,white};B{11,4,white};B{11,5,white};B{11,6,white};B{11,7,white};B{11,8,white};B{11,9,white};B{11,10,white};B{11,11,white};B{11,12,white};B{11,13,white};B{11,14,white};B{11,15,white};B{11,16,white};B{11,17,white};B{11,18,white};B{11,19,white};
B{12,0,white};B{12,1,white};B{12,2,white};B{12,3,black};B{12,4,black};B{12,5,black};B{12,6,white};B{12,7,white};B{12,8,white};B{12,9,white};B{12,10,white};B{12,11,white};B{12,12,white};B{12,13,white};B{12,14,white};B{12,15,white};B{12,16,white};B{12,17,white};B{12,18,white};B{12,19,white};
B{13,0,white};B{13,1,white};B{13,2,black};B{13,3,black};B{13,4,black};B{13,5,black};B{13,6,black};B{13,7,white};B{13,8,white};B{13,9,white};B{13,10,white};B{13,11,white};B{13,12,white};B{13,13,white};B{13,14,white};B{13,15,white};B{13,16,white};B{13,17,white};B{13,18,white};B{13,19,white};
B{14,0,white};B{14,1,white};B{14,2,black};B{14,3,black};B{14,4,black};B{14,5,black};B{14,6,black};B{14,7,black};B{14,8,white};B{14,9,white};B{14,10,white};B{14,11,white};B{14,12,white};B{14,13,white};B{14,14,white};B{14,15,white};B{14,16,white};B{14,17,white};B{14,18,white};B{14,19,white};
B{15,0,white};B{15,1,white};B{15,2,black};B{15,3,black};B{15,4,black};B{15,5,black};B{15,6,black};B{15,7,black};B{15,8,black};B{15,9,white};B{15,10,white};B{15,11,white};B{15,12,white};B{15,13,white};B{15,14,white};B{15,15,white};B{15,16,white};B{15,17,white};B{15,18,white};B{15,19,white};
B{16,0,white};B{16,1,white};B{16,2,black};B{16,3,black};B{16,4,black};B{16,5,black};B{16,6,black};B{16,7,black};B{16,8,black};B{16,9,white};B{16,10,white};B{16,11,white};B{16,12,white};B{16,13,white};B{16,14,white};B{16,15,white};B{16,16,white};B{16,17,white};B{16,18,white};B{16,19,white};
B{17,0,white};B{17,1,white};B{17,2,black};B{17,3,black};B{17,4,black};B{17,5,black};B{17,6,black};B{17,7,black};B{17,8,black};B{17,9,white};B{17,10,white};B{17,11,white};B{17,12,white};B{17,13,white};B{17,14,white};B{17,15,white};B{17,16,white};B{17,17,white};B{17,18,white};B{17,19,white};
B{18,0,white};B{18,1,white};B{18,2,white};B{18,3,black};B{18,4,black};B{18,5,black};B{18,6,black};B{18,7,black};B{18,8,white};B{18,9,white};B{18,10,white};B{18,11,white};B{18,12,white};B{18,13,white};B{18,14,white};B{18,15,white};B{18,16,white};B{18,17,white};B{18,18,white};B{18,19,white};
B{19,0,white};B{19,1,white};B{19,2,white};B{19,3,white};B{19,4,white};B{19,5,white};B{19,6,white};B{19,7,white};B{19,8,white};B{19,9,white};B{19,10,white};B{19,11,white};B{19,12,white};B{19,13,white};B{19,14,white};B{19,15,white};B{19,16,white};B{19,17,white};B{19,18,white};B{19,19,white}].

Definition rows' := 20.

Definition cols' := 20.

Definition threshold := 100.

(*A component of the input RGB image*) 
 Definition N8_component0:= 
[B{0,4,black};B{1,4,black};B{1,5,black};B{1,3,black};B{0,5,black};B{2,4,black};
B{2,5,black};B{1,6,black};B{2,3,black};B{1,2,black};B{0,6,black};B{3,4,black};
B{3,5,black};B{2,6,black};B{1,7,black};B{3,3,black};B{2,2,black};B{0,7,black};
B{4,4,black};B{4,5,black};B{3,6,black};B{2,7,black};B{1,8,black};B{4,3,black};
B{3,2,black};B{5,4,black};B{5,5,black};B{4,6,black};B{3,7,black};B{2,8,black};
B{1,9,black};B{5,3,black};B{4,2,black};B{3,1,black};B{6,4,black};B{6,5,black};
B{5,6,black};B{4,7,black};B{3,8,black};B{2,9,black};B{6,3,black};B{5,2,black};
B{4,1,black};B{7,4,black};B{7,5,black};B{6,6,black};B{5,7,black};B{4,8,black};
B{3,9,black};B{7,3,black};B{6,2,black};B{5,1,black};B{8,4,black};B{8,5,black};
B{7,6,black};B{6,7,black};B{5,8,black};B{4,9,black};B{3,10,black};B{7,2,black};
B{8,6,black};B{7,7,black};B{6,8,black};B{5,9,black};B{4,10,black};B{8,7,black};
B{7,8,black};B{6,9,black};B{5,10,black};B{7,9,black}].

(*Check if the object is well-formed: it is well-formed if the function returns true*) 
Compute (WF_object_8_b rows' cols' N8_component0).

(*Proving reflexivity property of two pixels in an image N8_component0.*) 
Lemma connect_refl_N8_component0: forall p, 
 connected_8 p p N8_component0. 
 Proof. 
 intros.  
 apply connected_8_refl; auto. 
Qed.

(*Proving communicative property of two pixels in an image N8_component0.*) 
Lemma connect_comm_N8_component0: forall p q, 
 connected_8 p q N8_component0 -> connected_8 q p N8_component0.  
Proof.  
 intros.   
 apply connected_8_comm; auto.  
Qed.  

(*Proving associative property of two pixels in an image N8_component0.*) 
Lemma connect_assoc_N8_component0: forall p q r, 
 connected_8 p q N8_component0 -> connected_8 q r N8_component0 -> connected_8 p r N8_component0. 
Proof.  
 intros.   
 apply connected_8_assoc with (q:=q); auto.  
Qed. 

(*A component of the input RGB image*) 
 Definition N8_component1:= 
[B{5,12,black};B{6,12,black};
B{6,13,black};B{5,13,black};B{7,12,black};B{7,13,black};B{6,14,black};B{5,14,black};
B{8,12,black};B{8,13,black};B{7,14,black};B{6,15,black};B{5,15,black};B{9,12,black};
B{9,13,black};B{8,14,black};B{7,15,black};B{6,16,black};B{5,16,black};B{10,12,black};
B{10,13,black};B{9,14,black};B{8,15,black};B{7,16,black};B{6,17,black};B{5,17,black};
B{10,14,black};B{9,15,black};B{8,16,black};B{7,17,black};B{10,15,black};B{9,16,black};
B{8,17,black};B{10,16,black};B{9,17,black};B{10,17,black}].

(*Check if the object is well-formed: it is well-formed if the function returns true*) 
Compute (WF_object_8_b rows' cols' N8_component1).

(*Proving reflexivity property of two pixels in an image N8_component1.*) 
Lemma connect_refl_N8_component1: forall p, 
 connected_8 p p N8_component1. 
 Proof. 
 intros.  
 apply connected_8_refl; auto. 
Qed.

(*Proving communicative property of two pixels in an image N8_component1.*) 
Lemma connect_comm_N8_component1: forall p q, 
 connected_8 p q N8_component1 -> connected_8 q p N8_component1.  
Proof.  
 intros.   
 apply connected_8_comm; auto.  
Qed.  

(*Proving associative property of two pixels in an image N8_component1.*) 
Lemma connect_assoc_N8_component1: forall p q r, 
 connected_8 p q N8_component1 -> connected_8 q r N8_component1 -> connected_8 p r N8_component1. 
Proof.  
 intros.   
 apply connected_8_assoc with (q:=q); auto.  
Qed. 

(*A component of the input RGB image*) 
 Definition N8_component2:= 
[B{12,3,black};B{13,3,black};
B{13,4,black};B{13,2,black};B{12,4,black};B{14,3,black};B{14,4,black};B{13,5,black};
B{14,2,black};B{12,5,black};B{15,3,black};B{15,4,black};B{14,5,black};B{13,6,black};
B{15,2,black};B{16,3,black};B{16,4,black};B{15,5,black};B{14,6,black};B{16,2,black};
B{17,3,black};B{17,4,black};B{16,5,black};B{15,6,black};B{14,7,black};B{17,2,black};
B{18,3,black};B{18,4,black};B{17,5,black};B{16,6,black};B{15,7,black};B{18,5,black};
B{17,6,black};B{16,7,black};B{15,8,black};B{18,6,black};B{17,7,black};B{16,8,black};
B{18,7,black};B{17,8,black}].

(*Check if the object is well-formed: it is well-formed if the function returns true*) 
Compute (WF_object_8_b rows' cols' N8_component2).

(*Proving reflexivity property of two pixels in an image N8_component2.*) 
Lemma connect_refl_N8_component2: forall p, 
 connected_8 p p N8_component2. 
 Proof. 
 intros.  
 apply connected_8_refl; auto. 
Qed.

(*Proving communicative property of two pixels in an image N8_component2.*) 
Lemma connect_comm_N8_component2: forall p q, 
 connected_8 p q N8_component2 -> connected_8 q p N8_component2.  
Proof.  
 intros.   
 apply connected_8_comm; auto.  
Qed.  

(*Proving associative property of two pixels in an image N8_component2.*) 
Lemma connect_assoc_N8_component2: forall p q r, 
 connected_8 p q N8_component2 -> connected_8 q r N8_component2 -> connected_8 p r N8_component2. 
Proof.  
 intros.   
 apply connected_8_assoc with (q:=q); auto.  
Qed. 

