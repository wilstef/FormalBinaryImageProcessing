Require Import binary_image_processing. 

(*Tool generated grayscale image matrix*)
Definition coqmatriximg := 
[97;93;84;79;86;95;130;142;120;90;104;106;112;67;78;126;111;150;110;156;
117;109;115;123;131;120;131;152;161;135;91;78;75;92;99;56;76;65;100;97;
82;95;102;97;85;131;147;162;134;154;151;141;87;71;76;89;75;88;61;68;
85;101;122;137;148;143;130;134;158;148;144;141;168;136;114;79;73;78;90;78;
79;87;98;129;138;136;140;125;136;126;161;149;144;146;148;150;121;81;85;88;
59;67;79;89;101;148;124;133;129;144;126;135;149;155;139;151;141;140;149;112;
43;75;84;74;65;93;132;134;122;118;133;138;142;134;137;147;145;133;132;127;
48;57;53;50;54;72;107;132;126;128;124;117;117;135;140;142;140;138;134;139;
61;51;54;61;72;68;115;140;142;145;140;126;119;126;137;140;137;132;131;136;
73;66;49;60;72;69;102;132;128;131;130;124;119;121;126;129;128;124;124;128;
78;62;54;61;70;75;115;130;122;124;127;129;126;125;130;134;133;128;129;132;
61;52;74;90;79;102;140;152;152;150;148;146;141;137;139;144;144;138;138;141;
52;58;107;101;81;104;143;165;157;155;152;148;143;145;149;152;149;144;143;145;
46;68;128;113;77;114;148;157;143;145;145;142;142;146;150;151;147;143;143;145;
32;49;99;132;95;141;143;140;141;141;140;136;134;133;134;133;142;142;144;147;
53;45;83;131;151;149;146;149;144;143;143;144;145;146;148;150;147;149;155;158;
44;41;49;75;112;137;135;136;136;136;137;139;142;144;145;146;141;140;137;136;
57;77;90;96;110;135;138;136;140;142;146;150;151;148;145;142;138;136;135;134;
84;122;147;142;129;132;133;136;138;139;139;141;141;139;137;135;136;136;136;136;
114;118;118;120;125;134;129;127;131;129;125;124;125;127;131;133;136;137;138;138].

(*Tool generated Coq definition of grayscale image*)
Definition coqgsimage := 
[G{0,0,97};G{0,1,93};G{0,2,84};G{0,3,79};G{0,4,86};G{0,5,95};G{0,6,130};G{0,7,142};G{0,8,120};G{0,9,90};G{0,10,104};G{0,11,106};G{0,12,112};G{0,13,67};G{0,14,78};G{0,15,126};G{0,16,111};G{0,17,150};G{0,18,110};G{0,19,156};
G{1,0,117};G{1,1,109};G{1,2,115};G{1,3,123};G{1,4,131};G{1,5,120};G{1,6,131};G{1,7,152};G{1,8,161};G{1,9,135};G{1,10,91};G{1,11,78};G{1,12,75};G{1,13,92};G{1,14,99};G{1,15,56};G{1,16,76};G{1,17,65};G{1,18,100};G{1,19,97};
G{2,0,82};G{2,1,95};G{2,2,102};G{2,3,97};G{2,4,85};G{2,5,131};G{2,6,147};G{2,7,162};G{2,8,134};G{2,9,154};G{2,10,151};G{2,11,141};G{2,12,87};G{2,13,71};G{2,14,76};G{2,15,89};G{2,16,75};G{2,17,88};G{2,18,61};G{2,19,68};
G{3,0,85};G{3,1,101};G{3,2,122};G{3,3,137};G{3,4,148};G{3,5,143};G{3,6,130};G{3,7,134};G{3,8,158};G{3,9,148};G{3,10,144};G{3,11,141};G{3,12,168};G{3,13,136};G{3,14,114};G{3,15,79};G{3,16,73};G{3,17,78};G{3,18,90};G{3,19,78};
G{4,0,79};G{4,1,87};G{4,2,98};G{4,3,129};G{4,4,138};G{4,5,136};G{4,6,140};G{4,7,125};G{4,8,136};G{4,9,126};G{4,10,161};G{4,11,149};G{4,12,144};G{4,13,146};G{4,14,148};G{4,15,150};G{4,16,121};G{4,17,81};G{4,18,85};G{4,19,88};
G{5,0,59};G{5,1,67};G{5,2,79};G{5,3,89};G{5,4,101};G{5,5,148};G{5,6,124};G{5,7,133};G{5,8,129};G{5,9,144};G{5,10,126};G{5,11,135};G{5,12,149};G{5,13,155};G{5,14,139};G{5,15,151};G{5,16,141};G{5,17,140};G{5,18,149};G{5,19,112};
G{6,0,43};G{6,1,75};G{6,2,84};G{6,3,74};G{6,4,65};G{6,5,93};G{6,6,132};G{6,7,134};G{6,8,122};G{6,9,118};G{6,10,133};G{6,11,138};G{6,12,142};G{6,13,134};G{6,14,137};G{6,15,147};G{6,16,145};G{6,17,133};G{6,18,132};G{6,19,127};
G{7,0,48};G{7,1,57};G{7,2,53};G{7,3,50};G{7,4,54};G{7,5,72};G{7,6,107};G{7,7,132};G{7,8,126};G{7,9,128};G{7,10,124};G{7,11,117};G{7,12,117};G{7,13,135};G{7,14,140};G{7,15,142};G{7,16,140};G{7,17,138};G{7,18,134};G{7,19,139};
G{8,0,61};G{8,1,51};G{8,2,54};G{8,3,61};G{8,4,72};G{8,5,68};G{8,6,115};G{8,7,140};G{8,8,142};G{8,9,145};G{8,10,140};G{8,11,126};G{8,12,119};G{8,13,126};G{8,14,137};G{8,15,140};G{8,16,137};G{8,17,132};G{8,18,131};G{8,19,136};
G{9,0,73};G{9,1,66};G{9,2,49};G{9,3,60};G{9,4,72};G{9,5,69};G{9,6,102};G{9,7,132};G{9,8,128};G{9,9,131};G{9,10,130};G{9,11,124};G{9,12,119};G{9,13,121};G{9,14,126};G{9,15,129};G{9,16,128};G{9,17,124};G{9,18,124};G{9,19,128};
G{10,0,78};G{10,1,62};G{10,2,54};G{10,3,61};G{10,4,70};G{10,5,75};G{10,6,115};G{10,7,130};G{10,8,122};G{10,9,124};G{10,10,127};G{10,11,129};G{10,12,126};G{10,13,125};G{10,14,130};G{10,15,134};G{10,16,133};G{10,17,128};G{10,18,129};G{10,19,132};
G{11,0,61};G{11,1,52};G{11,2,74};G{11,3,90};G{11,4,79};G{11,5,102};G{11,6,140};G{11,7,152};G{11,8,152};G{11,9,150};G{11,10,148};G{11,11,146};G{11,12,141};G{11,13,137};G{11,14,139};G{11,15,144};G{11,16,144};G{11,17,138};G{11,18,138};G{11,19,141};
G{12,0,52};G{12,1,58};G{12,2,107};G{12,3,101};G{12,4,81};G{12,5,104};G{12,6,143};G{12,7,165};G{12,8,157};G{12,9,155};G{12,10,152};G{12,11,148};G{12,12,143};G{12,13,145};G{12,14,149};G{12,15,152};G{12,16,149};G{12,17,144};G{12,18,143};G{12,19,145};
G{13,0,46};G{13,1,68};G{13,2,128};G{13,3,113};G{13,4,77};G{13,5,114};G{13,6,148};G{13,7,157};G{13,8,143};G{13,9,145};G{13,10,145};G{13,11,142};G{13,12,142};G{13,13,146};G{13,14,150};G{13,15,151};G{13,16,147};G{13,17,143};G{13,18,143};G{13,19,145};
G{14,0,32};G{14,1,49};G{14,2,99};G{14,3,132};G{14,4,95};G{14,5,141};G{14,6,143};G{14,7,140};G{14,8,141};G{14,9,141};G{14,10,140};G{14,11,136};G{14,12,134};G{14,13,133};G{14,14,134};G{14,15,133};G{14,16,142};G{14,17,142};G{14,18,144};G{14,19,147};
G{15,0,53};G{15,1,45};G{15,2,83};G{15,3,131};G{15,4,151};G{15,5,149};G{15,6,146};G{15,7,149};G{15,8,144};G{15,9,143};G{15,10,143};G{15,11,144};G{15,12,145};G{15,13,146};G{15,14,148};G{15,15,150};G{15,16,147};G{15,17,149};G{15,18,155};G{15,19,158};
G{16,0,44};G{16,1,41};G{16,2,49};G{16,3,75};G{16,4,112};G{16,5,137};G{16,6,135};G{16,7,136};G{16,8,136};G{16,9,136};G{16,10,137};G{16,11,139};G{16,12,142};G{16,13,144};G{16,14,145};G{16,15,146};G{16,16,141};G{16,17,140};G{16,18,137};G{16,19,136};
G{17,0,57};G{17,1,77};G{17,2,90};G{17,3,96};G{17,4,110};G{17,5,135};G{17,6,138};G{17,7,136};G{17,8,140};G{17,9,142};G{17,10,146};G{17,11,150};G{17,12,151};G{17,13,148};G{17,14,145};G{17,15,142};G{17,16,138};G{17,17,136};G{17,18,135};G{17,19,134};
G{18,0,84};G{18,1,122};G{18,2,147};G{18,3,142};G{18,4,129};G{18,5,132};G{18,6,133};G{18,7,136};G{18,8,138};G{18,9,139};G{18,10,139};G{18,11,141};G{18,12,141};G{18,13,139};G{18,14,137};G{18,15,135};G{18,16,136};G{18,17,136};G{18,18,136};G{18,19,136};
G{19,0,114};G{19,1,118};G{19,2,118};G{19,3,120};G{19,4,125};G{19,5,134};G{19,6,129};G{19,7,127};G{19,8,131};G{19,9,129};G{19,10,125};G{19,11,124};G{19,12,125};G{19,13,127};G{19,14,131};G{19,15,133};G{19,16,136};G{19,17,137};G{19,18,138};G{19,19,138}].

(*Tool generated Coq definition of binary image*)
Definition coqbinaryimage := 
[B{0,0,black};B{0,1,black};B{0,2,black};B{0,3,black};B{0,4,black};B{0,5,black};B{0,6,white};B{0,7,white};B{0,8,black};B{0,9,black};B{0,10,black};B{0,11,black};B{0,12,black};B{0,13,black};B{0,14,black};B{0,15,white};B{0,16,black};B{0,17,white};B{0,18,black};B{0,19,white};
B{1,0,black};B{1,1,black};B{1,2,black};B{1,3,white};B{1,4,white};B{1,5,black};B{1,6,white};B{1,7,white};B{1,8,white};B{1,9,white};B{1,10,black};B{1,11,black};B{1,12,black};B{1,13,black};B{1,14,black};B{1,15,black};B{1,16,black};B{1,17,black};B{1,18,black};B{1,19,black};
B{2,0,black};B{2,1,black};B{2,2,black};B{2,3,black};B{2,4,black};B{2,5,white};B{2,6,white};B{2,7,white};B{2,8,white};B{2,9,white};B{2,10,white};B{2,11,white};B{2,12,black};B{2,13,black};B{2,14,black};B{2,15,black};B{2,16,black};B{2,17,black};B{2,18,black};B{2,19,black};
B{3,0,black};B{3,1,black};B{3,2,white};B{3,3,white};B{3,4,white};B{3,5,white};B{3,6,white};B{3,7,white};B{3,8,white};B{3,9,white};B{3,10,white};B{3,11,white};B{3,12,white};B{3,13,white};B{3,14,black};B{3,15,black};B{3,16,black};B{3,17,black};B{3,18,black};B{3,19,black};
B{4,0,black};B{4,1,black};B{4,2,black};B{4,3,white};B{4,4,white};B{4,5,white};B{4,6,white};B{4,7,white};B{4,8,white};B{4,9,white};B{4,10,white};B{4,11,white};B{4,12,white};B{4,13,white};B{4,14,white};B{4,15,white};B{4,16,white};B{4,17,black};B{4,18,black};B{4,19,black};
B{5,0,black};B{5,1,black};B{5,2,black};B{5,3,black};B{5,4,black};B{5,5,white};B{5,6,white};B{5,7,white};B{5,8,white};B{5,9,white};B{5,10,white};B{5,11,white};B{5,12,white};B{5,13,white};B{5,14,white};B{5,15,white};B{5,16,white};B{5,17,white};B{5,18,white};B{5,19,black};
B{6,0,black};B{6,1,black};B{6,2,black};B{6,3,black};B{6,4,black};B{6,5,black};B{6,6,white};B{6,7,white};B{6,8,white};B{6,9,black};B{6,10,white};B{6,11,white};B{6,12,white};B{6,13,white};B{6,14,white};B{6,15,white};B{6,16,white};B{6,17,white};B{6,18,white};B{6,19,white};
B{7,0,black};B{7,1,black};B{7,2,black};B{7,3,black};B{7,4,black};B{7,5,black};B{7,6,black};B{7,7,white};B{7,8,white};B{7,9,white};B{7,10,white};B{7,11,black};B{7,12,black};B{7,13,white};B{7,14,white};B{7,15,white};B{7,16,white};B{7,17,white};B{7,18,white};B{7,19,white};
B{8,0,black};B{8,1,black};B{8,2,black};B{8,3,black};B{8,4,black};B{8,5,black};B{8,6,black};B{8,7,white};B{8,8,white};B{8,9,white};B{8,10,white};B{8,11,white};B{8,12,black};B{8,13,white};B{8,14,white};B{8,15,white};B{8,16,white};B{8,17,white};B{8,18,white};B{8,19,white};
B{9,0,black};B{9,1,black};B{9,2,black};B{9,3,black};B{9,4,black};B{9,5,black};B{9,6,black};B{9,7,white};B{9,8,white};B{9,9,white};B{9,10,white};B{9,11,white};B{9,12,black};B{9,13,white};B{9,14,white};B{9,15,white};B{9,16,white};B{9,17,white};B{9,18,white};B{9,19,white};
B{10,0,black};B{10,1,black};B{10,2,black};B{10,3,black};B{10,4,black};B{10,5,black};B{10,6,black};B{10,7,white};B{10,8,white};B{10,9,white};B{10,10,white};B{10,11,white};B{10,12,white};B{10,13,white};B{10,14,white};B{10,15,white};B{10,16,white};B{10,17,white};B{10,18,white};B{10,19,white};
B{11,0,black};B{11,1,black};B{11,2,black};B{11,3,black};B{11,4,black};B{11,5,black};B{11,6,white};B{11,7,white};B{11,8,white};B{11,9,white};B{11,10,white};B{11,11,white};B{11,12,white};B{11,13,white};B{11,14,white};B{11,15,white};B{11,16,white};B{11,17,white};B{11,18,white};B{11,19,white};
B{12,0,black};B{12,1,black};B{12,2,black};B{12,3,black};B{12,4,black};B{12,5,black};B{12,6,white};B{12,7,white};B{12,8,white};B{12,9,white};B{12,10,white};B{12,11,white};B{12,12,white};B{12,13,white};B{12,14,white};B{12,15,white};B{12,16,white};B{12,17,white};B{12,18,white};B{12,19,white};
B{13,0,black};B{13,1,black};B{13,2,white};B{13,3,black};B{13,4,black};B{13,5,black};B{13,6,white};B{13,7,white};B{13,8,white};B{13,9,white};B{13,10,white};B{13,11,white};B{13,12,white};B{13,13,white};B{13,14,white};B{13,15,white};B{13,16,white};B{13,17,white};B{13,18,white};B{13,19,white};
B{14,0,black};B{14,1,black};B{14,2,black};B{14,3,white};B{14,4,black};B{14,5,white};B{14,6,white};B{14,7,white};B{14,8,white};B{14,9,white};B{14,10,white};B{14,11,white};B{14,12,white};B{14,13,white};B{14,14,white};B{14,15,white};B{14,16,white};B{14,17,white};B{14,18,white};B{14,19,white};
B{15,0,black};B{15,1,black};B{15,2,black};B{15,3,white};B{15,4,white};B{15,5,white};B{15,6,white};B{15,7,white};B{15,8,white};B{15,9,white};B{15,10,white};B{15,11,white};B{15,12,white};B{15,13,white};B{15,14,white};B{15,15,white};B{15,16,white};B{15,17,white};B{15,18,white};B{15,19,white};
B{16,0,black};B{16,1,black};B{16,2,black};B{16,3,black};B{16,4,black};B{16,5,white};B{16,6,white};B{16,7,white};B{16,8,white};B{16,9,white};B{16,10,white};B{16,11,white};B{16,12,white};B{16,13,white};B{16,14,white};B{16,15,white};B{16,16,white};B{16,17,white};B{16,18,white};B{16,19,white};
B{17,0,black};B{17,1,black};B{17,2,black};B{17,3,black};B{17,4,black};B{17,5,white};B{17,6,white};B{17,7,white};B{17,8,white};B{17,9,white};B{17,10,white};B{17,11,white};B{17,12,white};B{17,13,white};B{17,14,white};B{17,15,white};B{17,16,white};B{17,17,white};B{17,18,white};B{17,19,white};
B{18,0,black};B{18,1,white};B{18,2,white};B{18,3,white};B{18,4,white};B{18,5,white};B{18,6,white};B{18,7,white};B{18,8,white};B{18,9,white};B{18,10,white};B{18,11,white};B{18,12,white};B{18,13,white};B{18,14,white};B{18,15,white};B{18,16,white};B{18,17,white};B{18,18,white};B{18,19,white};
B{19,0,black};B{19,1,black};B{19,2,black};B{19,3,black};B{19,4,white};B{19,5,white};B{19,6,white};B{19,7,white};B{19,8,white};B{19,9,white};B{19,10,white};B{19,11,white};B{19,12,white};B{19,13,white};B{19,14,white};B{19,15,white};B{19,16,white};B{19,17,white};B{19,18,white};B{19,19,white}].

Definition rows' := 20.

Definition cols' := 20.

Definition threshold := 120.

(*Coq generated grayscale image*) 
Definition gsimagecoq := createimage (rev coqmatriximg) (rows'-1) (cols'-1) (cols'-1). 

(*Coq generated binary image*)
 Definition binimagecoq := thresholding gsimagecoq threshold.

(*Proof that the tool generated gray image 'coqgsimage' and Coq generated image 'gsimagecoq' are the same.*) 
Lemma gsimage_eq: coqgsimage = gsimagecoq. 
 Proof. 
  unfold coqgsimage. 
  unfold gsimagecoq.  
  simpl.    
  reflexivity. 
Qed. 

(*Proof that the tool generated binary image 'coqbinaryimage' and Coq generated binary image 'binimagecoq' are the same.*)  
 Lemma binimage_eq: coqbinaryimage = binimagecoq. 
 Proof. 
  unfold coqbinaryimage. 
  unfold binimagecoq.  
 unfold gsimagecoq. 
  simpl.    
  reflexivity. 
Qed. 

Compute (thresholding coqgsimage 170). 

Compute gsimagecoq. (*creates gray scale image from coqmatriximg*) 

(*creates binary image in the threshold range*) 
Definition binaryimage := (thresholdrange coqgsimage 100 200). 

Compute (areasize binaryimage). 

Compute (runlength binaryimage). 

Compute (sumrunlen (runlength binaryimage)).