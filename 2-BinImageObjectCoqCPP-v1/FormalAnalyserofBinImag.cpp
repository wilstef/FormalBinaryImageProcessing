/*
 This C++ code reads an RGB image, convert the RGB image to:
   1. grayscale image (as a matrix) 
   2. binary image as a matrix (stored in 'binaryimage.txt') as well as Coq definition  of the image (stored in 'coqbinaryimage.text')
   3. labels and identifies all the image objects based on four and eight neighbours definitions,
   4. generates Coq proof that all the pixels in an object conforms to the Coq definition of neighbourhood
*/

#include <stdint.h>
#include <iostream>
#include <string>
#include <fstream>
//https://www.scaler.com/topics/cpp/pair-in-cpp/
#include <utility>
#include <tuple>
#include <list>
#include<bits/stdc++.h> //Using single pointer we have to typecast the 2D array.


using std::string;
using namespace std;  //for pair functions

#define STB_IMAGE_IMPLEMENTATION
#include "cpplibraries/stb_image.h"
#define STBI_MSC_SECURE_CRT
#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "cpplibraries/stb_image_write.h"

//returns four neibhours of a pixel at row,col in image negatedimg, with height x width dimension
//this definition conforms to the Coq definition as the Coq proof holds
 list<pair<int,int>>  getneighbours4(int row, int col, int height, int width, int *negatedimg) {
	list<pair<int, int>> tempneighbours4;
	
	if(row+1 < height & col < width & *((negatedimg+(row+1)*width) + col) == -1)
		tempneighbours4.push_back(make_pair(row+1,col) );
	
	if(row-1 < height & col < width & *((negatedimg+(row-1)*width) + col) == -1)
		tempneighbours4.push_back(make_pair(row-1,col));
	
	if(row < height & col+1 < width & *((negatedimg+row*width) + (col+1)) == -1)
		tempneighbours4.push_back(make_pair(row,col+1));	
	
	if(row < height & col-1 < width & *((negatedimg+row*width) + (col-1)) == -1)
		tempneighbours4.push_back(make_pair(row,col-1));
		
	return tempneighbours4;
 }
 
 //returns eight neibhours of a pixel at row,col in image negatedimg, with height x width dimension
 //this definition conforms to the Coq definition as the Coq proof holds
  list<pair<int,int>>  getneighbours8(int row, int col, int height, int width, int *negatedimg) {
	list<pair<int, int>> tempneighbours8;
	
	if(row+1 < height & col < width & *((negatedimg+(row+1)*width) + col) == -1)
		tempneighbours8.push_back(make_pair(row+1,col) );
	
	if(row+1 < height & col+1 < width & *((negatedimg+(row+1)*width) + (col+1)) == -1)
		tempneighbours8.push_back(make_pair(row+1,col+1) );
	
	if(row-1 < height & col < width & *((negatedimg+(row-1)*width) + col) == -1)
		tempneighbours8.push_back(make_pair(row-1,col));
	
	if(row+1 < height & col-1 < width & *((negatedimg+(row+1)*width) + (col-1)) == -1)
		tempneighbours8.push_back(make_pair(row+1,col-1) );
	
	if(row < height & col+1 < width & *((negatedimg+row*width) + (col+1)) == -1)
		tempneighbours8.push_back(make_pair(row,col+1));	
	
	if(row-1 < height & col-1 < width & *((negatedimg+(row-1)*width) + (col-1)) == -1)
		tempneighbours8.push_back(make_pair(row-1,col-1) );
	
	if(row < height & col-1 < width & *((negatedimg+row*width) + (col-1)) == -1)
		tempneighbours8.push_back(make_pair(row,col-1));
	
	if(row-1 < height & col+1 < width & *((negatedimg+(row-1)*width) + (col+1)) == -1)
		tempneighbours8.push_back(make_pair(row-1,col+1) );
		
	return tempneighbours8;
 }
 
int main() {
    int width, height, channels;
	int threshold = 100;
	string coqproofsallobjects = "";
	string coqgsimage =  "[";
	string coqmatriximg = "[";
	string coqbinaryimage = "[";
	string imagename = " ";
	string binaryimage = "";
	string negbinaryimagestr = "";
	list<pair<int, int>> imageobject;	
	
//Coq script-generalized proof of reflexivity, commutativity and associativity of connection relation over each image object.
const char *coqscript = "(*Proving reflexivity property of two pixels in an image componentn.*) \
\nLemma connect_refl_componentn: forall p, \n\
 connected_n p p componentn. \n\
 Proof. \n\
 intros.  \n\
 apply connected_n_refl; auto. \n\
Qed.\n\n\
(*Proving communicative property of two pixels in an image componentn.*) \n\
Lemma connect_comm_componentn: forall p q, \n\
 connected_n p q componentn -> connected_n q p componentn.  \n\
Proof.  \n\
 intros.   \n\
 apply connected_n_comm; auto.  \n\
Qed.  \n\n\
(*Proving associative property of two pixels in an image componentn.*) \n\
Lemma connect_assoc_componentn: forall p q r, \n\
 connected_n p q componentn -> connected_n q r componentn -> connected_n p r componentn. \n\
Proof.  \n\
 intros.   \n\
 apply connected_n_assoc with (q:=q); auto.  \n\
Qed. \n\n";

const char *wf_check_4 = "\n(*Check if the object is well-formed: it is well-formed if the function returns true*) \n\
Compute (WF_object_4_b rows' cols' componentn).";

const char *wf_check_8 =  "\n(*Check if the object is well-formed: it is well-formed if the function returns true*) \n\
Compute (WF_object_8_b rows' cols' componentn).";
	
	std::cout<<"\n---- Enter valid image file name with ----\n\t";
	std::cin >> imagename;
	
	std::cout<<"\n---- Enter a threshould value between (0-255) ----\n\t";
	std::cin >> threshold;
    
    uint8_t* rgb_image = stbi_load(imagename.c_str(), &width, &height, &channels, 0); 
	
    int *rgbimagearray = new int[width*height*channels]; 
	int *grayimagearray = new int[width*height];
	int negbinaryimageint4[height][width];    //stores (1's pixels) negated image for neighbours 4 analysis
	int negbinaryimageint8[height][width];    //stores (1's pixels) negated image for neighbours 4 analysis
	 
	//populate the rgbimage int array
	for(int i=0; i<width*height*channels; i++) {
		rgbimagearray[i] = (int)(rgb_image[i]);
	}
	
	//populate grayimagearray (take average of the R,G,B channel values)
	int index=0;
	for(int i=0; i<width*height*channels; i += channels){
		grayimagearray[index++] = (rgbimagearray[i] + rgbimagearray[i+1] + rgbimagearray[i+2])/3;
	}
				
	if (rgb_image == NULL | threshold < 0 | threshold > 255) {
		if (rgb_image == NULL)
			std::cerr << "The image "<<imagename<<" could not be loaded. \n Please enter a valid image file name." <<std::endl;
		else std::cerr << "The threshold value "<<threshold<<" is out of range." <<std::endl;
	}
    else {

		/*Create the content of text files (binary image matrix and Coq binary image), binary image, 
		 negated binary image, negated binary image as string, and binary image as Coq definition. 
		*/
		int row = 0;
		for(int i=0; i<width*height; i++) {
			if (i!= 0 && i%width == 0) {
				row++;
				coqmatriximg = coqmatriximg + "\n";
				coqgsimage = coqgsimage + "\n";
				coqbinaryimage = coqbinaryimage + "\n";
				binaryimage = binaryimage + "\n";
				negbinaryimagestr = negbinaryimagestr + "\n";
			}
			coqmatriximg = coqmatriximg + std::to_string(grayimagearray[i])+";";
			coqgsimage = coqgsimage +"G{"+std::to_string(row)+","+std::to_string(i%width)+","+std::to_string(grayimagearray[i])+"};";	
			if (grayimagearray[i] <= threshold)  {
				negbinaryimageint4[row][i%width] = -1;
				negbinaryimageint8[row][i%width] = -1;
				negbinaryimagestr = negbinaryimagestr + "-1" +" ";
				binaryimage = binaryimage + "1" +" ";
				coqbinaryimage = coqbinaryimage +"B{"+std::to_string(row)+","+std::to_string(i%width)+","+"black"+"};";	
			} 
		    else { negbinaryimageint4[row][i%width] = 0;
				   negbinaryimageint8[row][i%width] = 0;
				   negbinaryimagestr = negbinaryimagestr + "0" +" ";
				   binaryimage = binaryimage + "0" +" ";
				   coqbinaryimage = coqbinaryimage +"B{"+std::to_string(row)+","+std::to_string(i%width)+","+"white"+"};"; 
			}
		}

		coqmatriximg[coqmatriximg.length() - 1] = ']';
		coqgsimage[coqgsimage.length() - 1] = ']';
		coqbinaryimage[coqbinaryimage.length() - 1] = ']';
		binaryimage[binaryimage.length() - 1] = '\0';
		negbinaryimagestr[negbinaryimagestr.length() - 1] = ']';			
			
	    //writing the binary image to a file
		std::ofstream out2("imageobjects/binaryimage.txt");
		out2 << binaryimage;
		out2.close();
		
		//writing the binary image to a file
		std::ofstream out3("imageobjects/coqbinaryimage.txt");
		out3 << coqbinaryimage;
		out3.close();
		
		//writing the negated binary image to a file
		std::ofstream out4("imageobjects/negatedbinaryimage.txt");		
		out4 << negbinaryimagestr;
		out4.close();
		
		coqgsimage = "Require Import pixel_connectivity_8_equiv. \n\n(*Tool generated grayscale image matrix*)\nDefinition coqmatriximg := \n"+ coqmatriximg + ".\n\n" +
				  "(*Tool generated Coq definition of grayscale image*)\nDefinition coqgsimage := \n"+coqgsimage + ".\n\n"+
				   "(*Tool generated Coq definition of binary image*)\nDefinition coqbinaryimage := \n"+coqbinaryimage + ".\n\nDefinition rows' := "+std::to_string(height)+".\n\n" + 
				   "Definition cols' := "+std::to_string(width)+".\n\nDefinition threshold := "+std::to_string(threshold)+".\n\n";

		string coqcomponentdef = "(*A component of the input RGB image*) \n Definition ";		
		int index, screenwidth;
		string tempname, coqcomponent, tempstr;		
		
		
		//computation of image objects according to neighbours four definition
		index=0;
		screenwidth = 0;
		tempname = "";
		coqcomponent = "";	
		tempstr = "";
		for(int row=0; row<height; row++){
			for(int col=0; col<width; col++) {
				if(negbinaryimageint4[row][col] == -1) {
					negbinaryimageint4[row][col] = 1;
                    list<pair<int, int>> tempneighbours4list;
		        	int row2, col2;
			   
				   tempneighbours4list = getneighbours4(row, col, height, width, (int *)negbinaryimageint4);
		
				  for(auto itr=tempneighbours4list.begin();itr!=tempneighbours4list.end();itr++) {
					if (negbinaryimageint4[itr->first][itr->second] == -1) {
						imageobject.push_back(make_pair(itr->first,itr->second));
			
						row2 = itr->first;
						col2 = itr->second;
						negbinaryimageint4[row2][col2] = 1;	
						
						if(row2+1 < height & col2 < width & negbinaryimageint4[row2+1][col2] == -1) 
							tempneighbours4list.push_back(make_pair(row2+1,col2) );
	
						if(row2-1 > -1 & row2-1 < height & col2 < width & negbinaryimageint4[row2-1][col2] == -1) 
							tempneighbours4list.push_back(make_pair(row2-1,col2));   
	
						if(row2 < height & col2+1 < width & negbinaryimageint4[row2][col2+1] == -1)
							tempneighbours4list.push_back(make_pair(row2,col2+1));	   
	
						if(row2 < height & col2-1 > -1 & col2-1 < width & negbinaryimageint4[row2][col2-1] == -1)
							tempneighbours4list.push_back(make_pair(row2,col2-1));
			
					}
				  }

					imageobject.push_front(make_pair(row,col));
					
					for(auto itr=imageobject.begin();itr!=imageobject.end();itr++) {
						tempname = tempname + std::to_string(itr->first)+","+std::to_string(itr->second)+"\n";
						if( screenwidth++ == 5) {
							coqcomponent = coqcomponent + "B{"+std::to_string(itr->first)+","+std::to_string(itr->second)+",black};\n";
							screenwidth = 0;
						}
						else 
							coqcomponent = coqcomponent + "B{"+std::to_string(itr->first)+","+std::to_string(itr->second)+",black};";
					}
										
				    if(coqcomponent[coqcomponent.length()-1] == '\n') {
					    coqcomponent[coqcomponent.length() - 2] = ']';
						coqcomponent[coqcomponent.length() - 1] = '.';
					}
					else {	
						coqcomponent[coqcomponent.length() - 1] = ']';												
						coqcomponent = coqcomponent + ".";
					}
					
					//compute and write each neighbours four image object to a file 
					coqcomponent = coqcomponentdef + "N4_component" + std::to_string(index)+":= \n[" + coqcomponent;	
					imageobject.clear();
					std::ofstream objectfiles("imageobjects/N4_image_component"+ std::to_string(index)+".txt");
					objectfiles << tempname;					
					tempname  = "";
					objectfiles.close();
					
					//compute Coq proof script (proof of reflexivity, commutativity and transitivity
					tempstr = coqcomponent + "\n" + wf_check_4;
				    tempstr = tempstr + "\n\n" + coqscript; 
					tempstr = std::regex_replace(tempstr, std::regex("componentn"), "N4_component"+std::to_string(index));
					tempstr = std::regex_replace(tempstr, std::regex("connected_n"), "connected_4");
					coqproofsallobjects = coqproofsallobjects + tempstr;
					index++;
					coqcomponent = "";
				}
			}
		}			
			
		//writing the Coq definitions of the image, objects and proof of lemmas to a file
		std::ofstream out1("connectivity4_pixels_image_components.v");	
		out1 << coqgsimage + coqproofsallobjects;
		out1.close();					

        //computation of image objects according to neighbours eight definition
		index=0;
		screenwidth = 0;
		tempname = "";
		tempstr = "";
		coqcomponent = "";	
		imageobject.clear();
		coqproofsallobjects = "";
		
		for(int row=0; row<height; row++){
			for(int col=0; col<width; col++) {
				if(negbinaryimageint8[row][col] == -1) {
					negbinaryimageint8[row][col] = 1;
                    list<pair<int, int>> tempneighbours8list;
		        	int row2, col2;
			   
				   tempneighbours8list = getneighbours8(row, col, height, width, (int *)negbinaryimageint8);
		
				  for(auto itr=tempneighbours8list.begin();itr!=tempneighbours8list.end();itr++) {
					if (negbinaryimageint8[itr->first][itr->second] == -1) {
						imageobject.push_back(make_pair(itr->first,itr->second));
			
						row2 = itr->first;
						col2 = itr->second;
						negbinaryimageint8[row2][col2] = 1;	
						
						if(row2+1 < height & col2 < width & negbinaryimageint8[row2+1][col2] == -1) 
							tempneighbours8list.push_back(make_pair(row2+1,col2) );
	
						if(row2-1 > -1 & row2-1 < height & col2 < width & negbinaryimageint8[row2-1][col2] == -1) 
							tempneighbours8list.push_back(make_pair(row2-1,col2));   
	
						if(row2 < height & col2+1 < width & negbinaryimageint8[row2][col2+1] == -1)
							tempneighbours8list.push_back(make_pair(row2,col2+1));	   
	
						if(row2 < height & col2-1 > -1 & col2-1 < width & negbinaryimageint8[row2][col2-1] == -1)
							tempneighbours8list.push_back(make_pair(row2,col2-1));
			
					}
				  }

					imageobject.push_front(make_pair(row,col));
					
					for(auto itr=imageobject.begin();itr!=imageobject.end();itr++) {
						tempname = tempname + std::to_string(itr->first)+","+std::to_string(itr->second)+"\n";
						if( screenwidth++ == 5) {
							coqcomponent = coqcomponent + "B{"+std::to_string(itr->first)+","+std::to_string(itr->second)+",black};\n";
							screenwidth = 0;
						}
						else 
							coqcomponent = coqcomponent + "B{"+std::to_string(itr->first)+","+std::to_string(itr->second)+",black};";
					}
										
				    if(coqcomponent[coqcomponent.length()-1] == '\n') {
					    coqcomponent[coqcomponent.length() - 2] = ']';
						coqcomponent[coqcomponent.length() - 1] = '.';
					}
					else {	
						coqcomponent[coqcomponent.length() - 1] = ']';												
						coqcomponent = coqcomponent + ".";
					}
					
					//compute and write each neighbours eight image object to a file 
					coqcomponent = coqcomponentdef + "N8_component" + std::to_string(index)+":= \n[" + coqcomponent;		
					imageobject.clear();
					std::ofstream N8_objectfiles("imageobjects/N8_image_component"+ std::to_string(index)+".txt");
					N8_objectfiles << tempname;					
					tempname  = "";
					N8_objectfiles.close();
					
					
					//compute Coq proof script (proof of reflexivity, commutativity and transitivity
				    tempstr = coqcomponent + "\n" + wf_check_8;
				    tempstr = tempstr + "\n\n" + coqscript; 
					tempstr = std::regex_replace(tempstr, std::regex("componentn"), "N8_component"+std::to_string(index));
					tempstr = std::regex_replace(tempstr, std::regex("connected_n"), "connected_8");
					coqproofsallobjects = coqproofsallobjects + tempstr;
					index++;
					coqcomponent = "";
				}
			}
		}
		
		//writing the Coq definitions of the image, N8 objects and proof of lemmas to a file
		std::ofstream out5("connectivity8_pixels_image_components.v");	
		out5 << coqgsimage + coqproofsallobjects;
		out5.close();	

		//stbi_image_free(gray_img);
 		stbi_image_free(rgb_image);
    }
	
	system("pause");
    return 0;
}