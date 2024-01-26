
In this README file, we explain how to compiler the Coq and C++ files and then
test/verify the correctness of image object identification over a test RGB image. 

1. Function and compileration of the main application (in C++)
   The C++ file 'FormalAnalyserofBinImag.cpp' is the source of the image object
   identifiation and Coq script generator. It reads an image and threshold value
   (between 0-256) and generates binary file, both in 0s and 1s, and Coq definition
   of the binary image. In addition, the objects in the binary image are also identified
   and stored separately as arry age of row-column pair. Furthermore, this application,
   generates two Coq script files, connectivity4_pixels_image_components.v and connectivity8_pixels_image_components.v', 
   respectively for four and eight neighbours. The Coq scripts have many lemmas and their proofs, regarding
   some properties of the neighbourhood and well-formedness of the objects identified. 

   To compile the C++ file above, first make sure that desired C++ compiler (g++) is installed and its path
   has been added to the 'PATH' variable. To confirm that, first open Windows command prompt 
   (use Window search option), 
   and run the command 
   C:\g++ --version
   If it displays version details of the compiler, all is right. 

   Now using the DOS change directory command 'cd' to change to the working director. 
   C:\cd BinImageCPP-v1
   Then run compiler the application, using
    C:\cd BinImageCPP-v1>g++ FormalAnalyserofBinImag.cpp -o FormalAnalyserofBinImag.exe
   Then run the executable application using
    C:\cd BinImageCPP-v1>FormalAnalyserofBinImag.exe

    It will ask to enter the test image name. Just type 'image.png' and press ENTER
    it will ask to enter the threshold value. Just type any value between 0-256 and press ENTER.
    It will generate all the files, including the Coq scripts. 

2. Compilig the Coq files
   To run the Coq script using the Coq type checker, first the executable Coq source must be
   created. After the C++ application is executed over a test image, there will be FIVE Coq script
   files. 
   - binary_image.v (original)
   - pixel_connectivity_4_equiv (original)
   - pixel_connectivity_8_equiv (original)
   - connectivity4_pixels_image_components.v (automatically generated)
   - connectivity8_pixels_image_components.v (automatically generated)

   To compiler the last two files, as they are dependent on the first three, they needs to be compiled first. 
   First ensure the Coq compiler, coqc, is installed. To check that, on the command prompt, run the command. 
   C:\cd BinImageCPP-v1>coqc --version
   If it gives version detail, all is right. 
   Now compiler the first three Coq files. 
    C:\cd BinImageCPP-v1>coqc binary_image.v
    C:\cd BinImageCPP-v1>coqc pixel_connectivity_4_equiv.v
    C:\cd BinImageCPP-v1>coqc pixel_connectivity_8_equiv.v

    This will generated three files for each Coq script file. Delete all others, and keep the .vo files in these
    newly generated files. 

    Now everything is ready. Just double click the 'connectivity4_pixels_image_components.v' or 
    'connectivity8_pixels_image_components.v'. It will be opened in the Coq IDE. Run the down arrows in 
    the tool bar to check the script. If all the script is successfully compiled till the end, 
    the image objects are verified. 
