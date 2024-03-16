This directory contains code based on work of Jeremy Rouse, Andrew V. Sutherland, and David Zywina that computes models for universal elliptic curves over modular curves whose underlying moduli space is fine (away from cusps and elliptic points). 

The directory ```./finecurves_data/``` contains LMFDB labels for fine modular curves and the generators for their corresponding groups obtained from the LMFDB. In particular, 
- ```./finecurves_data/finelabels_level3to10.txt``` contains LMFDB labels for fine modular curves of level 3-10, and their corresponding generators are stored in ```./finecurves_data/finecurvesgen_level_3to10.txt```, 
- ```./finecurves_data/finelabels_level11to20.txt``` contains LMFDB labels for fine modular curves of level 11-20, and their corresponding generators are stored in ```./finecurves_data/finecurvesgen_level_11to20.txt```, and 
- ```./finecurves_data/finelabels_level21to30.txt``` contains LMFDB labels for fine modular curves of level 3-10, and their corresponding generators are stored in ```./finecurves_data/finecurvesgen_level_21to30.txt```.

The text file ```test.txt``` contains one line of the format "coarse-label:fine_label," which is most suitable for testing or experimenting purposes. 

To run the code on your local machine, after cloning the directory and initiating Magma, run the command 
```
AttachSpec("CHIMP.spec");

// Change the line below accordingly for your specific use case
// You can do, e.g. InputLabels := "./finecurves_data/finelabels_level3to10.txt"; instead. 
InputLabels := "test.txt"; 
generators := "./finecurves_data/finecurvesgen_level_3to10.txt";
ComputeUnivECModels(InputLabels, generators);
```




