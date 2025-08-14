# Comparing Reducible Representations with mod p image a p-group

Our Paper: _this will be in Arxiv soon_

# Prerequisites
You need to download Edgar Costa's polred for Magma
https://github.com/edgarcosta/MagmaPolred

The code also relies on [Gap](https://www.gap-system.org/) calls so you need to have Gap callable from the terminal. The Gap code is only used to compute the minimal generators of a group, which is available in the current version of Magma. You might want to change it if your Magma is updated, otherwise you can use Gap's function. There will be an automatich switch here in the future when this project is made into a package _soon_. 


# How to run
After installing the prerequisites and cloning the project, you need to change the spec path for Edgar Costa's code in the file _GreniesAlgorithm.m_. 

You can run the procedures _mod3Example_ and _GreniesExample_ as it is commented in the last lines of the file _GreniesAlgorithm.m_. 

---

We thank John Voight and Stephan Elsenhans for the _GaloisAutomorphismGroup.m_ function which speeds up the code inmensely. 

