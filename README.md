# Comparing Reducible Representations with mod p image a p-group
## Authors: Freitas, Nuno; Sánchez-Rodríguez, Ignasi.
Our Paper: _this will be in Arxiv soon_

# Prerequisites
You need to download Edgar Costa's polred for Magma
https://github.com/edgarcosta/MagmaPolred

In Magma's v2.28-5 version the function [SmallestGeneratingSet](http://magma.maths.usyd.edu.au/magma/handbook/text/647#7298) was introduced. If your Magma version is one from before, you won't have this function and the code might run slower, depending on how many generators Magma finds for your Galois groups. 


# How to run
After installing the prerequisites and cloning the project, you need to change the spec path for Edgar Costa's code in the file `GreniesAlgorithm.m`. 

` AttachSpec("PathToSpec"); `

You should also change the default `parisize` as it is recommeneded in Edgar Costa's repository. 

The examples in the paper correspond to the procedures `Example3Adic` for the 3-adic example (section 7) and `ExampleOfGrenie` for the validation of our code using Grenié's example (section 6). They are both in [GreniesAlgorithm.m](https://github.com/IgnasiSanchez/ComparingReducibleReps/blob/main/GreniesAlgorithm.m). So, for example, running the example of Grenié would look like this:

```
load "GreniesAlgorithm.m";
middleExtensions := [];
ExampleOfGrenie(~middleExtensions);
```

This fills the list `middleExtensions` with the tower $K_0 \subseteq K_1\subseteq \dots K_S$ for this example. 

To compute the minimal set of primes $T$ one can use `FrobeniusWithRelativeDecGrp.m` for the 3-adic example. Our code for the primes in Grenié's example is not uploaded yet, but it is the same as in the 3-adic example, using Magma's `FrobeniusElement` instead of computing the Decomposition Groups. 

---

We thank John Voight and Stephan Elsenhans for the `GaloisAutomorphismGroup.m` file. This function uses the `GaloisData` from the `GaloisGroup` computations and recovers the automorphisms acting on the field. This function is much faster than using `AutomorphismGroup` in the Galois case. 