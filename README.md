# Comparing Reducible Representations with mod p image a p-group
## Authors: Freitas, Nuno; Sánchez-Rodríguez, Ignasi.
Our Paper: _this will be in Arxiv soon_

# Prerequisites
You need to download Edgar Costa's polred for Magma
https://github.com/edgarcosta/MagmaPolred

In Magma's v2.28-5 version the function [SmallestGeneratingSet](http://magma.maths.usyd.edu.au/magma/handbook/text/647#7298) was introduced. If your Magma version is one from before, you won't have this function and thus we provide the function _MinimalGeneratingSet_ in [GreniesAlgorithm.m](https://github.com/IgnasiSanchez/ComparingReducibleReps/blob/main/GreniesAlgorithm.m) which calls relies on [Gap](https://www.gap-system.org/) calls so you need to have Gap callable from the terminal. The switch between using one or another is done automatically, but one must be able to call Gap from the terminal if the version is below 2.28.5. 


# How to run
After installing the prerequisites and cloning the project, you need to change the spec path for Edgar Costa's code in the file _GreniesAlgorithm.m_. 

The examples in the paper correspond to the procedures _Example3Adic_ for the 3-adic example (section 7) and _ExampleOfGrenie_ for the validation of our code using Grenié's example (section 6). They are both in [GreniesAlgorithm.m](https://github.com/IgnasiSanchez/ComparingReducibleReps/blob/main/GreniesAlgorithm.m). This computes the field tower $K_0 \subseteq K_1\subseteq \dots K_S$ for each one of the examples respectively. 

To compute the minimal set of primes $T$ one can use _FrobeniusWithRelativeDecGrp.m_ for the 3-adic example. Our code for the primes in Grenié's example is not uploaded yet, but it is the same as in the 3-adic example, using Magma's _FrobeniusElement_ instead of computing the Decomposition Groups. 

---

We thank John Voight and Stephan Elsenhans for the _GaloisAutomorphismGroup.m_ file. This function uses the _GaloisData_ from the _GaloisGroup_ computations and recovers the automorphisms acting on the field. This function is much faster than using _AutomorphismGroup_ in the Galois case. 

