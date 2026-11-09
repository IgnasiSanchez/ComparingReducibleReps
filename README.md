# Comparing Galois representations in the residually reducible case

Magma code for the paper by Nuno Freitas and Ignasi Sánchez-Rodríguez. [Paper on arXiv](https://arxiv.org/abs/2510.12956)

## Run the examples

- The paper used `Magma V2.28-20`. 
- The tower examples also require PARI/GP (`gp` on your path) and Edgar Costa’s [MagmaPolred](https://github.com/edgarcosta/MagmaPolred) package. In the example file you want to run, replace `AttachSpec("spec");` with the path to the package’s `spec` file, for example `AttachSpec("/path/to/MagmaPolred/spec");`. The package [documents](https://github.com/edgarcosta/MagmaPolred#prerequisites) an optional `parisize` setting for larger fields which should be changed for these examples to run.


| Example | Command at the Magma prompt | Expected result |
| --- | --- | --- |
| [3-adic without GRH](Example3AdicWithoutGRH.m) over $\mathbb Q(\sqrt{-3})$ (§§7–8) | `load "Example3AdicWithoutGRH.m";` | Absolute degrees $2,18,54$. Stops at degree $54$ using Theorem 8.1, since the last layer is cyclic of degree $3$. |
| [Same 3-adic tower with GRH](Example3Adic.m) (§7) | `load "Example3Adic.m";` | Same tower field as in the previous example but it continues checking that there is no more layers after the field of absolute degree 54. |
| [Grenié’s 2-adic example](ExampleOfGrenie.m) over $\mathbb Q$, with GRH (§6) | `load "ExampleOfGrenie.m";` | Absolute degrees $1,4,32,64$. Checks the degree-$64$ field against the reference polynomial and prints $T$ and $T'$ after stabilization. |

Each driver stores the fields in `middleExtensions`, starting with $K_0$ at index 1. After the 3-adic run, for example, you can inspect the degrees and recover the last field with

```magma
[ AbsoluteDegree(F) : F in middleExtensions ];  // [ 2, 18, 54 ]
L := middleExtensions[#middleExtensions];
```

## Reproduce Grenié’s prime lists

The default search takes the smallest eligible prime for each class it needs. On the degree-$64$ field the driver prints

```text
T  = [ 3, 5, 7, 17, 23, 31 ]
T' = [ 3, 5, 7, 11, 13, 17, 23, 31, 41, 73, 113, 337 ]
```

To reproduce Grenié’s published lists, run the following after `ExampleOfGrenie.m`. The last assertion checks the role of $13$ in $T'$ directly in the finite Galois group. Its Frobenius is conjugate to $\mathrm{Frob}_5^3$. [Grenié, §4.2](https://arxiv.org/abs/math/0506053)

```magma
L := middleExtensions[#middleExtensions];
primes := [5,7,11,13,17,19,23,31,73,137,257,337];
T, Tprime, frob := FrobeniusPrimeSets(L, [2], 3 : Candidates := primes);
assert T eq [5,7,11,17,23,31];
assert Tprime eq primes;
assert frob[5]^3 in Class(Parent(frob[5]), frob[13]);
```

## Compute a new example

Save this as `MyExample.m`, set the MagmaPolred path, and run `load "MyExample.m";` from the repository directory. Edit the inputs for your example. The base field must contain the $q$-th roots of unity.

```magma
AttachSpec("/path/to/MagmaPolred/spec");
load "TowerFieldAlgorithm.m";
load "FrobeniusPrimeSets.m";

// Inputs
K0 := Rationals();  // or, for example, QuadraticField(-1) when q = 2
q := 2;
n := 2;
S := [2];           // rational primes, including q
P := [p : p in NFirstPrimes(20) | p notin S];
f := q;
while f lt n do
    f *:= q;        // No need to compute m (minimum exponent such that q^m >= n).
end while;

// At K0 every relative residue degree is 1 < f, so the first step takes the full Selmer radical.
overQ := AbsoluteDegree(K0) eq 1;
L := K0;
middleExtensions := [* K0 *];

while true do
    if overQ then
        Knext := nextStep(L, S, P, f : q := q);
    else
        Knext := nextStep_rel(K0, L, S, P, f : q := q);
    end if;
    if Knext cmpeq -1 then break; end if;
    L := OptimizedRepresentation2(Knext);
    Append(~middleExtensions, L);
end while;

if overQ then
    T, Tprime := FrobeniusPrimeSets(L, S, n);
    print "T =", T;
    print "T' =", Tprime;
end if;
```

Before identifying `L` with $K_S$, check the exponent and stopping hypotheses in §§4–5. Over $\mathbb Q$, `Tprime` records Frobenius power classes in the finite quotient. A trace-only comparison also needs a justification for the Frobenius lifts (Remark 4.2). For relative prime lists, see the [§7 example](FrobeniusWithRelativeDecGrp.m).

## Acknowledgements

We thank John Voight and Stephan Elsenhans for the code that recovers field automorphisms from Magma’s Galois group data. [GaloisAutomorphismGroup.m](GaloisAutomorphismGroup.m)
