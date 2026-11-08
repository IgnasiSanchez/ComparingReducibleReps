# Comparing Galois representations in the residually reducible case

Magma code for the paper by Nuno Freitas and Ignasi Sánchez-Rodríguez. The examples construct the tower of number fields used to compare two $p$-adic Galois representations with residual image a $p$-group. The resulting primes specify where to compare Frobenius characteristic polynomials or, in the cases covered by the paper, traces. [Paper on arXiv](https://arxiv.org/abs/2510.12956)

## Run the examples

The paper used Magma V2.28-20. The tower examples also require PARI/GP (`gp` on your path) and Edgar Costa’s MagmaPolred package. In the example file you want to run, replace `AttachSpec("spec");` with the path to the package’s `spec` file, for example `AttachSpec("/path/to/MagmaPolred/spec");`. The package documents an optional `parisize` setting for larger fields. [MagmaPolred setup](https://github.com/edgarcosta/MagmaPolred#prerequisites)

Start Magma in the repository directory. For the example without GRH, **start a fresh Magma session** so it uses the default unconditional class-group bounds. The other two drivers set `SetClassGroupBounds("GRH");` for their class-group computations. [Magma handbook](https://magma.maths.usyd.edu.au/magma/handbook/text/416)

| Example | Command at the Magma prompt | Expected result |
| --- | --- | --- |
| [3-adic without GRH](Example3AdicWithoutGRH.m) over $\mathbb Q(\sqrt{-3})$ (§§7–8) | `load "Example3AdicWithoutGRH.m";` | Absolute degrees $2,18,54$. Stops at degree $54$ using Theorem 8.1, since the last layer is cyclic of degree $3$. |
| [Same 3-adic tower with GRH](Example3Adic.m) (§7) | `load "Example3Adic.m";` | Continues from degree $54$ and tests the next layer for stabilization. |
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

## Compute primes for another field

For a finite Galois extension $L/\mathbb Q$ given as an absolute number field, load the function directly. It uses Magma’s `FrobeniusElement` and runs independently of the tower and MagmaPolred. [FrobeniusPrimeSets.m](FrobeniusPrimeSets.m)

```magma
load "FrobeniusPrimeSets.m";
T, Tprime, frob := FrobeniusPrimeSets(L, S, n);
```

`S` is a sequence or set of excluded rational primes and `n` is the representation dimension. The search skips ramified primes and those in `S`. With `Candidates := primes`, it searches the supplied primes in increasing order and reports an error if coverage is incomplete.

- **$T$ (characteristic polynomials).** For each conjugacy class of maximal cyclic subgroups, take the first eligible prime whose Frobenius generates a subgroup in that class.
- **$T'$ (traces of powers).** For the generators $g$ selected for $T$, take the first eligible prime in each distinct nonidentity conjugacy class of $g^k$, for $1\leq k\leq n$. If the determinants are known to agree, `EqualDeterminants := true` uses $k\leq n-1$.
- **`frob` (optional).** For a prime in either list, `frob[p]` gives its Frobenius element in the common permutation group. This verifies coverage in $\operatorname{Gal}(L/\mathbb Q)$. Using an alternative $T'$ for a trace-only comparison also requires justifying the passage to traces of powers of the same lift in the absolute Galois group (Remark 4.2).

For the relative 3-adic example, a separate script computes Frobenius elements via decomposition groups in the fixed degree-$54$ field. Corollary 1.1 uses five **prime ideals** of $\mathbb Q(\sqrt{-3})$, namely the prime over $2$, both primes over $7$, and one prime each over $19$ and $73$. [FrobeniusWithRelativeDecGrp.m](FrobeniusWithRelativeDecGrp.m)

## Tower parameters and stopping

The drivers construct the first layer from a Selmer group. For subsequent layers, `nextStep(Ki, S, P, f)` works over $\mathbb Q$ with `q := 2` by default. The 3-adic driver calls `nextStep_rel(K0, Ki, S, P, f : q := 3)` with fixed base $K_0=\mathbb Q(\sqrt{-3})$ and current field $K_i$ given in absolute form. The construction assumes that $K_0$ contains the $q$-th roots of unity and $K_i/K_0$ is a Galois $q$-extension. [TowerFieldAlgorithm.m](TowerFieldAlgorithm.m)

Here `S` lists the rational primes where ramification is allowed and includes `q`. The working list `P` tests candidate layers against the residue-degree bound `f` ($4$ for Grenié, $3$ in the 3-adic example). Over a number field, the sieve considers every prime of $K_0$ above each prime in `P`. Following Grenié’s original computation, the drivers take the first 20 rational primes, through $71$, and remove the ramified prime, leaving 19. The worked calculations in §§6–7 use a cutoff of $100$. The final search for $T$ and $T'$ can use larger primes, as $337$ illustrates.

A tower step returns the next field, or `-1` if the sieve eliminates every nonzero candidate. For a new example, identifying the output with $K_S$ requires the exponent and stopping arguments of §§4–5. The 3-adic shortcut in §8 uses the cyclic last layer of that particular tower.

On Magma versions before V2.28-5, the tower code falls back to `Generators` in place of `SmallestGeneratingSet`. Extra group generators can make the Selmer-module computations slower.

## Acknowledgements

We thank John Voight and Stephan Elsenhans for the code that recovers field automorphisms from Magma’s Galois group data. [GaloisAutomorphismGroup.m](GaloisAutomorphismGroup.m)
