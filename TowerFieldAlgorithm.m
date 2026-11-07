/*
 * Authors: Nuno Freitas, Ignasi Sánchez-Rodríguez
 */

load "GaloisAutomorphismGroup.m";

/**
 * Computes the first n prime numbers.
 * 
 * Parameters:
 * n <- positive integer, the number of primes to compute
 * 
 * Returns:
 * A sequence containing the first n prime numbers starting with 2.
 * 
 * Example:
 * NFirstPrimes(5) returns [2, 3, 5, 7, 11]
**/
function NFirstPrimes(n)
	primes := [2];
	for i in [2 .. n] do
		primes:=Append(primes, NextPrime(primes[i-1]));
	end for;
	return primes;
end function;

/*
 * Computes optimized representation using pari/gp polredbest iterating it maxiter times if deg > 8
 * 
 * Parameters:
 * K <- Number field to optimize
 * 
 * Optional Parameters:
 * maxiter <- Maximum number of iterations for polynomial reduction (default: 10)
 * 
 * Returns:
 * An optimized number field with a reduced discriminant polynomial.
 * The function uses Polred to find a polynomial with smaller discriminant.
 * For polynomials of degree > 8, it iterates the reduction process up to maxiter times.
 * 
 * Note: 
 * Prints the percentage reduction in discriminant achieved.
*/
function OptimizedRepresentation2(K : maxiter := 10)
	f := DefiningPolynomial(K);
	origDisc := Discriminant(f);
	if Degree(f) gt 8 then
		f2 := f;
		i := 1;
		repeat
			f := f2;
			f2, _, _ := Polred(f);
			d := Abs(Discriminant(f));
			d2 := Abs(Discriminant(f2));
			i +:= 1;
		until (Abs(d-d2) lt 10) or (i ge maxiter);
		f := f2;
	else
		f := Polred(f); // f is polredabs
	end if;

	print Sprintf("Optimized rep reduced discriminant of f by %2o %%.", origDisc / Discriminant(f) * 100);

	return NumberField(f);
end function;

/**
 * Computes all 1-dimensional invariant subspaces of a module M under the action of a matrix.
 * 
 * Parameters:
 * M <- G-module 
 * mat <- matrix representing the action of a group element
 * p <- prime characteristic
 * 
 * Returns:
 * A set of all 1-dimensional submodules of M that are invariant under the action of mat.
 * The function finds eigenspaces and extracts 1-dimensional submodules from them.
**/
function dim1InvariantSubspaces(M, mat, p)
	vaps := [v[1] : v in SetToSequence(Eigenvalues(mat))];
	spaces := [Eigenspace(mat,v) : v in vaps];
	dim1Submods := [];
	for space in spaces do
		b := Basis(space);
		coefs := CartesianProduct([GF(p) : _  in [1..#b]]);
		// reduce coeffs to projective coords
		mods := {sub<M | &+[c[i]*b[i] : i in [1..#b]]> : c in coefs};
		Append(~dim1Submods, [module : module in mods | Dimension(module) eq 1]);
	end for;

	return 	Set(Flat(dim1Submods));
end function;

/**
 * Computes all 1-dimensional submodules that are invariant under all matrices in mats.
 * 
 * Parameters:
 * M <- G-module
 * mats <- sequence of matrices representing group actions
 * p <- prime characteristic
 * 
 * Returns:
 * The intersection of all 1-dimensional invariant subspaces for each matrix in mats.
 * This gives the 1-dimensional submodules that are invariant under the entire group action.
**/
function computeDim1Submodules(M, mats, p)
	return &meet [dim1InvariantSubspaces(M, mat, p) : mat in mats];
end function;


/**
 * Constructs n-dimensional submodules from (n-1)-dimensional submodules.
 * 
 * Parameters:
 * M <- G-module
 * mats <- sequence of matrices representing group actions
 * N1submod <- (n-1)-dimensional submodule
 * p <- prime characteristic
 * 
 * Returns:
 * A sequence of n-dimensional submodules of M that contain N1submod.
 * The function works by taking the quotient M/N1submod, finding 1-dimensional
 * submodules in the quotient, and lifting them back to M.
**/
function dimNfromDimN1Submod(M, mats, N1submod, p)
	Q, pi := quo<M | N1submod>;
	
	matsInQ := ActionGenerators(Q);
	subs := computeDim1Submodules(Q, matsInQ, p);
	subsOfM := [];
	for s in subs do
		q := Basis(s);
		q := Inverse(pi)(q[1]);
		Append(~subsOfM, sub<M| [M!b : b in Basis(N1submod)] cat [M!q]>);
	end for;

	return subsOfM;
end function;

function dimNfromDimN1Submods(M, mats, N1submods, p)
	return SetToSequence(Set(Flat([dimNfromDimN1Submod(M, mats, N1submod, p) : N1submod in N1submods])));
end function;


/**
 * Computes all submodules of dimension N by iteratively finding maximal submodules.
 * 
 * Parameters:
 * M <- G-module
 * N <- target dimension
 * 
 * Returns:
 * A sequence of all submodules of M having dimension exactly N.
 * The function starts with maximal submodules and recursively computes
 * their maximal submodules until reaching the desired dimension.
**/
function dimNSubmods(M, N)
	subs := MaximalSubmodules(M);
	while Dimension(subs[1]) gt N do
		subs := SetToSequence(Set(Flat([MaximalSubmodules(s) : s in subs])));
	end while;
	return subs;
end function;


/**
 * Computes the G-Module structure of the p-Selmer group KpS.
 * 
 * Parameters:
 * G <- Permutation group of K_i/K
 * phi <- map from G to Galois group Gal(K_i/K).
 * p <- prime for KpS
 * KpS <- p-Selmer group
 * toKpS <- map from K to KpS.
**/
function computeGModuleStructure(G, phi, p, KpS, toKpS)
	// just assume magma version is >= 2.28-5 for now
	gensG := [];
	v1,v2,v3 := GetVersion();
	if v1 ge 2 and v2 ge 28 and v3 ge 5 then
		gensG := eval "SmallestGeneratingSet(G)"; // Magma forces us to do this: if the function is not defined it would throw an error.
	else
		print "Magma version < 2.28-5. Using non-minimal generating set of G.";
		gensG := Generators(G);
	end if;
	Gp, fromGpToG := sub<G|gensG>; // Change G into a group with smaller number of generators.
	assert Order(Gp) eq Order(G);
	
	gensG := [ phi(fromGpToG(g)) : g in Generators(Gp) ];
	
	FF := GF(p);
	mats := [];
	iToKpS := Inverse(toKpS);
	gensOfKpSInK := [iToKpS(KpS.i) : i in [1..Ngens(KpS)]]; // precompute generators of selmer in K.
	for g in gensG do
		mat := [];
		for m in [1..Ngens(KpS)] do
			actionOfG := g(gensOfKpSInK[m]);
			returnToKpS := toKpS(actionOfG);
			Append(~mat, Eltseq(returnToKpS));
		end for;
		Append(~mats, Matrix(FF, mat));
	end for;

	return GModule(Gp, mats), mats;
end function;


/**
 * Function that, given a submodule N of M, it gives back the generators of N
 * as elements in the p-Selmer group KpS.
 *
 * Parameters:
 * M <- KpS with GModule structure
 * N <- Submodule of M
 * KpS <- Selmer Group
**/
function getModuleGeneratorsInSelmer(M, N, KpS)
	gensOfNInM := [Eltseq(M!g) : g in Generators(N)];
	return [&+[Integers()!g[i]*KpS.i : i in [1..#g]] : g in gensOfNInM];
end function;

/**
 * Test whether pp splits completely in the candidate Kummer extension of K.
 *
 * classes  Ordered Selmer classes generating the candidate submodule.
 * lifts    List of field representatives for the first #lifts entries of
 *          classes, initially empty for each candidate.
 * SelToK   Map choosing an integral representative in K for a Selmer class.
 * q        Prime exponent of the Kummer extension.
 * OK       Ring of integers of K, used to reduce the integral lift.
 * L        Presentation of K in which pp is defined (K or Krel).
 * pp       Selected prime ideal of L above a test prime outside S.
 * Fp       Residue field at pp.
 * m        Reduction map at pp with values in Fp.
 * pi       Initially the rational prime below pp. On first use, keep it as a
 *          uniformizer if its valuation is 1, or choose a uniformizer at pp.
 *
 * Compute SelToK(classes[k]) only when the test reaches generator k. This
 * saves the remaining lifts on early rejection and reuses computed lifts at
 * later primes. If a lift reduces to zero, reduce its local unit a/pi^v,
 * where v is its valuation at pp and q divides v.
 *
 * Return isSplit (1 for complete splitting, 0 otherwise), the updated lifts
 * for this candidate, and the updated pi for this prime.
**/
function checkSubmodule(classes, lifts, SelToK, q, OK, L, pp, Fp, m, pi)
	Kx<x> := PolynomialRing(Fp);
	for k in [1..#classes] do
		if k gt #lifts then
			Append(~lifts, SelToK(classes[k]));
		end if;
		a := lifts[k];
		residue := m(OK!a);
		if residue eq 0 then
			a := L!a;
			v := Valuation(a, pp);
			error if v mod q ne 0, "Selmer valuation is not divisible by q.";
			// An integer marks the untested rational prime. Keep it if its valuation at pp is 1.
			if Type(pi) eq RngIntElt then
				pi := L!pi;
				if Valuation(pi, pp) ne 1 then
					pi := L!UniformizingElement(pp);
				end if;
			end if;
			residue := m(a / pi^v);
			assert residue ne 0;
		end if;
		if IsEmpty(Roots(x^q - residue, Fp)) then
			return 0, lifts, pi;
		end if;
	end for;
	return 1, lifts, pi;
end function;

/**
 * Computes the next step in Grenie's algorithm for absolute extensions over Q.
 * 
 * This function implements one iteration of Grenie's algorithm, which constructs
 * the maximal abelian extension of K unramified outside S with bounded residual
 * degrees. It works by:
 * 1. Computing "blessed primes" that violate the residual degree bound
 * 2. Computing the p-Selmer group of K with respect to S
 * 3. Finding the maximal submodule that satisfies splitting conditions at blessed primes
 * 
 * Parameters:
 * K <- Current number field extension
 * S <- Set of rational primes where ramification is allowed
 * P <- Set of rational primes to test for residual degree conditions
 * f <- Residual degree bound (positive integer)
 * 
 * Optional Parameters:
 * q <- Prime characteristic for Selmer group (default: 2)
 *      Should satisfy Gal(K_{i+1}/K_i) ≅ F_q^t for some t
 * 
 * Returns:
 * - Next field in the tower if a proper extension exists
 * - -1 if K_S = K (no further extension possible)
 * 
 * Note: This version works only when the base field K_0 = Q.
 *       For relative extensions, use nextStep_rel instead.
**/ 
function nextStep(K, S, P, f : q := 2, CyclicCheck := false)
	print "Computing ring of integers of base field...";
	t0 := Realtime();
	OK := Integers(K);
	print "Done in", Realtime(t0), "seconds.";
	print "++++";
	print "Computing degree of base field...";
	t0 := Realtime();
	d := Degree(K);
	print "Done in", Realtime(t0), "seconds.";
	print "++++";
	print "Computing Blessed primes:";
	blessedPrimes := [];
	blessedPrimesInQ := [];
	for p in P do
		fact := Factorization(p*OK);
		firstPrimeAbove := fact[1][1];
		// check residual degree
		if d/#fact eq f then
			Append(~blessedPrimes, firstPrimeAbove);
			Append(~blessedPrimesInQ, p);
		end if;
	end for;
	print "The list of Blessed primes for this step is", blessedPrimesInQ;
	print "++++";

	SK := Flat([Factorization(s*OK) : s in S]);
	SK := [p[1] : p in SK];
	Kx<x> := PolynomialRing(K);

	print "Computing p-Selmer group...";
	t0 := Realtime();
	KpS, KToSel := pSelmerGroup(q, Set(SK));
	SelToK := Inverse(KToSel);
	print "Done in", Realtime(t0), "seconds.";
	print "Selmer group has", Ngens(KpS), "generators.";
	print "++++";

	// this means that there is no prime that violates the residual degree bound
	// In this case, the extension is the whole ray class field.
	if #blessedPrimes eq 0 then
		print "Since there are no blessed primes, the extension is the whole ray class field.";
		return AbsoluteField(NumberField([x^q - SelToK(KpS.i) : i in [1..Ngens(KpS)]]));
	end if;

	print "Computing Galois group of K...";
	t0 := Realtime();
	G,m := GaloisAutomorphismGroup(K);
	print "Done in", Realtime(t0), "seconds.";
	print "++++";

	blessedRFs := [* *];
	for p in blessedPrimes do
		Fp, Fpm := ResidueClassField(OK, p);
		Append(~blessedRFs, <p, Fp, Fpm>);
	end for;

	uniformizers := [* p : p in blessedPrimesInQ *];
	print "Computing G-Module structure of Sel_p(K,S)...";
	t0 := Realtime();
	M, mats := computeGModuleStructure(G, m, q, KpS, KToSel);
	print "Done in", Realtime(t0), "seconds.";
	print "Now we eliminate all of the submodules that do not satisfy the residual degree condition...";
	t0 := Realtime();
	j := 1;
	goodSubmodules := [];
	for i in [1..Ngens(KpS)] do
		print "Dimension", i, "of", Ngens(KpS);
		if i eq 1 then
			dim_i_modules := computeDim1Submodules(M, mats, q);
		else
			dim_i_modules := dimNfromDimN1Submods(M, mats, [N : N in goodSubmodules | Dimension(N) eq i-1], q);
		end if;
		if IsEmpty(goodSubmodules) then
			print "There are", #dim_i_modules, "modules of dimension", i;
		else
			print "There are", #dim_i_modules, "modules of dimension", i, "s.t. their all their maximal submodules do not violate the residual degree condition.";
		end if;
	
		newGoodSubmodules := [];
		jj := 1;
		for l in dim_i_modules do
			print "Checking submodule", jj, "of", #dim_i_modules;
			flag := 0;

			classes := getModuleGeneratorsInSelmer(M, l, KpS);
			lifts := [* *];
			for j in [1..#blessedRFs] do
				p, Fp, Fpm := Explode(blessedRFs[j]);
				print p;
				isSplit, lifts, pi := checkSubmodule(classes, lifts, SelToK, q,
					OK, K, p, Fp, Fpm, uniformizers[j]);
				uniformizers[j] := pi;
				if isSplit eq 0 then
					print "    - The prime", p, "is inert.";
					flag := 1;
					break;
				end if;
			end for;

			if flag eq 0 then
				print "  -- This submodule survives";
				Append(~newGoodSubmodules, l);
			end if;

			jj := jj+1;
		end for;

		if IsEmpty(newGoodSubmodules) then
			print "There are no submodules of dimension", i, "that satisfy the residual degree condition. We stop here.";
			break;
		else
			goodSubmodules :=  goodSubmodules cat newGoodSubmodules;
		end if;
	
	end for;

	if IsEmpty(goodSubmodules) then
		print "There are no submodules that satisfy the residual degree condition. K_S is the input field.";
		return -1;
	end if;
	dimOfGoodSubmod := [Dimension(l) : l in goodSubmodules];
	maxdim, idx := Maximum(dimOfGoodSubmod);
	print "Found maximal extension with dimension", maxdim;
	maxDimSubmod := goodSubmodules[idx];
	if maxdim ge 1 then
		gens := getModuleGeneratorsInSelmer(M, maxDimSubmod, KpS);
		print gens;
		return AbsoluteField(NumberField([x^q - SelToK(g) : g in gens]));
	else
		return -1;
	end if;

end function;


/**
 * Select saturated relative prime ideals without losing their base primes.
 *
 * K0 is the fixed base, Krel is the current field as an extension of K0,
 * P lists rational primes (each represents ALL base primes above it),
 * and f is the relative residue-degree bound.
 *
 * Requires Krel/K0 Galois, as checked by nextStep_rel. Tested base primes
 * must be unramified. Returns triples <p, p0, pp>, with p0 above the rational
 * prime p and pp above p0 of relative residue degree f. One pp per p0
 * suffices because the candidate radical subspaces are invariant over K0.
 */
function relativeBlessedPrimes(K0, Krel, P, f)
    OK0 := Integers(K0);
    OKrel := Integers(Krel);
    d_rel := Degree(Krel);
    result := [* *];
    for p in P do
        for baseFactor in Factorization(p*OK0) do
            p0 := baseFactor[1];
            factors := Factorization(
                ideal<OKrel | [OKrel!a : a in Generators(p0)]>
            );
            error if not &and[t[2] eq 1 : t in factors],
                "nextStep_rel: a tested base prime is ramified in K/K0.";
            assert d_rel mod #factors eq 0;
            residueDegree := d_rel div #factors;
            error if residueDegree gt f,
                "nextStep_rel: the current field already exceeds the residue-degree bound.";
            if residueDegree eq f then
                pp := factors[1][1];
                // Certify that this is a prime above the same p0.
                assert &and[Valuation(OKrel!a, pp) gt 0 :
                    a in Generators(p0)];
                Append(~result, <p, p0, pp>);
            end if;
        end for;
    end for;
    return result;
end function;

/**
 * Computes the next step in Grenie's algorithm for relative extensions.
 * 
 * This is the relative version of nextStep, designed for cases where the base
 * field K_0 has degree > 1 over Q. The algorithm works similarly to the absolute
 * case but takes into account the relative structure K/K_0.
 * 
 * The function:
 * 1. Sets up the relative field structure
 * 2. Computes blessed primes relative to the base field K_0
 * 3. Computes the p-Selmer group and its Galois module structure
 * 4. Finds submodules satisfying the relative residual degree conditions
 * 
 * Parameters:
 * K0 <- Base number field (with [K_0:Q] > 1)
 * K <- Current tower field K_i (Galois q-extension of the embedded K_0)
 * S <- Set of rational primes where ramification is allowed
 * P <- Rational test primes outside S; every base prime above each is tested
 * f <- Relative residue-degree bound q^m, with m a nonnegative integer
 * 
 * Optional Parameters:
 * q <- Prime characteristic for Selmer group (default: 2)
 *      Should satisfy Gal(K_{i+1}/K_i) ≅ F_q^t for some t
 * 
 * Returns:
 * - Next field in the tower if a proper extension exists
 * - -1 if K_S = K (no further extension possible)
 * 
 * The relative Galois and unramified-prime hypotheses are checked before use.
 * Note: This function handles the relative case where K_0 ≠ Q.
 *       For absolute extensions over Q, use nextStep instead.
**/ 
function nextStep_rel(K0, K, S, P, f : q := 2)
    error if not IsPrime(q), "nextStep_rel: q must be prime.";
    error if Type(f) ne RngIntElt, "nextStep_rel: f must be an integer.";
    error if f lt 1, "nextStep_rel: f must be positive.";
    if f gt 1 then
        error if PrimeDivisors(f) ne [q],
            "nextStep_rel: f must be a power of q.";
    end if;
    error if q notin S, "nextStep_rel: S must contain q.";
    error if not IsEmpty(Set(S) meet Set(P)),
        "nextStep_rel: tested primes must lie outside S.";

	print "Computing ring of integers of base field and checking subfields...";
	t0 := Realtime();
	hasBase, baseEmbedding := IsSubfield(K0, K);
    error if not hasBase, "nextStep_rel: K0 must embed in K.";
	Krel := RelativeField(K0, K);
    // Use the same embedded K0 for prime and automorphism computations.
    baseGenerators := [baseEmbedding(k) : k in Generators(K0)];
    assert &and[(Krel!baseEmbedding(k)) eq (Krel!k) :
        k in Generators(K0)];
	OK := Integers(K);
	d_rel := Degree(Krel);
	print "Done in", Realtime(t0), "seconds.";
	print "++++";

    // Certify the relative Galois hypothesis before the no-primes branch.
    print "Computing Galois group of K...";
    t0 := Realtime();
    G, m := GaloisAutomorphismGroup(K);
    G := sub<G | [g : g in G |
        &and[m(g)(k) eq k : k in baseGenerators]]>;
    error if #G ne d_rel, "nextStep_rel: K/K0 must be Galois.";
    if #G gt 1 then
        error if not &and[ell eq q : ell in PrimeDivisors(#G)],
            "nextStep_rel: Gal(K/K0) must be a q-group.";
    end if;
    print "Done in", Realtime(t0), "seconds.";
    print "++++";

    print "Computing Blessed primes:";
    blessedPrimes := relativeBlessedPrimes(K0, Krel, P, f);
    print "Blessed primes for this step (rational prime, base prime):",
        [* <entry[1], entry[2]> : entry in blessedPrimes *];
    print "++++";


	SK := Flat([Factorization(s*OK) : s in S]);
	SK := [p[1] : p in SK];

	PolyK<x> := PolynomialRing(K);

	print "Computing p-Selmer group...";
	t0 := Realtime();
	KpS, KToSel := pSelmerGroup(q, Set(SK));
	SelToK := Inverse(KToSel);
	print "Done in", Realtime(t0), "seconds.";
	print "Selmer group has", Ngens(KpS), "generators.";
	print "++++";

	// this means that there is no prime that violates the residual degree condition
	// In this case, the extension is the full elementary Kummer extension.
	if #blessedPrimes eq 0 then
		print "Since there are no blessed primes, the extension is the full elementary Kummer extension.";
		return AbsoluteField(NumberField([x^q - SelToK(KpS.i) : i in [1..Ngens(KpS)]]));
	end if;

	blessedRFs := [* *];
	for entry in blessedPrimes do
		p, p0, pp := Explode(entry);
		Fp, Fpm := ResidueClassField(pp);
		Append(~blessedRFs, <p, p0, Fp, Fpm, pp>);
	end for;

	uniformizers := [* entry[1] : entry in blessedPrimes *];
	print "Computing G-Module structure of Sel_p(K,S)...";
	t0 := Realtime();
	M, mats := computeGModuleStructure(G, m, q, KpS, KToSel);
	print "Done in", Realtime(t0), "seconds.";

	print "Now we eliminate all of the submodules that do not satisfy the residual degree condition...";
	t0 := Realtime();
	j := 1;
	goodSubmodules := [];
	for i in [1..Ngens(KpS)] do
		print "Dimension", i, "of", Ngens(KpS);
		if i eq 1 then
			dim_i_modules := computeDim1Submodules(M, mats, q);
		else
			dim_i_modules := dimNfromDimN1Submods(M, mats, [N : N in goodSubmodules | Dimension(N) eq i-1], q);
		end if;
		if IsEmpty(goodSubmodules) then
			print "There are", #dim_i_modules, "modules of dimension", i;
		else
			print "There are", #dim_i_modules, "modules of dimension", i, "s.t. their all their maximal submodules do not violate the residual degree condition.";
		end if;

		newGoodSubmodules := [];
		jj := 1;
		for l in dim_i_modules do
			print "Checking submodule", jj, "of", #dim_i_modules;
			flag := 0;
			
			classes := getModuleGeneratorsInSelmer(M, l, KpS);
			lifts := [* *];
			for j in [1..#blessedRFs] do
				p, p0, Fp, Fpm, pp := Explode(blessedRFs[j]);
				printf "    Testing base prime %o over %o.\n", p0, p;
				isSplit, lifts, pi := checkSubmodule(classes, lifts, SelToK, q,
					OK, Krel, pp, Fp, Fpm, uniformizers[j]);
				uniformizers[j] := pi;
				if isSplit eq 0 then
					printf "    - The candidate layer does not split completely above %o (over %o).\n", p0, p;
					flag := 1;
					break;
				end if; 
			end for;

			if flag eq 0 then
				print "  -- This submodule survives";
				Append(~newGoodSubmodules, l);
			end if;

			jj := jj + 1;
		end for;

		if IsEmpty(newGoodSubmodules) then
			print "There are no submodules of dimension", i, "that satisfy the residual degree condition. We stop here.";
			break;
		else
			goodSubmodules :=  goodSubmodules cat newGoodSubmodules;
		end if;

	end for;

	if IsEmpty(goodSubmodules) then
		print "There are no submodules that satisfy the residual degree condition. K_S is the input field.";
		return -1;
	end if;
	dimOfGoodSubmod := [Dimension(l) : l in goodSubmodules];
	maxdim, idx := Maximum(dimOfGoodSubmod);
	print "Found maximal extension with dimension", maxdim;
	maxDimSubmod := goodSubmodules[idx];
	if maxdim ge 1 then
		gens := getModuleGeneratorsInSelmer(M, maxDimSubmod, KpS);
		print gens;
		return AbsoluteField(NumberField([x^q - SelToK(g) : g in gens]));
	else
		return -1;
	end if;

end function;

/**
 * Optimized isomorphism test for degree 64 number fields.
 * 
 * This function provides a faster computation of IsIsomorphic specifically
 * for degree 64 fields by using the tower structure and intermediate fields.
 * It's used in the final layer of Grenie's algorithm to verify that the
 * computed field matches the expected nice polynomial representation.
 * 
 * The algorithm works by:
 * 1. Finding intermediate subfields of degrees 8 and 16
 * 2. Establishing the relative structure using these subfields
 * 3. Testing isomorphism in the relative setting, which is more efficient
 * 
 * Parameters:
 * K1 <- First degree 64 number field
 * K2 <- Second degree 64 number field  
 * K32 <- A common degree 32 subfield used in the tower construction
 * 
 * Returns:
 * Boolean indicating whether K1 and K2 are isomorphic.
 * 
 * Note: This specialized function is much faster than the general IsIsomorphic
 *       for degree 64 fields due to the specific tower structure utilized.
**/
function checkDegree64FieldIsomorphism(K1, K2, K32)
	S := Subfields(K32, 16);
	K16 := S[3][1];
	S := Subfields(K16, 8);
	K8 := S[1][1];
	IsSubfield(K8, K16);
	IsSubfield(K8, K32);
	IsSubfield(K16, K32);
	IsSubfield(K8, K1);
	K1rel8 := RelativeField(K8, K1);
	K32rel8 := RelativeField(K8, K32);

	IsSubfield(K32rel8, K1rel8);
	IsSubfield(K32, K1);

	// Same trick for K2:
	IsSubfield(K8, K2);
	K2rel8 := RelativeField(K8, K2);
	IsSubfield(K32rel8, K2rel8);
	IsSubfield(K32, K2);

	// Finally check that K1 and K2 are isomorphic:
	K1rel := RelativeField(K32, K1);
	K2rel := RelativeField(K32, K2);

	return IsIsomorphic(K1rel, K2rel);
end function;