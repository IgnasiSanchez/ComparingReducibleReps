/*
 * Authors: Nuno Freitas, Ignasi Sánchez-Rodríguez
 */

SetClassGroupBounds("GRH");
load "GaloisAutomorphismGroup.m";
AttachSpec("spec"); // Necessary: https://github.com/edgarcosta/MagmaPolred
SetNthreads(4);

function NFirstPrimes(n)
	primes := [2];
	for i in [2 .. n] do
		primes:=Append(primes, NextPrime(primes[i-1]));
	end for;
	return primes;
end function;

/*
 * Computes optimized representation using pari/gp polredbest iterating it maxiter times if deg > 8
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


/*
 * Computes the minimal generating set for a group G using Gap's MinimalGeneratingSet
*/
function MinimalGeneratingSet(G)
	d := Order(G);
	if d gt SmallGroupDatabaseLimit() and CanIdentifyGroup(G) then
		error "Group is too large. See Magma example GrpData_IdentifyGroup (H72E4) for more information.";
	end if;
	tag := IdentifyGroup(G);
	idx := tag[2];
	SG := SmallGroup(d,idx);
	_,phi := IsIsomorphic(SG,G);

	v1,v2,v3 := GetVersion();
	// if v1 ge 2 and v2 ge 28 and v3 ge 5 then
	// 	// Magma 2.28-5 or later
	// 	// try
	// 	// 	idx := SmallestGeneratingSet(SG);
	// 	// 	return [phi(g) : g in idx];
	// 	// catch e
	// 	// 	print "Magma version < 2.28-5";
	// 	// end try;
	// end if;	

	// If Magma version is earlier than 2.28-5 we need to call Gap to do the minimal generating set computations.

	s := Pipe("gap -q", Sprintf("G := SmallGroup(%o,%o); GeneratorsOfGroup(G); MinimalGeneratingSet(G);", d, idx));
	System("printf \"\\e[0m\""); // console colors are weird after calling gap...

	i0 := Index(s, "\n");
	s := s[i0+1..#s];
	gens := s[ Index(s, "[")+1 .. Index(s, "]")-1 ];
	gens := [StripWhiteSpace(g) : g in Split(gens, ",")];
	s2 := s[ Index(s, "]")+1..#s];
	minGens := s2[ Index(s2, "[")+1 .. Index(s2, "]")-1 ];
	minGens := [StripWhiteSpace(g) : g in Split(minGens, ",")];
	gensSG := Generators(SG);
	assert #gensSG eq #gens;

	newMinGens := [];
	for g in minGens do
	    seq := Eltseq(g);
		for i in [1..#seq] do
			if seq[i] eq "f" then
				seq[i] := "SG.";
			end if;
		end for;
		Append(~newMinGens, &cat(seq));
	end for;
	
	minGensSG := [eval g : g in newMinGens];

	assert Order(sub<SG|minGensSG>) eq d;

	return [phi(g) : g in minGensSG];

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
	gensG := [ phi(g) : g in SmallestGeneratingSet(G) ];
	Gp := sub<G|gensG>;
	assert Order(Gp) eq Order(G);
	FF := GF(p);
	//mats := [ Matrix(FF, [ Eltseq(toKpS(g((KpS.m)@@toKpS))) : m in [1..Ngens(KpS)] ]) : g in gensG ];
	mats := [];
	iToKpS := Inverse(toKpS);
	gensOfKpSInK := [iToKpS(KpS.i) : i in [1..Ngens(KpS)]];
	for g in gensG do
		mat := [];
		for m in [1..Ngens(KpS)] do
			actionOfG := g(gensOfKpSInK[m]);
			returnToKpS := toKpS(actionOfG);
			Append(~mat, Eltseq(returnToKpS));
		end for;
		Append(~mats, Matrix(FF, mat));
	end for;
	M := GModule(Gp, mats);
	S := Submodules(M);
	L := SubmoduleLattice(M);

	return M, S, L;
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
 * Checks the Goodness of Submodule. That is, given a submodule S,
 * let Oe be the set of generators from the function above 
 * and a prime p in K, it checks whether p is split or inert in K(Oe).
 * It returns 0 if the prime is inert and 1 if the prime is split.
 *
 * Parameters:
 * K <- number field we are working on.
 * M <- GModule strcture on KpS.
 * S <- Submodule of M we want to test.
 * KpS <- SelmerGroup
 * SelToK <- inverse map from second output in pSelmerGroup.
 * q <- Degree of the extension.
 * Fp <- Ring OK/p
 * m <- Map obtained from ResidueClassField

 * Optional Parameters:
 * OK <- Ring of Integers of K. If not provided, it will be computed.
**/
function checkSubmodule(K, M, S, KpS, SelToK, q, Fp, m : OK := {})

	if Type(OK) eq Type({}) then
		OK := Integers(K);
	end if;

	Kx<x> := PolynomialRing(Fp);
	try
		O := getModuleGeneratorsInSelmer(M, S, KpS);
	catch e
		print M;
		print S;
		print KpS;
		print e;
	end try;

	for e in O do
		IrrE := x^q - m(OK!SelToK(e));
		r := Roots(IrrE, Fp);
		if #r eq 0 then
			return 0;
		end if;
	end for;

	return 1;

end function;

/**
 * Given an extension K, it computes the next step in Grenie's algorithm. 
 * If there is no next step, it returns -1 (which would mean K_S = K).
 * This works when the base field K_0 = Q only.
 * 
 * Parameters:
 * K <- Current extension.
 * S <- Set of primes of Q where we allow ramification.
 * P <- Set of primes of Q to test the residual degree conditions.
 * f <- residual degree bound (integer)
 * Optional Parameters:
 * q <- Prime such that Gal(K_{i+1}/K_i) = F_q^t for some t. Default is 2.
**/ 
function nextStep(K, S, P, f : q := 2)
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

	print "Computing G-Module structure of Sel_p(K,S)...";
	t0 := Realtime();
	M, S, L := computeGModuleStructure(G, m, q, KpS, KToSel);
	print "Done in", Realtime(t0), "seconds.";
	print "The Lattice contains", #S, "submodules.";
	for i in [1..Ngens(KpS)] do
		print "The Lattice contains", #[l : l in L | Dimension(l) eq i], "submodules of dimension", i;
	end for;
	print "++++";
	print "Now we eliminate all of the submodules that do not satisfy the residual degree condition...";
	t0 := Realtime();
	j := 1;
	goodSubmodules := [];
	for i in [1..Ngens(KpS)] do
		print "Dimension", i, "of", Ngens(KpS);
		if IsEmpty(goodSubmodules) then
			dim_i_modules := [l : l in L | Dimension(l) eq i];
		else
			dim_i_modules := [l : l in L | Dimension(l) eq i and
			&and[Module(L!mm) in goodSubmodules : mm in MaximalSubmodules(l)]];
			print "There are", #dim_i_modules, "modules of dimension", i, "s.t. their all their maximal submodules do not violate the residual degree condition.";
		end if;
	
		newGoodSubmodules := [];
		jj := 1;
		for l in dim_i_modules do
			print "Checking submodule", jj, "of", #dim_i_modules, "(id", l, ")";
			flag := 0;

			for rf in blessedRFs do
				p := rf[1];
				Fp := rf[2];
				Fpm := rf[3];
				isSplit := checkSubmodule(K, M, Module(L!l), KpS, SelToK, q, Fp, Fpm: OK := OK);
				if isSplit eq 0 then
					print "    - The prime", p, "is inert.";
					flag := 1;
					break;
				end if;
			end for;

			if flag eq 0 then
				print "  -- This submodule survives";
				Append(~newGoodSubmodules, Module(L!l));
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
		gens := getModuleGeneratorsInSelmer(M, Module(L!maxDimSubmod), KpS);
		print gens;
		return AbsoluteField(NumberField([x^q - SelToK(g) : g in gens]));
	else
		return -1;
	end if;

end function;


/**
 * Given an extension K, it computes the next step in Grenie's algorithm. 
 * If there is no next step, it returns -1 (which would mean K_S = K).
 * This works when the base field [K_0:Q] > 1. 
 * 
 * Parameters:
 * K0 <- Base field. 
 * K <- Current extension.
 * S <- Set of primes of Q where we allow ramification.
 * P <- Set of primes of Q to test the residual degree conditions.
 * f <- residual degree bound (integer)
 * Optional Parameters:
 * q <- Prime such that Gal(K_{i+1}/K_i) = F_q^t for some t. Default is 2.
**/ 
function nextStep_rel(K0, K, S, P, f : q := 2)

	print "Computing ring of integers of base field and checking subfields...";
	t0 := Realtime();
	_ := IsSubfield(K0, K);
	Krel := RelativeField(K0, K);
	OK := Integers(K);
	OKrel := Integers(Krel);
	OK0 := Integers(K0);
	d_rel := Degree(Krel);
	d_abs := Degree(K);
	print "Done in", Realtime(t0), "seconds.";
	print "++++";

	print "Computing Blessed primes:";
	blessedPrimes := [];
	for p in P do
		pK0 := Factorization(p*OK0)[1][1];
		pK := Factorization(ideal<OKrel | [OKrel!g : g in Generators(pK0)]>);

		// check residual degree
		if d_rel/#pK eq f then
			Append(~blessedPrimes, p);
		end if;
	end for;
	print "The list of Blessed primes for this step is", blessedPrimes;
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
	// In this case, the extension is the whole ray class field.
	if #blessedPrimes eq 0 then
		print "Since there are no blessed primes, the extension is the whole ray class field.";
		return AbsoluteField(NumberField([x^q - SelToK(KpS.i) : i in [1..Ngens(KpS)]]));
	end if;

	print "Computing Galois group of K...";
	t0 := Realtime();
	//G,_,m := AutomorphismGroup(Krel);
	G,m := GaloisAutomorphismGroup(K);
	// we want the relative group:
	G:=sub<G | [g : g in G | &and[m(g)(k) eq k : k in Generators(K0)]]>;
	print "Done in", Realtime(t0), "seconds.";
	print "++++";
	

	blessedRFs := [* *];
	for p in blessedPrimes do
		pp := Factorization(p*OKrel)[1][1];
		Fp, Fpm := ResidueClassField(pp);
		Append(~blessedRFs, <p, Fp, Fpm>);
	end for;

	print "Computing G-Module structure of Sel_p(K,S)...";
	t0 := Realtime();
	M, S, L := computeGModuleStructure(G, m, q, KpS, KToSel);
	print "Done in", Realtime(t0), "seconds.";
	print "The Lattice contains", #S, "submodules.";
	for i in [1..Ngens(KpS)] do
		print "The Lattice contains", #[l : l in L | Dimension(l) eq i], "submodules of dimension", i;
	end for;
	print "++++";

	print "Now we eliminate all of the submodules that do not satisfy the residual degree condition...";
	t0 := Realtime();
	j := 1;
	goodSubmodules := [];
	for i in [1..Ngens(KpS)] do
		print "Dimension", i, "of", Ngens(KpS);
		if IsEmpty(goodSubmodules) then
			dim_i_modules := [l : l in L | Dimension(l) eq i];
		else
			dim_i_modules := [l : l in L | Dimension(l) eq i and 
        		&and[Module(L!mm) in goodSubmodules : mm in MaximalSubmodules(l)]];
			print "There are", #dim_i_modules, "modules of dimension", i, "s.t. their all their maximal submodules do not violate the residual degree condition.";
		end if;

		newGoodSubmodules := [];
		jj := 1;
		for l in dim_i_modules do
			print "Checking submodule", jj, "of", #dim_i_modules, "(id", l, ")";
			flag := 0;
			
			for rf in blessedRFs do
				p := rf[1];
				print p;
				Fp := rf[2];
				Fpm := rf[3];
				isSplit := checkSubmodule(K, M, Module(L!l), KpS, SelToK, q, Fp, Fpm: OK := OK);
				if isSplit eq 0 then
					print "    - The prime", p, "is inert.";
					flag := 1;
					break;
				end if; 
			end for;

			if flag eq 0 then
				print "  -- This submodule survives";
				Append(~newGoodSubmodules, Module(L!l));
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
		gens := getModuleGeneratorsInSelmer(M, Module(L!maxDimSubmod), KpS);
		print gens;
		return AbsoluteField(NumberField([x^q - SelToK(g) : g in gens]));
	else
		return -1;
	end if;

end function;

/*
 * This is a faster computation of IsIsomorphic when K1 and K2 are two degree 64 fields
 * Used in last layer of Grenié to compute the isomorphism between the output and the nice polynomial. 
 */
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


/*
 *  Grenié's example as in his paper and ours.
 */
procedure ExampleOfGrenie(~middleExtensions)
	q := 2;
	K := Rationals();
	S := [2];
	P := NFirstPrimes(20);
	Exclude(~P, 2);
	f := 4;

	KpS, KToSel := pSelmerGroup(q, Set(S));
	SelToK := Inverse(KToSel);
	Qx<x> := PolynomialRing(K);
	L:=AbsoluteField(NumberField([x^q - SelToK(KpS.i) : i in [1..Ngens(KpS)]]));


	middleExtensions := [* K, L *];
	while not (Type(L) eq Type(-1)) do
		print "";
		print "*******************************************************";
		print "";
		print "++++";
		print "Current Base Field:", L;
		print "++++";
		t0 := Realtime(); 
		if Degree(L) eq 64 then
			SetProfile(true);
		end if;
		L := nextStep(L, S, P, f);
		print "++++";
		print "Current step took", Realtime(t0), "seconds.";
		print "++++";
		print L;
		print "++++";
		print "Computing Optimized Representation...";
		if Type(L) ne Type(-1) and Degree(L) eq 64 then
			f2 := x^64 - 16*x^62 + 104*x^60 - 304*x^58 +
				344*x^56 + 496*x^54 + 568*x^52 - 48*x^50 + 1248*x^48 + 10336*x^46 +
				11720*x^44 + 17536*x^42 + 14168*x^40 + 52608*x^38 + 27320*x^36 - 19520*x^34
				- 8414*x^32 + 50224*x^30 + 243496*x^28 - 208624*x^26 - 259016*x^24 +
				244784*x^22 + 175544*x^20 - 204656*x^18 - 4384*x^16 + 55712*x^14 - 8248*x^12
				- 9920*x^10 + 4472*x^8 - 576*x^6 - 8*x^4 + 1;
			K2 := NumberField(f2);
			assert checkDegree64FieldIsomorphism(L, K2, middleExtensions[#middleExtensions]);
			L := K2;
		elif Type(L) ne Type(-1) then
			L := OptimizedRepresentation2(L);
		else
			print "We found K_S = K_{i-1}.";
			break;
		end if;
		print L;
		print "++++";
		Append(~middleExtensions, L);
	end while;
end procedure;

/*
 * The 3-adic example explained in our paper.
 */
procedure Example3Adic(~middleExtensions)
	q := 3;
	PolyQ<x> := PolynomialRing(Rationals());
	K<a> := NumberField(x^2 - x + 1);
	S := [3];
	P := NFirstPrimes(20);
	Exclude(~P, 3);
	f := 3;

	SK := Flat([Factorization(s*Integers(K)) : s in S]);
	SK := [p[1] : p in SK];
	KpS, KToSel := pSelmerGroup(q, Set(SK));
	SelToK := Inverse(KToSel);
	PolyK<x> := PolynomialRing(K);
	L:=AbsoluteField(NumberField([x^q - SelToK(KpS.i) : i in [1..Ngens(KpS)]]));


	middleExtensions := [* K, L *];
	while not (Type(L) eq Type(-1)) do 
		print "";
		print "*******************************************************";
		print "";
		print "++++";
		print "Current Base Field:", L;
		print "++++";
		t0 := Realtime(); 
		L := nextStep_rel(K, L, S, P, f : q := 3);
		print "++++";
		print "Current step took", Realtime(t0), "seconds.";
		print "++++";
		print L;
		print "++++";
		if Type(L) eq Type(-1) then
			print "We found K_S = K_{i-1}.";
			break;
		end if;
		print "Computing Optimized Representation...";
		L:=OptimizedRepresentation2(L);
		print L;
		Append(~middleExtensions, L);
	end while;
end procedure;

// Gal group of last layer of Grenié's example is [64, 34] https://people.maths.bris.ac.uk/~matyd/GroupNames/61/C4%5E2sC4.html
// Gal group of last layer of 3-adic example is [54, 5] https://people.maths.bris.ac.uk/~matyd/GroupNames/1/C3%5E2sC6.html

middleExtensions := [];
//ExampleOfGrenie(~middleExtensions);
//Example3Adic(~middleExtensions);

