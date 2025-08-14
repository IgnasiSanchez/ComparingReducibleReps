/**
 * Code by Stephan Elsenhans @ Magma
 * 
**/

/* GalAuto.m : Construct field automorphisms out of Galois Data */

function my_eval(f,x, modul)
	n := Degree(f);
	res := Coefficient(f,n);
	while n gt 0 do
		n := n - 1;
		res := (x*res + Coefficient(f,n)) mod modul;
	end while;
	return res;
end function;


// The automotphism of K that corresponds to a permutation with 1 |-> i
function PointToAutomorphism(K,G,S,i)

	vprint GaloisGroup,1:"Computing automorphism that maps 1st root to root Nr",i;
	G1 := Stabilizer(G,1);
	tran,t_map := Transversal(G,G1);
	sigma := [a : a in tran | 1^a eq i];
	assert #sigma eq 1;
	sigma := sigma[1];

	arg_nr := [1^a : a in tran];
	im_nr := [1^(sigma*a) : a in tran];

	rts := [GaloisRoot(i,S) : i in [1..Degree(G)]];
	k,pi := ResidueClassField(Parent(rts[1]));
	rts := [pi(a) : a in rts]; 
	p := S`Prime;
	pol := PolynomialRing(Integers())!Interpolation(rts[arg_nr], rts[im_nr]); 
	prec := 1;
	min_poly := DefiningPolynomial(K);
	if assigned S`Scale then
		Scale := S`Scale;
		min_poly := Evaluate(min_poly, PolynomialRing(Rationals()).1 / Rationals()!Scale);
		min_poly := min_poly / LeadingCoefficient(min_poly);
	else
		Scale := 1; 
	end if; 
	min_poly := PolynomialRing(Integers())!min_poly;
	K2 := NumberField(min_poly);
	ord := EquationOrder(K2);
	mul := ord!Evaluate(Derivative(min_poly), K2.1);    
	im_rt := ord!Evaluate(pol, K2.1);
	im_der := ord!Evaluate(Derivative(pol),K2.1);

	assert Discriminant(PolynomialRing(GF(p))!min_poly) ne 0;
	qu,pi := quo<ord | p*ord>;

	mul_inv := 1 / mul;
	d_mp := Derivative(min_poly);
	fs_inv := (1/Evaluate(d_mp,pi(im_rt))) @@ pi;
	modul := p;
	mod_id := modul*ord;
	im_rt_scal := im_rt * mul mod mod_id; 
	ex := 1;

	lift_bound := 2*FujiwaraBound(min_poly) * Degree(min_poly) * 
				Sqrt(&+[a^2  : a in Coefficients(min_poly)]) / LeadingCoefficient(min_poly);
	max_lift_prec := Ceiling(Log(lift_bound) / Log(p));

	repeat
		repeat
			ex := ex*2;
			vprint GaloisGroup,1:"Lifting image of generator to precision",ex;
			modul := modul^2;
			mod_id := modul*ord;
			f_val := my_eval(min_poly,im_rt,mod_id);
			im_rt := (im_rt - f_val * fs_inv) mod mod_id; // im_rt with new precision 
			fs_val := my_eval(d_mp,im_rt,mod_id);
			// fs_inv := fs_inv - (fs_val * fs_inv - 1) * fs_inv; 
			fs_inv := (2*fs_inv - fs_val * (fs_inv^2 mod mod_id) ) mod mod_id; // lift the inverse of the derivative
			im_rt_scal := (im_rt * mul) mod mod_id; 
			co_rec := [2*a gt modul select a - modul else a where a is Integers()!b mod modul : b in Eltseq(im_rt_scal)];
		until (ex ge max_lift_prec) or Max([AbsoluteValue(a) : a in co_rec])*10^6 lt modul; 
			res := (ord!co_rec) * mul_inv;
			test := Evaluate(min_poly,res); 
			assert (test eq 0) or (ex lt max_lift_prec);
			assert Max([AbsoluteValue(a) : a in co_rec]) lt lift_bound;
	until test eq 0;
		gen := Evaluate(Polynomial(Eltseq(res)),K.1*Scale) / Scale; //Image of K.1ç
	
	return hom<K -> K | gen>;
end function;

function GaloisAutomorphismGroup(K : Galois := false)
	if Galois cmpeq false then
		G, r, S := GaloisGroup(K);
	else
		G,r,S := Explode(Galois);
	end if;

	assert IsTransitive(G);
	assert S`Type eq "p-Adic"; // other cases are not implemented
	G1 := Stabilizer(G,1); 
	Fix := &join [a : a in Orbits(G1) | #a eq 1];
	G_bl := Stabilizer(G,Fix);
	phi := Action(G_bl,GSet(G_bl,Fix));
	aut_grp,pi := StandardGroup(Image(phi));
	assert IsRegular(aut_grp); 

	ReduceGenerators(~aut_grp);
	gen := GeneratorsSequence(aut_grp);
	image_gens := [PointToAutomorphism(K,G,S,1^((g @@ pi) @@ phi)) : g in gen];
	image_inv := [(Order(gen[i]) le 2) select 
						image_gens[i] else hom<K -> K | (image_gens[i]^(Order(gen[i]) -1))(K.1)> 
						: i in [1..#gen]];
	FG,iso := FPGroup(aut_grp); 
	return aut_grp, map<aut_grp ->  Aut(K) | g :-> &*([(c gt 0) select image_gens[c] else image_inv[-c] 
													: c in Eltseq(g@@iso)] cat [hom<K -> K | u :-> u>])>;

// return aut_grp, map<aut_grp ->  Aut(K) | g :-> PointToAutomorphism(K,G,S,1^((g @@ pi) @@ phi))>;
end function;
