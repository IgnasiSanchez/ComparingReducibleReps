AttachSpec("spec"); // Necessary: https://github.com/edgarcosta/MagmaPolred
SetNthreads(4);
load "TowerFieldAlgorithm.m";

// Algorithm parameters for the 3-adic example
q := 3;
PolyQ<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x + 1);
S := [3];
P := NFirstPrimes(20);
Exclude(~P, 3);
f := 3;

// First layer of the tower
SK := Flat([Factorization(s*Integers(K)) : s in S]);
SK := [p[1] : p in SK];
KpS, KToSel := pSelmerGroup(q, Set(SK));
SelToK := Inverse(KToSel);
PolyK<x> := PolynomialRing(K);
L:=AbsoluteField(NumberField([x^q - SelToK(KpS.i) : i in [1..Ngens(KpS)]]));
L := OptimizedRepresentation2(L);


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
    print "++++";
    Append(~middleExtensions, L);


    if Degree(L) eq 54 then
        print "Found last layer. With Theorem 8.1 we can conclude.";
        break;
    end if;
end while;
