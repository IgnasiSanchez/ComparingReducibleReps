load "TowerFieldAlgorithm.m";

// Algorithm parameters for Grenié
q := 2;
K := Rationals();
S := [2];
P := NFirstPrimes(20);
Exclude(~P, 2);
f := 4;

// First layer of the tower
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
    if Type(L) eq Type(-1) then
        print "We found K_S = K_{i-1}.";
        break;
    end if;
    print "Computing Optimized Representation...";
    if Degree(L) eq 64 then
        f2 := x^64 - 16*x^62 + 104*x^60 - 304*x^58 +
            344*x^56 + 496*x^54 + 568*x^52 - 48*x^50 + 1248*x^48 + 10336*x^46 +
            11720*x^44 + 17536*x^42 + 14168*x^40 + 52608*x^38 + 27320*x^36 - 19520*x^34
            - 8414*x^32 + 50224*x^30 + 243496*x^28 - 208624*x^26 - 259016*x^24 +
            244784*x^22 + 175544*x^20 - 204656*x^18 - 4384*x^16 + 55712*x^14 - 8248*x^12
            - 9920*x^10 + 4472*x^8 - 576*x^6 - 8*x^4 + 1;
        K2 := NumberField(f2);
        assert checkDegree64FieldIsomorphism(L, K2, middleExtensions[#middleExtensions]);
        L := K2;
    else
        L := OptimizedRepresentation2(L);
    end if;

    print L;
    print "++++";
    Append(~middleExtensions, L);
end while;
