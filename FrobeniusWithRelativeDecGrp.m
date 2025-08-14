PolyQ<x> := PolynomialRing(Rationals());
K := NumberField(x^2-x+1);
L := NumberField(x^54 - 9*x^53 + 27*x^52 - 9*x^51 - 162*x^50 + 621*x^49 - 927*x^48 - 2853*x^47 + 17271*x^46 - 27573*x^45 - 27216*x^44 + 199728*x^43 - 349578*x^42 - 215937*x^41 + 2463120*x^40 - 4329000*x^39 - 2196252*x^38 + 19087911*x^37 - 19754406*x^36 - 35947710*x^35 + 127700802*x^34 - 125645994*x^33 - 109373778*x^32 + 459822843*x^31 - 397050057*x^30 - 508686399*x^29 + 1533961935*x^28 - 935121814*x^27 - 1593661833*x^26 + 3194569692*x^25 - 906284115*x^24 - 3479989338*x^23 + 4441500135*x^22 + 101725164*x^21 - 4788925272*x^20 + 3255745041*x^19 + 2214881976*x^18 - 3829955346*x^17 + 659765313*x^16 + 1846125180*x^15 - 1804908330*x^14 + 380728098*x^13 + 1400962572*x^12 - 1176843159*x^11 - 720091548*x^10 + 827937882*x^9 + 322896141*x^8 - 297229302*x^7 - 125213643*x^6 + 40510512*x^5 + 26411823*x^4 + 4309533*x^3 + 496962*x^2 + 28782*x + 991);
_ := IsSubfield(K,L);
Lrel := RelativeField(K,L);
OK := Integers(K);
OLrel := Integers(Lrel);

G, _ , m := AutomorphismGroup(Lrel);


function RelativeDecompositionGroup(q, Lrel, OLrel, Grel, m)
    gensP := [g : g in Generators(q)];
    Dp := [g : g in Grel | ideal<OLrel | [OLrel!m(g)(p) : p in gensP]> eq q];
    return sub <Grel | Dp>;
end function;

//q7 := [p[1] : p in Factorization(7*OK)];
//q71inL := ideal<OLrel | [OLrel!p : p in Generators(q7[1])]>;
//RelativeDecompositionGroup(Factorization(q71inL)[1][1], Lrel, OLrel, G, m);

// Construct all the frobenius elements
P := [q : q in PrimesUpTo(1000, K) | Valuation(q,Factorization(3*OK)[1][1]) eq 0];
Frobs := [**];
for p in P do
    pInL := Factorization(ideal<OLrel | [OLrel!q : q in Generators(p)]>)[1][1];
    Dp := RelativeDecompositionGroup(pInL, Lrel, OLrel, G, m);
    RCF, pi := ResidueClassField(pInL);
    phi := map<G -> RCF | g :-> pi(m(g)(Inverse(pi)(RCF.1)))>;
    char := Characteristic(RCF);
    for g in Dp do
        if IsPrime(Norm(p)) then // p is split in K 
            if phi(g) eq RCF.1^char then
                Append(~Frobs, <p,g>);
                break;
            end if;
        else
            if phi(g) eq RCF.1^(char^2) then
                Append(~Frobs, <p,g>);
                break;
            end if;
        end if; 
    end for;
end for;

CS := CyclicSubgroups(G);
max_cyc := [];

for H in CS do
    Hs := H`subgroup;
    flag := 0;
    for H2 in CS do
        H2s := H2`subgroup;
        if Hs eq H2s then
            continue;
        else
            if Hs subset H2s then
                flag := 1;
                break;
            end if;
        end if;
    end for;
    if flag eq 0 then
        Append(~max_cyc, Hs);
    end if;
end for;

max_cyc_conj := [max_cyc[1]];
for H in max_cyc do
    flag := 0;
    for H2 in max_cyc_conj do
        if IsConjugate(G, H, H2) then
            flag := 1;
            break;
        end if;
    end for;
    if flag eq 0 then
        Append(~max_cyc_conj, H);
    end if;
end for;

for C in max_cyc_conj do
    print "+++++";
    gens := [[g : g in C][2]];
    for f in Frobs do
        if f[2] in gens then
            conjs := Conjugates(G, f[2]);
            min_frobs := [**];
            for ff in Frobs do
                if ff[2] in conjs then
                    Append(~min_frobs, ff);
                end if;
            end for;
            n := [];
            for ff in min_frobs do
                nn := Norm(ff[1]);
                if IsSquare(nn) then
                    Append(~n, Integers()!Sqrt(nn));
                else
                    Append(~n, nn);
                end if;
            end for;
            print Sort(n);
            break f;
        end if;
    end for;
end for;

for C in max_cyc_conj do
    print "+++++";
    gens := [[g : g in C][3]];
    for f in Frobs do
        if f[2] in gens then
            conjs := Conjugates(G, f[2]);
            min_frobs := [**];
            for ff in Frobs do
                if ff[2] in conjs then
                    Append(~min_frobs, ff);
                end if;
            end for;
            n := [];
            for ff in min_frobs do
                nn := Norm(ff[1]);
                if IsSquare(nn) then
                    Append(~n, Integers()!Sqrt(nn));
                else
                    Append(~n, nn);
                end if;
            end for;
            print Sort(n);
            break f;
        end if;
    end for;
end for;