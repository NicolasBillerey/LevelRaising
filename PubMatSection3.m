/*
This file contains the computations needed to prove the content of Section 3 from the paper
Some extensions of the modular method and Fermat equations of signature (13,13,n), Pub. Mat. (2023)
by N. Billerey, I. Chen, L. Dembélé, L. Dieulefait, and N. Freitas. 
*/

SetClassGroupBounds("GRH"); // We assume GRH for the sake of speed but this computation can also be performed without in ??? minutes.

QQ := Rationals();
PolsQ<x> := PolynomialRing(QQ);
K<b> := NumberField(x^3 + x^2 - 4*x + 1); // Totally real cubic subfield of Q(zeta_13)
OK := Integers(K);


I2:=Factorization(2*OK)[1,1];
I3:=Factorization(3*OK)[1,1];
I13:=Factorization(13*OK)[1,1];

N0:= I2*I3*I13;


print "Computing newforms..";
forms := Eigenforms(NewSubspace(HilbertCuspForms(K,N0)));
print "Done.";

print "The degree of the field of coefficients of the forms of conductor 2*3*I13 are : ";
[Degree(BaseField(f)) : f in forms];
print "In particular, there are 4 forms with rational coefficients, i.e. corresponding to elliptic curves.";

print "One of them is base change of the elliptic curve 78a1 over Q";
EoF:=ChangeRing(EllipticCurve("78a1"),K);
assert Conductor(EoF) eq N0;

print "A quick look at the traces of Frobenius of the prime ideals above the split prime 5 shows that the remaining 3 curves are not base change.";
[ [ HeckeEigenvalue(s, p[1]) : p in Factorisation(5*OK) ] : s in forms[1..4] ];
print "Therefore, since the conductor is Galois invariant, we conclude they are permuted by the action of Gal(K/Q).\n";

print "\nWe now proceed to the forms with non-rational coefficients.\n";
/* Forms with non-rational Hecke eigenvalues. */

s:=forms[5];
Qf:=BaseField(s);
assert IsSubfield(Qf,CyclotomicField(7));
assert IsTotallyReal(Qf);
print "The form number 5 has field of coefficients Q(zeta_7)^+.\n";

print "The forms 6 to 15 are those whose information is contained in Table 1.\n"; 
print "Note that for the last 3 forms in the table we do not include the generator of the conductor ideal because it has large coefficients, but it can be retrieved from the calculations below.\n";


for i in [6..15] do 
    print "+++++++++++++++++++++++++++++++++++++++";
    print "form i = ", i;
    Qf:= OptimizedRepresentation(BaseField(forms[i]));
    assert #(Subfields(Qf, n) where n:=Integers()!(Degree(Qf)/3)) eq 1;
    E<w> := OptimizedRepresentation(Subfields(Qf, n)[1][1]) where n := Integers()!(Degree(Qf)/3);
    Qf := RelativeField(E, Qf);
    L := RayClassField(Qf);
    condL := Conductor(L);
    bol, cL := IsPrincipal(condL);
    assert bol;
    print "\nA defining polynomial (not unique!) for E is:";
    DefiningPolynomial(E);
    print "\nHere is the factorisation of the conductor of Qf/E:";
    Factorisation(condL);
    print "\nHere is a generator (not unique!) for the conductor of Qf/E:";
    print E!cL;

    // The following proves Lemma 3.1
    if Norm(condL) mod 7 eq 0 then 
        print "\nThe following booleans prove the content of Lemma 3.1 for this form.";
        Of:=Integers(Qf); 
        factOf:=[I[1] : I in Factorisation(Gcd(7*Of,cL*Of))];
        //This proves the first claim of Lemma 3.1
        {AbsoluteNorm(p0) : p0 in factOf} eq {7};
        //This proves the second claim of Lemma 3.1
        {RamificationIndex(p0) : p0 in factOf} eq {3};
        if #factOf gt 1 then
            print "\nThere are",#factOf,"prime ideals p0 as in Lemma 3.1 for this form.\n";
        else
            print "\nThere is one prime ideal p0 as in Lemma 3.1 for this form.\n";
        end if;
    end if;
end for;
print "We have established the contents of Table 1 and Lemma 3.1.\n";

print "The following proves the claims at the end of the proof of Proposition 3.2.\n";
Newforms(CuspForms(Gamma0(78),2));
assert Coefficient($1[1,1],5) eq 2;
W:=EllipticCurve("78a1");
print "The trace of Frobenius at 5 of the elliptic curve W = 78a1 is",TraceOfFrobenius(W,5);

print "\nWe check that for the forms no 8, 12, 13 and 14, there is a prime Q|5 such that the trace of Frobenius at Q is not (2 mod 7)";
fact5:=[I[1] : I in Factorisation(5*OK)];
for i in [8,12,13,14] do
	Integers()!(Norm(HeckeEigenvalue(forms[i],fact5[1]) - 2)) mod 7 ne 0; 
end for;









