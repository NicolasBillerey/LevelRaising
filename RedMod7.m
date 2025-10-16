/*
We check the computational assertions from Section 5 of the paper.
*/


SetClassGroupBounds("GRH"); // We assume GRH for the sake of speed but this computation can also be performed without in ??? minutes.

QQ := Rationals();
PolsQ<x> := PolynomialRing(QQ);
K<b> := NumberField(x^3 + x^2 - 4*x + 1); // Totally real cubic subfield of Q(zeta_13)
OK := Integers(K);

Ps:=PrimesUpTo(30,K);

I2:=Factorization(2*OK)[1,1];
I3:=Factorization(3*OK)[1,1];
I13:=Factorization(13*OK)[1,1];



print "\nWe check that there are no newforms at level 1 or Q_13...";
assert #Eigenforms(NewSubspace(HilbertCuspForms(K,1*OK))) eq 0;
assert #Eigenforms(NewSubspace(HilbertCuspForms(K,I13))) eq 0;
print "...done!";


forms3:=Eigenforms(NewSubspace(HilbertCuspForms(K,3*OK)));
print "\nThe",#forms3,"newforms of level 3OK have been computed!";
for i in [1..#forms3] do
    f:=forms3[i];
    Qf:=BaseField(f);
    Of:=Integers(Qf);
    fact7:=Factorisation(7*Of);
    for I in fact7 do 
        Q,toQ:=ResidueClassField(I[1]);
        if {toQ(HeckeEigenvalue(f,q) - (Norm(q)+1)) : q in Ps | Norm(q) notin [8,13,27]} eq {0} then 
            print "One (possible) congruence prime mod 7 found for form no",i,"in level 3OK";
        end if;	
    end for;
end for;
print "\nAt level 3OK, there is a single pair (g,P) where P|7 and g has a mod P Eisenstein congruence.";


Qs:=[5, 31, 47, 53, 73, 79, 83]; // Primes < 100 which are (totally) split in K
for l in [2,3] do
    redPairs:=[**];
    redPairsLevel:=[];
    Nfs:=Newforms(CuspidalSubspace(ModularForms(l*13)));
    for i in [1..#Nfs] do
        f:=Nfs[i][1];
        Ff:=BaseField(f);
        Of:=Integers(Ff);
        fact7:=Factorisation(7*Of);
        for I in fact7 do 
            Q,toQ:=ResidueClassField(I[1]);
            if {toQ(Coefficient(f,q) - (Norm(q)+1)) : q in Qs } eq {0} then 
                Append(~redPairs,<i,Q,toQ>);
            end if;	
        end for;
    end for;
    print "\nThe number of pairs (f,P) for f newform of level",l*13,"and P|7 in Q_f such that a_q(f) = 1 + q (mod P) for every prime q < 100 split in K is",#redPairs;
end for;

print "\nWe have proved the assertions in Proposition 5.1.";


N0:=I2*I3*I13;
print "\nComputing newforms at level N0 = 2*3*Q13...";
forms := Eigenforms(NewSubspace(HilbertCuspForms(K,N0)));
print "...done!";


redPairs:=[**];
redPairsLevel:=[];
for i in [1..#forms] do
	f:=forms[i];
	Ff:=BaseField(f);
	Of:=Integers(Ff);
	fact7:=Factorisation(7*Of);
	for I in fact7 do 
		Q,toQ:=ResidueClassField(I[1]);
		if {toQ(HeckeEigenvalue(f,q) - (Norm(q)+1)) : q in Ps | Norm(q) notin [8,13,27]} eq {0} then 
			assert #Q eq 7;
			Append(~redPairs,<i,Q,toQ>);
			Append(~redPairsLevel,[toQ(HeckeEigenvalue(forms[i],q)) : q in Ps | Norm(q) in [8,13,27]]);
		end if;	
	end for;
end for;
print "\nWe check that there are five pairs (f,P) such that f has level N0 and satisfies an Eisenstein congruence modulo P|7...";
assert #redPairs eq 5;
assert #redPairsLevel eq 5;
print "...done!";
print "\nThe reduction of the coefficients at the level of the pairs (f,p7) that are Eisenstein are (with multiplicity) :";
{* f : f in redPairsLevel*};

print "\nWe have proved the assertions in Corollary 5.3.";
