/*
In this file we consider the form g introduced in Proposition 9 of the paper
A multi-Frey approach to Fermat equations of signature (r,r,p), TAMS 2019
by N. Billerey, I. Chen, L. Dieulefait, and N. Freitas
and show that among its two mod 7 systems of eigenvalues, one does not match the Frey curve E and the other one is equal to that of Z = E(1,-1), at least at all prime ideals above q in [5, 11, 17, 19, 23, 29, 37, 41, 43, 61, 83, 89]; see Proposition 6.1 in
Some extensions of the modular method and Fermat equations of signature (13,13,n), Pub. Mat. 67, Issue 2 (2023), 715--741
by N. Billerey, I. Chen, L. Dembébé, L. Dieulefait, and N. Freitas
for a general result though.
*/

load "CurveE.m";

Z:=FreyE(1,-1);

// The field F = Q(sqrt(13)) is defined in the file curveE.m
I2:=Factorisation(2*OF)[1,1];
I13:=Factorisation(13*OF)[1,1];

N:=I2^3*I13^2;

print "Computing newforms of level 2^3*13. Space of dimension", Dimension(NewSubspace(HilbertCuspForms(F,N)));
time forms:=Eigenforms(NewSubspace(HilbertCuspForms(F,N)));
print "...done!";
print "There are",#forms,"newforms.\n";

print "We consider the form g.\n";

g:=forms[27];
Qg<s>:=BaseField(g);
assert IsIsomorphic(Qg,QuadraticField(2));
Og:=Integers(Qg);
p7,p7prime:=Explode([p[1] : p in Factorisation(7*Og)]);



assert s+3 in p7;
assert s+4 in p7prime;


print "We show that for P being one of the two prime ideals above 7, there is no congruence modulo P between g and the Frey curve E by comparing traces at primes dividing 17.\n";

q:=17;
factQ:=Factorisation(q*OF);
valp7:=[];
valp7prime:=[];
for x,y in [0..q-1] do
    if ([x,y] ne [0,0]) then
        //print "x, y:=", x, y;
        C:=FreyE(x,y);
        for i in [1..#factQ] do
            Q:=factQ[i,1];
            if LocalInformation(C,Q)[3] eq 0 then
                // Here C has good reduction at Q
                Append(~valp7,Valuation((TraceOfFrobenius(C,Q) - HeckeEigenvalue(g,Q))*Og,p7));
                Append(~valp7prime,Valuation((TraceOfFrobenius(C,Q) - HeckeEigenvalue(g,Q))*Og,p7prime));

            else
                //print "Bad reduction";
                Append(~valp7,Valuation(((Norm(Q)+1)^2 - HeckeEigenvalue(g,Q)^2)*Og,p7));
                Append(~valp7prime,Valuation(((Norm(Q)+1)^2 - HeckeEigenvalue(g,Q)^2)*Og,p7prime));
            end if;
        end for;
    end if;
end for;
assert (Set(valp7) eq {0}) or (Set(valp7prime) eq {0});
// Hence for one of the two primes, there is no congruence between g and the Frey curve.

if Set(valp7) eq {0} then
    //print "No congruence modulo prime above 7 containing sqrt(2) + 3";
    k,tok:=ResidueClassField(p7prime);
else 
    //print "No congruence modulo prime above 7 containing sqrt(2) + 4";
    k,tok:=ResidueClassField(p7);
end if;

print "Done!\n";

print "We finally verify that the a_Q coefficients of g modulo the other prime above 7 match those of Z = E(1,-1) modulo 7 for every prime ideal Q|q with q in [5, 11, 17, 19, 23, 29, 37, 41, 43, 61, 83, 89].\n";

assert {tok(HeckeEigenvalue(g,Q[1])) eq TraceOfFrobenius(Z,Q[1]) : Q in Factorization(q*OF), q in [5, 11, 17, 19, 23, 29, 37, 41, 43, 61, 83, 89]} eq {true};


print "Done!";

// Therefore when comparing traces of Frobenius mod 7 of the Frey curve E at primes ideals above q in [5, 11, 17, 19, 23, 29, 37, 41, 43, 61, 83, 89], one may consider only the Frey curve Z = E(1,-1) and not the modular form g as their Hecke eigenvalues coincide.
