/*
We consider the elliptic curve E/Q(sqrt(13)) defined in the paper
A multi-Frey approach to Fermat equations of signature (r,r,p), TAMS 2019
by N. Billerey, I. Chen, L. Dieulefait, and N. Freitas
(see p. 8666 in the published version).
We also introduce useful fonctions for the elimination.
*/



L<z>:=CyclotomicField(13); // Here z denotes a primitive 13-th root of unity
OL:=Integers(L);
UL,phi:=UnitGroup(OL); 
Q7,pi:=UL/(7*UL);
psi:=Inverse(pi)*phi;

RL:=PolynomialRing(L,2);
FL<x,y>:=FieldOfFractions(RL);



f1:= x^2 + (z + 1/z)*x*y + y^2;
f2:= x^2 + (z^3 + 1/z^3)*x*y + y^2;
f3:= x^2 + (z^4 + 1/z^4)*x*y + y^2;

alpha:= z^4 + 1/z^4 - z^3 - 1/z^3;
beta:= z + 1/z - z^4 - 1/z^4;
gamma:= z^3 + 1/z^3 - z - 1/z;

A:=alpha*f1;
B:=beta*f2;
C:=gamma*f3;

SL<X>:=PolynomialRing(FL);

a4:=3^3*(A*B + A*C + B*C);
a6:=-3^3*(2*A^3 + 3*A^2*B - 3*A*B^2 - 2*B^3);

E:=EllipticCurve(X^3 + a4*X + a6); // The elliptic curve E (but defined over L = Q(zeta13))
AI:=aInvariants(E); // Coefficients of E



// The field F = Q(sqrt(13)) (i.e., the unique quadratic subfield in Q(zeta_13))
F<w>:=QuadraticField(13);
OF:=Integers(F);



RF<x1,y1>:=PolynomialRing(F,2);
_,gm:=IsSubfield(F,L);

AIn:=RL!AI[4]; // a4 coefficient of E
NM:=[Evaluate(c,[x1,y1]) : c in Monomials(AIn)];
NC:=[F!(gm^(-1))(c) : c in Coefficients(AIn)];
NAI4:=RF!(&+[NC[i]*NM[i] : i in [1..#NM]]);

AIn:=RL!AI[5]; // a6 coefficient of E
NM:=[Evaluate(c,[x1,y1]) : c in Monomials(AIn)];
NC:=[F!(gm^(-1))(c) : c in Coefficients(AIn)];
NAI6:=RF!(&+[NC[i]*NM[i] : i in [1..#NM]]);

function FreyE(a,b)
    E:=EllipticCurve([Evaluate(NAI4,[a,b]),Evaluate(NAI6,[a,b])]);
    return E;
end function;



// Given a prime q not in {2, 13} and not congruent to 1 mod 13 (and hence of good reduction for E), this function returns the list of (the "bad") pairs (a,b) in {0,..., q-1} such that there is a mod 7 congruence between the a_Q-coefficients of E(a,b) and Z = E(1,-1)
function BadPairs(q);
    BadPairsQ:=[];
    assert q mod 13 ne 1;
    assert q notin [2,7,13];
    factQ:=Factorization(q*OF);
    Z:=FreyE(1,-1);
    // By choice of q we are always in the case of good reduction
    // We collect the pairs (a,b) mod q of good reduction that are compatible with the mod 7 congruence
    for x,y in [0..q-1] do
        phixy:=x^12 - y*x^11 + y^2*x^10 - y^3*x^9 + y^4*x^8 - y^5*x^7 + y^6*x^6 - y^7*x^5 + y^8*x^4 - y^9*x^3 + y^10*x^2 - y^11*x + y^12;
        if (x le y) and [x,y] ne [0,0] then	
            Bxy:=0;
            C:=FreyE(x,y);
            for i in [1..#factQ] do
                Q:=factQ[i,1];
                assert LocalInformation(C,Q)[3] eq 0;
                Bxy:=Gcd(Bxy,TraceOfFrobenius(C,Q) - TraceOfFrobenius(Z,Q));
            end for;
            if Valuation(Bxy,7) ne 0 then 
                Append(~BadPairsQ,[x,y]); 
            end if; 
        end if;             		 
    end for;
    return BadPairsQ;
end function;


