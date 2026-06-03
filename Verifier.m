/*
We compute the 43 F_7-eigensystems introduced in Section 4 using a basis provided by the matrix from the file Matrix.m.
*/



SetSeed(510311973);

q:=7;
Fq:=GF(q);
Zq:=pAdicRing(q);
Q:=Rationals();
Z:=Integers();

_<x> := PolynomialRing(Q);
m4 := x^3 + x^2 - 4*x + 1;
F<c> := NumberField(m4);
O := Integers(F);
I13 := Factorisation(13*O)[1, 1];
I2 := 2*O;
I3:=3*O;
N0:=I2*I3*I13^2;

Ps:=[ p : p in PrimesUpTo(31, F) ] cat [Factorization(83*O)[i][1] : i in [1..3]];
    
S := HilbertCuspForms(F,N0);
Snew := NewSubspace(S);    
T := [ HeckeOperator(Snew, p) : p in Ps ];

load "Matrix.m";
load "Eigensystems.out";

Ta:=[Ma*Tp*Ma^-1 : Tp in T];
    
Tq := [ ChangeRing(ChangeRing(Tp,Zq), Fq) : Tp in Ta ];    
Aq := MatrixAlgebra<Fq, Dimension(Snew) | Tq>;
Mq := RModule(Aq);
Sq := Socle(Mq);
Cq := ConstituentsWithMultiplicities(Sq);
Cqdim1:=[c : c in Cq | Dimension(c[1]) eq 1];

tracesModq := [ <[M[1, 1] : M in ActionGenerators(c[1])], c[2]> : c in Cqdim1 ];
tracesModq;

assert Set(tracesModq) eq Set(tracesModqa);



