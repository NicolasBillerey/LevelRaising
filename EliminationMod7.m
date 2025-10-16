Q:=Rationals();
Z:=Integers();

_<x> := PolynomialRing(Q);
m4 := x^3 + x^2 - 4*x + 1;
F<c> := NumberField(m4);
O := Integers(F);

load "Eigensystems.out";

Ps:=[ p : p in PrimesUpTo(31, F) ] cat [Factorization(83*O)[i][1] : i in [1..3]];

survivors:=[];
for ff in tracesModqa do
	if {((Norm(Ps[i])+1)^2 - ff[1][i]^2) mod 7 : i in [1..#Ps] | Norm(Ps[i]) in [5,83]} eq {0} then
		Append(~survivors,ff);
	end if;
end for;
print "The following mod 7 forms are not eliminated";
survivors;


print "The standard reducible representation looks like : ";
[(Norm(p) + 1) mod 7 : p in Ps];
print "and twisting it by the quadratic character of Q(\sqrt{13}) gives : ";
[(Norm(p) + 1)*KroneckerSymbol(13,Rep(PrimeDivisors(Norm(p)))) mod 7 : p in Ps];


