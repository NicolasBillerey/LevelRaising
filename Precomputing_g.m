/*
In this file we precompute some coefficients "mod 7" of the form g introduced in Proposition 9 of the paper
A multi-Frey approach to Fermat equations of signature (r,r,p), TAMS 2019
by N. Billerey, I. Chen, L. Dieulefait, and N. Freitas
*/

load "13-curveE.m";


//F<w>:=QuadraticField(13);
//OF:=Integers(F);

W0:=FreyE(1,-1);


I2:=Factorisation(2*OF)[1,1];
I13:=Factorisation(13*OF)[1,1];

N:=I2^3*I13^2;

print "Computing newforms of level 2^3*13. Space of dimension", Dimension(NewSubspace(HilbertCuspForms(F,N)));
time forms:=Eigenforms(NewSubspace(HilbertCuspForms(F,N)));
print "...done!";
print "There are",#forms,"newforms.\n";

print "We consider the form g.";

g:=forms[27];
Qg<s>:=BaseField(g);
assert IsIsomorphic(Qg,QuadraticField(2));
Og:=Integers(Qg);
p7,p7prime:=Explode([p[1] : p in Factorisation(7*Og)]);



// We identify the right prime ideal above 7 to be considered

k,tok:=ResidueClassField(p7);
CongruencesMod7 := {tok(HeckeEigenvalue(g,Q)) eq TraceOfFrobenius(W0,Q) : Q in PrimesUpTo(50,F) | Valuation(N,Q) eq 0};
if CongruencesMod7 ne {true} then
    k,tok:=ResidueClassField(p7prime);
end if;


// We compute the Fourier coefficients of g modulo the right prime ideal above 7 and store them in a list which we save in a file to be used later. 

Coefficients_g:=[[*Q,tok(HeckeEigenvalue(g,Q[1]))*] : Q in Factorization(q*OF), q in [5, 11, 17, 19, 23, 29, 37, 41, 43, 61, 83, 89]];




procedure SaveCoeff_g(Coeficients_g, filename)
    SetOutputFile(filename : Overwrite := true);

    print "F<w>:=QuadraticField(13);";
    print "OF := Integers(F);";
    
    print "k := GF(", Characteristic(k), ", ", Integers()!Log(Characteristic(k), #k), ");";
    print "Coefficients_g := [];";

    for c in Coefficients_g do

        c1 := c[1]; // <prime ideal in the factorization of q*OF, exponent in the factorization>
        c2 := c[2]; // element of k

        coeffs_Q := [Eltseq(g) : g in Generators(c1[1])];
        print "Q := ideal<OF | [q[1]*OF.1 + q[2]*OF.2 : q in", coeffs_Q, "]>;";
        print "_ := IsPrincipal(Q);";
        print "_ := IsPrime(Q);";

        print "Append(~Coefficients_g, [*<Q,", c1[2], ">, k!", c2 ,"*]);";

    end for; 

    UnsetOutputFile();

    //return 1;

end procedure;

SaveCoeff_g(Coefficients_g,"Coefficients_g.out");