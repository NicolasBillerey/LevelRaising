procedure SaveCoeff_g(Coeff_g, filename)
    SetOutputFile(filename : Overwrite := true);

    print "F<w>:=QuadraticField(13);";
    print "OF := Integers(F);";
    
    print "k := GF(", Characteristic(k), ", ", Integers()!Log(Characteristic(k), #k), ");";

    print "Coeff_g := [];";

    for c in Coeff_g do

        c1 := c[1]; // <prime ideal in the factorization of q*OF, exponent in the factorization>
        c2 := c[2]; // element of k

        coeffs_Q := [Eltseq(g) : g in Generators(c1[1])];
        print "Q := ideal<OF | [q[1]*OF.1 + q[2]*OF.2 : q in", coeffs_Q, "]>;";
        print "_ := IsPrincipal(Q);";
        print "_ := IsPrime(Q);";

        print "Append(~Coeff_g, [*<Q,", c1[2], ">, k!", c2 ,"*]);";

    end for;


    UnsetOutputFile();

    return 1;

end procedure;