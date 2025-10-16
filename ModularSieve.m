/*
We perform the unit sieve in Section 2 of the paper.
*/


load "13-curveE.m";

/*
We have a mod \fp_7 congruence between E_{a,b} and the form g. 
We know that g mod \fp_7 matches E_{1,-1} so to compute Traces of Frobenius of g mod \fp_7 we can work with g = E_{1,-1} mod 7.
Note this fact is not used in the proof but we can use it here for the practical purpose of
accelerating the calculations; in particular it avoids computing the space of forms where g lives and access to traces is faster.
*/


function Sieving(AuxiliaryPrimes,BadPairsAt2,bool13)
    // AuxiliaryPrimes is the set of primes used for the sieve (containing 2 and excluding 13)
    // BadPairsAt2 is [[0,1]] if we sieve with a+b odd and [[1,1]] if we sieve with a+b even
    // bool13 is 1 if we sieve with 13 dividing a+b and is 0 otherwise
    unleft:=SetToSequence(Set(Q7));
    assert #unleft eq 16807;

    print "There are",#unleft,"units to eliminate.\n";

    for q in AuxiliaryPrimes do

        print "Using q-adic information with q =",q;

        if q eq 2 then
            BadPairsAtQ:=BadPairsAt2;
        else
            BadPairsAtQ:=BadPairs(q);
        end if;

        
        if bool13 eq 1 then
            addfact:=1-z;
        else
            addfact:=1;
        end if;

        factQ:=[I[1] : I in Factorization(q*OL)];
        ResFields:=[<Q,toQq> where Q,toQq := ResidueClassField(I) : I in factQ];

        survModqI:=[];
        for e in unleft do
            eps:=OL!psi(e);
            for pairxy in BadPairsAtQ do
                x,y:=Explode(pairxy);
                if {IsPower(res[2]((x+y*z)/(eps*addfact)),7) : res in ResFields} eq {true} then
                    Append(~survModqI,e);
                    break pairxy;
                end if;
            end for;
        end for;
        unleft:=survModqI;
        if #unleft gt 0 then
            print "There are still", #unleft,"units left.\n";
        else
            print "All units have been eliminated!\n";
        end if;
    end for;
    return "";
end function;




print "+++++++++++++++++++++++++++++++";
print "We sieve in the case a + b odd and 13 not dividing a + b.";
print "+++++++++++++++++++++++++++++++\n";

Sieving([2,11,19,23],[[0,1]],0);


print "";
print "+++++++++++++++++++++++++++++++";
print "We sieve in the case a + b odd and 13 dividing a + b.";
print "+++++++++++++++++++++++++++++++\n";

Sieving([2,11,19,23],[[0,1]],1);


print "+++++++++++++++++++++++++++++++";
print "We sieve in the case a + b even and 13 not dividing a + b.";
print "+++++++++++++++++++++++++++++++\n";


Sieving([2,11,19,23,83],[[1,1]],0);