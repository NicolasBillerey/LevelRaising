/*
We are in the case 4 | a + b and 13 does not divide a + b.
We seek level raising primes combining information coming from both the unit sieve and the modular method.
See Section 3 of the paper. 
*/

load "13-curveE.m";


eps0:=13^4/(1-z)^48;
assert Norm(eps0) eq 1;

pps:=[ 5, 17, 19, 23, 29, 37, 41, 43, 61, 83, 89 ];

print "+++++++++++++++++++++++++++++++++++++++++++++++++"; 
print "+++++++++++++++++++++++++++++++++++++++++++++++++"; 
print "Working with unit =", eps0; 

raisingPrimes:=[];

for q in pps do
    print "+++++++++++++++++++++++++";
    print "Working with q =",q;

    badPairs:=BadPairs(q); // Info from modular method

    if {(pr[1] + pr[2]) mod q : pr in badPairs} eq {0} then 
        Append(~raisingPrimes,q); 
        print "Conclusion from modular information only.";
        continue;
    end if;

    
    badPairs:={pr : pr in badPairs | (pr[1] + pr[2]) mod q ne 0};
    
    SurvivingPairs:=[];

    factQ:=[I[1] : I in Factorization(q*OL)];
    ResFields:=[<Q,toQq> where Q,toQq := ResidueClassField(I) : I in factQ];
    
    for pr in badPairs do
        if {IsPower(res[2]((pr[1]+pr[2]*z)/eps0),7) : res in ResFields} eq {true} then // Info from unit sieve
            Append(~SurvivingPairs,pr);
        end if;
    end for;

    if SurvivingPairs eq [] then 
        Append(~raisingPrimes,q); 
        print "Conclusion from modular information and sieve.";
    else
        print "No information at q =",q;
    end if;

end for;