# Extensions to the modular method for small exponents

Electronic resources for the paper 'Extensions to the modular method for small exponents' by Nicolas Billerey, Imin Chen, Lassina Dembélé, Luis Dieulefait, and Nuno Freitas.

The paper is available on <a href="https://arxiv.org/abs/2510.13773">arXiv</a>.

We provide below a brief description of each of the Magma codes used in this work. All files run within a few minutes at most on a personal computer with one notable exception for the file Verifier.m which requires about 4 hours to terminate.

Last update: June 26, 2026

**Description of the files:**

* Avoiding_g.m: we show that when comparing traces of the Frey curve E mod 7 at prime ideals above q in {5, 11, 17, 19, 23, 29, 37, 41, 43, 61, 83, 89}, one can restrict ourselves to the specific curve Z = E(1,-1) and forget about the form g (~9 minutes).

* CurveE.m: we define a Frey curve E/Q(sqrt(13)) (from the paper 'A multi-Frey approach to Fermat equations of signature (r,r,p)', TAMS 2019 by N. Billerey, I. Chen, L. Dieulefait, and N. Freitas)

* Eigensystems.out: we store the 43 F_7-eigensystems introduced in Section 4.

* EliminationMod7.m: We perform the elimination at level 2.3.Q13^2 using only mod 7 computations. This, together with the results from Section 5, proves Theorem 4.1.

* LevelRaisingSieve.m: we seek level raising primes in the case 4 | a + b and 13 does not divide a + b by combining information coming from both the unit sieve and the modular method.

* Matrix.m: in this (heavy: 17.8 MB) file, we store a 2353 x 2353 matrix which gives the 'right' change of basis that guarantees that all computed F_7-eigensystems will appear with multiplicity one in the socle.

* ModularSieve.m: we perform the unit sieve described in Section 2 using modular information coming from the Frey curve E.

* PubMatSection3.m: this file contains all computations in support of the assertions made in Section 3 of the paper 'Some extensions of the modular method and Fermat equations of signature (13,13,n)', Pub. Mat. (2023) by N. Billerey, I. Chen, L. Dieulefait, and N. Freitas used in this paper.

* RedMod7.m: We check the computational assertions from Section 5 of the paper.

* Verifier.m: this file is used to compute the F_7-eigensystems of forms of level 2.3.Q13^2 using the matrix provided in the file Matrix.m (~4 hours). (Note that it is important to set the seed because of Magma using random choices.)






