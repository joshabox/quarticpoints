//This is part of the accompanying Magma file of the paper ``Computing models for quotients of modular curves''
//by Josha Box. It computes the map X(b5,ns7) --> X(ns7) on the canonical model.
//At the end of the file, we have added the computation of the map X(b5,ns7) --> X_0(5).


/* In this Magma file, we first verify that our model for X(b5,ns7) 
is isomorphic to the Derickx--Najman--Siksek model.
We then compute the map X(b5,ns7) --> X(ns7) explicitly. */

//We copy-paste the equations for X(b5,ns7) from the output of the Sage file.
P<X0,X1,X2,X3,X4,X5>:=ProjectiveSpace(Rationals(),5);
Xb5ns7:=Curve(P,[14*X0^2 + 12*X2*X3 - 16*X3^2 - 14*X2*X4 + 30*X3*X4 - 11*X4^2 + 28*X2*X5 - 58*X3*X5 + 40*X4*X5 - 28*X5^2, 7*X0*X1 - 2*X2*X4 - 4*X3*X4 + 2*X4^2 + 12*X3*X5 - 7*X4*X5 + 10*X5^2, 14*X1^2 - 4*X2*X3 + 16*X3^2 + 10*X2*X4 + 14*X3*X4 - 21*X4^2 + 4*X2*X5 - 58*X3*X5 + 64*X4*X5 - 66*X5^2, 2*X0*X2 - 2*X0*X3 + 2*X1*X3 - 5*X0*X4 - 6*X1*X4 + 8*X0*X5 + 4*X1*X5, 4*X1*X2 - 2*X0*X3 - 6*X1*X3 - X0*X4 + 3*X1*X4 + 3*X0*X5 - 2*X1*X5, 8*X2^2 - 20*X2*X3 + 16*X3^2 - 14*X2*X4 + 14*X3*X4 - 21*X4^2 + 28*X2*X5 - 42*X3*X5 + 56*X4*X5 - 28*X5^2]);


//The below function is code written by Derickx--Najman--Siksek.
//It takes as input a curve XX isomorphic to X(b5,ns7)
//The output is a map XX --> X, where X is a ``nice'' planar model for XX.

DNSplanarmodel:=function(XX)
tf,XXtoF:=Genus6PlaneCurveModel(XX);
F:=Codomain(XXtoF);
//The below code, written by Derickx--Najman--Siksek, makes this model look a little nicer.

// We want to check the claim that F has four singular points,
// and that these are ordinary double points.
S:=SingularSubscheme(F);
assert Dimension(S) eq 0;
assert #PointsOverSplittingField(S) eq 4;
// Thus F has four singular points.
// We shall show that these are nodes,
// and that two are defined over \Q(i)
// and the other two are defined over \Q(\sqrt{5}).

assert #Points(S) eq 0;
// None of the four singular points are defined over \Q.

K1 := QuadraticField(-1);
K2 := QuadraticField(5);

singPointsK1:=Points(S,K1);
assert #singPointsK1 eq 2;
FK1:=ChangeRing(F,K1);
assert IsNode(FK1!Eltseq(singPointsK1[1]));
assert IsNode(FK1!Eltseq(singPointsK1[2]));

singPointsK2:=Points(S,K2);
assert #singPointsK2 eq 2;
FK2:=ChangeRing(F,K2);
assert IsNode(FK2!Eltseq(singPointsK2[1]));
assert IsNode(FK2!Eltseq(singPointsK2[2]));
// We have now checked that all four
// singular points are nodes,
// with two defined over K1=\Q(i)
// and two defined over K2:=\Q(\sqrt{5}).

// Let the two points defined over \Q(i)
// be x_1, x_2
// and the two points defined over \Q(\sqrt{5})
// by y_1, y_2.
// We change coordinates so that
// x_1, x_2 map to 
// a_1=(i : 0 : 1), a_2=(-i:0:1)
// and y_1, y_2 map to 
// b_1=(0 : 1/\sqrt{5} : 1), b_2= (0 : -1/\sqrt{5} :1).

K := Compositum(K1,K2);
PK<u,v,w> := ProjectiveSpace(K,2);
x1,x2 := Explode(Setseq(RationalPoints(S,K1)));
y1,y2 := Explode(Setseq(RationalPoints(S,K2)));
x1 := PK ! Eltseq(x1);
x2 := PK ! Eltseq(x2);
y1 := PK ! Eltseq(y1);
y2 := PK ! Eltseq(y2);
a1 := PK ! [K1.1,0,1];
a2 := PK ! [-K1.1,0,1];
b1 := PK ! [0,K2.1/5,1];
b2 := PK ! [0,-K2.1/5,1];
T1 := TranslationOfSimplex(PK,[x1,x2,y1,y2]);
T2 := TranslationOfSimplex(PK,[a1,a2,b1,b2]);
T := T2^(-1)*T1;
// T^-1 gives our desired change of coordinates.

PQ<u,v,w> := AmbientSpace(F);

// T is defined over K. However it preserves Q-conjugacy
// and so must be defined over Q. 
// We now write a model for T over Q.
Teqs := DefiningEquations(T);
T1 :=  Numerator(Teqs[1]/Teqs[2]);
lambda := K ! (T1/Teqs[1]);
TeqsQ := [CoordinateRing(PQ) ! (lambda*t) : t in Teqs];
TQ := map< PQ -> PQ | TeqsQ>; // This is a model for T over Q.
// As a sanity check we base change TQ back to K and check that
// we get T.
TK := map< PK -> PK |  [ CoordinateRing(PK)!t : t in DefiningEquations(TQ)  ]  >;
assert TK eq T; // Sanity check.

X := Pullback(TQ,F);  
R<u,v,w>:=CoordinateRing(AmbientSpace(X));
invTQ:=map< F -> X | DefiningEquations(Inverse(TQ))>;
return XXtoF*invTQ;
end function;


Xb5ns7toX:=DNSplanarmodel(Xb5ns7);
X:=Codomain(Xb5ns7toX);
print "The planar model we find for X(b5,ns7) is ",X; 
print "This is the exact same model as found by Derick--Najman--Siksek.";
print "The map from X(b5,ns7) to the planar model is linear: ",Expand(Xb5ns7toX); 
//By comparison, the map from Le Hung's model to X found by Derickx--Najman--Siksek
//is so complicated that even evaluating points is too time-expensive.

//Next, we set about computing the j-invariant on Xb5ns7 by first computing the map to X(ns7).

P<x>:=PolynomialRing(Rationals());
K<a>:=NumberField(x^3+x^2-2*x-1);
PP<z>:=PolynomialRing(K);
F<t>:=PolynomialRing(K);
F<t>:=FieldOfFractions(F);
L<q>:=LaurentSeriesRing(F,200);
g:=x^3+x^2-2*x-1;
f:=(4*x^2+5*x+2)*(x^2+3*x+4)*(x^2+10*x+4)*(3*x+1); //Chen's model for the j-map on X(ns7)=P^1 is g^3/f^7. 

//We use the j-map on X(ns7) to compute the q-expansion of the Hauptmodul n7 on X(ns7) giving rise to this j-map.
//Chen shows that the q-exp of n7 starts at q^0, i.e. n7(infty) \neq infty. From the shape of j, we see that 
//this is only possible when n7=a+O(q). We compute the next coefficient. Need g(n7)^3/f(n7)^7 = j(q^7) = q^-7+ O(1).

assert Evaluate(f,a+t*q+O(q^2))^3/(Evaluate(g,a+t*q+O(q^2))/q)^7 eq (3019478*a^2 + 6779640*a + 2419179)/t^7 + O(q);
ff:=z^7-(3019478*a^2 + 6779640*a + 2419179);
assert [fact : fact in Factorization(ff) | Degree(fact[1]) eq 1][1] eq Factorization(ff)[1];
a1:=-Coefficients(Factorization(ff)[1][1])[1]; //So n7=a+a1*q+O(q^2).
LL<qq>:=LaurentSeriesRing(Rationals(),200);
j:=L!qExpansionsOfGenerators(1,LL,200)[1]; //The q-exp of j
j7:=q^7*Evaluate(j,q^7); 
n7:=a+a1*q;

//We recursively compute the coefficients of n7 using the fact that j(q^7)=f(n7)^3/g(n7)^7
//and given our choices of the first two coefficients. 
prec:=199;
for n in [2..prec] do
    m7:=n7+t*q^n+O(q^(n+1));
    df:=Evaluate(f,m7)^3/((Evaluate(g,m7)/q)^7)-j7;
    assert Valuation(df) ge n-1;
    eqn:=Coefficient(df,n-1);
    cfs:=Coefficients(Numerator(eqn)); //linear in t
    an:=-cfs[1]/cfs[2];
    assert Evaluate(Numerator(eqn),an) eq 0;
    n7:=n7+an*q^n;
end for;
assert Valuation(Evaluate(f,n7)^3/Evaluate(g,n7)^7-Evaluate(j,q^7)) ge 80;
LL<q>:=LaurentSeriesRing(K,prec+1);
n7:=LL!n7+O(q^prec);

//We import the cusp forms f0,...,f4 used to compute our canonical model for X(b5,ns7)
//To find the map X(b5,ns7) --> X(ns7), it thus suffices to find polynomials 
//p and q such that q(f0,...,f4)*n7 = p(f0,...,f4). This comes down to linear algebra.

Q7<zeta>:=CyclotomicField(7);
Q7plus<z7plus>:=sub<Q7 | zeta+zeta^-1>;
tf,phi:=IsIsomorphic(Q7plus,K);
aut,S,phii:=AutomorphismGroup(K);
Embed(Q7plus,K,phii(aut.1^2)(phi(z7plus)));
//It is important to take the right isomorphism between Q7plus and K.

LLL<q7p>:=LaurentSeriesRing(Q7plus,200);
f0:=LL!((10*z7plus^2 + 2*z7plus - 16)*q7p + (4*z7plus^2 + 12*z7plus - 12)*q7p^2 + (-6*z7plus^2 - 4*z7plus + 18)*q7p^3 + (8*z7plus^2 + 10*z7plus - 10)*q7p^5 + (-8*z7plus^2 + 4*z7plus + 24)*q7p^6 + (24*z7plus^2 + 16*z7plus - 16)*q7p^8 + (8*z7plus^2 + 24*z7plus - 24)*q7p^9 + (-8*z7plus^2 + 4*z7plus + 24)*q7p^10 + (-10*z7plus^2 - 16*z7plus + 30)*q7p^11 + (-42*z7plus^2 - 14*z7plus + 56)*q7p^13 + (-2*z7plus^2 - 6*z7plus - 8)*q7p^15 + (32*z7plus^2 + 40*z7plus - 40)*q7p^16 + (22*z7plus^2 - 4*z7plus - 66)*q7p^17 + (-8*z7plus^2 + 32*z7plus + 24)*q7p^18 + (48*z7plus^2 + 60*z7plus - 60)*q7p^19 + (-4*z7plus^2 + 16*z7plus + 40)*q7p^22 + (-52*z7plus^2 - 72*z7plus + 72)*q7p^23 + (8*z7plus^2 + 24*z7plus - 24)*q7p^24 + (-2*z7plus^2 + 8*z7plus + 6)*q7p^25 + (-28*z7plus^2 - 56*z7plus + 56)*q7p^26 + (-22*z7plus^2 - 10*z7plus + 24)*q7p^27 + (-78*z7plus^2 - 38*z7plus + 80)*q7p^29 + (-12*z7plus^2 - 8*z7plus + 8)*q7p^30 + (36*z7plus^2 - 60*z7plus - 108)*q7p^31 + (-36*z7plus^2 - 10*z7plus + 10)*q7p^33 + (48*z7plus^2 + 4*z7plus - 88)*q7p^34 + (4*z7plus^2 - 16*z7plus + 16)*q7p^37 + (-48*z7plus^2 + 24*z7plus + 144)*q7p^38 + (14*z7plus^2 - 42)*q7p^39 + (8*z7plus^2 + 24*z7plus - 24)*q7p^40 + (56*z7plus^2 + 28*z7plus - 56)*q7p^41 + (20*z7plus^2 + 4*z7plus - 32)*q7p^43 + (-16*z7plus^2 + 8*z7plus + 48)*q7p^45 + (52*z7plus^2 - 40*z7plus - 156)*q7p^46 + (-36*z7plus^2 - 66*z7plus + 66)*q7p^47 + (-8*z7plus^2 - 24*z7plus - 32)*q7p^48 + (-12*z7plus^2 - 8*z7plus + 8)*q7p^50 + (40*z7plus^2 + 22*z7plus - 22)*q7p^51 + (-24*z7plus^2 + 12*z7plus + 72)*q7p^53 + (-20*z7plus^2 - 32*z7plus + 32)*q7p^54 + (6*z7plus^2 - 10*z7plus - 32)*q7p^55 + (-12*z7plus^2 - 36*z7plus - 48)*q7p^57 + (-76*z7plus^2 - 116*z7plus + 116)*q7p^58 + (-20*z7plus^2 - 4*z7plus + 60)*q7p^59 + (-8*z7plus^2 - 24*z7plus + 24)*q7p^61 + (132*z7plus^2 + 60*z7plus - 144)*q7p^62 + (80*z7plus^2 + 16*z7plus - 128)*q7p^64 + (-28*z7plus^2 - 42*z7plus + 42)*q7p^65 + (36*z7plus^2 + 52*z7plus - 108)*q7p^66 + (32*z7plus^2 - 44*z7plus - 96)*q7p^67 + (20*z7plus^2 + 32*z7plus + 24)*q7p^69 + (-36*z7plus^2 + 4*z7plus + 80)*q7p^71 + (64*z7plus^2 + 80*z7plus - 80)*q7p^72 + (-48*z7plus^2 + 24*z7plus + 144)*q7p^73 + (-4*z7plus^2 - 40*z7plus + 12)*q7p^74 + (4*z7plus^2 - 2*z7plus + 2)*q7p^75 + (28*z7plus^2 - 56)*q7p^78 + (32*z7plus^2 - 2*z7plus + 2)*q7p^79 + (-8*z7plus^2 + 32*z7plus + 24)*q7p^80 + (-46*z7plus^2 + 16*z7plus + 138)*q7p^81 + (56*z7plus^2 + 84*z7plus - 84)*q7p^82 + (26*z7plus^2 + 22*z7plus - 8)*q7p^85 + (8*z7plus^2 + 24*z7plus - 24)*q7p^86 + (2*z7plus^2 - 36*z7plus - 6)*q7p^87 + (32*z7plus^2 + 40*z7plus - 96)*q7p^88 + (-64*z7plus^2 - 80*z7plus + 80)*q7p^89 + (-40*z7plus^2 - 8*z7plus + 64)*q7p^90 + (12*z7plus^2 + 36*z7plus - 36)*q7p^93 + (36*z7plus^2 - 60*z7plus - 108)*q7p^94 + (-12*z7plus^2 + 48*z7plus + 36)*q7p^95 + (-126*z7plus^2 - 42*z7plus + 168)*q7p^97 + (-8*z7plus^2 + 32*z7plus + 80)*q7p^99 + (36*z7plus^2 + 24*z7plus - 108)*q7p^101 + (-40*z7plus^2 - 36*z7plus + 120)*q7p^102 + (132*z7plus^2 + 186*z7plus - 186)*q7p^103 + (-112*z7plus^2 - 56*z7plus + 112)*q7p^104 + (-60*z7plus^2 - 12*z7plus + 96)*q7p^106 + (-24*z7plus^2 + 12*z7plus - 12)*q7p^107 + (-10*z7plus^2 + 40*z7plus + 30)*q7p^109 + (-20*z7plus^2 - 4*z7plus + 4)*q7p^110 + (20*z7plus^2 - 24*z7plus - 88)*q7p^111 + (-120*z7plus^2 - 52*z7plus + 136)*q7p^113 + (-72*z7plus^2 - 48*z7plus + 48)*q7p^114 + (20*z7plus^2 - 52*z7plus - 60)*q7p^115 + (-56*z7plus^2 - 112*z7plus + 112)*q7p^117 + (-36*z7plus^2 + 4*z7plus + 80)*q7p^118 + (-16*z7plus^2 + 8*z7plus + 48)*q7p^120 + (84*z7plus - 84)*q7p^121 + (8*z7plus^2 - 32*z7plus - 24)*q7p^122 + 28*z7plus*q7p^123 + (-10*z7plus^2 - 2*z7plus + 16)*q7p^125 + (76*z7plus^2 + 32*z7plus - 88)*q7p^127 + (32*z7plus^2 + 96*z7plus - 96)*q7p^128 + (-12*z7plus^2 - 8*z7plus + 36)*q7p^129 + (28*z7plus^2 - 28*z7plus - 84)*q7p^130 + (76*z7plus^2 + 116*z7plus - 116)*q7p^131 + (108*z7plus^2 + 44*z7plus - 128)*q7p^134 + (-12*z7plus^2 - 22*z7plus + 22)*q7p^135 + (8*z7plus^2 - 88*z7plus - 24)*q7p^136 + (-24*z7plus^2 + 96*z7plus + 72)*q7p^137 + (64*z7plus^2 + 52*z7plus - 52)*q7p^138 + (-84*z7plus^2 + 168)*q7p^139 + (30*z7plus^2 + 6*z7plus - 48)*q7p^141 + (8*z7plus^2 - 32*z7plus + 32)*q7p^142 + (14*z7plus^2 + 28*z7plus - 42)*q7p^143 + (-64*z7plus^2 + 32*z7plus + 192)*q7p^144 + (-40*z7plus^2 - 78*z7plus + 78)*q7p^145 + (-120*z7plus^2 - 24*z7plus + 192)*q7p^146 + (88*z7plus^2 + 96*z7plus - 96)*q7p^149 + (-4*z7plus^2 - 12*z7plus + 12)*q7p^150 + (46*z7plus^2 - 16*z7plus - 138)*q7p^151 + (48*z7plus^2 + 144*z7plus - 144)*q7p^152 + (96*z7plus^2 + 8*z7plus - 176)*q7p^153 + (96*z7plus^2 + 36*z7plus - 120)*q7p^155 + (-20*z7plus^2 + 136*z7plus + 60)*q7p^157 + (-32*z7plus^2 - 68*z7plus + 96)*q7p^158 + (-36*z7plus^2 - 24*z7plus + 24)*q7p^159 + (-108*z7plus^2 - 16*z7plus + 184)*q7p^162 + (60*z7plus^2 + 96*z7plus - 96)*q7p^163 + (-26*z7plus^2 - 36*z7plus + 78)*q7p^165 + (-14*z7plus^2 + 14*z7plus + 56)*q7p^167 + (52*z7plus^2 + 44*z7plus - 16)*q7p^169 + (44*z7plus^2 + 48*z7plus - 48)*q7p^170 + (-96*z7plus^2 + 48*z7plus + 288)*q7p^171 + (-36*z7plus^2 - 66*z7plus + 66)*q7p^173 + (40*z7plus^2 + 36*z7plus - 8)*q7p^174 + (24*z7plus^2 - 40*z7plus - 128)*q7p^176 + (-44*z7plus^2 - 20*z7plus + 20)*q7p^177 + (64*z7plus^2 - 32*z7plus - 192)*q7p^178 + (60*z7plus^2 - 72*z7plus - 180)*q7p^179 + (168*z7plus^2 + 84*z7plus - 168)*q7p^181 + (16*z7plus^2 - 8*z7plus - 48)*q7p^183 + (-80*z7plus^2 - 184*z7plus + 184)*q7p^184 + (20*z7plus^2 + 4*z7plus - 60)*q7p^185 + (-12*z7plus^2 + 48*z7plus + 36)*q7p^186 + (76*z7plus^2 + 18*z7plus - 18)*q7p^187 + (-72*z7plus^2 - 48*z7plus + 48)*q7p^190 + (-24*z7plus^2 - 114*z7plus + 114)*q7p^191 + (-48*z7plus^2 - 32*z7plus + 144)*q7p^192 + (32*z7plus^2 - 128*z7plus - 96)*q7p^193 + (-84*z7plus^2 - 168*z7plus + 168)*q7p^194 + (14*z7plus^2 + 14*z7plus)*q7p^195 + (132*z7plus^2 + 32*z7plus - 200)*q7p^197 + (64*z7plus^2 + 24*z7plus - 24)*q7p^198 + (-20*z7plus^2 + 52*z7plus + 60)*q7p^199+O(q7p^200));
f1:=LL!((-6*z7plus^2 - 4*z7plus + 4)*q7p + (-8*z7plus^2 - 10*z7plus + 10)*q7p^2 + (-2*z7plus^2 - 6*z7plus + 6)*q7p^3 + (-2*z7plus^2 - 6*z7plus + 6)*q7p^5 + (2*z7plus^2 + 6*z7plus + 8)*q7p^6 + (-20*z7plus^2 - 4*z7plus + 32)*q7p^8 + (-16*z7plus^2 - 20*z7plus + 20)*q7p^9 + (2*z7plus^2 - 8*z7plus - 6)*q7p^10 + (-8*z7plus^2 - 10*z7plus + 24)*q7p^11 + (28*z7plus^2 + 14*z7plus - 28)*q7p^13 + (4*z7plus^2 - 2*z7plus - 12)*q7p^15 + (-8*z7plus^2 - 24*z7plus + 24)*q7p^16 + (-2*z7plus^2 + 22*z7plus + 6)*q7p^17 + (16*z7plus^2 - 8*z7plus - 48)*q7p^18 + (-12*z7plus^2 - 36*z7plus + 36)*q7p^19 + (-6*z7plus^2 + 10*z7plus + 32)*q7p^22 + (20*z7plus^2 + 46*z7plus - 46)*q7p^23 + (12*z7plus^2 + 8*z7plus - 36)*q7p^24 + (4*z7plus^2 - 2*z7plus - 12)*q7p^25 + (28*z7plus^2 + 42*z7plus - 42)*q7p^26 + (16*z7plus^2 + 6*z7plus - 20)*q7p^27 + (58*z7plus^2 + 20*z7plus - 76)*q7p^29 + (-4*z7plus^2 + 2*z7plus - 2)*q7p^30 + (-30*z7plus^2 + 36*z7plus + 90)*q7p^31 + (-26*z7plus^2 - 8*z7plus + 8)*q7p^33 + (-26*z7plus^2 - 22*z7plus + 8)*q7p^34 + (20*z7plus^2 + 18*z7plus - 18)*q7p^37 + (12*z7plus^2 - 48*z7plus - 36)*q7p^38 + 14*z7plus*q7p^39 + (-16*z7plus^2 - 20*z7plus + 20)*q7p^40 + (-42*z7plus^2 - 14*z7plus + 56)*q7p^41 + (-12*z7plus^2 - 8*z7plus + 8)*q7p^43 + (4*z7plus^2 - 16*z7plus - 12)*q7p^45 + (-20*z7plus^2 + 52*z7plus + 60)*q7p^46 + (30*z7plus^2 + 48*z7plus - 48)*q7p^47 + (16*z7plus^2 - 8*z7plus - 48)*q7p^48 + (10*z7plus^2 + 2*z7plus - 16)*q7p^50 + (18*z7plus^2 - 2*z7plus + 2)*q7p^51 + (6*z7plus^2 - 24*z7plus - 18)*q7p^53 + (12*z7plus^2 + 22*z7plus - 22)*q7p^54 + (2*z7plus^2 - 8*z7plus - 20)*q7p^55 + (24*z7plus^2 - 12*z7plus - 72)*q7p^57 + (40*z7plus^2 + 78*z7plus - 78)*q7p^58 + (-2*z7plus^2 - 20*z7plus + 6)*q7p^59 + (16*z7plus^2 + 20*z7plus - 20)*q7p^61 + (-96*z7plus^2 - 36*z7plus + 120)*q7p^62 + (-48*z7plus^2 - 32*z7plus + 32)*q7p^64 + (14*z7plus^2 + 28*z7plus - 28)*q7p^65 + (26*z7plus^2 + 36*z7plus - 78)*q7p^66 + (-22*z7plus^2 + 32*z7plus + 66)*q7p^67 + (-26*z7plus^2 + 6*z7plus + 64)*q7p^69 + (16*z7plus^2 + 20*z7plus + 8)*q7p^71 + (-16*z7plus^2 - 48*z7plus + 48)*q7p^72 + (12*z7plus^2 - 48*z7plus - 36)*q7p^73 + (-20*z7plus^2 - 4*z7plus + 60)*q7p^74 + (6*z7plus^2 + 4*z7plus - 4)*q7p^75 + (-14*z7plus^2 - 14*z7plus)*q7p^78 + (34*z7plus^2 + 18*z7plus - 18)*q7p^79 + (16*z7plus^2 - 8*z7plus - 48)*q7p^80 + (8*z7plus^2 - 46*z7plus - 24)*q7p^81 + (-28*z7plus^2 - 56*z7plus + 56)*q7p^82 + (-24*z7plus^2 - 2*z7plus + 44)*q7p^85 + (-16*z7plus^2 - 20*z7plus + 20)*q7p^86 + (-18*z7plus^2 + 2*z7plus + 54)*q7p^87 + (20*z7plus^2 + 32*z7plus - 60)*q7p^88 + (16*z7plus^2 + 48*z7plus - 48)*q7p^89 + (24*z7plus^2 + 16*z7plus - 16)*q7p^90 + (-24*z7plus^2 - 30*z7plus + 30)*q7p^93 + (-30*z7plus^2 + 36*z7plus + 90)*q7p^94 + (24*z7plus^2 - 12*z7plus - 72)*q7p^95 + (84*z7plus^2 + 42*z7plus - 84)*q7p^97 + (-12*z7plus^2 + 20*z7plus + 64)*q7p^99 + (12*z7plus^2 + 36*z7plus - 36)*q7p^101 + (-18*z7plus^2 - 40*z7plus + 54)*q7p^102 + (-54*z7plus^2 - 120*z7plus + 120)*q7p^103 + (84*z7plus^2 + 28*z7plus - 112)*q7p^104 + (36*z7plus^2 + 24*z7plus - 24)*q7p^106 + (-36*z7plus^2 - 24*z7plus + 24)*q7p^107 + (20*z7plus^2 - 10*z7plus - 60)*q7p^109 + (-16*z7plus^2 - 6*z7plus + 6)*q7p^110 + (2*z7plus^2 - 22*z7plus - 48)*q7p^111 + (86*z7plus^2 + 34*z7plus - 104)*q7p^113 + (-24*z7plus^2 + 12*z7plus - 12)*q7p^114 + (-26*z7plus^2 + 20*z7plus + 78)*q7p^115 + (56*z7plus^2 + 84*z7plus - 84)*q7p^117 + (16*z7plus^2 + 20*z7plus + 8)*q7p^118 + (4*z7plus^2 + 12*z7plus + 16)*q7p^120 + (-84*z7plus^2 - 84*z7plus + 84)*q7p^121 + (-16*z7plus^2 + 8*z7plus + 48)*q7p^122 + (14*z7plus^2 - 42)*q7p^123 + (6*z7plus^2 + 4*z7plus - 4)*q7p^125 + (-54*z7plus^2 - 22*z7plus + 64)*q7p^127 + (-64*z7plus^2 - 80*z7plus + 80)*q7p^128 + (-4*z7plus^2 - 12*z7plus + 12)*q7p^129 + (-14*z7plus^2 + 28*z7plus + 42)*q7p^130 + (-40*z7plus^2 - 78*z7plus + 78)*q7p^131 + (-76*z7plus^2 - 32*z7plus + 88)*q7p^134 + (10*z7plus^2 + 16*z7plus - 16)*q7p^135 + (-44*z7plus^2 + 8*z7plus + 132)*q7p^136 + (48*z7plus^2 - 24*z7plus - 144)*q7p^137 + (12*z7plus^2 - 20*z7plus + 20)*q7p^138 + (42*z7plus^2 + 42*z7plus)*q7p^139 + (-18*z7plus^2 - 12*z7plus + 12)*q7p^141 + (40*z7plus^2 + 36*z7plus - 36)*q7p^142 + (14*z7plus^2 + 14*z7plus - 42)*q7p^143 + (16*z7plus^2 - 64*z7plus - 48)*q7p^144 + (38*z7plus^2 + 58*z7plus - 58)*q7p^145 + (72*z7plus^2 + 48*z7plus - 48)*q7p^146 + (-8*z7plus^2 - 52*z7plus + 52)*q7p^149 + (-6*z7plus^2 - 4*z7plus + 18)*q7p^150 + (-8*z7plus^2 + 46*z7plus + 24)*q7p^151 + (-96*z7plus^2 - 120*z7plus + 120)*q7p^152 + (-52*z7plus^2 - 44*z7plus + 16)*q7p^153 + (-66*z7plus^2 - 30*z7plus + 72)*q7p^155 + (68*z7plus^2 - 20*z7plus - 204)*q7p^157 + (-34*z7plus^2 - 32*z7plus + 102)*q7p^158 + (-12*z7plus^2 + 6*z7plus - 6)*q7p^159 + (62*z7plus^2 + 46*z7plus - 32)*q7p^162 + (-36*z7plus^2 - 66*z7plus + 66)*q7p^163 + (-18*z7plus^2 - 26*z7plus + 54)*q7p^165 + (14*z7plus + 28)*q7p^167 + (-48*z7plus^2 - 4*z7plus + 88)*q7p^169 + (-4*z7plus^2 - 26*z7plus + 26)*q7p^170 + (24*z7plus^2 - 96*z7plus - 72)*q7p^171 + (30*z7plus^2 + 48*z7plus - 48)*q7p^173 + (-38*z7plus^2 - 2*z7plus + 72)*q7p^174 + (8*z7plus^2 - 32*z7plus - 80)*q7p^176 + (-24*z7plus^2 - 2*z7plus + 2)*q7p^177 + (-16*z7plus^2 + 64*z7plus + 48)*q7p^178 + (-36*z7plus^2 + 60*z7plus + 108)*q7p^179 + (-126*z7plus^2 - 42*z7plus + 168)*q7p^181 + (-4*z7plus^2 - 12*z7plus - 16)*q7p^183 + (104*z7plus^2 + 144*z7plus - 144)*q7p^184 + (2*z7plus^2 + 20*z7plus - 6)*q7p^185 + (24*z7plus^2 - 12*z7plus - 72)*q7p^186 + (58*z7plus^2 + 20*z7plus - 20)*q7p^187 + (60*z7plus^2 + 12*z7plus - 96)*q7p^190 + (90*z7plus^2 + 102*z7plus - 102)*q7p^191 + (-16*z7plus^2 - 48*z7plus + 48)*q7p^192 + (-64*z7plus^2 + 32*z7plus + 192)*q7p^193 + (84*z7plus^2 + 126*z7plus - 126)*q7p^194 + (-14*z7plus^2 + 28)*q7p^195 + (-82*z7plus^2 - 50*z7plus + 64)*q7p^197 + (40*z7plus^2 + 8*z7plus - 8)*q7p^198 + (26*z7plus^2 - 20*z7plus - 78)*q7p^199+O(q7p^200));
f2:=LL!( (-2*z7plus^2 - 6*z7plus + 6)*q7p + (-16*z7plus^2 + 8*z7plus + 48)*q7p^2 + (-12*z7plus^2 - 8*z7plus + 8)*q7p^3 + (42*z7plus^2 + 28*z7plus - 28)*q7p^4 + (-4*z7plus^2 + 2*z7plus + 12)*q7p^5 + (2*z7plus^2 + 6*z7plus - 6)*q7p^6 + (-28*z7plus^2 + 28*z7plus + 56)*q7p^7 + (-12*z7plus^2 - 36*z7plus + 36)*q7p^8 + (24*z7plus^2 - 12*z7plus - 72)*q7p^9 + (24*z7plus^2 + 16*z7plus - 16)*q7p^10 + (-24*z7plus^2 - 16*z7plus + 16)*q7p^11 + (16*z7plus^2 + 48*z7plus - 48)*q7p^13 + (98*z7plus^2 + 28*z7plus - 154)*q7p^14 + (4*z7plus^2 + 12*z7plus - 12)*q7p^15 + (-12*z7plus^2 + 6*z7plus + 36)*q7p^16 + (48*z7plus^2 + 32*z7plus - 32)*q7p^17 + (-60*z7plus^2 - 40*z7plus + 40)*q7p^18 + (-24*z7plus^2 + 12*z7plus + 72)*q7p^19 + (-14*z7plus^2 - 42*z7plus + 42)*q7p^20 + (14*z7plus^2 - 14*z7plus - 28)*q7p^21 + (4*z7plus^2 + 12*z7plus - 12)*q7p^22 + (-8*z7plus^2 + 4*z7plus + 24)*q7p^23 + (-30*z7plus^2 - 20*z7plus + 20)*q7p^24 + (6*z7plus^2 + 4*z7plus - 4)*q7p^25 + (72*z7plus^2 - 36*z7plus - 216)*q7p^26 + (-8*z7plus^2 - 24*z7plus + 24)*q7p^27 + (-112*z7plus^2 - 140*z7plus + 140)*q7p^28 + (2*z7plus^2 + 6*z7plus - 6)*q7p^29 + (4*z7plus^2 - 2*z7plus - 12)*q7p^30 + (-36*z7plus^2 - 24*z7plus + 24)*q7p^31 + (24*z7plus^2 - 12*z7plus - 72)*q7p^33 + (-36*z7plus^2 - 108*z7plus + 108)*q7p^34 + (56*z7plus^2 + 28*z7plus - 84)*q7p^35 + (28*z7plus^2 + 84*z7plus - 84)*q7p^36 + (60*z7plus^2 + 40*z7plus - 40)*q7p^38 + (12*z7plus^2 + 8*z7plus - 8)*q7p^39 + (-24*z7plus^2 + 12*z7plus + 72)*q7p^40 + (22*z7plus^2 + 66*z7plus - 66)*q7p^41 + (28*z7plus^2 - 28*z7plus - 56)*q7p^42 + (-4*z7plus^2 - 12*z7plus + 12)*q7p^43 + (-36*z7plus^2 - 24*z7plus + 24)*q7p^45 + (6*z7plus^2 + 4*z7plus - 4)*q7p^46 + (-8*z7plus^2 + 4*z7plus + 24)*q7p^47 + (12*z7plus^2 + 36*z7plus - 36)*q7p^48 + (-14*z7plus^2 + 98*z7plus + 56)*q7p^49 + (-8*z7plus^2 - 24*z7plus + 24)*q7p^50 + (8*z7plus^2 - 4*z7plus - 24)*q7p^51 + (-168*z7plus^2 - 112*z7plus + 112)*q7p^52 + (12*z7plus^2 + 8*z7plus - 8)*q7p^53 + (-36*z7plus^2 + 18*z7plus + 108)*q7p^54 + (8*z7plus^2 + 24*z7plus - 24)*q7p^55 + (-84*z7plus^2 + 126*z7plus + 182)*q7p^56 + (-4*z7plus^2 - 12*z7plus + 12)*q7p^57 + (16*z7plus^2 - 8*z7plus - 48)*q7p^58 + (84*z7plus^2 + 56*z7plus - 56)*q7p^59 + (-60*z7plus^2 + 30*z7plus + 180)*q7p^61 + (48*z7plus^2 + 144*z7plus - 144)*q7p^62 + (-84*z7plus^2 + 140)*q7p^63 + (26*z7plus^2 + 78*z7plus - 78)*q7p^64 + (32*z7plus^2 - 16*z7plus - 96)*q7p^65 + (24*z7plus^2 + 16*z7plus - 16)*q7p^66 + (48*z7plus^2 + 32*z7plus - 32)*q7p^67 + (-112*z7plus^2 + 56*z7plus + 336)*q7p^68 + (-6*z7plus^2 - 18*z7plus + 18)*q7p^69 + (-70*z7plus^2 - 98*z7plus + 84)*q7p^70 + (-28*z7plus^2 - 84*z7plus + 84)*q7p^71 + (88*z7plus^2 - 44*z7plus - 264)*q7p^72 + (-24*z7plus^2 - 16*z7plus + 16)*q7p^73 + (8*z7plus^2 - 4*z7plus - 24)*q7p^75 + (-28*z7plus^2 - 84*z7plus + 84)*q7p^76 + (28*z7plus^2 - 28*z7plus - 56)*q7p^77 + (-16*z7plus^2 - 48*z7plus + 48)*q7p^78 + (-72*z7plus^2 + 36*z7plus + 216)*q7p^79 + (18*z7plus^2 + 12*z7plus - 12)*q7p^80 + (102*z7plus^2 + 68*z7plus - 68)*q7p^81 + (120*z7plus^2 - 60*z7plus - 360)*q7p^82 + (-56*z7plus^2 - 168*z7plus + 168)*q7p^83 + (-126*z7plus^2 - 84*z7plus + 182)*q7p^84 + (-16*z7plus^2 - 48*z7plus + 48)*q7p^85 + (-60*z7plus^2 + 30*z7plus + 180)*q7p^86 + (12*z7plus^2 + 8*z7plus - 8)*q7p^87 + (-60*z7plus^2 - 40*z7plus + 40)*q7p^88 + (60*z7plus^2 - 30*z7plus - 180)*q7p^89 + (20*z7plus^2 + 60*z7plus - 60)*q7p^90 + (56*z7plus^2 - 140*z7plus - 140)*q7p^91 + (-48*z7plus^2 + 24*z7plus + 144)*q7p^93 + (48*z7plus^2 + 32*z7plus - 32)*q7p^94 + (36*z7plus^2 + 24*z7plus - 24)*q7p^95 + (-28*z7plus^2 + 14*z7plus + 84)*q7p^96 + (-36*z7plus^2 - 108*z7plus + 108)*q7p^97 + (280*z7plus^2 + 140*z7plus - 420)*q7p^98 + (8*z7plus^2 + 24*z7plus - 24)*q7p^99 + (-28*z7plus^2 + 14*z7plus + 84)*q7p^100 + (-138*z7plus^2 - 92*z7plus + 92)*q7p^101 + (-48*z7plus^2 - 32*z7plus + 32)*q7p^102 + (16*z7plus^2 - 8*z7plus - 48)*q7p^103 + (68*z7plus^2 + 204*z7plus - 204)*q7p^104 + (-28*z7plus^2 - 14*z7plus + 42)*q7p^105 + (12*z7plus^2 + 36*z7plus - 36)*q7p^106 + (-64*z7plus^2 + 32*z7plus + 192)*q7p^107 + (84*z7plus^2 + 56*z7plus - 56)*q7p^108 + (-138*z7plus^2 - 92*z7plus + 92)*q7p^109 + (8*z7plus^2 - 4*z7plus - 24)*q7p^110 + (168*z7plus^2 + 84*z7plus - 252)*q7p^112 + (28*z7plus^2 + 84*z7plus - 84)*q7p^113 + (24*z7plus^2 - 12*z7plus - 72)*q7p^114 + (12*z7plus^2 + 8*z7plus - 8)*q7p^115 + (-42*z7plus^2 - 28*z7plus + 28)*q7p^116 + (-80*z7plus^2 + 40*z7plus + 240)*q7p^117 + (-28*z7plus^2 - 84*z7plus + 84)*q7p^118 + (-140*z7plus^2 - 196*z7plus + 168)*q7p^119 + (10*z7plus^2 + 30*z7plus - 30)*q7p^120 + (92*z7plus^2 - 46*z7plus - 276)*q7p^121 + (108*z7plus^2 + 72*z7plus - 72)*q7p^122 + (48*z7plus^2 + 32*z7plus - 32)*q7p^123 + (168*z7plus^2 - 84*z7plus - 504)*q7p^124 + (-2*z7plus^2 - 6*z7plus + 6)*q7p^125 + (196*z7plus^2 + 308*z7plus - 224)*q7p^126 + (44*z7plus^2 + 132*z7plus - 132)*q7p^127 + (152*z7plus^2 - 76*z7plus - 456)*q7p^128 + (-66*z7plus^2 - 44*z7plus + 44)*q7p^129 + (-108*z7plus^2 - 72*z7plus + 72)*q7p^130 + (128*z7plus^2 - 64*z7plus - 384)*q7p^131 + (-28*z7plus^2 - 84*z7plus + 84)*q7p^132 + (84*z7plus^2 - 140)*q7p^133 + (-78*z7plus^2 - 234*z7plus + 234)*q7p^134 + (-16*z7plus^2 + 8*z7plus + 48)*q7p^135 + (204*z7plus^2 + 136*z7plus - 136)*q7p^136 + (-96*z7plus^2 - 64*z7plus + 64)*q7p^137 + (8*z7plus^2 - 4*z7plus - 24)*q7p^138 + (64*z7plus^2 + 192*z7plus - 192)*q7p^139 + (-28*z7plus^2 + 112*z7plus + 84)*q7p^140 + (8*z7plus^2 + 24*z7plus - 24)*q7p^141 + (-56*z7plus^2 + 28*z7plus + 168)*q7p^142 + (24*z7plus^2 + 16*z7plus - 16)*q7p^143 + (-108*z7plus^2 - 72*z7plus + 72)*q7p^144 + (4*z7plus^2 - 2*z7plus - 12)*q7p^145 + (4*z7plus^2 + 12*z7plus - 12)*q7p^146 + (-56*z7plus^2 + 56*z7plus + 112)*q7p^147 + (-4*z7plus^2 + 2*z7plus + 12)*q7p^149 + (-6*z7plus^2 - 4*z7plus + 4)*q7p^150 + (108*z7plus^2 + 72*z7plus - 72)*q7p^151 + (-88*z7plus^2 + 44*z7plus + 264)*q7p^152 + (40*z7plus^2 + 120*z7plus - 120)*q7p^153 + (56*z7plus^2 - 56*z7plus - 112)*q7p^154 + (12*z7plus^2 + 36*z7plus - 36)*q7p^155 + (-56*z7plus^2 + 28*z7plus + 168)*q7p^156 + (180*z7plus^2 + 120*z7plus - 120)*q7p^157 + (348*z7plus^2 + 232*z7plus - 232)*q7p^158 + (-40*z7plus^2 + 20*z7plus + 120)*q7p^159 + (-14*z7plus^2 - 28*z7plus + 14)*q7p^161 + (-52*z7plus^2 - 156*z7plus + 156)*q7p^162 + (-24*z7plus^2 + 12*z7plus + 72)*q7p^163 + (-294*z7plus^2 - 196*z7plus + 196)*q7p^164 + (-36*z7plus^2 - 24*z7plus + 24)*q7p^165 + (-196*z7plus^2 + 98*z7plus + 588)*q7p^166 + (-48*z7plus^2 - 144*z7plus + 144)*q7p^167 + (56*z7plus^2 + 28*z7plus - 84)*q7p^168 + (-46*z7plus^2 - 138*z7plus + 138)*q7p^169 + (-72*z7plus^2 + 36*z7plus + 216)*q7p^170 + (-48*z7plus^2 - 32*z7plus + 32)*q7p^171 + (168*z7plus^2 + 112*z7plus - 112)*q7p^172 + (-64*z7plus^2 + 32*z7plus + 192)*q7p^173 + (-2*z7plus^2 - 6*z7plus + 6)*q7p^174 + (-28*z7plus^2 - 56*z7plus + 28)*q7p^175 + (24*z7plus^2 + 72*z7plus - 72)*q7p^176 + (-56*z7plus^2 + 28*z7plus + 168)*q7p^177 + (-192*z7plus^2 - 128*z7plus + 128)*q7p^178 + (-60*z7plus^2 - 40*z7plus + 40)*q7p^179 + (56*z7plus^2 - 28*z7plus - 168)*q7p^180 + (-18*z7plus^2 - 54*z7plus + 54)*q7p^181 + (-504*z7plus^2 - 168*z7plus + 784)*q7p^182 + (-24*z7plus^2 - 72*z7plus + 72)*q7p^183 + (-20*z7plus^2 + 10*z7plus + 60)*q7p^184 + (36*z7plus^2 + 24*z7plus - 24)*q7p^186 + (16*z7plus^2 - 8*z7plus - 48)*q7p^187 + (-28*z7plus^2 - 84*z7plus + 84)*q7p^188 + (-28*z7plus^2 + 70*z7plus + 70)*q7p^189 + (-20*z7plus^2 - 60*z7plus + 60)*q7p^190 + (64*z7plus^2 - 32*z7plus - 192)*q7p^191 + (72*z7plus^2 + 48*z7plus - 48)*q7p^192 + (-12*z7plus^2 - 8*z7plus + 8)*q7p^193 + (-176*z7plus^2 + 88*z7plus + 528)*q7p^194 + (-4*z7plus^2 - 12*z7plus + 12)*q7p^195 + (-182*z7plus^2 - 448*z7plus + 154)*q7p^196 + (12*z7plus^2 + 36*z7plus - 36)*q7p^197 + (-48*z7plus^2 + 24*z7plus + 144)*q7p^198 + (-96*z7plus^2 - 64*z7plus + 64)*q7p^199+O(q7p^200));
f3:=LL!((-3*z7plus^2 - 9*z7plus + 9)*q7p + (-10*z7plus^2 + 5*z7plus + 30)*q7p^2 + (3*z7plus^2 + 2*z7plus - 2)*q7p^3 + (21*z7plus^2 + 14*z7plus - 14)*q7p^4 + (-6*z7plus^2 + 3*z7plus + 18)*q7p^5 + (3*z7plus^2 + 9*z7plus - 9)*q7p^6 + (21*z7plus + 7)*q7p^7 + (-11*z7plus^2 - 33*z7plus + 33)*q7p^8 + (8*z7plus^2 - 4*z7plus - 24)*q7p^9 + (15*z7plus^2 + 10*z7plus - 10)*q7p^10 + (6*z7plus^2 + 4*z7plus - 4)*q7p^11 + (14*z7plus^2 - 7*z7plus - 42)*q7p^12 + (10*z7plus^2 + 30*z7plus - 30)*q7p^13 + (77*z7plus^2 + 28*z7plus - 119)*q7p^14 + (-z7plus^2 - 3*z7plus + 3)*q7p^15 + (-18*z7plus^2 + 9*z7plus + 54)*q7p^16 + (30*z7plus^2 + 20*z7plus - 20)*q7p^17 + (-48*z7plus^2 - 32*z7plus + 32)*q7p^18 + (-8*z7plus^2 + 4*z7plus + 24)*q7p^19 + (-7*z7plus^2 - 21*z7plus + 21)*q7p^20 + (7*z7plus^2 + 35*z7plus)*q7p^21 + (6*z7plus^2 + 18*z7plus - 18)*q7p^22 + (2*z7plus^2 - z7plus - 6)*q7p^23 + (-3*z7plus^2 - 2*z7plus + 2)*q7p^24 + (9*z7plus^2 + 6*z7plus - 6)*q7p^25 + (52*z7plus^2 - 26*z7plus - 156)*q7p^26 + (-5*z7plus^2 - 15*z7plus + 15)*q7p^27 + (-77*z7plus^2 - 133*z7plus + 84)*q7p^28 + (3*z7plus^2 + 9*z7plus - 9)*q7p^29 + (6*z7plus^2 - 3*z7plus - 18)*q7p^30 + (-54*z7plus^2 - 36*z7plus + 36)*q7p^31 + (-21*z7plus^2 - 14*z7plus + 14)*q7p^32 + (-20*z7plus^2 + 10*z7plus + 60)*q7p^33 + (-26*z7plus^2 - 78*z7plus + 78)*q7p^34 + (21*z7plus^2 - 35)*q7p^35 + (28*z7plus^2 + 84*z7plus - 84)*q7p^36 + (48*z7plus^2 + 32*z7plus - 32)*q7p^38 + (18*z7plus^2 + 12*z7plus - 12)*q7p^39 + (-22*z7plus^2 + 11*z7plus + 66)*q7p^40 + (19*z7plus^2 + 57*z7plus - 57)*q7p^41 + (-21*z7plus - 7)*q7p^42 + (-13*z7plus^2 - 39*z7plus + 39)*q7p^43 + (28*z7plus^2 - 14*z7plus - 84)*q7p^44 + (-12*z7plus^2 - 8*z7plus + 8)*q7p^45 + (9*z7plus^2 + 6*z7plus - 6)*q7p^46 + (-12*z7plus^2 + 6*z7plus + 36)*q7p^47 + (-3*z7plus^2 - 9*z7plus + 9)*q7p^48 + (-63*z7plus^2 + 21*z7plus + 112)*q7p^49 + (-5*z7plus^2 - 15*z7plus + 15)*q7p^50 + (12*z7plus^2 - 6*z7plus - 36)*q7p^51 + (-126*z7plus^2 - 84*z7plus + 84)*q7p^52 + (-24*z7plus^2 - 16*z7plus + 16)*q7p^53 + (-26*z7plus^2 + 13*z7plus + 78)*q7p^54 + (-2*z7plus^2 - 6*z7plus + 6)*q7p^55 + (-28*z7plus^2 + 91*z7plus + 77)*q7p^56 + (8*z7plus^2 + 24*z7plus - 24)*q7p^57 + (10*z7plus^2 - 5*z7plus - 30)*q7p^58 + (-21*z7plus^2 - 14*z7plus + 14)*q7p^60 + (-6*z7plus^2 + 3*z7plus + 18)*q7p^61 + (30*z7plus^2 + 90*z7plus - 90)*q7p^62 + (-112*z7plus^2 - 56*z7plus + 168)*q7p^63 + (25*z7plus^2 + 75*z7plus - 75)*q7p^64 + (20*z7plus^2 - 10*z7plus - 60)*q7p^65 + (-6*z7plus^2 - 4*z7plus + 4)*q7p^66 + (93*z7plus^2 + 62*z7plus - 62)*q7p^67 + (-84*z7plus^2 + 42*z7plus + 252)*q7p^68 + (5*z7plus^2 + 15*z7plus - 15)*q7p^69 + (-49*z7plus^2 - 77*z7plus + 56)*q7p^70 + (48*z7plus^2 - 24*z7plus - 144)*q7p^72 + (6*z7plus^2 + 4*z7plus - 4)*q7p^73 + (-2*z7plus^2 + z7plus + 6)*q7p^75 + (-28*z7plus^2 - 84*z7plus + 84)*q7p^76 + (14*z7plus^2 + 70*z7plus)*q7p^77 + (-10*z7plus^2 - 30*z7plus + 30)*q7p^78 + (-80*z7plus^2 + 40*z7plus + 240)*q7p^79 + (27*z7plus^2 + 18*z7plus - 18)*q7p^80 + (27*z7plus^2 + 18*z7plus - 18)*q7p^81 + (82*z7plus^2 - 41*z7plus - 246)*q7p^82 + (-21*z7plus^2 - 63*z7plus + 63)*q7p^83 + (-7*z7plus^2 + 28*z7plus + 21)*q7p^84 + (-10*z7plus^2 - 30*z7plus + 30)*q7p^85 + (-34*z7plus^2 + 17*z7plus + 102)*q7p^86 + (-3*z7plus^2 - 2*z7plus + 2)*q7p^87 + (-6*z7plus^2 - 4*z7plus + 4)*q7p^88 + (34*z7plus^2 - 17*z7plus - 102)*q7p^89 + (16*z7plus^2 + 48*z7plus - 48)*q7p^90 + (56*z7plus^2 - 98*z7plus - 126)*q7p^91 + (-7*z7plus^2 - 21*z7plus + 21)*q7p^92 + (12*z7plus^2 - 6*z7plus - 36)*q7p^93 + (30*z7plus^2 + 20*z7plus - 20)*q7p^94 + (12*z7plus^2 + 8*z7plus - 8)*q7p^95 + (14*z7plus^2 - 7*z7plus - 42)*q7p^96 + (-26*z7plus^2 - 78*z7plus + 78)*q7p^97 + (196*z7plus^2 + 77*z7plus - 301)*q7p^98 + (-16*z7plus^2 - 48*z7plus + 48)*q7p^99 + (-14*z7plus^2 + 7*z7plus + 42)*q7p^100 + (-39*z7plus^2 - 26*z7plus + 26)*q7p^101 + (-30*z7plus^2 - 20*z7plus + 20)*q7p^102 + (10*z7plus^2 - 5*z7plus - 30)*q7p^103 + (46*z7plus^2 + 138*z7plus - 138)*q7p^104 + (28*z7plus^2 - 7*z7plus - 49)*q7p^105 + (4*z7plus^2 + 12*z7plus - 12)*q7p^106 + (-54*z7plus^2 + 27*z7plus + 162)*q7p^107 + (63*z7plus^2 + 42*z7plus - 42)*q7p^108 + (-81*z7plus^2 - 54*z7plus + 54)*q7p^109 + (12*z7plus^2 - 6*z7plus - 36)*q7p^110 + (63*z7plus^2 - 105)*q7p^112 + (8*z7plus^2 - 4*z7plus - 24)*q7p^114 + (-3*z7plus^2 - 2*z7plus + 2)*q7p^115 + (-21*z7plus^2 - 14*z7plus + 14)*q7p^116 + (-64*z7plus^2 + 32*z7plus + 192)*q7p^117 + (-28*z7plus^2 - 84*z7plus + 84)*q7p^118 + (-98*z7plus^2 - 154*z7plus + 112)*q7p^119 + (z7plus^2 + 3*z7plus - 3)*q7p^120 + (26*z7plus^2 - 13*z7plus - 78)*q7p^121 + (99*z7plus^2 + 66*z7plus - 66)*q7p^122 + (9*z7plus^2 + 6*z7plus - 6)*q7p^123 + (84*z7plus^2 - 42*z7plus - 252)*q7p^124 + (-3*z7plus^2 - 9*z7plus + 9)*q7p^125 + (140*z7plus^2 + 196*z7plus - 168)*q7p^126 + (10*z7plus^2 + 30*z7plus - 30)*q7p^127 + (74*z7plus^2 - 37*z7plus - 222)*q7p^128 + (27*z7plus^2 + 18*z7plus - 18)*q7p^129 + (-78*z7plus^2 - 52*z7plus + 52)*q7p^130 + (80*z7plus^2 - 40*z7plus - 240)*q7p^131 + (14*z7plus^2 + 42*z7plus - 42)*q7p^132 + (112*z7plus^2 + 56*z7plus - 168)*q7p^133 + (-47*z7plus^2 - 141*z7plus + 141)*q7p^134 + (-10*z7plus^2 + 5*z7plus + 30)*q7p^135 + (138*z7plus^2 + 92*z7plus - 92)*q7p^136 + (-60*z7plus^2 - 40*z7plus + 40)*q7p^137 + (-2*z7plus^2 + z7plus + 6)*q7p^138 + (26*z7plus^2 + 78*z7plus - 78)*q7p^139 + (-56*z7plus^2 + 77*z7plus + 119)*q7p^140 + (-2*z7plus^2 - 6*z7plus + 6)*q7p^141 + (-56*z7plus^2 + 28*z7plus + 168)*q7p^142 + (36*z7plus^2 + 24*z7plus - 24)*q7p^143 + (-36*z7plus^2 - 24*z7plus + 24)*q7p^144 + (6*z7plus^2 - 3*z7plus - 18)*q7p^145 + (6*z7plus^2 + 18*z7plus - 18)*q7p^146 + (77*z7plus^2 + 28*z7plus - 119)*q7p^147 + (22*z7plus^2 - 11*z7plus - 66)*q7p^149 + (-9*z7plus^2 - 6*z7plus + 6)*q7p^150 + (78*z7plus^2 + 52*z7plus - 52)*q7p^151 + (-48*z7plus^2 + 24*z7plus + 144)*q7p^152 + (32*z7plus^2 + 96*z7plus - 96)*q7p^153 + (-42*z7plus - 14)*q7p^154 + (18*z7plus^2 + 54*z7plus - 54)*q7p^155 + (-28*z7plus^2 + 14*z7plus + 84)*q7p^156 + (102*z7plus^2 + 68*z7plus - 68)*q7p^157 + (228*z7plus^2 + 152*z7plus - 152)*q7p^158 + (24*z7plus^2 - 12*z7plus - 72)*q7p^159 + (7*z7plus^2 + 21*z7plus - 21)*q7p^160 + (35*z7plus^2 + 28*z7plus - 49)*q7p^161 + (-43*z7plus^2 - 129*z7plus + 129)*q7p^162 + (-92*z7plus^2 + 46*z7plus + 276)*q7p^163 + (-189*z7plus^2 - 126*z7plus + 126)*q7p^164 + (30*z7plus^2 + 20*z7plus - 20)*q7p^165 + (-154*z7plus^2 + 77*z7plus + 462)*q7p^166 + (-65*z7plus^2 - 195*z7plus + 195)*q7p^167 + (35*z7plus^2 + 91*z7plus - 28)*q7p^168 + (-13*z7plus^2 - 39*z7plus + 39)*q7p^169 + (-52*z7plus^2 + 26*z7plus + 156)*q7p^170 + (-72*z7plus^2 - 48*z7plus + 48)*q7p^171 + (63*z7plus^2 + 42*z7plus - 42)*q7p^172 + (16*z7plus^2 - 8*z7plus - 48)*q7p^173 + (-3*z7plus^2 - 9*z7plus + 9)*q7p^174 + (-21*z7plus^2 - 21*z7plus + 28)*q7p^175 + (-6*z7plus^2 - 18*z7plus + 18)*q7p^176 + (56*z7plus^2 - 28*z7plus - 168)*q7p^177 + (-141*z7plus^2 - 94*z7plus + 94)*q7p^178 + (-90*z7plus^2 - 60*z7plus + 60)*q7p^179 + (56*z7plus^2 - 28*z7plus - 168)*q7p^180 + (z7plus^2 + 3*z7plus - 3)*q7p^181 + (-350*z7plus^2 - 112*z7plus + 546)*q7p^182 + (27*z7plus^2 + 81*z7plus - 81)*q7p^183 + (-2*z7plus^2 + z7plus + 6)*q7p^184 + (54*z7plus^2 + 36*z7plus - 36)*q7p^186 + (24*z7plus^2 - 12*z7plus - 72)*q7p^187 + (-14*z7plus^2 - 42*z7plus + 42)*q7p^188 + (-28*z7plus^2 + 49*z7plus + 63)*q7p^189 + (-16*z7plus^2 - 48*z7plus + 48)*q7p^190 + (68*z7plus^2 - 34*z7plus - 204)*q7p^191 + (3*z7plus^2 + 2*z7plus - 2)*q7p^192 + (-18*z7plus^2 - 12*z7plus + 12)*q7p^193 + (-124*z7plus^2 + 62*z7plus + 372)*q7p^194 + (-6*z7plus^2 - 18*z7plus + 18)*q7p^195 + (-217*z7plus^2 - 308*z7plus + 259)*q7p^196 + (46*z7plus^2 + 138*z7plus - 138)*q7p^197 + (-16*z7plus^2 + 8*z7plus + 48)*q7p^198 + (-60*z7plus^2 - 40*z7plus + 40)*q7p^199+O(q7p^200));
f4:=LL!((10*z7plus^2 + 2*z7plus - 16)*q7p + (-4*z7plus^2 - 12*z7plus + 12)*q7p^2 + (-10*z7plus^2 + 12*z7plus + 30)*q7p^3 + (-8*z7plus^2 - 10*z7plus + 10)*q7p^5 + (32*z7plus^2 + 12*z7plus - 40)*q7p^6 + (-24*z7plus^2 - 16*z7plus + 16)*q7p^8 + (-8*z7plus^2 - 24*z7plus + 24)*q7p^9 + (-8*z7plus^2 + 4*z7plus + 24)*q7p^10 + (22*z7plus^2 - 32*z7plus - 66)*q7p^11 + (18*z7plus^2 - 2*z7plus - 40)*q7p^13 + (22*z7plus^2 + 10*z7plus - 24)*q7p^15 + (32*z7plus^2 + 40*z7plus - 40)*q7p^16 + (26*z7plus^2 - 20*z7plus - 78)*q7p^17 + (-8*z7plus^2 + 32*z7plus + 24)*q7p^18 + (-48*z7plus^2 - 60*z7plus + 60)*q7p^19 + (-76*z7plus^2 - 32*z7plus + 88)*q7p^22 + (-44*z7plus^2 - 48*z7plus + 48)*q7p^23 + (24*z7plus^2 - 40*z7plus - 72)*q7p^24 + (-2*z7plus^2 + 8*z7plus + 6)*q7p^25 + (4*z7plus^2 - 16*z7plus + 16)*q7p^26 + (-2*z7plus^2 - 6*z7plus - 8)*q7p^27 + (18*z7plus^2 + 26*z7plus + 16)*q7p^29 + (-20*z7plus^2 - 32*z7plus + 32)*q7p^30 + (12*z7plus^2 + 36*z7plus - 36)*q7p^31 + (76*z7plus^2 + 130*z7plus - 130)*q7p^33 + (-72*z7plus^2 - 20*z7plus + 104)*q7p^34 + (28*z7plus^2 + 56*z7plus - 56)*q7p^37 + (-48*z7plus^2 + 24*z7plus + 144)*q7p^38 + (-18*z7plus^2 + 16*z7plus + 54)*q7p^39 + (8*z7plus^2 + 24*z7plus - 24)*q7p^40 + (16*z7plus^2 + 20*z7plus + 8)*q7p^41 + (20*z7plus^2 + 4*z7plus - 32)*q7p^43 + (-16*z7plus^2 + 8*z7plus + 48)*q7p^45 + (-44*z7plus^2 + 8*z7plus + 132)*q7p^46 + (12*z7plus^2 - 6*z7plus + 6)*q7p^47 + (-88*z7plus^2 - 40*z7plus + 96)*q7p^48 + (12*z7plus^2 + 8*z7plus - 8)*q7p^50 + (72*z7plus^2 + 118*z7plus - 118)*q7p^51 + (24*z7plus^2 - 12*z7plus - 72)*q7p^53 + (12*z7plus^2 + 8*z7plus - 8)*q7p^54 + (-54*z7plus^2 - 22*z7plus + 64)*q7p^55 + (132*z7plus^2 + 60*z7plus - 144)*q7p^57 + (-52*z7plus^2 - 44*z7plus + 44)*q7p^58 + (-28*z7plus^2 + 28*z7plus + 84)*q7p^59 + (-8*z7plus^2 - 24*z7plus + 24)*q7p^61 + (12*z7plus^2 + 36*z7plus + 48)*q7p^62 + (80*z7plus^2 + 16*z7plus - 128)*q7p^64 + (-20*z7plus^2 - 18*z7plus + 18)*q7p^65 + (76*z7plus^2 - 108*z7plus - 228)*q7p^66 + (-16*z7plus^2 - 20*z7plus + 48)*q7p^67 + (100*z7plus^2 + 48*z7plus - 104)*q7p^69 + (-84*z7plus^2 - 28*z7plus + 112)*q7p^71 + (64*z7plus^2 + 80*z7plus - 80)*q7p^72 + (-48*z7plus^2 + 24*z7plus + 144)*q7p^73 + (28*z7plus^2 - 56*z7plus - 84)*q7p^74 + (-12*z7plus^2 - 22*z7plus + 22)*q7p^75 + (52*z7plus^2 + 16*z7plus - 72)*q7p^78 + (80*z7plus^2 + 142*z7plus - 142)*q7p^79 + (8*z7plus^2 - 32*z7plus - 24)*q7p^80 + (50*z7plus^2 - 32*z7plus - 150)*q7p^81 + (-40*z7plus^2 - 36*z7plus + 36)*q7p^82 + (-46*z7plus^2 - 26*z7plus + 40)*q7p^85 + (-8*z7plus^2 - 24*z7plus + 24)*q7p^86 + (-18*z7plus^2 + 44*z7plus + 54)*q7p^87 + (-64*z7plus^2 + 88*z7plus + 192)*q7p^88 + (64*z7plus^2 + 80*z7plus - 80)*q7p^89 + (40*z7plus^2 + 8*z7plus - 64)*q7p^90 + (-12*z7plus^2 - 36*z7plus + 36)*q7p^93 + (12*z7plus^2 + 36*z7plus - 36)*q7p^94 + (-12*z7plus^2 + 48*z7plus + 36)*q7p^95 + (54*z7plus^2 - 6*z7plus - 120)*q7p^97 + (-152*z7plus^2 - 64*z7plus + 176)*q7p^99 + (60*z7plus^2 - 72*z7plus - 180)*q7p^101 + (72*z7plus^2 - 92*z7plus - 216)*q7p^102 + (-108*z7plus^2 - 114*z7plus + 114)*q7p^103 + (-32*z7plus^2 - 40*z7plus - 16)*q7p^104 + (-60*z7plus^2 - 12*z7plus + 96)*q7p^106 + (-72*z7plus^2 - 132*z7plus + 132)*q7p^107 + (-10*z7plus^2 + 40*z7plus + 30)*q7p^109 + (44*z7plus^2 + 76*z7plus - 76)*q7p^110 + (-140*z7plus^2 - 56*z7plus + 168)*q7p^111 + (28*z7plus + 56)*q7p^113 + (-120*z7plus^2 - 192*z7plus + 192)*q7p^114 + (-4*z7plus^2 + 44*z7plus + 12)*q7p^115 + (8*z7plus^2 - 32*z7plus + 32)*q7p^117 + (84*z7plus^2 + 28*z7plus - 112)*q7p^118 + (-64*z7plus^2 - 24*z7plus + 80)*q7p^120 + (-96*z7plus^2 - 204*z7plus + 204)*q7p^121 + (-8*z7plus^2 + 32*z7plus + 24)*q7p^122 + (-16*z7plus^2 + 36*z7plus + 48)*q7p^123 + (10*z7plus^2 + 2*z7plus - 16)*q7p^125 + (4*z7plus^2 - 16*z7plus - 40)*q7p^127 + (-32*z7plus^2 - 96*z7plus + 96)*q7p^128 + (-20*z7plus^2 + 24*z7plus + 60)*q7p^129 + (-20*z7plus^2 - 4*z7plus + 60)*q7p^130 + (-52*z7plus^2 - 44*z7plus + 44)*q7p^131 + (12*z7plus^2 - 20*z7plus - 64)*q7p^134 + (-4*z7plus^2 + 2*z7plus - 2)*q7p^135 + (-40*z7plus^2 + 104*z7plus + 120)*q7p^136 + (-24*z7plus^2 + 96*z7plus + 72)*q7p^137 + (-96*z7plus^2 - 148*z7plus + 148)*q7p^138 + (156*z7plus^2 + 48*z7plus - 216)*q7p^139 + (30*z7plus^2 + 6*z7plus - 48)*q7p^141 + (56*z7plus^2 + 112*z7plus - 112)*q7p^142 + (34*z7plus^2 - 52*z7plus - 102)*q7p^143 + (64*z7plus^2 - 32*z7plus - 192)*q7p^144 + (8*z7plus^2 - 18*z7plus + 18)*q7p^145 + (120*z7plus^2 + 24*z7plus - 192)*q7p^146 + (104*z7plus^2 + 144*z7plus - 144)*q7p^149 + (-12*z7plus^2 + 20*z7plus + 36)*q7p^150 + (-50*z7plus^2 + 32*z7plus + 150)*q7p^151 + (48*z7plus^2 + 144*z7plus - 144)*q7p^152 + (-144*z7plus^2 - 40*z7plus + 208)*q7p^153 + (24*z7plus^2 - 12*z7plus - 72)*q7p^155 + (52*z7plus^2 - 152*z7plus - 156)*q7p^157 + (80*z7plus^2 - 124*z7plus - 240)*q7p^158 + (60*z7plus^2 + 96*z7plus - 96)*q7p^159 + (-132*z7plus^2 - 32*z7plus + 200)*q7p^162 + (36*z7plus^2 + 24*z7plus - 24)*q7p^163 + (54*z7plus^2 - 76*z7plus - 162)*q7p^165 + (86*z7plus^2 + 34*z7plus - 104)*q7p^167 + (-92*z7plus^2 - 52*z7plus + 80)*q7p^169 + (52*z7plus^2 + 72*z7plus - 72)*q7p^170 + (-96*z7plus^2 + 48*z7plus + 288)*q7p^171 + (12*z7plus^2 - 6*z7plus + 6)*q7p^173 + (80*z7plus^2 + 44*z7plus - 72)*q7p^174 + (216*z7plus^2 + 88*z7plus - 256)*q7p^176 + (-84*z7plus^2 - 140*z7plus + 140)*q7p^177 + (64*z7plus^2 - 32*z7plus - 192)*q7p^178 + (-36*z7plus^2 - 24*z7plus + 108)*q7p^179 + (48*z7plus^2 + 60*z7plus + 24)*q7p^181 + (64*z7plus^2 + 24*z7plus - 80)*q7p^183 + (16*z7plus^2 + 104*z7plus - 104)*q7p^184 + (28*z7plus^2 - 28*z7plus - 84)*q7p^185 + (-12*z7plus^2 + 48*z7plus + 36)*q7p^186 + (-164*z7plus^2 - 282*z7plus + 282)*q7p^187 + (72*z7plus^2 + 48*z7plus - 48)*q7p^190 + (72*z7plus^2 + 174*z7plus - 174)*q7p^191 + (-80*z7plus^2 + 96*z7plus + 240)*q7p^192 + (32*z7plus^2 - 128*z7plus - 96)*q7p^193 + (12*z7plus^2 - 48*z7plus + 48)*q7p^194 + (34*z7plus^2 + 18*z7plus - 32)*q7p^195 + (108*z7plus^2 + 16*z7plus - 184)*q7p^197 + (128*z7plus^2 + 216*z7plus - 216)*q7p^198 + (4*z7plus^2 - 44*z7plus - 12)*q7p^199+O(q7p^200));
f5:=LL!( (6*z7plus^2 + 4*z7plus - 4)*q7p + (-8*z7plus^2 - 10*z7plus + 10)*q7p^2 + (-6*z7plus^2 + 10*z7plus + 18)*q7p^3 + (-2*z7plus^2 - 6*z7plus + 6)*q7p^5 + (22*z7plus^2 + 10*z7plus - 24)*q7p^6 + (-20*z7plus^2 - 4*z7plus + 32)*q7p^8 + (-16*z7plus^2 - 20*z7plus + 20)*q7p^9 + (-2*z7plus^2 + 8*z7plus + 6)*q7p^10 + (16*z7plus^2 - 22*z7plus - 48)*q7p^11 + (8*z7plus^2 + 10*z7plus + 4)*q7p^13 + (16*z7plus^2 + 6*z7plus - 20)*q7p^15 + (8*z7plus^2 + 24*z7plus - 24)*q7p^16 + (10*z7plus^2 - 26*z7plus - 30)*q7p^17 + (-16*z7plus^2 + 8*z7plus + 48)*q7p^18 + (-12*z7plus^2 - 36*z7plus + 36)*q7p^19 + (-54*z7plus^2 - 22*z7plus + 64)*q7p^22 + (-4*z7plus^2 - 26*z7plus + 26)*q7p^23 + (20*z7plus^2 - 24*z7plus - 60)*q7p^24 + (-4*z7plus^2 + 2*z7plus + 12)*q7p^25 + (-20*z7plus^2 - 18*z7plus + 18)*q7p^26 + (-4*z7plus^2 + 2*z7plus + 12)*q7p^27 + (22*z7plus^2 - 4*z7plus - 52)*q7p^29 + (-12*z7plus^2 - 22*z7plus + 22)*q7p^30 + (-18*z7plus^2 - 12*z7plus + 54)*q7p^31 + (54*z7plus^2 + 92*z7plus - 92)*q7p^33 + (-46*z7plus^2 - 26*z7plus + 40)*q7p^34 + (28*z7plus^2 + 42*z7plus - 42)*q7p^37 + (-12*z7plus^2 + 48*z7plus + 36)*q7p^38 + (-8*z7plus^2 + 18*z7plus + 24)*q7p^39 + (16*z7plus^2 + 20*z7plus - 20)*q7p^40 + (18*z7plus^2 - 2*z7plus - 40)*q7p^41 + (12*z7plus^2 + 8*z7plus - 8)*q7p^43 + (-4*z7plus^2 + 16*z7plus + 12)*q7p^45 + (-4*z7plus^2 + 44*z7plus + 12)*q7p^46 + (-18*z7plus^2 - 12*z7plus + 12)*q7p^47 + (-64*z7plus^2 - 24*z7plus + 80)*q7p^48 + (10*z7plus^2 + 2*z7plus - 16)*q7p^50 + (46*z7plus^2 + 82*z7plus - 82)*q7p^51 + (6*z7plus^2 - 24*z7plus - 18)*q7p^53 + (-4*z7plus^2 + 2*z7plus - 2)*q7p^54 + (-38*z7plus^2 - 16*z7plus + 44)*q7p^55 + (96*z7plus^2 + 36*z7plus - 120)*q7p^57 + (8*z7plus^2 - 18*z7plus + 18)*q7p^58 + (-14*z7plus^2 + 28*z7plus + 42)*q7p^59 + (-16*z7plus^2 - 20*z7plus + 20)*q7p^61 + (24*z7plus^2 - 12*z7plus - 72)*q7p^62 + (48*z7plus^2 + 32*z7plus - 32)*q7p^64 + (2*z7plus^2 - 8*z7plus + 8)*q7p^65 + (54*z7plus^2 - 76*z7plus - 162)*q7p^66 + (10*z7plus^2 + 16*z7plus - 30)*q7p^67 + (74*z7plus^2 + 26*z7plus - 96)*q7p^69 + (-56*z7plus^2 - 28*z7plus + 56)*q7p^71 + (16*z7plus^2 + 48*z7plus - 48)*q7p^72 + (-12*z7plus^2 + 48*z7plus + 36)*q7p^73 + (28*z7plus^2 - 28*z7plus - 84)*q7p^74 + (-10*z7plus^2 - 16*z7plus + 16)*q7p^75 + (34*z7plus^2 + 18*z7plus - 32)*q7p^78 + (62*z7plus^2 + 102*z7plus - 102)*q7p^79 + (16*z7plus^2 - 8*z7plus - 48)*q7p^80 + (16*z7plus^2 - 50*z7plus - 48)*q7p^81 + (4*z7plus^2 - 16*z7plus + 16)*q7p^82 + (-36*z7plus^2 - 10*z7plus + 52)*q7p^85 + (-16*z7plus^2 - 20*z7plus + 20)*q7p^86 + (-22*z7plus^2 + 18*z7plus + 66)*q7p^87 + (-44*z7plus^2 + 64*z7plus + 132)*q7p^88 + (16*z7plus^2 + 48*z7plus - 48)*q7p^89 + (24*z7plus^2 + 16*z7plus - 16)*q7p^90 + (-24*z7plus^2 - 30*z7plus + 30)*q7p^93 + (-18*z7plus^2 - 12*z7plus + 54)*q7p^94 + (-24*z7plus^2 + 12*z7plus + 72)*q7p^95 + (24*z7plus^2 + 30*z7plus + 12)*q7p^97 + (-108*z7plus^2 - 44*z7plus + 128)*q7p^99 + (36*z7plus^2 - 60*z7plus - 108)*q7p^101 + (46*z7plus^2 - 72*z7plus - 138)*q7p^102 + (-6*z7plus^2 - 60*z7plus + 60)*q7p^103 + (-36*z7plus^2 + 4*z7plus + 80)*q7p^104 + (-36*z7plus^2 - 24*z7plus + 24)*q7p^106 + (-60*z7plus^2 - 96*z7plus + 96)*q7p^107 + (-20*z7plus^2 + 10*z7plus + 60)*q7p^109 + (32*z7plus^2 + 54*z7plus - 54)*q7p^110 + (-98*z7plus^2 - 42*z7plus + 112)*q7p^111 + (14*z7plus^2 - 14*z7plus - 56)*q7p^113 + (-72*z7plus^2 - 132*z7plus + 132)*q7p^114 + (-22*z7plus^2 + 4*z7plus + 66)*q7p^115 + (-40*z7plus^2 - 36*z7plus + 36)*q7p^117 + (56*z7plus^2 + 28*z7plus - 56)*q7p^118 + (-44*z7plus^2 - 20*z7plus + 48)*q7p^120 + (-108*z7plus^2 - 156*z7plus + 156)*q7p^121 + (-16*z7plus^2 + 8*z7plus + 48)*q7p^122 + (-18*z7plus^2 + 16*z7plus + 54)*q7p^123 + (6*z7plus^2 + 4*z7plus - 4)*q7p^125 + (-6*z7plus^2 + 10*z7plus + 32)*q7p^127 + (-64*z7plus^2 - 80*z7plus + 80)*q7p^128 + (-12*z7plus^2 + 20*z7plus + 36)*q7p^129 + (2*z7plus^2 + 20*z7plus - 6)*q7p^130 + (8*z7plus^2 - 18*z7plus + 18)*q7p^131 + (-4*z7plus^2 + 16*z7plus + 40)*q7p^134 + (6*z7plus^2 + 4*z7plus - 4)*q7p^135 + (-52*z7plus^2 + 40*z7plus + 156)*q7p^136 + (-48*z7plus^2 + 24*z7plus + 144)*q7p^137 + (-52*z7plus^2 - 100*z7plus + 100)*q7p^138 + (102*z7plus^2 + 54*z7plus - 96)*q7p^139 + (18*z7plus^2 + 12*z7plus - 12)*q7p^141 + (56*z7plus^2 + 84*z7plus - 84)*q7p^142 + (26*z7plus^2 - 34*z7plus - 78)*q7p^143 + (16*z7plus^2 - 64*z7plus - 48)*q7p^144 + (-26*z7plus^2 - 22*z7plus + 22)*q7p^145 + (72*z7plus^2 + 48*z7plus - 48)*q7p^146 + (40*z7plus^2 + 92*z7plus - 92)*q7p^149 + (-10*z7plus^2 + 12*z7plus + 30)*q7p^150 + (-16*z7plus^2 + 50*z7plus + 48)*q7p^151 + (96*z7plus^2 + 120*z7plus - 120)*q7p^152 + (-92*z7plus^2 - 52*z7plus + 80)*q7p^153 + (6*z7plus^2 + 18*z7plus + 24)*q7p^155 + (76*z7plus^2 - 52*z7plus - 228)*q7p^157 + (62*z7plus^2 - 80*z7plus - 186)*q7p^158 + (36*z7plus^2 + 66*z7plus - 66)*q7p^159 + (-82*z7plus^2 - 50*z7plus + 64)*q7p^162 + (-12*z7plus^2 + 6*z7plus - 6)*q7p^163 + (38*z7plus^2 - 54*z7plus - 114)*q7p^165 + (60*z7plus^2 + 26*z7plus - 68)*q7p^167 + (-72*z7plus^2 - 20*z7plus + 104)*q7p^169 + (20*z7plus^2 + 46*z7plus - 46)*q7p^170 + (-24*z7plus^2 + 96*z7plus + 72)*q7p^171 + (-18*z7plus^2 - 12*z7plus + 12)*q7p^173 + (62*z7plus^2 + 18*z7plus - 88)*q7p^174 + (152*z7plus^2 + 64*z7plus - 176)*q7p^176 + (-56*z7plus^2 - 98*z7plus + 98)*q7p^177 + (16*z7plus^2 - 64*z7plus - 48)*q7p^178 + (12*z7plus^2 + 36*z7plus - 36)*q7p^179 + (54*z7plus^2 - 6*z7plus - 120)*q7p^181 + (44*z7plus^2 + 20*z7plus - 48)*q7p^183 + (88*z7plus^2 + 96*z7plus - 96)*q7p^184 + (14*z7plus^2 - 28*z7plus - 42)*q7p^185 + (-24*z7plus^2 + 12*z7plus + 72)*q7p^186 + (-118*z7plus^2 - 200*z7plus + 200)*q7p^187 + (60*z7plus^2 + 12*z7plus - 96)*q7p^190 + (102*z7plus^2 + 138*z7plus - 138)*q7p^191 + (-48*z7plus^2 + 80*z7plus + 144)*q7p^192 + (64*z7plus^2 - 32*z7plus - 192)*q7p^193 + (-60*z7plus^2 - 54*z7plus + 54)*q7p^194 + (26*z7plus^2 + 8*z7plus - 36)*q7p^195 + (62*z7plus^2 + 46*z7plus - 32)*q7p^197 + (88*z7plus^2 + 152*z7plus - 152)*q7p^198 + (22*z7plus^2 - 4*z7plus - 66)*q7p^199+O(q7p^200));

Bexp:=[f0,f1,f2,f3,f4,f5];


//Compute the morphism X-->Z of modular curves,
//where X is a canonical model with variables
//corresponding to the q-expansions in qexps,
//and Z=P^1 with Hauptmodul hauptmodul, and
//d is the degree of X-->Z. 
//Outputs polynomials <num,denom> defining the map.
//This uses code written by Ozman and Siksek.

MapToP1FromqExp:=function(X,qexps,Z,hauptmodul,dd)
u:=hauptmodul;
prec:=Minimum([AbsolutePrecision(f) : f in qexps cat [hauptmodul]]);
K:=BaseRing(Parent(hauptmodul));
XK:=ChangeRing(X,K);
ZK:=ChangeRing(Z,K);
dim:=Dimension(AmbientSpace(X))+1;
R<[x]>:=CoordinateRing(AmbientSpace(XK));
KX:=FunctionField(XK);
KXgens:=[KX!(R.i/R.dim) : i in [1..(dim-1)]] cat [KX!1]; // The functions x_i/x_dim as elements of the function field of X.
//We want to express u as an element of the function field of X
		nds:={};
		d:=0;
		while #nds eq 0 do
			d:=d+1;
			mons:=MonomialsOfDegree(R,d);
			monsq:=[Evaluate(mon,qexps) : mon in mons];
			V:=VectorSpace(K,2*#mons);
			W:=VectorSpace(K,prec-10);
			h:=hom<V->W | 
				[W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]] 
				cat  [ W![Coefficient(-u*monsq[i],j) : j in [1..(prec-10)]  ]  : i in [1..#mons] ]>;
			Kn:=Kernel(h);
			for a in [1..Dimension(Kn)] do
				num:=&+[Eltseq(V!Kn.a)[j]*mons[j] : j in [1..#mons] ];
				denom:=&+[Eltseq(V!Kn.a)[j+#mons]*mons[j] : j in [1..#mons] ];
				numK:=Evaluate(num,KXgens); 
				denomK:=Evaluate(denom,KXgens);
				if numK ne KX!0 and denomK ne KX!0 then
					nds:=nds join {<num,denom>};
				end if;
			end for;
		end while;
		assert #nds eq 1;
RQ<[x]>:=CoordinateRing(AmbientSpace(X));
numQ:=Evaluate(num,x);
denQ:=Evaluate(denom,x);
phi:=map<X->Z | [numQ,denQ]>;
phifun:=FunctionField(X)!(numQ/denQ);
degphi:=&+[-Valuation(phifun,P)*Degree(P) : P in Poles(phifun)];
assert degphi eq dd;
// Now if phifun is not the right function psifun, then the difference phifun-psifun is a rational
// function of degree at most 2*degj (think about the poles).
// Hence to prove that phifun=psifun all we have to check is that their
// q-Expansions agree up to 2*degj+1.
assert prec ge 2*dd+1; //This suffices, but we double-check
assert Valuation(Evaluate(num,qexps)/Evaluate(denom,qexps)-hauptmodul) ge 2*d+1;
return phi;
end function;
        
Xns7:=Curve(ProjectiveSpace(Rationals(),1));
Xb5ns7toXns7:=MapToP1FromqExp(Xb5ns7,Bexp,Xns7,n7,6);
CR<x,y>:=CoordinateRing(AmbientSpace(Xns7));
Fns7:=FunctionField(Xns7);
jns7:=Evaluate(f,Fns7!(x/y))^3/Evaluate(g,Fns7!(x/y))^7;
jX:=Pullback(Xb5ns7toXns7,jns7);
print "We find the following map X(b5,ns7) to X(ns7): ", Xb5ns7toXns7;

//Next, we would like to determine the map Xb5ns7 --> X05. The same procedure as for Xb5ns7 --> Xns7 is too time-expensive. 
X05:=SmallModularCurve(5);
j5:=jFunction(X05,5);

//XtoX05:=MapToP1FromqExp(Xb5ns7,Bexp,X05,f5,21); //Works in theory, not in practice. 
//So we shall resort to a trick. The curve X05 is P1, so the map Xb5ns7 --> X05 corresponds to a function g.

F:=FunctionField(Xb5ns7);
P<g>:=PolynomialRing(F);
//We know that j5(g) = jX. This gives us a degree 6 equation in g, that we need to solve over F.
pfj5:=ProjectiveFunction(j5);
eqn:=Evaluate(Numerator(pfj5),[g,1])-jX*Evaluate(Denominator(pfj5),[g,1]);
rts:=Roots(eqn); //This is it!
assert #rts eq 1;
g:=rts[1][1];
assert Parent(g) eq F; //Indeed in the function field. 
defeqns:=[Numerator(ProjectiveFunction(g)),Denominator(ProjectiveFunction(g))];

//The two equations in defeqns define the map Xb5ns7 --> X05. We make it look a little nicer.
for p in PrimesUpTo(1000) do
    v:=Minimum([Valuation(c,p) : c in Coefficients(defeqns[1]) cat Coefficients(defeqns[2])]);
    defeqns:=[p^(-v)*a : a in defeqns];
end for;
assert GCD([Integers()!c : c in Coefficients(defeqns[1]) cat Coefficients(defeqns[2])]) eq 1;

Xb5ns7toX5:=map<Xb5ns7 -> X05 | defeqns>;
assert Degree(Xb5ns7toX5) eq 21;
assert Evaluate(Numerator(pfj5),[g,1])/Evaluate(Denominator(pfj5),[g,1]) eq jX; 
