SetMemoryLimit(256*10^9);

load "X1andX2sieve.m";

//Below we copy-paste the equations for X1, as computed separately in Sage.

P7<X0,X1,X2,X3,X4,X5,X6,X7>:=ProjectiveSpace(Rationals(),7);

X:=Curve(P7,[1276085552*X0^2 + 5633428224*X1*X4 - 1565021952*X2*X4 +
6177490515*X3*X4 - 2527071267*X4^2 + 1787669408*X0*X5 - 4420065792*X1*X5
+ 587896416*X2*X5 - 2211517539*X3*X5 - 169106973*X4*X5 + 2729275472*X5^2
- 70043128*X6^2 - 89714576*X6*X7 - 66413968*X7^2, 61252106496*X0*X1 +
333067766784*X1*X4 - 97947018432*X2*X4 + 374037137775*X3*X4 -
160280194767*X4^2 + 85663001088*X0*X5 - 279075700224*X1*X5 +
37992434976*X2*X5 - 294675800013*X3*X5 + 29993977965*X4*X5 +
142987667760*X5^2 - 3558575592*X6^2 - 4274284432*X6*X7 -
2240637808*X7^2, 1306711605248*X1^2 + 1568832551936*X1*X4 -
484351013376*X2*X4 + 812975384718*X3*X4 - 130514025166*X4^2 -
832229717760*X0*X5 - 90219076608*X1*X5 + 60130271232*X2*X5 -
2330904152745*X3*X5 + 1396850278089*X4*X5 - 76303900512*X5^2 -
26950683712*X6^2 - 47045660192*X6*X7 - 14477899584*X7^2,
45939079872*X0*X2 + 288943927296*X1*X4 - 81070104384*X2*X4 +
74501032662*X3*X4 - 63309191190*X4^2 + 33760090560*X0*X5 -
242235632640*X1*X5 + 56613088512*X2*X5 - 325661245875*X3*X5 +
43975302483*X4*X5 + 62322455328*X5^2 - 2513172832*X6^2 -
2091566304*X6*X7 + 1333524608*X7^2, 1470050555904*X1*X2 +
8881689283584*X1*X4 - 3223765975680*X2*X4 + 9537996009906*X3*X4 -
3639236617842*X4^2 - 415457636160*X0*X5 - 5018318659584*X1*X5 +
896867328384*X2*X5 - 16471498211721*X3*X5 + 7344086945769*X4*X5 +
1674638847840*X5^2 - 108226980864*X6^2 - 207694162016*X6*X7 -
86356022272*X7^2, 413451718848*X2^2 + 13044156881664*X1*X4 -
4489626451680*X2*X4 + 17761275149499*X3*X4 - 7191820383195*X4^2 +
4274332639920*X0*X5 - 10024834548480*X1*X5 + 1820280517632*X2*X5 -
16117953501195*X3*X5 + 5980071151131*X4*X5 + 3104099349120*X5^2 -
162149554904*X6^2 - 323564456032*X6*X7 - 198128455680*X7^2,
275634479232*X0*X3 + 933665252352*X1*X4 - 308990513664*X2*X4 +
831443104674*X3*X4 - 372206552802*X4^2 + 156388802304*X0*X5 -
568304606208*X1*X5 + 90174654720*X2*X5 - 948231577377*X3*X5 +
227051102145*X4*X5 + 412200299616*X5^2 - 9212243968*X6^2 -
14728726560*X6*X7 - 8453520640*X7^2, 34454309904*X1*X3 -
108174659088*X1*X4 + 29998279296*X2*X4 - 109308059280*X3*X4 +
46713587088*X4^2 - 24179352960*X0*X5 + 72737828352*X1*X5 -
10104651648*X2*X5 + 116601096969*X3*X5 - 22281571305*X4*X5 -
43089831456*X5^2 + 1061070912*X6^2 + 1329457120*X6*X7 + 700892864*X7^2,
38761098642*X2*X3 - 306095898624*X1*X4 + 78455890350*X2*X4 -
392573612718*X3*X4 + 162121030638*X4^2 - 75043067904*X0*X5 +
232955433984*X1*X5 - 30752987328*X2*X5 + 388145774205*X3*X5 -
63210623133*X4*X5 - 136156384224*X5^2 + 3679259680*X6^2 +
5050608608*X6*X7 + 2612166144*X7^2, 406991535741*X3^2 +
380574695424*X1*X4 - 108729556992*X2*X4 - 90239244858*X3*X4 -
51511869507*X4^2 + 87793348608*X0*X5 - 219652030464*X1*X5 +
33496031232*X2*X5 - 377172270720*X3*X5 + 63841013376*X4*X5 +
155325090816*X5^2 - 3896345600*X6^2 - 4619560960*X6*X7 -
2490249216*X7^2, 30626053248*X0*X4 + 169738208256*X1*X4 -
52028785152*X2*X4 + 151042133970*X3*X4 - 63958741266*X4^2 +
29047576320*X0*X5 - 103078542336*X1*X5 + 17769685248*X2*X5 -
143106393465*X3*X5 + 24308411673*X4*X5 + 78361865568*X5^2 -
1680150528*X6^2 - 2443948832*X6*X7 - 1380963584*X7^2, 79968*X0*X6 +
34272*X4*X6 - 57120*X5*X6 + 15232*X0*X7 - 19456*X1*X7 + 4224*X2*X7 -
187425*X3*X7 + 191233*X4*X7 + 19040*X5*X7, 1919232*X1*X6 - 993888*X4*X6
+ 2935968*X5*X6 + 437920*X0*X7 + 4897280*X1*X7 + 22656*X2*X7 +
9213813*X3*X7 - 8764469*X4*X7 + 1686944*X5*X7, 359856*X2*X6 +
68544*X4*X6 + 125664*X5*X6 - 795872*X0*X7 + 2559488*X1*X7 - 164256*X2*X7
+ 3456117*X3*X7 - 1955765*X4*X7 - 335104*X5*X7, 67473*X3*X6 -
33201*X4*X6 + 22848*X5*X6 + 15232*X0*X7 - 19456*X1*X7 + 4224*X2*X7 +
82467*X3*X7 - 78659*X4*X7 + 19040*X5*X7]);

assert Genus(X) eq 8;
w:=iso<X->X | [-X0,-X1,-X2,-X3,-X4,-X5,X6,X7],[-X0,-X1,-X2,-X3,-X4,-X5,X6,X7]>;
G:=AutomorphismGroup(X,[w]);
CC,pi:=CurveQuotient(G);
C1,m:=SimplifiedModel(CC);
XtoC1:=pi*m;

tf,la:=IsIsomorphic(C,C1);
assert tf; //C and C1 are isomorphic.
assert #AutomorphismGroup(C) eq 2; //There are two isomorphisms: la and HyperellipticInvolution(C)*la.

// Since X --> C1 has degree 2,there must be a function t on C1 such that t is not a square in Q(C1)
// but the pullback of t is a square on X. This function t then determines the cover.
CRC<x,y,z>:=CoordinateRing(AmbientSpace(C1));
QX:=FunctionField(X);
QC1:=FunctionField(C1);
defs:=DefiningEquations(XtoC1);
f1:=defs[1]; f2:=defs[2]; f3:=defs[3]; //The images of x,y,z
//We see that each term in f2 is either X5^2*f(X6,X7) or just f(X6,X7) for some f
//And, except for the last term, these terms alternate. We make use of this factorisation.
p:=&+[Terms(f2)[i] : i in [1..#Terms(f2) by 2]];
q:=&+[Terms(f2)[i] : i in [2..#Terms(f2) by 2]];
a:=5316515201024/6477979727169868797*X6*X7^89;
p:=p+a;
q:=q-a;
assert p+q eq f2;
fact:=Factorisation(p); //This has a factor X5^2
p:=35/154324115352*fact[3][1]*fact[4][1];
aa:=X5*fact[1][1]^(30)*fact[5][1];
assert aa^2 * p + q eq f2; //Note that the coefficient of p is a square
assert QX!(X6/X7) eq QX!(2/(f1/f3-1));
ff3:=f3^3/(fact[1][1]^(60)*fact[5][1]^2*X6^2);
bbC:=Evaluate(q*ff3/(f3^3*p),[0,0,0,0,0,0,2/(QC1!(x/z)-1),1]); 
aaC:=Evaluate(ff3/p,[0,0,0,0,0,0,2/(QC1!(x/z)-1),1]); 
t:=aaC*(QC1!(y/z^3))-bbC;
assert Pullback(XtoC1,t) eq  QX!(X5^2/X6^2);
assert not IsSquare(t);

//The curves C and C1 are isomorphic and there are two isomorphisms:
Qzet<zet>:=CyclotomicField(7);
L<eta>:=sub<Qzet | 2*(zet^3+zet^-3)+3>;
c0C1:=C1(L)![-1/4*(-eta^2 + 4*eta + 5), -1/2*(-4*eta^2 + 21*eta + 7),1]; //The image of the zero cusp under la.
assert IsSquare(Evaluate(t,c0C1));
assert not IsSquare(Evaluate(t,HyperellipticInvolution(C1)(c0C1)));
c0C:=Xb5ns7toC(invTQ(c0F)); //The image of the zero cusp in C
assert la(c0C) eq c0C1; 
//Since we know that the cusps on X are defined over L, la must be the right isomorphism.

XtoC:=XtoC1*Inverse(la); //Using la, we only work with C and forget about C1.
t:=Pullback(la,t);
RC<x,y,z>:=CoordinateRing(AmbientSpace(C));
t:=t*(FunctionField(C)!(z^2/x^2)); //This slightly simplifies t.

//Let's check that evaluating t allows us to decide which places split in X. 
q:=19;
Xq:=ChangeRing(X,GF(q));
Cq:=ChangeRing(C,GF(q));
Rq<[xq]>:=CoordinateRing(AmbientSpace(Xq));
tq:=reduceFunctionSc(t,C,Cq,Place(ptsC[6]));
XtoCq:=map<Xq->Cq | [Evaluate(eqn,xq) : eqn in DefiningEquations(XtoC)]>;
Aq:=AffinePatch(Cq,1);
pts2:=[Place(Cq(GF(q^2))!(Eltseq(pt) cat [1])) : pt in Points(Aq,GF(q^2))] cat [Place(pt) : pt in PointsAtInfinity(Cq)];
assert &and[IsSquare(EvalNotInf(tq,P)) eq (Degree(Decomposition(Pullback(XtoCq,P))[1][1]) eq Degree(P)) : P in pts2];

//We cannot find any quadratic points on X other than those coming from rational points on C.
//For those we compute uniformisers.
deg2pb:=[Decomposition(Pullback(XtoC,Place(pt)))[1][1] : pt in ptsC];
unifsC:=[UniformizingParameter(Place(pt)) : pt in ptsC];
unifsX:=[Pullback(XtoC,f) : f in unifsC]; //Since none of the points in ptsC ramify, these are uniformisers.

//Computing the space of vanishing differentials on X
V,phi:=SpaceOfDifferentialsFirstKind(X); //The space of all differentials.
Qzeta7<z7>:=CyclotomicField(7);
Qz7plus<z7plus>:=sub<Qzeta7 | [z7+z7^-1]>;
L<q7p>:=PowerSeriesRing(Qz7plus);

//The below modular forms were computed separately in Sage and copy-pasted into this file. The ith modular form corresponds to the ith variable X(i+1) in the coordinate ring of the ambient space of X.
modforms:=[(z7plus^2 - z7plus - 2)*q7p + (-2*z7plus^2 - z7plus + 3)*q7p^2 +
(-z7plus^2 - 2*z7plus + 1)*q7p^4 + (10*z7plus^2 + 5*z7plus - 15)*q7p^5 +
(-3*z7plus^2 + 3*z7plus + 6)*q7p^8 + (6*z7plus^2 + 3*z7plus - 9)*q7p^9 +
(-5*z7plus^2 - 10*z7plus + 5)*q7p^10 + (4*z7plus^2 + 8*z7plus -
4)*q7p^11 + (2*z7plus^2 + z7plus - 3)*q7p^16 + (-3*z7plus^2 - 6*z7plus +
3)*q7p^18 + O(q7p^20), (z7plus^2 + z7plus + 1)*q7p + (-11/8*z7plus +
11/4)*q7p^2 + (-5/8*z7plus^2 + 5/2)*q7p^3 + (-7/4*z7plus^2 + 7)*q7p^4 +
(-z7plus + 2)*q7p^5 + (-z7plus^2 - z7plus - 1)*q7p^6 + (9/4*z7plus^2 -
15/8*z7plus - 35/8)*q7p^7 + (27/8*z7plus^2 + 27/8*z7plus + 27/8)*q7p^8 +
(3/4*z7plus - 3/2)*q7p^9 + (-11/8*z7plus^2 + 11/2)*q7p^10 +
(-5/4*z7plus^2 + 5)*q7p^11 + (21/8*z7plus - 21/4)*q7p^12 +
(-11/4*z7plus^2 - 11/4*z7plus - 11/4)*q7p^13 + (-45/4*z7plus^2 -
57/4*z7plus + 14)*q7p^14 + (5/8*z7plus^2 + 5/8*z7plus + 5/8)*q7p^15 +
(-3*z7plus + 6)*q7p^16 + (-11/4*z7plus^2 + 11)*q7p^17 + (19/4*z7plus^2 -
19)*q7p^18 + (-3/4*z7plus + 3/2)*q7p^19 + O(q7p^20), (z7plus^2 + z7plus
+ 1)*q7p + (-19/3*z7plus + 38/3)*q7p^2 + (13/3*z7plus^2 - 52/3)*q7p^3 +
(-35/3*z7plus^2 + 140/3)*q7p^4 + (-z7plus + 2)*q7p^5 + (-z7plus^2 -
z7plus - 1)*q7p^6 + (32*z7plus^2 + 13*z7plus - 49)*q7p^7 +
(25/3*z7plus^2 + 25/3*z7plus + 25/3)*q7p^8 + (32/3*z7plus - 64/3)*q7p^9
+ (-19/3*z7plus^2 + 76/3)*q7p^10 + (26/3*z7plus^2 - 104/3)*q7p^11 +
(-7/3*z7plus + 14/3)*q7p^12 + (-38/3*z7plus^2 - 38/3*z7plus -
38/3)*q7p^13 + (-41*z7plus^2 - 44*z7plus + 161/3)*q7p^14 +
(-13/3*z7plus^2 - 13/3*z7plus - 13/3)*q7p^15 + (-3*z7plus + 6)*q7p^16 +
(-38/3*z7plus^2 + 152/3)*q7p^17 + (44/3*z7plus^2 - 176/3)*q7p^18 +
(-32/3*z7plus + 64/3)*q7p^19 + O(q7p^20), (z7plus^2 + z7plus - 2)*q7p +
(13/9*z7plus + 13/9)*q7p^2 + (-4/9*z7plus^2 + 4/9)*q7p^3 +
(-31/9*z7plus^2 + 31/9)*q7p^4 + (-z7plus - 1)*q7p^5 + (-4*z7plus^2 -
4*z7plus + 8)*q7p^6 - 4*q7p^7 + (-49/9*z7plus^2 - 49/9*z7plus +
98/9)*q7p^8 + (-5/9*z7plus - 5/9)*q7p^9 + (13/9*z7plus^2 - 13/9)*q7p^10
+ (4/9*z7plus^2 - 4/9)*q7p^11 + (-44/9*z7plus - 44/9)*q7p^12 +
(14/9*z7plus^2 + 14/9*z7plus - 28/9)*q7p^13 + 52/9*q7p^14 +
(4/9*z7plus^2 + 4/9*z7plus - 8/9)*q7p^15 + (-13/3*z7plus - 13/3)*q7p^16
+ (14/9*z7plus^2 - 14/9)*q7p^17 + (-23/9*z7plus^2 + 23/9)*q7p^18 +
(44/9*z7plus + 44/9)*q7p^19 + O(q7p^20), (z7plus^2 + z7plus - 2)*q7p +
(5*z7plus + 5)*q7p^2 + (-4*z7plus^2 + 4)*q7p^3 + (-7*z7plus^2 + 7)*q7p^4
+ (-z7plus - 1)*q7p^5 + (-4*z7plus^2 - 4*z7plus + 8)*q7p^6 - 4*q7p^7 +
(-9*z7plus^2 - 9*z7plus + 18)*q7p^8 + (3*z7plus + 3)*q7p^9 + (5*z7plus^2
- 5)*q7p^10 + (4*z7plus^2 - 4)*q7p^11 + (-12*z7plus - 12)*q7p^12 +
(-2*z7plus^2 - 2*z7plus + 4)*q7p^13 + 20*q7p^14 + (4*z7plus^2 + 4*z7plus
- 8)*q7p^15 + (-15*z7plus - 15)*q7p^16 + (-2*z7plus^2 + 2)*q7p^17 +
(z7plus^2 - 1)*q7p^18 + (12*z7plus + 12)*q7p^19 + O(q7p^20), (z7plus^2 -
z7plus - 2)*q7p + (4*z7plus^2 + 2*z7plus - 6)*q7p^2 + (-3*z7plus^2 -
6*z7plus + 3)*q7p^3 + (2*z7plus^2 + 4*z7plus - 2)*q7p^4 + (-2*z7plus^2 -
z7plus + 3)*q7p^5 + (6*z7plus^2 - 6*z7plus - 12)*q7p^6 + (-12*z7plus^2 -
6*z7plus + 18)*q7p^9 + (-2*z7plus^2 - 4*z7plus + 2)*q7p^10 + (z7plus^2 +
2*z7plus - 1)*q7p^11 + (12*z7plus^2 + 6*z7plus - 18)*q7p^12 +
(-3*z7plus^2 + 3*z7plus + 6)*q7p^13 + (-3*z7plus^2 + 3*z7plus +
6)*q7p^15 + (8*z7plus^2 + 4*z7plus - 12)*q7p^16 + (3*z7plus^2 + 6*z7plus
- 3)*q7p^17 + (-12*z7plus^2 - 24*z7plus + 12)*q7p^18 + (12*z7plus^2 +
6*z7plus - 18)*q7p^19 + O(q7p^20), (18*z7plus^2 + 12*z7plus - 12)*q7p +
(24*z7plus^2 + 30*z7plus - 30)*q7p^2 + (6*z7plus^2 + 18*z7plus -
18)*q7p^3 + (6*z7plus^2 + 18*z7plus - 18)*q7p^5 + (-6*z7plus^2 -
18*z7plus - 24)*q7p^6 + (60*z7plus^2 + 12*z7plus - 96)*q7p^8 +
(48*z7plus^2 + 60*z7plus - 60)*q7p^9 + (-6*z7plus^2 + 24*z7plus +
18)*q7p^10 + (24*z7plus^2 + 30*z7plus - 72)*q7p^11 + (-84*z7plus^2 -
42*z7plus + 84)*q7p^13 + (-12*z7plus^2 + 6*z7plus + 36)*q7p^15 +
(24*z7plus^2 + 72*z7plus - 72)*q7p^16 + (6*z7plus^2 - 66*z7plus -
18)*q7p^17 + (-48*z7plus^2 + 24*z7plus + 144)*q7p^18 + (36*z7plus^2 +
108*z7plus - 108)*q7p^19 + O(q7p^20), (-15*z7plus^2 - 3*z7plus + 24)*q7p
+ (-6*z7plus^2 - 18*z7plus + 18)*q7p^2 + (9*z7plus^2 + 6*z7plus -
27)*q7p^3 + (-12*z7plus^2 - 15*z7plus + 15)*q7p^5 + (12*z7plus^2 -
6*z7plus - 36)*q7p^6 + (-36*z7plus^2 - 24*z7plus + 24)*q7p^8 +
(-12*z7plus^2 - 36*z7plus + 36)*q7p^9 + (12*z7plus^2 - 6*z7plus -
36)*q7p^10 + (15*z7plus^2 + 24*z7plus - 45)*q7p^11 + (63*z7plus^2 +
21*z7plus - 84)*q7p^13 + (3*z7plus^2 + 9*z7plus + 12)*q7p^15 +
(-48*z7plus^2 - 60*z7plus + 60)*q7p^16 + (-33*z7plus^2 + 6*z7plus +
99)*q7p^17 + (12*z7plus^2 - 48*z7plus - 36)*q7p^18 + (-72*z7plus^2 -
90*z7plus + 90)*q7p^19 + O(q7p^20)]; 

modforms:=[f/q7p : f in modforms]; //We divide them all by q to get expansions for the corresponding differentials.
QX:=FunctionField(X);

//This function transforms a differential on X into its corresponding q-expansion.
DiffToqExp:=function(omega)
f0:=QX!(X0/X7);
df0:=Differential(f0);
f:=omega/df0;
return L!(Evaluate(Numerator(ProjectiveFunction(f)), modforms)/Evaluate(Denominator(ProjectiveFunction(f)),modforms)*Derivative(modforms[1]/modforms[8]));
end function;

//Next, we want to find the linear combinations of the differentials on X that make up each of the modular forms
Kn:=VectorSpace(Qz7plus,17); //17 is just the precision
omegas:=[DiffToqExp(phi(V.i)) : i in [1..Dimension(V)]]; //q-exps of a basis of the differentials on X
vects:=[[Coefficient(omega,i) : i in [0..16]] : omega in omegas]; //We store their first 17 coefficients only
W:=VectorSpace(Qz7plus,#vects);
ii:=Hom(W,Kn)!vects; //They give us a linear map W-->Kn by mapping W.i to the expansion of phi(V.i).
assert Dimension(Kernel(ii)) eq 0; //This checks that our precision is high enough: they remain linearly independent.
modforms_vects:=[Kn![Coefficient(f,i) : i in [0..16]] : f in modforms]; 
assert &and[f in Image(ii) : f in modforms_vects]; //Important sanity check: all modular forms are indeed differentials on X.
coeffs:=[f@@ii : f in modforms_vects]; //We pull them back along ii to get the coefficients in terms of omegas.
omegafs:=[&+[coeffs[j][i]*phi(V.i) : i in [1..Dimension(V)]] : j in [1..#modforms]]; //The differentials corresponding to the modular forms
vandiffs:=[omegafs[i] : i in [2,3,4,5]]; //These are the differentials corresponding to rank 0 quotients: the vanishing diffs.

//We compute expansions of differentials at the quadratic places up to 14=2g-2. Takes about 1 hour.
exps:=<[ExpandDifferential(om,deg2pb[i],unifsX[i],14) : om in vandiffs] : i in [1..#ptsC]>;
primes:=[43,53,67,83,13,23,71,89,97,181];
divs:=<d1,d2,D7,D3,D4>;
MWSieve(deg2pb,primes,t,prE5,divs,unifsC,exps);
divs:=<d1,d2,D7,D5,D6>;
MWSieve(deg2pb,primes,t,pr155,divs,unifsC,exps);








