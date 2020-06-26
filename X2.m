SetMemoryLimit(256*10^9);

load "X1andX2sieve.m";

P4<X0,X1,X2,X3,X4>:=ProjectiveSpace(Rationals(),4);

X:=Curve(P4,[2205*X0^2 - 329*X1^2 - 5*X2^2 - 18*X2*X3 - 20*X3^2 + 1764*X0*X4 +
28*X1*X4 + 112*X4^2, 105*X0*X1 + 7*X1^2 - X2*X3 - 42*X0*X4 - 14*X1*X4 -
56*X4^2, 6*X0*X2 - X1*X2 + 3*X0*X3 - 3*X1*X3 - 2*X2*X4]);

assert Genus(X) eq 5;
w:=iso<X->X | [-X0,-X1,X2,X3,-X4],[-X0,-X1,X2,X3,-X4]>;
G:=AutomorphismGroup(X,[w]);
CC,pi:=CurveQuotient(G);
C1,m:=SimplifiedModel(CC);
XtoC1:=pi*m;

tf,la:=IsIsomorphic(C,C1);
la:=la*HyperellipticInvolution(C1);
assert tf; //C and C1 are isomorphic.
assert #AutomorphismGroup(C) eq 2; //There are two isomorphisms: la and HyperellipticInvolution(C)*la.

// Since X --> C1 has degree 2,there must be a function t on C1 such that t is not a square in Q(C1)
// but the pullback of t is a square on X. This function t then determines the cover.
CRC<x,y,z>:=CoordinateRing(AmbientSpace(C1));
QX:=FunctionField(X);
QC:=FunctionField(C1);
//We will find ff in QC such that ff is a square in QX but not in QC
defs:=DefiningEquations(XtoC1);
f1:=defs[1]; f2:=defs[2]; f3:=defs[3]; //The images of x,y,z
q:=&+[Terms(f2)[i] : i in [1..13]];
p:=&+[Terms(f2)[i] : i in [14..#Terms(f2)]];
assert p+q eq f2;
fact:=Factorisation(p);
p:=7/2544768*fact[5][1];
aa:=X4*fact[2][1]^(12)*fact[3][1]*fact[4][1];
assert aa^2 * p + q eq f2; //Note that the coefficient of p is a square
assert QX!(X2/X3) eq QX!(2/(f1/f3-1));
ff3:=f3^3/(fact[2][1]^(24)*fact[3][1]^2*fact[4][1]^2*X2^2);
bbC:=Evaluate(q*ff3/(f3^3*p),[0,0,2/(QC!(x/z)-1),1,0]); 
aaC:=Evaluate(ff3/p,[0,0,2/(QC!(x/z)-1),1,0]); 
t:=aaC*(QC!(y/z^3))-bbC;
assert Pullback(XtoC1,t) eq  QX!(X4^2/X2^2);
assert not IsSquare(t);
t:=4*9*t;

//The curves C and C1 are isomorphic and there are two isomorphisms:
Qzet<zet>:=CyclotomicField(7);
L<eta>:=sub<Qzet | 2*(zet^3+zet^-3)+3>;
c0C1:=HyperellipticInvolution(C1)(C1(L)![-1/4*(-eta^2 + 4*eta + 5), -1/2*(-4*eta^2 + 21*eta + 7),1]);
assert IsSquare(Evaluate(t,c0C1));
assert not IsSquare(Evaluate(t,HyperellipticInvolution(C1)(c0C1)));
c0C:=Xb5ns7toC(invTQ(c0F)); //The image of the zero cusp on C.
assert la(c0C) eq c0C1;
//Since we know that the cusps on X are defined over L, la must be the right isomorphism.


XtoC:=XtoC1*Inverse(la);
t:=Pullback(la,t);
RC<x,y,z>:=CoordinateRing(AmbientSpace(C));
t:=t*(FunctionField(C)!(z^2/x^2));

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


//The below modular forms were computed separately in Sage and copy-pasted into this file. The ith modular form corresponds to the ith variable X(i+1) in the coordinate ring of the ambient space of X.

V,phi:=SpaceOfDifferentialsFirstKind(X);
Qzeta7<z7>:=CyclotomicField(7);
Qz7plus<z7plus>:=sub<Qzeta7 | [z7+z7^-1]>;
L<q7p>:=PowerSeriesRing(Qz7plus);
modforms:=[(z7plus^2 + z7plus - 2)*q7p + (-z7plus^2 + 1)*q7p^3 + (2*z7plus^2 -
2)*q7p^4 + (z7plus + 1)*q7p^5 + 4*q7p^7 + (2*z7plus + 2)*q7p^9 +
(3*z7plus^2 - 3)*q7p^11 + (2*z7plus + 2)*q7p^12 + (5*z7plus^2 + 5*z7plus
- 10)*q7p^13 + (-z7plus^2 - z7plus + 2)*q7p^15 + (-4*z7plus - 4)*q7p^16
+ (-3*z7plus^2 + 3)*q7p^17 + (-2*z7plus - 2)*q7p^19 + O(q7p^20),
(-z7plus^2 + z7plus + 2)*q7p + (-4*z7plus^2 - 2*z7plus + 6)*q7p^2 +
(-3*z7plus^2 - 6*z7plus + 3)*q7p^3 + (-2*z7plus^2 - 4*z7plus + 2)*q7p^4
+ (-2*z7plus^2 - z7plus + 3)*q7p^5 + (6*z7plus^2 - 6*z7plus - 12)*q7p^6
+ (12*z7plus^2 + 6*z7plus - 18)*q7p^9 + (-2*z7plus^2 - 4*z7plus +
2)*q7p^10 + (-z7plus^2 - 2*z7plus + 1)*q7p^11 + (12*z7plus^2 + 6*z7plus
- 18)*q7p^12 + (-3*z7plus^2 + 3*z7plus + 6)*q7p^13 + (3*z7plus^2 -
3*z7plus - 6)*q7p^15 + (-8*z7plus^2 - 4*z7plus + 12)*q7p^16 +
(3*z7plus^2 + 6*z7plus - 3)*q7p^17 + (12*z7plus^2 + 24*z7plus -
12)*q7p^18 + (12*z7plus^2 + 6*z7plus - 18)*q7p^19 + O(q7p^20),
(18*z7plus^2 + 12*z7plus - 12)*q7p + (24*z7plus^2 + 30*z7plus -
30)*q7p^2 + (6*z7plus^2 + 18*z7plus - 18)*q7p^3 + (6*z7plus^2 +
18*z7plus - 18)*q7p^5 + (-6*z7plus^2 - 18*z7plus - 24)*q7p^6 +
(60*z7plus^2 + 12*z7plus - 96)*q7p^8 + (48*z7plus^2 + 60*z7plus -
60)*q7p^9 + (-6*z7plus^2 + 24*z7plus + 18)*q7p^10 + (24*z7plus^2 +
30*z7plus - 72)*q7p^11 + (-84*z7plus^2 - 42*z7plus + 84)*q7p^13 +
(-12*z7plus^2 + 6*z7plus + 36)*q7p^15 + (24*z7plus^2 + 72*z7plus -
72)*q7p^16 + (6*z7plus^2 - 66*z7plus - 18)*q7p^17 + (-48*z7plus^2 +
24*z7plus + 144)*q7p^18 + (36*z7plus^2 + 108*z7plus - 108)*q7p^19 +
O(q7p^20), (-15*z7plus^2 - 3*z7plus + 24)*q7p + (-6*z7plus^2 - 18*z7plus
+ 18)*q7p^2 + (9*z7plus^2 + 6*z7plus - 27)*q7p^3 + (-12*z7plus^2 -
15*z7plus + 15)*q7p^5 + (12*z7plus^2 - 6*z7plus - 36)*q7p^6 +
(-36*z7plus^2 - 24*z7plus + 24)*q7p^8 + (-12*z7plus^2 - 36*z7plus +
36)*q7p^9 + (12*z7plus^2 - 6*z7plus - 36)*q7p^10 + (15*z7plus^2 +
24*z7plus - 45)*q7p^11 + (63*z7plus^2 + 21*z7plus - 84)*q7p^13 +
(3*z7plus^2 + 9*z7plus + 12)*q7p^15 + (-48*z7plus^2 - 60*z7plus +
60)*q7p^16 + (-33*z7plus^2 + 6*z7plus + 99)*q7p^17 + (12*z7plus^2 -
48*z7plus - 36)*q7p^18 + (-72*z7plus^2 - 90*z7plus + 90)*q7p^19 +
O(q7p^20), (-z7plus^2 + z7plus + 2)*q7p + (2*z7plus^2 + z7plus -
3)*q7p^2 + (z7plus^2 + 2*z7plus - 1)*q7p^4 + (10*z7plus^2 + 5*z7plus -
15)*q7p^5 + (3*z7plus^2 - 3*z7plus - 6)*q7p^8 + (-6*z7plus^2 - 3*z7plus
+ 9)*q7p^9 + (-5*z7plus^2 - 10*z7plus + 5)*q7p^10 + (-4*z7plus^2 -
8*z7plus + 4)*q7p^11 + (-2*z7plus^2 - z7plus + 3)*q7p^16 + (3*z7plus^2 +
6*z7plus - 3)*q7p^18 + O(q7p^20)]; //Create the modular forms as power series and divide them all by q
modforms:=[f/q7p : f in modforms];
QX:=FunctionField(X);

assert &and[QX.1 eq QX!(X0/X3),QX.2 eq QX!(X1/X3),QX.3 eq QX!(X2/X3), QX.4 eq QX!(X4/X3)];
DiffToqExp:=function(omega)
f0:=QX!(X0/X3);
df0:=Differential(f0);
f:=omega/df0;
return L!(Evaluate(Numerator(ProjectiveFunction(f)), modforms)/Evaluate(Denominator(ProjectiveFunction(f)),modforms)*Derivative(modforms[1]/modforms[4]));
end function;

//Next, we want to find the linear combinations of these that make up each of the modular forms
Kn:=VectorSpace(Qz7plus,17);
omegas:=[DiffToqExp(phi(V.i)) : i in [1..Dimension(V)]];
vects:=[[Coefficient(omega,i) : i in [0..16]] : omega in omegas];
W:=VectorSpace(Qz7plus,#vects);
ii:=Hom(W,Kn)!vects;
assert Dimension(Kernel(ii)) eq 0;
modforms_vects:=[Kn![Coefficient(f,i) : i in [0..16]] : f in modforms];
assert &and[f in Image(ii) : f in modforms_vects];
coeffs:=[f@@ii : f in modforms_vects];
omegafs:=[&+[coeffs[j][i]*phi(V.i) : i in [1..Dimension(V)]] : j in [1..#modforms]];
vandiffs:=[omegafs[i] : i in [1,2]];

//Compute expansions of differentials at the quadratic places. Takes about 1 hour.
exps:=<[ExpandDifferential(om,deg2pb[i],unifsX[i],8) : om in vandiffs] : i in [1..#ptsC]>;
primes:=[43,53,67,83,13,23,71,89,97,181];
divs:=<d1,d2,D7,D3,D4>;
MWSieve(deg2pb,primes,t,prE5,divs,unifsC,exps);
divs:=<d1,d2,D7,D5,D6>;
MWSieve(deg2pb,primes,t,pr155,divs,unifsC,exps);











