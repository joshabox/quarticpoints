//This code computes the map X_2 --> C as well as the vanishing differentials on X_2.
//We then execute the sieves for X_2.

gX:=5;
load "usefulfunctions.m";
load "X1andX2sieve.m";

P4<X0,X1,X2,X3,X4>:=ProjectiveSpace(Rationals(),4);

//We copy-paste the curve from the output of the Sage code for computing X1, X2 and X(b5,ns7)
//constructed in the paper "Computing models for quotients of modular curves".
X:=Curve(P4,[448*X0^2 - 9*X1^2 + 9*X2^2 + 54*X2*X3 + 9*X3^2 + 112*X0*X4 + 126*X1*X4 + 7*X4^2, 16*X0*X1 - 3*X1^2 + 3*X2^2 + 6*X2*X3 + 3*X3^2 + 2*X1*X4 + 21*X4^2, 3*X1*X2 + 28*X0*X3 + 12*X1*X3 + 21*X2*X4 + 14*X3*X4]);

assert Genus(X) eq 5;
w:=iso<X->X | [X0,X1,-X2,-X3,X4],[X0,X1,-X2,-X3,X4]>;
G:=AutomorphismGroup(X,[w]);
CC,pi:=CurveQuotient(G);
C1,m:=SimplifiedModel(CC);
XtoC1:=pi*m;

tf,la:=IsIsomorphic(C,C1);
la:=la*HyperellipticInvolution(C1);
assert tf; //C and C1 are isomorphic.
assert #AutomorphismGroup(C) eq 2; //There are two isomorphisms: la and HyperellipticInvolution(C)*la.

// Since X --> C1 has degree 2,there must be a function t on C1 such that t is not a square in Q(C1)
// but the pullback of t is a square on X. This function t then determines the cover. We compute it.
CRC<x,y,z>:=CoordinateRing(AmbientSpace(C1));
QX:=FunctionField(X);
QC1:=FunctionField(C1);
defs:=DefiningEquations(XtoC1);
f1:=defs[1]; f2:=defs[2]; f3:=defs[3]; //The images of x,y,z. We first simplify these.
f1:=Parent(f1)!((FieldOfFractions(Parent(f1))!f1)/X3^8);
f2:=Parent(f2)!((FieldOfFractions(Parent(f2))!f2)/X3^24);
f3:=Parent(f3)!((FieldOfFractions(Parent(f3))!f3)/X3^8);
for p in PrimesUpTo(100) do
    v:=Floor(Minimum([Rationals()!Valuation(c,p) : c in Coefficients(f1) cat Coefficients(f3)] cat [(Rationals()!Valuation(c,p))/3 : c in Coefficients(f2)]));
    f1,f2,f3:=Explode([p^(-v)*f1,p^(-3*v)*f2,p^(-v)*f3]); 
end for;
XtoC1:=map<X -> C1| [f1,f2,f3]>;

//We see that each term in f2 is either X4^2*f(X2,X3) or just f(X2,X3) for some f,
//and each term in f1 and f3 is a function of X2,X3.
p:=&+[T : T in Terms(f2) | IsDivisibleBy(T,X4^2)];
q:=f2-p;
tf,p:=IsDivisibleBy(p,X4^2); //We get X4^2*p+q = f2.
aa:=4*&*[ff[1]^(ff[2] div 2) : ff in Factorization(p) | IsDivisibleBy(ff[2],2)];
p:=p div aa^2; //We get X4^2 * aa^2 * p+q = f2. Isolating aa doesn't change anything theoretically,
//but it makes Magma process quotients more efficiently.
assert QX!(X2/X3) eq QX!(-f1/f3)-1;
ff3:=f3^3/aa^2;
bbC:=Evaluate(q / (aa^2*p*X3^2),[0,0,QC1!(-x/z)-1,1,0]);
aaC:=Evaluate(ff3/(p*X3^2),[0,0,QC1!(-x/z)-1,1,0]);
t:=aaC*(QC1!(y/z^3))-bbC;
assert Pullback(XtoC1,t) eq QX!(X4^2/X3^2);
assert not IsSquare(t);

//The curves C and C1 are isomorphic and there are two isomorphisms: which one is correct?
cusp0C:=Xb5ns7toC(RepresentativePoint(cusp0));
las:=[ism : ism in [la,la*HyperellipticInvolution(C1)] | IsSquare(Evaluate(t,ism(cusp0C)))];
assert #las eq 1;
la:=las[1];
//We know that cusp0C has degree 3 on X(b5,e7), so t(la(cusp0C)) must be a square. This determines the isomrphism. 

XtoC:=XtoC1*Inverse(la);
t:=Pullback(la,t);
RC<x,y,z>:=CoordinateRing(AmbientSpace(C));

//Let's check that evaluating t allows us to decide which places split in X. 
q:=19;
Xq:=ChangeRing(X,GF(q));
Cq:=ChangeRing(C,GF(q));
Rq<[xq]>:=CoordinateRing(AmbientSpace(Xq));
tq:=reduceFunctionSc(t,C,Cq,ptsC);
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
//Recall that we have imported the cusp forms defining our model for X1
//The ith cusp form corresponds to the variable X(i+1).
V,phi:=SpaceOfDifferentialsFirstKind(X);
//Recall that we 
modforms:=[f/q7p : f in cuspformsX2]; //We divide them all by q to get expansions for the corresponding differentials.

assert &and[QX.1 eq QX!(X0/X3),QX.2 eq QX!(X1/X3),QX.3 eq QX!(X2/X3), QX.4 eq QX!(X4/X3)];
DiffToqExp:=function(omega)
f0:=QX!(X0/X3);
df0:=Differential(f0);
f:=omega/df0;
return L!(Evaluate(Numerator(ProjectiveFunction(f)), modforms)/Evaluate(Denominator(ProjectiveFunction(f)),modforms)*Derivative(modforms[1]/modforms[4]));
end function;

//Next, we want to find the linear combinations of these that make up each of the modular forms
Kn:=VectorSpace(Q7plus,17);
omegas:=[DiffToqExp(phi(V.i)) : i in [1..Dimension(V)]];
vects:=[[Coefficient(omega,i) : i in [0..16]] : omega in omegas];
W:=VectorSpace(Q7plus,#vects);
ii:=Hom(W,Kn)!vects;
assert Dimension(Kernel(ii)) eq 0;
modforms_vects:=[Kn![Coefficient(f,i) : i in [0..16]] : f in modforms];
assert &and[f in Image(ii) : f in modforms_vects];
coeffs:=[f@@ii : f in modforms_vects];
omegafs:=[&+[coeffs[j][i]*phi(V.i) : i in [1..Dimension(V)]] : j in [1..#modforms]];
vandiffs:=[omegafs[i] : i in [2,5]];

//Compute expansions of differentials at the quadratic places. Takes about 1 hour.
exps:=<[ExpandDifferential(om,deg2pb[i],unifsX[i],8) : om in vandiffs] : i in [1..#ptsC]>;
primes:=[43,53,67,83,13,23,71,89,97,181];
divs:=<d1,d2,D7,D3,D4,d21,d22,d2tor>;
assert MWSieve(deg2pb,primes,t,Xs3b5toX05,divs,unifsC,exps,[]);
divs:=<d1,d2,D7,D5,D6,d21,d22,d2tor>;;
assert MWSieve(deg2pb,primes,t,X015toX05,divs,unifsC,exps,[]);




