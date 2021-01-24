//In this file, we compute the map X_1 --> C as well as the vanishing differentials on X_1.
//We then run the sieve.

gX:=8;
load "usefulfunctions.m";
load "X1andX2sieve.m";

//We copy-paste the curve from the output of the Sage code for computing X1, X2 and X(b5,ns7)
//constructed in the paper "Computing models for quotients of modular curves".

P7<X0,X1,X2,X3,X6,X7,X4,X5>:=ProjectiveSpace(Rationals(),7);
//This strange ordering of variables somehow massively speeds up certain computations. 
//E.g. Computing the simplified version of XtoC1 on line 43 goes from not terminating to instantaneous.

X:=Curve(P7,[3528*X0^2 + 177*X4*X5 + 597*X5^2 - 2716*X0*X6 - 423*X1*X6 - 6365*X2*X6 - 1918*X3*X6 - 13454*X6^2 + 2842*X0*X7 + 626*X1*X7 + 9144*X2*X7 + 3010*X3*X7 + 35252*X6*X7 - 22960*X7^2, 56*X0*X1 - 135*X4*X5 - 327*X5^2 - 140*X0*X6 - 37*X1*X6 + 2381*X2*X6 + 1890*X3*X6 + 2982*X6^2 + 910*X0*X7 + 16*X1*X7 - 3270*X2*X7 - 2758*X3*X7 - 7476*X6*X7 + 4816*X7^2, 56*X1^2 + 1215*X4*X5 + 2835*X5^2 + 11340*X0*X6 - 715*X1*X6 - 22389*X2*X6 - 12726*X3*X6 - 38290*X6^2 - 19530*X0*X7 + 820*X1*X7 + 30894*X2*X7 + 21546*X3*X7 + 99764*X6*X7 - 64624*X7^2, 168*X0*X2 - 15*X4*X5 - 3*X5^2 - 56*X0*X6 - 45*X1*X6 + 89*X2*X6 + 238*X3*X6 - 238*X6^2 + 182*X0*X7 + 52*X1*X7 - 138*X2*X7 - 406*X3*X7 + 532*X6*X7 - 224*X7^2, 56*X1*X2 - 171*X4*X5 - 315*X5^2 + 168*X0*X6 - 253*X1*X6 + 2713*X2*X6 + 2562*X3*X6 + 2086*X6^2 + 1050*X0*X7 + 260*X1*X7 - 3910*X2*X7 - 3738*X3*X7 - 5292*X6*X7 + 3584*X7^2, 56*X2^2 + 87*X4*X5 + 147*X5^2 - 364*X0*X6 + 141*X1*X6 - 1285*X2*X6 - 1582*X3*X6 - 714*X6^2 - 266*X0*X7 - 148*X1*X7 + 1894*X2*X7 + 2170*X3*X7 + 1764*X6*X7 - 1232*X7^2, 1764*X0*X3 - 579*X4*X5 - 1050*X5^2 + 1505*X0*X6 - 774*X1*X6 + 7009*X2*X6 + 6083*X3*X6 + 7021*X6^2 + 1456*X0*X7 + 851*X1*X7 - 9837*X2*X7 - 8582*X3*X7 - 15778*X6*X7 + 9044*X7^2, 28*X1*X3 + 9*X4*X5 + 6*X5^2 + 357*X0*X6 - X1*X6 + 74*X2*X6 + 161*X3*X6 - 63*X6^2 - 364*X0*X7 - 20*X1*X7 - 144*X2*X7 - 168*X3*X7 + 210*X6*X7 - 140*X7^2, 84*X2*X3 - 15*X4*X5 - 30*X5^2 - 35*X0*X6 - 27*X1*X6 + 80*X2*X6 + 133*X3*X6 + 329*X6^2 + 140*X0*X7 + 34*X1*X7 - 66*X2*X7 - 196*X3*X7 - 854*X6*X7 + 532*X7^2, 252*X3^2 + 12*X4*X5 - 30*X5^2 + 70*X0*X6 + 45*X1*X6 + 443*X2*X6 + 28*X3*X6 + 350*X6^2 - 196*X0*X7 - 59*X1*X7 - 639*X2*X7 + 14*X3*X7 - 728*X6*X7 + 280*X7^2, 18*X0*X4 - 19*X0*X5 - 12*X1*X5 - 27*X2*X5 + 17*X3*X5 - 120*X4*X6 - 66*X5*X6 + 114*X4*X7 + 54*X5*X7, 2*X1*X4 - 21*X0*X5 + 8*X1*X5 + 7*X2*X5 - 21*X3*X5 + 28*X4*X6 + 56*X5*X6 - 28*X4*X7 - 84*X5*X7, 6*X2*X4 + 7*X0*X5 + 3*X2*X5 + 7*X3*X5, 9*X3*X4 - 28*X0*X5 - 3*X1*X5 - 9*X2*X5 + 8*X3*X5 - 39*X4*X6 - 30*X5*X6 + 33*X4*X7 + 27*X5*X7, 63*X4^2 + 426*X4*X5 + 690*X5^2 + 1120*X0*X6 + 207*X1*X6 - 4405*X2*X6 - 2702*X3*X6 - 7000*X6^2 - 2464*X0*X7 - 263*X1*X7 + 6057*X2*X7 + 4298*X3*X7 + 18172*X6*X7 - 11984*X7^2]);
assert Genus(X) eq 8;

w:=iso<X->X | [X0,X1,X2,X3,X6,X7,-X4,-X5],[X0,X1,X2,X3,X6,X7,-X4,-X5]>;
G:=AutomorphismGroup(X,[w]);
CC,pi:=CurveQuotient(G);
C1,m:=SimplifiedModel(CC);
XtoC1:=pi*m;

//Recall that C = X(b5,ns7)/w_5
tf,la:=IsIsomorphic(C,C1);
assert tf; //C and C1 are isomorphic, as expected.
assert #AutomorphismGroup(C) eq 2; //There are two isomorphisms: la and HyperellipticInvolution(C)*la.

// Since X --> C1 has degree 2,there must be a function t on C1 such that t is not a square in Q(C1)
// but the pullback of t is a square on X. This function t then determines the cover.
CRC<x,y,z>:=CoordinateRing(AmbientSpace(C1));
QX:=FunctionField(X);
QC1:=FunctionField(C1);
defs:=DefiningEquations(XtoC1);
f1:=defs[1]; f2:=defs[2]; f3:=defs[3]; //The images of x,y,z. We first simplify these.
f1:=Parent(f1)!((FieldOfFractions(Parent(f1))!f1)/X5^20);
f2:=Parent(f2)!((FieldOfFractions(Parent(f2))!f2)/X5^60);
f3:=Parent(f3)!((FieldOfFractions(Parent(f3))!f3)/X5^20);
for p in PrimesUpTo(100) do
    v:=Floor(Minimum([Rationals()!Valuation(c,p) : c in Coefficients(f1) cat Coefficients(f3)] cat [(Rationals()!Valuation(c,p))/3 : c in Coefficients(f2)]));
    f1,f2,f3:=Explode([p^(-v)*f1,p^(-3*v)*f2,p^(-v)*f3]); 
end for;
XtoC1:=map<X -> C1| [f1,f2,f3]>;

//We see that each term in f2 is either X7^2*f(X4,X5) or just f(X4,X5) for some f,
//and each term in f1 and f3 is a function of X4,X5.
p:=&+[T : T in Terms(f2) | IsDivisibleBy(T,X7^2)];
q:=f2-p;
tf,p:=IsDivisibleBy(p,X7^2); //We get X7^2*p+q = f2.
aa:=2*&*[ff[1]^(ff[2] div 2) : ff in Factorization(p) | IsDivisibleBy(ff[2],2)];
p:=p div aa^2; //We get X7^2 * aa^2 * p+q = f2. Isolating aa doesn't change anything theoretically,
//but it makes Magma process quotients more efficiently.
assert QX!(X4/X5) eq QX!(-f1/f3)-1;
ff3:=f3^3/aa^2;
bbC:=Evaluate(q / (aa^2*p*X5^2),[0,0,0,0,0,0,QC1!(-x/z)-1,1]);
aaC:=Evaluate(ff3/(p*X5^2),[0,0,0,0,0,0,QC1!(-x/z)-1,1]);
t:=aaC*(QC1!(y/z^3))-bbC;
assert Pullback(XtoC1,t) eq QX!(X7^2/X5^2);
assert not IsSquare(t);

//The curves C and C1 are isomorphic and there are two isomorphisms: which one is correct?
cusp0C:=Xb5ns7toC(RepresentativePoint(cusp0));
las:=[ism : ism in [la,la*HyperellipticInvolution(C1)] | IsSquare(Evaluate(t,ism(cusp0C)))];
assert #las eq 1;
la:=las[1];
//We know that cusp0C has degree 3 on X(b5,e7), so t(la(cusp0C)) must be a square. This determines the isomrphism. 

XtoC:=XtoC1*Inverse(la); //Using la, we only work with C and forget about C1.
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

//Computing the space of vanishing differentials on X
V,phi:=SpaceOfDifferentialsFirstKind(X); //The space of all differentials.
//Recall that we have imported the cusp forms defining our model for X1
//The ith cusp form corresponds to the variable X(i+1).
//We reorder the cusp forms according to our reordering of the variables X0,...X7.
modforms:=cuspformsX1;
modforms:=[modforms[1],modforms[2],modforms[3],modforms[4],modforms[7],modforms[8],modforms[5],modforms[6]];
modforms:=[f/q7p : f in modforms]; //We divide them all by q to get expansions for the corresponding differentials.

//This function transforms a differential on X into its corresponding q-expansion.
DiffToqExp:=function(omega)
f0:=QX!(X0/X7);
df0:=Differential(f0);
f:=omega/df0;
return L!(Evaluate(Numerator(ProjectiveFunction(f)), modforms)/Evaluate(Denominator(ProjectiveFunction(f)),modforms)*Derivative(modforms[1]/modforms[6]));
end function;

//Next, we want to find the linear combinations of the differentials on X that make up each of the modular forms
Kn:=VectorSpace(Q7plus,17); //17 is just the precision
omegas:=[DiffToqExp(phi(V.i)) : i in [1..Dimension(V)]]; //q-exps of a basis of the differentials on X
vects:=[[Coefficient(omega,i) : i in [0..16]] : omega in omegas]; //We store their first 17 coefficients only
W:=VectorSpace(Q7plus,#vects);
ii:=Hom(W,Kn)!vects; //They give us a linear map W-->Kn by mapping W.i to the expansion of phi(V.i).
assert Dimension(Kernel(ii)) eq 0; //This checks that our precision is high enough: they remain linearly independent.
modforms_vects:=[Kn![Coefficient(f,i) : i in [0..16]] : f in modforms]; 
assert &and[f in Image(ii) : f in modforms_vects]; //Important sanity check: all modular forms are indeed differentials on X.
coeffs:=[f@@ii : f in modforms_vects]; //We pull them back along ii to get the coefficients in terms of omegas.
omegafs:=[&+[coeffs[j][i]*phi(V.i) : i in [1..Dimension(V)]] : j in [1..#modforms]]; //The differentials corresponding to the modular forms
vandiffs:=[omegafs[i] : i in [2,3,5,6]]; //These are the differentials corresponding to rank 0 quotients: the vanishing diffs.

//We compute expansions of differentials at the quadratic places up to 14=2g-2. Takes about 1 hour.
exps:=<[ExpandDifferential(om,deg2pb[i],unifsX[i],14) : om in vandiffs] : i in [1..#ptsC]>;

primes:=[13,23,43,53,67,83,71,89,97,79,181];
divs:=<d1,d2,D7,D3,D4,d21,d22,d2tor>; //While we input d21,d22,d2tor, these are not used when *=s.
assert MWSieve(deg2pb,primes,t,Xs3b5toX05,divs,unifsC,exps,[]);
divs:=<d1,d2,D7,D5,D6,d21,d22,d2tor>;
torsubpos:=[[a,b,c,d] : a in [0,1], b in [0,1], c in [0..3], d in [0,1]]; 
//torsubpos are the possible coefficients for D7,D3,D4,d2tor in the MW groups.
//Separating these possibilities speeds up the sieve.
assert &and[MWSieve(deg2pb,primes,t,X015toX05,divs,unifsC,exps,T) : T in torsubpos];











