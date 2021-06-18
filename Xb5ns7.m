//This is part of the accompanying Magma file of the paper ``Computing models for quotients of modular curves''
//At the end of the file, we have added to this the computation of the map X(b5,ns7) --> X_0(5).


//------------------------Magma file from other paper------------------------------------------

/* In this Magma file, we first verify that our model for X(b5,ns7) 
is isomorphic to the Derickx--Najman--Siksek model.
We then compute the map X(b5,ns7) --> X(ns7) explicitly. */

//We copy-paste the equations for X(b5,ns7) from the output of the Sage file.
P<X0,X1,X2,X3,X4,X5>:=ProjectiveSpace(Rationals(),5);
Xb5ns7:=Curve(P,[14*X0^2 + 12*X2*X3 - 16*X3^2 - 14*X2*X4 + 30*X3*X4 - 11*X4^2 + 28*X2*X5 - 58*X3*X5 + 40*X4*X5 - 28*X5^2, 7*X0*X1 - 2*X2*X4 - 4*X3*X4 + 2*X4^2 + 12*X3*X5 - 7*X4*X5 + 10*X5^2, 14*X1^2 - 4*X2*X3 + 16*X3^2 + 10*X2*X4 + 14*X3*X4 - 21*X4^2 + 4*X2*X5 - 58*X3*X5 + 64*X4*X5 - 66*X5^2, 2*X0*X2 - 2*X0*X3 + 2*X1*X3 - 5*X0*X4 - 6*X1*X4 + 8*X0*X5 + 4*X1*X5, 4*X1*X2 - 2*X0*X3 - 6*X1*X3 - X0*X4 + 3*X1*X4 + 3*X0*X5 - 2*X1*X5, 8*X2^2 - 20*X2*X3 + 16*X3^2 - 14*X2*X4 + 14*X3*X4 - 21*X4^2 + 28*X2*X5 - 42*X3*X5 + 56*X4*X5 - 28*X5^2]);

print "The found canonical model for X(b5,ns7) is ", Xb5ns7;
w5:=iso<Xb5ns7 -> Xb5ns7 | [-X0,-X1,X2,X3,X4,X5],[-X0,-X1,X2,X3,X4,X5]>;
CC,pi:=CurveQuotient(AutomorphismGroup(Xb5ns7,[w5]));
C,s:=SimplifiedModel(CC);
Xb5ns7toC:=pi*s;
ptsC:=Points(C: Bound:=500);

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
F<t>:=FieldOfFractions(PP);
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

//We import the cusp forms used to define our canonical model for X(b5,ns7).
load "cuspforms.m";
tf,phi:=IsIsomorphic(Q7plus,K);
assert MinimalPolynomial(phi(Q7plus.1)) eq MinimalPolynomial(a^2-2);
Embed(Q7plus,K,a^2-2);
Bexp:=[LL!f : f in cuspformsXb5ns7];
Xns7:=Curve(ProjectiveSpace(Rationals(),1));
Xb5ns7toXns7:=MapToP1FromqExp(Xb5ns7,Bexp,Xns7,n7,6);
CR<x,y>:=CoordinateRing(AmbientSpace(Xns7));
Fns7:=FunctionField(Xns7);
jns7:=Evaluate(f,Fns7!(x/y))^3/Evaluate(g,Fns7!(x/y))^7;
jX:=Pullback(Xb5ns7toXns7,jns7);
print "We find the following map X(b5,ns7) to X(ns7): ", Xb5ns7toXns7;

//We use the j-map to find the cusps
cuspdivXns7:=Poles(jns7)[1];
cuspdivXb5ns7:=Pullback(Xb5ns7toXns7,cuspdivXns7);
cusp0:=Decomposition(cuspdivXb5ns7)[1][1];
cuspinf:=Decomposition(cuspdivXb5ns7)[2][1];
assert Pullback(w5,1*cusp0) eq 1*cuspinf;

//-----------------Map to X05-------------------------------------------

//Next, we would like to determine the map Xb5ns7 --> X05. 
//The same procedure as for Xb5ns7 --> Xns7 is too time-expensive. 
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

Xb5ns7toX05:=map<Xb5ns7 -> X05 | defeqns>;
assert Degree(Xb5ns7toX05) eq 21;
assert Evaluate(Numerator(pfj5),[g,1])/Evaluate(Denominator(pfj5),[g,1]) eq jX;
prX05fn:=g;


