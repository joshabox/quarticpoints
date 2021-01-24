//This is the Magma code for X(s3,b5,b7)

load "usefulfunctions.m";

//First we check that only quadratic points Q on X_0(5) satisfy j(Q) = j(w5(Q)).
X05:=SmallModularCurve(5);
w5:=AtkinLehnerInvolution(X05,5,5);
j:=jFunction(X05,5);
X1:=Curve(ProjectiveSpace(Rationals(),1));
jmap:=map<X05 ->X1 | [Numerator(ProjectiveFunction(j)), Denominator(ProjectiveFunction(j))]>;
jw5map:=w5*jmap;
jw5fun:=FunctionField(X05)!(DefiningEquations(jw5map)[1]/DefiningEquations(jw5map)[2]);
jdiff:=map<X05->X1 | [Numerator(ProjectiveFunction(j-jw5fun)),Denominator(ProjectiveFunction(j-jw5fun))]>;
ZZ:=Pullback(jdiff,X1![0,1]);
ptsZZ:=Setseq(PointsOverSplittingField(ZZ));
Rng<x,y>:=CoordinateRing(AmbientSpace(X05));
emb:=map<ZZ->X05 | [x,y]>;
for P in ptsZZ do
    assert Degree(ResidueClassField(Place(emb(P)))) eq 2;
end for;


//-------------X_0(35)---------------------------------------------------

X035SMC:=SmallModularCurve(35);
j35SMC:=jFunction(X035SMC,35);
X035,m:=SimplifiedModel(X035SMC);
j35:=Pullback(Inverse(m),j35SMC);
X07:=SmallModularCurve(7);
pr35to7SMC:=ProjectionMap(X035SMC,35,X07,7);
pr35to7:=Inverse(m)*pr35to7SMC;

ptsX035:= [X035![1 , 1 , 0], X035![1 , -1 , 0], X035![0 , -1 , 1], X035![0 , 1 , 1]]; //The cusps of X_0(35).
D1X035:=Place(ptsX035[2])-Place(ptsX035[1]);
D2X035:=3*Place(ptsX035[3])-3*Place(ptsX035[1]); 
infdivX035:=2*Place(ptsX035[1])+2*Place(ptsX035[2]);
deg4X035:=[a*D1X035+b*D2X035+infdivX035 : a in [0..23], b in [0..1]];
pr35to7fun:=DefiningEquations(pr35to7)[1]/DefiningEquations(pr35to7)[2];

//We now verify that D1X035 and D2X035 generate the MW group.
p:=3;
X035p:=ChangeRing(X035,GF(p));
assert IsSingular(X035p) eq false; // Now we know that J_X(Q)-->J_X(\F_p) is injective (rank 0).
D1X035mod3:=Divisor(X035p![1,-1,0])-Divisor(X035p![1,1,0]);
D2X035mod3:=3*Divisor(X035p![0,-1,1])-3*Divisor(X035p![1,1,0]);
JX035F3,phi,psi:=JacobianFp(X035p); // This is isomorphic to J_X(\F_p).
assert IsIsomorphic(JX035F3,AbelianGroup([2,24]));
assert sub<JX035F3 | [psi(D1X035mod3),psi(D2X035mod3)]> eq JX035F3;
assert Order(psi(D1X035mod3)) eq 24;
assert Order(psi(D2X035mod3)) eq 2;

//We check that all found rational points are cusps.
cusps7:=&cat[CuspPlaces(X07,7,d) : d in Divisors(7)];
assert cusps7 eq [Place(X07![0,1]),Place(X07![1,0])];
assert {Place(pr35to7(P)) : P in ptsX035} eq Seqset(cusps7); //So ptsX is the set of cusps on X


//-----------------X(s3,b7)---------------------------------------

prs3b7to7:=MapFromHyperellipticQuotient(63,[9],7); //The map X_0(63)/w_9 --> X_0(7)
Xs3b7:=Domain(prs3b7to7);
prs3b7to7:=map<Xs3b7 -> X07 | DefiningEquations(prs3b7to7)>;  //We set X07 as codomain
ptsXs3b7:=Points(Xs3b7 : Bound:=100);
D1Xs3b7:=-9*(Place(ptsXs3b7[2])-Place(ptsXs3b7[1]))+Place(ptsXs3b7[4])-Place(ptsXs3b7[1]);
D2Xs3b7:=2*(Place(ptsXs3b7[2])-Place(ptsXs3b7[1]))+Place(ptsXs3b7[4])-Place(ptsXs3b7[1]);
infdivXs3b7:=2*Place(ptsXs3b7[1])+2*Place(ptsXs3b7[2]);
deg4Xs3b7:=[a*D1Xs3b7+b*D2Xs3b7+infdivXs3b7 : a in [0..1], b in [0..23]];
prs3b7to7fun:=DefiningEquations(prs3b7to7)[1]/DefiningEquations(prs3b7to7)[2];

//We check that D1Xs3b7 and D2Xs3b7 generate the Mordell--Weil group
p:=5;
Xs3b7p:=ChangeRing(Xs3b7,GF(p));
assert IsSingular(Xs3b7p) eq false; // Now we know that J_X(Q)-->J_X(\F_p) is injective (rank 0).
JXs3b7F5,phi,psi:=JacobianFp(Xs3b7p); // This is isomorphic to J_X(\F_p).
assert IsIsomorphic(JXs3b7F5,AbelianGroup([2,2,2,24]));
D1Xs3b7mod5:=-9*(Divisor(Xs3b7p!Eltseq(ptsXs3b7[2]))-Divisor(Xs3b7p!Eltseq(ptsXs3b7[1])))+Divisor(Xs3b7p!Eltseq(ptsXs3b7[4]))-Divisor(Xs3b7p!Eltseq(ptsXs3b7[1]));
D2Xs3b7mod5:=2*(Divisor(Xs3b7p!Eltseq(ptsXs3b7[2]))-Divisor(Xs3b7p!Eltseq(ptsXs3b7[1])))+Divisor(Xs3b7p!Eltseq(ptsXs3b7[4]))-Divisor(Xs3b7p!Eltseq(ptsXs3b7[1]));
assert IsIsomorphic(sub<JXs3b7F5 | [psi(D1Xs3b7mod5),psi(D2Xs3b7mod5)]>,AbelianGroup([2,24])); //So D1Xs3b7,D2Xs3b7 generate a subgroup isom. to Z/2Z x Z/24Z
assert Order(psi(D1Xs3b7mod5)) eq 2;
assert Order(psi(D2Xs3b7mod5)) eq 24;
p:=11;
Xs3b7p:=ChangeRing(Xs3b7,GF(p));
assert IsSingular(Xs3b7p) eq false; // Now we know that J_X(Q)-->J_X(\F_p) is injective (rank 0).
JXs3b7F11:=JacobianFp(Xs3b7p); // This is isomorphic to J_X(\F_p).
assert IsIsomorphic(JXs3b7F11,AbelianGroup([4,264]));
//JXs3b7F11 and JXs3b7F5 together show that J(Xs3b7)(Q) = Z/2Z D1Xs3b7 x Z/24Z D2Xs3b7 = 

//We check that the found rational points on Xs3b7 indeed are the cusps.
assert {Place(prs3b7to7(P)) : P in ptsXs3b7} eq Seqset(cusps7); //So ptsY is the set of cusps on Y

//We study the automorphism group. We know of two involutions: w_7 and phi_3 (the inv. inducing X(s3,b7) --> X(ns3,b7)). 
assert #AutomorphismGroup(Xs3b7) eq 4;
assert &and[Order(g) in [1,2] : g in AutomorphismGroup(Xs3b7)]; //So AutomorphismGroup(Xs3b7) = Z/2Z x Z/2Z
//So the automorphisms are w_7, phi_3, w_7*phi_3 and Id. We know that X(ns3,b7) has genus 2 by Le Hung. 
assert Genus(ModularCurveQuotient(63,[7,9])) eq 1; //So we must have phi_3*w_7 = hyperelliptic involution


//-------------------Pairs of quartic points with the same image-------------------------

//Input: dec=Decomposition(D), where D is a divisor of degree 4
//f is the function Curve(D) -> P^1 as element in the function field of Curve(D)
//Returns the coefficients of the degree 4 equation defining the divisor f_*D

PushFwdToP1:=function(dec,f)
mp:=&*[MinimalPolynomial(Evaluate(f,dec[i][1]))^(dec[i][2]) : i in [1..#dec]];
//Normally, mp would be the minimal polynomial.
//However, Magma sometimes views the field in which f(dec[i][1]) lies as a tower of two degree 2 extensions. Since the Magma function AbsoluteField() does not work on such fields, we find the minimal polynomial manually.
assert Degree(mp) in [2,4];
if Degree(mp) eq 2 then
    assert &or[Degree(MinimalPolynomial(c)) gt 1 : c in Coefficients(mp)]; //This verifies that the coefficients of mp are not defined over the right field.
    xx:=Evaluate(f,dec[1][1]); //This problem only occurs when #dec = 1, else mp is a product of two deg 2 polynomials and there is no tower.
    assert #dec eq 1; //We doublecheck this.
    a3:=-Trace(Trace(xx));
    a0:=Norm(Norm(xx));
    a2:=Norm(Trace(xx))+Trace(Norm(xx));
    a1:=BaseRing(Curve(dec[1][1]))!(-(xx^4+a3*xx^3+a2*xx^2+a0)/xx);
    cfs:=[a0,a1,a2,a3,1];
else cfs:=Coefficients(mp);
end if;
assert #cfs eq 5;
return cfs;
end function;

//We doublecheck correctness of this function in an example
Q5:=QuadraticField(5);
Pex<x>:=PolynomialRing(Q5);
Q57:=NumberField(x^2-7); //This field is now saved as a degree 2 extension of Q5
A<x>:=AffineSpace(Q57,1);
a:=Q5.1+Q57.1; //rt5 + rt7
assert Degree(MinimalPolynomial(a)) eq 2; 
assert Degree(MinimalPolynomial(AbsoluteField(Q57)!a)) eq 4;
assert Coefficients(MinimalPolynomial(AbsoluteField(Q57)!a)) eq PushFwdToP1(Decomposition(1*Place(A(Q57)![a])),FunctionField(A)!x);


//Input: a degree 4 divisor D1 on a curve X, and a degree 4 divisor D2 on a curve Y
//Only implemented for the case where X,Y are hyperelliptic.
//Also input: maps prX: X --> P^1 and prY: Y --> P^1
//Finds pairs (P,Q) of quartic points on X and Y such that their degree 4 divisors are linearly
//equivalent to D1 and D2 respectively and such that prX(P)=prY(Q), and such that moreover prX(P) has degree 4 (not smaller).

FindLiftsInClass:=function(D1,prX,D2,prY)
X:=Curve(D1);
Y:=Curve(D2);
Z:=Codomain(prX);
assert Z eq Codomain(prY);
F1<x1,y1>:=FunctionField(X);
F2<x2,y2>:=FunctionField(Y);
V1,phi1:=RiemannRochSpace(D1);
V2,phi2:=RiemannRochSpace(D2);
dim1:=Dimension(V1);
dim2:=Dimension(V2);
Pt:=PolynomialRing(Rationals(),dim1);
Ps:=PolynomialRing(Rationals(),dim2);
K<[t]>:=FieldOfFractions(Pt);
L<[s]>:=FieldOfFractions(Ps);
XK:=ChangeRing(X,K);
ZK:=ChangeRing(Z,K);
YL:=ChangeRing(Y,L);
ZL:=ChangeRing(Z,L);
R1<u1,v1,w1>:=CoordinateRing(AmbientSpace(X));
R2<u2,v2,w2>:=CoordinateRing(AmbientSpace(Y));
RK<u1,v1,w1>:=CoordinateRing(AmbientSpace(XK));
RL<u2,v2,w2>:=CoordinateRing(AmbientSpace(YL));
FK1<x1,y1>:=FunctionField(XK);
FL2<x2,y2>:=FunctionField(YL);
defmapK:=[Evaluate(defeqn,[u1,v1,w1]) : defeqn in DefiningEquations(prX)];
prXK:=map<XK->ZK | defmapK>;
prXfunK:=defmapK[1]/defmapK[2];
defmapL:=[Evaluate(defeqn,[u2,v2,w2]) : defeqn in DefiningEquations(prY)];
prYL:=map<YL -> ZL | defmapL>;
prYfunL:=defmapL[1]/defmapL[2];
I1:=Ideal(D1+Divisor(phi1(V1.1))); 
I2:=Ideal(D2+Divisor(phi2(V2.1))); //We translate to an effective divisor so we can use ideals.
ID1:=ideal<RK | [Evaluate(gg,[u1,v1,w1]) : gg in Basis(I1)]>; 
ID2:=ideal<RL | [Evaluate(ff,[u2,v2,w2]) : ff in Basis(I2)]>; //Cheating here
F1A,tr:=AlgorithmicFunctionField(F1);
F1AK,trK:=AlgorithmicFunctionField(FK1);
hh1:=hom<F1A -> F1AK | F1AK.1>; //This is base change to K
f1list:=[phi1(V1.i)/phi1(V1.1) : i in [1..dim1]];
f1Klist:=[Inverse(trK)(hh1(tr(f1))) : f1 in f1list]; //The base changed R--R functions for D1+Divisor(phi1(V1.1))
D1t:=Divisor(XK,ID1)+Divisor(&+([0] cat [t[i]*f1Klist[i] : i in [1..#f1Klist]])); //A generic effective divisor lin. equiv. to D1
decD1t:=Decomposition(D1t);
F2A,tr:=AlgorithmicFunctionField(F2);
F2AL,trL:=AlgorithmicFunctionField(FL2);
hh2:=hom<F2A -> F2AL | F2AL.1>;
f2list:=[phi2(V2.i)/phi2(V2.1) : i in [1..dim2]];
f2Llist:=[Inverse(trL)(hh2(tr(f2))) : f2 in f2list];
D2s:=Divisor(YL,ID2)+Divisor(&+([0] cat [s[i]*f2Llist[i] : i in [1..#f2Llist]]));
decD2s:=Decomposition(D2s);

for i in [1..#decD1t] do
    if prXK(RepresentativePoint(decD1t[i][1])) in [ZK![1,0],ZK![0,1]] then return [],[];
    end if;
end for;
for i in [1..#decD2s] do
    if prYL(RepresentativePoint(decD2s[i][1])) in [ZL![1,0],ZL![0,1]] then return [],[];
    end if;
end for; //If a point has rational image in X_0(7), its j-invariant is rational. Moreover, these are the cusps.

//We compute coefficients of the degree 4 equation satisfied by the pushforwards
cfs1:=PushFwdToP1(decD1t,FK1!prXfunK);
cfs2:=PushFwdToP1(decD2s,FL2!prYfunL);

PxP<[ts]>:=ProductProjectiveSpace(Rationals(),[dim1-1,dim2-1]); //The ambient space of the solution set
CR:=CoordinateRing(PxP);
int:=hom<Pt -> CR | [ts[i] : i in [1..dim1]]>;
ins:=hom<Ps -> CR | [ts[i] : i in [dim1+1..dim1+dim2]]>;
eqns:=[];
denoms:=[]; numscc:=[];

dens:=[int(Denominator(c)) : c in cfs1] cat [ins(Denominator(c)) : c in cfs2]; //Denominators
numscc:=[int(Numerator(cfs1[1])),ins(Numerator(cfs2[1]))];
eqns:=[int(Numerator(cfs1[i]))*ins(Denominator(cfs2[i]))-int(Denominator(cfs1[i]))*ins(Numerator(cfs2[i])) : i in [1..#cfs1]];
//These are the polynomial equations satisfied by t and s. 

sols:=Scheme(PxP,eqns);
pts:=[];
for A in [AffinePatch(sols,i) : i in [1..NumberOfAffinePatches(sols)]] do
        phi:=ProjectiveClosureMap(AmbientSpace(A));
        if Dimension(A) le 0 then
            pts:=pts cat [sols!phi(pt) : pt in RationalPoints(A)];
        else assert Dimension(A) eq 1;
            irs:=IrreducibleComponents(A);
            for ir in irs do
                if Dimension(ir) le 0 then
                    pts:=pts cat [sols!phi(pt) : pt in RationalPoints(ir)];
                else Irad:=Radical(Ideal(phi(ir)));
                    assert &or[den in Irad : den in dens]; //This means that the points corresponding to solutions in ir are quadratic or rational on X_0(7).
                     //Combinations of pts P1 on X and P2 on Y giving vanishing denominators of coefficients of the pushforwards, are always counted as solutions (regardless of whether prX(P1)=prY(P2)), which is why 1-dimensional components occur. We can safely disregard these.
                end if;
            end for;
        end if;
end for;
pointlist1:=[];
pointlist2:=[];

pts:={pt : pt in pts | &and[not Evaluate(denom,Eltseq(pt)) eq 0 : denom in dens]}; //As before, we can safely disregard these points.
//pts:=[pt : pt in pts | &and[not Evaluate(num,Eltseq(pt)) eq 0 : num in numscc]];
//Similarly, we remove the points where the constant coefficient of the minpol vanishes. 
for pt in pts do
    div1:=Divisor(X,I1)+Divisor(&+([0] cat [pt[i]*f1list[i] : i in [1..#f1list]]));
    div2:=Divisor(Y,I2)+Divisor(&+([0] cat [pt[i+dim1]*f2list[i] : i in [1..#f2list]]));
    assert &and[IsEffective(div1),IsEffective(div2)];
    d1:=Decomposition(div1);
    d2:=Decomposition(div2);
    //We translate solutions to divisors on X_0(35) and X(s3,b7), only counting those corresponding to quartic points and where fields of definition match.
    if [#d1,#d2,d1[1][2],d2[1][2]] eq [1,1,1,1] and IsIsomorphic(AbsoluteField(ResidueClassField(d1[1][1])),AbsoluteField(ResidueClassField(d2[1][1]))) then
        Append(~pointlist1,d1[1][1]);
        Append(~pointlist2,d2[1][1]);
    end if;
end for;

return pointlist1,pointlist2; 
//Returns parallel lists such that (pointlist1[i],pointlist2[i]) corresponds to a pair
//degree 4 effective divisors on X and Y mapping to the same divisor on Z.
end function;

//For each combination except (deg4X035[1],deg4Xs3b7[1]) we run FindLiftsInClass to find possible quartic points.
//This takes a while.
foundpts1:=[];
foundpts2:=[];
for i in [1..#deg4X035] do
   for j in [1..#deg4Xs3b7] do
     if not [i,j] eq [1,1] then
        pl1,pl2:=FindLiftsInClass(deg4X035[i],pr35to7,deg4Xs3b7[j],prs3b7to7);
        if not pl1 eq [] then
            foundpts1:=foundpts1 cat pl1;
            foundpts2:=foundpts2 cat pl2;
        end if;
     end if;
   end for;
end for;

//We find two pairs of solutions, but those correspond to quadratic j-invariants.
assert #Set(foundpts1) eq 1 and #Set(foundpts2) eq 2;
P:=foundpts1[1];
jP:=Evaluate(j35,P);
jP:=AbsoluteField(Parent(jP))!jP;
Q5<rt5>:=QuadraticField(5);
a:=282880*rt5 + 632000;
assert Coefficients(MinimalPolynomial(jP)) eq Coefficients(MinimalPolynomial(a));

//This is the same elliptic curve that occurred on X_0(105). Let us investigate a bit more. First we doublecheck.
assert IsSquare(ResidueClassField(P)!(-1)); //So P is defined over Q(rt5, i).
PP<x>:=PolynomialRing(Q5);
L:=AbsoluteField(NumberField(x^2+1)); //This is Q(rt5,i)
X03:=SmallModularCurve(3);
X01:=SmallModularCurve(1);
pr3to1:=ProjectionMap(X03,3,X01,1);
plstoa:=[d[1] : d in Decomposition(Pullback(pr3to1,Place(X01(Q5)![a,1])))];
assert &or[IsIsomorphic(AbsoluteField(ResidueClassField(Q)),L) : Q in plstoa]; //There is indeed a point on X03 defined over L with j-invariant equal to a.

X09:=SmallModularCurve(9);
pr9to1pow3:=ProjectionMap(X09,9,X01,1,3); //The map X_0(9) --> X_0(1) that acts on q-exps as q --> q^3. This factors via X_0(9)/w_9 = X(s3). 
plstoa:=[d[1] : d in Decomposition(Pullback(pr9to1pow3,Place(X01(Q5)![a,1])))];
assert &or[IsIsomorphic(AbsoluteField(ResidueClassField(Q)),L) : Q in plstoa]; //So even on a degree 2 cover of X(s3) there is a point defined over L with j-inv a.

E:=EllipticCurveWithjInvariant(a);
assert Norm(Conductor(E)) eq 2^(12)*5^2*11^4*19^2;

print "Done";





