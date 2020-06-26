//The sieve for quadratic points on X1 and X2. Let Y be one of X_0(15) and X(s3,b5). The purpose of the sieve is to show that there are no quadratic points on X giving rise to quartic points on both Y and X(e7), except possibly for the 6 pairs of quadratic points mapping to rational points on C.

load "ozmansiksek2.m";
load "DNS.m";
w5:=iso<Xb5ns7->Xb5ns7 | [-u,-v,w],[-u,-v,w]>;

//We first compute X(e7), X_0(15) and X(s3,b5).
R<xe7>:=PolynomialRing(Rationals());
Xe7:=HyperellipticCurve(7*(16*xe7^4 + 68*xe7^3 + 111*xe7^2 + 62*xe7 + 11)); //This is an elliptic curve with M-W group Z/2Z
R<xe7,ye7,ze7>:=CoordinateRing(AmbientSpace(Xe7));
ptse7:=Setseq(Points(Xe7 : Bound:=200)); //Two rational points
Ee7,me7:=EllipticCurve(Xe7,ptse7[2]);
D7:=Divisor(ptse7[1])-Divisor(ptse7[2]); //The generator of the M-W group (checked below).
bpe7:=Divisor(ptse7[2]);
MWEe7,embe7,tf1,tf2:=MordellWeilGroup(Ee7);
assert &and[tf1,tf2, #MordellWeilGroup(Ee7) eq 2];
assert Pullback(me7,Place(embe7(MWEe7.1))-Place(Zero(Ee7))) eq D7;
//The map to Xns7+ is (x,y) :--> x.
Xns7<xns7,yns7>:=Curve(ProjectiveSpace(Rationals(),1));
pre7ns7:=map<Xe7 -> Xns7 | [xe7,ze7]>;

//There is a subtle problem that needs to solved: Le Hung's fibred product model for XlH comes with projection maps (x1:x2, y1:y2) :--> (x1:x2) and (x1:x2, y1:y2) :--> (y1:y2) onto X_0(5) and X(ns7) respectively. This is based on j-invariant maps to X(1) for X_0(5) and X(ns7). Similarly, X_0(5) and its j-invariant can be computed by the Small Modular Curves package, and in the quadratic modularity paper X(e7) is computed using a j-invariant for X(ns7). The two j-invariants on X_0(5) obtained like this are NOT the same, and neither are the two j-invariants for X(ns7). They correspond to different (isomorphic) models, and we need to make sure things match up. 

//We start with Xns7. The j-invariant map on Xns7 used in the quadratic modularity paper was computed by Chen, whereas the j-invariant map on Xns7 used in Le Hung's thesis and the cubic modularity paper was computed by Elkies. We find the automorphism on Xns7 that translates between the two.

Fe7<xe7,ye7>:=FunctionField(Xe7);
PP<xx1,xx2,xx3>:=AmbientSpace(Xe7);
Fns7<xe7>:=FunctionField(Xns7);
X1:=SmallModularCurve(1);
jns71:=((3*xe7+1)^3*(4*xe7^2+5*xe7+2)^3*(xe7^2+3*xe7+4)^3*(xe7^2+10*xe7+4)^3)/(xe7^3+xe7^2-2*xe7-1)^7; //The j-invariant map of Chen's model used in the quadratic modularity paper.
jns72:=FunctionField(Xns7)!(Evaluate(G1,[1,1,xe7,1])/Evaluate(G2,[1,1,xe7,1])); //The j-invariant map of Elkies' model used in Le Hung's thesis and the cubic modularity paper.
//In order to use both models, we need the corresponding isomorphism of Xns7=P^1 relating the two models. All Q-automorphisms of P^1 are given by matrices in PGL_2(Q).
//Suppose that phi=[a,b,c,d] is such a matrix.

P3<a,b,c,d>:=ProjectiveSpace(Rationals(),3);
R2<[y]>:=PolynomialRing(CoordinateRing(P3),2);
denj2:=y[1]^3-7*y[1]^2*y[2]+7*y[1]*y[2]^2+7*y[2]^3; //denj2^7 is the denominator of jsn72
denj1:=y[1]^3+y[1]^2*y[2]-2*y[1]*y[2]^2-y[2]^3; //denj1^7 is the denominator of jns71
//Since denj1 and denj2 have the same degree and 1 is the only 7th root of unity in Q, phi must map denj1 to denj2 up to constant.
//Comparing coefficients for y1^3,we see that the constant is a^3+a^2*c-2*a*c^2-c^3.
cfs:=Coefficients(Evaluate(denj1,[a*y[1]+b*y[2],c*y[1]+d*y[2]])-(a^3+a^2*c-2*a*c^2-c^3)*Evaluate(denj2,[y[1],y[2]]));
//We are looking for the values of a,b,c,d such that all polynomials in cfs vanish.
Xphi:=Scheme(P3,cfs);
compsXphi:=IrreducibleComponents(Xphi);
assert (a*d-b*c) in Ideal(compsXphi[1]); //This component does not correspond to invertible matrices, so we can discard it.
assert #compsXphi eq 5;
solsabcd:=[];
for i in [2..5] do
    comp:=compsXphi[i];
    assert Dimension(comp) eq 0;
    ptscomp:=RationalPoints(comp);
    for PP in ptscomp do Append(~solsabcd,Eltseq(PP));
    end for;
end for;
assert #solsabcd eq 3; //We find three possible matrices.
jns7map2:=map<Xns7 -> X1 | [Numerator(ProjectiveFunction(jns72)),Denominator(ProjectiveFunction(jns72))]>;
jns7map1:=map<Xns7 -> X1 | [Numerator(ProjectiveFunction(jns71)),Denominator(ProjectiveFunction(jns71))]>;
phimaps:=[map<Xns7 -> Xns7 | [solsabcd[i][1]*xns7+solsabcd[i][2]*yns7,solsabcd[i][3]*xns7+solsabcd[i][4]*yns7]> : i in [1..3]];
assert phimaps[1]*jns7map1 eq jns7map2;
assert &and[not phimaps[i]*jns7map1 eq jns7map2 : i in [2,3]];
//This shows that there is a unique automorphism  phi of Xns7  such that jns71*phi=jns72.
phins7:=phimaps[1];
tf, psins7:=IsInvertible(phins7);
assert tf;

//We choose to use Chen's model.
pre7ns7:=map<Xe7->Xns7 | [xx1,xx3]>;
prXns7:=map<XlH -> Xns7 | [y1,y2]>*phins7;
jns7map:=jns7map1;

//We compute X(s3,b5) and X_0(15) with their maps to X_0(5)
Xs3b5toX05:=MapFromQuotient(45,[9],5);
Xs3b5:=Domain(Xs3b5toX05);
X05:=Codomain(Xs3b5toX05);
pts35:=PointSearch(Xs3b5,200);
EE,mm:=EllipticCurve(Xs3b5,pts35[1]);
tf,invmm:=IsInvertible(mm);
E,m:=SimplifiedModel(EE); //We consider Xs3b5 as elliptic curve.
prE5:=Inverse(m)*invmm*Xs3b5toX05; //The map E -> X05.
X015:=SmallModularCurve(15);
pr155:=ProjectionMap(X015,15,X05,5);

//We now compute the right projection map from XlH to X05. For his j-invariant on X_0(5), Le Hung refers to Elkies, who computes X_0(5) first in the same manner as the SMC package, and then does a change of variables t \mapsto 5^3/t. Note that Elkies made a typo in the paper and wrote t \mapsto 1/t instead.
prX05:=map<XlH -> X05 | [5^3*x2,x1]>; //This projection map is compatible with the j-inv on X05 computed using the SMC package.
j05:=jFunction(X05,5);
j05fn:=ProjectiveFunction(j05);
j05map:=map< X05 -> X1 | [Numerator(j05fn), Denominator(j05fn)]>;
assert prX05*j05map eq prXns7*jns7map; //This confirms that we've done the right thing.

//We compute M--W groups
MWE,phiE:=MordellWeilGroup(E);
assert IsIsomorphic(MWE,AbelianGroup([2,4]));
assert Order(MWE.1) eq 2 and Order(MWE.2) eq 4;
D3:=Divisor(phiE(MWE.1))-Divisor(Zero(E));
D4:=Divisor(phiE(MWE.2))-Divisor(Zero(E));
MW15,phi15:=MordellWeilGroup(X015);
assert IsIsomorphic(MW15,AbelianGroup([2,4]));
assert Order(MW15.1) eq 2 and Order(MW15.2) eq 4;
D5:=Divisor(phi15(MW15.1))-Divisor(Zero(X015));
D6:=Divisor(phi15(MW15.1))-Divisor(Zero(X015));

//It is important that the maps reduce as they should modulo primes, so we multiply/divide by "excess" prime factors.
defsE5:=[3^(98)*17^(48)/5^(98) * d : d in DefiningEquations(prE5)]; //Somehow each coefficient of each defining equation has these powers of 3, 17 in denominator and 5 in numerator.
defsXX:=[509759177*5^4*2^(10)*7^2*23*127/(3*63577*67271) * d : d in DefiningEquations(XlHtoXb5ns7)];
for p in [3,11,13,17,19,23] do
    defsX:=[];
    m:=Minimum([Valuation(c,p) : c in &cat[Coefficients(eqn) : eqn in defsXX]]);
    for eqn in defsXX do
        Append(~defsX,p^(-m)*eqn);
    end for;
    defsXX:=defsX;
end for;

//We compute the quotient C=X/w5
Cprime,projCprime:=CurveQuotient(AutomorphismGroup(Xb5ns7,[w5]));
C,h:=SimplifiedModel(Cprime);
Xb5ns7toC:=Expand(projCprime*h);
ptsC:=Setseq(Points(C : Bound:=1000)); //6 points
d1:=Place(ptsC[3])-Place(ptsC[1]);
d2:=Place(ptsC[5])-Place(ptsC[1]); //Recall that d1,d2 generate the MW group of C.

//We gather the infomation on Mordell--Weil group generators
divsXe7:=[D7];
divsC:=[d1,d2];
bp:=Place(ptsC[1])+Place(ptsC[2]);
A:=AbelianGroup([0,0,2,2,4]); //Generated by d1,d2,D7,D3,D4 (or replace D3,D4 by D5,D6)
divsE:=[D3,D4];
divsX015:=[D5,D6];

//This function reduces a function up to constant. Constant can be found by evaluating function at a point if necessary.
reduceFunction:=function(f,C,Cp);
divf:=Divisor(f);
reddivf:=reduce(C,Cp,divf);
tf,redf:=IsPrincipal(reddivf);
return redf;
end function;

//This function reduces a function mod p by using the previous function and evaluation at P. Need f(P) to reduce into Fp* for this to work. 
reduceFunctionSc:=function(f,C,Cp,P);
Fp:=BaseRing(Cp);
p:=Characteristic(Fp);
redf:=reduceFunction(f,C,Cp);
a:=Fp!Evaluate(f,P);
redP:=reduce(C,Cp,P);
Embed(ResidueClassField(Decomposition(1*redP)[1][1]),Fp);
b:=Fp!Evaluate(redf,Decomposition(1*reduce(C,Cp,P))[1][1]);
if not a*b eq 0 then return (a/b)*redf; 
else return true;
end if;
end function;

//The below function is used more often: should move it to a file with general functions.
ExpandDifferential:=function(om,Q,tQ,n)
X:=Curve(om);
assert n ge 0;
dt:=Differential(tQ);
f:=om/dt;
FF:=Parent(f);
K:=ResidueClassField(Q);
XK:=ChangeRing(X,K);
Qpt:=XK!Eltseq(RepresentativePoint(Q));
CRK<[xK]>:=CoordinateRing(AmbientSpace(XK));
FK:=FunctionField(XK);
f:=FK!(Evaluate(Numerator(ProjectiveFunction(f)),xK)/Evaluate(Denominator(ProjectiveFunction(f)),xK));
tQ:=FK!(Evaluate(Numerator(ProjectiveFunction(tQ)),xK)/Evaluate(Denominator(ProjectiveFunction(tQ)),xK));
alist:=[Evaluate(f,Qpt)];
if n gt 0 then
flist:=[(f-(Evaluate(f,Qpt)))/tQ];
for i in [1..n] do
    Append(~alist,flist[i](Qpt));
    Append(~flist,(flist[i]-alist[i+1])/tQ);
end for;
end if;
return alist;
end function;

//Input: exp is the expansion of a differential omega at a place Q wrt a uniformizer tQ.
//If tQ is well-behaved and exp has length 2g-2 then the result is (omega/dtQ)(Q).
a0:=function(exp,p,Fq)
K:=Parent(exp[3]);
OK:=MaximalOrder(K);
factp:=Factorization(p*OK);
pp:=factp[1][1]; //We make a choice of prime above p. Different choice corresponds to the expansion around the Galois conjugate point. Note that for relative Chabauty we need to choose only one point from deg2pb[i] and it doesn't matter which one.
FF,red:=ResidueClassField(pp);
Embed(FF,Fq);
pi:=UniformizingElement(pp);
m:=Minimum([Valuation(a,pp) : a in exp]);
expred:=[red(pi^(-m)*a) : a in exp];
//If exp has length 2g-2, then by construction, expred must be the expansion of an integral differential at p.
return expred[1];
end function;

//MORDELL-WEIL SIEVE FOR QUADRATIC POINTS

/* INPUT: model for projective curve X/\Q; set deg2 of degree 2 divisors on X,
split into sets deg2pb and deg2npb of pullbacks from C(\Q) and not pullbacks
from C(\Q) respectively,
set auts of matrices defining Atkin-Lehner operators on X such that C=X/Gamma 
,where Gamma is the group generated by the AL operators in auts, satisfying
rk(J(C)(\Q))=rk(J(X)(\Q)); set divs of degree 0 divisors that generate a subgroup G \subset J(X)(\Q), 
and an integer I such that I*J(X)(\Q) \subset G,
an abstract abelian group A isomorphic to G such that A.i corresponds to divs[i]
and a number genusC that is the genus of C; if #Gamma=2 also a degree 2 divisor
bp on X that is the pullback of a rational point on C, to be used to embed X^{(2)} in J. */

//This function verifies that the residue class of deg2pb[i] contains only pullbacks.
IsOnlyWithFamily:=function(i,p,a0sp)
if p le 7 then
return false;
end if;
a0list:=a0sp[i];
if not &and[a eq 0 : a in a0list] then
return true;
else return false;
end if;
end function;


/*This function translates the info from IsOnlyWithFamily
into the right subgroup of A. Input are a prime p, and a set L of degree 2
divisors on X (the known points). It outputs a subgroup B of A together 
with the inclusion map iA: B --> A and the set W\subset A of possible
B-cosets that IsLonely and IsWithFamily allow. */

//The below function computes the pushforward of a divisor under a map to P^1
quickpfwd:=function(fmap,D)
f:=FunctionField(Domain(fmap))!(DefiningEquations(fmap)[1]/DefiningEquations(fmap)[2]);
decD:=Decomposition(D);
evas:=<Evaluate(f,d) : d in [dd[1] : dd in decD]>;
pfwds:=[];
for eva in evas do
    if not eva eq 0 and 1/eva eq 0 then
        Append(~pfwds,Place(Codomain(fmap)![1,0]));
    else Append(~pfwds,Place(Codomain(fmap)(Parent(eva))![eva,1]));
    end if;
end for;
mults:=[decD[i][2]*(Integers()!(Degree(decD[i][1])/Degree(pfwds[i]))) : i in [1..#decD]];
pfwd:=&+[mults[i]*pfwds[i] : i in [1..#mults]];
assert Degree(pfwd) eq Degree(D);
return pfwd;
end function;

//Given a map pr: Y--> Z and divisor D on Z, the below function computes the divisors on Y pushing forward to D.
InvImages:=function(pr,D)
dec:=Decomposition(D);
pls:=[d[1] : d in dec];
mults:=[d[2] :d in dec];
d:=Degree(D);
pbs:=[Pullback(pr,P) : P in pls]; 
pbdecs:=[Decomposition(pb) : pb in pbs];
poss:=[[&+[a[j]*pbdecs[i][j][1] : j in [1..#pbdecs[i]]] : a in CartesianPower([0..d],#pbdecs[i]) | &+[aa : aa in a] le d and &+[a[j]*Degree(pbdecs[i][j][1]) : j in [1..#pbdecs[i]]] eq mults[i]*Degree(pls[i])] : i in [1..#pbdecs]];
Ds:=[&+[DD : DD in a] : a in CartesianProduct(poss)]; 
assert &and[Degree(DD) eq d : DD in Ds];
return Ds;
end function;

//The below function evaluates a function at a place P. If zero or infinite, it will divide/multiply f by the square of a uniformiser at P and try to evaluate that. Either returns a finite non-zero number or returns zero. Hence IsSquare(EvalNotInf(t,P)) determines whether P in C splits in X or not. If EvalNotInf(t,P)=0, that means P ramifies in X -> C.
EvalNotInf:=function(f,P);
ev:=Evaluate(f,P);
if Type(ev) eq Infty then
    unifP:=UniformizingParameter(P);
    f:=f*unifP^2;
    ev:=Evaluate(f,P);
    if Type(ev) eq Infty then return $$(f,P);
    else return ResidueClassField(P)!ev;
    end if;
elif ev eq 0 then
    unifP:=UniformizingParameter(P);
    f:=f/unifP^2;
    ev:=Evaluate(f,P);
    if ev eq 0 then return $$(f,P);
    elif Type(ev) eq Infty then return (ResidueClassField(P)!0);
    else return ResidueClassField(P)!ev;
    end if;
else return ResidueClassField(P)!ev;
end if;
end function;


ChabautyInfo:=function(deg2pb,p,B,iA,W,t,prE5,divs,unifsC,exps)
Fp:=GF(p);
Fp2:=GF(p^2);
Cp:=ChangeRing(C,Fp);
assert not IsSingular(Cp);
assert &and[Valuation(Divisor(reduceFunction(unifsC[i],C,Cp)),Decomposition(1*reduce(C,Cp,Place(ptsC[i])))[1][1]) eq 1 : i in [1..#ptsC]];
//The above shows that unifsC are well-behaved uniformizers at the points in ptsC, and hence unifsX are well-behaved at the pts in deg2pb as long there is no ramification mod p (which we check below).
a0sp:=<[a0(exp,p,Fp2) : exp in ee] : ee in exps>;

//We reduce all relevant objects mod p
tp:=reduceFunctionSc(t,C,Cp,Place(ptsC[6])); //tp checks whether a place on Cp splits on X or not.
assert &and[not EvalNotInf(tp,Decomposition(reduce(C,Cp,Place(P)))[1][1]) eq 0  : P in ptsC]; //Indeed no ramification.
Xb5ns7p:=ChangeRing(Xb5ns7,Fp);
Rp<xp,yp,zp>:=CoordinateRing(AmbientSpace(Xb5ns7p));
Xns7p:=ChangeRing(Xns7,Fp);
Rns7p<xns7p,zns7p>:=CoordinateRing(AmbientSpace(Xns7p));
Xb5ns7toCp:=map<Xb5ns7p->Cp | [Evaluate(eqn,[xp,yp,zp]): eqn in DefiningEquations(Xb5ns7toC)]>;
Xe7p:=ChangeRing(Xe7,Fp);
Re7p<xe7p,ye7p,ze7p>:=CoordinateRing(AmbientSpace(Xe7p));
PxPp<x1p,x2p,y1p,y2p>:=ProductProjectiveSpace(GF(p),[1,1]);
XlHp:=Curve(Scheme(PxPp,[Evaluate(eqn,[x1p,x2p,y1p,y2p]) : eqn in DefiningEquations(XlH)]));
XlHtoXb5ns7p:=map<XlHp->Xb5ns7p | [Evaluate(eqn,[x1p,x2p,y1p,y2p]) : eqn in defsXX]>;
pre7ns7p:=map<Xe7p -> Xns7p | [Evaluate(eqn, [xe7p,ye7p,ze7p]) : eqn in DefiningEquations(pre7ns7)]>;
prXns7p:=map<XlHp -> Xns7p | [Evaluate(eqn,[x1p,x2p,y1p,y2p]) : eqn in DefiningEquations(prXns7)]>; 
X05p:=ChangeRing(X05,Fp);
prX05p:=map<XlHp -> X05p | [Evaluate(eqn,[x1p,x2p,y1p,y2p]) : eqn in DefiningEquations(prX05)]>;
E:=Domain(prE5);
Ep:=ChangeRing(E,Fp);
REp<xEp,yEp,zEp>:=CoordinateRing(AmbientSpace(Ep));
prE5p:=map<Ep -> X05p | [Evaluate(eqn,[xEp,yEp,zEp]) : eqn in defsE5]>;

redsC:=[2*reduce(C,Cp,Place(pt)): pt in ptsC];
tfs:=[IsOnlyWithFamily(i,p,a0sp) : i in [1..#redsC]]; //We check which quadratic places have only pullbacks in their residue class
//tfs:=[true,true,true,true,true,true]; //Use this line to test the sieve without having to wait for an hour to compute exps.
//We now compute M--W groups over Fp
CC,phii,psi:=ClassGroup(Cp);
Z:=FreeAbelianGroup(1);
degr:=hom<CC->Z | [ Degree(phii(a))*Z.1 : a in OrderedGenerators(CC)]>;
JFp:=Kernel(degr); // This is isomorphic to J_C(\F_p).
fact:=Factorisation(#JFp);
n:=1;
for pp in fact do
    if pp[1] gt 11 and not pp[1] in [23,41,71,233] then n:=n*pp[1]^(pp[2]);
    end if;
end for;
mn:=hom<JFp -> JFp | [n*g : g in OrderedGenerators(JFp)]>; 
//When sieving we neglect all factors of JFp whose order is not a power of a small prime, by multiplying by such numbers. This greatly improves the speed of the sieve. 

CE,phiCE,psiCE:=ClassGroup(Ep);
degrCE:=hom<CE->Z | [ Degree(phiCE(a))*Z.1 : a in OrderedGenerators(CE)]>;
JEFp:=Kernel(degrCE); // This is isomorphic to J_E(\F_p).
bpE:=Place(Zero(Ep));

Ce7,phie7,psie7:=ClassGroup(Xe7p);
Z:=FreeAbelianGroup(1);
degre7:=hom<Ce7->Z | [ Degree(phie7(a))*Z.1 : a in OrderedGenerators(Ce7)]>;
Je7Fp:=Kernel(degre7); // This is isomorphic to J_Xe7(\F_p).
bpe7p:=reduce(Xe7,Xe7p,bpe7);

divsp:=<reduce(C,Cp,divs[1]),reduce(C,Cp,divs[2]),reduce(Xe7,Xe7p,divs[3]),reduce(E,Ep,divs[4]),reduce(E,Ep,divs[5])>;
bpp:=reduce(C,Cp,bp);//We reduce the divisors and the basepoint
JxJxJ,phis:=DirectSum([JFp,Je7Fp,JEFp]);
mnJxJxJ:=hom<JxJxJ -> JxJxJ | [n*g : g in OrderedGenerators(JxJxJ)]>;
hC:=hom<A -> JFp | [JFp!psi(divsp[1]),JFp!psi(divsp[2])] cat [JFp!0,JFp!0,JFp!0]>; //The map A--> J_X(\F_p).
h:=hom<A -> JxJxJ | [phis[1](JFp!psi(divsp[1])),phis[1](JFp!psi(divsp[2])),phis[2](Je7Fp!psie7(divsp[3])),phis[3](JEFp!psiCE(divsp[4])),phis[3](JEFp!psiCE(divsp[5]))]>;
hE:=hom<A -> JEFp | [JEFp!0,JEFp!0,JEFp!0, JEFp!psiCE(divsp[4]),JEFp!psiCE(divsp[5])]>;
he7:=hom<A -> Je7Fp | [Je7Fp!0,Je7Fp!0] cat [Je7Fp!psie7(divsp[3])] cat [Je7Fp!0,Je7Fp!0] >;

//We now split our cosets in W into smaller cosets on which h takes a single value.
Bp,iAp:=sub<A | Kernel(h)>;
newB,newiA:=sub<A | iA(B) meet iAp(Bp)>;
AmodnewB,pi1:=quo< A | newiA(newB)>;
AmodB,pi2:=quo<AmodnewB | pi1(iA(B))>;
WW:=[(x+w)@@pi1 : x in Kernel(pi2), w in pi1(W)];
imW:={h(x) : x in WW}; //And map them to J_X(\F_p).
mnimW:={mnJxJxJ(x) : x in imW}; //Note that n is coprime to the orders of the Q-rational torsion subgroups
imWC:={hC(x) : x in WW};
imWe7:={he7(x) : x in WW};
redsCJ:=[JFp!psi(DD-bpp) : DD in redsC];
newimW:={};

//For p ge 97 Magma struggles with the computation of Riemann--Roch spaces, so we compute effective degree 2 divisors by listing points. For this we make the following precomputation: we list all degree 2 effective divisors on Cp together with their images in the M--W group.
if p ge 97 then
    Ap:=AffinePatch(Cp,1);
    ptsAp:=Points(Ap,Fp2);
    pts2:=[Place(Cp(Fp2)!(Eltseq(pt) cat [1])) : pt in ptsAp] cat [Place(pt) : pt in PointsAtInfinity(Cp)];
    pls2:=[P : P in pts2 | Degree(P) eq 2];
    pls1:=[P : P in pts2 | Degree(P) eq 1];
    divs2:=pls2 cat [pls1[i]+pls1[j] : i in [1..#pls1], j in [1..#pls1] | i le j]; //All deg 2 divs occur twice, but removing doubles is expensive.
    divwithimage:=[<D,JFp!(psi(D-bpp))> : D in divs2];
end if;

//The below for-loop will decide which points in imW correspond to effective degree 2,4,4 divisors on X, Xe7 and E respectively, which could come from a rational degree 4 divisor on X(s3,b5,e7) or X(b3,b5,e7). 
for x in imWC do
phis1mnx:=phis[1](mn(x)); //We multiply by n and embed in JxJxJ. We give the result an original name.
posx:={phis1mnx + a*h(A.3) + b*h(A.4)+c*h(A.5) : a in {0,1}, b in {0,1}, c in {0..7}}; //Possible elements of JxJxJ in image mapping to x, multiplied by n. Note that n is coprime to the torsion orders.

if not #(posx meet mnimW) eq #(posx meet newimW) then //If we have already added all of posx meet mnimW, then there is no need to consider it again. This often happens and is how multiplication by n speeds up the sieve.

    if (not p ge 97) or (x eq hC(A!0)) then
    phx:=phii(x);
    V,PHI:=RiemannRochSpace(phx+bpp);
    fns:=[PHI(V.i) : i in [1..Dimension(V)]];
    CP:=ProjectiveSpace(Fp,#fns-1);
    divsx:=[Divisor(&+[a[i]*fns[i] : i in [1..#fns]])+bpp+phx : a in Points(CP,Fp)]; //The deg2 divs mapping to x.
    //if x is not zero then #divsx = 1, else #divsx = p+1
    else divsx:=Setseq({DD[1] : DD in divwithimage | DD[2] eq x});
    end if;
    
    for divx in divsx do
    dec:=Decomposition(divx);
    //The below if-statement checks whether divx could come from an eff degr 2 div on X that isn't a pullback.
    if (#dec eq 1 and dec[1][2] eq 1 and IsSquare(EvalNotInf(tp,dec[1][1]))) or (#dec eq 2 and IsSquare(EvalNotInf(tp,dec[1][1])) and IsSquare(EvalNotInf(tp,dec[2][1]))) or (#dec eq 1 and dec[1][2] eq 2 and not dec[1][2]*dec[1][1] in redsC) or (#dec eq 1 and (dec[1][2]*dec[1][1] in redsC) and not tfs[Index(redsC,dec[1][2]*dec[1][1])]) then 
        
        //Now we check which deg4 eff divisors on Xe7 and E divx could come from.
        pbXb5ns7:=Pullback(XlHtoXb5ns7p,Pullback(Xb5ns7toCp,divx)); //We pull back to XlH, then push forward to Xns7
        pfwd:=quickpfwd(prXns7p,pbXb5ns7); //And finally look for inverse images in Xe7.
        De7s:=InvImages(pre7ns7p,pfwd); //We then do the same for E.
        pfwd:=quickpfwd(prX05p,pbXb5ns7);
        DEs:=InvImages(prE5p,pfwd);
        
        //Finally we multiply all these options by n and add them.
        newimW:=newimW join {mnJxJxJ(H) : H in ({phis[1](x)+phis[2](Je7Fp!psie7(DD-Degree(DD)*bpe7p))+phis[3](JEFp!psiCE(dd-Degree(dd)*bpE)) : DD in De7s, dd in DEs} meet imW)};
    end if;
    end for; 
end if;
end for;

mnjposP:=newimW;
print "The number of elements in mnjposP is"; #mnjposP;
//Finally we save only the information up to multiplication by n. 
h:=h*mnJxJxJ;
Bp,iAp:=sub<A | Kernel(h)>;
newB,newiA:=sub<A | iA(B) meet iAp(Bp)>;
AmodnewB,pi1:=quo< A | newiA(newB)>;
AmodB,pi2:=quo<AmodnewB | pi1(iA(B))>;
W:=[(x+w)@@pi1 : x in Kernel(pi2), w in pi1(W)];
B:=newB; iA:=newiA;
W:=[x : x in W | h(x) in mnjposP];
return W,B,iA;
end function;


// L is a set of known points on X.
// primes is the set of primes of good reduction you want the sieve to consider.
// Also assume A is the abstract abelian group generated by divs in J(X)(\Q)
// such that A.i corresponds to divs[i] for each i.

MWSieve:=function(L,primes,t,prE5,divs,unifsC,exps)
B,iA:=sub<A|A>; //This subgroup will shrink as we consider more primes. We excluded the coset 0+B because it corresponds to points from the quotient.
W:={0*A.1};
// Together, B+W \subset A consists of the possible images of unknown (rational)
// points in A. The map X(\Q) \to A is composition of X(\Q) \to J(X)(\Q) and
// multiplication by integer I such that I*J(X)(\Q) \subset A.

for p in primes do
p;
W,B,iA:=ChabautyInfo(L,p,B,iA,W,t,prE5,divs,unifsC,exps);
if W eq [] then return true; end if;
#W;
end for;
return B,iA,W;
end function;




