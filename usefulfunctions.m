//This file contains a number of functions that are either useful in their own right,
//or are used at least in two separate Magma files. 

load "ozmansiksek2.m";

/*
List of functions defined in this file, in order of occurrence:
- JacobianFp
- RatPtsSubgp
- AbelJacobiInverse

- quickpfwd
- quickpfwdhyp2
- InvImages

- reduceFunction
- reduceFunctionSc
- EvalNotInf
- ExpandDifferential
- a0

- ModCrvQuot
- MapFromQuotient
- HyperellipticModularQuotient
- MapFromHyperellipticQuotient
- MapToP1FromqExp
*/

//---------Mordell--Weil groups and Abel--Jacobi map-----------------

//This function computes J_X(F_p).
JacobianFp:=function(X)
CC,phii,psii:=ClassGroup(X); //Algorithm of Hess
Z:=FreeAbelianGroup(1);
degr:=hom<CC->Z | [ Degree(phii(a))*Z.1 : a in OrderedGenerators(CC)]>;
JFp:=Kernel(degr); // This is isomorphic to J_X(\F_p).
return JFp,phii,psii;
end function;

//This function computes the subgroup of J_XX(F_p)
//generated by the differences of rational points.
RatPtsSubgp:=function(XX,p) //Contains the cuspidal subgp if all cusps are rational.
if not IsHyperelliptic(XX) then
ptsXX:=PointSearch(XX,200);
else ptsXX:=Setseq(Points(XX : Bound:=200));
end if;
Xp:=ChangeRing(XX,GF(p));
assert not IsSingular(Xp);
Jp,phip,psip:=JacobianFp(Xp);
ZZ:=FreeAbelianGroup(#ptsXX-1);
hC:=hom<ZZ -> Jp | [psip(Place(Xp![GF(p)!a : a in Eltseq(ptsXX[i])])-Place(Xp![GF(p)!b : b in Eltseq(ptsXX[1])])) : i in [2..#ptsXX]]>; 
//The isomorphic image of the rational cusp subgp inside Jp.
return Image(hC),hC;
end function;

//Computes all effective degree d=Degree(D0) divisors mapping into the classes
//in divlist under the Abel-Jacobi map defined by D |--> [D-D0]
//Works only if all Riemann--Roch spaces are at most 1-dimensional
AbelJacobiInverse:=function(divlist,D0)
degddivs:=[];
for D in divlist do
    RR,phi:=RiemannRochSpace(D+D0);
    assert Dimension(RR) le 1; 
    if Dimension(RR) eq 1 then
        Append(~degddivs,D+D0+Divisor(phi(RR.1)));
    end if;
end for;
return degddivs;
end function;


//---------Pullback and pushforward of divisors------------------

//The below function computes the pushforward of a divisor under a map to P^1
quickpfwd:=function(fmap,D,CD)
if Type(fmap) eq FldFunFracSchElt then f:=fmap;
else f:=FunctionField(Domain(fmap))!(DefiningEquations(fmap)[1]/DefiningEquations(fmap)[2]);
end if;
decD:=Decomposition(D);
evas:=<Evaluate(f,d) : d in [dd[1] : dd in decD]>;
pfwds:=[];
for eva in evas do
    if not eva eq 0 and 1/eva eq 0 then
        Append(~pfwds,Place(CD![1,0]));
    else Append(~pfwds,Place(CD(Parent(eva))![eva,1]));
    end if;
end for;
mults:=[decD[i][2]*(Integers()!(Degree(decD[i][1])/Degree(pfwds[i]))) : i in [1..#decD]];
pfwd:=&+[mults[i]*pfwds[i] : i in [1..#mults]];
assert Degree(pfwd) eq Degree(D);
return pfwd;
end function;

//Input: 2 functions f1 and f2 such that map is (f1:f2:1) (remember to divide by a cube for f2)
quickpfwdhyp2:=function(f1,f2,D,CD)
decD:=Decomposition(D);
evas1:=<Evaluate(f1,d) : d in [dd[1] : dd in decD]>;
evas2:=<Evaluate(f2,d) : d in [dd[1] : dd in decD]>;
pfwds:=[];
for i in [1..#evas1] do
    eva1:=evas1[i]; eva2:=evas2[i];
    KK:=ResidueClassField(decD[i][1]);
    if ((not eva1 eq 0 and 1/eva1 eq 0) or (not eva2 eq 0 and 1/eva2 eq 0)) then
        Append(~pfwds,Place(CD(KK)![1,Evaluate(f2/f1^3,decD[i][1]),0]));
    else Append(~pfwds,Place(CD(KK)![eva1,eva2,1]));
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
poss:=[[&+[a[j]*pbdecs[i][j][1] : j in [1..#pbdecs[i]]] : a in CartesianPower([0..d],#pbdecs[i]) | 
    &+[aa : aa in a] le d and &+[a[j]*Degree(pbdecs[i][j][1]) : j in [1..#pbdecs[i]]] eq mults[i]*Degree(pls[i])] : i in [1..#pbdecs]];
Ds:=[&+[DD : DD in a] : a in CartesianProduct(poss)]; 
assert &and[Degree(DD) eq d : DD in Ds];
return Ds;
end function;



//-------Functions and differentials------------------------

//This function reduces a function up to constant. 
//Constant can be found by evaluating function at a point if necessary.
reduceFunction:=function(f,C,Cp);
divf:=Divisor(f);
reddivf:=reduce(C,Cp,divf);
tf,redf:=IsPrincipal(reddivf);
return redf;
end function;

//This function reduces a function mod p by using the previous function and evaluation at
//one of the points in pts. Need f(P) to reduce into Fp* for one P in pts for this to work. 
reduceFunctionSc:=function(f,C,Cp,pts);
Fp:=BaseRing(Cp);
p:=Characteristic(Fp);
redf:=reduceFunction(f,C,Cp);
for pt in pts do
    P:=Place(pt);
    ev:=Evaluate(f,P);
    if not Type(ev) eq Infty and not (Denominator(ev) mod p) eq 0 then
    a:=Fp!Evaluate(f,P);
    redP:=reduce(C,Cp,P);
    Embed(ResidueClassField(Decomposition(1*redP)[1][1]),Fp);
    b:=Fp!Evaluate(redf,Decomposition(1*reduce(C,Cp,P))[1][1]);
    if not a*b eq 0 then return (a/b)*redf; end if;
    end if;
end for;
return true;
end function;

//The below function evaluates a function at a place P. 
//If zero or infinite, it will divide/multiply f by the square of a uniformiser at P and try to evaluate that. 
//This is ambiguous, but the point is that IsSquare(EvalNotInf) is well-defined.
//Either returns a finite non-zero number or returns zero.
//If X-->C is a degree 2 map such that t in FunctionField(C) is not a square
//but pulls back to a square on X, thenIsSquare(EvalNotInf(t,P)) 
//determines whether P in C splits in X or not. 
//If EvalNotInf(t,P)=0, that means P ramifies in X -> C.

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


//The following function computes the expansion of a differential 
//om around the uniformizer tQ of a point Q, up to the (n+1)th coefficient a_n.
ExpandDifferential:=function(om,Q,tQ,n)
if Type(Q) eq PlcCrvElt then
    Q:=RepresentativePoint(Q);
end if;
assert n ge 0;
dt:=Differential(tQ);
f:=om/dt;
FF:=Parent(f);
K:=Parent(Eltseq(Q)[1]);
XK:=ChangeRing(Curve(om),K);
Qpt:=XK!Eltseq(Q);
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
//If tQ is well-behaved and exp has length 2g-2 then the result is 
//the mod p reduction of (omega/dtQ)(Q).
a0:=function(exp,p,Fq)
K:=Parent(exp[3]);
OK:=MaximalOrder(K);
factp:=Factorization(p*OK);
pp:=factp[1][1]; //We make a choice of prime above p. 
//Different choice corresponds to the expansion around the Galois conjugate point. 
//Note that for relative Chabauty we need to choose only one point from deg2pb[i] and it doesn't matter which one.
FF,red:=ResidueClassField(pp);
Embed(FF,Fq);
pi:=UniformizingElement(pp);
m:=Minimum([Valuation(a,pp) : a in exp]);
expred:=[red(pi^(-m)*a) : a in exp];
//If exp has length 2g-2, then by construction, expred must be the expansion of an integral differential at p.
return expred[1];
end function;




//---------Models for modular curves and maps-----------------------

//The below functions compute models for modular curves
//and maps between them. All of these are based on the modeqns function
//written by Ozman and Siksek. In particular, they compute (maps between)
//modular curves by determining equations between q-expansions. 
//While Magma has good implementation for maps between modular curves X_0(N),
//the implementation for quotients of modular curves is limited.
//There are a few functions depending on whether the curve is
//non-hyperelliptic, hyperelliptic of genus geq 2, or elliptic.

//ModCrvQuot computes the quotient of a modular curve by the Atkin--Lehner involutions
//w_M for M in wlist, as well as the action of the Atkin--Lehner involutions
//w_m for m in remwlist on this quotient. The Magma function 
//ModularCurveQuotient can also compute such quotients, but not the action of A--L invs. 
//ModCrvQuot is only implemented for non-hyperelliptic quotients of modular curves.

ModCrvQuot:=function(N,wlist,remwlist)
C:=CuspForms(N);
ws:=[AtkinLehnerOperator(C,n) : n in wlist];
remws:=[AtkinLehnerOperator(C,n) : n in remwlist];
W:=AtkinLehnerOperator(C,N);
NN:=&meet([Nullspace(Matrix(w-1)) : w in ws] cat [Nullspace(1-W^2)]);
dim:=Dimension(NN);
seqs:=[[Coordinates(NN,Basis(NN)[i]*Matrix(w)) : i in [1..dim]] : w in remws];
BB:=[&+[(Integers()!(2*Eltseq(Basis(NN)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..dim]];
prec:=500;
L<q>:=LaurentSeriesRing(Rationals(),prec);
R<[x]>:=PolynomialRing(Rationals(),dim);
Bexp:=[L!qExpansion(BB[i],prec) : i in [1..dim]];
eqns:=[R | ];
	d:=1;
	tf:=false;
	while tf eq false do
		d:=d+1;
		mons:=MonomialsOfDegree(R,d);
		monsq:=[Evaluate(mon,Bexp) : mon in mons];
		V:=VectorSpace(Rationals(),#mons);
		W:=VectorSpace(Rationals(),prec-10);
		h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
		K:=Kernel(h);
		eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
        I:=Radical(ideal<R | eqns>);
		X:=Scheme(ProjectiveSpace(R),I);
		if Dimension(X) eq 1 then
			if IsSingular(X) eq false then
				X:=Curve(ProjectiveSpace(R),eqns);
				if Genus(X) eq dim then
					tf:=true;
				end if;
			end if;
		end if;
	end while;
	eqns:=GroebnerBasis(ideal<R | eqns>); // Simplifying the equations.
	tf:=true;
	repeat
		t:=#eqns;
		tf:=(eqns[t] in ideal<R | eqns[1..(t-1)]>);
		if tf then 
			Exclude(~eqns,eqns[t]);
		end if;
	until tf eq false;
	t:=0;
	repeat
		t:=t+1;
		tf:=(eqns[t] in ideal<R | Exclude(eqns,eqns[t])>);	
		if tf then
			Exclude(~eqns,eqns[t]);
			t:=0;
		end if;
	until tf eq false and t eq #eqns;
	X:=Curve(ProjectiveSpace(R),eqns); // Our model for X_0(N) discovered via the canonical embedding.
	assert Genus(X) eq dim;
	assert IsSingular(X) eq false;
    indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];	
	indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)
	for eqn in eqns do
		eqnScaled:=LCM([Denominator(c) : c in Coefficients(eqn)])*eqn;
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound.
										// See Stein's book, Thm 9.18.
		Bexp1:=[qExpansion(BB[i],hecke+10) : i in [1..dim]]; // q-expansions
                        // of basis for S 
                        // up to precision hecke+10.
		assert Valuation(Evaluate(eqnScaled,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X. 
seqlist:=[[&+[seq[i][j]*x[j] : j in [1..dim]] : i in [1..dim]] : seq in seqs];
wmaplist:=[iso<X->X | seq,seq> : seq in seqlist];
return X,wmaplist;
end function;

//This function computes the map X_0(N)/ws --> X_0(n), assuming that
//X_0(n)=P^1. It computes first X_0(N), and is not very efficient.
//This works well when X_0(N)/ws is an elliptic curve and X_0(N)
//is not. Then cusp forms for X_0(N) are used.
//We require that the product of the integers in wlist equals N/n and is a square. 
//We construct the map X_0(N)/ws --> X_0(N) given on q-expansions by q |--> q^l, where l^2=N/n.

MapFromQuotient:=function(N,ws,n)
tf,m:=IsSquare(Integers()!(N/n));
assert tf;
X0N:=SmallModularCurve(N);
X0n:=SmallModularCurve(n);
ws:=[AtkinLehnerInvolution(X0N,N,w) : w in ws];
Y,prY:=CurveQuotient(AutomorphismGroup(X0N,ws));
prec:=200;
L<q>:=LaurentSeriesRing(Rationals(),prec);
qexps:=qExpansionsOfGenerators(N,L,200); //These are the q-expansions of the cuspforms defining the model for X_0(N) computed by the SMC package.
fn:=qExpansionsOfGenerators(n,L,200)[1]; //This is the q-expansion of the Hauptmodul function on X_0(n) with respect to which the SMC package computes maps to and from X_0(n). Starts as q^-1+... 
fnm:=Evaluate(fn,q^m); //This is a function on Y.
eqns:=DefiningEquations(prY);
eqnsev:=[Evaluate(eqn,qexps) : eqn in eqns];
fns:=[eqnsev[i]/eqnsev[#eqns] : i in [1..#eqns-1]]; //The q-exps of modular functions generating
//the function field of Y. To compute the map we simply need to write fnd as
//a rational function in the elements of fns. We can do this by linear algebra on q-exps.
tf:=false;
d:=0;
while tf eq false do
d:=d+1;
R:=PolynomialRing(Rationals(),#eqns-1);
mons:=&cat[Setseq(MonomialsOfDegree(R,e)) : e in [0..d]];
k:=prec-100;
Zk:=FreeAbelianGroup(k);
Zm:=VectorSpace(Rationals(),(2*#mons));
Zk:=VectorSpace(Rationals(),k+101);
h:=hom<Zm -> Zk | [[Coefficient(Evaluate(mons[i],fns)*fnm,j) : j in [-100..k]] : i in [1..#mons]] cat [[Coefficient(Evaluate(-mons[i],fns),j) : j in [-100..k]] : i in [1..#mons]]>;
K:=Kernel(h);
for v in Basis(K) do
if not &+[Eltseq(v)[j] : j in [1..#mons]] eq 0 and not &+[Eltseq(v)[j+#mons] : j in [1..#mons]] eq 0   then
vseq:=Eltseq(v);
tf:=true;
end if; 
end for;
end while;
F<[xx]>:=FunctionField(Y);
theeqn:=Evaluate(&+[vseq[i+#mons]*mons[i] : i in [1..#mons]],xx)/Evaluate(&+[vseq[i]*mons[i] : i in [1..#mons]],xx);
thefn:=ProjectiveFunction(theeqn);
themap:=map<Y->X0n | [Numerator(thefn),Denominator(thefn)]>; //This is the one.
projNn:=ProjectionMap(X0N,N,X0n,n,m); //Map X0N->X0n that is multiplication by m on complex upper half plane
assert projNn eq prY*themap; //This proves that we have found the right map. No need to check if we computed q-expansions to suff high order.
return themap;
end function;

//The above function is too inefficient to compute X_0(63)/w_9 --> X_0(7), so we 
//consider hyperelliptic curves separately.

//There exists a Magma function ModularCurveQuotient for computing any quotient of a modular curve by Atkin--Lehner involutions.
//However, we also need q-expansions corresponding to the coordinates. For hyperelliptic curves, these are not just given by cusp forms.
HyperellipticModularQuotient:=function(N,wlist)
C:=CuspForms(N);
ws:=[AtkinLehnerOperator(C,a) : a in wlist];
NN:=&meet[Nullspace(Matrix(w-1)) : w in ws];
dimC:=Dimension(C);
dimN:=Dimension(NN);
den:=LCM(&cat[[Denominator(Eltseq(v)[i]) : i in [1..#Eltseq(v)]] : v in Basis(NN)]);
B:=[&+[(Integers()!(den*Eltseq(Basis(NN)[i])[j]))*C.j : j in [1..dimC]] : i in [1..dimN]]; //basis for cusp forms fixed by ws
prec:=500;
L<q>:=LaurentSeriesRing(Rationals(),prec);
x:=(L!qExpansion(B[#B-1],500))/(L!qExpansion(B[#B],500));
y:=q*Derivative(x)/(L!qExpansion(B[#B],500));
d:=2*dimN+2;
R<[xx]>:=PolynomialRing(Rationals(),2);
mons:=&cat[Setseq(MonomialsOfDegree(R,e)) : e in [0..d]];
m:=#mons;
k:=prec-100;
Zm:=VectorSpace(Rationals(),#mons);
Zk:=VectorSpace(Rationals(),k+101);
h:=hom<Zm -> Zk | [[Coefficient(Evaluate(mons[i],[x,y]),j) : j in [-100..k]] : i in [1..m]]>;
K:=Kernel(h);
assert Dimension(K) eq 1; //The equation we construct from K holds provably as it is the only one.
//This is not the most efficient way of finding the equation; since we know that such a hyperelliptic equation between x and y exists,
//we can also remove a multiple of x^d from y^2 to make lowest coefficient in q-exp vanish, then continue with x^(d-1) etc. 
eqnlist:=Eltseq(Basis(K)[1]);
den:=LCM([Denominator(aa) : aa in eqnlist]);
hypeqn:=&+[den*eqnlist[i]*mons[i] : i in [1..#mons]];
ysqcoeff:=-MonomialCoefficient(hypeqn,xx[2]^2);
hypeqn:=hypeqn/ysqcoeff;
assert Evaluate(hypeqn,[0,xx[2]]) eq -xx[2]^2+MonomialCoefficient(hypeqn,1);
RR<z>:=PolynomialRing(Rationals());
hypeqn:=Evaluate(hypeqn,[z,0]);
Y:=HyperellipticCurve(hypeqn);
return Y,[x,y];
end function;

//The below function is the same as MapFromQuotient, but only
//works for hyperelliptic curves and is more efficient in that case.
//Input N and wlist st X_0(N)/wlist is a hyperelliptic modular curve.
//Currently needs X_0(n) to be P^1.
//wlist is a sequence of integers dividing N maximally, corresponding to Atkin--Lehner operators on X_0(N).
//We require that the product of the integers in wlist equals N/n and is a square. 
//We construct the map X_0(N)/ws --> X_0(N) given on q-expansions by q |--> q^l, where l^2=N/n.

MapFromHyperellipticQuotient:=function(N,wlist,n)
tf,ell:=IsSquare(Integers()!(N/n));
assert tf;
prec:=500;
Y,qexps:=HyperellipticModularQuotient(N,wlist);
x,y:=Explode(qexps);
L<q>:=Parent(x);
F<xx,yy>:=FunctionField(Y);
Z:=SmallModularCurve(n);
qE:=qExpansionsOfGenerators(n,L,prec)[1];
qE3:=Evaluate(qE,q^(ell));

//We search for polynomials p(x,y) and q(x,y) such that qE3 = p(x,y)/q(x,y), i.e. qE3*q(x,y) = p(x,y)
tf:=false;
d:=0;
while tf eq false do
    d:=d+1;
    R:=PolynomialRing(Rationals(),2);
    mons:=&cat[Setseq(MonomialsOfDegree(R,e)) : e in [0..d]];
    m:=#mons;
    k:=prec-100;
    Zm:=VectorSpace(Rationals(),(2*#mons));
    Zk:=VectorSpace(Rationals(),k+101);
    h:=hom<Zm -> Zk | [[Coefficient(Evaluate(mons[i],[x,y])*qE3,j) : j in [-100..k]] : i in [1..m]] cat [[Coefficient(Evaluate(-mons[i],[x,y]),j) : j in [-100..k]] : i in [1..m]]>;
    K:=Kernel(h);
    for v in Basis(K) do
        //We discount solutions where p(x,y)=0 or q(x,y)=0, as they just equations on Y
        if not &and[Eltseq(v)[j] eq 0 : j in [1..#mons]] and not &and[Eltseq(v)[j+#mons] eq 0 : j in [1..#mons]] then
            vseq:=Eltseq(v);
            tf:=true;
        end if; 
    end for;
end while;
theeqn:=Evaluate(&+[vseq[i+#mons]*mons[i] : i in [1..#mons]],[xx,yy])/Evaluate(&+[vseq[i]*mons[i] : i in [1..#mons]],[xx,yy]);
thefn:=ProjectiveFunction(theeqn);
themap:=map<Y->Z | [Numerator(thefn),Denominator(thefn)]>;

deg:=Degree(themap);
dN:=Integers()!((1/2)*(N^3)*&*[Rationals() | 1-1/p^2 : p in PrimeDivisors(N)]);
dn:=Integers()!((1/2)*(n^3)*&*[Rationals() | 1-1/p^2 : p in PrimeDivisors(n)]);
deg2:=Integers()!(dN/(2*dn));
//qE3 defines a function on Y of degree equal to the degree of Y->Z.
//theeqn defines such a function of degree deg.
//Then if unequal, the degree of the difference is at most deg+Degree(qE3).
assert prec-100 ge deg2+deg; //This proves that the equation for the map holds.
return themap;
end function;

//This function computes the map from X-->Z=P^1 when X is non-hyperelliptic.
//Here X is assumed to be given as canonical model, and qexps[i]
//is the q-expansion corresponding to the ith variable.
//hauptmodul is the q-exp of a Hauptmodul on Z=P^1, and dd=degree(X-->Z).
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
		//assert #nds eq 1;
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

