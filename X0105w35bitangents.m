//In this file, we compute the bitangents of X_0(105)/w35, and use this
//to compute the mod 2 Galois representations explicitly.
//This uses code of Ozman and Siksek for the latter.

X:=ModularCurveQuotient(105,[35]);
assert Genus(X) eq 3;
assert #DefiningEquations(X) eq 1;
eqn:=DefiningEquations(X)[1];
assert Degree(eqn) eq 4; //X is indeed given as a plane quartic

//We now compute the bitangents. The EliminationIdeal method from Ozman and Siskek is too computationally expensive here.
//Instead, we first choose a chart (y=1), and we substitute a generic line z+beta*x+gamma=0. 
//The values of beta,gamma for which the result is the square of a quadratic polynomial, correspond to the bitangents.
//One property of the square of a quadratic polynomial is that the GCD with its derivative has degree 2.
//So the Euclidean algorithm is a cheap way of computing the bitangents.

P<beta,gam>:=PolynomialRing(Rationals(),2);
L:=FieldOfFractions(P);
R<x>:=PolynomialRing(L);
f:=R!Evaluate(eqn,[x,1,-beta*x-gam]);  
f1 := f; f2 := Derivative(f); f3 := f1 mod f2; // f3 generically has degree 2
// We want f3 to divide f1 and f2, so set coefficients of f1 mod f3 and f2 mod f3 equal to zero
cfs1:=Coefficients(f1 mod f3); cfs2:=Coefficients(f2 mod f3);
nums:=[Numerator(c) : c in cfs1 cat cfs2];
A<u,v>:=AffineSpace(Rationals(),2);
XX6:=Scheme(A,nums);
assert Dimension(XX6) eq 0;
QQ<t>:=PolynomialRing(Rationals());
K5:=NumberField(t^2-5);
Km3:=NumberField(t^2+3);
Km7:=NumberField(t^2+7);
K:=Compositum(K5,Km3);
K:=Compositum(K,Km7); // L = Q (sqrt(5), sqrt(-3), sqrt(-7))
pts6:=RationalPoints(XX6,K);

//We check which of the solutions actually correspond to bitangents.
pts:=[];
cfs:=Coefficients(f); mons:=Monomials(f);
for P in pts6 do
    PP<x>:=PolynomialRing(K);
    mons:=[PP!m : m in mons];
    ff:=&+[Evaluate(cfs[i],Eltseq(P))*Evaluate(mons[i],PP.1) : i in [1..#mons]];  
    ff:=ff/LeadingCoefficient(ff);
    if IsSquare(ff) then Append(~pts,P); 
    end if;
end for;
assert #pts eq 27;
//There is in fact one more bitangent; we didn't find it because it's not on our chart.
g:=Evaluate(eqn,[1,1,x]); //This is the one.
assert IsSquare(g/LeadingCoefficient(g)); 

//We turn the pairs (beta,gamma) into actual bitangent lines.
XK:=ChangeRing(X,K);
AmbXK<xx,yy,zz>:=CoordinateRing(AmbientSpace(XK));
L:={};
for pt in pts do
	E:=Eltseq(pt);
	beta,gam:=Explode(E);
	L:=L join {ideal<AmbXK | beta*xx+gam*yy+zz>};
end for;
L:=L join {ideal<AmbXK | xx-yy>}; //The extra bitangent corr to g
L:=SetToSequence(L);
assert #L eq 28;

//The code below is the code of Ozman and Siksek for computing the representation Gal(Qbar/Q) --> J[2] using the bitangents.
//This takes a while to run for our curve.
//Below their code, we also display the code written by the anonymous referee, which does the same computation much faster.

LD:=[ &+[(d[2] div 2)*d[1] : d in Decomposition(Divisor(XK,l))] : l in L];
w:=CanonicalDivisor(XK);
S:=Subsets({1..#L},4);
cnt:=0;
Sigma:=[];
for s in S do
	cnt:=cnt+1;
    if cnt mod 500 eq 0 then cnt; end if;
	tf:=IsPrincipal(&+[LD[i] : i in s]-2*w);
	if tf then
		Append(~Sigma,s);
	end if;
end for;

assert #Sigma eq 315; // This is the set \Sigma in the notation
// of BPS.


// Next we need the group Sp_6(\F_2),
// which get from the "Atlas of finite
// group representations".

/*
www-ATLAS of Group Representations.
S6(2) represented as 6 x 6 matrices over GF(2).
*/

F:=GF(2);

x:=CambridgeMatrix(1,F,6,[
"010000",
"100000",
"111000",
"110100",
"000010",
"110001"]);

y:=CambridgeMatrix(1,F,6,[
"001000",
"011000",
"000100",
"000010",
"000001",
"111010"]);

G<x,y>:=MatrixGroup<6,F|x,y>;
print "Group G is S6(2) < GL(6,GF(2))"; //Sp_6(F_2)

gf:=Graph< {1..315} | {{s,t} : s,t in {1..315} | s gt t and #(Sigma[s] meet Sigma[t]) ge 1} >; // The graph mentioned in the paper.

A,V:=AutomorphismGroup(gf);

tf,mu:=IsIsomorphic(A,G);

assert tf; 

auts:=Automorphisms(K);
rt5:=Roots(t^2-5,K)[1,1];
rtm3:=Roots(t^2+3,K)[1,1];
rtm7:=Roots(t^2+7,K)[1,1];

tau1:=[a : a in auts | rt5@a eq -rt5 and rtm3@a eq rtm3 and rtm7@a eq rtm7][1];
tau2:=[a : a in auts | rt5@a eq rt5 and rtm3@a eq -rtm3 and rtm7@a eq rtm7][1];
tau3:=[a : a in auts | rt5@a eq rt5 and rtm3@a eq rtm3 and rtm7@a eq -rtm7][1];

action:=function(I,tau);
	B:=Basis(I);
	assert #B eq 1;
	return ideal<AmbXK | &+[(MonomialCoefficient(B[1],m)@tau)*m : m in [xx,yy,zz]] >;
end function;

imgL:=function(i,tau); // Galois action on the i-th line.
	N:=[j : j in [1..28] | action(L[i],tau) eq L[j]];
	assert #N eq 1;
	return N[1];
end function;

S28:=SymmetricGroup(28);
imgS28:=function(tau); // tau as a permutation of the 28 lines
	return S28![imgL(i,tau) : i in [1..28]];
end function;

eps1:=imgS28(tau1);
eps2:=imgS28(tau2);
eps3:=imgS28(tau3);

imgQ:=function(i,eps);
	N:=[j : j in [1..315] | Sigma[i]^eps eq Sigma[j]];
	assert #N eq 1;
	return N[1];
end function;

imgA:=function(eps);
	return A![imgQ(i,eps) : i in [1..315]];	
end function;

mat1:=imgA(eps1)@mu; // The three matrices M_1, M_2, M_3
mat2:=imgA(eps2)@mu; // in the notation of the paper.
mat3:=imgA(eps3)@mu;

print mat1, mat2, mat3;

V1:=Eigenspace(mat1,F!1);
V2:=Eigenspace(mat2,F!1);
V3:=Eigenspace(mat3,F!1);

assert [Dimension(V) : V in [V1,V2,V3]] eq [4,4,4];
assert Dimension((V1 meet V2) meet V3) eq 2; 
//This means that J(Q)[2] is a 2-dimensional F_2-vector space.

//--------Code written by anonymous referee to compute the representation--------
// work mod 79, which is totally split in K and use J(K)_tors >--> J(F)
L:=[[K|1,-1,0]]; // first entry is Galois invariant
for pt in pts do
  beta,gam:=Explode(Eltseq(pt));
  Append(~L, [beta,gam,1]);
end for;
assert #L eq 28;

OK:=Integers(K);
pr:=Decomposition(OK, 79)[1,1];
F,KtoF:=ResidueClassField(pr);
pi:=UniformizingElement(pr);
XF:=ChangeRing(X,F);
CF<xF,yF,zF>:=CoordinateRing(Ambient(XF));
linesF:=[[KtoF(a/pi^n) : a in s] where n := Min([Valuation(a,pr) : a in s]) where s := Eltseq(l) : l in L];
// the "half" contact divisors
divsD:=[&+[ExactQuotient(d[2],2)*d[1]
            : d in Decomposition(Divisor(XF, ideal<CF | l[1]*xF+l[2]*yF+l[3]*zF>))]
          : l in linesF];
// set up map from degree zero part of free abelian group on the bitangents
// to JX(F)
JXF,fromJXF,toJXF := ClassGroup(XF);
A:=FreeAbelianGroup(27);
d0:=divsD[1]; // base-point
h:=hom<A -> JXF | [toJXF(d-d0) : d in divsD[2..28]]>;
// the image should be the full 2-torsion subgroup
JX2:=Image(h);
assert Invariants(JX2) eq [2,2,2,2,2,2];
// now set up Galois action on the 2-torsion
// using the isomorphism with (Z/2Z)^6 provided by h
AutK,AutKset,mAutK:=AutomorphismGroup(K);
AutKgens:=[mAutK(g) : g in OrderedGenerators(AutK)];
// find action on A
inAutA:=[hom<A -> A | [A.(Position(L, [a(c) : c in l])-1) : l in L[2..28]]> : a in AutKgens];
// and induced action on JX2
inAutJ2:=[hom<JX2 -> JX2 | [g @@ h @ a @ h : g in OrderedGenerators(JX2)]> : a in inAutA];
// determine invariants
assert Invariants(&meet[Kernel(hom<JX2 -> JX2 | [a(g)-g : g in OrderedGenerators(JX2)]>) : a in inAutJ2])
        eq [2,2];


print "Done";

