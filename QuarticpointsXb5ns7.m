load "ozmansiksek2.m";
load "QuarticsieveXb5ns7.m";
load "Xb5ns7.m";

X:=Codomain(Xb5ns7toX);
CR<u,v,w>:=CoordinateRing(AmbientSpace(X));
w5:=iso<X->X | [-u,-v,w],[-u,-v,w]>;


Cprime,projCprime:=CurveQuotient(AutomorphismGroup(X,[w5]));
C,h:=SimplifiedModel(Cprime);
XtoC:=Expand(projCprime*h);
ptsC:=Setseq(Points(C : Bound:=1000)); //8 points
//We use an algorithm of Stoll to show that J(C)(Q) is generated by deg1C[3]-deg1C[1] and deg1C[5]-deg1C[1], corresponding to D1 and D2 below. bp corresponds to ptsC[1].
J:=Jacobian(C);
assert #TorsionSubgroup(J) eq 1; 
ptsJ:=[pt-ptsC[1] : pt in ptsC]; 
Q1:=ptsJ[3];
Q2:=ptsJ[5];
bas,M:=ReducedBasis([Q1,Q2]);
assert #bas eq 2;//This shows J(C)(\Q) has rank 2;
//We will show that Q1,Q2 are a basis using Stoll's algorithm
N:=Orthogonalize(M);
absbd:=Ceiling(Exp((N[1,1]^2+N[1,2]^2+N[2,1]^2+N[2,2]^2)/4+HeightConstant(J)));
//J(C)(\Q) is generated by P1,P2 and all points of height up to absbd.
PtsUpToAbsBound:=Points(J : Bound:=absbd);
assert ReducedBasis([pt : pt in PtsUpToAbsBound]) eq [-Q2,-Q1-Q2]; //This shows Q1,Q2 are a basis.

d1:=Place(ptsC[3])-Place(ptsC[1]);
d2:=Place(ptsC[5])-Place(ptsC[1]);

print "Searching for degree 4 points on X.";
deg2,pls1,pls2,plsbig:=searchDiv2(X,5,[w5]);
pls2:=pls2 cat [Pullback(XtoC,Place(P)) : P in ptsC];
pls4:=[DD : DD in plsbig | Degree(DD) eq 4];
pls3:=[DD : DD in plsbig | Degree(DD) eq 3];
deg4:=[1*pl1+1*pl2+1*pl3+1*pl4 : pl1 in pls1, pl2 in pls1, pl3 in pls1, pl4 in pls1] cat [1*pl1 + 1*pl2 + 1*pl3 : pl1 in pls1, pl2 in pls1, pl3 in pls2] cat [pls2[i1] + pls2[i2] : i1 in [1..#pls2], i2 in [1..#pls2] | i2 le i1] cat [1*pl1 + 1*pl2 : pl1 in pls1, pl2 in pls3] cat [1*pl : pl in pls4];
deg4npb:=Setseq({DD : DD in deg4 | not Pullback(w5,DD) eq DD}); 

genusC:=2;
auts:=[Matrix([[-1,0,0],[0,-1,0],[0,0,1]])];
n:=Dimension(AmbientSpace(X));

bpideal:=ideal<CoordinateRing(AmbientSpace(X)) | [
    v^2 - 4/5*w^2,
    u - 5/2*v]>;
bp:=Divisor(X,bpideal); //This is the basepoint for our map X^{(2)} --> J.
I1:=ideal<CoordinateRing(AmbientSpace(X)) | [v^2 + 1/11*w^2,u - 2*v]>;
I2:=ideal<CoordinateRing(AmbientSpace(X)) | [v^2 + 1/4*w^2,u]>;
I0:=ideal<CoordinateRing(AmbientSpace(X)) | [
    u^3 - 44/7*u*w^2 + 29/7*v*w^2 - 12/7*w^3,
    u^2*v - 27/14*u*w^2 + 17/14*v*w^2 - 1/2*w^3,
    u*v^2 - 4/7*u*w^2 + 2/7*v*w^2 - 1/7*w^3,
    v^3 - 1/14*u*w^2 - 3/14*v*w^2 - 1/14*w^3,
    u^2*w - 37/14*u*w^2 + 29/14*v*w^2 - 13/14*w^3,
    u*v*w - 11/14*u*w^2 + 9/14*v*w^2 - 5/14*w^3,
    v^2*w - 1/14*u*w^2 - 3/14*v*w^2 - 3/14*w^3]>;
c0:=Divisor(X,I0); //The first degree 3 Galois orbit of cusps.
cinf:=Pullback(w5,c0); //The second degree 3 Galois orbit of cusps.
//assert Place(invTQ(F(L)!c0F)) in [c0,cinf];
Dtor:=c0-cinf;
D1:=Divisor(X,I1)-bp;
D2:=Divisor(X,I2)-bp;
assert D1 eq Pullback(XtoC,d1) and D2 eq Pullback(XtoC,d2);
bp:=2*bp; //Need a degree 4 basepoint from now on.

//The sieve initially didn't terminate, but did point us in the direction of new pairs of degree 4 places.
for D in [3*Dtor+D1-D2,3*Dtor-D1-3*D2,3*Dtor-D1-4*D2] do
    RRsp,phimap:=RiemannRochSpace(D+bp);
    deco:=Decomposition(Divisor(phimap(RRsp.1)));
    extrapls:=[d[1] : d in deco | Degree(d[1]) eq 4][1];
    extrapls2:=Pullback(w5,extrapls);
    Append(~deg4npb,1*extrapls);
    Append(~deg4npb,extrapls2);
end for;
print "The number of non-pullbacks is"; #deg4npb;

divs:=[D1,D2,Dtor];
A:=AbelianGroup([0,0,7]);

//We use p=19 to check that D2 is not a double in J_X(Q)
for p in [19] do
    Xp:=ChangeRing(X,GF(p));
    CC,phi,psi:=ClassGroup(Xp);
    Z:=FreeAbelianGroup(1);
    degr:=hom<CC->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CC)]>;
    JFp:=Kernel(degr); // This is isomorphic to J_X(\F_p).
    divsp:=[reduce(X,Xp,divi) : divi in divs];
    h:=hom<A -> JFp | [JFp!psi(divp) : divp in divsp]>; //The map A--> J_X(\F_p).
    m2:=hom<JFp -> JFp | [2*g : g in OrderedGenerators(JFp)]>;
    assert not h(A.2) in Image(m2);
end for;

B0,iA0:=sub<A | A.1,2*A.2>; //Since D2 is not a double, we end up in B0 x <A.3> after multiplying by I=2.
W0s:={{A.3},{2*A.3},{3*A.3}}; //The option 0*A.3 we have excluded theoretically,
//and the possibilities k*A.3 and -k*A.3 are w5-symmetric, so it suffices to consider A.3, 2*A.3 and 3*A.3.
primes:=[11,13,17,23,53,29,71,43,37,31];
I:=2;

assert &and[MWSieve(X,w5,deg4npb,primes,A,divs,I,bp,B0,iA0,W0) : W0 in W0s];

//Since we have used a singular model X, we should check that the mod p reductions
//correspond to the special fibre of the minimal proper regular model over Zp. 
//Note that the canonical model is a smooth model for X(b5,ns7),
//so if that model has non-singular reduction at p and function fields correspond, we have found *the* reduction.
for p in primes do
    Xb5ns7p:=ChangeRing(Xb5ns7,GF(p));
    assert Dimension(Xb5ns7p) eq 1;
    assert not IsSingular(Xb5ns7p);
    Xp:=ChangeRing(X,GF(p));
    FXb5ns7p:=AlgorithmicFunctionField(FunctionField(Xb5ns7p));
    FXp:=AlgorithmicFunctionField(FunctionField(Xp));
    assert IsIsomorphic(FXb5ns7p,FXp); //If this is true, then Xb5ns7p and Xp are birational and J(Xb5ns7p) = J(Xp)
end for;


//Next, we compute j-invariants of the found degree 4 points. 
//For this, we first need to pull them back to the canonical model. 
//This is problematic in practice because the rational map X(b5,ns7) --> X
//is not defined everywhere. We can work around this.

pls4npb:=[Decomposition(P)[1][1] : P in deg4npb | Decomposition(P)[1][2]*(#Decomposition(P)) eq 1];
assert #pls4npb eq 8; 
deg4pls:=[];
for P in pls4npb do
    Z:=Scheme(X,Ideal(1*P)); 
    Zpb:=Pullback(Xb5ns7toX,Z); //This has ``extra'' irreducible components.
    irs:=IrreducibleComponents(Zpb);
    irs4:=[ir : ir in irs | Degree(ir) eq 4];
    for ir in irs4 do
        D:=Divisor(Xb5ns7,ir);
        assert Degree(D) eq 4;
        Q:=Decomposition(D)[1][1];
        K:=ResidueClassField(Q);
        if P eq Place(X(K)!Eltseq(Xb5ns7toX(RepresentativePoint(Q)))) then
            Append(~deg4pls,Q);
        end if;
     end for;
end for;
assert #deg4pls eq 8;

//We display the j-invariants
for Q in deg4pls do
    print "Information about this isolated quartic point on X(b5,ns7):";
    j:=jns7(Xb5ns7toXns7(RepresentativePoint(Q)));
    L:=ResidueClassField(Q);
    K:=NumberField(MinimalPolynomial(j));
    assert Degree(K) in [1,4]; //So it suffices to work in L.
    LL,psi:=OptimizedRepresentation(L);
    QQ:=X(LL)![psi(a) : a in Eltseq(Xb5ns7toX(RepresentativePoint(Q)))];
    print "The field of the point is ", LL;
    print "The coordinates of the point are ", QQ;
    print "The j-invariant is ", psi(j);
    Ej:=EllipticCurveFromjInvariant(psi(j));
    print "CM? ",HasComplexMultiplication(Ej);
end for;
    
