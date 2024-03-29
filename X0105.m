load "usefulfunctions.m";

//------------------X_0(105)-------------------------------------------

X,wmaps:=ModCrvQuot(105,[5],[3,7]); //This is X_0(105)/w_5
w3map:=wmaps[1];
w7map:=wmaps[2];

//We now compute X_0(105) as a double cover of X_0(105)/w5.
//To this end, we compute a canonical model using a basis of cusp forms
//which are all eigenforms for w_5.
//The below code for computing this model is adapted from code of Ozman and Siksek.

C:=CuspForms(105);
assert Dimension(C) eq 13;
w5:=AtkinLehnerOperator(C,5);
remws:=[AtkinLehnerOperator(C,n) : n in [5,105]];
N5:=Nullspace(Matrix(w5-1));
N5c:=Nullspace(Matrix(w5+1));
seqs105:=[[Coordinates(N5c,Basis(N5c)[i]*Matrix(w)) cat [0 : j in [1..Dimension(N5)]]: i in [1..Dimension(N5c)]] cat [[0 : j in [1..Dimension(N5c)]] cat Coordinates(N5,Basis(N5)[i]*Matrix(w)): i in [1..Dimension(N5)]] : w in remws];
//seqs defines the matrices for w5 and w105 on this model for X_0(105). The latter will be useful later on.
assert Dimension(N5) eq 5;
B5:=[&+[(Integers()!(2*Eltseq(Basis(N5)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(N5)]];
B5c:=[&+[(Integers()!(2*Eltseq(Basis(N5c)[i])[j]))*C.j : j in [1..Dimension(C)]] : i in [1..Dimension(N5c)]];
dim:=13;
prec:=500;
N:=105;
L<q>:=LaurentSeriesRing(Rationals(),prec);
R<[x]>:=PolynomialRing(Rationals(),dim);
Bexp:=[L!qExpansion((B5c cat B5)[i],prec) : i in [1..dim]]; //We take a basis of cusp forms containing the cusp forms used to create the canonical model for X_0(105)/w5

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
	X105:=Scheme(ProjectiveSpace(R),I);
	if Dimension(X105) eq 1 then
			X105:=Curve(ProjectiveSpace(R),eqns);
			if Genus(X105) eq dim then
				tf:=true;
			end if;
	end if;
end while;

//X0105 is a canonical model for X_0(105)
f:=9*x[9]^2 - 6*x[9]*x[10] + x[10]^2 + 6*x[10]*x[11] + 21*x[10]*x[12] - 
    12*x[10]*x[13] - 17*x[11]^2 + 19*x[11]*x[12] + 18*x[11]*x[13] + 7*x[12]^2 - 
    18*x[12]*x[13] + 27*x[13]^2;
g:=3*x[1] - x[2] + x[4] + x[5] + x[6] + 7*x[7] - x[8];
assert g^2-f in Ideal(X105); //So f is a square in X_0(105).

//We construct the degree 2 cover defined by g^2=f. 
CR<x1,x2,x3,x4,x5,z>:=PolynomialRing(Rationals(),6);
fff:=Evaluate(f,[0,0,0,0,0,0,0,0,x1,x2,x3,x4,x5]);
defsX:=[Evaluate(eqn,[x1,x2,x3,x4,x5]) : eqn in DefiningEquations(X)];
XX105:=Curve(Scheme(ProjectiveSpace(CR),[z^2-fff] cat defsX));
assert Genus(XX105) eq 13; //The genus now implies that XX105 = X_0(105).
pi:=map<XX105 -> X | [x1,x2,x3,x4,x5]>; //This is the map X_0(105) --> X_0(105)/w_5.


//-----------------E_7, E_21 and C-------------------------------------------

//We create the curves denoted in the paper by E_7, E_21 and C
CC1,mm1:=CurveQuotient(AutomorphismGroup(X,[w7map]));
CC2,mm2:=CurveQuotient(AutomorphismGroup(X,[w3map*w7map]));
mmff1:=(FunctionField(X)!(DefiningEquations(mm1)[1]/DefiningEquations(mm1)[2]));
mmff2:=(FunctionField(X)!(DefiningEquations(mm2)[1]/DefiningEquations(mm2)[2]));
CC,mm:=CurveQuotient(AutomorphismGroup(X,[w3map]));
assert Genus(CC) eq 3;
ptsX:=PointSearch(X,100);
E7,mE1:=EllipticCurve(CC1,mm1(ptsX[1]));  
prE7:=mm1*mE1;
E21,mE2:=EllipticCurve(CC2,mm2(ptsX[1]));
prE21:=mm2*mE2;

//We check that the MW groups are as claimed.
MW1,phi1,tf1,tf2:=MordellWeilGroup(E7);
MW2,phi2,tf3,tf4:=MordellWeilGroup(E21);
assert &and[tf1,tf2,tf3,tf4];
assert IsIsomorphic(MW1,AbelianGroup([4]));
assert IsIsomorphic(MW2,AbelianGroup([3]));


//-------------------X_0(105)/w_5-----------------------------------------

//Next, we compute the MW group of X_0(105)/w_5 
//We first show that the cuspidal subgroup is Z/6Z x Z/24Z by embedding it into J(X)(F_11).
assert #ptsX eq 4; //We only find the cusps.
CQgens:=[Divisor(ptsX[i])-Divisor(ptsX[1]) : i in [2,3,4]]; //Generators for the rational cuspidal subgp
X11:=ChangeRing(X,GF(11));
assert not IsSingular(X11);
J11,phi11,psi11:=JacobianFp(X11); //This is J_X(\F_11)
Z3:=FreeAbelianGroup(3);
hC:=hom<Z3 -> J11 | [psi11(reduce(X,X11,DD)) : DD in CQgens]>; //The isomorphic image of the rational cusp subgp inside J11.
AC:=AbelianGroup([6,24]);
assert IsIsomorphic(Image(hC),AC);
assert Order(hC(7*Z3.1-6*Z3.2)) eq 6;
assert Order(hC(Z3.3)) eq 24;
assert sub<J11 | [hC(7*Z3.1-6*Z3.2),hC(Z3.3)]> eq Image(hC);
divs:=[7*(Place(ptsX[2])-Place(ptsX[1]))-6*(Place(ptsX[3])-Place(ptsX[1])),Place(ptsX[4])-Place(ptsX[1])];

//We compute J_X(\F_p) for p=11 and p=13 to pin down J_X(\Q) up to two factors of Z/2Z.
A11:=AbelianGroup([2,2,60,600]);
A13:=AbelianGroup([2,6,6,3168]);
assert IsIsomorphic(J11,A11);

X13:=ChangeRing(X,GF(13));
assert not IsSingular(X13);
J13,phi13,psi13:=JacobianFp(X13);
assert IsIsomorphic(J13,A13);

assert GCD([600,3168]) eq 24;
//We conclude that J_X(\Q) is isomorphic to Z/6Z x Z/24Z times either one or two factors of Z/2Z.
//So it suffices to show that J_X(Q)[2] is isomorphic to (Z/2/Z)^2.
//We will in fact show that J_X(Q(\sqrt{21}))[2] is isomorphic to (Z/2Z)^3
//and determine J_X(Q)[2] as its Galois invariants.

CCs,simp:=SimplifiedModel(CC); //This is a hyperelliptic genus 3 curve in Weierstrass form.
mmm:=mm*simp;
R<x,y,z>:=CoordinateRing(AmbientSpace(CCs));
I2:=ideal< R | x-2*z>; //We consider the ideal given by x=2.
D2:=Divisor(CCs,I2); //The quadratic place given by x=2.
assert IsSquare(ResidueClassField(Decomposition(D2)[1][1])!(3*5*7)); //The quadratic field is Q(\sqrt{105}).
DD:=Pullback(mmm,D2); //A degree 4 divisor on X.
assert #Decomposition(DD) eq 1; //In fact a degree 4 place
K:=ResidueClassField(Decomposition(DD)[1][1]);
assert IsSquare(K!21) and IsSquare(K!5); //So K=Q(\sqrt{5},\sqrt{21}).
//Now the pushforward of DD to CCs is 2*D2. Over \Q this divisor DD cannot be split up, but over Q(\sqrt{21}) it can.
IDD:=Ideal(DD);

Q21<t>:=QuadraticField(21);
X21:=ChangeRing(X,Q21);
R21<[x]>:=CoordinateRing(AmbientSpace(X21));
IDD21:=ideal<R21 | [Evaluate(a,[x[i] :i in [1..5]]) : a in Basis(IDD)]>; //The base change of IDD to Q21.
DD21:=Divisor(X21,IDD21);
dec21:=Decomposition(DD21);
assert #dec21 eq 2; //DD splits over Q21 into two parts of degree 2.
Deff:=1*dec21[1][1]; //This is the divisor we desire. Its pushforward is 1*D2.
P0:=Divisor(X21!Eltseq(ptsX[1]));
D:=Deff-2*P0;
cuspgens:=[Divisor(X21!Eltseq(ptsX[i])) - P0 : i in [2,3,4]]; //Generators of the rat. cuspidal subgp. basechanged to Q21.
twotors:=3*D-cuspgens[1]-2*cuspgens[2]+cuspgens[3];
assert IsPrincipal(2*twotors); //We have found a two-torsion element in J_X(\Q(\sqrt{21})).
assert not IsPrincipal(3*Deff-3*dec21[2][1]); // Implies that the class [twotors] is not defined over the rationals.
assert IsSquare(GF(17)!21) and IsSquare(GF(47)!21); //17 and 47 split in Q(\sqrt{21}).
//This implies that J_X(\Q(\sqrt{21})) embeds in J_X(\F_17) and J_X(\F_47).

Z4:=FreeAbelianGroup(4);
X17:=ChangeRing(X,GF(17));
assert not IsSingular(X17);
J17,phi17,psi17:=JacobianFp(X17);

//To reduce D mod (a prime above) 17, we reduce DD instead mod 17. This will reduce to a sum of 2 degree 2 places, and we pick one.
//Note that it doesn't matter which one we pick, since the choice corresponds to a choice of prime above 17.
DD17:=reduce(X,X17,DD);
assert #Decomposition(DD17) eq 2;
D17:=Decomposition(DD17)[1][1];
h17:=hom<Z4 -> J17 | [psi17(D17-2*reduce(X,X17,Divisor(ptsX[1])))] cat [psi17(reduce(X,X17,Divisor(ptsX[i])-Divisor(ptsX[1]))) : i in [2,3,4]]>; 
assert IsIsomorphic(Image(h17),AbelianGroup([2,6,24])); //Indeed an extra Z/2Z factor!
assert Order(h17(3*Z4.1-Z4.2-2*Z4.3+Z4.4)) eq 2; //twotors is indeed a non-trivial 2-torsion elt.
//However, J17 still has J17[2] \simeq (Z/2Z)^4. Do we need to find an extra 2-torsion element?
//NO! We can compare with J47 to show that there do not exist isomorphic subgroups A1,A2 of J17 and J47
//respectively containing (Z/2Z)^4 such that the isomorphism A1 -> A2 restricted to  
//to the image of the rational cuspidal subgroup is the map it should be. This uses the algorithm of Ozman and Siksek.

p:=17;
Xp:=ChangeRing(X,GF(17));
P0:=Divisor(ptsX[1]);
divspts:=[Divisor(ptsX[i]) : i in [2,3,4]];
h,Ksub,bas,divsNew:=findGenerators(X,divspts,P0,p); 
homs:=possibleJList(X,divsNew,P0,Ksub,bas,[17,47]);
imgs:=[Codomain(hh) : hh in homs]; //The possibilities for J_X(Q(\sqrt{21})) as abstract group.
for H in imgs do
    m2:=hom<H -> H | [2*H.i : i in [1..#Generators(H)]]>;
    assert #Kernel(m2) lt 9;
end for;
//This shows that the largest possible 2-torsion is (Z/2Z)^3, so indeed J_X(Q(\sqrt{21}))[2] \simeq (Z/2Z)^3.
//Since we checked that the class of twotors is not defined over Q, we conclude that J_X(Q)[2] \simeq (Z/2Z)^2.
//It thus follows that J_X(Q) is equal to the rational cuspidal subgroup.


//-----------------------------Quartic points on X_0(105)/w_5-----------------------------------------

//Next, we determine the set of quartic points that do not map to a quadratic point on E_7 or E_21.

allexcdivs:=[];
nonexcdivs:=[];
bp:=&+[Place(pt) : pt in ptsX];
for a in [-2..3] do
 for b in [-11..12] do
    DD:=a*divs[1]+b*divs[2];
    RR,phi:=RiemannRochSpace(DD+bp);
    if Dimension(RR) gt 1 then
        assert Dimension(RR) eq 2;
        Append(~nonexcdivs,DD);
    elif Dimension(RR) eq 1 then
        DDeff:=(DD + bp+ Divisor(phi(RR.1)));
        Append(~allexcdivs,DDeff);
    end if;
end for;
end for;
excdecs:=[Decomposition(D) : D in allexcdivs];
deg4inds:=[i : i in [1..#allexcdivs] | #excdecs[i] eq 1 and Degree(excdecs[i][1][1]) eq 4];
deg4:=[allexcdivs[i] : i in deg4inds];
deg2dec:=&cat[[d[1] :d  in Ddec] : Ddec in excdecs | #Ddec gt 1 or Ddec[1][2] gt 1];
deg2:=Setseq({D : D in deg2dec | Degree(D) eq 2});
pls4:=[excdecs[i][1][1] : i in deg4inds];

//The degree 2 places come from E_7(Q) or E_21(Q) and thus correspond to Q-curves.
assert &and[&or[Degree(Place(pr(RepresentativePoint(P)))) eq 1 : pr in [prE7,prE21]] : P in deg2];

//We check that no "exceptional" degree 4 place on X_0(105)/w_5 lifts to a degree 4 place on X_0(105).
CR<[y]>:=CoordinateRing(AmbientSpace(X));
ff:=Evaluate(f,[0,0,0,0,0,0,0,0,y[1],y[2],y[3],y[4],y[5]]);
for P in pls4 do
    PP:=Eltseq(RepresentativePoint(P));
    assert not IsSquare(ResidueClassField(P)!Evaluate(ff,PP));
end for;

assert #nonexcdivs eq 6;
//By counting, these must be the classes coming from E_7 and E_21. We doublecheck this anyway.
for DD in nonexcdivs do
    V,phi:=RiemannRochSpace(DD+bp);
    D:=DD+bp+Divisor(phi(V.1));
    fn:=ProjectiveFunction(phi(V.2)/phi(V.1));
    hf:=map<X->ProjectiveSpace(Rationals(),1) | [Numerator(fn),Denominator(fn)]>;
    assert &or[(w*hf eq hf and Pullback(w,D) eq D) : w in [w7map,w7map*w3map]];
end for;
//This shows that all 2-dimensional Riemann-Roch spaces have basis 1, f where f factors via one of the two elliptic curves.



//----------------Quadratic points on X_0(105)/w35, X_0(105)/<w7,w105> and X_0(105)/<w7,w21>---------------

//We need to find the quadratic points on X_0(105)/w_35 (genus 3 non-hyp), X_0(105)/w_7,w_105 and X_0(105)/w_7,w21 (both genus 3 hyp).
//For the first of these it is hard to determine the MW group. In a separate file we use the bitangents to show that its 2-torsion is Z/2 x Z/2.

X35,wmaps:=ModCrvQuot(105,[35],[3,5]); //This is X_0(35), and wmaps=[w3,w5]
Xstar,proj35star:=CurveQuotient(AutomorphismGroup(X35,wmaps));

//The below function computes a list of mod p MW groups
MWgpmodp:=function(X,primes)
Z:=FreeAbelianGroup(1);
mwgps:=[];
for p in primes do
    Xp:=ChangeRing(X,GF(p));
    assert not IsSingular(Xp);
    Jp,phip,psip:=JacobianFp(Xp); //The MW group J_X(Fp).
    Append(~mwgps,Jp);
end for;
    return mwgps;
end function;

CQ,hC,ptsX:=RatPtsSubgp(X35,13);
assert IsIsomorphic(CQ,AbelianGroup([4,8]));
mwgps35:=MWgpmodp(X35,[11,29,107]);
assert IsIsomorphic(mwgps35[1],AbelianGroup([2,2,4,96]));
assert IsIsomorphic(mwgps35[2],AbelianGroup([4,8,32,32]));
assert IsIsomorphic(mwgps35[3],AbelianGroup([2,4,120,1560]));
//Since gcd(32,96,1560)=8, this shows that the MW gp must be one of Z/4 x Z/8, Z/2 x Z/4 x Z/8, Z/2 x Z/2 x Z/4 x Z/8.
//By our bitangent computation (different file), we conclude that the MWgp is CQ = Z/4 x Z/8, generated by the differences of rational points.

Zk:=Domain(hC);
assert sub<CQ | hC(Zk.1),hC(Zk.2)> eq CQ;
assert Order(hC(Zk.1)) eq 8;
assert Order(hC(Zk.1+Zk.2)) eq 4;
//This shows that CQ is generated by ptsX[2]+ptsX[3]-2*ptsX[1] and ptsX[2]-ptsX[1], with orders 4 and 8 respectively.
ptsX:=PointSearch(X35,500);
MWgp:=[a*(Divisor(ptsX[2])+Divisor(ptsX[3])-2*Divisor(ptsX[1]))+b*(Divisor(ptsX[3])-Divisor(ptsX[1])) : a in [0..3], b in [0..7]]; 

//We determine the quadratic points on X35
quaddivs:=AbelJacobiInverse(MWgp,2*Divisor(ptsX[1]));
quadpts:=Set([Decomposition(D)[1][1] : D in quaddivs | Degree(Decomposition(D)[1][1]) eq 2]);
assert #quadpts eq 4;
assert &and[Degree(Place(proj35star(RepresentativePoint(P)))) eq 1 : P in quadpts];
//This shows that all points map to a rational point in X_0(105)* so correspond to Q-curves.

//Next, we consider the hyperelliptic curves.
X7,ws:=ModCrvQuot(105,[7],[3,21,105]); //X_0(105)/w7
X73,pi3:=CurveQuotient(AutomorphismGroup(X7,[ws[1]])); //X_0(105)/w7,w3
X21,wss:=ModCrvQuot(105,[21],[7,5]);
X105,wsss:=ModCrvQuot(105,[105],[7]);
X721,pi21:=CurveQuotient(AutomorphismGroup(X7,[ws[2]])); //X_0(105)/w7,w21
X217,pi7:=CurveQuotient(AutomorphismGroup(X21,[wss[1]])); //X_0(105)/w21,w7
X1057,pii7:=CurveQuotient(AutomorphismGroup(X105,[wsss[1]])); //X_0(105)/w7,w105
Z721,m:=SimplifiedModel(X721);
tf,X721,mm:=HasOddDegreeModel(Z721); assert tf;
pi21:=pi21*m*mm;
Z217,m:=SimplifiedModel(X217);
tf,X217,mm:=HasOddDegreeModel(Z217); assert tf;
pi7:=pi7*m*mm;
Z1057,m:=SimplifiedModel(X1057);
tf,X1057,mm:=HasOddDegreeModel(Z1057); assert tf;
pii7:=pii7*m*mm; //We choose odd degree Weierstrass models for all three hyperelliptic curves.

//Remaining Atkin--Lehner involution = Hyperelliptic involution
assert #AutomorphismGroup(X721) eq 2;
assert #AutomorphismGroup(X1057) eq 2;

//We start with X217.
CQ,hC:=RatPtsSubgp(X217,11);
assert IsIsomorphic(CQ,AbelianGroup([32]));
assert Order(hC(Domain(hC).1)) eq 32; //Generated by ptsX217[2]-ptsX217[1];
mwgps:=MWgpmodp(X721,[13,31,43]);
assert &and[IsIsomorphic(mwgps[1],AbelianGroup([16,128])),IsIsomorphic(mwgps[2],AbelianGroup([2,16,32,32])),IsIsomorphic(mwgps[3],AbelianGroup([2,2,2,7520]))];
//This shows that J_X217(Q) is either Z/2 x Z/32 or Z/32.
J217:=Jacobian(X217);
tt,phi:=TwoTorsionSubgroup(J217);
assert #tt eq 4; //So it's Z/2 x Z/32. We now determine the Z/2Z generator as a difference of divisors.
ptsX217:=Points(X217 : Bound:=200);
D1:=Divisor(ptsX217[2])-Divisor(ptsX217[1]);
assert 16*(J217!D1) eq phi(tt.1); //So phi(tt.2) is the other generator.

//From the description of phi(tt.2), we can read off the corresponding divisor
CR<xx,yy,zz>:=CoordinateRing(AmbientSpace(X217));
I:=ideal<CR | yy*zz, xx^2+xx*zz-zz^2>;
D2:=Divisor(X217,I)-2*Divisor(ptsX217[1]);
assert J217!D2 eq phi(tt.2);
MWgp:=[a*D1+b*D2 : a in [0..31], b in [0..1] | not [a,b] eq [0,0]];
//We exclude the zero class since that corresponds to rational points on X_0(105)^* --> Q-curves
assert #AutomorphismGroup(X217) eq 2; //Check that the hyperelliptic involution and the remaining A--L involution are equivalent.
//We now determine the quadratic points that are not the pullback from a rational point on X_0(105)^*
quaddivs:=AbelJacobiInverse(MWgp,2*Divisor(ptsX217[1]));
quadpts:=Set([Decomposition(D)[1][1] : D in quaddivs | Degree(Decomposition(D)[1][1]) eq 2]);

//Note that X721 is the same curve as X217, but we computed it separately to have the map from X_0(105)/w7 towards it as well.
//In fact, the models for X721 and X217 that we have chosen are the same, so after relating them, we also have the degree 2 divisors on X721.
tf,isom:=IsIsomorphic(X721,X217); //Funny: the isomorphism Magma chooses between identical models is the hyperelliptic involution
assert tf;
pi21:=pi21*isom; 

//We pull these quadratic points back to X_0(105)/w_{21} and X_0(105)/w_7
quadptspb7:=[];
quadptspb21:=[];
quadpts721:=[];
for D in quadpts do
    dec7:=Decomposition(Pullback(pi7,D));
    dec21:=Decomposition(Pullback(pi21,D));
    for d in dec7 do
        if Degree(d[1]) eq 2 then Append(~quadptspb7,d[1]); 
        Append(~quadpts721,D);
        end if;
    end for;
    for d in dec21 do
       if Degree(d[1]) eq 2 then Append(~quadptspb21,d[1]); 
        end if;
    end for; 
end for;
assert #Set(quadptspb7) eq 2;
assert #Set(quadptspb21) eq 0;
assert &and[IsIsomorphic(ResidueClassField(P),QuadraticField(5)) : P in Set(quadptspb7)];
//We find two quadratic points on X_0(105)/w_{21} that do not map to a rational pt on X_0(105)*, and both are defined over Q(rt5).

//We investigate these two (pairs of) quadratic points further.
//Computing the j-invariant map on X_0(105) is too computationally expensive, so we try something else.
w5:=wss[2];
assert &and[w5(RepresentativePoint(P)) eq RepresentativePoint(P) : P in Set(quadptspb7)];
//The quadratic points are fixed by w5 on X_0(105)/w_{21}, so each quartic point on X_0(105) mapping to one of these points is fixed by either w_5 or w_105.
//If fixed by w_5, then also their image in X_0(5) is fixed by w_5. 
X5:=SmallModularCurve(5);
j5:=jInvariant(X5,5);
w5:=AtkinLehnerInvolution(X5,5,5);
CR<[x]>:=CoordinateRing(AmbientSpace(X5)); 
I:=ideal<CR | [x[1]*DefiningEquations(w5)[2]-x[2]*DefiningEquations(w5)[1]]>;
fixedw5div:=Divisor(X5,I);
assert #Decomposition(fixedw5div) eq 1;
fixedpl:=Decomposition(fixedw5div)[1][1];
assert w5(RepresentativePoint(fixedpl)) eq RepresentativePoint(fixedpl);
tf,isom:=IsIsomorphic(ResidueClassField(fixedpl),QuadraticField(5));
assert tf; //Indeed defined over Q(rt5), but quadratic!
rt5:=QuadraticField(5).1;
assert Coefficients(MinimalPolynomial(isom(Evaluate(j5,RepresentativePoint(fixedpl))))) eq Coefficients(MinimalPolynomial(282880*rt5 + 632000));

//If fixed by w_{105}, then we compute an equation it must satisfy on our canonical model for X_0(105). Recall that seqs105[2] is a matrix for w_105.
assert Eltseq(Basis(Kernel(Matrix(seqs105[2])-1))[5]) eq [0,0,0,0,0,0,0,0,1,0,-2,-2,-1];
//It is too computationally expensive to compute divisors on X_0(105) fixed by w_105, but we notice that the equation x[9]-2x[11]-2x[12]-x[13] holds true on X_0(105). This is an equation between coordinates coming from X_0(105)/w_5.
CR<[y]>:=CoordinateRing(AmbientSpace(X));
I:=ideal<CoordinateRing(AmbientSpace(X)) | y[1]-2*y[3]-2*y[4]-y[5]>;
fixeddiv:=Divisor(X,I);
assert #Decomposition(fixeddiv) eq 2;
assert &and[Degree(d[1]) eq 4 : d in Decomposition(fixeddiv)];
assert &and[not IsSquare(ResidueClassField(d[1])!Evaluate(ff,Eltseq(RepresentativePoint(d[1])))) : d in Decomposition(fixeddiv)];
//This means that the places fixed by w_{105} on X_0(105) have degree 8. 

//Next up is X1057.
CQ,hC:=RatPtsSubgp(X1057,11);
assert IsIsomorphic(CQ,AbelianGroup([16]));
assert Order(hC(Domain(hC).1)) eq 16; //Generated by ptsX1057[2]-ptsX1057[1].
mwgps1057:=MWgpmodp(X1057,[11,17,79]); 
assert &and[IsIsomorphic(mwgps1057[1],AbelianGroup([2,2,256])), IsIsomorphic(mwgps1057[2],AbelianGroup([4,2496])), IsIsomorphic(mwgps1057[3],AbelianGroup([2,2,16,10704]))]; //These show that the MWgp is either Z/2 x Z/16 or Z/16 (note that 10704/16 is odd).
J1057:=Jacobian(X1057);
tt,phi:=TwoTorsionSubgroup(J1057);
assert #tt eq 4; //So it's Z/2 x Z/16. We now determine the Z/2Z generator as a difference of divisors.
ptsX1057:=Points(X1057 : Bound:=200);
D1:=Divisor(ptsX1057[2])-Divisor(ptsX1057[1]);
assert 8*(J1057!D1) eq phi(tt.2); //So phi(tt.1) is the other generator.
CR<xx,yy,zz>:=CoordinateRing(AmbientSpace(X1057));
I:=ideal<CR | yy*zz, xx^2-5/7*xx*zz+1/7*zz^2>;
D2:=Divisor(X1057,I)-2*Divisor(ptsX1057[1]);
assert J1057!D2 eq phi(tt.1);
MWgp:=[a*D1+b*D2 : a in [0..7], b in [0..1] | not [a,b] eq [0,0]]; //We exclude the zero class since that corresponds to rational points on X_0(105)^* --> Q-curves
assert #AutomorphismGroup(X1057) eq 2; //Indeed, the hyperlliptic involution and the remaining A--L involution are equivalent.
quaddivs:=AbelJacobiInverse(MWgp,2*Divisor(ptsX1057[1]));
quadpts:=Set([Decomposition(D)[1][1] : D in quaddivs | Degree(Decomposition(D)[1][1]) eq 2]);
for D in quadpts do
    dec:=Decomposition(Pullback(pii7,D));
    for d in dec do
    assert Degree(d[1]) eq 4;
    end for;
end for;
//This shows that X_0(105)/w105 has no quadratic points that do not come from a rational point on X_0(105)^*

//Finally, note that we have already studyied the quadratic points on X_0(105), but we doublecheck them anyway.
alldivs:=[a*divs[1]+b*divs[2] : a in [-2..3], b in [-11..12]];
quaddivs:=AbelJacobiInverse(alldivs,2*Place(PointSearch(X,200)[1]));
quadpts:=Set([Decomposition(D)[1][1] : D in quaddivs | Degree(Decomposition(D)[1][1]) eq 2]);
//The degree 2 places come from E_7(Q) or E_21(Q) and thus correspond to Q-curves.
assert &and[&or[Degree(Place(pr(RepresentativePoint(P)))) eq 1 : pr in [prE7,prE21]] : P in quadpts];

print "Done";
