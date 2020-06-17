//The reduce function below was written by Ekin Ozman and Samir Siksek.
reduce:=function(X,Xp,D);
        if Type(D) eq DivCrvElt then
                decomp:=Decomposition(D);
                return &+[ pr[2]*$$(X,Xp,pr[1]) : pr in decomp]; // Reduce the problem to reducing places.
        end if;
        assert Type(D) eq PlcCrvElt;
        if  Degree(D) eq 1 and not IsHyperelliptic(X) then
                P:=D;
                R<[x]>:=CoordinateRing(AmbientSpace(X));
                m:=Rank(R);
                KX:=FunctionField(X);
                inds:=[i : i in [1..m] | &and[Valuation(KX!(x[j]/x[i]),P) ge 0 : j in [1..m]]];
                assert #inds ne 0;
                i:=inds[1];
                PP:=[Evaluate(KX!(x[j]/x[i]),P) : j in [1..m]];
                denom:=LCM([Denominator(d) : d in PP]);
                PP:=[Integers()!(denom*d) : d in PP];
                g:=GCD(PP);
                PP:=[d div g : d in PP];
                Fp:=BaseRing(Xp);
                PP:=Xp![Fp!d : d in PP];
                return Place(PP);
        end if;
        I:=Ideal(D);
        Fp:=BaseRing(Xp);
        p:=Characteristic(Fp);
        B:=Basis(I) cat DefiningEquations(X);
        m:=Rank(CoordinateRing(X));
        assert Rank(CoordinateRing(Xp)) eq m;
        R:=PolynomialRing(Integers(),m);
        BR:=[];
        for f in B do
                g:=f*p^-(Minimum([Valuation(c,p) : c in Coefficients(f)]));
                g:=g*LCM([Denominator(c) : c in Coefficients(g)]);
                Append(~BR,g);
        end for;
        J:=ideal<R | BR>;
        J:=Saturation(J,R!p);
        BR:=Basis(J);
        Rp:=CoordinateRing(AmbientSpace(Xp));
        assert Rank(Rp) eq m;
        BRp:=[Evaluate(f,[Rp.i : i in [1..m]]) : f in BR];
        Jp:=ideal<Rp| BRp>;
        Dp:=Divisor(Xp,Jp);
        return Dp;
end function;

//The rest of this file was written by Derickx, Najman and Siksek.

PxP<x1,x2,y1,y2>:=ProductProjectiveSpace(Rationals(),[1,1]); // P^1 x P^1
F1:=(x1^2+10*x1*x2+5*x2^2)^3;
F2:=x1*x2^5;


G1:= 64*(y1*(y1^2+7*y2^2)*(y1^2-7*y1*y2+14*y2^2)*(5*y1^2-14*y1*y2-7*y2^2))^3;
G2:=(y1^3-7*y1^2*y2+7*y1*y2^2+7*y2^3)^7;

// XlH is Le Hung's model for X(b5,ns7) as a curve in P^1 x P^1.
XlH:=Curve(PxP,F1*G2-G1*F2);
assert Genus(XlH) eq 6;

// Next we write down the cusps on this model.
Qzet<zet>:=CyclotomicField(7);
L<eta>:=sub<Qzet | 2*(zet^3+zet^-3)+3>;
assert Evaluate(ChangeRing(G2,L),[0,0,eta,1]) eq 0; // (\eta : 1) is a zero of G2.
c0C:=XlH(L)![0,1,eta,1];  // The 0 cusps on XlH are the Galois orbit of this.
cinfC:=XlH(L)![1,0,eta,1]; // The infty cusps on C are the Galois orbit of this. 

// Let's check that difference of the Galois orbit of cusps really gives
// a point of order 7 on the Jacobian.

plsc0C:=Places(c0C);
assert #plsc0C eq 1;
c0:=plsc0C[1]; // The 0 cusps as a place of degree 3.
assert Degree(c0) eq 3;
plscinfC:=Places(cinfC); 
assert #plscinfC eq 1;
cinf:=plscinfC[1];  // The infinity cusps as a place of degree 3.

// We will now use Magma to write down a plane model cut out by
// a single degree 6 equations, which has exactly four nodes
// as its singular locus. We shall call this model F,
// and later change coordinates to obtain a better plane model
// that is denoted by D in the paper.
tf, XlHtoF := Genus6PlaneCurveModel(XlH);
assert tf; 
F := Codomain(XlHtoF); // F is a planar model for C.
assert Genus(F) eq 6;
assert #DefiningEquations(F) eq 1;
assert Degree(DefiningEquations(F)[1]) eq 6;
assert IsProjective(F);
assert Dimension(AmbientSpace(F)) eq 2;
// Thus F is cut out in P^2 by one degree 6 equation.


// We transfer the cusps to F.
def:=DefiningEquations(XlHtoF);
FFC:=FunctionField(XlH);
c0F:=[Evaluate(FFC!(def[1]/def[3]),c0C),Evaluate(FFC!(def[2]/def[3]),c0C),1]; // A representative
                                                                                // of the Galois orbit of cusps at 0 on F.  
cinfF:=[Evaluate(FFC!(def[1]/def[3]),cinfC),Evaluate(FFC!(def[2]/def[3]),cinfC),1]; // A representative
                                                                                // of the Galois orbit of cusps at infinity on F. 

// We now put the coordinates of these cusp representatives in L.
tf,ism:=IsIsomorphic(Universe(c0F),L);
assert tf;
c0F:=[ism(a) : a in c0F];
tf,ism:=IsIsomorphic(Universe(cinfF),L);
assert tf;
cinfF:=[ism(a) : a in cinfF];


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

D := Pullback(TQ,F);  
R<u,v,w>:=CoordinateRing(AmbientSpace(D));
Xb5ns7:=D;
invTQ:=map< F -> D | DefiningEquations(Inverse(TQ))>;
XlHtoXb5ns7:=XlHtoF*invTQ;
