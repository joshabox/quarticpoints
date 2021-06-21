//This file contains code written by Tom Fisher to improve the models for the curves 

//X(b5,e7)/phi_7w_5, X(b5,e7)/w_5 and X(b5,ns7)

//such that the equations are simpler and have good reduction at 2 and 3.



//------X(b5,e7)/phi_7w_5--------------------------------


P4<X0,X1,X2,X3,X4>:=ProjectiveSpace(Rationals(),4);

// Josha's equations (taken from "checks_and_j_map.m")

Xb5e7modphi7w5:=Curve(P4,[448*X0^2 - 9*X1^2 + 9*X2^2 + 54*X2*X3 + 9*X3^2 + 112*X0*X4 + 126*X1*X4 + 7*X4^2, 16*X0*X1 - 3*X1^2 + 3*X2^2 + 6*X2*X3 + 3*X3^2 + 2*X1*X4 + 21*X4^2, 3*X1*X2 + 28*X0*X3 + 12*X1*X3 + 21*X2*X4 + 14*X3*X4]);

// The new equations

// version with smaller coefficients
Xb5e7modphi7w5_neweqns1 := [
    X0*X2 - X1*X2 - X0*X3 + X1*X3 - X3^2 + X0*X4 - X1*X4 - X3*X4 - 2*X4^2,
    X0^2 + X0*X1 + X0*X2 + X1*X3 - 2*X3^2 - X0*X4 + 2*X1*X4 - 2*X2*X4 + 3*X3*X4,
    X1^2 - X0*X2 - X2^2 - 2*X1*X3 - 2*X2*X3 + 2*X0*X4 + 2*X1*X4 - 2*X2*X4 + X3*X4
];

// version with fewer monomials
Xb5e7modphi7w5_neweqns2 := [
    X0^2 + X0*X2 - X2^2 - X1*X3 - X2*X3 + 7*X2*X4 - 14*X4^2,
    X0*X1 + X1*X2 - 2*X1*X3 + X3^2 - 7*X1*X4 + 7*X3*X4 + 14*X4^2,
    X0^2 + X1^2 + 3*X1*X2 - 2*X1*X3 - X2*X3 - X3^2 - 7*X1*X4 + 7*X4^2
];

// The changes of coordinates used

M1 := Matrix(Rationals(),5,5,[
    [ 0, 0, 0, 1, -1 ],
    [ 2, -2, 2, 1, 0 ],
    [ -4, 0, 0, -2, 0 ],
    [ 2, 2, 2, 0, 2 ],
    [ 0, 0, 0, 1, 2 ]
]);
assert Determinant(M1) eq 2^5*3;
// See below for output showing this change of coordinates
// gives good reduction at p = 2,3.

M2 := Matrix(Rationals(),5,5,[
    [ 0, -1, -1, 0, 2 ],
    [ 0, 0, -1, 0, 2 ],
    [ 1, 0, 1, -1, -5 ],
    [ 0, 0, 0, 1, 3 ],
    [ 0, 0, 0, 0, 1 ]
]);
assert Determinant(M2) eq 1;

quads0 := Equations(Xb5e7modphi7w5);
quads1 := Xb5e7modphi7w5_neweqns1;
quads2 := Xb5e7modphi7w5_neweqns2;
assert Ideal([q^M1 : q in quads0]) eq Ideal(quads1);
assert Ideal([q^M2 : q in quads1]) eq Ideal(quads2);

// The involution w5 = phi7 on the old and new models

D0 := DiagonalMatrix(Rationals(),[1,1,-1,-1,1]);
assert Ideal([q^D0: q in quads0]) eq Ideal(quads0);

D1 := M1^(-1)*D0*M1;
assert Ideal([q^D1: q in quads1]) eq Ideal(quads1);
// no longer diagonal, but this is inevitable if we want
// good reduction at p = 2

D2 := M2^(-1)*D1*M2;
assert Ideal([q^D2: q in quads2]) eq Ideal(quads2);

// Computing a better basis for the original space of quadrics

MD := MonomialsOfDegree;
MC := MonomialCoefficient;
mons := MD(CoordinateRing(P4),2);
mat := Matrix(#quads0,#mons,[MC(q,mon): mon in mons,q in quads0]);
mat := LLL(Matrix(Basis(PureLattice(Lattice(mat)))));
quads0 := [&+[mat[i,j]*mons[j]: j in [1..#mons]]: i in [1..Nrows(mat)]];

// Looking at the reductions mod p of the old and new models

print "";
for ctr in [1,2] do
  if ctr eq 1 then print "Old equations"; qq := quads0; end if;
  if ctr eq 2 then print "New equations"; qq := quads1; end if;
  pp := [p : p in [2..20] | IsPrime(p)];
  for p in pp do
    printf "p = %o : ",p;
    Rp<[x]> := PolynomialRing(GF(p),5);
    Cp := Scheme(Proj(Rp),[Rp!q : q in qq]);
    XX := IrreducibleComponents(Cp);
    printf "dims = %o  degs = %o  red_degs = %o  sing = %o \n",
      [Dimension(X): X in XX],
      [Degree(X): X in XX],
      [Degree(ReducedSubscheme(X)): X in XX],
      [IsSingular(X): X in XX];
  end for;
  print "";
end for;

/*

Old equations
p = 2 : dims = [ 2, 1 ]  degs = [ 2, 4 ]  red_degs = [ 1, 1 ]  sing = [ true, true ] 
p = 3 : dims = [ 3, 1 ]  degs = [ 1, 2 ]  red_degs = [ 1, 1 ]  sing = [ false, true ] 
p = 5 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ true ] 
p = 7 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 1 ]  sing = [ true ] 
p = 11 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 
p = 13 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 
p = 17 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 
p = 19 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 

New equations
p = 2 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 
p = 3 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 
p = 5 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ true ] 
p = 7 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 1 ]  sing = [ true ] 
p = 11 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 
p = 13 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 
p = 17 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 
p = 19 : dims = [ 1 ]  degs = [ 8 ]  red_degs = [ 8 ]  sing = [ false ] 

*/



//--------------X(b5,e7)/w_5------------------------------------


P7<X0,X1,X2,X3,X4,X5,X6,X7>:=ProjectiveSpace(Rationals(),7);

// Josha's equations (taken from "checks_and_j_map.m")

Xb5e7modw5:=Curve(P7,[3528*X0^2 + 177*X4*X5 + 597*X5^2 - 2716*X0*X6 - 423*X1*X6 - 6365*X2*X6 - 1918*X3*X6 - 13454*X6^2 + 2842*X0*X7 + 626*X1*X7 + 9144*X2*X7 + 3010*X3*X7 + 35252*X6*X7 - 22960*X7^2, 56*X0*X1 - 135*X4*X5 - 327*X5^2 - 140*X0*X6 - 37*X1*X6 + 2381*X2*X6 + 1890*X3*X6 + 2982*X6^2 + 910*X0*X7 + 16*X1*X7 - 3270*X2*X7 - 2758*X3*X7 - 7476*X6*X7 + 4816*X7^2, 56*X1^2 + 1215*X4*X5 + 2835*X5^2 + 11340*X0*X6 - 715*X1*X6 - 22389*X2*X6 - 12726*X3*X6 - 38290*X6^2 - 19530*X0*X7 + 820*X1*X7 + 30894*X2*X7 + 21546*X3*X7 + 99764*X6*X7 - 64624*X7^2, 168*X0*X2 - 15*X4*X5 - 3*X5^2 - 56*X0*X6 - 45*X1*X6 + 89*X2*X6 + 238*X3*X6 - 238*X6^2 + 182*X0*X7 + 52*X1*X7 - 138*X2*X7 - 406*X3*X7 + 532*X6*X7 - 224*X7^2, 56*X1*X2 - 171*X4*X5 - 315*X5^2 + 168*X0*X6 - 253*X1*X6 + 2713*X2*X6 + 2562*X3*X6 + 2086*X6^2 + 1050*X0*X7 + 260*X1*X7 - 3910*X2*X7 - 3738*X3*X7 - 5292*X6*X7 + 3584*X7^2, 56*X2^2 + 87*X4*X5 + 147*X5^2 - 364*X0*X6 + 141*X1*X6 - 1285*X2*X6 - 1582*X3*X6 - 714*X6^2 - 266*X0*X7 - 148*X1*X7 + 1894*X2*X7 + 2170*X3*X7 + 1764*X6*X7 - 1232*X7^2, 1764*X0*X3 - 579*X4*X5 - 1050*X5^2 + 1505*X0*X6 - 774*X1*X6 + 7009*X2*X6 + 6083*X3*X6 + 7021*X6^2 + 1456*X0*X7 + 851*X1*X7 - 9837*X2*X7 - 8582*X3*X7 - 15778*X6*X7 + 9044*X7^2, 28*X1*X3 + 9*X4*X5 + 6*X5^2 + 357*X0*X6 - X1*X6 + 74*X2*X6 + 161*X3*X6 - 63*X6^2 - 364*X0*X7 - 20*X1*X7 - 144*X2*X7 - 168*X3*X7 + 210*X6*X7 - 140*X7^2, 84*X2*X3 - 15*X4*X5 - 30*X5^2 - 35*X0*X6 - 27*X1*X6 + 80*X2*X6 + 133*X3*X6 + 329*X6^2 + 140*X0*X7 + 34*X1*X7 - 66*X2*X7 - 196*X3*X7 - 854*X6*X7 + 532*X7^2, 252*X3^2 + 12*X4*X5 - 30*X5^2 + 70*X0*X6 + 45*X1*X6 + 443*X2*X6 + 28*X3*X6 + 350*X6^2 - 196*X0*X7 - 59*X1*X7 - 639*X2*X7 + 14*X3*X7 - 728*X6*X7 + 280*X7^2, 18*X0*X4 - 19*X0*X5 - 12*X1*X5 - 27*X2*X5 + 17*X3*X5 - 120*X4*X6 - 66*X5*X6 + 114*X4*X7 + 54*X5*X7, 2*X1*X4 - 21*X0*X5 + 8*X1*X5 + 7*X2*X5 - 21*X3*X5 + 28*X4*X6 + 56*X5*X6 - 28*X4*X7 - 84*X5*X7, 6*X2*X4 + 7*X0*X5 + 3*X2*X5 + 7*X3*X5, 9*X3*X4 - 28*X0*X5 - 3*X1*X5 - 9*X2*X5 + 8*X3*X5 - 39*X4*X6 - 30*X5*X6 + 33*X4*X7 + 27*X5*X7, 63*X4^2 + 426*X4*X5 + 690*X5^2 + 1120*X0*X6 + 207*X1*X6 - 4405*X2*X6 - 2702*X3*X6 - 7000*X6^2 - 2464*X0*X7 - 263*X1*X7 + 6057*X2*X7 + 4298*X3*X7 + 18172*X6*X7 - 11984*X7^2]);

// The new equations

Xb5e7modw5_neweqns := [ X1*X2 - X0*X3, X1*X4 - X0*X5, X1*X6 - X0*X7,
  X3*X4 - X2*X5, X5*X6 - X4*X7, X3*X6 - X2*X7, 13*X2*X3 - 5*X3^2 -
  12*X3*X4 + 4*X4*X5 - X2*X7 - 4*X3*X7 + 2*X5*X7, 13*X2^2 - 5*X2*X3 -
  12*X2*X4 + 4*X4^2 - X2*X6 + 2*X5*X6 - 4*X2*X7, 5*X2*X6 - X6^2 +
  13*X2*X7 - 6*X3*X7 - 10*X4*X7 - 2*X5*X7 - 2*X6*X7 - 4*X7^2, 5*X2*X4
  + 13*X2*X5 - 6*X3*X5 - 10*X4*X5 - 2*X5^2 - X4*X6 - 2*X4*X7 -
  4*X5*X7, 5*X0*X2 + 13*X0*X3 - 6*X1*X3 - 10*X0*X5 - 2*X1*X5 - X0*X6 -
  2*X0*X7 - 4*X1*X7, 4*X2^2 - 9*X2*X3 + 3*X3^2 - 6*X2*X4 + 2*X4^2 +
  5*X2*X5 + X3*X5 + X5*X6 - X2*X7 + 2*X3*X7, 7*X0^2 + 3*X2^2 + X2*X3 +
  20*X2*X4 - 3*X4^2 - 16*X2*X5 - 16*X4*X5 - 27*X2*X6 + 4*X6^2 +
  10*X4*X7 + 8*X6*X7, 7*X1^2 + 2*X2*X3 - 6*X3^2 + 32*X2*X5 - 16*X3*X5
  - 24*X4*X5 + X5^2 + 10*X3*X7 + 8*X4*X7 - 16*X5*X7 - 2*X6*X7, 7*X0*X1
  + 3*X2*X3 + X3^2 + 20*X2*X5 - 16*X3*X5 - 3*X4*X5 - 16*X5^2 -
  27*X2*X7 + 10*X5*X7 + 4*X6*X7 + 8*X7^2 ];

// The change of coordinates used

M := Matrix(Rationals(),8,8,[
  [ 0, 0, 26, -8, -6, -6, -2, -8 ],
  [ 0, 0, 84, -14, 28, -28, -28, 0 ],
  [ 0, 0, 0, -14, 0, 0, 0, 0 ],
  [ 0, 0, -14, 2, 6, 6, 2, 8 ],
  [ -28, 28, 0, 0, 0, 0, 0, 0 ],
  [ 0, -28, 0, 0, 0, 0, 0, 0 ],
  [ 0, 0, -18, 6, 20, -20, -2, 12 ],
  [ 0, 0, -27, 11, 22, -10, -1, 12 ]]);
assert Determinant(M) eq -2^13*3^3*7^5;
// See below for output suggesting this change of coordinates
// makes the reduction "less bad" at p = 2,3,7.

quads0 := Equations(Xb5e7modw5);
quads1 := Xb5e7modw5_neweqns;
assert Ideal([q^M : q in quads0]) eq Ideal(quads1);

// The involution phi7 on the old and new models

D0 := DiagonalMatrix(Rationals(),[1,1,1,1,-1,-1,1,1]);
assert Ideal([q^D0: q in quads0]) eq Ideal(quads0);

D1 := M^(-1)*D0*M;
assert D1 eq DiagonalMatrix(Rationals(),[-1,-1,1,1,1,1,1,1]);
assert Ideal([q^D1: q in quads1]) eq Ideal(quads1);

// Computing a better basis for the original space of quadrics

MD := MonomialsOfDegree;
MC := MonomialCoefficient;
mons := MD(CoordinateRing(P7),2);
mat := Matrix(#quads0,#mons,[MC(q,mon): mon in mons,q in quads0]);
mat := LLL(Matrix(Basis(PureLattice(Lattice(mat)))));
quads0 := [&+[mat[i,j]*mons[j] : j in [1..#mons]]: i in [1..Nrows(mat)]];

// Looking at the reductions mod p of the old and new models

print "";
for ctr in [1,2] do
  if ctr eq 1 then print "Old equations"; qq := quads0; end if;
  if ctr eq 2 then print "New equations"; qq := quads1; end if;
  pp := [p : p in [2..20] | IsPrime(p)];
  for p in pp do
    printf "p = %o : ",p;
    Rp<[x]> := PolynomialRing(GF(p),8);
    Cp := Scheme(Proj(Rp),[Rp!q : q in qq]);
    XX := IrreducibleComponents(Cp);
    printf "dims = %o  degs = %o  red_degs = %o\n",
      [Dimension(X): X in XX],
      [Degree(X): X in XX],
      [Degree(ReducedSubscheme(X)): X in XX];
  end for;
  print "";
end for;

/*

Old equations
p = 2 : dims = [ 2, 2, 1, 0 ]  degs = [ 2, 2, 4, 23 ]  red_degs = [ 1, 1, 1, 1 ]
p = 3 : dims = [ 4, 0, 0, 0 ]  degs = [ 1, 2, 2, 2 ]  red_degs = [ 1, 1, 1, 1 ]
p = 5 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]
p = 7 : dims = [ 2, 1 ]  degs = [ 4, 12 ]  red_degs = [ 1, 2 ]
p = 11 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]
p = 13 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]
p = 17 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]
p = 19 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]

New equations
p = 2 : dims = [ 2, 0 ]  degs = [ 6, 4 ]  red_degs = [ 3, 1 ]
p = 3 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]
p = 5 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]
p = 7 : dims = [ 1, 1 ]  degs = [ 10, 4 ]  red_degs = [ 1, 1 ]
p = 11 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]
p = 13 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]
p = 17 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]
p = 19 : dims = [ 1 ]  degs = [ 14 ]  red_degs = [ 14 ]

*/

// Equations for Xb5e7modw5 in P^1 x P^3

P1P3<y0,y1,z0,z1,z2,z3> := ProductProjectiveSpace(Rationals(),[1,3]);
subst := [y*z : y in [y1,y0],z in [z0,z1,z2,z3]];

eqns := [
  (6*y0^2 - 13*y0*y1 - 5*y1^2)*z1 + 2*(y0^2 + 5*y0*y1)*z2 + (4*y0^2 + 2*y0*y1 + y1^2)*z3,
  (5*z1^2 + 4*z1*z3 - 2*z2*z3)*y0 - (13*z1^2 - 12*z1*z2 + 4*z2^2 - z1*z3)*y1,
  (z1^2 - 16*z1*z2 - 16*z2^2 + 10*z2*z3 + 8*z3^2)*y0
     + (7*z0^2 + 3*z1^2 + 20*z1*z2 - 3*z2^2 - 27*z1*z3 + 4*z3^2)*y1,
  (7*z0^2 - 6*z1^2 - 16*z1*z2 + z2^2 + 10*z1*z3 - 16*z2*z3)*y0
     + 2*(z1^2 + 16*z1*z2 - 12*z2^2 + 4*z2*z3 - z3^2)*y1 ];

I := Ideal([Evaluate(q,subst): q in quads1]);
assert I subset Ideal(eqns);
assert forall{f : f in [z0,z1,z2,z3] | f*eqns[1] in I};
assert forall{[f,j] : f in [y0,y1],j in [2..4] | f*eqns[j] in I};




//-------------X(b5,ns7)---------------------------------------------


P5<X0,X1,X2,X3,X4,X5>:=ProjectiveSpace(Rationals(),5);

// Josha's equations (taken from "checks_and_j_map.m")

Xb5ns7:=Curve(P5,[14*X0^2 + 12*X2*X3 - 16*X3^2 - 14*X2*X4 + 30*X3*X4 - 11*X4^2 + 28*X2*X5 - 58*X3*X5 + 40*X4*X5 - 28*X5^2, 7*X0*X1 - 2*X2*X4 - 4*X3*X4 + 2*X4^2 + 12*X3*X5 - 7*X4*X5 + 10*X5^2, 14*X1^2 - 4*X2*X3 + 16*X3^2 + 10*X2*X4 + 14*X3*X4 - 21*X4^2 + 4*X2*X5 - 58*X3*X5 + 64*X4*X5 - 66*X5^2, 2*X0*X2 - 2*X0*X3 + 2*X1*X3 - 5*X0*X4 - 6*X1*X4 + 8*X0*X5 + 4*X1*X5, 4*X1*X2 - 2*X0*X3 - 6*X1*X3 - X0*X4 + 3*X1*X4 + 3*X0*X5 - 2*X1*X5, 8*X2^2 - 20*X2*X3 + 16*X3^2 - 14*X2*X4 + 14*X3*X4 - 21*X4^2 + 28*X2*X5 - 42*X3*X5 + 56*X4*X5 - 28*X5^2]);

// Formula for the map Xb5ns7 -> Xns7
// (taken from the output of "checks_and_j_map.m")

P5<[x]> := P5;
maptoXns7 := [
  x[1] - 2/7*x[3] + 4/7*x[4] - 1/7*x[5] - 4/7*x[6],
  -2*x[1] - x[2] + 6/7*x[3] - 12/7*x[4] + 10/7*x[5] - 9/7*x[6]
  ];
P5<X0,X1,X2,X3,X4,X5> := P5;

// The new equations

Xb5ns7_neweqns := [ X0*X4 - X1*X3, X0*X5 - X2*X3, X1*X5 - X2*X4, X0^2
   - 8*X0*X1 - 5*X1^2 + X2^2 - 14*X0*X4, X0*X3 - 8*X0*X4 - 5*X1*X4 +
   X2*X5 - 14*X3*X4 , X0^2 - 4*X0*X1 - X1^2 + 2*X0*X3 + 5*X3^2 -
   4*X1*X4 + 2*X3*X4 - 4*X4^2 - 2*X2*X5 - X5^2 ];

// The change of coordinates used

M := Matrix(Rationals(),6,6,[
    [ 0, 0, 2, 0, 0, 2 ],
    [ 0, 0, -2, 0, 0, -4 ],
    [ 3, 3, 0, 8, 3, 0 ],
    [ 1, 8, 0, 5, 8, 0 ],
    [ -2, 10, 0, 2, 6, 0 ],
    [ 0, 4, 0, 4, -2, 0 ]
]);
assert Determinant(M) eq 2^4*7^2;
// See below for output suggesting this change of coordinates
// makes the reduction "less bad" at p = 2,7.

quads0 := Equations(Xb5ns7);
quads1 := Xb5ns7_neweqns;
assert Ideal([q^M : q in quads0]) eq Ideal(quads1);

// The map from the new model of Xb5ns7 to Xns7

maptoXns7 := [(1/2)*f^M : f in maptoXns7];
assert maptoXns7 eq [ X2 - X3 + 2*X4 + X5, -X0 - X1 - X2 - 2*X3 ];

// The involution w5 on the old and new models

D0 := DiagonalMatrix(Rationals(),[-1,-1,1,1,1,1]);
assert Ideal([q^D0: q in quads0]) eq Ideal(quads0);

D1 := M^(-1)*D0*M;
assert D1 eq DiagonalMatrix(Rationals(),[1,1,-1,1,1,-1]);
assert Ideal([q^D1: q in quads1]) eq Ideal(quads1);

// Computing a better basis for the original space of quadrics

MD := MonomialsOfDegree;
MC := MonomialCoefficient;
mons := MD(CoordinateRing(P5),2);
mat := Matrix(#quads0,#mons,[MC(q,mon): mon in mons,q in quads0]);
mat := LLL(Matrix(Basis(PureLattice(Lattice(mat)))));
quads0 := [&+[mat[i,j]*mons[j] : j in [1..#mons]]: i in [1..Nrows(mat)]];

// Looking at the reductions mod p of the old and new models

print "";
for ctr in [1,2] do
  if ctr eq 1 then print "Old equations"; qq := quads0; end if;
  if ctr eq 2 then print "New equations"; qq := quads1; end if;
  pp := [p : p in [2..20] | IsPrime(p)];
  for p in pp do
    printf "p = %o : ",p;
    Rp<[x]> := PolynomialRing(GF(p),6);
    Cp := Scheme(Proj(Rp),[Rp!q : q in qq]);
    XX := IrreducibleComponents(Cp);
    printf "dims = %o  degs = %o  red_degs = %o \n",
      [Dimension(X): X in XX],
      [Degree(X): X in XX],
      [Degree(ReducedSubscheme(X)): X in XX];
  end for;
  print "";
end for;

/*

Old equations
p = 2 : dims = [ 2 ]  degs = [ 4 ]  red_degs = [ 1 ]
p = 3 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]
p = 5 : dims = [ 1, 1 ]  degs = [ 5, 5 ]  red_degs = [ 5, 5 ]
p = 7 : dims = [ 3, 1, 0 ]  degs = [ 1, 8, 6 ]  red_degs = [ 1, 1, 1 ]
p = 11 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]
p = 13 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]
p = 17 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]
p = 19 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]

New equations
p = 2 : dims = [ 1, 1 ]  degs = [ 8, 2 ]  red_degs = [ 2, 1 ]
p = 3 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]
p = 5 : dims = [ 1, 1 ]  degs = [ 5, 5 ]  red_degs = [ 5, 5 ]
p = 7 : dims = [ 1, 1 ]  degs = [ 8, 2 ]  red_degs = [ 8, 2 ]
p = 11 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]
p = 13 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]
p = 17 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]
p = 19 : dims = [ 1 ]  degs = [ 10 ]  red_degs = [ 10 ]

*/


// Equations for Xb5ns7 in P^1 x P^2 (coordinates t and (u:v:w))

K<t> := PolynomialRing(Rationals());
R<u,v,w> := PolynomialRing(K,3);
subst := [u,v,w,t*u,t*v,t*w];
eqns := [Evaluate(f,subst): f in quads1];
maptoXns7_P1P2 := [Evaluate(f,subst): f in maptoXns7];
eqns[5] -:= t*eqns[4];
eqns := [f : f in eqns | f ne 0];

assert eqns eq [ u^2 - 5*v^2 + w^2 - (14*t + 8)*u*v,
 (5*t^2 + 2*t + 1)*u^2 - (2*t + 1)^2*v^2 - t*(t + 2)*w^2 + (2*t^2 - 4)*u*v ];
      
assert maptoXns7_P1P2 eq [ -t*u + 2*t*v + (t + 1)*w, (-2*t - 1)*u - v - w ];

R<u,v,w> := PolynomialRing(Rationals(),3);
P<t> := PolynomialRing(R);
eqns := eval Sprint(eqns);
g := Resultant(eqns[1],eqns[2]);

// Singular planar model in [DNS20]

assert g eq 5*u^6 - 50*u^5*v + 206*u^4*v^2 - 408*u^3*v^3 + 321*u^2*v^4
  + 10*u*v^5- 100*v^6 + 9*u^4*w^2 - 60*u^3*v*w^2 + 80*u^2*v^2*w^2 +
  48*u*v^3*w^2+ 15*v^4*w^2 + 3*u^2*w^4 - 10*u*v*w^4 + 6*v^2*w^4 - w^6;

print "The singular points on the plane model";
C := Curve(Proj(R),g);
SS := IrreducibleComponents(SingularSubscheme(C));
print SS;

/*

[
    Scheme over Rational Field defined by
    u^2 + w^2,
    v,
    Scheme over Rational Field defined by
    u,
    v^2 - 1/5*w^2
]

*/

// The map from the singular planar model of Xb5ns7 to Xns7 = P^1

KC<u,v> := FunctionField(C);
assert Evaluate(g,[u,v,1]) eq 0;
w := 1;
t := (u^2 - 5*v^2 + w^2 - 8*u*v)/(14*u*v);
subst := [u,v,w,t*u,t*v,t*w];
maptoXns7 := [Evaluate(f,subst): f in maptoXns7];
la := u^3 - 10*u^2*v - u^2*w + 11*u*v^2 - 6*u*v*w
         + u*w^2 + 10*v^3 + 5*v^2*w - 2*v*w^2 - w^3;
mu := 2*(u^3 - u^2*v + 2*u*v^2 + 7*u*v*w + u*w^2);
assert maptoXns7[1]/maptoXns7[2] eq la/mu;


