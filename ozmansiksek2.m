//This code was written by Ozman and Siksek.
/*
Functions defined in this file:

- modeqns
- searchDiv2
- reduce

- extenProb
- findGenerators
- reduceHom
- reduceHoms
- possibleJList
*/
//---------------------------------------------------------
//
// Function for writing down equations for X_0(N)
// and the j-map.
//
//-------------------------------------------------------- 


// Let N be a positive integer and n be a proper divisor.
// Suppose X_0(N) has genus \ge 3 and is not hyperelliptic.
// It is assumed that X_0(n) is in the Small Modular Curves database (n=1 is allowed).
// The function returns
// X,Z,phi,j, al, <num,denom>.
// X is the modular curve X_0(N)
// Z is the modular curve X_0(n) (exactly the same model as given by the Small Modular Curve package).
// \phi : X_0(N) \rightarrow X_0(n) is the degeneracy map.
// j is the j-function on X_0(N) as an element of its function field.
// al is a list of matrices whose action on the ambient projective space
// correspond to Atkin-Lehner involutions on X.
// num and denom are elements of the coordinate ring of the ambient
// space of X, such that num/denom restricted to X is the j-map.
modeqns:=function(N,n);
	assert IsDivisibleBy(N,n);
	gen0:=[1..10] cat [12, 13, 16, 18, 25]; // Values of N for which X_0(N) has genus 0.
	gen1:=[11, 14, 15, 17, 19, 20, 21, 24, 27, 32, 36, 49]; // Values of N for which X_0(N) has genus 1.
	hyp:=[37] cat [40,48] cat [22,23,26,28,29,30,31,33,35,39,41,46,47,50,59,71]; // Values of N for which X_0(N) is hyperelliptic.
	// These values are taken from Ogg's paper, "Hyperelliptic Modular Curves", Bull. Soc. math. France, 102, 1974, p. 449-462.
	assert #gen0 eq 15;
	assert #gen1 eq 12;
	assert #hyp eq 19;
	assert N in (gen0 cat gen1 cat hyp) eq false;
	// Thus X_0(N) has genus \ge 3 and is non-hyperelliptic, so the canonical map is an embedding.
	// We use this to construct the equations for X_0(N).
	prec:=500;
	L<q> := LaurentSeriesRing(Rationals(),prec);
	S:=CuspForms(N);
	dim:=Dimension(S);
	if dim eq 3 then
		R<x_0,x_1,x_2>:=PolynomialRing(Rationals(),dim);
	elif dim eq 4 then 
		R<x_0,x_1,x_2,x_3>:=PolynomialRing(Rationals(),dim);
	elif dim eq 5 then
		R<x_0,x_1,x_2,x_3,x_4>:=PolynomialRing(Rationals(),dim);
	else
		R<[x]>:=PolynomialRing(Rationals(),dim);
	end if;
	Bexp:=[L!qExpansion(S.i,prec) : i in [1..dim]];
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
		X:=Scheme(ProjectiveSpace(R),eqns);
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
	// We now check the equations for X rigorously, i.e.
	// up to the Sturm bound.
	indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];	
	indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)
	for eqn in eqns do
		eqnScaled:=LCM([Denominator(c) : c in Coefficients(eqn)])*eqn;
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound.
										// See Stein's book, Thm 9.18.
		Bexp1:=[qExpansion(S.i,hecke+10) : i in [1..dim]]; // q-expansions
                        // of basis for S 
                        // up to precision hecke+10.
		assert Valuation(Evaluate(eqnScaled,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X.
	Z:=SmallModularCurve(n); 
	KZ:=FunctionField(Z);
	qEZ:=qExpansionsOfGenerators(n,L,prec); // This gives gives qExpansions of the generators
						// of the function field of Z=X_0(n) as Laurent series in q. 
	KX:=FunctionField(X);
	KXgens:=[KX!(R.i/R.dim) : i in [1..(dim-1)]] cat [KX!1]; // The functions x_i/x_dim as elements of the function field of X.
	coords:=[]; // This will contain the generators of the function field of Z as element of the function of X.
	for u in qEZ do
		//We want to express u as an element of the function field of X=X_0(N).
		Su:={};
		d:=0;
		while #Su eq 0 do
			d:=d+1;
			mons:=MonomialsOfDegree(R,d);
			monsq:=[Evaluate(mon,Bexp) : mon in mons];
			V:=VectorSpace(Rationals(),2*#mons);
			W:=VectorSpace(Rationals(),prec-10);
			h:=hom<V->W | 
				[W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]] 
				cat  [ W![Coefficient(-u*monsq[i],j) : j in [1..(prec-10)]  ]  : i in [1..#mons] ]>;
			K:=Kernel(h);
			for a in [1..Dimension(K)] do
				num:=&+[Eltseq(V!K.a)[j]*mons[j] : j in [1..#mons] ];
				denom:=&+[Eltseq(V!K.a)[j+#mons]*mons[j] : j in [1..#mons] ];
				numK:=Evaluate(num,KXgens); 
				denomK:=Evaluate(denom,KXgens);
				if numK ne KX!0 and denomK ne KX!0 then
					Su:=Su join {numK/denomK};
				end if;
			end for;
		end while;
		assert #Su eq 1;
		coords:=coords cat SetToSequence(Su);
	end for;
	phi:=map<X -> Z | coords cat [1]>;
	jd:=Pullback(phi,jFunction(Z,n));
		P:=AmbientSpace(X);
		R:=CoordinateRing(P);
		assert Rank(R) eq dim;
		num:=Numerator(FunctionField(P)!jd);
		denom:=Denominator(FunctionField(P)!jd);
		num:=Evaluate(num,[R.i : i in [1..(dim-1)]]);
		denom:=Evaluate(denom,[R.i : i in [1..(dim-1)]]);
		deg:=Max([Degree(num),Degree(denom)]);
		num:=Homogenization(num,R.dim,deg);
		denom:=Homogenization(denom,R.dim,deg);
		assert Evaluate(num,KXgens)/Evaluate(denom,KXgens) eq jd;	
		// We compute the degree of j : X_0(N) --> X(1) using the formula
		// in Diamond and Shurman, pages 106--107.
		assert N gt 2;
		dN:=(1/2)*N^3*&*[Rationals() | 1-1/p^2 : p in PrimeDivisors(N)];
		dN:=Integers()!dN;
		degj:=(2*dN)/(N*EulerPhi(N));
		degj:=Integers()!degj; // Degree j : X_0(N)-->X(1)
		degjd:=&+[-Valuation(jd,P)*Degree(P) : P in Poles(jd)];
		assert degj eq degjd;
		// Now if j \ne jd then the the difference j-jd is a rational
		// function of degree at most 2*degj (think about the poles).
		// Hence to prove that j=jd all we have to check is that their
		// q-Expansions agree up to 2*degj+1.
		jdExpansion:=Evaluate(num,Bexp)/Evaluate(denom,Bexp);
		jdiff:=jdExpansion-jInvariant(q);
		assert Valuation(jdiff) ge 2*degj+1; // We have proven the corrections of the
										// j-map jd on X_0(N).
	// Next we want to write down the matrices for the Atkin-Lehner
	// operators on X_0(N)
	alindices:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
	al:=[AtkinLehnerOperator(S,m) : m in alindices];
	return X, Z, phi, jd, al, <num,denom>;
end function;

// Search for divisors of degree 2
// Given a curve X/\Q as before, and a bound bd and a true/false tf
// this function returns
// deg2,pls1,pls2,plsbig
// Here pls1 is a set of places of degree 1
// pls2 is a set of places of degree 2 and
// plsbig is a set of places of degree at least 3 but less than genus.
// pls1 are found by a search for rational points on X
// pls2, plsbig are found by intersecting hyperplanes with X.
// deg 2 are the known degree 2 effective divisors: sums of pairs of
// elements of pls1, and elements of pls2.
// If tf=true then the automorphism group of X is used
// to enlarge the sets pls1 and pls2 (if possible).

searchDiv2:=function(X,bd,A);
	g:=Genus(X);
	//
	// First we find degree 1 points
	pts:=PointSearch(X , 1000);
	pls1:={Place(P) : P in pts};
	pls2:={};
	plsbig:={};
	R:=CoordinateRing(AmbientSpace(X));
	n:=Rank(R);
	// Next we intersect X with hyperplanes with coefficients bounded by bd
	// and see what divisors we obtain.
	C:=CartesianPower([-bd..bd],n);
	ctr:=0;
	for a in C do
		ctr:=ctr+1;
		//print #C,ctr,#pls1, #pls2,#plsbig;
		b:=[a[i] : i in [1..n]];
		if &or[b[i] ne 0 : i in [1..n]] then
			if GCD(b) eq 1 and b[1] ge 0 then
				f:=&+[b[i]*R.i : i in [1..n]];
				D:=Divisor(X,ideal<R | f>);
				decomp:=Decomposition(D);
				for pr in decomp do
					P:=pr[1];
					if Degree(P) eq 1 then
						pls1:=pls1 join {P};
					else
						if Degree(P) eq 2 then
							pls2:=pls2 join {P};
						else
							if Degree(P) le g then
								plsbig:=plsbig join {P};
							end if;
						end if;
					end if;
				end for;
			end if;
		end if;
	end for;
	
		// We will use the automorphisms of X
						// to enlarge the sets pls1, pls2.
		for phi in A do
			for P in pls1 do
				D:=Pullback(phi,P);
				pls1:=pls1 join {Decomposition(D)[1,1]};
			end for;
			for P in pls2 do
				D:=Pullback(phi,P);
				pls2:=pls2 join {Decomposition(D)[1,1]};
			end for;
		end for;
	
	pls1:=SetToSequence(pls1);
	pls2:=SetToSequence(pls2);
	plsbig:=SetToSequence(plsbig);
	deg2:=[];
	for i,j in [1..#pls1] do
		if i le j then
			Append(~deg2,1*pls1[i]+1*pls1[j]);
		end if;
	end for;
	deg2:=deg2 cat [1*P : P in pls2];
	return deg2,pls1,pls2,plsbig;
end function;


// X is a projective curve over rationals,
// p prime of good reduction,
// D divisor on X,
// This reduces to a divisor on X/F_p.

reduce:=function(X,Xp,D);
	if Type(D) eq DivCrvElt then
		decomp:=Decomposition(D);
		return &+[ pr[2]*$$(X,Xp,pr[1]) : pr in decomp]; // Reduce the problem to reducing places.
	end if;
	R<[x]>:=CoordinateRing(AmbientSpace(X));
        assert Type(D) eq PlcCrvElt;
        if  (Degree(D) eq 1) and (#{Degree(xx) : xx in x} eq 1) then
		P:=D;
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



//Functions for Abelian group theory. 
//
//-------------------------------------------------------- 


//                i1       pi1
// Given 0--> C1 -----> A1 -----> B1 -->0
//            |                   |                              
//            phi                mu  
//            |                   |
//            V                   V
//      0--> C2 -----> A2 -----> B2 -->0
//               i2         pi2
// with top and bottom row exact sequence of finite abelian groups
// and phi, mu isomorphisms, is there an isomorphism psi : A1 --> A2
// making the diagram commute?
extenProb:=function(phi,mu,i1,i2,pi1,pi2);
    C1:=Domain(i1);
    C2:=Domain(i2);
    assert C1 eq Domain(phi);
    assert C2 eq Codomain(phi);
    A1:=Domain(pi1);
    A2:=Domain(pi2);
    assert A1 eq Codomain(i1);
    assert A2 eq Codomain(i2);
B1:=Codomain(pi1);
    B2:=Codomain(pi2);
    assert B1 eq Domain(mu);
    assert B2 eq Codomain(mu);
    assert #Kernel(i1) eq 1;
    assert #Kernel(i2) eq 1;
    assert Image(pi1) eq B1;
    assert Image(pi2) eq B2;
    assert Kernel(pi1) eq Image(i1);
    assert Kernel(pi2) eq Image(i2);
    assert #Kernel(phi) eq 1;
    assert #Kernel(mu) eq 1;
    assert #C1 eq #C2;
    assert #B1 eq #B2;
    if #B1 eq 1 then
        // In this case i1 and i2 are isomorphisms.
        return true, hom<A1->A2 | [ i2(phi(a@@i1)) : a in OrderedGenerators(A1)]>;
    end if;
    Q,modC1:=quo< A1 | sub<A1  | [i1(c) : c in OrderedGenerators(C1)]> >;
    Qgens:=OrderedGenerators(Q);
    r:=#Qgens;
	xs:=[q@@modC1 : q in Qgens]; // x1,..xr together with i1(C1) generates A1.
    ys:=[(mu(pi1(x)))@@pi2 : x in xs];
    Zr:=FreeAbelianGroup(r);
    pretau:=hom<Zr->A1 | xs>;
    Astar,j1,j2,pj1,pj2:=DirectSum(Zr,C1); //Z^r x C_1.
    // j1, j2 are the inclusion maps Z^r --> A^*, C_1 --> A^*.
    // pj1, pj2 are the projection maps A^* --> Z^r, A^* --> C_1.
    //tau:=hom<Astar->A1 | [ pretau(pj1(d))+(pj2(d))@@i1 : d in OrderedGenerators(Astar)]>;
    tau:=hom<Astar->A1 | [ pretau(pj1(d))+(pj2(d))@i1 : d in OrderedGenerators(Astar)]>;
    K:=Kernel(tau);
    Kgens:=OrderedGenerators(K);
    s:=#Kgens;
    clist:=[ i2(phi(pj2(Astar!k))) : k in Kgens];
    nlist:=[ Eltseq(pj1(Astar!k)) : k in Kgens];
    Cr,Crinjs,Crprojs:=DirectSum([C2 : i in [1..r]]);
    Cs,Csinjs,Csprojs:=DirectSum([C2 : i in [1..s]]);
    Crgens:=[ [Crprojs[i](delta) : i in [1..r]] : delta in OrderedGenerators(Cr)];
    dotprod:=func<nn,tt | &+[ nn[i]*tt[i] : i in [1..#tt]]>;
	eta:=hom<Cr->Cs | [  &+[ Csinjs[j](dotprod(nlist[j],crgen)) : j in [1..s]   ]      : crgen in Crgens ]  >;
    testelt:=-1*&+[ Csinjs[j]((clist[j]+dotprod(nlist[j],ys))@@i2) : j in [1..s]];
    I:=Image(eta);
    if testelt in I then
        tlist:=testelt@@eta;
        tlist:=[Crprojs[i](tlist) : i in [1..r]];
        presigma:=hom<Zr->A2 | [ys[i]+i2(tlist[i]) : i in [1..r]]>;
        sigma:=hom<Astar->A2 | [presigma(pj1(d))+i2(phi(pj2(d))) : d in OrderedGenerators(Astar)]>;
        psi:=hom<A1->A2 | [ sigma(a@@tau) : a in OrderedGenerators(A1)]>;
        assert #Kernel(psi) eq 1;
        assert #A1 eq #A2; // psi is really an isomorphism.
        assert &and[psi(i1(c)) eq i2(phi(c)) : c in OrderedGenerators(C1)];
        assert &and[mu(pi1(a)) eq pi2(psi(a)) : a in OrderedGenerators(A1)];
        // And it really makes the diagram commutative.
        return true, psi;
    else
        return false;
    end if;
end function;

/*

Derek Holt's example. The extension problem is impossible:

A:=AbelianGroup([2,4,8]);
C1:=sub<A | [A.1,2*A.3]>;
C2:=sub<A | [4*A.3,A.2]>;  
i1:=hom<C1->A | [A!(C1.1),A!(C1.2)]>;
i2:=hom<C2->A | [A!(C2.1),A!(C2.2)]>;
B1,pi1:=quo<A | C1>;
B2,pi2:=quo<A | C2>;
phi:=hom<C1->C2 | [C2.1,C2.2]>;
mu:=hom<B1->B2 | [B2.1,B2.2]>; 
extenProb(phi,mu,i1,i2,pi1,pi2); 
==================================================================

Random example

A:=AbelianGroup([2,4,8]);
C1:=sub<A | [A.1,A.2]>;
C2:=sub<A | [A.1,A.2]>;  
i1:=hom<C1->A | [A!(C1.1),A!(C1.2)]>;
i2:=hom<C2->A | [A!(C2.1),A!(C2.2)]>;
B1,pi1:=quo<A | C1>;
B2,pi2:=quo<A | C2>;
phi:=hom<C1->C2 | [C2.1,-C2.2]>;
mu:=hom<B1->B2 | [-B2.1]>; 
tf,psi:=extenProb(phi,mu,i1,i2,pi1,pi2);
assert tf;
assert &and[psi(i1(c)) eq i2(phi(c)) : c in C1];
assert &and[mu(pi1(b)) eq pi2(psi(b)) : b in A];

*/

// i1 : C --> A1
// i2 : C --> A2
// injective homomorphisms of finite abelian groups.
// Is there an isomomorphism psi: A1 --> A2
// making the triangle commute? 
homExtend:=function(i1,i2);
    assert Domain(i1) eq Domain(i2);
    C:=Domain(i1);
    assert #Kernel(i1) eq 1;
    assert #Kernel(i2) eq 1;
    A1:=Codomain(i1);
    A2:=Codomain(i2);
    if IsIsomorphic(A1,A2) eq false then
            return false;
    end if;
    B1,pi1:=quo<A1 | Image(i1)>;
    B2,pi2:=quo<A2 | Image(i2)>;
    tf,mu1:=IsIsomorphic(B1,B2);
    if tf eq false then
        return false;
    end if;
	phi:=hom<C->C | [c : c in OrderedGenerators(C)]>; // The
    // identity map C-->C.
    mapautB2,autB2:=PermutationRepresentation(AutomorphismGroup(B2));
    for kappa in autB2 do // autB2 is a permutation group that
                        // is isomorphic to the automorphism group of B2.
        eta:=kappa@@mapautB2; // This converts the permutation into an
                            // an automorphism of B2.
        mu:=hom<B1->B2 | [  eta(mu1(b)) : b in OrderedGenerators(B1) ]>;
                        // As kappa runs through the elements of autB2
                        // mu runs through the isomorphisms B1-->B2.
        tf:=extenProb(phi,mu,i1,i2,pi1,pi2);
        if tf then
            return true;
        end if;
    end for;
    return false;
end function;




	
// divs are a bunch of known effective divisors,
// P0 is a base point of degree 1,
// p>2 is a prime of good reduction.
// This determines an abstract abelian group Ksub
// isomorphic to the group spanned by [D-deg(D) P_0] 
// where D runs through the elements of divs.  
// It also returns a subset divsNew such that [[D-deg(D) P_0] : D in divsNew]
// generates the same subgroup.
// It also determines a homomorphism 
// h : \Z^r --> Ksub
// where divsNew=[D_1,..,D_r]
// and h([a_1,..,a_r]) is the image of 
// a_1 (D_1-deg(D_1) P_0)+\cdots + a_r (D_r-deg(D_r) P_0)
// in Ksub.

findGenerators:=function(X,divs,P0,p);
	fn:=func<A,B| Degree(A)-Degree(B)>;
	Sort(~divs,fn); // Sort the divisors by degree.
	assert IsPrime(p);
	assert p ge 3;
	Xp:=ChangeRing(X,GF(p));
	assert IsSingular(Xp) eq false; // Now we know that
	// J_X(Q)-->J_X(\F_p) is injective (we're assuming rank 0).
	C,phi,psi:=ClassGroup(Xp);
	Z:=FreeAbelianGroup(1);
	degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
	A:=Kernel(degr); // This is isomorphic to J_X(\F_p).
	Pp0:=reduce(X,Xp,P0);
	divsRed:=[reduce(X,Xp,D) : D in divs];
	divsRedA:=[psi(D-Degree(D)*Pp0) : D in divsRed]; // The image of the divisors in A;
	Ksub1:=sub<A | divsRedA>; // The subgroup of J(\F_p) generated by
							// [D-deg(D)*P_0] with D in divs.	
	// Next we eliminate as many of the divisors as possible
	// while keeping the same image.
	r:=#divs;
	inds:=[i : i in [1..r]];
	i:=r+1;
	repeat
		i:=i-1;
		indsNew:=Exclude(inds,i);
		if sub<A | [divsRedA[j] : j in indsNew]> eq Ksub1 then
			inds:=indsNew;
		end if;
	until i eq 1;
	divsNew:=[divs[j] : j in inds];
	divsRedA:=[divsRedA[j] : j in inds];
	r:=#divsNew;	
	Zr:=FreeAbelianGroup(r);
	h:=hom<Zr->A | divsRedA>;
	Ksub:=Image(h); // Stands from known subgroup.
	assert Ksub eq Ksub1;
	h:=hom<Zr->Ksub | [ Ksub!h(Zr.i) :  i in [1..r] ]>;
	// Restrict the codomain of h so that it is equal to Ksub.
	bas:=[Eltseq(i@@h) : i in OrderedGenerators(Ksub)];
	return h,Ksub,bas,divsNew;
end function;


// Determine the homomorphism from Ksub-->J(F_p)
reduceHom:=function(X,divs,P0,Xp,Ksub,bas);
	C,phi,psi:=ClassGroup(Xp);
	Z:=FreeAbelianGroup(1);
	degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
	A:=Kernel(degr); // This is isomorphic to J_X(\F_p).
	Pp0:=reduce(X,Xp,P0);
	divsRed:=[reduce(X,Xp,D) : D in divs];
	r:=#divsRed;
	Zr:=FreeAbelianGroup(r);
	eta:=hom<Zr->A | [psi(D-Degree(D)*Pp0) : D in divsRed]>;
	pi:=hom<Ksub->A | [ eta(Zr!g) : g in bas]>;
	return pi,phi,psi;
end function;

// Determine all possible subgroups A of J(F_p) 
// that contain the image of Ksub-->J(F_p)
// and return the induced injective maps Ksub-->A.
reduceHoms:=function(X,divs,P0,Xp,Ksub,bas);
    C,phi,psi:=ClassGroup(Xp);
    Z:=FreeAbelianGroup(1);
    degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
    J:=Kernel(degr); // This is isomorphic to J_X(\F_p).
    Pp0:=reduce(X,Xp,P0);
    divsRed:=[reduce(X,Xp,D) : D in divs];
    r:=#divsRed;
    Zr:=FreeAbelianGroup(r);
    eta:=hom<Zr->J | [psi(D-Degree(D)*Pp0) : D in divsRed]>;
    pi:=hom<Ksub->J | [ eta(Zr!g) : g in bas]>;
    I:=Image(pi);
    Q,mu:=quo<J | I>;
    subs:=Subgroups(Q);
    subs:=[H`subgroup : H in subs];
    subs:=[ sub<J | [g@@mu : g in OrderedGenerators(H) ] cat OrderedGenerators(I)> : H in subs ];
    homs:=[ hom<Ksub -> H | [H!(pi(g)) : g in OrderedGenerators(Ksub)]> : H in subs ];
    return homs;
end function;

// This function uses reduction modulo the primes in prs
// to determine a set of injections Ksub --> A
// such that for one of these injections, A is isomorphic
// to J(\Q), and Ksub --> A is the natural injection.
possibleJList:=function(X,divs,P0,Ksub,bas,prs);
    p:=prs[1];
    hms:=[* reduceHoms(X,divs,P0,ChangeRing(X,GF(p)),Ksub,bas) : p in prs *];
    homs:=hms[1];
    n:=#prs;
    for i in [2..n] do
        homsi:=hms[i];
        homsNew:=homs;
        for h in homs do
            if &and[homExtend(h,hi) eq false : hi in homsi] then
                Exclude(~homsNew,h);
            end if;
        end for;
        homs:=homsNew;
    end for;
    return homs;
end function;

