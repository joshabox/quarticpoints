
//MORDELL--WEIL SIEVE FOR QUARTIC POINTS
/*This sieve is implemented to work for isolated degree 4 effective divisors on a curve X and for
points of the form Q+R, where Q is an effective degree 2 divisor on X and R is the pullback
from a rational point on a curve C admitting a degree 2 map X --> C. It is also possible to add to the IsLonely function
the option that the effective degree 4 divisor is a pullback from an effective degree 2 divisor on C,
but we did not need that. */

/* INPUT: model for projective curve X/\Q; set L of degree 4 divisors on X,
 set divs of degree 0 divisors that generate a finite index subgroup G of J_X(Q), 
 an integer I such that I*J_X(Q) subset G,
an abstract abelian group A isomorphic to G such that A.i corresponds to divs[i], 
a degree 4 divisor bp on X, to be used to embed X^{(4)} in J_X,
an automorphism w5 on X such that we do Chabauty
relative to the quotient of X by this autmorphism,
a subgroup B0 of A embedded via iA0: B0 --> A and a set W0 of B-coset representatives in A.
The triple (B0,iA0,W0) is needed to start the sieve. When assuming nothing, these should be
B0=A, iA0=Id and W0={0}. */

//The following function computes the expansion of a differential 
//om around the uniformizer tQ of a point Q, up to the (n+1)th coefficient a_n.
ExpandDifferential:=function(om,Q,tQ,n)
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


//This function verifies the conditions of Theorem XXX
//Input: degree 4 divisor QQ and prime p of good reduction
IsLonely:=function(QQ,p,X,w5)
FF:=GF(p^(12)); //Fp, Fp^2, Fp^3 and Fp^4 all embed into FF.
XFF:=ChangeRing(X,FF);
Embed(GF(p),FF);
if p eq 7 then return false; end if; //Small primes condition
d:=4; //Just there to emphasize that we work on X^{(d)} for d=4.

Xp:=ChangeRing(X,GF(p));
Rp<[up]>:=CoordinateRing(AmbientSpace(Xp));
wpeqns:=[Evaluate(eqn,up) : eqn in DefiningEquations(w5)];
wp:=iso<Xp->Xp | wpeqns,wpeqns>;
V,phi:=SpaceOfDifferentialsFirstKind(Xp);
t:=hom<V->V | [ (Pullback(wp,phi(V.i)))@@phi -V.i  : i in [1..Genus(X)] ]>;
T:=Image(t); //The space of vanishing differentials
omegas:=[phi(T.i) : i in [1..Dimension(T)]]; //A basis of reductions of vanishing differentials
matrixseq:=[];
ChangeUniverse(~matrixseq,Parent([FF.1]));

decred:=Decomposition(reduce(X,Xp,QQ));
dec:=Decomposition(1*QQ);
decs:=[dec[i][1] : i in [1..#dec]];
pbpart:=[DD[1] : DD in dec | Pullback(w5,DD[1]) eq DD[1]];

for i in [1..#decred] do
    Qt:=decred[i][1];
    if IsSingular(RepresentativePoint(Qt)) then return false; end if;
    k<t>:=ResidueClassField(Qt);
    Xk:=ChangeRing(X,k);
    Embed(k,FF);
    if Degree(k) eq 1 then
        frobs:=[IdentityHomomorphism(k)];
    else frobs:=[hom<k->k | k.1^(p^a)> : a in [0..Degree(k)-1]];
    end if;
    tQt:=UniformizingParameter(Qt);
    for frob in frobs do
        Qk:=Xk![frob(a): a in Eltseq(RepresentativePoint(Qt))];
        exps:=[ExpandDifferential(om,Qk,tQt,decred[i][2]-1) : om in omegas];
        for j in [1..#exps[1]] do
            Append(~matrixseq,[exps[m][j] : m in [1..#exps]]);
        end for;
    end for;
end for;

Atilde:=Matrix(matrixseq);
if pbpart eq [] and Rank(Atilde) eq d then return true;
elif #pbpart gt 0 then assert (#pbpart eq 1 and Degree(pbpart[1]) eq 2); //The partially relative Chabauty case.
    if Rank(Atilde) eq d-1 then return true;
    end if;
end if;
return false;
end function;


ChabautyInfo:=function(X,w5,L,p,A,divs,I,bp,B,iA,W)
//I must satisfy I*J_X(\Q) \subset G.
Fp:=GF(p);
Xp:=ChangeRing(X,Fp);
CC,phi,psi:=ClassGroup(Xp);
Z:=FreeAbelianGroup(1);
degr:=hom<CC->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CC)]>;
JFp:=Kernel(degr); // This is isomorphic to J_X(\F_p).
divsp:=[reduce(X,Xp,divi) : divi in divs];
bpp:=reduce(X,Xp,bp); //We reduce the divisors and the basepoint
h:=hom<A -> JFp | [JFp!psi(divp) : divp in divsp]>; //The map A--> J_X(\F_p).

//We now split our cosets in W into smaller cosets on which h takes a single value.
Bp,iAp:=sub<A | Kernel(h)>;
newB,newiA:=sub<A | iA(B) meet iAp(Bp)>; 
AmodnewB,pi1:=quo< A | newiA(newB)>;
AmodB,pi2:=quo<AmodnewB | pi1(iA(B))>;
W:=[(x+w)@@pi1 : x in Kernel(pi2), w in pi1(W)]; 
B:=newB; iA:=newiA;
mI:=hom<JFp -> JFp | [I*g : g in OrderedGenerators(JFp)]>;
imW:={h(x) : x in W | h(x) in Image(mI)}; 
K:=Kernel(mI);
reds:=[reduce(X,Xp,DD) : DD in L];
redL2:=[psi(DD-bpp) : DD in reds];
jposP:=[];

for x in imW do //For each z such that I*z = x, we check whether z can come from a rational point. If yes for some z, we keep x. 
    z:=x@@mI;
    if &or[Dimension(phi(z+k)+bpp) gt 0 and (not CC!(z+k) in redL2 or p in [11,13] or not IsLonely(L[Index(redL2,CC!(z+k))],p,X,w5)) : k in K] then Append(~jposP,x);
    end if;
end for;

print "The nr of jposP is"; #jposP;
W:=[x : x in W | h(x) in jposP]; //Representatives for the B-cosets of A corresponding to jposP.
return W,B,iA; 
end function;



MWSieve:=function(X,w5,L,primes,A,divs,I,bp,B0,iA0,W0)
B:=B0;
iA:=iA0;
W:=W0;
// Together, B+W \subset A consists of the possible images of unknown (rational)
// points in A. The map X(\Q) \to A is composition of X(\Q) \to J(X)(\Q) and
// multiplication by integer I such that I*J(X)(\Q) \subset A.
for p in primes do
p;
W,B,iA:=ChabautyInfo(X,w5,L,p,A,divs,I,bp,B,iA,W);
// Whatever Chabauty method we use, it should output a subgroup iAp: Bp \to A and
// a set Wp of Bp-cosets containing the hypothetical unknown points.
if W eq [] then return true; end if;
print "The number of possible cosets unknown points can land is"; #W;
end for;
return B,iA,W;
end function;

