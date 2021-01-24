#In this file, we check the assertions made in the final corollary of the paper.

N = 5 * 7^2
K = 7
M = 5 #Notation of K,M and N corresponds to the paper.
g1 = CRT([8,1], [K^2,M]) #g1 is 8 mod 49 and 1 mod 5 (8 is a generator of the subgroup of Z/49Z* of elements that are 1 mod 7)
g2 = CRT([1,2], [K^2,M]) #g2 is 1 mod 49 and 2 mod 5 (2 is a generator of Z/5Z*)
G = GammaH(N,[g1,g2]) #This is Gamma_0(MK^2) \cap \Gamma_1(K)
G35 = GammaH(35,[CRT([2,1],[5,7])]) #Congruence subgroup corresponding to old subspace of level 35
G49 = GammaH(49,[8]) #Congruence subgroup corr to old subspace of level 49

N49=Newforms(G49,names='a')
f49=N49[0] #This is f_49
assert f49.has_cm()
#Also f49 = f49 \otimes chi^3 so f49 has inner twists too.

N35=Newforms(G35,names='a')
f35=N35[0]
g35=N35[1]
assert len(N35) == 3 #f35, g35 and the conjugate of g35.
assert not f35.has_cm()
assert not g35.has_cm()
#They also do not have inner twists as f35 \otimes chi^3 and g35\otimes chi^3 are not conjugates.

N=Newforms(G,names='a')
f0pos=[f for f in N if f.hecke_eigenvalue_field().discriminant()==1 and f[3] == -3]
assert len(f0pos) == 1
f0=f0pos[0] #this must be f0
f1pos=[f for f in N if f[4] == 0 and f[2]^2 == 2 and f[3]==-(f[2]+1)]
assert len(f1pos) == 1
f1=f1pos[0] #this must be f1
f2pos=[f for f in N if (f[2]-1)^2 == 2 and f[3]==-f[2]+2]
assert len(f2pos) == 1
f2=f2pos[0] #this must be f2
assert not f0.has_cm()
assert not f1.has_cm() 
assert not f2.has_cm()

DG7 = DirichletGroup(7)
chis = [chi for chi in list(DG7) if (chi.conductor() in [7] and chi.order() == 6)]
chi = chis[0] 

#In order to twist, we first extend the base field.
N35K = Newforms(G35,base_ring = CyclotomicField(6),names='a')
N49K = Newforms(G49,base_ring = CyclotomicField(6),names='b')
NK=Newforms(G,base_ring=CyclotomicField(6),names='c')
NN=N49K+N35K+NK
fs=[f35,g35,f0,f1,f2]

#We recover the fs in NN
fsK=[]
for f in fs:
    fKs=[g for g in NN if g[2].minpoly() == f[2].minpoly() and g[3].minpoly() == f[3].minpoly()]
    assert len(fKs) <= 2 #only f and its conjuage
    fsK.append(fKs[0])

#We compute twists
f35twists=[fsK[0].twist(chi^a) for a in range(6)]
g35twists=[fsK[1].twist(chi^a) for a in range(6)]
f0twists=[fsK[2].twist(chi^a,level=5*7^2) for a in range(6)]
f1twists=[fsK[3].twist(chi^a,level=5*7^2) for a in range(6)]
f2twists=[fsK[4],fsK[4].twist(chi,level=5*7^2),fsK[4].twist(chi^2,level=5*7),fsK[4].twist(chi^3,level=5*7^2),fsK[4].twist(chi^4,level=5*7),fsK[4].twist(chi^5,level=5*7^2)]

#And finally we evaluate their L-series. 
Ls1f35=[f.lseries()(1) for f in f35twists]
Ls1g35=[f.lseries()(1) for f in g35twists] 
Ls1f0=[f.lseries()(1) for f in f0twists]   
Ls1f1=[f.lseries()(1) for f in f1twists]   
Ls1f2=[f.lseries()(1) for f in f2twists] 

assert all([a.abs() > 0.1 for a in Ls1g35])
assert all([a.abs() > 0.1 for a in Ls1f2])
assert all([a.abs() > 0.1 for a in [Ls1f0[1],Ls1f0[3],Ls1f0[5]]])
assert all([a.abs() > 0.1 for a in [Ls1f35[0],Ls1f35[2],Ls1f35[4]]])

#This shows that all twists of g35, the twists of f1 by chi,chi^3 and chi^5, and
#f35, and its twists by chi^2 and chi^4 all have non-vanishing Lseries at 1.
