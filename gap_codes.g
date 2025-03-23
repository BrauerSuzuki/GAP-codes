#behavior of ShallowCopy and StructuralCopy
#a:=[[1]];; b:=a;; c:=ShallowCopy(a);; d:=StructuralCopy(a);; 
#a[1]:=[2];; b; c; d; 
#[ [ 2 ] ]
#[ [ 1 ] ]
#[ [ 1 ] ]

#a:=[[1]];; b:=a;; c:=ShallowCopy(a);; d:=StructuralCopy(a);; 
#a[1][1]:=3;; b; c; d;
#[ [ 3 ] ]
#[ [ 3 ] ]
#[ [ 1 ] ]

#LoadPackage("anupq");
#1536to512:=function(id) #return IdGroup(SylowSubgroup(SmallGroup(1536,id),2))[2]
#local G,P,F,H;
	#if id<=10494213 then return id; fi; #nilpotent groups
	#G:=SmallGroup(1536,id);
	#P:=SylowSubgroup(G,2);
	#F:=PqStandardPresentation(P);
	#H:=PcGroupFpGroup(F);
	#return IdStandardPresented512Group(H)[2];
#end;

#Id512:=function(G)
#local F,H;
	#F:=PqStandardPresentation(G);
	#H:=PcGroupFpGroup(F);
	#return IdStandardPresented512Group(H);
#end;

SporLinGroups:=[[25,15],[25,18],[25,19],[49,25],[49,29],[121,39],[121,42],[121,56],[121,57],[19^2,86],[23^2,59],[29^2,106],[29^2,110],[59^2,84],[16,20],[81,71],[81,90],[81,99],[81,130],[81,129],[81,124],[81,126],[81,127],[81,128],[3^6,396]];

NonsolvableOrders:=[ 60, 120, 168, 180, 240, 300, 336, 360, 420, 480, 504, 540, 600, 660, 672, 
  720, 780, 840, 900, 960, 1008, 1020, 1080, 1092, 1140, 1176, 1200, 1260, 
  1320, 1344, 1380, 1440, 1500, 1512, 1560, 1620, 1680, 1740, 1800, 1848, 
  1860, 1920, 1980 ];

FLOAT.VIEW_DIG:=50;

PPart:=function(n,p) if n=0 then return infinity; else return p^Valuation(n,p); fi; end;
PPN:=function(n,p) return n/p^Valuation(n,p); end;

Sym:=SymmetricGroup;
Alt:=AlternatingGroup;
DP:=DirectProduct;
EA:=ElementaryAbelianGroup;
CG:=CyclicGroup;
AG:=AbelianGroup;

SubgroupsC:=function(G)
return List(ConjugacyClassesSubgroups(G),Representative);
end;

ElementsC:=function(G)
return List(ConjugacyClasses(G),Representative);
end;

Codegree:=function(G,chi)
	return Index(G,KernelOfCharacter(chi))/chi[1];
end;

#LoadPackage("grape",false);;
HasStronglyP:=function(G,p)
local P,S,g;
	if Size(G) mod p<>0 or Size(PCore(G,p))>1 then return false; fi;
	P:=SylowSubgroup(G,p);
	if IsCyclic(P) or IsQuaternionGroup(P) then return true; fi;
	S:=List(ConjugacyClassSubgroups(G,P));
	g:=Graph(Group(()),S,OnPoints,{x,y}->Size(Intersection(x,y))>1,true );
	return not IsConnectedGraph(g);
end;

PermCol:=function(M,g) #permute columns of matrix
local T;
	T:=List(TransposedMat(M));
	T:=Permuted(T,g);
	return TransposedMat(T);
end;

IsIsoclinic:=function(G,H)
local DG,DH,ZG,ZH,fG,fH,AH,a,iso,genDG,genDH,test,R;
	DG:=DerivedSubgroup(G);
	DH:=DerivedSubgroup(H);
	if IdGroup(DG)<>IdGroup(DH) then return false; fi;
	ZG:=Center(G);
	ZH:=Center(H);
	if IdGroup(G/ZG)<>IdGroup(H/ZH) then return false; fi;
	fG:=NaturalHomomorphismByNormalSubgroup(G,ZG);
	fH:=NaturalHomomorphismByNormalSubgroup(H,ZH);
	AH:=AutomorphismGroup(Image(fH));
	iso:=IsomorphismGroups(Image(fG),Image(fH));
	R:=Combinations(reps(G,ZG),2);
	genDG:=List(R,Comm);
	for a in AH do
		genDH:=List(R,c->Comm(Representative(PreImages(fH,((c[1]^fG)^iso)^a)),Representative(PreImages(fH,((c[2]^fG)^iso)^a))));
		test:=GroupHomomorphismByImages(DG,DH,genDG,genDH);
		if test<>fail and IsSurjective(test) then return true; fi;
	od;
	return false;
end;

IsRegularPGroup2:=function(G) #incomplete
local p,lc,e;
	p:=PrimePGroup(G);
	if p=2 then return IsAbelian(G); fi;
	if Exponent(G)=p or NilpotencyClassOfGroup(G)<p then return true; fi;
	lc:=LowerCentralSeriesOfGroup(G);
	if Size(lc)<p or IsCyclic(lc[p-1]) then return true; fi; #Berkovich
	e:=LogInt(Exponent(G),p);
	if ForAny([1..e-1],i->Exponent(Omega(G,p,i))>p^i) then return false; fi;
	return fail;
end;

IsRegularPGroup3 :=  function(g) #Robert Morse, also sufficient but not necessary
	local p,e;
	if not IsPGroup(g) then return fail; fi;
	if IsAbelian(g) then return true; fi;
	p := PrimePowersInt(Size(g));
	e := p[2];
	p := p[1];
	return Index(g,Agemo(g,p,1))<p^p or Index(DerivedSubgroup(g),Agemo(DerivedSubgroup(g),p,1))<p^(p-1) or Size(Omega(g,p,1))<p^(p-1);
end;

InvPS:=function(a,d) #inverse of power series with coefficients a=(a_0,…) where a_0\ne 0, up to d coefficients
local s,b,i;
	if a[1]=0 then Error("Power series not invertible"); fi;
	s:=Size(a);
	b:=[1/a[1]];
	for i in [2..d-1] do
		b[i]:=-Sum([1..Minimum(i-1,s-1)],j->a[j+1]*b[i-j])/a[1];
	od;
	return b;
end;

GroupDeterminant:=function(G) #too slow
local n,el,x,i,j,D;
	n:=Size(G);
	el:=Elements(G);
	x:=[];
	for i in [1..n] do x[i]:=X(Rationals,Concatenation("X",String(i))); od;
	D:=NullMat(n,n);
	for i in [1..n] do
		for j in [1..n] do 
			D[i][j]:=x[Position(el,el[i]*el[j]^-1)];
		od;
	od;
	return Determinant(D);
end;

IsRationalGroup:=function(G)
local pi;
	if IsSolvable(G) then
		pi:=PrimeDivisors(Size(G));
		if not IsSubset([2,3,5],pi) then return false; fi; #Gow
		if Exponent(G) mod 25=0 or Index(G,PCore(G,5)) mod 5=0 then return false; fi; #Hegedüs
	fi;
	return Size(RationalClasses(G))=NrConjugacyClasses(G);
end;

FieldOfValue:=function(G)
	return Field(Union(Irr(G)));
end;

GGtoNF:=function(G) #convert Galois group to number field
local n,res;	
	n:=Characteristic(One(G));
	res:=List(Elements(G),Int);
	return NF(n,res);
end;

Qg:=function(G,g) #Q(g) where g in G
local rc,gg;	
	rc:=RationalClass(G,g);
	gg:=GaloisGroup(rc);
	return GGtoNF(gg);
end;

PadicExp:=function(n,p)
	if n<0 or p<2 then Error(n," must be non-negative and ",p," must be at least 2"); fi;
	if n<p then return [n]; else return Concatenation(PadicExp(Int(n/p),p),[n mod p]); fi;
end;

HallPoly:=function(lam,mu,q) #returns the Hall polynomial in q with respect to partitions mu \subseteq lam
local lam2,mu2;
	lam2:=AssociatedPartition(lam);
	mu2:=Concatenation(AssociatedPartition(mu),0*[1..lam[1]-mu[1]+1]);
	return Product([1..lam[1]],i->q^(mu2[i+1]*(lam2[i]-mu2[i]))*GaussianCoefficient(lam2[i]-mu2[i+1],mu2[i]-mu2[i+1],q));
end;

NrSubgroups:=function(lam,n,q) #return the number of subgroups of order q^n in the abelian group of type lam
local F,mu;
	F:=Filtered(Partitions(n),mu->Size(mu)<=Size(lam) and ForAll([1..Size(mu)],i->mu[i]<=lam[i]));
	return Sum(F,mu->HallPoly(lam,mu,q));
end;

ReducedWordSym:=function(s) #returns (a_1,...,a_l) such that the permutation is the
#product of the transpositions (a_1,a_1+1),... and l is minimal
local n,a,p;
	if Order(s)=1 then return []; fi;
	n:=LargestMovedPoint(s);
	a:=n^(s^-1);
	p:=Product([n-1,n-2..a],i->(i,i+1));
	return Concatenation([a..n-1],ReducedWordSym(p*s));
end;

PPCore:=function(G,p) #p'-core of G
local pd,F,n;
	pd:=PrimeDivisors(Size(G));
	if not p in pd then return G;
	elif pd=[p] then return TrivialSubgroup(G);
	elif Size(pd)=2 then return PCore(G,Difference(pd,[p])[1]);
	else
		F:=Filtered(NormalSubgroups(G),n->Size(n) mod p<>0);
		SortBy(F,Size);
		return F[Size(F)]; 
	fi;
end;

SubgroupComplement:=function(G,H) #return complement of H in G or fail if there is none
local buildup,builddown,epi,gen,found,com;

	buildup:=function(sg,k) #construct complements from bottom
	local x,sg2;
		#Print(k," ",Size(gen)," ",Size(sg),"\n"); #debug
		if k=Size(gen) then found:=true; com:=sg;
		else
			for x in PreImages(epi,gen[k+1]) do
				sg2:=ClosureGroup(sg,x);
				if (not found) and Size(Intersection(sg2,H))=1 then buildup(sg2,k+1); fi;
			od;
		fi;
	end;

	builddown:=function(sg) #construct complement from top
	local M;
		if Size(Intersection(sg,H))=1 then found:=true; com:=sg;
		else
			for M in MaximalSubgroups(sg) do
				if (not found) and Size(M)*Index(H,Intersection(H,M))=Size(G) then builddown(M); fi;
			od;
		fi;
	end;

	found:=false;
	if IsNormal(G,H) then
		if Gcd(Size(H),Index(G,H))=1 then return HallSubgroup(G,PrimeDivisors(Index(G,H))); fi; #Schur-Zassenhaus
		#if Size(Center(H))=1 and Size(OuterAutomorphismGroup(H))=1 then return true; fi; #Baer
		epi:=NaturalHomomorphismByNormalSubgroupNC(G,H);
		gen:=SmallGeneratingSet(Image(epi));
		buildup(TrivialSubgroup(G),0);
		if found then return com; else return fail; fi;
	else
		builddown(G);
		if found then return com; else return fail; fi;
		#return ForAny(SubgroupsC(G),x->Size(x)=n and Size(Intersection(x,H))=1); #needs memory
	fi;
end;

PLength:=function(G,p)
local N;
	if not IsPSolvable(G,p) then return fail; fi;
	if Size(G) mod p<>0 then return 0; fi;
	N:=PPCore(G,p);
	if Size(N)>1 then return PLength(G/N,p); else return 1+PLength(G/PCore(G,p),p); fi;
end;

FusionNumber:=function(ct,p,b) #fusion number of b-th p-block
local pb,pos,M,F,d,ed,ed2,i,j;
	pb:=PrimeBlocks(ct,p);
	pos:=Positions(pb.block,b);
	M:=MutableCopyMatrix(Irr(ct){pos});;
	M:=MutableCopyMatrix(TransposedMat(M)*ComplexConjugate(M));;
	F:=Field(Union(M));
	d:=DegreeOverPrimeField(F); #form union of Galois conjugate blocks
	for i in [1..Size(M)] do
		for j in [1..Size(M)] do
			M[i][j]:=Trace(F,Rationals,M[i][j]);
		od;
	od;
	ed:=ElementaryDivisorsPPartRkExp(M,p,d*Size(pos),pb.defect[b]);
	ed2:=[]; ed2[1]:=d*Size(pos)-ed[1];
	for i in [1..Size(ed)-1] do ed2[i+1]:=ed[i]-ed[i+1]; od;
	ed2[Size(ed)+1]:=ed[Size(ed)];
	return Sum([1..Size(ed2)],i->ed2[i]*p^(1-i))/d;
end;

PrimIdem:=function(G,p)
#p prime, G p-solvable group, F splitting field of G of characteristic p
#returns pairwise orthogonal representatives for the primitive idempotents in FG up to conjugation 
local ct,preg,elG,H,q,repH,R,emb,elH,elHC,idem,phi,chi,theta,e_t,D,M,id,c,d,s,e,chars;
	if not IsPSolvable(G,p) then Error(G," must be ",p,"-solvable"); fi;
	ct:=CharacterTable(G);
	preg:=PositionsProperty(OrdersClassRepresentatives(ct),x->x mod p<>0); #p-reg elements
	elG:=ElementsC(G);
	H:=SylowComplement(G,p);
	q:=p^OrderMod(p,Exponent(H));
	repH:=IrreducibleRepresentations(H);
	R:=GroupRing(GF(q),G);
	emb:=Embedding(G,R);
	elH:=Elements(H);
	elHC:=ElementsC(H);
	idem:=[];
	chars:=[];
	for phi in Irr(ct mod p) do
		chi:=First(Irr(ct),c->c{preg}=phi); #lift Brauer character by Fong-Swan
		theta:=First(ConstituentsOfCharacter(RestrictedClassFunction(chi,H)),x->x[1]=PPN(chi[1],p)); #Fong char
		Add(chars,theta);
		e_t:=Sum(H,h->FrobeniusCharacterValue(h^theta,p)*h^emb)/Size(H); #central primitive idempotent
		D:=First(repH,d->ForAll(elHC,x->Trace(x^d)=x^theta)); #rep of phi
		M:=List(elH,h->List(Flat(h^D),x->FrobeniusCharacterValue(x,p)));
		id:=[1..theta[1]^2]*Zero(GF(p));
		id[1]:=Z(p)^0;
		s:=SolutionMat(M,id); #one preimage out of many
		e:=e_t*Sum([1..Size(H)],i->s[i]*elH[i]^emb);
		Add(idem,e);
	od;
	return rec(groupring:=R, embedding:=emb, idempotents:=idem, characters:=chars);
end;

kGVnumbers:=function(G,p)
#G = P:H where P is a normal Sylow p-subgroup, F splitting field for G of char p
#returns list of triples [d,e,z] where d is dim of simple FG-module (FH-module),
#e is a primitive idempotent of the corresponding PIM and z=dim eZ(FG)e
local H,q,R,gen,emb,elH,ctH,repH,res,idem,psi,e_t,D,M,id,s,e,i,x,d,h;
	H:=SylowComplement(G,p);
	q:=p^OrderMod(p,Exponent(H));
	R:=GroupRing(GF(q),G);
	gen:=Basis(Center(R));
	emb:=Embedding(G,R);
	elH:=Elements(H);
	ctH:=CharacterTable(H);
	repH:=IrreducibleRepresentations(H);
	res:=[];
	for psi in Irr(ctH) do
		e_t:=Sum(H,h->FrobeniusCharacterValue(h^psi,p)*h^emb)/Size(H); #central primitive idempotent
		D:=First(repH,d->ForAll(elH,x->Trace(x^d)=x^psi)); #rep of phi
		M:=List(elH,h->List(Flat(h^D),x->FrobeniusCharacterValue(x,p)));
		id:=[1..psi[1]^2]*Zero(GF(p));
		id[1]:=Z(p)^0;
		s:=SolutionMat(M,id); #one preimage out of many
		e:=e_t*Sum([1..Size(H)],i->s[i]*elH[i]^emb);
		Add(res,[psi[1],e,Dimension(Subspace(R,e*gen*e))]);
	od;
	return res;
end;

IsFrobeniusGroup:=function(G)
local N;
	N:=FittingSubgroup(G);
	if Size(N) in [1,Size(G)] or Gcd(Size(N),Index(G,N))>1 then return false; fi;
	if NrConjugacyClasses(G)=NrConjugacyClasses(G/N)+(NrConjugacyClasses(N)-1)/Index(G,N) then return true; else return false; fi;
end;

#might be easier: epi:=EpimorphismSchurCover(L); G:=SemidirectProduct(Source(epi),epi,D);
UsamiPuig:=function(L)
#Usami-Puig method for blocks B with abelian defect group D, inertial quotient E and L = D:E
local F,p,epi,LS,d,D,Qs,Q,E,H,ct,preg,pb,b,IrrB0,A,a,C,sv,pos,vec,CE,k,ort,sol,i,c;
	F:=FittingSubgroup(L);
	if not (Centralizer(L,F)=F and IsPGroup(F)) then Error("Input must have an abelian, normal, selfcentralizing Sylow subgroup"); fi;
	if F=L then return true; fi; #nilpotent block
	p:=PrimePGroup(F);
	epi:=EpimorphismSchurCover(L,Difference(PrimeDivisors(Size(L)),[p])); 
	LS:=Source(epi); #p'-Schur cover
	LS:=Image(IsomorphismPermGroup(LS)); #PermGroup is faster
	D:=SylowSubgroup(LS,p); #defect group
	Qs:=[];
	for Q in List(Orbits(LS,AllSubgroups(D)),Representative) do
		if IsCyclic(D/Q) and Normalizer(LS,Q)=Centralizer(LS,Q) then continue; fi; #E acts trivially on IBr
		E:=Normalizer(LS,Q)/Centralizer(LS,D);
		if Size(E)>4 and IdGroup(E)<>[6,1] and (p>2 or Size(E)>7) then Add(Qs,Q); fi; #UP+Sambale
	od;
	for Q in Qs do
		H:=Centralizer(LS,Q)/Q;
		ct:=CharacterTable(H);
		d:=Valuation(Size(H),p);
		preg:=PositionsProperty(OrdersClassRepresentatives(ct),i->i mod p<>0); #p-regular classes
		pb:=PrimeBlocks(ct,p);
		for b in [1..Size(pb.defect)] do
			IrrB0:=Irr(ct){Positions(pb.block,b)}{preg};
			A:=TransposedMat(NullspaceIntMat(IntegralizedMat(IrrB0).mat)); #ZIrr^0
			if Normalizer(LS,Q)<>Centralizer(LS,Q) and ForAny(Combinations(A,2),a->a[1] in [a[2],-a[2]]) then #solution not unique
				Print(Size(Q)," ",b,"\n"); 
				return false; 
			fi;
			CE:=Centralizer(LS,Q)/Centralizer(LS,D);
			if IsCyclic(D/Q) or Size(CE)<5 or IdGroup(CE)=[6,1] or (p=2 and Size(CE)<8) then continue; fi; #Delta unique or E acts trivial
			C:=TransposedMat(A)*A;;
			sv:=ShortestVectors(p^d*C^-1,p^d-1); #rows for Lemma
			pos:=PositionsProperty(sv.norms,x->x mod p<>0); #apply Lemma
			vec:=sv.vectors{pos};
			ort:=OrthogonalEmbeddingsNEW(C,rec(vectors:=vec)); #Plesken's algorithm
			sol:=ort.solutions;
			if Size(sol)>1 then Print(Size(Q)," ",b," ",List(sol,Size),"\n"); return false; fi;
		od;
	od;
	return true;
end;

Binomial2:=function(n,k) #n any complex number
	return Product([1..k],i->(n-i+1)/i); 
end;

Number2Latex:=function(n)
local c,s,p;
	if not IsInt(n) then Error(n," must be an integer"); fi;
	if n in [0,1] then return String(n); fi;
	if n<0 then return Concatenation("-",Number2Latex(-n)); fi;
	c:=Collected(FactorsInt(n));
	s:="";
	for p in [1..Size(c)] do
		if c[p][2]>1 then	s:=Concatenation(s,String(c[p][1]),"^{",String(c[p][2]),"}"); else Append(s,String(c[p][1])); fi;
		if p<Size(c) then Append(s,"\\cdot"); fi;
	od;
	return s;
end;

EDchar:=function(ct)
local f,S,x,c;
	f:=ClassFunction(ct,List(SizesCentralizers(ct),x->x^-1));
	S:=List(Irr(ct),c->ScalarProduct(c,f));
	return Lcm(List(S,DenominatorRat));
end;

EDchar2:=function(ct)
local f,x;
	f:=List(SizesConjugacyClasses(ct),x->x^2);
	return Gcd(List(Irr(ct),x->List(x)*f));
end;
#EDchar2:=function(ct)
#local f,S,c;
	#f:=Size(ct)*ClassFunction(ct,SizesConjugacyClasses(ct));
	#S:=List(Irr(ct),c->ScalarProduct(c,f));
	#return Gcd(S);
#end;

PrintMoebiusValues:=function(G) #G can be a group of a string like "M11"
local tom,MT,i,H;
	tom:=TableOfMarks(G);;
	MT:=MoebiusTom(tom);;
	Print(["Subgroup H","|H|","mu(H,G)"],"\n");
	for i in [1..Size(MT.mu)] do
		H:=RepresentativeTom(tom,i);
		if not IsBound(MT.mu[i]) then
			Print([H,Size(H),0],"\n");
		else
			Print([H,Size(H),MT.mu[i]],"\n");
		fi;
	od;
end;

MoebiusFunction:=function(H,G)
#compute \mu(H,G) for finite groups H\le G where \mu is the Moebius function of the subgroup lattice
local tom,MT,n,k;
	tom:=TableOfMarks(G);;
	MT:=MoebiusTom(tom);;
	n:=Size(MT.mu);
	k:=First([1..n],i->IsConjugate(G,H,RepresentativeTom(tom,i)));
	if not IsBound(MT.mu[k]) then return 0; else return MT.mu[k]; fi;
end;

IsPiSeparable:=function(G,pi)
local cs,pi2;
	cs:=CompositionSeries(G);
	pi2:=Difference(PrimeDivisors(Size(G)),pi);
	return ForAll([1..Size(cs)-1],i->Gcd(Index(cs[i],cs[i+1]),Product(pi))=1 or Gcd(Index(cs[i],cs[i+1]),Product(pi2))=1);
end;


PI:=function(G,p,n) #perfect isometry group of n-th p-block of G, p>2
local ct,pb,B,kB,char,sign,preg,psin,PItest,heights,S,pdeg,L,W,f,g,h;
	if IsCharacterTable(G) then ct:=G; else ct:=CharacterTable(G); fi;
	pb:=PrimeBlocks(ct,p);
	B:=Positions(pb.block,n);
	kB:=Size(B);
	if kB=1 then return Group(()); fi;
	char:=Irr(ct){B};

	sign:=function(g) #signs of a PI such that first sign is +1, requires p>2
	local h,rat,i;
		h:=0*[1..kB]+1;
		rat:=(PPN(char[1^g][1],p)/PPN(char[1][1],p)) mod p;
		#if not rat in [1,p-1] then Info(InfoWarning,1,"Counterexample!!! ",ct," ",p," ",n); fi;
		for i in [2..kB] do 
			if (PPN(char[i^g][1],p)/PPN(char[i][1],p)) mod p<>rat then h[i]:=-1; fi; 
		od;
		return h;
	end;
	
	preg:=PositionsProperty(OrdersClassRepresentatives(ct),x->x mod p<>0); #p-regular elements
	psin:=Difference([1..NrConjugacyClasses(ct)],preg); #p-singular elements
	
	PItest:=function(g) #check if permutation g induces PI
	local h;
		h:=sign(g);
		if not ForAll(preg,x->ForAll(psin,y->Sum([1..kB],i->char[i][x]*h[i]*char[i^g][y])=0)) then return false; fi; #(sep)
		if not ForAll(psin,x->ForAll(psin,y->IsIntegralCyclotomic(Sum([1..kB],i->char[i][x]*h[i]*char[i^g][y])/PPart(SizesCentralizers(ct)[x],p)) and IsIntegralCyclotomic(Sum([1..kB],i->char[i][x]*h[i]*char[i^g][y])/PPart(SizesCentralizers(ct)[y],p)))) then return false; fi; #(int')
		return true;
	end;
	
	heights:=pb.height{B};
	S:=DirectProduct(List(Set(heights),h->SymmetricGroup(Positions(heights,h)))); #PIs perserve character heights
	if p>3 then 
		pdeg:=Set([1..(p-1)/2],i->Filtered([1..kB],c->PPN(char[c][1],p) mod p in [i,p-i]));
		pdeg:=Filtered(pdeg,c->c<>[]);
		S:=Stabilizer(S,pdeg,OnSetsDisjointSets); #Isaacs-Navarro congruences are preserved
	fi;
	
	if Size(S)>10^10 then Info(InfoWarning,1,"permutation group has order ",Size(S)); fi;
	#if Size(S)>10^7 then return fail; fi;
	#if Size(S)>10^7 then Error("permutation group is too big ",Size(S)); fi;
	
	S:=SubgroupProperty(S,PItest); #magic :-)
	
	if Size(S)=1 then return S; fi;
	W:=WreathProduct(Group((1,2)),S); #embed PI into C2 wr S_kB
	f:=Embedding(W,NrMovedPoints(S)+1);
	L:=[Product([1..NrMovedPoints(S)],i->(2*i-1,2*i))]; #-id in PI(B)
	for g in GeneratorsOfGroup(S) do
		h:=sign(g){MovedPoints(S)}; #extract relevant signs
		Add(L,Product([1..NrMovedPoints(S)],i->(2*i-1,2*i)^((1-h[i])/2))*g^f);
	od;	
	return Group(L);
end;

SemidihedralGroup:=function(n)
local p,q;
if (not IsPrimePowerInt(n)) or (n mod 2=1) or (n<16) then Error(n," must be a power of 2 and at least 16!"); fi;
p:=[2..n/2];
Add(p,1);
p:=PermList(p);
q:=Cycle(p^(-1+n/4),[1..n/2],1);
q:=PermList(q);
return Group([p,q]);
end;

OrderpSubgroups:=function(G) #returns set of subgroups of order p of p-group G up to conjugacy
local p,F,L,Q;
	p:=PrimePGroup(G);
	F:=Filtered(ElementsC(G),x->Order(x)=p);
	L:=[];
	while F<>[] do
		Q:=Subgroup(G,[F[1]]);
		Add(L,Q);
		F:=Difference(F,Q);
	od;
	return L;
end;

CoveredBlocks:=function(ct,p,i,ctN) #positions of blocks of N covered by the i-th p-block of G
local pb,pbN,chi,rest,phi;
pb:=PrimeBlocks(ct,p);
pbN:=PrimeBlocks(ctN,p);
chi:=Irr(ct)[Position(pb.block,i)];
rest:=RestrictedClassFunction(chi,ctN);
return Set(ConstituentsOfCharacter(rest),phi->pbN.block[Position(Irr(ctN),phi)]);
end;

CoveredByBlocks:=function(ctN,p,i,ct) #positions of blocks of G covering the i-th p-block of N
local pb,pbN,chi,rest,phi;
pb:=PrimeBlocks(ct,p);
pbN:=PrimeBlocks(ctN,p);
chi:=Irr(ctN)[Position(pbN.block,i)];
rest:=InducedClassFunction(chi,ct);
return Set(ConstituentsOfCharacter(rest),phi->pb.block[Position(Irr(ct),phi)]);
end;

DefectGroupNew:=function(G,ct,p,b)
#returns a defect group of the b-th p-block of G (with character table ct)
local pb,d,IrrB,e,supp,c,C;
	if b=1 then return SylowSubgroup(G,p); fi; #principal block
	pb:=PrimeBlocks(ct,p);
	if b>Size(pb.defect) then Error("Block does not exist!"); fi;
	d:=pb.defect[b];
	if d=0 then return TrivialSubgroup(G); fi;
	if d=pb.defect[1] then return SylowSubgroup(G,p); fi; #maximal defect
	IrrB:=Irr(ct){Positions(pb.block,b)};
	e:=Sum(IrrB,c->c[1]*c)/PPart(Size(G),p); #coefficients of block idempotent in O, more or less
	supp:=PositionsProperty(e,x->not IsIntegralCyclotomic(x/p)); #non-zero coefficients in F
	c:=First(ConjugacyClasses(ct){supp},x->Valuation(Size(x),p)+d=pb.defect[1]); #defect class
	C:=Centralizer(G,Representative(c)); 
	return SylowSubgroup(C,p); 
end;

BrauerFMT:=function(G,ct,p,b)
#returns [D,ctN,c] where D is a defect group, ctN the character table of N_G(D) and c the label of the Brauer's first main correspondent of b-th p-block of G
local pb,irrB,D,N,ctN,pbN,c,psi,s,chi;
	pb:=PrimeBlocks(ct,p);
	irrB:=Irr(ct){Positions(pb.block,b)};
	D:=DefectGroupNew(G,ct,p,b);
	N:=Normalizer(G,D);
	ctN:=CharacterTable(N);
	pbN:=PrimeBlocks(ctN,p);
	for c in [1..Size(pbN.defect)] do
		if pbN.defect[c]<>pb.defect[b] then continue; fi;
		psi:=Irr(ctN)[Position(pbN.block,c)];
		s:=Sum(irrB,chi->chi[1]*ScalarProduct(RestrictedClassFunction(chi,N),psi)); #[Navarro,6.4]
		if PPart(s,p)=PPart(Index(G,N)*psi[1],p) then return [D,ctN,c]; fi;
	od;
end;

CyclicDefectGroup:=function(ct,p,b) #returns if b-th p-block of ct has cyclic defect group
local pb,d,irrB,Qpp,deg,c;
	pb:=PrimeBlocks(ct,p);
	d:=pb.defect[b];
	if d<2 then return true; fi;
	Qpp:=CF(PPN(Size(ct),p));
	irrB:=Irr(ct){Positions(pb.block,b)};
	for c in irrB do
		deg:=DegreeOverPrimeField(Intersection(Qpp,Field(c)));
		if (DegreeOverPrimeField(Field(c))/deg) mod p^(d-1) = 0 then return true; fi;
	od;
	return false;
end;

IsTameBlock:=function(ct,b) #returns if b-th 2-block of ct is tame
local pb,d,pos,z,w,F;
	pb:=PrimeBlocks(ct,2);
	d:=pb.defect[b];
	if d<2 then return false; fi;
	if d=2 then return not CyclicDefectGroup(ct,2,b); fi;
	pos:=Positions(pb.block,b);
	if Size(pos)>=2^d then return false; fi; #abelian defect
	z:=E(2^(d-1));
	w:=E(PPN(Size(ct),2)); #odd part of |G|
	F:=Field(Concatenation(Union(Irr(ct){pos}),[w]));
	return Intersection(F,Field(z)) in [Field(z+z^-1),Field(z-z^-1)];
end;

CanonicalCharacter:=function(G,ct,p,b)
#returns [D,theta] where D is a defect group and theta is a canonical character in DC_G(D) of the b-th p-block of G
local fmt,D,N,ctN,DC,ctD,c,pbD,irrc,can;
	fmt:=BrauerFMT(G,ct,p,b);
	D:=fmt[1];
	N:=Normalizer(G,D);
	ctN:=fmt[2];
	DC:=ClosureGroup(Centralizer(G,D),D);
	ctD:=CharacterTable(DC);
	c:=CoveredBlocks(ctN,p,fmt[3],ctD)[1];
	pbD:=PrimeBlocks(ctD,p);
	irrc:=Irr(ctD){Positions(pbD.block,c)};
	can:=First(irrc,psi->IsSubset(KernelOfCharacter(psi),D));
	return [D,can];
end;

Subsection:=function(G,ct,x,B) #returns [ctC,c] where ctC is the character table of C_G(x) and c the number of the block b such that (x,b) is a B-subsection
local p,pb,irrB,cent,ctC,pbC,c,psi,s;
	p:=PrimeDivisors(Order(x))[1];
	pb:=PrimeBlocks(ct,p);
	irrB:=Irr(ct){Positions(pb.block,B)};
	cent:=Centralizer(G,x);
	ctC:=CharacterTable(cent);
	pbC:=PrimeBlocks(ctC,p);
	for c in [1..Size(pbC.defect)] do
		psi:=Irr(ctC)[Position(pbC.block,c)];
		s:=Sum(irrB,chi->chi[1]*ScalarProduct(RestrictedClassFunction(chi,ctC),psi)); #[Navarro,6.4]
		if PPart(s,p)=PPart(Index(G,cent)*psi[1],p) then return [ctC,c]; fi;
	od;
end;


InertialQuotient:=function(G,ct,p,b)
#returns N_G(D,b_D) where D is a defect group and b_D a Brauer correspondent of b-th p-block of G
local can,D;
	can:=CanonicalCharacter(G,ct,p,b);
	D:=can[1];
	return Stabilizer(Normalizer(G,D),can[2]);
end;
  
ExtendedDefectGroup:=function(G,ct,b) #returns [D,E] where D is a defect group and E is an extended defect group of real 2-block with label b
local P,pb,chi,IrrB,e,supp,cc,c,C,x,g,Ex;
	if b=1 then P:=SylowSubgroup(G,2); return [P,P]; fi; #principal block
	pb:=PrimeBlocks(ct,2);
	if b>Size(pb.defect) then Error("Block does not exist!"); fi;
	IrrB:=Irr(ct){Positions(pb.block,b)};
	chi:=IrrB[1];
	if not ComplexConjugate(chi) in IrrB then Error("Block is not real!"); fi;
	e:=Sum(IrrB,c->c[1]*c)/PPart(Size(G),2); #coefficients of block idempotent in O, more or less
	supp:=PositionsProperty(e,x->not IsIntegralCyclotomic(x/2)); #non-zero coefficients in F
	cc:=ConjugacyClasses(ct){supp};
	c:=First(cc,x->Representative(x)^-1 in x and (not IsIntegralCyclotomic(Representative(x)^chi*Size(x)/chi[1]/2))); #real defect class, [Murray, Prop. 14]
	x:=Representative(c);
	C:=SubgroupByProperty(Normalizer(G,Subgroup(G,[x])),g->x^g in [x,x^-1]); #extended centralizer
	Ex:=SylowSubgroup(C,2);
	return [Intersection(Ex,Centralizer(G,x)),Ex];
end;

LowerDefectGroups:=function(G,ct,p,b) #returns list of lower defect groups with multiplicities of the b-th p-block of G (with character table ct)
local pb,IrrB,cc,el,gen,K,L,c,i,F,d,subs,def,pos,x,Q,cl,mQ,LD;
	pb:=PrimeBlocks(ct,p);
	if b>Size(pb.defect) then Error("Block does not exist!"); fi;
	IrrB:=Irr(ct){Positions(pb.block,b)};
	cc:=ConjugacyClasses(ct);	
	el:=List(cc,Representative);
	gen:=List(cc,K->List(cc,L->Size(K)*Sum(IrrB,c->c[Position(cc,K)]*ComplexConjugate(c[Position(cc,L)]))))/Size(ct);
	F:=Field(Union(gen));
	d:=DegreeOverPrimeField(F); 
	#if d>1 then Print("Number of Galois conjugates: ",d,"\n"); fi; #debug info
	gen:=List(gen,c->List(c,i->Trace(F,Rationals,i)))*One(GF(p)); #sum of Galois conjugate blocks
	cl:=Filtered([1..Size(el)],i->ForAny(gen,c->c[i]<>Zero(GF(p)))); #relevant classes
	gen:=BaseMat(gen{[1..Size(gen)]}{cl}); #basis of Z(B)
	def:=List(el{cl},x->SylowSubgroup(Centralizer(G,x),p)); #potential lower defect groups
	subs:=Set(def,Q->ConjugacyClassSubgroups(G,Q)); #...up to G-conjugation
	SortBy(subs,x->Size(Representative(x))); #ordered by increasing size
	LD:=[];
	for Q in subs do
		pos:=PositionsProperty(def,c->ForAny(Q,x->IsSubset(x,c)));
		K:=IdentityMat(Size(cl)){pos}*One(GF(p));
		mQ:=Size(SumIntersectionMat(gen,K)[2]); #dim Z(B)\cap I_Q
		pos:=Filtered(pos,c->Size(def[c])<Size(Representative(Q))); 
		if pos<>[] then 
			K:=IdentityMat(Size(cl)){pos}*One(GF(p)); #I_<Q
			mQ:=mQ-Size(SumIntersectionMat(gen,K)[2]);
		fi;
		if mQ>0 then Add(LD,[Representative(Q),mQ/d]); fi;
	od;
	return LD;
end;

LDorders:=function(ct,p,b) #orders of lower defect groups
local pb,pos,M,F,d,ed,ed2,i,j;
	pb:=PrimeBlocks(ct,p);
	pos:=Positions(pb.block,b);
	M:=MutableCopyMatrix(Irr(ct){pos});;
	M:=MutableCopyMatrix(TransposedMat(M)*ComplexConjugate(M));;
	F:=Field(Union(M));
	d:=DegreeOverPrimeField(F); #form union of Galois conjugate blocks
	for i in [1..Size(M)] do
		for j in [1..Size(M)] do
			M[i][j]:=Trace(F,Rationals,M[i][j]);
		od;
	od;
	ed:=ElementaryDivisorsPPartRkExp(M,p,d*Size(pos),pb.defect[b]);
	ed2:=[]; ed2[1]:=d*Size(pos)-ed[1];
	for i in [1..Size(ed)-1] do ed2[i+1]:=ed[i]-ed[i+1]; od;
	ed2[Size(ed)+1]:=ed[Size(ed)];
	return Concatenation(List([1..Size(ed2)],i->[1..ed2[i]/d]*0+p^(i-1)));
end;

NrMoritaClasses:=function(p,w) #returns upper bound for the number of Morita equivalence classes of p-blocks of symmetric groups with weight w
	return Binomial(w*p,p-1)/2/p+Binomial(Int(w*p/2),Int(p/2))/2;
end;

RoCKBlockN:=function(p,w) #returns n such that the p-RoCK block of weight w belongs to S_n
	return p*((w-1)^2*p*(p^2-1)+2*(w-1)*p^2+22*w+2)/24;
end;

NrIrr:=function(p,w) #returns the number of irreducible ordinary characters in a p-block of weight w
local part;
	return Sum(Partitions(w),part->Product(part,NrPartitions)*NrPermutationsList(part)*Binomial(p,Size(part)));
end;

NrIBr:=function(p,w) #returns the number of irreducible Brauer characters in a p-block of weight w
local part;
	return Sum(Partitions(w),part->Product(part,NrPartitions)*NrPermutationsList(part)*Binomial(p-1,Size(part)));
end;

#EnumerateAbaci:=function(L,p,w) #auxiliary (recursive) function to enumerate abaci
#local L2,i,a;
	#if L=[] then L:=List([0..w-1],i->[i]); return EnumerateAbaci(L,p,w); fi;
	#if Size(L[1])=p-1 then return L; fi;
	#L2:=[];
	#for a in L do
		#Append(L2,List([0..a[Size(a)]+w-1],i->Concatenation(a,[i])));
	#od;
	#return EnumerateAbaci(L2,p,w);
#end;

#ScopesCores:=function(p,w) #returns representatives of the Scope cores of p-blocks with weight w without conjugate cores
#local L,cores,a,part,l,i;
	#L:=EnumerateAbaci([],p,w); #list of core abaci
	#cores:=[]; #list of cores
	#for a in L do #construct partition from abacus a
		#part:=[];
		#l:=0; #initial length of partition part
		#for i in [1..(p-1)*p*(w-1)-1] do #possible first hook lengths
			#if i mod p<>0 and a[RemInt(i,p)]>Int(i/p) then 
				#Add(part,i-l); 
				#l:=l+1;
			#fi;
		#od;
		#part:=Reversed(part);
		#if part=[] or (not AssociatedPartition(part) in cores) then AddSet(cores,part); fi;
	#od;
	#SortBy(cores,Sum);
	#return cores;
#end;

#PartitionsWithCore:=function(p,core,w) #returns partitions with given core and weight
	#return Reversed(SortedList(List(PartitionTuples(w,p),lam->CombineEQuotientECore(p,lam,core))));
#end;	

#HookLengths:=function(part) #returns list of hook lengths for each box in Young diagram
#local hl,part2,i,j;
	#if part=[] then return []; fi;
	#hl:=[];
	#part2:=AssociatedPartition(part);
	#for i in [1..Size(part)] do
		#hl[i]:=[];
		#for j in [1..part[i]] do
			#hl[i][j]:=part[i]+part2[j]-i-j+1;
		#od;
	#od;
	#return hl;
#end;

#partial:=function(p,part) #return difference of leg lengths of (two) p-hooks
#local hl,i,j,k,l,hlm,mu,leg1,leg2;
	#if EWeight(p,part)<>2 then Error(part," has not ",p,"-weight 2"); fi;
	#hl:=HookLengths(part);
	#for i in [1..Size(part)] do
		#for j in [1..part[i]] do
			#if hl[i][j]=p then 
				#leg1:=p-part[i]+j; 
				#mu:=RemoveRimHook(part,i,j);
				#hlm:=HookLengths(mu);
				#for k in [1..Size(mu)] do
					#for l in [1..mu[k]] do
						#if hlm[k][l]=p then 
							#leg2:=p-mu[k]+l; 
							#return AbsInt(leg1-leg2);
						#fi;
					#od;
				#od;
			#fi;
		#od;
	#od;
#end;

#DecMatWeight2:=function(p,core) #returns decomposition matrix of p-block with given core and weight 2<p (Richards' algorithm)
#local B,regB,i,j,dec;
	#if p=2 or not IsPrimeInt(p) then Error(p," is not an odd prime"); fi;
	#if not IsECore(p,core) then Error(core," is not a ",p,"-core"); fi;
	#B:=PartitionsWithCore(p,core,2); #ordinary characters in decreasing lexicographical order
	#regB:=Filtered(B,part->IsERegular(p,part)); #Brauer characters
	#B:=Concatenation(regB,Difference(B,regB)); #relabel to get unitriangular shape
	#dec:=[];
	#for i in [1..Size(B)] do
		#dec[i]:=[];
		#for j in [1..Size(regB)] do
			#if B[i]=regB[j] or B[i]=AssociatedPartition(MullineuxMap(p,regB[j])) then dec[i][j]:=1; 
			#elif Dominates(regB[j],B[i]) and Dominates(B[i],AssociatedPartition(MullineuxMap(p,regB[j]))) and AbsInt(partial(p,B[i])-partial(p,regB[j]))=1 then dec[i][j]:=1;
			#else dec[i][j]:=0; fi;
		#od;
	#od; 
	#return dec;
#end;

#PSign:=function(p,part) #returns the p-sign of the partition part
#local s,hl,a,perm,z,i;
	#s:=Size(part);
	#hl:=List([0..s-1],i->part[s-i]+i); #first colum hook length = beta-set
	#a:=List([0..p-1],i->Filtered(hl,x->x mod p=i)); #abacus upslided
	#perm:=[];
	#z:=0;
	#while Size(perm)<s do
		#if IsBound(a[(z mod p)+1][Int(z/p)+1]) then Add(perm,a[(z mod p)+1][Int(z/p)+1]); fi;
		#z:=z+1;
	#od;
	#return SignPerm(MappingPermListList(hl,perm));
#end;

##replacement for CombineEQuotientCore which has a minor bug
#CoreQuotient2Partition:=function(p,core,quot) #returns partition with given p-core and p-quotient
#local s,hl,w,d,beta,a,b,i,j,x,abacus;
	#if not IsECore(p,core) then Error(core," is not a ",p," core"); fi;
	#s:=Size(core);
	#hl:=List([1..s],i->core[i]+s-i); #first column hook lengths
	#w:=Maximum(List(quot,Size)); #maximal number of beads on runners
	#d:=p*w+((-s) mod p);
	#beta:=hl+List(hl,i->d); #construct beta-size of large enough size = 0 (mod p)
	#for i in [1..d] do Add(beta,d-i); od; 
	#a:=List([0..p-1],i->Number(beta,x->x mod p=i)); #count beads on runners
	#b:=List(quot,lam->List([1..Size(lam)],i->lam[i]+Size(lam)-i)); #beta-set from quot
	#for i in [1..p] do 
		#d:=a[i]-Size(b[i]);
		#b[i]:=b[i]+List(b[i],j->d); #make beta-set b[i] long enough
		#for j in [1..d] do Add(b[i],d-j); od;
	#od;
	#abacus:=Union(List([1..p],i->List(b[i],j->j*p+(i-1)))); #abacus of desired partition
	#return Reversed(Filtered(List([1..Size(abacus)],i->abacus[i]-i+1),i->i>0));
#end;

#JantzenSchaper:=function(p,core,w) #returns decomposition matrix of the p-block with given core and weight w<4
#local B,regB,hooks,lam,lam2,Hlam,h,pairs,c,dec,Co,i,j,k;
	#B:=PartitionsWithCore(p,core,w); 
	#regB:=Filtered(B,part->IsERegular(p,part)); 
	#hooks:=[];
	#for lam in B do
		#lam2:=AssociatedPartition(lam);
		#Hlam:=[];
		#for i in [1..Size(lam)] do
			#for j in [1..lam[i]] do
				#h:=lam[i]+lam2[j]-i-j+1;
				#if h mod p=0 then Add(Hlam,[i,j,h,(lam2[j]-i) mod 2]); fi;
			#od;
		#od;
		#Add(hooks,Hlam);
	#od;
	#Co:=NullMat(Size(B),Size(B));
	#for i in [1..Size(B)] do
		#for j in [1..i-1] do
			#pairs:=Filtered(Cartesian(hooks[i],hooks[j]),c->c[1][3]=c[2][3] and RemoveRimHook(B[i],c[1][1],c[1][2])=RemoveRimHook(B[j],c[2][1],c[2][2]));
			#Co[i][j]:=-Sum(pairs,c->(-1)^(c[1][4]+c[2][4])*Valuation(c[1][3],p));
		#od;
	#od;
	#dec:=NullMat(Size(B),Size(regB));
	#for i in [1..Size(B)] do
		#for j in [1..Size(regB)] do
			#if B[i]=regB[j] then dec[i][j]:=1; elif 
				#Sum([1..i-1],k->dec[k][j]*Co[i][k])>0 then dec[i][j]:=1;
			#fi;
		#od;
	#od;
	#return dec;
#end;

#ContribMatSym:=function(p,w,core)
#local ct,F,Q,c,x;
	#ct:=CharacterTableWreathSymmetric(CharacterTable("cyclic",p),w);
	#F:=PositionsProperty(ClassParameters(ct),c->c[1]=[]);
	#Q:=DiagonalMat(List(PartitionTuples(w,p),x->PSign(p,CombineEQuotientECore(p,x,core))))*Irr(ct){[1..NrConjugacyClasses(ct)]}{F};
	#return PPN(Size(ct),p)^-1*ComplexConjugate(Q)*DiagonalMat(SizesConjugacyClasses(ct){F})*TransposedMat(Q);
#end;

IsMetacyclic2Group:=function(G)
local H,U;
if Size(FrattiniSubgroup(G))<>Size(G)/4 or (not IsAbelian(DerivedSubgroup(G))) then return false; fi;
H:=Subgroup(G,Filtered(G,x->Order(x)<=4));
if G<>H then return IsMetacyclic2Group(H); fi;
U:=Difference(G,[Identity(G)]);
while not IsEmpty(U) do
  if IsNormal(G,Subgroup(G,[U[1]])) and IsCyclic(FactorGroup(G,Subgroup(G,[U[1]]))) then return true; fi;
  U:=Difference(U,Subgroup(G,[U[1]]));
od;
return false;
end;

IsMetacyclic:=function(G)
local U;
if IsCyclic(G) then return true; fi;
if IsPGroup(G) and PrimePGroup(G)=2 then return IsMetacyclic2Group(G); fi;
if (not IsAbelian(DerivedSubgroup(G))) then return false; fi;
U:=Difference(G,[Identity(G)]);
while not IsEmpty(U) do
  if IsNormal(G,Subgroup(G,[U[1]])) and IsCyclic(FactorGroup(G,Subgroup(G,[U[1]]))) then return true; fi;
  U:=Difference(U,Subgroup(G,[U[1]]));
od;
return false;
end;

IsBicyclic2Group:=function(G)
local M;
if RankPGroup(G)>2 then return false; fi;
M:=MaximalSubgroups(G);
if Size(Filtered(M,IsMetacyclic))=2 then return true; fi;
return false;
end;

IsBicyclic:=function(G)
local x,y,H,K,U,V;
if IsCyclic(G) then return true; fi;
if IsPGroup(G) and PrimePGroup(G)=2 then return IsBicyclic2Group(G); fi;
U:=Difference(G,[Identity(G)]);
while not IsEmpty(U) do
x:=U[1];
H:=Subgroup(G,[x]);
V:=Difference(U,H);
while not IsEmpty(V) do
y:=V[1];
K:=Subgroup(G,[y]);
if Size(H)*Size(K)/Size(Intersection(H,K))=Size(G) then return true; fi;
V:=Difference(V,K);
od;
U:=Difference(U,H);
od;
return false;
end;

IsMinimalNonabelian:=function(G)
if IsAbelian(G) then return false; fi;
#if Size(FrattiniSubgroup(G))<>Size(G)/4 or Size(DerivedSubgroup(G))<>2 then return false; fi;
return ForAll(MaximalSubgroupClassReps(G),IsAbelian);
end;

MNA:=function(r,s,p)
local A,B,gen,a,Aut,phi,G;
A:=AbelianGroup([p^r,p]);
B:=CyclicGroup(p^s);
gen:=GeneratorsOfGroup(A);
a:=GroupHomomorphismByImagesNC(A,A,gen,[gen[1]*gen[2],gen[2]]);
Aut:=AutomorphismGroup(A);
phi:=GroupHomomorphismByImagesNC(B,Aut,[B.1],[a]);
G:=SemidirectProduct(B,phi,A);
return G;
end;

#F:=FreeGroup("x","y");
#G:=F/[F.x^(p^r),F.y^(p^s),Comm(F.x,F.y)^p,Comm(Comm(F.x,F.y),F.x),Comm(Comm(F.x,F.y),F.y)];
#return Image(IsomorphismPermGroup(G));
#end;

CentralProductDefault:=function(G,H)
local ZG,ZH,f,iso,D,p,q,S,epi;
ZG:=Center(G);
ZH:=Center(H);
f:=IsomorphismGroups(ZG,ZH);
if f=fail then Error("centers are not isomorphic"); fi;
D:=DirectProduct(G,H);
p:=Embedding(D,1);
q:=Embedding(D,2);
S:=Subgroup(D,List(GeneratorsOfGroup(ZG),g->g^p*g^(f*q)));
epi:=NaturalHomomorphismByNormalSubgroupNC(D,S);
return [Image(epi),Image(p*epi),Image(q*epi)];
end;

#CentralProductOld:=function(arg)
#local G,H,D,f,f1,f2,S,g,M;
#if Length(arg)=1 and IsList(arg[1]) then arg:=arg[1]; fi;
#if Length(arg)=0 then return TrivialGroup(); fi;
#if Length(arg)=1 then return arg[1]; fi;
#G:=arg[1];
#H:=arg[2];
#D:=DirectProduct(G,H);
#f:=IsomorphismGroups(Center(G),Center(H));
#if f=fail then 
	#if IsPGroup(Center(G)) and IsCyclic(Center(H)) then
		#f:=IsomorphismGroups(Center(G),Filtered(AllSubgroups(Center(H)),M->Size(M)=Size(Center(G)))[1]);
		#if f=fail then Error("Centers are not compatible"); fi;
	#else
		#f:=IsomorphismGroups(Filtered(AllSubgroups(Center(G)),M->Size(M)=Size(Center(H)))[1],Center(H));
		#if f=fail then Error("Centers are not compatible"); fi;
	#fi;
#fi;
#f1:=Embedding(D,1);
#f2:=Embedding(D,2);
#S:=Set(Center(G),g->g^(f1)*(g^(-1))^(f*f2));
#Remove(arg,1);
#arg[1]:=FactorGroup(D,Subgroup(D,S));
#return CentralProduct(arg);
#end;

AllNondirectCentralProducts:=function(G,H) #returns triples (G*H,G,H) where G*H is not of the form GxK with K\le H
local ZG,ZH,exp,AG,AH,SG,SH,D,eG,eH,CPs,WG,WH,f,S,epi,g;
	ZG:=Center(G);
	ZH:=Center(H);
	exp:=Gcd(Exponent(ZG),Exponent(ZH));
	if exp=1 then return []; fi; #only GxH possible
	ZG:=Kernel(GroupHomomorphismByFunction(ZG,ZG,x->x^exp)); #Subgroup(ZG,Filtered(ZG,x->x^exp=One(G)));
	ZH:=Kernel(GroupHomomorphismByFunction(ZH,ZH,x->x^exp)); #Subgroup(ZH,Filtered(ZH,x->x^exp=One(H)));
	SG:=Filtered(AllSubgroups(ZG),z->SubgroupComplement(G,z)=fail);
	SH:=Filtered(AllSubgroups(ZH),z->SubgroupComplement(H,z)=fail);
	AG:=AutomorphismGroup(G);
	AH:=AutomorphismGroup(H);
	SG:=List(OrbitsDomain(AG,SG,{W,a}->Image(a,W)),Representative);
	SH:=List(OrbitsDomain(AH,SH,{W,a}->Image(a,W)),Representative);
	D:=DirectProduct(G,H);
	eG:=Embedding(D,1);
	eH:=Embedding(D,2);
	CPs:=[]; #list of central products
	for WG in SG do
		for WH in SH do
			for f in AllIsomorphisms(WG,WH) do
				S:=Subgroup(D,List(GeneratorsOfGroup(ZG),g->g^eG*g^(f*eH)));
				epi:=NaturalHomomorphismByNormalSubgroupNC(D,S);
				Add(CPs,[Image(epi),Image(eG*epi),Image(eH*epi)]);
			od;
		od;
	od;
	return CPs;
end;

IsPositiveDefinite:=function(M)
local p,l,i;
	if not TransposedMat(M)=M then Error("Matrix must be symmetric"); fi;
	p:=CharacteristicPolynomial(M);
	l:=CoefficientsOfUnivariatePolynomial(p);
	if ForAll([1..Size(l)-1],i->l[i]*l[i+1]<0) then return true; else return false; fi;
end;

IsPositiveSemidefinite:=function(M)
local p,l,i;
	if not TransposedMat(M)=M then Error("Matrix must be symmetric"); fi;
	p:=CharacteristicPolynomial(M);
	l:=List(CoefficientsOfUnivariatePolynomial(p));
	while l[1]=0 do Remove(l,1); od;
	if ForAll([1..Size(l)-1],i->l[i]*l[i+1]<0) then return true; else return false; fi;
end;

IsSymmetricMat:=function(M)
return M=TransposedMat(M);
end;

OuterAutomorphismGroup:=function(G)
local A;
	A:=AutomorphismGroup(G);
	return A/InnerAutomorphismsAutomorphismGroup(A);
end;

IsPNilpotent2:=function(G,p)
if AsGroup(Filtered(G,x->Order(x) mod p<>0))=fail then return false; else return true; fi;
end;

ActPerm:=function(M,g)
	return TransposedMat(Permuted(TransposedMat(Permuted(M,g)),g));
end;

PRank:=function(G)
	local f,H;
	if IsAbelian(G) then return RankPGroup(G); else
	f:=NaturalHomomorphismByNormalSubgroupNC(G,Center(G));
	return Maximum(List(Filtered(List(SubgroupsC(G/Center(G)),H->PreImage(f,H)),IsAbelian),RankPGroup)); fi;
end;

HasMaximalClass:=function(G)
	if not IsPGroup(G) then Error(G," must be a p-group!"); fi;
	if Size(FactorsInt(Size(G)))-NilpotencyClassOfGroup(G)=1 then return true; else return false; fi;
end;
	
Gamma1:=function(G)
	local LC,f;
	if not HasMaximalClass(G) then Error(G, "must be a p-group of maximal class!"); fi;
	LC:=LowerCentralSeries(G);
	f:=NaturalHomomorphismByNormalSubgroupNC(G,LC[4]);
	return PreImage(f,Centralizer(G/LC[4],Image(f,LC[2])));
end;

IsExceptionalGroup:=function(G)
	local n;
	if not HasMaximalClass(G) then Error(G, "must be a p-group of maximal class!"); fi;
	n:=Size(FactorsInt(Size(G)));
	if n<5 then Error(G, "must have order at least p^5!"); fi;
	if PrimePGroup(G)<5 or n>PrimePGroup(G)+1 or n mod 2=1 then return false; fi;
	if Gamma1(G)=Centralizer(G,LowerCentralSeries(G)[n-2]) then return false; else return true; fi;
end;

Cartanmatrix:=function(ct,p,nr)
local L,L2,i,Q,A;
	L:=Positions(PrimeBlocks(ct,p).block,nr);
	L2:=PositionsProperty(OrdersClassRepresentatives(ct),i->i mod p=0);
	A:=Irr(ct){L}{L2};
	Q:=NullspaceIntMat(IntegralizedMat(A).mat);
	return LLLReducedGramMat(Q*TransposedMat(Q)).remainder; #ReduceQF(Q*TransposedMat(Q));
end;

#Magma: CartanMatrix(G,F) faster
CartanMatrixFG:=function(F,G) #Cartan matrix of finite group G over field F
local PIM,Sim,FG,C,k,i,j;
	PIM:=[];;
	Sim:=[];;
	FG:=RegularModule(G,F)[2];
	PIM:=List(MTX.HomogeneousComponents(FG),h->h.component[2]);
	Sim:=List(PIM,P->MTX.CompositionFactors(P)[1]);
	C:=[];;
	k:=Size(PIM);
	for i in [1..k] do
		C[i]:=[];
		for j in [1..k] do
			C[i][j]:=Size(MTX.BasisModuleHomomorphisms(PIM[i],PIM[j]))/Size(MTX.BasisModuleEndomorphisms(Sim[i]));
		od;
	od;
	return C;
end;

Extracti:=function(i,size)
if IsList(i) then return Size(Intersection([1..size],i[1])); else return i; fi;
end;

BlockInfo:=function(ct,p,def)
local pb,b,j,k,l,sum,kj,pconj,C,chars,D,G,orb,Ga,e;
pb:=PrimeBlocks(ct,p);
for b in [1..Size(pb.defect)] do
  Print("Block no. ",b,":\n");
  Print("Defect = ",pb.defect[b],"\n");
  if pb.defect[b]=0 then Print("\n"); continue; fi;
	chars:=Positions(pb.block,b);
	if def and pb.defect[b]>1 and pb.defect[b]<7 and Size(ct)<10^10 then
		G:=false;
		if HasUnderlyingGroup(ct) then G:=UnderlyingGroup(ct); fi;
		if HasIdentifier(ct) then G:=AtlasGroup(Identifier(ct)); fi;
		if G<>false and G<>fail then
			D:=DefectGroupNew(G,ct,p,b);
			Print("Defect group = ",IdGroup(D)," = ",StructureDescription(D),"\n");
		fi;
	fi;
  Print("k(B) = ",Size(chars),"\n");
  j:=0;
  sum:=0;
  while sum<Size(chars) do
		kj:=Irr(ct){Filtered(chars,k->pb.height[k]=j)};
		if Size(kj)>1 then
			if Conductor(Union(kj)) mod p<>0 then orb:=List(kj,i->1); else
				Ga:=GaloisGroup(CF(Conductor(Union(kj)))); #ist manchmal zu groß
				Ga:=Stabilizer(Ga,E(PPN(Conductor(Union(kj)),p)));
				orb:=SortedList(List(Orbits(Ga,kj),Size));
			fi;
			Print("k",j,"(B) = ",Size(kj)," = ",JoinStringsWithSeparator(orb," + ")," (families of p-conjugate characters)\n");
		else
			Print("k",j,"(B) = ",Size(kj),"\n");
		fi;
    sum:=sum+Size(kj);
    j:=j+1;
  od;
  C:=Cartanmatrix(ct,p,b);  
  Print("l(B) = ",Size(C),"\n");
  if Size(C)>1 then 
		Print("Elementary divisors of the Cartan matrix = ");
		for e in ElementaryDivisorsMat(C) do 
			if e<=p then Print(e); else Print(p,"^",LogInt(e,p)); fi;
			if LogInt(e,p)=pb.defect[b] then Print("\n"); else Print(", "); fi;
		od;
	fi;
od;
end;

#pconj:=Filtered(List(GaloisMat(kj).galoisfams,k->Extracti(k,Size(kj))),l->l>0);

NrBrauerChars:=function(ct,p,nr)
local L,L2,i,A;
	L:=Positions(PrimeBlocks(ct,p).block,nr);
	L2:=PositionsProperty(OrdersClassRepresentatives(ct),i->i mod p<>0);
  A:=IntegralizedMat(Irr(ct){L}{L2}).mat; #Rank is faster for integral matrices
  return Rank(A);
end;
#NrBrauerChars:=function(ct,p,nr)#alt
#local L,L2,i,A;
	#L:=Positions(PrimeBlocks(ct,p).block,nr);
	#L2:=PositionsProperty(OrdersClassRepresentatives(ct),i->i mod p=0);
  #A:=IntegralizedMat(Irr(ct){L}{L2}).mat; #Rank is faster for integral matrices
  #return Size(A)-Rank(A);
#end;

NrRealBrauerChars:=function(ct,p,b) #returns number of real Brauer characters of b-the p-block of character table ct
local pb,IrrB,preg,CTreg,lB,Im,A,NS;
	pb:=PrimeBlocks(ct,p);
	IrrB:=Irr(ct){Positions(pb.block,b)};
	if not ComplexConjugate(IrrB[1]) in IrrB then return 0; fi; #non-real block
	preg:=PositionsProperty(OrdersClassRepresentatives(ct),x->x mod p<>0);
	CTreg:=IrrB{[1..Size(IrrB)]}{preg}; #p-regular character table of B
	lB:=RankMat(CTreg);
	Im:=2*ImaginaryPart(CTreg); #times 2 to keep algebraic integers
	A:=IntegralizedMat(Im).mat; #integers matrix is faster to solve
	NS:=NullspaceIntMat(A);
	#NS:=NullspaceMat(A); #not sure if integer solutions
	return 2*RankMat(NS*CTreg)-lB;
end;

DecompositionBS:=function(ct,p,nr)
local L,L2,i,Q,A;
	L:=Positions(PrimeBlocks(ct,p).block,nr);
	L2:=PositionsProperty(OrdersClassRepresentatives(ct),i->i mod p=0);
  A:=Irr(ct){L}{L2};
	Q:=NullspaceIntMat(IntegralizedMat(A).mat);
	return TransposedMat(Q); 
end;

GeneralizedDecomposition:=function(G,ct,u,i)
local p,j,B,B2,C,ctc,rest,i2,D,Q,k,psi,pos;
if not u in G or not IsPrimePowerInt(Order(u)) then Error(u," must be a non-trivial p-element"); fi;
p:=FactorsInt(Order(u))[1];
if Size(PrimeBlocks(ct,p).defect)<i then return fail; fi;
B:=Irr(ct){Positions(PrimeBlocks(ct,p).block,i)};
C:=Centralizer(G,u);
ctc:=CharacterTable(C);
rest:=RestrictedClassFunction(B[1],C);
psi:=ConstituentsOfCharacter(rest)[1];
i2:=Position(Irr(ctc),psi);
i2:=PrimeBlocks(ctc,p).block[i2];
B2:=Positions(PrimeBlocks(ctc,p).block,i2);
D:=DecompositionBS(ctc,p,i2);
Q:=NullMat(Size(B),Size(D[1]));
for k in [1..Size(B)] do
	rest:=RestrictedClassFunction(B[k],C);
	for psi in Intersection(Irr(ctc){B2},ConstituentsOfCharacter(rest)) do
		pos:=Position(Irr(ctc),psi);
		Q[k]:=Q[k]+u^psi/One(C)^psi*ScalarProduct(rest,psi)*D[Position(B2,pos)];
	od;
od;
return Q;
end;

GeneralizedDecomposition2:=function(G,ct,u,i)
local p,j,B,B2,C,ctc,rest,i2,D,Q,k,psi,pos,L,po,pb,pb2,psi2,rest2,Bh1,corr;
if not u in G or not IsPrimePowerInt(Order(u)) then Error(u," must be a non-trivial p-element"); fi;
p:=FactorsInt(Order(u))[1];
pb:=PrimeBlocks(ct,p);
B:=Irr(ct){Positions(pb.block,i)};
Bh1:=Irr(ct)[First([1..NrConjugacyClasses(ct)],j->pb.block[j]=i and pb.height[j]=0)];
C:=Centralizer(G,u);
ctc:=CharacterTable(C);
Irr(ctc);
pb2:=PrimeBlocks(ctc,p);
L:=[];
Print("number of possible class fusions: ",Size(PossibleClassFusions(ctc,ct)),"\n");
for po in PossibleClassFusions(ctc,ct) do 
	rest:=Character(ctc,Bh1{po});
	corr:=Set(ConstituentsOfCharacter(rest),psi->pb2.block[Position(Irr(ctc),psi)]);
	Print("number of possible Brauer correspondents: ",Size(corr),"\n");
	for i2 in corr do
		B2:=Positions(pb2.block,i2);
		D:=DecompositionBS(ctc,p,i2);
		Q:=NullMat(Size(B),Size(D[1]));
		for k in [1..Size(B)] do
			rest2:=Character(ctc,B[k]{po});
			for psi2 in Intersection(Irr(ctc){B2},ConstituentsOfCharacter(rest2)) do
				pos:=Position(Irr(ctc),psi2);
				Q[k]:=Q[k]+u^psi2/One(C)^psi2*ScalarProduct(rest2,psi2)*D[Position(B2,pos)];
			od;
		od;
		if Union(Q)<>[0] then AddSet(L,Q); fi;
	od;
od;
return L;
end;

MatchUp:=function(P,Q,s,PM)
local n,i,j,t,Qt,PM2,S;
n:=Size(P);
if s>n then return PM; fi;
PM2:=MutableCopyMat(PM);
for i in Filtered(Positions(DiagonalOfMat(Q),P[s][s]),j->j>=s) do
	for t in [1,-1] do
		if i<>s then Qt:=MutableCopyMat(ActPerm(Q,(s,i))); else Qt:=MutableCopyMat(Q); fi;
		MultRowVector(Qt[s],t);
		Qt:=TransposedMatMutable(Qt);
		MultRowVector(Qt[s],t);
		if Qt{[1..s]}{[1..s]}=P{[1..s]}{[1..s]} then 
			if s<>i then PM2:=Permuted(PM2,(s,i)); fi;
			MultRowVector(PM2[s],t);
			S:=MatchUp(P,Qt,s+1,PM2);
			if S<>fail then return S; else
				MultRowVector(PM2[s],t);
				if s<>i then PM2:=Permuted(PM2,(s,i)); fi;
			fi;
		fi;
	od;
od;
return fail;
end;

UpToBasicSets:=function(P,Q) #returns S transforming dec matrices P to Q (up to permutations and signs of rows)
local Cp,Cq,P1,P2,P3,Q1,i,j,Mp,Mq,n,m,l,mp,mpp,mq,mqq,PG,c,g,t,t2,S,x,temp;
if P=Q then return IdentityMat(Size(P[1])); fi;
if Size(P)<>Size(Q) or Size(P[1])<>Size(Q[1]) then return fail; fi;
Cp:=TransposedMat(P)*P;
Cq:=TransposedMat(Q)*Q;
if ElementaryDivisorsMat(Cp)<>ElementaryDivisorsMat(Cq) then return fail; fi;
P1:=MutableCopyMat(P);
Q1:=MutableCopyMat(Q);
SortBy(P1,x->x*Cp^-1*x);
SortBy(Q1,x->x*Cq^-1*x);
for i in [1..Size(P)] do if First(P1[i],x->x<>0)<0 then MultRowVector(P1[i],-1); fi; od;
for i in [1..Size(Q)] do if First(Q1[i],x->x<>0)<0 then MultRowVector(Q1[i],-1); fi; od;
Mp:=DiagonalOfMat(P1*Cp^-1*TransposedMat(P1));
Mq:=DiagonalOfMat(Q1*Cq^-1*TransposedMat(Q1));
if Mp<>Mq then return fail; fi;
n:=Size(Set(Mp));
l:=[];
mp:=[];
mq:=[];
mpp:=[];
mqq:=[];
PG:=[()];
for i in [1..n] do 
	l[i]:=Positions(Mp,Unique(Mp)[i]); 
	P1{l[i]}:=SortedList(P1{l[i]});
	Q1{l[i]}:=SortedList(Q1{l[i]});
	mp[i]:=Size(Set(P1{l[i]}));
	mq[i]:=Size(Set(Q1{l[i]}));
	mpp[i]:=[];
	mqq[i]:=[];
	if mp[i]<>mq[i] then return fail; fi;
	temp:=P1{l[i]};
	SortBy(temp,x->Size(Positions(temp,x)));
	P1{l[i]}:=temp;
	temp:=Q1{l[i]};
	SortBy(temp,x->Size(Positions(temp,x)));
	Q1{l[i]}:=temp;
	for j in [1..mp[i]] do
		mpp[i][j]:=Positions(P1,Unique(P1{l[i]})[j]);
		mqq[i][j]:=Positions(Q1,Unique(Q1{l[i]})[j]);
	od;
	if List(mpp[i],Size)<>List(mqq[i],Size) then return fail; fi;
	for c in Combinations([1..Size(mpp[i])],2) do
		if Size(mpp[i][c[1]])=Size(mpp[i][c[2]]) then Add(PG,Product([1..Size(mpp[i][c[1]])],x->(mpp[i][c[1]][x],mpp[i][c[2]][x]))); fi;
	od;
od;
PG:=Group(PG);
for g in PG do
	P2:=Permuted(P1,g);
	m:=Size(Set(P2))-1;
	for t in Tuples([1,-1],m) do
		t2:=Concatenation(t,[1]);
		P3:=MutableCopyMat(P2);
		for i in [1..Size(P)] do MultRowVector(P3[i],t2[Position(Set(P2),P2[i])]); od;
		S:=(TransposedMat(P3)*P3)^-1*TransposedMat(P3)*Q1;
		if Determinant(S) in [1,-1] and ForAll(Union(S),IsInt) then return S; fi;
	od;
od;
return fail;
end;

Matrix2Latex:=function(M)
	local i,j,irr,p;
	irr:=[];
	Print("\\begin{pmatrix}\n");
	for i in [1..Size(M)] do
		for j in [1..Size(M[1])] do
			if M[i][j]=0 then Print(".");
			elif IsInt(M[i][j]) then Print(M[i][j]);
			else
				p:=Position(irr,M[i][j]);
				if p=fail then Add(irr,M[i][j]); Print("\\sigma_",Size(irr)); else Print("\\sigma_",p); fi;
			fi;
			if j<Size(M[1]) then Print("&"); fi;
		od;
		if i<Size(M) then Print("\\\\\n"); else Print("\n"); fi;
	od;
	Print("\\end{pmatrix}\n");
	for i in [1..Size(irr)] do
		Print("\\sigma_",i,"=",irr[i]);
		if i<Size(irr) then Print("\\\\\n"); else Print("\n"); fi;
	od;
end;

LoewyLength:=function(A) #binary power method
local J,JJ,ll,L,k,P;
if Dimension(A)<2 then return Dimension(A); fi;
J:=RadicalOfAlgebra(A);
if IsTrivial(J) then return 1; fi;
JJ:=J;
L:=[];
repeat
	Add(L,JJ);
	JJ:=ProductSpace(JJ,JJ); #binary power method
until IsTrivial(JJ);
JJ:=L[Size(L)];
ll:=2^(Size(L)-1); #keep track of Loewy length
for k in [1..Size(L)-1] do
	P:=ProductSpace(JJ,L[Size(L)-k]);
	if not IsTrivial(P) then JJ:=P; ll:=ll+2^(Size(L)-k-1); fi;
od;
return ll+1;
end;

ThJ:=function(P)
local m;
m:=Maximum(List(Filtered(SubgroupsC(P),IsAbelian),Size));
return Subgroup(P,Union(Filtered(AllSubgroups(P),H->Size(H)=m and IsAbelian(H))));
end;

reps:=function(G,N)
local x;
	return Filtered(RightTransversal(G,N),x->not x in N);
end;

PResidue:=function(G,p)
local L;
L:=Filtered(ElementsC(G),x->Order(x) mod p<>0);
return NormalClosure(G,Subgroup(G,L));
end;

PPrimeResidue:=function(G,p)
return NormalClosure(G,SylowSubgroup(G,p));
end;

PNilpotentRadical:=function(G,p) #O_pp'(G)
local F,m,N,f;
F:=Filtered(NormalSubgroups(G),n->Size(n) mod p<>0);
m:=Maximum(List(F,Size));
N:=First(F,n->Size(n)=m); #O_p'(G)
f:=NaturalHomomorphismByNormalSubgroupNC(G,N);
return PreImage(f,PCore(Image(f),p));
end;

NilpotentResidue:=function(G)
local LC;
	LC:=LowerCentralSeriesOfGroup(G);
	return LC[Size(LC)];
end;

CompositionFactors:=function(G)
local cs;
	cs:=CompositionSeries(G);
	return List([1..Size(cs)-1],i->cs[i]/cs[i+1]);
end;

PPrimeSubgroups:=function(G,p) #p'-subgroups (not necessarily up to conjugation)
local f,npp,L,q,Q,SGQ,H,R,N,pre;
if PrimeDivisors(Size(G))=[p] then return [TrivialSubgroup(G)]; fi;
if IsPSolvable(G,p) then return SubgroupsC(SylowComplement(G,p)); fi;
if (Size(G)<10^4) or (Size(G) mod p<>0) then return Filtered(SubgroupsC(G),H->Size(H) mod p<>0); fi; #brute force
R:=PResidue(G,p);
if R<>G then return PPrimeSubgroups(R,p); fi;
R:=PCore(G,p);
if Size(R)>1 then
	f:=NaturalHomomorphismByNormalSubgroupNC(G,R);
	return List(PPrimeSubgroups(Image(f),p),Q->SylowComplement(PreImage(f,Q),p));
fi;
npp:=PPN(Size(G),p); #p'-part of |G|
if p>2 and (not IsSolvable(G)) then Info(InfoWarning,1,"Nonsolvable p'-subgroups not considered!"); fi;
L:=[];
for q in Difference(PrimeDivisors(Size(G)),[p]) do
	Q:=SylowSubgroup(G,q);
  UniteSet(L,SubgroupsC(Q));
	SGQ:=Filtered(SubgroupsC(Q),H->IsElementaryAbelian(H) and Size(H)>1);
	for H in SGQ do
		N:=Normalizer(G,H);
		f:=NaturalHomomorphismByNormalSubgroupNC(N,H);
    pre:=List(PPrimeSubgroups(Image(f),p),R->PreImage(f,R));
    UniteSet(L,Filtered(pre,R->not IsPGroup(R)));
	od;
od;
return L;
end;

bysize:=function(n,m)
return Size(n)<Size(m);
end;

InducedRep:=function(G,H,f,q) #return the induced rep f^G where f is matrix rep for H\le G in F_q
local d,gen,img,R,k,g,T,i,j,x;
	d:=Size(One(H)^f); #degree of f
	gen:=SmallGeneratingSet(G);
	img:=[];
	R:=RightTransversal(G,H);
	k:=Size(R);
	for g in gen do
		T:=NullMat(d*k,d*k,GF(q));
		for i in [1..k] do
			for j in [1..k] do
				x:=R[i]*g*R[j]^-1;
				if x in H then T{[1+(i-1)*d..i*d]}{[1+(j-1)*d..j*d]}:=x^f; break; fi;
			od;
		od;
		ConvertToMatrixRep(T); #compress matrix(?), otherwise warning
		Add(img,T);
	od;
	return GroupHomomorphismByImagesNC(G,GL(d*k,q),gen,img);
end;

CharacterAlgebra:=function(G,p)
local ct,dim,i,j,l,k,SCT;
if IsCharacterTable(G) then ct:=G; else ct:=CharacterTable(G); Irr(ct); fi;
dim:=NrConjugacyClasses(ct);
SCT:=EmptySCTable(dim, Zero(GF(p)), "symmetric");
for i in [1..dim] do
	for j in [i..dim] do
		l:=[];
		for k in [1..2*dim] do
			if k mod 2=1 then l[k]:=ScalarProduct(Irr(ct)[i]*Irr(ct)[j],Irr(ct)[(k+1)/2])*One(GF(p)); else l[k]:=k/2; fi;
		od;
		SetEntrySCTable(SCT,i,j,l);
	od;
od;
return AlgebraByStructureConstants(GF(p),SCT);
end;

FPAlgebra:=function(H,P) # fixed point algebra FP^H, P can be a group or a module like ZmodnZ(p^e)^n
local p,orb,dim,SCT,i,j,k,l,classprod,f;
	p:=PrimeDivisors(Size(P))[1];
	orb:=OrbitsDomain(H,P);
	dim:=Size(orb);
	SCT:=EmptySCTable(dim, Zero(GF(p)), "symmetric"); # construct commutative F_p-algebra of dimension dim
	for i in [1..dim] do
		for j in [i..dim] do
			l:=[];
			if IsGroup(P) then classprod:=Collected(ListX(orb[i],orb[j],PROD)); else classprod:=Collected(ListX(orb[i],orb[j],SUM)); fi;
			 # product of orbits
			for k in [1..2*dim] do
				if k mod 2=1 then
					f:=First(classprod,c->c[1] in orb[(k+1)/2]);
					if f<>fail then l[k]:=f[2]; else l[k]:=0; fi;
				else l[k]:=k/2; fi;
			od;
			SetEntrySCTable(SCT,i,j,l);
		od;
	od;
	return AlgebraByStructureConstants(GF(p),SCT);
end;

CenterOfGroupAlgebra:=function(G,p)
local ct,dim,i,j,l,k,SCT;
if IsCharacterTable(G) then ct:=G; else ct:=CharacterTable(G); Irr(ct); fi;
dim:=NrConjugacyClasses(ct);
SCT:=EmptySCTable(dim, Zero(GF(p)), "symmetric");
for i in [1..dim] do
	for j in [i..dim] do
		l:=[];
		for k in [1..2*dim] do
			if k mod 2=1 then l[k]:=ClassMultiplicationCoefficient(ct,i,j,(k+1)/2)*One(GF(p)); else l[k]:=k/2; fi;
		od;
		SetEntrySCTable(SCT,i,j,l);
	od;
od;
return AlgebraByStructureConstants(GF(p),SCT);
end;

ClassAlgebra:=CenterOfGroupAlgebra;

CenterOfBlock:=function(ct,p,b) #center of b-th p-group of group with ct over splitting field of char p
local dim,i,j,l,k,SCT,A,pb,IrrB,gen,eB,c,val,F;
dim:=NrConjugacyClasses(ct);
pb:=PrimeBlocks(ct,p);
IrrB:=Irr(ct){Positions(pb.block,b)};
val:=List([1..dim],i->FrobeniusCharacterValue(Sum(IrrB,c->c[1]*ComplexConjugate(c[i]))/Size(ct),p));
F:=Field(val);

SCT:=EmptySCTable(dim, Zero(F), "symmetric");
for i in [1..dim] do
	for j in [i..dim] do
		l:=[];
		for k in [1..2*dim] do
			if k mod 2=1 then l[k]:=ClassMultiplicationCoefficient(ct,i,j,(k+1)/2)*One(F); else l[k]:=k/2; fi;
		od;
		SetEntrySCTable(SCT,i,j,l);
	od;
od;
A:=AlgebraByStructureConstants(F,SCT); #Z(F_pG)
gen:=GeneratorsOfAlgebra(A);
eB:=Sum([1..dim],i->val[i]*gen[i]); #block idempotent
return Subalgebra(A,gen*eB);
end;

CenterOfBlockPuig:=function(Q,q) 
#Q generalized decomposition matrix of a p-block B, columns labeled by ordinary irreducible characters
#q power of p
#returns Z(B) regarded as an algebra over the finite field with q elements
local Qinv,n,M,z,i,j,r,s,S,A,SCT;
n:=Size(Q);
Qinv:=Q^-1;
M:=NullMat(n^2-n,n^2);;
z:=1;
for r in [1..n] do #define linear system coming from Puig's paper
	for s in Difference([1..n],[r]) do
		for i in [1..n] do
			for j in [1..n] do
				M[z][n*(i-1)+j]:=Q[j][s]*Qinv[r][i];
			od;
		od;
		z:=z+1;
	od;
od;
r:=ComplexConjugate(Q)*TransposedMat(Q);
r:=ElementaryDivisorsMat(r)[n]; #=order of defect group
M:=IntegralizedMat(TransposedMat(r*M)).mat; #make coefficient matrix integral
M:=NullspaceIntMat(M); #solve linear system over integers
S:=[];
for z in M do #retransform solutions into diagonal matrices
	A:=NullMat(n,n);
	for i in [1..n] do A[i]:=z{[n*(i-1)+1..n*i]}; od;
	if not IsDiagonalMat(Qinv*A*Q) then return fail; fi; #test...
	Add(S,DiagonalOfMat(Qinv*A*Q)); 
od;
SCT:=EmptySCTable(n,Zero(GF(q)), "symmetric");
for i in [1..n] do
	for j in [i..n] do
		r:=[];
		M:=SolutionMat(S,List([1..n],x->S[i][x]*S[j][x])); #compute structure constants
		for s in [1..2*n] do
			if s mod 2=1 then r[s]:=M[(s+1)/2]*One(GF(q)); else r[s]:=s/2; fi;
		od;
		SetEntrySCTable(SCT,i,j,r);
	od;
od;
return AlgebraByStructureConstants(GF(q),SCT);
end;

PSections:=function(ct,p)
local ords,L,i,psec;
ords:=OrdersClassRepresentatives(ct);
L:=List([1..NrConjugacyClasses(ct)],i->PowerMap(ct,ords[i]/p^Valuation(ords[i],p),i));
psec:=[];
for i in AsSet(L) do
	Add(psec,Positions(L,i));
od;
return psec;
end;

ClassBlocks:=function(ct,p)
local pb,clbls,sec,bl,i,c,rel,x,y,br,tr,L;
pb:=PrimeBlocks(ct,p);
clbls:=[];
for sec in PSections(ct,p) do
	rel:=[]; #make a reflexive, symmetric relation
	for i in [1..Size(sec)] do rel[i]:=[i]; od;
	for x in [1..Size(sec)] do
		for y in [x+1..Size(sec)] do
			if ForAny([1..Size(pb.defect)],bl->Sum(PositionsProperty(pb.block,i->i=bl),c->Irr(ct)[c][sec[x]]*ComplexConjugate(Irr(ct)[c][sec[y]]))<>0) then Add(rel[x],y); Add(rel[y],x); fi;
		od;
	od;
	br:=BinaryRelationOnPoints(rel);
	tr:=TransitiveClosureBinaryRelation(br);
	L:=List(EquivalenceClasses(tr),Elements);
	for i in L do Add(clbls,sec{i}); od;
od;
return clbls;
end;

DefectOfCB:=function(ct,p,C)
local G,El,Syl,m,i,x;
G:=UnderlyingGroup(ct);
El:=List(ConjugacyClasses(ct),Representative);
Syl:=List(C,i->SylowSubgroup(Centralizer(G,El[i]),p));
m:=Maximum(List(Syl,Size));
return First(Syl,x->Order(x)=m);
end;

NilpotentBlocks:=function(ct,p) #based on a conjecture by Malle-Navarro
local pb,n,L,i,j,pos;
pb:=PrimeBlocks(ct,p);
n:=Size(pb.defect);
L:=[];
for i in [1..n] do
	pos:=PositionsProperty([1..Size(pb.block)],j->pb.block[j]=i and pb.height[j]=0);
	if Size(Set(Irr(ct){pos},DegreeOfCharacter))=1 then Add(L,i); fi;
od;
return L;
end;

lB1Blocks:=function(ct,p) #non-nilpotent blocks with l(B)=1
	local pb,bl,b; 
	pb:=PrimeBlocks(ct,p);
	bl:=Difference([1..Size(pb.defect)],NilpotentBlocks(ct,p));
	return Filtered(bl,b->NrBrauerChars(ct,p,b)=1);
end;

IsQuasiPrimitiveBlock:=function(G,p,i) #checks if i-th p-block of G is quasiprimitive
local ct,N,ctN;
ct:=CharacterTable(G);
for N in NormalSubgroups(G) do
	ctN:=CharacterTable(N);
	if Size(CoveredBlocks(ct,p,i,ctN))>1 then return false; fi;
od;
return true;
end;

Sturm:=function(P,a,b) #returns number of distinct real roots of polynomial P in interval (a,b]
	local L,sa,sb,i,j;
	L:=[];
	L[1]:=P/Gcd(P,Derivative(P));
	L[2]:=Derivative(L[1]);
	while Degree(L[Size(L)])>0 do
		Add(L,-EuclideanRemainder(L[Size(L)-1],L[Size(L)]));
	od;
	sa:=Filtered(List(L,i->Value(i,a)),j->j<>0);
	sa:=Number([1..Size(sa)-1],i->sa[i]*sa[i+1]<0);
	sb:=Filtered(List(L,i->Value(i,b)),j->j<>0);
	sb:=Number([1..Size(sb)-1],i->sb[i]*sb[i+1]<0);
	return sa-sb;
end;

contrib:=function(q) #returns contribution matrix of given decomposition matrix
	return ComplexConjugate(q)*(TransposedMat(q)*ComplexConjugate(q))^-1*TransposedMat(q);
end;

IsCentralType:=function(G) #returns if G is a group of central type
local d;
	d:=Index(G,Center(G));
	if d=1 or not IsSquareInt(d) then return false; fi;
	if ForAny(CharacterDegrees(G),c->c[1]=Sqrt(d)) then return true; else return false; fi;
end;

OrthogonalEmbeddingsNEW:=function( arg )
    local ExtendAtPosition,
          A, maxdim, mindim, nonnegative, x, checkdim, n, i, j, Adiag, Ainv,
          denom, row, norms, m, M, increaserank, D, f, sol, soldim, solcount,
          s, k, iota, mult, sumg, sumh, tosort, x2, phi, prod, out, minnorm,
          normdiff, l, char, coeff, SNF, A1, vec, n1, ortA1, existence;

    ExtendAtPosition:= function( i )
      local v, k1, phi_i, ii, sum, j, r;

      # Find v that solves the equation v D M^{tr} = - phi[i]
      # and adjust the data structures according to the addition of v
      # to the end of the matrix M.
      v:= [];
      k1:= 0;
      phi_i:= phi[i];

      for ii in [ 1 .. s-1 ] do
        # Here we have Length( M[ii] ) = k1.
        if k1 = 0 then
          sum:= 0;
        else
          sum:= v * M[ii];
        fi;
        if increaserank[ii] then
          k1:= k1 + 1;
          v[k1]:= -( phi_i[ f[ii] ] + sum ) / D[k1];
        elif sum <> -phi_i[ f[ii] ] then
          return false;
        fi;
      od;

      # Here we have k1 = k-1.
      r:= denom - norms[i];
      for j in [ 1 .. k1 ] do
        r:= r - v[j] * D[j] * v[j];
      od;
      if r < 0 then
        return false;
      elif r = 0 then
        increaserank[s]:= false;
      else
        increaserank[s]:= true;

        # Extend the diagonal matrix.
        D[k]:= r;
        k:= k + 1;
      fi;

      for j in [ 1 .. k1 ] do
        v[j]:= v[j] * D[j];
      od;

      # Extend the matrix M.
      M[s]:= v;
      f[s]:= i;
      s:= s + 1;
      iota[i]:= iota[i] + 1;
      normdiff:= normdiff - norms[i] + minnorm;

      return true;
    end;

    # Get and check the input.
    if Length( arg ) = 0 then
      Error( "usage: OrthogonalEmbeddings( <A>, <arec> )" );
    fi;

    A:= arg[1];

    if not IsList( A ) or Length( A ) = 0 or not IsList( A[1] ) then
      Error( "<A> must be a symmetric matrix" );
    fi;

    maxdim:= fail;
    mindim:= 0;
    existence:=false;
    nonnegative:= false;
    if IsBound( arg[2] ) and IsRecord( arg[2] ) then
      if IsBound( arg[2].maxdim ) and IsPosInt( arg[2].maxdim ) then
        maxdim:= arg[2].maxdim;
      fi;
      if IsBound( arg[2].mindim ) then
        mindim:= arg[2].mindim;
      fi;
      if IsBound( arg[2].nonnegative ) and arg[2].nonnegative = true then
        nonnegative:= true;
      fi;
      if IsBound( arg[2].vectors ) then
        x:= arg[2].vectors;
      fi;
      if IsBound( arg[2].existence ) then
				existence:=arg[2].existence;
			fi;
	    else
      # backwards compatibility ...
      if "positive" in arg then
        nonnegative:= true;
      fi;
      maxdim:= First( arg, IsInt );
    fi;
    checkdim:= maxdim <> fail;

    n:= Length( A );
    
    if IsBound(x) and IsList(x) and nonnegative then
      x:=Filtered(x,i->ForAll(i,j->j>=0));
    fi;    
    
		if A<>TransposedMat(A) then 
			Error( "matrix <A> must be symmetric" );
		fi;
	
		char:=CharacteristicPolynomial(A);
		coeff:=List(CoefficientsOfUnivariatePolynomial(char));
		while coeff[1]=0 do Remove(coeff,1); od;
		if ForAny([1..Size(coeff)-1],i->coeff[i]*coeff[i+1]>=0) then
			Error( "matrix <A> must be positive semidefinite" );
		fi;
		
		if Determinant(A)=0 then
			if Rank(A)=0 then return rec(vectors:=[], solutions:=[], norms:=[]); fi;
			SNF:=SmithNormalFormIntegerMatTransforms(A);
			A1:=SNF.normal*SNF.coltrans^-1*TransposedMat(SNF.rowtrans);
			A1:=A1{[1..SNF.rank]}{[1..SNF.rank]};
			n1:=Length(A1);
			Info( InfoZLattice, 2,
            "OrthogonalEmbeddings: reduction to dimension ",n1);
			if IsBound(x) and IsList(x) then
				vec:=List(x*TransposedMat(SNF.rowtrans),i->i{[1..n1]});
				ortA1:=OrthogonalEmbeddingsNEW(A1,rec(mindim:=mindim, maxdim:=maxdim, vectors:=vec));
			elif nonnegative then
				denom:=ElementaryDivisorsMat(A1)[n1];
				vec:=Filtered(ShortestVectors(denom*A1^-1,denom).vectors,i->ForAll(Concatenation(i,[1..n-n1]*0)*TransposedMat(SNF.rowtrans)^-1,j->j>=0) or ForAll(Concatenation(i,[1..n-n1]*0)*TransposedMat(SNF.rowtrans)^-1,j->j<=0));
				ortA1:=OrthogonalEmbeddingsNEW(A1,rec(mindim:=mindim, maxdim:=maxdim, vectors:=vec));
			else
				ortA1:=OrthogonalEmbeddingsNEW(A1,rec(mindim:=mindim, maxdim:=maxdim));
			fi;
			vec:=List(ortA1.vectors,i->Concatenation(i,[1..n-n1]*0)*TransposedMat(SNF.rowtrans)^-1);
			for row in vec do if row[1]<0 then MultRowVector(row,-1); fi; od;
			out:=rec(vectors:=vec, solutions:=ortA1.solutions);
			return out;
		fi;
	
    #for i in [ 1 .. n ] do
    #  for j in [ 1 .. i-1 ] do
    #    if A[i][j] <> A[j][i] then
    #      Error( "matrix <A> must be symmetric" );
    #    fi;
    #  od;
    #od;

    # 'Ainv' is an integer matrix and 'denom' is an integer
    # such that 'Ainv = denom * Inverse( A )'.
    
    Adiag:= List( [ 1 .. n ], i -> A[i][i] );
		denom:=ElementaryDivisorsMat(A)[n];    
		Ainv:=denom*A^-1;

		#Ainv:= InverseMutable( A );
    #denom:= 1;
    #for row in Ainv do
    #  for i in row do
    #    denom:= Lcm( denom, DenominatorRat( i ) );
    #  od;
    #od;
    #for row in Ainv do
    #  MultRowVector( row, denom );
    #od;

    if IsBound( x ) then
      if IsList( x ) then
        x:= rec( vectors:= x, norms:= List( x, v -> v * Ainv * v ) );
      fi;
    else
      if nonnegative then
        x:= ShortestVectors( Ainv, denom, "positive" );
      else
        x:= ShortestVectors( Ainv, denom );
      fi;
      Info( InfoZLattice, 2,
            "OrthogonalEmbeddings: ",
            Length( x.vectors ), " candidate vectors found" );
    fi;

    norms:= x.norms;
    x:= x.vectors;
    m:= Length( x );
    M:= [ [] ];
    increaserank:= [];
    D:= [];
    f:= [];
    sol:= [];
    soldim:= [];
    solcount:= 0;
    s:= 1;
    k:= 1;
    iota:= 0 * [ 1 .. m ];
    mult:= ShallowCopy( iota );
    sumg:= 0 * [ 1 .. n ];
    sumh:= ShallowCopy( sumg );

    # Sort the vectors and the norms such that the norms are non-increasing,
    # and vectors of the same norm are sorted according to non-increasing
    # absolute values of the entries.
    tosort:= List( [ 1 .. m ], i -> [ norms[i], x[i] ] );
    Sort( tosort,
      function( i, j )
        local v, w, k;

        if i[1] = j[1] then
          v:= i[2];
          w:= j[2];
          for k in [ 1 .. n ] do
            if AbsInt( v[k] ) > AbsInt( w[k] ) then
              return true;
            elif AbsInt( v[k] ) < AbsInt( w[k] ) then
              return false;
            fi;
          od;
        else
          return j[1] < i[1];
        fi;
      end );
    norms:= List( tosort, pair -> pair[1] );
    x:= List( tosort, pair -> pair[2] );

    # 'x2[i]' stores the contribution of 'x[i]' to the diagonal of 'A'.
    x2:= List( x, v -> List( v, y -> y^2 ) );

    # Store the scalar product of x_i and x_j w.r.t. 'Ainv' in 'phi[i][j]'.
    phi:= [];
    for i in [ 1 .. m ] do
       row:= [];
       prod:= x[i] * Ainv;
       for j in [ 1 .. i-1 ] do
         row[j]:= prod * x[j];
       od;
       row[i]:= norms[i];
       phi[i]:= row;
    od;

    # Initialize the result record.
    out:= rec( vectors:= x,
               norms:= norms / denom,
               solutions:= [] );

    # Let $X = [ x_1, x_2, \ldots, x_k ]$ be a solution of $X^{tr} X = A$,
    # and let $P = X A^{-1} X^{tr}$ (see [Ple95, Prop. 2.2]).
    # The trace of $P$ is $n$, and the $i$-th diagonal entry of $P$ is
    # $x_i A^{-1} x_i^{tr}$,
    # thus $n$ is the sum of the norms of the $k$ involved vectors.
    # The a priori implication is that $n$ is at least $k$ times the smallest
    # norm that occurs.
    # (We have sorted the vectors according to non-increasing norm.)
    minnorm:= norms[m];

    # Any solution $X$ of dimension $k$ for which the multiplicities
    # of involved vectors are at least the ones from $\iota_i$ satisfies
    # $n \geq \sum_{i=1}^m \iota_i x_i A^{-1} x_i^{tr} +
    # (k - \sum_{i=1}^m \iota_i) x_m A^{-1} x_m^{tr}$.
    # For minimal $k$, we get the condition that
    # 'n * denom - mindim * minnorm
    # - Sum( [ 1 .. m ], i -> iota[i] * ( norms[i] - minnorm ) )'
    # is nonnegative.
    normdiff:= n * denom - mindim * minnorm;
    if normdiff < 0 then
      return out;
    fi;

    # Start the enumeration of coefficient vectors.
    l:= 1;
    repeat

      # The multiplicities of the first 'l-1' vectors have been fixed.
      if 0 <= normdiff then

        # Compute the maximal multiplicities of x_l, x_{l+1}, ...,
        # assuming that only one of these vectors occurs,
        # and store the contributions to the trace in 'sumh'.
        MultRowVector( sumh, 0 );
        i:= l;
        while i <= m and ( not checkdim or s <= maxdim ) do
          if mult[i] * norms[i] < denom then
            repeat
               if not ExtendAtPosition( i ) then
                 break;
               fi;
            until iota[i] * norms[i] >= denom or ( checkdim and s > maxdim );
            mult[i]:= iota[i];

            # Reset the i-th coefficient to zero, adjust the data structures.
            while 0 < iota[i] do
              s:= s - 1;
              if increaserank[s] then
                k:= k -1;
              fi;
              iota[i]:= iota[i] - 1;
              normdiff:= normdiff + norms[i] - minnorm;
            od;
          fi;
          if mult[i] <> 0 then
            AddRowVector( sumh, x2[i], mult[i] );
          fi;
          i:= i + 1;
        od;

        # Proceed with the current initial part 'iota{ [ 1 .. l-1 ] }'
        # only if this part plus the sum of *all* possible vectors
        # is big enough for reaching the diagonal values.
        if ForAll( [ 1 .. n ], i -> Adiag[i] <= sumg[i] + sumh[i] ) then
          # Increase the coefficients of the vectors x_l, x_{l+1}, ...
          # as much as possible.
          i:= l;
          while i <= m and ( not checkdim or s <= maxdim ) do
            repeat
              if ExtendAtPosition( i ) then
                AddRowVector( sumg, x2[i] );
                l:= i;
              else
                break;
              fi;
            until iota[i] >= mult[i] or ( checkdim and maxdim < s );
            mult[i]:= 0;
            i:= i + 1;
          od;

          # Check whether this vector describes a solution.
          if s = n + k and mindim < s then
            solcount:= solcount + 1;
            Info( InfoZLattice, 2,
                  "OrthogonalEmbeddings: ",
                  Ordinal( solcount ), " solution has dimension ", s - 1 );
            sol[ solcount ]:= ShallowCopy( iota );
            soldim[ solcount ]:= s - 1;
            if existence then
							out.solutions[1]:= [];
							for j in [ 1 .. m ] do
								for k in [ 1 .. sol[1][j] ] do
									Add( out.solutions[1], j );
								od;
							od;
							return out; 
						fi;
          fi;
        fi;
      fi;

      # elementary decrease step
      while l > 0 do
        if iota[l] <> 0 then
          if l = m then
            # Set the m-th coefficient to zero, adjust the data structures.
            AddRowVector( sumg, x2[l], -iota[l] );
            while iota[l] > 0 do
              s:= s - 1;
              if increaserank[s] then
                k:= k - 1;
              fi;
              iota[l]:= iota[l] - 1;
              normdiff:= normdiff + norms[l] - minnorm;
            od;
          else
            AddRowVector( sumg, x2[l], -1 );
            s:= s - 1;
            if increaserank[s] then
              k:= k - 1;
            fi;
            iota[l]:= iota[l] - 1;
            normdiff:= normdiff + norms[l] - minnorm;
            l:= l + 1;
            break;
          fi;
        fi;
        l:= l - 1;
      od;

    until l <= 1;

    # Format the solutions.
    # The solutions are sorted according to increasing dimension,
    # and such that two solutions of same dimension are sorted
    # reverse lexicographically.
    tosort:= List( [ 1 .. solcount ], i -> [ soldim[i], sol[i] ] );
    Sort( tosort,
        function( i, j )
          if i[1] = j[1] then
            return j[2] < i[2];
          else
            return i[1] < j[1];
          fi;
        end );
    sol:= List( tosort, x -> x[2] );

    for i in [ 1 .. solcount ] do
      out.solutions[i]:= [];
      for j in [ 1 .. m ] do
        for k in [ 1 .. sol[i][j] ] do
          Add( out.solutions[i], j );
        od;
      od;
    od;

    return out;
end;

CTs:=[ "Alt(2)", "C2", "C3", "C4", "V4", "C6", "S3", "2^3", "D8", "Q8", "3^2", "D10", "a4", "2.S3", "S3x2", "D14", "4.2^2", "D16", "2.D8", "D8x2", "M11N2", 
  "D18", "3^2:2", "5:4", "D20", "bd10", "7:3", "D22", "s4", "1/2(8xS3)", "(2^2x3).2", "3xD8", "2.D12", "2.L2(3)", "D24", "D26", "3^(1+2)_+", "2.D14", 
  "D28", "3xD10", "D30", "QD16.2", "D8xV4", "U3(5).2N2", "2.D16", "D32", "M12C4", "3^2:4", "2.D18", "S3xS3", "13:3", "2.D20", "2x5:4", "5:8", "2x7:3", 
  "7:6", "2.D22", "2xSymm(4)", "2.Symm(4)", "4^2:3", "A4xC4", "2.D24", "2.S4", "6.A6N2", "D8xS3", "2.D26", "13:4", "9:6", "3^(1+2)_+:2", "11:5", "2.D28", 
  "2^3:7", "2^2xD14", "19:3", "(3xD10).2", "D6xD10", "5:4x3", "3x2.D10", "A5", "2.D30", "D62", "7:3x3", "group3", "L3(4)Syl2", "M12N2", "2.D32", "2^3.D8", 
  "4.2^4", "s3wrs2", "3^2:8", "3xSymm(4)", "2.A4x3", "(A4x3):2", "A4xS3", "3^2:Q8", "13:6", "2.M12N5", "Isoclinic(2x5:8)", "5:4x2^2", "2x7:6", "4x7:3", 
  "7:12", "31:3", "4^2:s3", "4.s4", "S4x2^2", "2^2:S4", "2.2^4:3", "group6", "25:4", "2x13:4", "D108", "M12N3", "3^(1+2):4", "D110", "2x11:5", "11:10", 
  "37:3", "D112", "19:6", "D114", "3x5:8", "(3x2.D10).2", "D120", "S3x5:4", "2xA5", "2.A5", "6x5:4", "A5.2", "D122", "D62x2", "6x7:3", "(7:3x3):2", 
  "3x7:6", "7:3xS3", "D126", "G2(3).2N2", "2.M12N2", "A11Syl2", "2^4:D8", "43:3", "17:8", "3^2:Q8.2", "(2.A4x3).2", "S4xS3", "3x2.Symm(4)", "2x(A4x3):2", 
  "Isoclinic(2x3^2:Q8)", "2.A8N3", "(3xSL(2,3)):2", "2.A4xS3", "5^2:S3", "31:5", "13:12", "(2x13).6", "2x13:6", "(9x3).S3", "3^3:S3", "41:4", "3x11:5", 
  "L3(2)", "(2^2xD14):3", "2^3.7.3", "19:9", "3x19:3", "3xA5", "3xD6xD10", "31:6", "M8.S4", "2^4:A4", "4^2:D12", "2^4:A4b", "2^(1+4).S3", "2^3.S4v1", 
  "3xM12N2", "2^3.S4v2", "2^2x13:4", "6^2:S3", "3^(1+2)_+:Q8", "3^(1+2):8", "2xM12N3", "3^(1+2):D8", "3.(A4x3):2", "6.A6M3", "3^2:2A4", "73:3", "4x11:5", 
  "2x11:10", "11:20", "2^2x11:5", "3x13:6", "2.A5.2", "5:4xA4", "3xIsoclinic(2x5:8)", "Isoclinic(2.A5.2)", "2.(S3x5:4)", "2xS5", "(A4xD10).2", "12x7:3", 
  "S3x7:6", "A4x7:3", "(7:3x3):4", "23:11", "LyN2", "2.M22N2", "(2x17).8", "17:16", "91:3", "Isoclinic(4x3^2:Q8)", "(4^2x3):S3", "2^2.(3^2:Q8)", 
  "Isoclinic(2x(2.A4x3).2)", "2^4:(3x3):2", "2.(A4xA4)", "2x(3^2.QD16)", "S3x2.S4", "2x2.A4xS3", "7^2:S3", "5xA5", "5^2:12", "5^2:D12", "31:10", 
  "(D10xU3(5)N2).2", "3^3:A4", "2x3^3:S3", "3^3:(S3x2)", "6x11:5", "3x11:10", "11:5xS3", "Co2N7", "L3(2).2", "2xL3(2)", "2.L3(2)", "(Q8xD14):3", "3x19:6", 
  "2x19:9", "19:18", "3^3:13", "A6", "3xA5.2", "S3xA5", "3x2.A5", "(A5x3):2", "2.M12M10", "2.M12M9", "2.(D8x2^2).S3", "s2wrs4", "2^(1+1+2+2):S3", 
  "4^2:D12.2", "8^2:S3", "J2N2", "2.U4(2)N2", "3xMcLN2", "NRS(M22,[2^6])", "M22C2A", "2.2^4.2.S3", "2^3.(S4x2)", "133:3", "(D10xD10).2^2", "29:14", 
  "3x17:8", "2.J2N3", "3^(1+2):SD16", "6^2:D12", "2x3.(A4x3):2", "3^2.2.S4", "2x3^2:2A4", "6.(A4x3).2", "Isoclinic(2x3^(1+2)_+:Q8)", "(2^2x11:5).2", 
  "37:12", "2^(3+3):7", "31:15", "S3x13:6", "6x13:6", "3x(2x13).6", "(3x13:6).2", "2S5.2", "2.M12M8", "5:4xS4", "NDG(2.HS,Q8)", "(2^2xA5):2", "gl25", 
  "3xL3(2)", "(A4x7:3):2", "2xS3x7:6", "7:3xS4", "L2(8)", "2x23:11", "23:22", "4.M22N2", "S6(2)N2", "4^3.D8", "HSN2", "group2", "3x19:9", "2^4:3^2:4", 
  "D8x3^2:Q8", "b33141", "S4xS4", "NDG(ON,D8)", "2xS3x2.S4", "3x4^2:D12", "3x2^3.S4v1", "2^(1+4)+:3^2.2", "2^2.(3^2:Q8.2)", "2.HSN3", "2^4:(S3xS3)", 
  "(2x5^2).12", "2.J2M8", "10^2:S3", "a5xd10", "5^2:(4xS3)", "43:14", "(2^2x13:4):3", "g61s1", "5:4xU3(5).2N2", "3^3.S4", "hess", "2x3^3:(S3x2)", 
  "3^2:2A4x3", "3^(1+2)+:2A4", "3^3:S4`", "2x6x11:5", "11:10xS3", "12x11:5", "3x11:20", "L2(11)", "37:18", "2^2xL2(7)", "Isoclinic(2.L3(2).2)", 
  "(2xL3(2)).2", "2.L3(2).2", "L3(2).2x2", "2x3^3:13", "S5xS3", "a4xa5", "2xA6", "3xIsoclinic(2.A5.2)", "3x2S5", "S3x2.A5", "2.A6", "(3^2:4xD10).2", 
  "(2.A5x3).2", "A6.2_1", "A6.2_2", "A6.2_3", "3xS3x7:6", "3x23:11", "2^(2+4).(S3x2)", "(4^2x2)S4", "4.2^4:(2xS3)", "2^4.(S4x2)", "3x2.M22N2", "2.J2N2", 
  "(3xMcLN2).2", "(2x29).14", "frob", "3x17:16", "2x3^2.2.S4", "(2x3^(1+2)_+:8):2", "2^2.(3^2:2A4)", "3^(1+2):8:4", "12.M22N3", "S3x(3xSL(2,3)):2", 
  "S4x3^2:4", "NDG(12.M22,3^2)", "(3^(1+2)x2).SD16", "127:7", "2.2^(3+3):7", "31:30", "2x31:15", "2^4:A5", "P1/G1/L1/V1/ext2", "NDG(2.HS,Q8).2", 
  "2^(2+4):15", "(3x3^3:S3):2", "5^(1+2)+:8", "3xL3(2).2", "6xL3(2)", "L3(2)xS3", "c3d2", "(SL2(3)x7:3).2", "3x2.L3(2)", "(SL(2,3)x7:3).2", "ON.2N2", 
  "M24N2", "2.HSN2", "Co3N2", "3.A6", "47:23", "L2(13)", "3xJ3N2", "2(S4xS4)", "3xM22C2A", "2.(D8x3^2:Q8)", "2^(1+4).S3^2", "NDG(ON,D8).2", "s4wrs2", 
  "2^2+4.3xs3", "2.(2.(A4xA4).2)", "3xNRS(M22,[2^6])", "2(A4xA4).2^2", "2^(2+4):(3x3):2", "2.HS.2N3", "2^(1+4)+.(S3xS3)", "g72x16", "w(f4)", "7^2:2A4", 
  "7^2:24", "group5", "5^2:4A4", "2.J2.2N5", "5:4xa5", "2A5xD10", "(A5xD10).2", "2.D10xA5", "3x29:14", "(Q8x13:4):3", "(2x3^3).S4`", "2x3^(1+2)+:2A4", 
  "3^(1+2)+:2S4", "3^(1+2)+.2S4", "s3wrs3", "(2x3^3).S4", "(11:5xD12).2", "L2(11).2", "2xL2(11)", "(A4x11:5).2", "2.L2(11)", "D8xL3(2)", "2^3.L3(2)", 
  "2^3:sl(3,2)", "2^(3+3):7:3", "3x31:15", "(A4xA5):2", "2^2xA6", "2.A5.2xS3", "M10x2", "(3x2S5).2", "S6x2", "(3^2:D8xD10).2", "(2xA6).2_3", "2.HSN3A", 
  "2.A6.2_2", "2A4xA5", "a4xs5", "Isoclinic(2.A6x2)", "A6.2^2", "2.A6.2_1", "67:22", "3xL2(8)", "3x(A4x7:3):2", "L2(8).3", "6xS3x7:6", "2.[2^6].(2xS3)", 
  "2^6:S4b", "(4x2^2).2^4.S3", "(4^2x2).2^3.S3", "4^3:S4", "3xONN2", "(4^2x2)(2xS4)", "3x4.M22N2", "4.2^4:S4", "2^6:S4a", "41:40", "S4x3^2:Q8", 
  "3.2^(1+4)+:3^2.2", "D8x3^(1+2)_+:Q8", "2^2x3^2.2.S4", "NDG(3.ON,D8)", "hed3", "2^2.2^(3+3):7", "3x5^2:(4xS3)", "(13:6xA4).2", "P1/G2/L1/V2/ext2", 
  "P1/G2/L1/V1/ext2", "2^(2+4):(3xD10)", "2^4:s5", "2^1+4b:a5", "2.(2^4:A5)", "mo62", "P1/G2/L2/V2/ext2", "2.D8.S5", "3^2.3^(1+2):8", "3xL2(11)", 
  "5^(1+2):(8.2)", "2F4(2)'N2", "2.HS.2N2", "7^1+2.6", "j3m6", "3.A6.2_2", "6.A6", "2x3.A6", "3.A6.2_1", "2.A6x3", "3.A6.2_3", "(3xA6).2_1", 
  "(3^(1+2):4xD10).2", "2x47:23", "2.L2(13)", "L2(13).2", "2^(2+4):(S3xS3)", "2.S4x2.S4", "2(A4xA4).4.2", "2.(2.(A4xA4).2.2)", "2^{3+4}:(3xS3)", 
  "4(A4xA4).4", "(7xL2(7)):2", "5:4x2.A5", "5:4xS5", "(2.A5xD10).2", "Fi22N5", "L2(17)", "A7", "7:3xS5", "(7:3xA5):2", "2x3^(1+2)_+:2S4", "2.(3^3:(S4x2))",
  "S4x3^(1+2):4", "2.L2(11).2", "2xL2(11).2", "2.(2xL2(11))", "2(L2(7)x4).2", "2^3.L3(2):2", "2x2^3:L3(2)", "2^(1+3):L3(2)", "(3^2:2x13:6).2", 
  "(4xA6).2_3", "4.A6.2_3", "2^2.S6", "(2xA6).2^2", "2.(S6x2)", "S5xS4", "(4xA6):2", "A6.D8", "3x2^4:A5", "2.(A5xA4).2", "2xa6.2^2", "j3m4", "3^4.3^2:4", 
  "3^2.(3x3^(1+2)+):2^2", "5^(1+2)+:24", "5^1+2.2A4", "5^(1+2):3:8", "3x5^(1+2)_+:8", "5^2:2A5", "L2(8):3x2", "S3xL2(8)", "3x(SL(2,3)x7:3).2", 
  "[2^9].S3b", "2.2^3.2^5.S3", "[2^9].S3a", "(2^2x4).2^5.S3", "(3xONN2).2", "2.2^4.2^4.S3", "(2x4^2).2^4.S3", "3^4:40", "3xL2(13)", "L2(19)", 
  "2^(1+4)_+.(S3x3^2:2)", "3x2(A4xA4).2^2", "3.2^(2+4):(3x3):2", "2.(D8x3^(1+2)_+:Q8)", "NDG(He.2,3^2)", "3x2^(2+4):(3xS3)", "2.2^4.(S3x3^2:2)", 
  "NDG(J4,3^2)", "7:3xpsl(3,2)", "7xL2(8)", "7^2:(3x2A4)", "3x2.J2.2N5", "A5xA5", "3x(A5xD10).2", "2.(13:6xA4).2", "2^{1+4}_-:2A5", "P1/G3/L2/V1/ext2", 
  "twd5a", "2.M22M5", "4_2.2^4:A5", "4_1.2^4:A5", "M22.2M4", "s2wrs5", "2^(1+4).S5", "3^2.3^(1+2):8.2", "S3x3^(1+2)+:2A4", "3^(1+2)_+.(2S4x3)", 
  "(3x3^(1+2)+:2A4).2", "(L2(11)x3).2", "3x(A4x11:5).2", "6xL2(11)", "5^1+2:(2^5)", "5^(1+2):8:4", "3x2^3:L3(2)", "s4xpsl(3,2)", "3x2^3.L3(2)", "L2(16)", 
  "2F4(2)'.2N2", "O8+(2)N2", "2x3.S6", "(2.A6x3).2_1", "Isoclinic(3.A6.2_3x2)", "Isoclinic(6.A6x2)", "6.A6.2_1", "3.A6.2^2", "6.A6.2_2", "S3xS6", 
  "(2x3.A6).2", "(3xM10):2", "(S3xS3xA5):2", "Isoclinic(L2(13).2x2)", "2.L2(13).2", "3xL2(8).3", "2(A4xA4).4.2^2", "(2^4:A4xA4).2", "2.[2^6]:(S3xS3)", 
  "3x(4^2x2).2^3.S3", "3x(4x2^2).2^4.S3", "2xFi22N5", "5:4xS5x2", "P1/G1/L1/V2/ext3", "P1/G1/L1/V1/ext3", "L2(17).2", "L2(17)x2", "2.L2(17)", "2.A7", 
  "7:6xA5.2", "A7.2", "2xA7", "S4x3^(1+2)_+:Q8", "2x2.(3^3:(S4x2))", "2(L2(11)x2).2", "4.M22M6", "2x2^3:L3(2)x2", "L3(3)", "(2xA6.2^2).2", "2.HSM11", 
  "(4xA6).2^2", "2^4:a6", "2^4:(3xA5).2", "3x2^5.A5", "3x2^(1+4)_-:A5", "3x2^4:s5", "S6xD8", "2.(S4xS5)", "3^2.(3x3^(1+2)+):D8", "3^3.3^(1+2):8", "HNN3", 
  "3^4.3^2.Q8", "3^4:3^2:D8", "109:54", "5^(1+2):(24:2)", "2x5^2:2A5", "U3(3)", "L2(23)", "2^2.2^8:s3", "7^(1+2):(S3x3)", "113:56", "3x(3xA6):2_2", 
  "2.L2(19)", "L2(19).2", "(2^(1+4)x3).GO+(4,2)", "3.2^(2+4):(S3xS3)", "7^2:(3x2S4)", "7:6xL3(2)", "(7:3xL2(7)):2", "2x7^2:(3x2A4)", "3x5:4xS5", "a5wc2", 
  "(A5xA5):2", "3x(2.A5xD10).2", "5xIsoclinic(2.A6.2_2)", "2.A5xA5", "(D10xA6).2", "3xFi22N5", "11^2:60", "3xL2(17)", "3.A7", "A7x3", "4.M22M5", "2^6:S5", 
  "4.2^4.S5", "M24C2B", "5^3:62", "L2(25)", "M11", "3x2.(2xL2(11))", "2.HS.2N5", "5^(1+2):(4x4):4", "2^3:L3(2)xS3", "6x2^3:L3(2)", "S4xL3(2).2", 
  "L2(16).2", "suzs2", "7^(1+2):(D8x3)", "(3^(1+2)_+:2x13:6).2", "12.M22M7", "3x2^4:(3xA5)", "2.(S3xS6)", "(A6xA4).2", "12.A6.2_3", "3.A6.(2x4)", 
  "(S3xS3):2xS5", "3^3.(3x3^(1+2)+):2^2", "3x5^(1+2):3:8", "s3xpsl(2,8).3", "2^2.[2^6].(S3xS3)", "NRS(M24,2^(4+4))", "2^(2+2+4).(S3xS3)", "3^4:S5", 
  "3^4:(2xA5)", "2.L2(17).2", "L2(27)", "Co1N5", "2.A7.2", "2.(2xA7)", "S7x2", "Isoclinic(2.A7.2)", "2.2^8.f20", "3xL2(19)", "(7xL2(8)).3", "2^(3+6):21", 
  "P11/G1/L1/V2/ext2", "P11/G1/L1/V1/ext2", "P11/G1/L1/V3/ext2", "P11/G2/L1/V1/ext2", "4^3.L3(2)", "4^3:psl(3,2)", "P11/G2/L1/V2/ext2", "L3(3)x2", 
  "L3(3).2", "3x4_1.2^4:A5", "2^6:(3xA5)", "2^5:A6", "3x4_2.2^4:A5", "P21/G1/L1/V1/ext2", "M22.2M3", "3x2.M22M5", "(2^4:S5x3).2", "2^4.s6", "(D8xA6).2^2", 
  "McL.2N3", "3^(1+4)_+.2S4", "3^3.3^(1+2):8.2", "3^4.(3xSL(2,3)).2", "HN.2N3", "(3^(1+2)+x3^2):2S4", "5^(1+2):4S4", "5^2:4s5", "2xU3(3)", "U3(3).2", 
  "L2(23).2", "2.L2(23)", "L2(29)", "2^2.[2^9]:S3", "7^(1+2):(S3x6)", "3.(3xM10):2", "S3x3.S6", "Isoclinic(2.L2(19).2)", "2.L2(19).2", "2^6:3^(1+2).D8", 
  "(A4x2(A4xA4).2).2", "2x(7:3xL2(7)):2", "(2.D10xA6).2", "h4", "6xFi22N5", "2.(A5xA5).2", "(2.A5xA5):2", "2.(A5wr2)", "(A5xA5):4", "6x5:4xS5", "5:4xS6", 
  "(A5xA5):2^2", "P1/G2/L1/V1/ext3", "L2(31)", "6.A7", "2.A7x3", "(A7x3).2", "2x(3.A7)", "3.A7.2", "A7xS3", "P1/G1/L1/V1/ext4", "2^(1+6)_+:S5", "2.HSM10", 
  "3^4:2^3.S4(a)", "3^4:2^3.S4", "L2(25).2_1", "L2(25).2_2", "L2(25).2_3", "2.L2(25)", "2xM11", "3x4.M22M6", "L2(16).4", "RuN2", "7^(1+2)_+:(3xD16)", 
  "7^2:2psl(2,7)", "7^(1+2):48", "2.(A6xA4).2", "3.M22M2", "S6xS4", "3.3^4.3^2.Q8", "3.McL.2N5", "2^(4+4).(S3xS3).2", "L2(27).2", "2.L2(27)", "2xCo1N5", 
  "A8", "L3(4)", "2.[2^9]:5:4", "2^(1+6)_-3.3.3^2:2", "2.4^3.L3(2)", "4^3.(L3(2)x2)", "P11/G3/L3/V1/ext2", "2.2^6.L3(2)", "P11/G3/L1/V1/ext2", 
  "P11/G3/L4/V2/ext2", "2^(3+1+3).L3(2)", "2^1+6.psl(3,2)", "2^3.(2x2^3.L3(2))", "4^3:(L3(2)x2)", "(D10x3.A6).2_3", "(2xL3(3)).2", "2^5.S6", 
  "2^6:(3xA5):2", "2.2^4.S6", "4.M22M2", "3x4.M22M5", "2^5:S6", "3^(1+4)_+:(S3xQD16)", "3^(1+4)+.4S4", "3^(1+4):4S4", "3xL2(25)", "3xM11", "2x5^2:4S5", 
  "2xU3(3).2", "Isoclinic(2xU3(3).2)", "Isoclinic(2.L2(23).2)", "2.L2(23).2", "L2(29).2", "2.L2(29)", "3xL2(16).2", "2.2^(4+6).2.S3", "2^(1+8).D8.S3", 
  "SuzN2", "3x7^(1+2):(D8x3)", "7^(1+2)_+:(6xS3).2", "L2(37)", "U4(2)", "3^4:2^(1+4)D10", "(3^2:4xa6).2", "ONM5", "(D10x2^3.L3(2)).2", "2^2.[2^7*3^2].S3", 
  "2.(A4x2(A4xA4).2).2", "BN7", "s5wrs2", "2.(A5xA5).4", "(A5xA5).(2x4)", "2.(A5xA5).2^2", "F3+N5", "Sz(8)", "sl25ex", "3^4:A6", "L2(27).3", "L2(31).2", 
  "2.L2(31)", "5^(1+2)+:4A5", "5^3:(2xA5).2", "Isoclinic(6.A7.2)", "6.A7.2", "(2.A7x3).2", "S7xS3", "3.s7x2", "2.(2x3.A7)", "P2/G2/L1/V1/ext2", 
  "P2/G2/L1/V2/ext2", "P2/G1/L1/V1/ext2", "S3wrS4", "2.3^4.2^3.S4", "(2x3^4:2^3).S4", "L2(25).2^2", "Isoclinic(L2(25).2_3x2)", "2.L2(25).2_1", 
  "Isoclinic(2.L2(25)x2)", "2.L2(25).2_2", "2^(5+5):31", "3x4^3.L3(2)", "L2(32)", "2.RuN2", "ThN2", "7^2:2.L2(7).2", "3xL3(3).2", "L2(41)", "2.(S6xS4)", 
  "6.M22M2", "2^4:3.S6", "3^5:(3^2:SD16)", "3.McL.2N3", "3.(3^(1+2)+x3^2):2S4", "NDG(Co1,5^2)", "3xU3(3).2", "G2(4)N2", "3xF3+N7", "P1/G1/L1/V1/ext5", 
  "2.L2(27).2", "L2(43)", "2.L3(4)", "2^4:a7", "A8.2", "L3(4).2_3", "L3(4).2_2", "2.A8", "L3(4).2_1", "2xA8", "2^(2+6):3^3:S3", "3.(A4x2(A4xA4).2).2", 
  "2^6:3^3:S4", "2^(1+6)_+.L3(2).2", "P11/G4/L1/V1/ext2", "(a6xa5).2", "(2.D10x3.A6).2_3", "(A6xA5):2", "P1/G3/L2/V1/ext3", "3xL2(31)", "L3(3)xD8", 
  "2^(4+4):(3xA5)", "2.(2^5:S6)", "2.2^5.S6", "2^6:S6", "4.3^(1+4)_+.2S4", "3^(1+4)+.2^(1+4)-.S3", "3^4:2(A4xA4).2", "(3xL2(25)).2_2", "3x2.L2(25)", 
  "M11xS3", "2.L2(29).2", "(3xL2(16):2).2", "2.SuzN2", "HNN2", "2^(2+1+2).2^(1+1+2).2^2.S4", "2.2^(2+2).2^(1+1+2+2):S4", "3.ON.2N7", "2.U4(2)", 
  "(3^2:8xA6).2", "(3^2:4xA6).2^2", "U4(2).2", "3xS6xS4", "(3^2:4x2.A6).2", "NDG(HN,3^2)", "3^4:2^(1+4).(5:4)", "L2(47)", "13^1+2.2A4", "11^(1+2)+:40", 
  "L3(2)wr2", "2.BN7", "(L3(2)xL3(2)):2", "(2x2.(A5xA5)):2^2", "S4x5^2:4S4", "2.Sz(8)", "2x3^4:A6", "3^4:(2xA6)", "3^(2+4):80", "3^(1+4):2S5", 
  "3^(1+4):4A5", "3^4:m10", "3^4:2.A6", "3^4:S6", "L2(49)", "2.L2(27).3", "L2(27).6", "2.L2(31).2", "5^3:(4xS5)", "5^(1+2):GL2(5)", "A8x3", "(A7xA4):2", 
  "L3(4).3", "3.L3(4)", "2^(1+8)_+.(2xA5)", "P1/G2/L2/V2/ext4", "P1/G2/L1/V1/ext4", "P1/G2/L1/V2/ext4", "(2^2x3^4).2^3.S4", "4.L2(25).2_3", "U3(4)", 
  "L2(25).(2x4)", "2^6:(psl(3,2)xs3)", "P41/G1/L1/V2/ext2", "P41/G1/L1/V1/ext2", "P41/G1/L1/V4/ext2", "3x(2xL3(3)).2", "12.M22M2", "2x3^5:(3^2:SD16)", 
  "LyN3", "Co3N3", "NDG(2.Co1,5^2)", "11^2:(5x2.A5)", "2^(2+8).2^2.(3xS3)", "2^(1+8).2^2.S3^2", "2^(4+6).2^2.(3xS3)", "2.G2(4)N2", "3xSuzN2", "3.F3+.2N7", 
  "L2(53)", "3xU4(2)", "3.ONM5", "P1/G1/L1/V1/ext6", "3.ONM6", "(3^(1+2):4xA6).2", "P1/G1/L1/V2/ext6", "Fi22N3", "Isoclinic(2.A8.2)", "2^2.L3(4)", 
  "L3(4).2^2", "2.A8.2", "Isoclinic(2.L3(4).2_3)", "2.L3(4).2_3", "Isoclinic(2.L3(4).2_2)", "2.L3(4).2_2", "Isoclinic(2.L3(4).2_1)", "4_2.L3(4)", 
  "Isoclinic(S8x2)", "2.L3(4).2_1", "4_1.L3(4)", "S8x2", "S4wrS3", "6.(A4x2(A4xA4).2).2", "2^(1+6)_-.3^3.S4", "2^{1+6}:3^{1+2}:2A4", "2^2.[2^9]:(7xS3)", 
  "P12/G1/L2/V1/ext2", "2^(3+3+3).L3(2)", "(A6:2_2xA5).2", "2.(A6xA5).2", "3.F3+N5", "S6xS5", "(A6x2.A5).2", "Sz(8).3", "P21/G1/L1/V1/ext3", 
  "P21/G1/L3/V2/ext3", "3^4:2(A4xA4).4", "3^(1+4).2^(1+1+2+2).S3", "F4(2)M13", "M12", "D8xU3(3).2", "2^(1+8).2^4.2.S3", "2^(1+8).2^3.2^2.S3", 
  "2^(1+8).2^(1+4).S3", "2^(4+8).(2xA4)", "2^5.2^6.D8.S3", "3x7^2:2.L2(7).2", "5:4xS7", "L2(59)", "NDG(HN.2,3^2)", "3x2.(S6xS4)", "2.U4(2).2", 
  "3.3^5:(3^2:SD16)", "3^2.(3^(1+4)_+.2S4)", "7:6xA7", "(7:3xA7):2", "2^(1+8)_+:(S3xS3xS3)", "L2(61)", "7^(1+2).Sp(2,7)", "2^2.Sz(8)", "3^4:(M10x2)", 
  "2.(2x3^4:A6)", "2x3^4:(2xA6)", "3^(1+4):4S5", "HN.2M13", "L2(49).2_3", "2.L2(49)", "L2(49).2_1", "L2(49).2_2", "2.L2(27).6", "2x5^(1+2):GL2(5)", 
  "5^3:(4x(2xA5).2)", "S7xS4", "6.L3(4)", "3.L3(4).2_1", "(A8x3).2", "3.L3(4).2_2", "3.2^4:a7", "L3(4).3.2_2", "3.L3(4).2_3", "L3(4).3.2_3", "3x2.A8", 
  "3xL3(4).2_2", "2.(A7xA4).2", "L3(4).6", "A8xS3", "P11/G1/L1/V1/ext3", "P11/G2/L1/V1/ext3", "2^(1+6)_-.2^4.A5", "U3(4).2", "HNN5", "U3(5)", 
  "P41/G2/L1/V1/ext2", "(3.A6xA5):2", "f22s2", "2^12.(2^2xD8)", "2^6:3.s6", "3^2+4:2(2^2xa4)2", "(D10x(A5xA5).2).2", "2^(1+8)_+.(A4xA4).2", 
  "2^(2+1+2+4+2).(3xS4)", "3x2.SuzN2", "L2(67)", "3^3:L3(3)", "3.ON.2N3", "S3xU4(2)", "(3^(1+2):4x2.A6).2", "(3^(1+2):8xA6).2", "(3xU4(2)):2", "3.ON.2M4", 
  "Co1N3", "2xFi22N3", "2.L3(4).(2^2)_{1*2*3*}", "4_2.L3(4).2_1", "Isoclinic(4_2.L3(4).2_3)", "2^2.L3(4).2_3", "4_1.L3(4).2_2", "2.L3(4).(2^2)_{123}", 
  "2.L3(4).(2^2)_{1*23}", "2.L3(4).(2^2)_{12*3}", "(2x4).L3(4)", "2.L3(4).(2^2)_{123*}", "4_2.L3(4).2_2", "4_2.L3(4).2_2*", "Isoclinic(4_1.L3(4).2_1)", 
  "Isoclinic(4_1.L3(4).2_2)", "2.L3(4).(2^2)_{12*3*}", "2.L3(4).(2^2)_{1*2*3}", "2.L3(4).(2^2)_{1*23*}", "4_2.L3(4).2_3", "P27/G1/L1/V1/ext2", 
  "2^2.L3(4).2_1", "4_1.L3(4).2_3", "2^2.L3(4).2_2", "4_1.L3(4).2_1", "Isoclinic(4_2.L3(4).2_1)", "4_1.L3(4).2_3*", "L2(32).5", "(A4wr2^2):2", 
  "2^(1+6).3^(1+2).2S4", "P13/G1/L2/V1/ext2", "P13/G1/L6/V1/ext2", "3.F3+.2N5", "3^5:M10", "3.3^(1+4):2S5", "J1", "L2(71)", "A9", "3.L3(4).3", 
  "2^{1+8}_+:(S3xA5)", "2^(4+6):(A5x3)", "P21/G2/L2/V3/ext2", "2^(2+8):(3xA5)", "P21/G2/L2/V1/ext2", "P21/G2/L5/V2/ext2", "P21/G2/L1/V3/ext2", 
  "P21/G2/L1/V1/ext2", "3^4:2(S4xS4).2", "2.(3^(1+4).[2^7.3])", "M12.2", "2.M12", "2xm12", "(Q16xU3(3)).2", "L2(73)", "2^10.2^3.S4", "(2^2xU4(2)):2", 
  "2x2.U4(2).2", "2x3.3^5:(3^2:SD16)", "7:6xS7", "(7:3x2.A7):2", "3x2^(2+8).2^2.(3xS3)", "3x2^(4+6).2^2.(3xS3)", "2.2^(1+8)_+:(S3xS3xS3)", "2^6:(7xL2(8))",
  "3^4.A6.D8", "L2(49).2^2", "2.L2(49).2_2", "Isoclinic(2.L2(49)x2)", "Isoclinic(L2(49).2_3x2)", "2.L2(49).2_1", "3.Fi22N3", "ThN3", "S8xS3", 
  "6.L3(4).2_2", "Isoclinic(6.L3(4).2_2)", "L3(4).D12", "Isoclinic(6.L3(4).2_1)", "6.L3(4).2_3", "6.L3(4).2_1", "3.L3(4).2^2", "(3xL3(4).2_2).2", 
  "Isoclinic(6.L3(4).2_3)", "2^2.L3(4).3", "12_2.L3(4)", "12_1.L3(4)", "(2.A8x3).2", "(2^2x3).L3(4)", "2.2^4+6:S5", "L2(79)", "Isoclinic(2xU3(4).2)", 
  "U3(4).4", "LyN5", "U3(5).2", "2^2.[2^9]:(7:3xS3)", "2^(1+8)+:L2(8)", "2^{3+6}:(L3(2)x3)", "(3.A6.2_2xA5):2", "(3.A6x2.A5).2", "L2(64)", "2.Fi22N2", 
  "Co2N2", "3^2.(3^4:A6)", "L2(81)", "2.SuzM11", "3.(3^(1+4).[2^7.3])", "3^(2+4):2(S4xD8)", "3xM12", "L2(83)", "5^2:4S4xS5", "(D10x2.(A5xA5).2).2", 
  "S4xU3(3).2", "2^(4+8):(A4xS3)", "(2^5.2^6.2^2)b.S3^2", "2^(1+8).2^4.S3^2", "(2^5.2^6.2^2)a.S3^2", "(A7xA5):2", "2x(3xU4(2)):2", "(3x2.U4(2)):2", 
  "(3^(1+2):8x2.A6).2", "affine", "NDG(2.Co1,3^3)", "2xS3xU4(2)", "A4xU4(2)", "S3xU4(2).2", "3^5.3^3.(2xS4)", "(3^(1+6).3)a.2.S4", "3^5.3^(1+2).2.S4", 
  "2xCo1N3", "11+^(1+2):(5x2S4)", "4_1.L3(4).(2^2)_{1*23*}", "4^2.L3(4)", "4_1.L3(4).(2^2)_{12*3}", "4_1.L3(4).(2^2)_{12*3*}", "2^(1+6)_+:A7", 
  "4_1.L3(4).(2^2)_{1*2*3*}", "4_1.L3(4).(2^2)_{1*23}", "2^4.a8", "4_2.L3(4).(2^2)_{1*23*}", "4_2.L3(4).(2^2)_{12*3}", "4_1.L3(4).(2^2)_{1*2*3}", 
  "4_2.L3(4).(2^2)_{1*23}", "4_1.L3(4).(2^2)_{123*}", "4_2.L3(4).(2^2)_{1*2*3*}", "4_2.L3(4).(2^2)_{1*2*3}", "4_2.L3(4).(2^2)_{123}", "2^4:a8", 
  "4_2.L3(4).(2^2)_{12*3*}", "4_1.L3(4).(2^2)_{123}", "2^2.L3(4).2^2", "2^6:S7", "4_2.L3(4).(2^2)_{123*}", "O8+(3)M27", "2^3+8:L3(2)", "(2^2xSz(8)):3", 
  "2^2.Sz(8).3", "3^5:2S6", "3.3^(1+4):4S5", "3^5:(M10x2)", "J1x2", "L2(89)", "A9.2", "2.A9", "2xA9", "3.L3(4).6", "3.L3(4).3.2_3", "3.L3(4).3.2_2", 
  "P11/G3/L1/V1/ext3", "P11/G3/L1/V2/ext3", "2^(4+6):(A5x3):2", "2^(2+8):(3xA5):2", "2^(1+8)_+.(A4xA5)", "3x2^(1+6)_-.2^4.A5", "P21/G1/L1/V1/ext4", 
  "P21/G3/L2/V1/ext2", "2^2+8(a5xs3)", "2.2^(2+8).(3xA5)", "2.2^(4+6).(A5x3)", "L3(5)", "3.U3(5)", "U3(5).3", "2.M12.2", "Isoclinic(2.M12.2)", "M12.2x2", 
  "2x2.M12", "2^6:u3(3)", "g61", "2^(5+8):(S3xD8)", "2^(5+8):(2xS4)", "2^10.2^2.2^2.S4", "2^10.2^3.2^3.S3", "3xFi22N2", "2.(2^2xU4(2)).2", 
  "3.3^(2+4):2(A4x2^2).2", "2^2.(2^(1+8)_+:(S3xS3xS3))", "M22", "L2(97)", "3xS3xU4(2)", "3^4:GL2(9)", "4.L2(49).2_3", "2x3.Fi22N3", 
  "6.L3(4).(2^2)_{1*2*3}", "6.L3(4).(2^2)_{1*23}", "6.L3(4).(2^2)_{123}", "6.L3(4).(2^2)_{123*}", "12_1.L3(4).2_1", "(a4xpsl(3,4)):2", 
  "6.L3(4).(2^2)_{12*3}", "2^6:3A7", "(2x12).L3(4)", "6.L3(4).(2^2)_{1*23*}", "6.L3(4).(2^2)_{12*3*}", "(A8xA4):2", "2^2.L3(4).6", "12_2.L3(4).2_3", 
  "12_2.L3(4).2_2", "12_2.L3(4).2_1", "12_1.L3(4).2_3", "2^2.L3(4).3.2_2", "(2^2x3).L3(4).2_3", "(2^2x3).L3(4).2_2", "(2^2x3).L3(4).2_1", "12_1.L3(4).2_2",
  "2^2.L3(4).3.2_3", "6.L3(4).(2^2)_{1*2*3*}", "2.2.2^4+6:S5", "2^9.2^4.A5a", "2^9.2^4.A5b", "2xBN5", "2xU3(5).2", "Isoclinic(U3(5).2x2)", "3^(3+6):26", 
  "L2(101)", "(A6xA6):2^2", "3xJ1", "2.L2(81)", "L2(81).2_1", "L2(81).2_2", "L2(81).2_3", "A6xL2(8):3", "A9x3", "L2(103)", "6.(3^(1+4).[2^7.3])", 
  "3xM12.2", "(5^2:4S4x2.A5):2", "3x2^10.2^3.S4", "2.(A7xA5).2", "J2", "S7xS5", "L2(107)", "3x(2^2xU4(2)):2", "2^2xS3xU4(2)", "(A4xU4(2)):2", 
  "2.(A4xU4(2))", "2x(3x2.U4(2)):2", "2x3^5.3^(1+2).2.S4", "2x(3^(1+6).3)a.2.S4", "2x3^5.3^3.(2xS4)", "13^(1+2):(3x4S4)", "L2(109)", "P43/G3/L1/V2/ext2", 
  "P43/G3/L1/V1/ext2", "P43/G1/L1/V1/ext2", "P11/G1/L1/V2/ext4", "P11/G1/L1/V1/ext4", "P11/G1/L1/V3/ext4", "2^5.2^6.(2xL3(2))", "(2^(1+8).2^3)b.L3(2)", 
  "2.2^3+8:L3(2)", "(2^(1+8).2^3)a.L3(2)", "2.(2^2xSz(8)):3", "3^(2+4):2A5.D8", "3^1+4:4s6", "L2(113)", "2x2.A9", "Isoclinic(2.A9.2)", "S9x2", "2.A9.2", 
  "(2^2x3).L3(4).3", "2^(2+8):(S5xS3)", "2^(1+8).2^2.(3xA5).2", "2.SuzM9", "L3(5).2", "5^2.5.5^2.4A5", "3.U3(5).2", "U3(5).3.2", "2^(1+8)_+:L2(8):3", 
  "P49/G1/L1/V1/ext2", "2^6:u3(3):2", "2^(1+8)_+.2^3.2^5.S3", "2^(1+8)_+.2^3.2^2.2^3.S3", "2^(1+8)_+.2^2.2^2.2^4.S3", "3x2.Fi22N2", "P2/G1/L1/V1/ext3", 
  "P2/G2/L1/V1/ext3", "3.3^(2+4):2(S4xD8)", "6.SuzM11", "(A7xL2(7)):2", "(13:6xL3(3)).2", "L2(121)", "2.M22", "M22.2", "2xM22", "5^(1+4):4.3^2:D8", 
  "6xS3xU4(2)", "3^1+4:2^1+4.s5", "ThM7", "ThN3B", "(4^2x3).L3(4)", "2.(A8xA4).2", "2^2.L3(4).D12", "(A4xL3(4):2_3):2", "2.(A4xL3(4)).2", "S8xS4", 
  "2^(1+6)_+:3A7", "L2(125)", "S4(4)", "2^3.2^2.2^6.(3xL3(2))", "(A6xA6).D8", "(S6xS6):2", "2.(A6xA6).2^2", "L2(81).2^2", "2.L2(81).2_2", "L2(81).4_2", 
  "Isoclinic(2.L2(81)x2)", "Isoclinic(L2(81).2_3x2)", "2.L2(81).2_1", "L2(81).4_1", "A9xS3", "S6xL2(8):3", "(A9x3):2", "2.A9x3", "3xS9", 
  "P11/G4/L1/V1/ext3", "P41/G1/L1/V1/ext3", "P41/G1/L1/V3/ext3", "3x2^(2+8):(A5xS3)", "2^4+6:3a6", "(2^2x3).(3^(1+4).[2^7.3])", "3.U3(5).3", "S3xM12.2", 
  "3xIsoclinic(2.M12.2)", "2^2.(U3(3).2xS4)", "2^(1+1+2+4).(2x2^(2+4).S3^2)", "3x2^10.2^2.2^2.S4", "3x2^(5+8):(S3xD8)", "3x2^(5+8):(2xS4)", 
  "2^(5+8):(S3xS4)", "(2x2^(1+8)_+).2.2^4.(S3xS3)", "(7^2:(3x2A4)xL2(7)).2", "2.J2", "J2.2", "S4xU4(2).2", "3x2.(2^2xU4(2)).2", "O7(3)N3A", 
  "3^(3+4):2(S4xA4)", "2^6:A8", "3.M22", "2^10.2^3.L3(2)", "(A4x3.L3(4)).2", "S6(2)", "2^(4+8):(S3xA5)", "2^6.2^5.S6", "13^2:2.L2(13).4", "5^2.5.5^2.4S5", 
  "5^(1+4):GL(2,5)", "2.2^6:u3(3):2", "L2(64).6", "11^2:(5x2L2(11).2)", "P50/G1/L1/V1/ext2", "2^6.U4(2)", "(2.A7xL2(7)).2", "(L2(11)xL2(11)):4", 
  "2x2.M22", "Isoclinic(2.M22.2)", "2.M22.2", "4.M22", "A10", "(A7xA6):2", "P27/G1/L1/V1/ext3", "2^2x3xS3xU4(2)", "L3(7)", "3^5:M11", "S4(4).2", 
  "2^10.2^4.S5", "5^(1+4):2^(1+4).5.4", "(2^5.2^6)a.(S3xL3(2))", "(2^5.2^6)b.(L3(2)xS3)", "2^3.2^2.2^6.(S3xL3(2))", "(S6xS6).4", "(S6xS6).2^2", 
  "4.L2(81).2_3", "L2(81).(2x4)", "2.L2(81).4_1", "S9xS3", "2.A9xS3", "(2.A9x3).2", "3xIsoclinic(2.A9.2)", "P12/G1/L2/V1/ext3", "2.SuzM7", 
  "(3x2^(2+8):(A5xS3)).2", "3x2.SuzM9", "2^(4+6):3S6", "3.U3(5).S3", "2^(4+10).(S4xS3)", "J2.2x2", "(A8xA5):2", "Isoclinic(2.J2.2)", "2.J2.2", 
  "2.O7(3)M9", "3^(3+4):2(S4xS4)", "(D10xU3(5)).2", "2^6:S8", "2^(1+6)_+.A8", "P31/G1/L1/V1/ext2", "3.M22.2", "6.M22", "2x3.M22", 
  "2^3.(2x2^(1+3+3+3).L3(2))", "2xS6(2)", "6.SuzM8", "2.S6(2)", "(A4x3.L3(4).2_3).2", "P13/G1/L2/V1/ext3", "2.2^(4+8):(S3xA5)", "(A5xU4(2)):2", "U4(3)", 
  "P41/G2/L1/V1/ext3", "2^6:U4(2).2", "3x2^(4+6).3A6", "2^1+6.u4q2", "2^6.U4(2).2", "(7:3x2.L3(4).2).2", "3x2^(5+8):(S3xS4)", 
  "3x(2x2^(1+8)_+).2.2^4.(S3xS3)", "Isoclinic(4.M22.2)", "4.M22.2", "S7xS6", "(D10xA9).2", "2.A10", "3xJ2.2", "A10.2", "2^(1+8).(A5xA5).2", "L3(7).2", 
  "3.O7(3)M9", "2x3^5:M11", "3^5:(2xm11)", "3^5:(M11x2)", "S4(4).4", "2^10:(2^5:s5)", "5^(1+4)_+:(4Y2^(1+4)_-.5.4)", "3^(3+3):L3(3)", "3^6:L3(3)", 
  "2^(6+6):(S3xL3(2))", "3x2^10.2^3.L3(2)", "3^4.2U4(2)", "[7^6]:(6x6)", "G2(3)", "4.L2(81).4_2", "(A9xA4):2", "(A6xU3(3)):2", "3xS6(2)", "3x2^6.2^5.S6", 
  "3x2^(4+8):(S3xA5)", "S4(5)", "S8xS5", "3^(1+6):2^(3+4):3^2:2", "3^(3+4):(2.S4)^2", "5:4xU3(5):2", "(2x2^(1+6)_+).A8", "6.M22.2", "Isoclinic(6.M22.2)", 
  "2x6.M22", "12.M22", "2^(1+1+3+3).(2x2^(3+3).L3(2))", "U3(8)", "3.L3(7)", "L3(7).3", "U3(7)", "3^6.M11", "2^2xS6(2)", "2x2.S6(2)", "2^(5+8):(2xA6)", 
  "2^2.2^(4+8):(S3xA5)", "3x2^10.2^4.S5", "L4(3)", "3^5.U4(2)", "3^5:U4(2)", "U4(3).2_3", "2.U4(3)", "U4(3).2_1", "U4(3).2_2", "3x2.SuzM7", 
  "(3x2^(4+6):3A6).2", "2^(1+6)_-.U4(2).2", "2.SuzM4", "Isoclinic(2.A10.2)", "3x2.J2.2", "S3xJ2.2", "2.A10.2", "S10x2", "2^(1+8)_+.(A5xA5).2^2", 
  "6.O7(3)M9", "P48/G1/L1/V2/ext2", "P48/G1/L1/V1/ext2", "2x3^(3+3):L3(3)", "3^4.2U4(2).2", "2xG2(3)", "G2(3).2", "6xS6(2)", "(2.A6xU3(3)).2", "S3xS6(2)", 
  "S9xS4", "3x2.S6(2)", "3x2.2^(4+8):(S3xA5)", "2^(3+8):(S3xS6)", "5^(1+4):4S6", "2.S4(5)", "S4(5).2", "3_1.U4(3)", "3_2.U4(3)", "3x2^(1+6)_-.U4(2)", 
  "L5(2)", "3^(1+6)_+:2^(3+4):(S3xS3)", "2.(3^(1+6):2^(3+4):3^2:2)", "M23", "P27/G1/L1/V1/ext4", "2^9.L3(4)", "2^5.2^4.L4(2)", "2^8:S8", "(S5xS5xS5):S3", 
  "(11:5xM12):2", "Isoclinic(12.M22.2)", "12.M22.2", "3x(D10xA9).2", "(A10x3):2", "3xA10.2", "U3(8).2", "3xL3(7).2", "L3(7).S3", "3.L3(7).2", "U3(7).2", 
  "M11xA6.2^2", "3^6:(M11x2)", "2x3^6.M11", "D8xS6(2)", "2^(1+8)_+.2^5.S4(2)", "2^(4+10)(S5xS3)", "(D10xJ2).2", "L4(3)x2", "L4(3).2_3", "L4(3).2_2", 
  "2.L4(3)", "L4(3).2_1", "3.(3^(3+3):L3(3))", "3^5:U4(2):2", "3^(1+4).2U4(2)", "3.G2(3)", "Fi23N3", "2.U4(3).2_2", "U4(3).4", "Isoclinic(2.U4(3).2_2)", 
  "Isoclinic(2.U4(3).2_1)", "2.U4(3).2_3", "2xU4(3).2_2", "2.U4(3).2_1", "U4(3).(2^2)_{133}", "4.U4(3)", "U4(3).(2^2)_{122}", "Isoclinic(2.U4(3).2_3)", 
  "P49/G1/L1/V1/ext3", "P49/G1/L1/V2/ext3", "2^(1+8)_+:U4(2)", "U5(2)", "P3L62", "3.3^(1+6):2^(3+4):3^2:2", "L3(8)", "U3(8).3_1", "U3(8).3_3", 
  "U3(8).3_2", "3.U3(8)", "3.L3(7).3", "2^2x3xS6(2)", "2xS3xS6(2)", "2^(5+8):(2x3.A6)", "2^(5+8):(S3xA6)", "3x2^2.2^(4+8):(S3xA5)", "2F4(2)'", 
  "2.S4(5).2", "3.3^5.U4(2)", "P50/G1/L1/V1/ext3", "6_1.U4(3)", "3_2.U4(3).2_3", "3_2.U4(3).2_3'", "S3xU4(3)", "3_1.U4(3).2_2'", "3_1.U4(3).2_2", 
  "3_1.U4(3).2_1", "3_2.U4(3).2_1", "6_2.U4(3)", "3x2.SuzM4", "(3x2^(1+6)_-.U4(2)).2", "A11", "L5(2).2", "2E6(2)N3C", "2^10.A8", "2^(1+8):S8", 
  "2.U6(2)M3", "S10xS3", "(A5xA9):2", "5^(1+4).2^(1+4).A5.4", "2.(D10xJ2).2", "L4(3).2^2", "2.L4(3).2_1", "2.L4(3).2_2", "2.L4(3).2_3", 
  "2x3.(3^(3+3):L3(3))", "(2x3^5).U4(2).2", "3^(1+4).2U4(2).2", "3^5:(2xU4(2).2)", "2x3^5:U4(2):2", "(3xG2(3)):2", "3.G2(3).2", "2x3.G2(3)", 
  "4.U4(3).2_1", "2.U4(3).(2^2)_{12*2*}", "4.U4(3).2_2", "2.U4(3).(2^2)_{133}", "2.U4(3).(2^2)_{1*22}", "2.U4(3).(2^2)_{1*33}", "2.U4(3).(2^2)_{1*2*2}", 
  "2.U4(3).(2^2)_{13*3}", "2.U4(3).(2^2)_{12*2}", "2.U4(3).4", "U4(3).D8", "4.U4(3).2_3", "2.U4(3).(2^2)_{1*3*3}", "2x2.U4(3).2_2", "2.U4(3).(2^2)_{122}", 
  "2.U4(3).(2^2)_{13*3*}", "2.U4(3).(2^2)_{1*3*3*}", "2.U4(3).(2^2)_{1*2*2*}", "2xU4(3).(2^2)_{122}", "2.2^(1+8)_+:U4(2)", "U5(2).2", "2xU5(2)", 
  "2^11.2^6.3^(1+2).D8", "3^2.U4(3)", "P2L62", "3.U6(2)M3", "Sz(32)", "L3(8).2", "U3(8).S3", "U3(8).6", "3.U3(8).2", "3.L3(7).S3", "7^(2+1+2):GL2(7)", 
  "S4xS6(2)", "2^(5+8):(S3xS6)", "2^(1+5+8).(S3xA6)", "2F4(2)'.2", "2x2F4(2)'", "3xL4(3).2_2", "3.3^5:U4(2):2", "6_1.U4(3).2_1", "3_2.U4(3).(2^2)_{133}", 
  "6_1.U4(3).2_2", "2x3_1.U4(3).2_2", "12_1.U4(3)", "6_1.U4(3).2_2'", "12_2.U4(3)", "6_2.U4(3).2_1", "Isoclinic(6_2.U4(3).2_3')", "6_2.U4(3).2_3'", 
  "6_2.U4(3).2_3", "3_1.U4(3).(2^2)_{122}", "S3xU4(3).2_2", "3x2^(1+8)_+:U4(2)", "2.A11", "A11.2", "3xU5(2)", "2^2.U6(2)M3", "2^1+4+6.a8", "L3(9)", 
  "U3(9)", "S5xS9", "P31/G1/L1/V1/ext3", "HS", "2^8.A9", "5^3.psl(3,5)", "L3(8).3", "3.U3(8).3_2", "Isoclinic(3.U3(8)x3)", "Isoclinic(U3(8).3_3x3)", 
  "U3(8).3^2", "3.U3(8).3_1", "J3", "2x3^(1+4).2U4(2).2", "4.U4(3).4", "2^2.U4(3).(2^2)_{122}", "2.U4(3).D8", "2^12.(S3x3S6)", "(2x2^(1+8)):U4(2):2", 
  "2^(5+8):(S3x3.A6)", "2^2.2^(1+8)_+:U4(2)", "3x2F4(2)'", "2xU5(2).2", "2^2xU5(2)", "C9Y3.3^5.U4(2)", "(S6xL3(4).2).2", "5^4:(3x2.L2(25)).2", 
  "(3^2x2).U4(3)", "3^2.U4(3).2_3'", "6.U6(2)M3", "U3(11)", "2.RuM1", "(A7x(A5xA5):2^2):2", "(A5xJ2):2", "3x2.L4(3).2_2", "6.(3^5:U4(2):2)", 
  "3x2.U4(3).(2^2)_{122}", "12_1.U4(3).2_1", "12_1.U4(3).2_2", "12_1.U4(3).2_2'", "12_2.U4(3).2_1", "12_2.U4(3).2_3", "S3x2.U4(3).2_2", "2x6_1.U4(3).2_2", 
  "S3xU4(3).(2^2)_{122}", "2xS3xU4(3).2_2", "12_2.U4(3).2_3'", "3x2.2^(1+8)_+:U4(2)", "2.A11.2", "Isoclinic(2.A11.2)", "S11x2", "6xU5(2)", "(3xU5(2)).2", 
  "7^1+4.2A7", "L3(9).2_3", "L3(9).2_2", "L3(9).2_1", "2^(4+12).(S3x3^(1+2)_+:D8)", "U3(9).2", "HS.2", "2.HS", "2^1+8.a9", "2^6:s6f2", "D8xL4(3).2_2", 
  "L3(8).6", "3.U3(8).6", "3.U3(8).S3", "U3(8).(S3x3)", "J3.2", "(2x2^(1+8)):(U4(2):2x2)", "P50/G1/L1/V1/ext4", "2.(2x2^(1+8)):U4(2):2", "A5.2xM22.2", 
  "(3^2x4).U4(3)", "3^2.U4(3).(2^2)_{133}", "Isoclinic((3^2x2).U4(3).2_3')", "S3x3_1.U4(3).2_2", "(3^2x2).U4(3).2_3'", "2^12:Sz(8)", "(2^2x3).U6(2)M3", 
  "(L2(11)xM12):2", "O8+(3)M14", "S4(7)", "3^6:2M12", "U3(11).2", "2.(A5xJ2).2", "9.U3(8).3_3", "3.J3", "(3^2:2xG2(3)).2", "2xS3x2.U4(3).2_2", 
  "2xS3xU4(3).(2^2)_{122}", "(S3x2.U4(3).2_2).2", "3x2^2.2^(1+8)_+:U4(2)", "3x(2x2^(1+8)):U4(2):2", "Sz(32).5", "2^2x3xU5(2)", "L3(9).2^2", "U3(9).4", 
  "O8+(2)", "2.HS.2", "Isoclinic(2.HS.2)", "HS.2x2", "Isoclinic(2.HSx2)", "2^1+8.2.A9", "S8(2)M3", "2^7:S6(2)", "MN5", "O8-(2)", "3^2.3^3.3^6.(S4x2S4)", 
  "3D4(2)", "L3(11)", "U3(11).3", "3.U3(11)", "3^(3+6):(L3(3)x2)", "S3x6_1.U4(3).2_2", "3^2.U4(3).D8", "A12", "M24", "2^(6+8):(A7xS3)", "G2(4)", 
  "S4(7).2", "2x3^6:2.M12", "3x2^6:S6(2)", "D8x2F4(2)'.2", "(2.A5x2.J2).2", "3.J3.2", "(5^2:[2^4]xU3(5)).S3", "(S3xS3xG2(3)):2", 
  "(2^2x2^(1+8)).(3xU4(2)).2", "3.(2x2^(1+8)):(U4(2):2x2)", "2^5.psl(5,2)", "2^5:L5(2)", "2.O8+(2)", "O8+(2).2", "4.HS.2", "2^8:S6(2)", "O8-(2).2", 
  "U3(11).S3", "3.U3(11).2", "2^10:m22", "2^10:M22'", "(3^2x2).U4(3).D8", "A12.2", "2.A12", "2.G2(4)", "G2(4).2", "7^(1+4):(3x2.S7)", "O8+(2).3", 
  "3xO8+(2)", "(QD16x2F4(2)').2", "3D4(2).3", "3.U3(11).3", "(L3(2)xS4(4):2).2", "J4M4", "Fi23M8", "2.O8+(2).2", "2^2.O8+(2)", "2^1+8:s6f2", "3xG2(4)", 
  "2^(4+12).(S3x3S6)", "S4x2F4(2)'.2", "3^(3+6):(L3(3)xD8)", "McL", "2.Fi22M5", "2^10:m22:2", "Fi22.2M4", "(3^(1+2):2^2xG2(3)):2", "Isoclinic(2.A12.2)", 
  "2.A12.2", "L4(4)", "Isoclinic(2.G2(4).2)", "2.G2(4).2", "U4(4)", "O8+(2).3.2", "(3xO8+(2)):2", "S4(8)", "[2^20]:(S3xL3(2))", "5^(2+2+4):(S3xGL2(5))", 
  "(3xO8-(2)):2", "3.U3(11).S3", "3.Fi22M5", "2^2.O8+(2).2", "(3xG2(4)).2", "3x2.G2(4)", "2.2^(4+12).(S3x3S6)", "S4(9)", "(GL(2,3)x2F4(2)').2", 
  "5:4xHS.2", "McL.2", "(3^2:D8xU4(3).2^2).2", "L4(4).2_1", "L4(4).2_3", "L4(4).2_2", "2^(3+12).(L3(2)xA6)", "2^(6+8).(S3xA8)", "2^(2+12):(A8xS3)", 
  "(A5xU3(8):3):2", "O8+(2):S3x2", "2^2.O8+(2).3", "2.F4(2)M5", "(A6xA6xA6).(2xS4)", "2^12:J2", "3.McL", "6.Fi22M5", "A13", "3xO8+(2):S3", 
  "3^(1+8).2^(1+6).3^(1+2).2S4", "S4(9).2_3", "S4(9).2_2", "S4(9).2_1", "2.(3^2:D8xU4(3).2^2).2", "L4(4).2^2", "2^(7+8).(S3xA8)", "2.2^(2+12):(A8xS3)", 
  "2^(3+12).(L3(2)xS6)", "He", "U4(4).4", "2^2.O8+(2).3.2", "3^6:L4(3)", "S6(3)", "O7(3)", "3.McL.2", "G2(5)", "(A4xG2(4)):2", "A13.2", "2.A13", 
  "6xO8+(2):S3", "S4(9).2^2", "L4(5)", "He.2", "3^6:(L4(3)x2)", "3^6:L4(3):2_2", "S6(3).2", "2.S6(3)", "O7(3).2", "2xO7(3)", "2.O7(3)", "U6(2)", 
  "3^6:2U4(3).2_1", "R(27)", "2^10:L5(2)", "5^(3+3).(2xL3(5))", "2.(A4xG2(4)).2", "2.A13.2", "Isoclinic(2.A13.2)", "(A4xO8+(2).3).2", "3.O7(3)", 
  "3^2.3^4.3^8.(A5x2A4).2", "2^12:(L4(2)xL3(2))", "2.L4(5)", "U4(5)", "3^3.[3^10].GL3(3)", "2.S6(3).2", "Isoclinic(2.O7(3).2)", "O7(3).2x2", "2.O7(3).2", 
  "U6(2).2", "2.U6(2)", "L6(2)", "2..11.m23", "c2aj4", "(2^6x2^8):S6(2)", "(2.A4x2.G2(4)).2", "S4xO8+(2):S3", "3.O7(3).2", "S3xO7(3)", "6.O7(3)", 
  "2x3.O7(3)", "3^2.3^4.3^8.(S5x2S4)", "U6(2).3", "3.U6(2)", "(A5xA12):2", "4.L4(5)", "3^(1+10)_+:2^(1+6)_-:3^(1+2)_+:2S4", "U4(5).2_2", "U4(5).2_1", 
  "U4(5).2_3", "R(27).3", "3^6.L4(3).D8", "3^3.[3^10].(L3(3)x2^2)", "2^2.U6(2)", "2.U6(2).2", "L6(2).2", "A14", "2^8:O8+(2)", "S8(2)", 
  "(2^(1+8)x2^6):S6(2)", "2^8:O8-(2)", "6.O7(3).2", "3.U6(2).2", "U6(2).3.2", "6.U6(2)", "3^(1+10)_+:(2x2^(1+6)_-:3^(1+2)_+:2S4)", "U4(5).2^2", 
  "2^10:(L5(2)xS3)", "2^2.U6(2).2", "2^12.3_1.U4(3).2_2'", "3.U6(2).3", "2.Alt(14)", "A14.2", "2^8:O8+(2):2", "2^(1+8)+.O8+(2)", "2.F4(2)M1", 
  "2^8:O8-(2):2", "(2^2x3).U6(2)", "6.U6(2).2", "2xU6(2).3.2", "2^2.U6(2).3", "3^(1+8).2^(1+6).U4(2).2", "Ru", "2^(1+12).3_1.U4(3).2_2'", "3.U6(2).3.2", 
  "U72CT", "(7:3xHe):2", "Isoclinic(2.A14.2)", "2.A14.2", "(2x2^(1+8)_+).O8+(2)", "(2^2x3).U6(2).2", "2^2.U6(2).3.2", "L5(3)", "2^12.3^2.U4(3).2_2'", 
  "U5(3)", "2.Ru", "2^(1+12)_+.3_1.U4(3).2^2_{122}", "(2^2x3).U6(2).3", "5^(1+6):2.J2.4", "2^2.U6(2):S3x2", "Suz", "ON", "L5(3).2", "3.2^(1+12).3U4(3).2", 
  "Co3", "2^11:M24", "F3+M7", "mx1j4", "A15", "Suz.2", "2.Suz", "ON.2", "2xCo3", "2^12.M24", "2.2^11:M24", "2^6:L6(2)", "A15.2", "2.Alt(15)", "3.Suz", 
  "3.ON", "Isoclinic(2.Suz.2)", "2.Suz.2", "2.A15.2", "2.Sym(15)", "6.Suz", "3.Suz.2", "3.ON.2", "S6(4)", "3^(1+10):U5(2):2", "O8+(3)", 
  "Isoclinic(6.Suz.2)", "6.Suz.2", "S6(4).2", "3^(1+10):(2xU5(2):2)", "O8+(3).2_2", "2.O8+(3)", "O8+(3).2_1", "3^7.O7(3)", "3^7:O7(3)", "O8-(3)", "A16", 
  "3^(3+2+6+6):(L3(3)xSD16)", "2^8:S8(2)", "O8+(3).3", "2^2.O8+(3)", "O8+(3).(2^2)_{111}", "O8+(3).4", "O8+(3).(2^2)_{122}", "3^7.O7(3):2", "O8-(3).2_3", 
  "2.O8-(3)", "O8-(3).2_2", "O8-(3).2_1", "3D4(3)", "2.Alt(16)", "A16.2", "O10+(2)", "O10-(2)", "O8+(3).3.2", "O8+(3).D8", "O8-(3).2^2", "2.A16.2", 
  "2.Sym(16)", "Co2", "O10+(2).2", "3^(2+5+10).(M11x2S4)", "O10-(2).2", "L4(9)", "U5(4)", "O8+(3).A4", "2^2.O8+(3).3", "Fi22", "2xCo2", 
  "3^(1+12).(2xU5(2).2)", "(3xO8+(3):3):2", "U5(4).2", "O8+(3).S4", "Fi22.2", "2xFi22", "2.Fi22", "L7(2)", "A17", "S3xO8+(3):S3", "3.Fi22", "U7(2)", 
  "S6(5)", "O7(5)", "(2xO8+(3)).S4", "Isoclinic(2.Fi22.2)", "2.Fi22.2", "2xFi22.2", "2x2.Fi22", "HN", "L7(2).2", "A17.2", "2.Alt(17)", "2x3.Fi22", 
  "6.Fi22", "3.Fi22.2", "O7(5).2", "P2L82", "2^2.Fi22.2", "HN.2", "[2^35].(S5xL3(2))", "2.Sym(17)", "2.A17.2", "3x2.Fi22.2", "S3xFi22.2", "2x6.Fi22", 
  "Isoclinic(6.Fi22.2)", "6.Fi22.2", "(S3x2.Fi22).2", "(3^2:2xO8+(3)).S4", "A18", "F4(2)", "(D10xHN).2", "A18.2", "2.Alt(18)", "F4(2).2", "2.F4(2)", 
  "2xF4(2)", "3xF4(2)", "[2^30].L5(2)", "2.A18.2", "2.Sym(18)", "2^2xF4(2)", "Isoclinic(2.F4(2).2)", "2x2.F4(2)", "2.F4(2).2", "2xF4(2).2", "6xF4(2)", 
  "3x2.F4(2)", "P1L82", "2^(2+10+20).(M22.2xS3)", "S10(2)", "(2^2xF4(2)):2", "2.(2xF4(2)).2", "Isoclinic(2x2.F4(2).2)", "6x2.F4(2)", "Ly", "A19", "O9(3)", 
  "S8(3)", "3D4(4)", "Th", "A19.2", "2.Alt(19)", "2.O9(3)", "3^8.O8-(3).2_3", "2xTh", "2^[39].(L3(2)x3.S6)", "2.Sym(19)", "S3xTh", "2^(9+16).S8(2)", 
  "3^(1+12).2.Suz.2", "3^12.6.Suz.2", "Fi23", "Co1", "L8(2)", "2xFi23", "2.Co1", "3^(1+12):6.Suz.2", "3xFi23", "O12+(2)", "2^(2+11+22).(M24xS3)", 
  "O12-(2)", "J4", "O12+(2).2", "O12-(2).2", "2^(1+22).Co2", "O10-(3)", "U6(4)", "O10+(3)", "2.O10-(3)", "2^(10+16).O10+(2)", "2E6(2)", "O8+(7)", 
  "2.2E6(2)", "2E6(2).2", "S12(2)", "E6(2)", "2.O8+(7)", "3.2E6(2)", "2E6(2).3", "2F4(8)", "2.2E6(2).2", "2^2.2E6(2)", "6.2E6(2)", "3.2E6(2).2", 
  "2E6(2).3.2", "2^2.2E6(2).2", "(2^2x3).2E6(2)", "6.2E6(2).2", "2^2.2E6(2).3", "F3+", "(2^2x3).2E6(2).2", "2^2.2E6(2).3.2", "F3+.2", "3.F3+", "3.F3+.2", 
  "2^24.Co1", "2^1+24.Co1", "2^1+24.2.Co1", "O12+(3)", "2_1.O12+(3)", "O12-(3)", "B", "2.B", "M" ];
  
CTAlmostSimple:=[ "A5", "A5.2", "L3(2)", "L3(2).2", "A6", "L2(8)", "L2(11)", "Sym(6)", "A6.2_3", "A6.2_2", "A6.2_1", "L2(13)", "L2(11).2", "A6.2^2", "L2(8).3", 
  "L2(13).2", "L2(17)", "A7", "L2(19)", "L2(16)", "L2(17).2", "A7.2", "L3(3)", "U3(3)", "L2(23)", "L2(19).2", "L2(25)", "M11", "L2(16).2", 
  "L2(27)", "L3(3).2", "U3(3).2", "L2(23).2", "L2(29)", "L2(31)", "L2(25).2_3", "L2(25).2_2", "L2(25).2_1", "L2(16).4", "L2(27).2", "A8", "L3(4)", 
  "L2(29).2", "L2(37)", "U4(2)", "Sz(8)", "L2(27).3", "L2(31).2", "L2(25).2^2", "L2(32)", "L2(41)", "L2(43)", "L3(4).2_1", "L3(4).2_2", "L3(4).2_3", 
  "A8.2", "U4(2).2", "L2(47)", "L2(49)", "L2(27).6", "L3(4).3", "U3(4)", "L2(53)", "L3(4).2^2", "Sz(8).3", "M12", "L2(59)", "L2(61)", "L2(49).2_1", 
  "L2(49).2_2", "L2(49).2_3", "L3(4).6", "L3(4).3.2_3", "L3(4).3.2_2", "U3(4).2", "U3(5)", "L2(67)", "L2(32).5", "J1", "L2(71)", "A9", "M12.2", "L2(73)", 
  "L2(49).2^2", "L3(4).D12", "L2(79)", "U3(4).4", "U3(5).2", "L2(64)", "L2(81)", "L2(83)", "L2(89)", "A9.2", "L3(5)", "U3(5).3", "M22", 
  "L2(97)", "L2(101)", "L2(81).2_1", "L2(81).2_2", "L2(81).2_3", "L2(103)", "J2", "L2(107)", "L2(109)", "L2(113)", "L3(5).2", "U3(5).3.2", "L2(121)", 
  "M22.2", "L2(125)", "S4(4)", "L2(81).4_1", "L2(81).2^2", "L2(81).4_2", "J2.2", "S6(2)", "L2(64).6", "A10", "L3(7)", "S4(4).2", "L2(81).(2x4)", "U4(3)", 
  "A10.2", "L3(7).2", "S4(4).4", "G2(3)", "S4(5)", "U3(8)", "L3(7).3", "U3(7)", "L4(3)", "U4(3).2_3", "U4(3).2_2", "U4(3).2_1", "G2(3).2", 
  "S4(5).2", "L5(2)", "M23", "U3(8).2", "L3(7).S3", "U3(7).2", "L4(3).2_1", "L4(3).2_2", "L4(3).2_3", "U4(3).(2^2)_{122}", "U4(3).(2^2)_{133}", "U4(3).4", 
  "U5(2)", "L3(8)", "U3(8).3_3", "U3(8).3_1", "U3(8).3_2", "2F4(2)'", "A11", "L5(2).2", "L4(3).2^2", "U4(3).D8", "U5(2).2", "Sz(32)", "L3(8).2", 
  "U3(8).6", "U3(8).S3", "2F4(2)'.2", "A11.2", "L3(9)", "U3(9)", "HS", "L3(8).3", "J3", "U3(11)", "L3(9).2_2", "L3(9).2_1", "L3(9).2_3", 
  "U3(9).2", "HS.2", "L3(8).6", "J3.2", "S4(7)", "U3(11).2", "Sz(32).5", "L3(9).2^2", "U3(9).4", "O8+(2)", "O8-(2)", "3D4(2)", "L3(11)", "U3(11).3", 
  "A12", "M24", "G2(4)", "S4(7).2", "O8+(2).2", "O8-(2).2", "U3(11).S3", "A12.2", "G2(4).2", "O8+(2).3", "3D4(2).3", "McL", "L4(4)", "U4(4)", 
  "O8+(2).3.2", "S4(8)", "S4(9)", "McL.2", "L4(4).2_3", "L4(4).2_2", "L4(4).2_1", "A13", "S4(9).2_1", "S4(9).2_2", "S4(9).2_3", "L4(4).2^2", "He", 
  "U4(4).4", "O7(3)", "S6(3)", "G2(5)", "A13.2", "S4(9).2^2", "L4(5)", "He.2", "O7(3).2", "S6(3).2", "U6(2)", "R(27)", "U4(5)", "U6(2).2", 
  "L6(2)", "U6(2).3", "U4(5).2_1", "U4(5).2_2", "U4(5).2_3", "R(27).3", "L6(2).2", "A14", "S8(2)", "U6(2).3.2", "U4(5).2^2", "A14.2", "Ru", 
  "L5(3)", "U5(3)", "Suz", "ON", "L5(3).2", "Co3", "A15", "Suz.2", "ON.2", "A15.2", "S6(4)", "O8+(3)", "S6(4).2", "O8+(3).2_1", "O8+(3).2_2", 
  "O8-(3)", "A16", "O8+(3).3", "O8+(3).4", "O8+(3).(2^2)_{111}", "O8+(3).(2^2)_{122}", "O8-(3).2_3", "O8-(3).2_2", "O8-(3).2_1", "Sym(16)", "A16.2", 
  "O10+(2)", "O10-(2)", "O8+(3).3.2", "O8+(3).D8", "O8-(3).2^2", "Co2", "O10+(2).2", "O10-(2).2", "L4(9)", "U5(4)", "O8+(3).A4", "Fi22", "U5(4).2", 
  "O8+(3).S4", "Fi22.2", "L7(2)", "A17", "U7(2)", "S6(5)", "O7(5)", "HN", "L7(2).2", "A17.2", "O7(5).2", "HN.2", "A18", "F4(2)", 
  "A18.2", "F4(2).2", "S10(2)", "Ly", "A19", "S8(3)", "O9(3)", "Th", "A19.2", "Fi23", "Co1", "L8(2)", "J4", "O12+(2).2", "O12-(2).2", 
  "O10-(3)", "U6(4)", "2E6(2)", "O8+(7)", "2E6(2).2", "S12(2)", "E6(2)", "2E6(2).3", "2F4(8)", "2E6(2).3.2", "F3+", "F3+.2", "B", "M" ];

CTSporadic:=[ "M11", "M12", "J1", "M22", "J2", "M23", "HS", "J3", "M24", "McL", "He", "Ru", "Suz", "ON", "Co3", "Co2", "Fi22", "HN", "Ly", "Th", "Fi23", "Co1", "J4", "F3+", "B", "M" ];

CTNonsolv:=[ "A5", "A5.2", "2xA5", "2.A5", "L3(2)", "3xA5", "2.A5.2", "2.Sym(5)", "Isoclinic(2.A5.2)", "2xS5", "5xA5", "2xL3(2)", "2.L3(2)", "L3(2).2", 
  "(A5x3):2", "3x2.A5", "A6", "3xA5.2", "2S5.2", "(2^2xA5):2", "gl25", "2.M12M8", "L2(8)", "3xL3(2)", "a5xd10", "L2(11)", "L3(2).2x2", "2.L3(2).2", 
  "(2xL3(2)).2", "2^2xL2(7)", "Isoclinic(2.L3(2).2)", "A6.2_2", "A6.2_3", "S5xS3", "3xIsoclinic(2.A5.2)", "a4xa5", "A6.2_1", "2.A6", "2xA6", "(2.A5x3).2", 
  "Sym(6)", "3x2S5", "2^4:A5", "P1/G1/L1/V1/ext2", "L3(2)xS3", "6xL3(2)", "3xL3(2).2", "3x2.L3(2)", "3.A6", "L2(13)", "5:4xa5", "(A5xD10).2", "2A5xD10", 
  "2.L2(11)", "2xL2(11)", "L2(11).2", "2^3.L3(2)", "D8xL3(2)", "2^3:sl(3,2)", "S6x2", "2.A6.2_2", "2.A6.2_1", "M10x2", "2A4xA5", "(A4xA5):2", 
  "(2xA6).2_3", "A6.2^2", "2.Sym(6)", "(3x2S5).2", "a4xs5", "2^2xA6", "3xL2(8)", "L2(8).3", "2^1+4b:a5", "2^4:s5", "P1/G2/L2/V2/ext2", "P1/G2/L1/V2/ext2", 
  "P1/G2/L1/V1/ext2", "mo62", "2.(2^4:A5)", "3xL2(11)", "3.A6.2_2", "3.A6.2_3", "6.A6", "j3m6", "(3xA6).2_1", "2x3.A6", "3.A6.2_1", "2.A6x3", "2.L2(13)", 
  "L2(13).2", "(7xL2(7)):2", "5:4x2.A5", "5:4xS5", "(2.A5xD10).2", "L2(17)", "A7", "2xL2(11).2", "2.(2xL2(11))", "2.L2(11).2", "2^(1+3):L3(2)", 
  "2^3.L3(2):2", "2x2^3:L3(2)", "2(L2(7)x4).2", "S5xS4", "2^2.S6", "A6.D8", "(4xA6):2", "(4xA6).2_3", "2.(A5xA4).2", "j3m4", "4.A6.2_3", "2.(S6x2)", 
  "2xa6.2^2", "3x2^4:A5", "(2xA6).2^2", "5^2:2A5", "S3xL2(8)", "L2(8):3x2", "3xL2(13)", "L2(19)", "7:3xpsl(3,2)", "7xL2(8)", "A5xA5", "2^{1+4}_-:2A5", 
  "P1/G3/L2/V1/ext2", "4_1.2^4:A5", "4_2.2^4:A5", "s2wrs5", "2.M22M5", "twd5a", "M22.2M4", "2^(1+4).S5", "6xL2(11)", "3x2^3.L3(2)", "3x2^3:L3(2)", 
  "s4xpsl(3,2)", "L2(16)", "6.A6.2_2", "(S3xS3xA5):2", "Isoclinic(3.A6.2_3x2)", "(3xM10):2", "S3xS6", "(2.A6x3).2_1", "3.A6.2^2", "6.A6.2_1", 
  "Isoclinic(6.A6x2)", "(2x3.A6).2", "Isoclinic(L2(13).2x2)", "2.L2(13).2", "3xL2(8).3", "P1/G1/L1/V1/ext3", "P1/G1/L1/V2/ext3", "2.L2(17)", "L2(17)x2", 
  "L2(17).2", "2xA7", "A7.2", "7:6xA5.2", "2.A7", "2(L2(11)x2).2", "2x2^3:L3(2)x2", "4.M22M6", "L3(3)", "(4xA6).2^2", "2^4:a6", "3x2^(1+4)_-:A5",
  "2.HSM11", "(2xA6.2^2).2", "2^4:(3xA5).2", "3x2^4:s5", "3x2^5.A5", "U3(3)", "L2(23)", "3x(3xA6):2_2", "L2(19).2", "2.L2(19)", "7:6xL3(2)", "2.A5xA5", 
  "5xIsoclinic(2.A6.2_2)", "a5wc2", "3.A7", "A7x3", "2^6:S5", "4.M22M5", "M24C2B", "4.2^4.S5", "L2(25)", "M11", "3x2.(2xL2(11))", "S4xL3(2).2", 
  "6x2^3:L3(2)", "L2(16).2", "12.M22M7", "3.A6.(2x4)", "3x2^4:(3xA5)", "2.(S3xS6)", "(A6xA4).2", "12.A6.2_3", "(S3xS3):2xS5", "s3xpsl(2,8).3", 
  "3^4:(2xA5)", "3^4:S5", "2.L2(17).2", "L2(27)", "2.(2xA7)", "2.A7.2", "Isoclinic(2.A7.2)", "2.Sym(7)", "S7x2", "(7xL2(8)).3", "4^3:psl(3,2)", 
  "P11/G1/L1/V1/ext2", "P11/G1/L1/V2/ext2", "P11/G1/L1/V3/ext2", "P11/G2/L1/V1/ext2", "P11/G2/L1/V2/ext2", "4^3.L3(2)", "L3(3).2", "3x4_1.2^4:A5", 
  "3x2.M22M5", "P21/G1/L1/V1/ext2", "M22.2M3", "3x4_2.2^4:A5", "2^4.s6", "2^6:(3xA5)", "5^2:4s5", "2xU3(3)", "U3(3).2", "L2(23).2", "2.L2(23)", "L2(29)", 
  "3.(3xM10):2", "2.L2(19).2", "Isoclinic(2.L2(19).2)", "h4", "(A5xA5):4", "(A5xA5):2^2", "2.(A5xA5).2", "P1/G2/L1/V1/ext3", "L2(31)", "3.A7.2", 
  "(A7x3).2", "2x(3.A7)", "2.A7x3", "6.A7", "2.HSM10", "2^(1+6)_+:S5", "P1/G1/L1/V1/ext4", "2.L2(25)", "L2(25).2_2", "L2(25).2_1", "L2(25).2_3", "2xM11", 
  "3x4.M22M6", "L2(16).4", "7^2:2psl(2,7)", "2.(A6xA4).2", "S6xS4", "3.M22M2", "2.L2(27)", "L2(27).2", "L3(4)", "A8", "2^(3+1+3).L3(2)", "2.4^3.L3(2)", 
  "P11/G3/L3/V1/ext2", "2.2^6.L3(2)", "2^1+6.psl(3,2)", "4^3:(L3(2)x2)", "P11/G3/L1/V1/ext2", "P11/G3/L4/V2/ext2", "4^3.(L3(2)x2)", "(2xL3(3)).2", 
  "2^5.S6", "2.2^4.S6", "2^5:S6", "3x4.M22M5", "2^6:(3xA5):2", "4.M22M2", "3xL2(25)", "3xM11", "2x5^2:4S5", "Isoclinic(2xU3(3).2)", "2xU3(3).2", 
  "Isoclinic(2.L2(23).2)", "2.L2(23).2", "L2(29).2", "2.L2(29)", "L2(37)", "ONM5", "(3^2:4xa6).2", "U4(2)", "s5wrs2", "2.(A5xA5).4", "2.(A5xA5).2^2", 
  "(A5xA5).(2x4)", "Sz(8)", "3^4:A6", "sl25ex", "L2(27).3", "L2(31).2", "2.L2(31)", "5^(1+2)+:4A5", "5^3:(2xA5).2", "S7xS3", "6.A7.2", "Isoclinic(6.A7.2)",
  "3.s7x2", "(2.A7x3).2", "2.(2x3.A7)", "P2/G2/L1/V2/ext2", "P2/G2/L1/V1/ext2", "P2/G1/L1/V1/ext2", "L2(25).2^2", "Isoclinic(2.L2(25)x2)", "2.L2(25).2_1", 
  "2.L2(25).2_2", "Isoclinic(L2(25).2_3x2)", "L2(32)", "7^2:2.L2(7).2", "3xL3(3).2", "L2(41)", "2^4:3.S6", "2.(S6xS4)", "6.M22M2", "NDG(Co1,5^2)", 
  "3xU3(3).2", "P1/G1/L1/V1/ext5", "2.L2(27).2", "L2(43)", "2xA8", "2.L3(4)", "L3(4).2_3", "L3(4).2_2", "L3(4).2_1", "2^4:a7", "2.A8", "A8.2", 
  "2^(1+6)_+.L3(2).2", "P11/G4/L1/V1/ext2", "(a6xa5).2", "(A6xA5):2", "P1/G3/L2/V1/ext3", "L3(3)xD8", "2.2^5.S6", "2^6:S6", "2.(2^5:S6)", "2^(4+4):(3xA5)",
  "(3xL2(25)).2_2", "3x2.L2(25)", "2.L2(29).2", "(3^2:8xA6).2", "2.U4(2)", "(3^2:4x2.A6).2", "U4(2).2", "(3^2:4xA6).2^2", "NDG(HN,3^2)", "3xS6xS4", 
  "L2(47)", "L3(2)wr2", "(2x2.(A5xA5)):2^2", "2.Sz(8)", "3^4:2.A6", "3^4:m10", "3^(1+4):4A5", "3^4:(2xA6)", "2x3^4:A6", "3^(1+4):2S5", "L2(49)", 
  "L2(27).6", "2.L2(27).3", "2.L2(31).2", "5^(1+2):GL2(5)", "3.L3(4)", "(A7xA4):2", "A8x3", "L3(4).3", "P1/G2/L2/V2/ext4", 
  "P1/G2/L1/V2/ext4", "P1/G2/L1/V1/ext4", "U3(4)", "L2(25).(2x4)", "4.L2(25).2_3", "P41/G1/L1/V4/ext2", "P41/G1/L1/V1/ext2", "P41/G1/L1/V2/ext2", 
  "2^6:(psl(3,2)xs3)", "3x(2xL3(3)).2", "12.M22M2", "NDG(2.Co1,5^2)", "11^2:(5x2.A5)", "L2(53)", "P1/G1/L1/V2/ext6", "P1/G1/L1/V1/ext6", 
  "(3^(1+2):4xA6).2", "3xU4(2)", "3.ONM5", "2.L3(4).2_1", "4_1.L3(4)", "S8x2", "Isoclinic(2.A8.2)", "4_2.L3(4)", "Isoclinic(S8x2)", "2.L3(4).2_2", 
  "Isoclinic(2.L3(4).2_1)", "2.L3(4).2_3", "Isoclinic(2.L3(4).2_2)", "L3(4).2^2", "Isoclinic(2.L3(4).2_3)", "2.A8.2", "2^2.L3(4)", "2.Sym(8)", 
  "P12/G1/L2/V1/ext2", "(A6x2.A5).2", "(A6:2_2xA5).2", "S6xS5", "2.(A6xA5).2", "Sz(8).3", "P21/G1/L1/V1/ext3", "P21/G1/L3/V2/ext3", "M12", 
  "3x7^2:2.L2(7).2", "L2(59)", "NDG(HN.2,3^2)", "2.U4(2).2", "3x2.(S6xS4)", "7:6xA7", "L2(61)", "7^(1+2).Sp(2,7)", "2^2.Sz(8)", "3^4:(M10x2)", 
  "3^(1+4):4S5", "HN.2M13", "2.(2x3^4:A6)", "2.L2(49)", "L2(49).2_3", "L2(49).2_2", "L2(49).2_1", "2.L2(27).6", "2x5^(1+2):GL2(5)", "3.L3(4).2_2", 
  "3.L3(4).2_1", "3.2^4:a7", "3.L3(4).2_3", "2.(A7xA4).2", "3xL3(4).2_2", "L3(4).6", "L3(4).3.2_3", "L3(4).3.2_2", "6.L3(4)", "(A8x3).2", "S7xS4", 
  "3x2.A8", "P11/G2/L1/V1/ext3", "P11/G1/L1/V1/ext3", "U3(4).2", "U3(5)", "P41/G2/L1/V1/ext2", "(3.A6xA5):2", "2^6:3.s6", "(D10x(A5xA5).2).2", "L2(67)", 
  "3^3:L3(3)", "(3^(1+2):4x2.A6).2", "S3xU4(2)", "(3xU4(2)):2", "(3^(1+2):8xA6).2", "3.ON.2M4", "Isoclinic(4_1.L3(4).2_1)", "(2x4).L3(4)", 
  "P27/G1/L1/V1/ext2", "Isoclinic(4_1.L3(4).2_2)", "Isoclinic(4_2.L3(4).2_1)", "2.L3(4).(2^2)_{1*2*3}", "4_1.L3(4).2_2", "4_1.L3(4).2_3", "4_1.L3(4).2_3*",
  "4_2.L3(4).2_1", "4_2.L3(4).2_2", "2.L3(4).(2^2)_{1*2*3*}", "2.L3(4).(2^2)_{1*23*}", "2.L3(4).(2^2)_{1*23}", "2.L3(4).(2^2)_{12*3*}", 
  "2.L3(4).(2^2)_{123*}", "2^2.L3(4).2_3", "4_2.L3(4).2_2*", "4_2.L3(4).2_3", "2^2.L3(4).2_1", "2.L3(4).(2^2)_{12*3}", "2.L3(4).(2^2)_{123}", 
  "2^2.L3(4).2_2", "Isoclinic(4_2.L3(4).2_3)", "4_1.L3(4).2_1", "L2(32).5", "P13/G1/L2/V1/ext2", "P13/G1/L6/V1/ext2", "3.3^(1+4):2S5",  "J1", 
  "L2(71)", "3.L3(4).3", "A9", "2^{1+8}_+:(S3xA5)", "P21/G2/L5/V2/ext2", "P21/G2/L2/V3/ext2", "P21/G2/L2/V1/ext2", "2^(2+8):(3xA5)", "P21/G2/L1/V3/ext2", 
  "2^(4+6):(A5x3)", "P21/G2/L1/V1/ext2", "M12.2", "2xm12", "2.M12", "L2(73)", "(2^2xU4(2)):2", "7:6xS7", "2^6:(7xL2(8))", "2.L2(49).2_1", "L2(49).2^2", 
  "2.L2(49).2_2", "Isoclinic(6.L3(4).2_1)", "6.L3(4).2_3", "L3(4).D12", "12_1.L3(4)", "12_2.L3(4)", "(2^2x3).L3(4)", "2^2.L3(4).3", "(2.A8x3).2", "S8xS3", 
  "3.L3(4).2^2", "Isoclinic(6.L3(4).2_3)", "Isoclinic(6.L3(4).2_2)", "6.L3(4).2_1", "6.L3(4).2_2", "2.2^4+6:S5", "L2(79)", "Isoclinic(2xU3(4).2)", 
  "U3(4).4", "U3(5).2", "2^{3+6}:(L3(2)x3)", "2^(1+8)+:L2(8)", "(3.A6x2.A5).2", "(3.A6.2_2xA5):2", "L2(64)", "3^2.(3^4:A6)", "L2(81)", "L2(83)", 
  "5^2:4S4xS5", "(A7xA5):2", "2xS3xU4(2)", "affine", "A4xU4(2)", "NDG(2.Co1,3^3)", "(3x2.U4(2)):2", "2x(3xU4(2)):2", "4_1.L3(4).(2^2)_{1*2*3*}", 
  "4_2.L3(4).(2^2)_{1*23}", "4_2.L3(4).(2^2)_{12*3*}", "4_2.L3(4).(2^2)_{12*3}", "4_2.L3(4).(2^2)_{1*23*}", "4_2.L3(4).(2^2)_{1*2*3}", 
  "4_2.L3(4).(2^2)_{1*2*3*}", "4_2.L3(4).(2^2)_{123*}", "2^4.a8", "4_1.L3(4).(2^2)_{1*2*3}", "4_1.L3(4).(2^2)_{12*3*}", "2^4:a8", "4_2.L3(4).(2^2)_{123}", 
  "2^2.L3(4).2^2", "4_1.L3(4).(2^2)_{1*23}", "4_1.L3(4).(2^2)_{12*3}", "4^2.L3(4)", "2^(1+6)_+:A7", "4_1.L3(4).(2^2)_{123}", "4_1.L3(4).(2^2)_{123*}", 
  "4_1.L3(4).(2^2)_{1*23*}", "2^3+8:L3(2)", "2^2.Sz(8).3", "(2^2xSz(8)):3", "3^5:2S6", "3.3^(1+4):4S5", "J1x2", "L2(89)", "A9.2", "3.L3(4).3.2_2", 
   "2xA9", "2.A9", "3.L3(4).6", "P11/G3/L1/V1/ext3", "P11/G3/L1/V2/ext3", "P21/G1/L1/V1/ext4", "2^2+8(a5xs3)", "P21/G3/L2/V1/ext2", 
  "2.2^(4+6).(A5x3)", "2.2^(2+8).(3xA5)", "L3(5)", "3.U3(5)", "U3(5).3", "Isoclinic(2.M12.2)", "M12.2x2", "2.M12.2", "2^6:u3(3)", "2.(2^2xU4(2)).2", 
  "M22", "L2(97)", "3xS3xU4(2)", "3^4:GL2(9)", "12_1.L3(4).2_1", "(a4xpsl(3,4)):2", "2^2.L3(4).3.2_2", "(2x12).L3(4)", "12_1.L3(4).2_2", "12_1.L3(4).2_3", 
  "2^2.L3(4).6", "(2^2x3).L3(4).2_1", "6.L3(4).(2^2)_{123*}", "12_2.L3(4).2_1", "(2^2x3).L3(4).2_2", "6.L3(4).(2^2)_{12*3}", "2^2.L3(4).3.2_3", 
  "12_2.L3(4).2_2", "12_2.L3(4).2_3", "2^6:3A7", "6.L3(4).(2^2)_{1*2*3*}", "6.L3(4).(2^2)_{1*2*3}", "6.L3(4).(2^2)_{1*23}", "6.L3(4).(2^2)_{1*23*}", 
  "6.L3(4).(2^2)_{123}", "(A8xA4):2", "6.L3(4).(2^2)_{12*3*}", "(2^2x3).L3(4).2_3", "2.2.2^4+6:S5", "2xU3(5).2", "Isoclinic(U3(5).2x2)", "L2(101)", 
  "(A6xA6):2^2", "L2(81).2_1", "L2(81).2_2", "L2(81).2_3", "2.L2(81)", "A6xL2(8):3", "A9x3", "L2(103)", "3xM12.2", "(5^2:4S4x2.A5):2", "S7xS5", 
  "2.(A7xA5).2", "J2", "L2(107)", "2x(3x2.U4(2)):2", "(A4xU4(2)):2", "2.(A4xU4(2))", "3x(2^2xU4(2)):2", "2^2xS3xU4(2)", "L2(109)", "P43/G3/L1/V2/ext2", 
  "P43/G1/L1/V1/ext2", "P43/G3/L1/V1/ext2", "P11/G1/L1/V3/ext4", "2.2^3+8:L3(2)", "P11/G1/L1/V1/ext4", "P11/G1/L1/V2/ext4", "2.(2^2xSz(8)):3", 
  "3^(2+4):2A5.D8", "3^1+4:4s6", "L2(113)", "S9x2", "2x2.A9", "(2^2x3).L3(4).3", "2.A9.2", "Isoclinic(2.A9.2)", "2.Sym(9)", "2.SuzM9", "2^(2+8):(S5xS3)", 
  "L3(5).2", "5^2.5.5^2.4A5", "U3(5).3.2", "3.U3(5).2", "2^6:u3(3):2", "P49/G1/L1/V1/ext2", "P2/G2/L1/V1/ext3", "P2/G1/L1/V1/ext3", "(A7xL2(7)):2", 
  "(13:6xL3(3)).2", "L2(121)", "2xM22", "M22.2", "2.M22", "3^1+4:2^1+4.s5", "6xS3xU4(2)", "2^2.L3(4).D12", "2^(1+6)_+:3A7", "(4^2x3).L3(4)", 
  "2.(A8xA4).2", "2.(A4xL3(4)).2", "(A4xL3(4):2_3):2", "S8xS4", "L2(125)", "S4(4)", "2^3.2^2.2^6.(3xL3(2))", "(S6xS6):2", "2.(A6xA6).2^2", "(A6xA6).D8", 
  "2.L2(81).2_2", "L2(81).4_2", "2.L2(81).2_1", "L2(81).2^2", "L2(81).4_1", "S6xL2(8):3", "(A9x3):2", "A9xS3", "2.A9x3", "3xS9", "P41/G1/L1/V3/ext3", 
  "P41/G1/L1/V1/ext3", "P11/G4/L1/V1/ext3", "3x2^(2+8):(A5xS3)", "2^4+6:3a6", "3.U3(5).3", "3xIsoclinic(2.M12.2)", "S3xM12.2", "2^2.(U3(3).2xS4)", 
  "(7^2:(3x2A4)xL2(7)).2", "J2.2", "2.J2", "3x2.(2^2xU4(2)).2", "S4xU4(2).2", "2^6:A8", "3.M22", "(A4x3.L3(4)).2", "S6(2)", "2^(4+8):(S3xA5)", 
  "13^2:2.L2(13).4", "5^2.5.5^2.4S5", "5^(1+4):GL(2,5)", "2.2^6:u3(3):2", "L2(64).6", "11^2:(5x2L2(11).2)", "2^6.U4(2)", "P50/G1/L1/V1/ext2", 
  "(L2(11)xL2(11)):4", "2.M22.2", "Isoclinic(2.M22.2)", "2x2.M22", "4.M22", "(A7xA6):2", "A10", "P27/G1/L1/V1/ext3", "2^2x3xS3xU4(2)", "L3(7)", "3^5:M11", 
  "S4(4).2", "2^3.2^2.2^6.(S3xL3(2))", "(S6xS6).2^2", "(S6xS6).4", "2.L2(81).4_1", "L2(81).(2x4)", "3xIsoclinic(2.A9.2)", "S9xS3", "(2.A9x3).2", 
  "P12/G1/L2/V1/ext3", "(3x2^(2+8):(A5xS3)).2", "3x2.SuzM9", "2.SuzM7", "2^(4+6):3S6", "3.U3(5).S3", "J2.2x2", "2.J2.2", "(A8xA5):2", "Isoclinic(2.J2.2)", 
  "(D10xU3(5)).2", "2^(1+6)_+.A8", "P31/G1/L1/V1/ext2", "2^6:S8", "6.M22", "2x3.M22", "3.M22.2", "6.SuzM8", "(A4x3.L3(4).2_3).2", "2.S6(2)", "2xS6(2)", 
  "P13/G1/L2/V1/ext3", "2.2^(4+8):(S3xA5)", "U4(3)", "P41/G2/L1/V1/ext3", "2^6:U4(2).2", "2^1+6.u4q2", "3x2^(4+6).3A6", "2^6.U4(2).2", 
  "Isoclinic(4.M22.2)", "4.M22.2", "3xJ2.2", "2.A10", "A10.2", "S7xS6", "2^(1+8).(A5xA5).2", "L3(7).2", "3^5:(2xm11)", 
  "3^5:(M11x2)", "2x3^5:M11", "S4(4).4", "2^10:(2^5:s5)", "3^6:L3(3)", "3^(3+3):L3(3)", "2^(6+6):(S3xL3(2))", "3^4.2U4(2)", "G2(3)", "(A9xA4):2", 
  "3xS6(2)", "(A6xU3(3)):2", "3x2^(4+8):(S3xA5)", "S4(5)", "S8xS5", "5:4xU3(5):2", "(2x2^(1+6)_+).A8", "Isoclinic(6.M22.2)", "12.M22", "6.M22.2", 
  "2x6.M22", "U3(8)", "3.L3(7)", "L3(7).3", "U3(7)", "3^6.M11", "2^2xS6(2)", "2x2.S6(2)", "2^2.2^(4+8):(S3xA5)", "L4(3)", "3^5.U4(2)", "3^5:U4(2)", 
  "U4(3).2_1", "U4(3).2_2", "U4(3).2_3", "2.U4(3)", "(3x2^(4+6):3A6).2", "3x2.SuzM7", "2.SuzM4", "2^(1+6)_-.U4(2).2", "Isoclinic(2.A10.2)", "S10x2", 
  "3x2.J2.2", "2.A10.2", "S3xJ2.2", "2.Sym(10)", "2^(1+8)_+.(A5xA5).2^2", "P48/G1/L1/V2/ext2", "P48/G1/L1/V1/ext2", "2x3^(3+3):L3(3)", "3^4.2U4(2).2", 
  "G2(3).2", "2xG2(3)", "S9xS4", "6xS6(2)", "3x2.S6(2)", "S3xS6(2)", "3x2.2^(4+8):(S3xA5)", "2^(3+8):(S3xS6)", "5^(1+4):4S6", "S4(5).2", "2.S4(5)", 
  "3_1.U4(3)", "3_2.U4(3)", "3x2^(1+6)_-.U4(2)", "L5(2)", "M23", "P27/G1/L1/V1/ext4", "2^9.L3(4)", "2^8:S8", "(S5xS5xS5):S3", "Isoclinic(12.M22.2)", 
  "12.M22.2", "(A10x3):2", "U3(8).2", "L3(7).S3", "3.L3(7).2", "U3(7).2", "M11xA6.2^2", "3^6:(M11x2)", "2x3^6.M11", "D8xS6(2)", "2^(4+10)(S5xS3)", 
  "L4(3)x2", "L4(3).2_3", "L4(3).2_2", "2.L4(3)", "L4(3).2_1", "3.(3^(3+3):L3(3))", "3^(1+4).2U4(2)", "3^5:U4(2):2", "3.G2(3)", "U4(3).4", "2.U4(3).2_3", 
  "Isoclinic(2.U4(3).2_2)", "Isoclinic(2.U4(3).2_1)", "Isoclinic(2.U4(3).2_3)", "2.U4(3).2_1", "4.U4(3)", "U4(3).(2^2)_{122}", "U4(3).(2^2)_{133}", 
  "2.U4(3).2_2", "2xU4(3).2_2", "P49/G1/L1/V1/ext3", "P49/G1/L1/V2/ext3", "2^(1+8)_+:U4(2)", "U5(2)", "P3L62", "L3(8)", "3.U3(8)", "U3(8).3_2", 
  "U3(8).3_3", "U3(8).3_1", "3.L3(7).3", "2^2x3xS6(2)", "3x2^2.2^(4+8):(S3xA5)", "2^(5+8):(S3xA6)", "2F4(2)'", "2.S4(5).2", "3.3^5.U4(2)", 
  "P50/G1/L1/V1/ext3", "3_2.U4(3).2_3", "3_1.U4(3).2_2'", "3_1.U4(3).2_2", "6_2.U4(3)", "3_2.U4(3).2_1", "S3xU4(3)", "3_1.U4(3).2_1", "6_1.U4(3)", 
  "3_2.U4(3).2_3'", "3x2.SuzM4", "(3x2^(1+6)_-.U4(2)).2", "A11", "L5(2).2", "2^(1+8):S8", "2.U6(2)M3", "2^10.A8", "S10xS3", "(A5xA9):2", 
  "5^(1+4).2^(1+4).A5.4", "2.L4(3).2_1", "2.L4(3).2_3", "L4(3).2^2", "2.L4(3).2_2", "2x3.(3^(3+3):L3(3))", "3^(1+4).2U4(2).2", "(2x3^5).U4(2).2", 
  "3^5:(2xU4(2).2)", "3.G2(3).2", "2x3.G2(3)", "(3xG2(3)):2", "2.U4(3).(2^2)_{13*3}", "2.U4(3).(2^2)_{13*3*}", "2.U4(3).(2^2)_{1*2*2*}", "2x2.U4(3).2_2", 
  "2.U4(3).(2^2)_{122}", "U4(3).D8", "2.U4(3).(2^2)_{12*2}", "2.U4(3).(2^2)_{12*2*}", "2.U4(3).(2^2)_{1*33}", "2.U4(3).(2^2)_{1*3*3*}", "4.U4(3).2_1", 
  "4.U4(3).2_2", "2.U4(3).(2^2)_{133}", "2xU4(3).(2^2)_{122}", "2.U4(3).(2^2)_{1*3*3}", "2.U4(3).4", "2.U4(3).(2^2)_{1*2*2}", "4.U4(3).2_3", 
  "2.U4(3).(2^2)_{1*22}", "2.2^(1+8)_+:U4(2)", "U5(2).2", "2xU5(2)", "3^2.U4(3)", "3.U6(2)M3", "P2L62", "Sz(32)", "L3(8).2", "U3(8).6", "U3(8).S3", 
  "3.U3(8).2", "3.L3(7).S3", "7^(2+1+2):GL2(7)", "S4xS6(2)", "2^(5+8):(S3xS6)", "2F4(2)'.2", "3xL4(3).2_2", "3.3^5:U4(2):2", "3_1.U4(3).(2^2)_{122}", 
  "2x3_1.U4(3).2_2", "12_2.U4(3)", "S3xU4(3).2_2", "12_1.U4(3)", "6_2.U4(3).2_3'", "6_2.U4(3).2_3", "3_2.U4(3).(2^2)_{133}", "6_1.U4(3).2_2'", 
  "6_1.U4(3).2_2", "6_1.U4(3).2_1", "Isoclinic(6_2.U4(3).2_3')", "6_2.U4(3).2_1", "3x2^(1+8)_+:U4(2)", "A11.2", "2.A11",
  "3xU5(2)", "2^2.U6(2)M3", "2^1+4+6.a8", "L3(9)", "U3(9)", "S5xS9", "P31/G1/L1/V1/ext3", "HS", "2^8.A9", "5^3.psl(3,5)", "L3(8).3", "3.U3(8).3_1", 
  "3.U3(8).3_2", "J3", "2.U4(3).D8", "2^2.U4(3).(2^2)_{122}", "4.U4(3).4", "2^2.2^(1+8)_+:U4(2)", "(2x2^(1+8)):U4(2):2", "2^2xU5(2)", "C9Y3.3^5.U4(2)", 
  "(S6xL3(4).2).2", "5^4:(3x2.L2(25)).2", "(3^2x2).U4(3)", "3^2.U4(3).2_3'", "6.U6(2)M3", "U3(11)", "2.RuM1", "(A5xJ2):2", "(A7x(A5xA5):2^2):2", 
  "3x2.L4(3).2_2", "6.(3^5:U4(2):2)", "12_2.U4(3).2_1", "12_1.U4(3).2_2", "12_2.U4(3).2_3", "12_1.U4(3).2_1", "2xS3xU4(3).2_2", "S3x2.U4(3).2_2", 
  "3x2.U4(3).(2^2)_{122}", "S3xU4(3).(2^2)_{122}", "2x6_1.U4(3).2_2", "3x2.2^(1+8)_+:U4(2)", "2.A11.2", "S11x2", "Isoclinic(2.A11.2)", "2.Sym(11)", 
  "(3xU5(2)).2", "6xU5(2)", "7^1+4.2A7", "L3(9).2_1", "L3(9).2_2", "L3(9).2_3", "U3(9).2", "HS.2", "2.HS", "2^1+8.a9", "2^6:s6f2", "D8xL4(3).2_2", 
  "L3(8).6", "3.U3(8).6", "3.U3(8).S3", "J3.2", "2.(2x2^(1+8)):U4(2):2", "(2x2^(1+8)):(U4(2):2x2)", "P50/G1/L1/V1/ext4", "A5.2xM22.2", 
  "Isoclinic((3^2x2).U4(3).2_3')", "3^2.U4(3).(2^2)_{133}", "(3^2x4).U4(3)", "(3^2x2).U4(3).2_3'", "2^12:Sz(8)", "(2^2x3).U6(2)M3", "(L2(11)xM12):2", 
  "S4(7)", "3^6:2M12", "U3(11).2", "3.J3", "(3^2:2xG2(3)).2", "(S3x2.U4(3).2_2).2", "2xS3x2.U4(3).2_2", "2xS3xU4(3).(2^2)_{122}", "3x2^2.2^(1+8)_+:U4(2)", 
  "3x(2x2^(1+8)):U4(2):2", "Sz(32).5", "2^2x3xU5(2)", "L3(9).2^2", "U3(9).4", "O8+(2)", "2.HS.2", "Isoclinic(2.HSx2)", "Isoclinic(2.HS.2)", "HS.2x2", 
  "2^7:S6(2)", "S8(2)M3", "2^1+8.2.A9", "O8-(2)", "3D4(2)", "L3(11)", "U3(11).3", "3.U3(11)", "S3x6_1.U4(3).2_2", "3^2.U4(3).D8", "A12", "M24", 
  "2^(6+8):(A7xS3)", "G2(4)", "S4(7).2", "D8x2F4(2)'.2", "3.J3.2", "(5^2:[2^4]xU3(5)).S3", "(S3xS3xG2(3)):2", "3.(2x2^(1+8)):(U4(2):2x2)", 
  "(2^2x2^(1+8)).(3xU4(2)).2", "2^5.psl(5,2)", "2^5:L5(2)", "2.O8+(2)", "O8+(2).2", "4.HS.2", "2^8:S6(2)", "O8-(2).2", "U3(11).S3", "3.U3(11).2", 
  "2^10:M22'", "2^10:m22", "(3^2x2).U4(3).D8", "A12.2", "2.A12", "G2(4).2", "2.G2(4)", "7^(1+4):(3x2.S7)", "O8+(2).3", 
  "(QD16x2F4(2)').2", "3D4(2).3", "3.U3(11).3", "(L3(2)xS4(4):2).2", "J4M4", "Fi23M8", "2^2.O8+(2)", "2.O8+(2).2", "2^1+8:s6f2", "3xG2(4)", 
  "2^(4+12).(S3x3S6)", "S4x2F4(2)'.2", "3^(3+6):(L3(3)xD8)", "McL", "2^10:m22:2", "2.Fi22M5", "Fi22.2M4", "(3^(1+2):2^2xG2(3)):2", "Isoclinic(2.A12.2)", 
  "2.A12.2", "L4(4)", "Isoclinic(2.G2(4).2)", "2.G2(4).2", "U4(4)", "O8+(2).3.2", "S4(8)", "5^(2+2+4):(S3xGL2(5))", "3.U3(11).S3", 
  "3.Fi22M5", "2^2.O8+(2).2", "3x2.G2(4)", "(3xG2(4)).2", "S4(9)", "(GL(2,3)x2F4(2)').2", "5:4xHS.2", "McL.2", "(3^2:D8xU4(3).2^2).2", "L4(4).2_3", 
  "L4(4).2_2", "L4(4).2_1", "2^(2+12):(A8xS3)", "2^(3+12).(L3(2)xA6)", "2^(6+8).(S3xA8)", "(A5xU3(8):3):2", "O8+(2):S3x2", "2^2.O8+(2).3", 
  "(A6xA6xA6).(2xS4)", "2^12:J2", "3.McL", "6.Fi22M5", "A13", "3xO8+(2):S3", "S4(9).2_3", "S4(9).2_2", "S4(9).2_1", "2.(3^2:D8xU4(3).2^2).2", "L4(4).2^2", 
  "2^(3+12).(L3(2)xS6)", "2^(7+8).(S3xA8)", "He", "U4(4).4", "2^2.O8+(2).3.2", "3^6:L4(3)", "O7(3)", "S6(3)", "3.McL.2", "G2(5)", "(A4xG2(4)):2", "2.A13", 
 "A13.2", "6xO8+(2):S3", "S4(9).2^2", "L4(5)", "He.2", "3^6:(L4(3)x2)", "S6(3).2", "2.O7(3)", "O7(3).2", "2xO7(3)", "2.S6(3)", 
  "U6(2)", "3^6:2U4(3).2_1", "R(27)", "2^10:L5(2)", "5^(3+3).(2xL3(5))", "Isoclinic(2.A13.2)", "2.A13.2", "(A4xO8+(2).3).2", "3.O7(3)", 
  "3^2.3^4.3^8.(A5x2A4).2", "2^12:(L4(2)xL3(2))", "2.L4(5)", "U4(5)", "3^3.[3^10].GL3(3)", "O7(3).2x2", "2.S6(3).2", "2.O7(3).2", "2.U6(2)", "U6(2).2", 
  "L6(2)", "2..11.m23", "c2aj4", "(2^6x2^8):S6(2)", "S4xO8+(2):S3", "S3xO7(3)", "6.O7(3)", "2x3.O7(3)", "3.O7(3).2", "3^2.3^4.3^8.(S5x2S4)", "3.U6(2)", 
  "U6(2).3", "(A5xA12):2", "4.L4(5)", "U4(5).2_1", "U4(5).2_2", "U4(5).2_3", "R(27).3", "3^6.L4(3).D8", "3^3.[3^10].(L3(3)x2^2)", "2.U6(2).2", 
  "2^2.U6(2)", "L6(2).2", "A14", "2^8:O8+(2)", "S8(2)", "(2^(1+8)x2^6):S6(2)", "2^8:O8-(2)", "6.O7(3).2", "6.U6(2)", "3.U6(2).2", "U6(2).3.2", 
  "U4(5).2^2", "2^10:(L5(2)xS3)", "2^2.U6(2).2", "2^12.3_1.U4(3).2_2'", "3.U6(2).3", "A14.2", "2.Alt(14)", "2^(1+8)+.O8+(2)", "2^8:O8+(2):2", 
  "2^8:O8-(2):2", "(2^2x3).U6(2)", "2^2.U6(2).3", "6.U6(2).2", "3^(1+8).2^(1+6).U4(2).2", "Ru", "2^(1+12).3_1.U4(3).2_2'", "3.U6(2).3.2", "U72CT", 
  "(7:3xHe):2", "2.A14.2", "Isoclinic(2.A14.2)", "(2^2x3).U6(2).2", "2^2.U6(2).3.2", "L5(3)", "2^12.3^2.U4(3).2_2'", "U5(3)", "2.Ru", 
  "2^(1+12)_+.3_1.U4(3).2^2_{122}", "(2^2x3).U6(2).3", "5^(1+6):2.J2.4", "2^2.U6(2):S3x2", "Suz", "ON", "L5(3).2", "3.2^(1+12).3U4(3).2", "Co3", "F3+M7", 
  "mx1j4", "2^11:M24", "A15", "2.Suz", "Suz.2", "ON.2", "2.2^11:M24", "2^12.M24", "2^6:L6(2)", "2.Alt(15)", "A15.2", "3.Suz", "3.ON", 
  "Isoclinic(2.Suz.2)", "2.Suz.2", "2.A15.2", "6.Suz", "3.Suz.2", "3.ON.2", "S6(4)", "3^(1+10):U5(2):2", "O8+(3)", "Isoclinic(6.Suz.2)", 
  "6.Suz.2", "S6(4).2", "3^(1+10):(2xU5(2):2)", "O8+(3).2_1", "2.O8+(3)", "O8+(3).2_2", "3^7.O7(3)", "3^7:O7(3)", "O8-(3)", "A16", "2^8:S8(2)", 
  "O8+(3).3", "2^2.O8+(3)", "O8+(3).4", "O8+(3).(2^2)_{122}", "O8+(3).(2^2)_{111}", "3^7.O7(3):2", "O8-(3).2_3", "2.O8-(3)", "O8-(3).2_2", "O8-(3).2_1", 
  "2.Alt(16)", "A16.2", "O10+(2)", "O10-(2)", "O8+(3).3.2", "O8+(3).D8", "O8-(3).2^2", "2.A16.2", "Co2", "O10+(2).2", "O10-(2).2", 
  "L4(9)", "U5(4)", "O8+(3).A4", "2^2.O8+(3).3", "Fi22", "(3xO8+(3):3):2", "U5(4).2", "O8+(3).S4", "2.Fi22", "2xFi22", "Fi22.2", "L7(2)", "A17", 
  "S3xO8+(3):S3", "3.Fi22", "U7(2)", "O7(5)", "S6(5)", "Isoclinic(2.Fi22.2)", "2x2.Fi22", "2.Fi22.2", "2xFi22.2", "HN", "L7(2).2", "2.Alt(17)", "A17.2", 
   "3.Fi22.2", "2x3.Fi22", "6.Fi22", "O7(5).2", "P2L82", "2^2.Fi22.2", "HN.2", "[2^35].(S5xL3(2))", "2.Sym(17)", "3x2.Fi22.2", 
  "2x6.Fi22", "S3xFi22.2", "6.Fi22.2", "Isoclinic(6.Fi22.2)", "(S3x2.Fi22).2", "A18", "F4(2)", "(D10xHN).2", "2.Alt(18)", "A18.2", "2.F4(2)", 
  "F4(2).2", "2xF4(2)", "3xF4(2)", "[2^30].L5(2)", "2.A18.2", "2^2xF4(2)", "2.F4(2).2", "2xF4(2).2", "Isoclinic(2.F4(2).2)", "2x2.F4(2)", 
  "3x2.F4(2)", "6xF4(2)", "P1L82", "2^(2+10+20).(M22.2xS3)", "S10(2)", "(2^2xF4(2)):2", "2.(2xF4(2)).2", "Isoclinic(2x2.F4(2).2)", "6x2.F4(2)", "Ly", 
  "A19", "S8(3)", "O9(3)", "Th", "A19.2", "2.Alt(19)", "2.O9(3)", "2xTh", "2.Sym(19)", "S3xTh", "2^(9+16).S8(2)", "3^(1+12).2.Suz.2", 
  "3^12.6.Suz.2", "Fi23", "Co1", "L8(2)", "2xFi23", "2.Co1", "3^(1+12):6.Suz.2", "3xFi23", "J4", "O12+(2).2", "O12-(2).2", "2^(1+22).Co2", "O10-(3)", 
  "U6(4)", "2.O10-(3)", "2E6(2)", "O8+(7)", "2E6(2).2", "2.2E6(2)", "S12(2)", "E6(2)", "2.O8+(7)", "2E6(2).3", "3.2E6(2)", "2F4(8)", "2.2E6(2).2", 
  "2^2.2E6(2)", "3.2E6(2).2", "6.2E6(2)", "2E6(2).3.2", "2^2.2E6(2).2", "6.2E6(2).2", "2^2.2E6(2).3", "(2^2x3).2E6(2)", "F3+", "(2^2x3).2E6(2).2", 
  "2^2.2E6(2).3.2", "F3+.2", "3.F3+", "3.F3+.2", "2^24.Co1", "2^1+24.Co1", "2^1+24.2.Co1", "B", "2.B", "M" ];

NonSolvIds:=[ [ 60, 5 ], [ 120, 5 ], [ 120, 34 ], [ 120, 35 ], [ 168, 42 ], [ 180, 19 ], [ 240, 89 ], [ 240, 90 ], [ 240, 91 ], [ 240, 92 ], [ 240, 93 ], [ 240, 94 ], 
  [ 240, 189 ], [ 240, 190 ], [ 300, 22 ], [ 336, 114 ], [ 336, 208 ], [ 336, 209 ], [ 360, 51 ], [ 360, 118 ], [ 360, 119 ], [ 360, 120 ], [ 360, 121 ], 
  [ 360, 122 ], [ 420, 13 ], [ 480, 217 ], [ 480, 218 ], [ 480, 219 ], [ 480, 220 ], [ 480, 221 ], [ 480, 222 ], [ 480, 943 ], [ 480, 944 ], [ 480, 945 ], 
  [ 480, 946 ], [ 480, 947 ], [ 480, 948 ], [ 480, 949 ], [ 480, 950 ], [ 480, 951 ], [ 480, 952 ], [ 480, 953 ], [ 480, 954 ], [ 480, 955 ], 
  [ 480, 956 ], [ 480, 957 ], [ 480, 958 ], [ 480, 959 ], [ 480, 960 ], [ 480, 1186 ], [ 480, 1187 ], [ 504, 156 ], [ 504, 157 ], [ 540, 31 ], 
  [ 540, 88 ], [ 600, 54 ], [ 600, 144 ], [ 600, 145 ], [ 600, 146 ], [ 600, 147 ], [ 660, 13 ], [ 660, 14 ], [ 672, 1043 ], [ 672, 1044 ], [ 672, 1045 ], 
  [ 672, 1046 ], [ 672, 1047 ], [ 672, 1048 ], [ 672, 1254 ], [ 672, 1255 ], [ 720, 409 ], [ 720, 410 ], [ 720, 411 ], [ 720, 412 ], [ 720, 413 ], 
  [ 720, 414 ], [ 720, 415 ], [ 720, 416 ], [ 720, 417 ], [ 720, 418 ], [ 720, 419 ], [ 720, 420 ], [ 720, 421 ], [ 720, 763 ], [ 720, 764 ], 
  [ 720, 765 ], [ 720, 766 ], [ 720, 767 ], [ 720, 768 ], [ 720, 769 ], [ 720, 770 ], [ 720, 771 ], [ 720, 772 ], [ 780, 13 ], [ 840, 13 ], [ 840, 134 ], 
  [ 840, 135 ], [ 840, 136 ], [ 840, 137 ], [ 840, 138 ], [ 900, 88 ], [ 960, 637 ], [ 960, 638 ], [ 960, 639 ], [ 960, 640 ], [ 960, 641 ], [ 960, 642 ], 
  [ 960, 5681 ], [ 960, 5682 ], [ 960, 5683 ], [ 960, 5684 ], [ 960, 5685 ], [ 960, 5686 ], [ 960, 5687 ], [ 960, 5688 ], [ 960, 5689 ], [ 960, 5690 ], 
  [ 960, 5691 ], [ 960, 5692 ], [ 960, 5693 ], [ 960, 5694 ], [ 960, 5695 ], [ 960, 5696 ], [ 960, 5697 ], [ 960, 5698 ], [ 960, 5699 ], [ 960, 5700 ], 
  [ 960, 5701 ], [ 960, 5702 ], [ 960, 5703 ], [ 960, 5704 ], [ 960, 5705 ], [ 960, 5706 ], [ 960, 5707 ], [ 960, 5708 ], [ 960, 5709 ], [ 960, 5710 ], 
  [ 960, 5711 ], [ 960, 5712 ], [ 960, 5713 ], [ 960, 5714 ], [ 960, 5715 ], [ 960, 5716 ], [ 960, 5717 ], [ 960, 5718 ], [ 960, 5719 ], [ 960, 5720 ], 
  [ 960, 5721 ], [ 960, 5722 ], [ 960, 5723 ], [ 960, 5724 ], [ 960, 5725 ], [ 960, 5726 ], [ 960, 5727 ], [ 960, 5728 ], [ 960, 5729 ], [ 960, 5730 ], 
  [ 960, 5731 ], [ 960, 5732 ], [ 960, 5733 ], [ 960, 5734 ], [ 960, 5735 ], [ 960, 5736 ], [ 960, 5737 ], [ 960, 5738 ], [ 960, 5739 ], [ 960, 5740 ], 
  [ 960, 5741 ], [ 960, 5742 ], [ 960, 5743 ], [ 960, 5744 ], [ 960, 5745 ], [ 960, 5746 ], [ 960, 5747 ], [ 960, 10863 ], [ 960, 10864 ], [ 960, 10865 ], 
  [ 960, 10866 ], [ 960, 10867 ], [ 960, 10868 ], [ 960, 10869 ], [ 960, 10870 ], [ 960, 10871 ], [ 960, 10872 ], [ 960, 10873 ], [ 960, 10874 ], 
  [ 960, 10875 ], [ 960, 10876 ], [ 960, 10877 ], [ 960, 10878 ], [ 960, 10879 ], [ 960, 10880 ], [ 960, 10881 ], [ 960, 10882 ], [ 960, 10883 ], 
  [ 960, 10884 ], [ 960, 10885 ], [ 960, 10886 ], [ 960, 10887 ], [ 960, 10888 ], [ 960, 10889 ], [ 960, 10890 ], [ 960, 10891 ], [ 960, 10892 ], 
  [ 960, 11355 ], [ 960, 11356 ], [ 960, 11357 ], [ 960, 11358 ], [ 1008, 517 ], [ 1008, 880 ], [ 1008, 881 ], [ 1008, 882 ], [ 1008, 883 ], 
  [ 1008, 884 ], [ 1020, 9 ], [ 1080, 63 ], [ 1080, 260 ], [ 1080, 261 ], [ 1080, 262 ], [ 1080, 263 ], [ 1080, 264 ], [ 1080, 363 ], [ 1080, 487 ], 
  [ 1080, 488 ], [ 1080, 489 ], [ 1080, 490 ], [ 1080, 491 ], [ 1080, 492 ], [ 1080, 493 ], [ 1092, 25 ], [ 1140, 13 ], [ 1176, 212 ], [ 1200, 473 ], 
  [ 1200, 474 ], [ 1200, 475 ], [ 1200, 476 ], [ 1200, 477 ], [ 1200, 478 ], [ 1200, 479 ], [ 1200, 480 ], [ 1200, 481 ], [ 1200, 482 ], [ 1200, 483 ], 
  [ 1200, 484 ], [ 1200, 939 ], [ 1200, 940 ], [ 1200, 941 ], [ 1200, 942 ], [ 1200, 943 ], [ 1200, 944 ], [ 1200, 945 ], [ 1260, 61 ], [ 1260, 62 ], 
  [ 1320, 13 ], [ 1320, 14 ], [ 1320, 133 ], [ 1320, 134 ], [ 1320, 135 ], [ 1320, 136 ], [ 1320, 137 ], [ 1320, 138 ], [ 1344, 814 ], [ 1344, 6311 ], 
  [ 1344, 6312 ], [ 1344, 6313 ], [ 1344, 6314 ], [ 1344, 6315 ], [ 1344, 6316 ], [ 1344, 11288 ], [ 1344, 11289 ], [ 1344, 11290 ], [ 1344, 11291 ], 
  [ 1344, 11292 ], [ 1344, 11293 ], [ 1344, 11294 ], [ 1344, 11295 ], [ 1344, 11296 ], [ 1344, 11297 ], [ 1344, 11298 ], [ 1344, 11299 ], [ 1344, 11300 ], 
  [ 1344, 11301 ], [ 1344, 11302 ], [ 1344, 11303 ], [ 1344, 11304 ], [ 1344, 11305 ], [ 1344, 11684 ], [ 1344, 11685 ], [ 1344, 11686 ], [ 1380, 9 ], 
  [ 1440, 1682 ], [ 1440, 1683 ], [ 1440, 1684 ], [ 1440, 1685 ], [ 1440, 1686 ], [ 1440, 1687 ], [ 1440, 1688 ], [ 1440, 1689 ], [ 1440, 1690 ], 
  [ 1440, 1691 ], [ 1440, 1692 ], [ 1440, 1693 ], [ 1440, 4590 ], [ 1440, 4591 ], [ 1440, 4592 ], [ 1440, 4593 ], [ 1440, 4594 ], [ 1440, 4595 ], 
  [ 1440, 4596 ], [ 1440, 4597 ], [ 1440, 4598 ], [ 1440, 4599 ], [ 1440, 4600 ], [ 1440, 4601 ], [ 1440, 4602 ], [ 1440, 4603 ], [ 1440, 4604 ], 
  [ 1440, 4605 ], [ 1440, 4606 ], [ 1440, 4607 ], [ 1440, 4608 ], [ 1440, 4609 ], [ 1440, 4610 ], [ 1440, 4611 ], [ 1440, 4612 ], [ 1440, 4613 ], 
  [ 1440, 4614 ], [ 1440, 4615 ], [ 1440, 4616 ], [ 1440, 4617 ], [ 1440, 4618 ], [ 1440, 4619 ], [ 1440, 4620 ], [ 1440, 4621 ], [ 1440, 4622 ], 
  [ 1440, 4623 ], [ 1440, 4624 ], [ 1440, 4625 ], [ 1440, 4626 ], [ 1440, 4627 ], [ 1440, 4628 ], [ 1440, 4629 ], [ 1440, 4630 ], [ 1440, 4631 ], 
  [ 1440, 4632 ], [ 1440, 4633 ], [ 1440, 4634 ], [ 1440, 4635 ], [ 1440, 4636 ], [ 1440, 4637 ], [ 1440, 4638 ], [ 1440, 4639 ], [ 1440, 4640 ], 
  [ 1440, 4641 ], [ 1440, 4642 ], [ 1440, 4643 ], [ 1440, 4644 ], [ 1440, 4645 ], [ 1440, 4646 ], [ 1440, 4647 ], [ 1440, 4648 ], [ 1440, 4649 ], 
  [ 1440, 4650 ], [ 1440, 4651 ], [ 1440, 4652 ], [ 1440, 4653 ], [ 1440, 4654 ], [ 1440, 4655 ], [ 1440, 4656 ], [ 1440, 5841 ], [ 1440, 5842 ], 
  [ 1440, 5843 ], [ 1440, 5844 ], [ 1440, 5845 ], [ 1440, 5846 ], [ 1440, 5847 ], [ 1440, 5848 ], [ 1440, 5849 ], [ 1440, 5850 ], [ 1440, 5851 ], 
  [ 1440, 5852 ], [ 1440, 5853 ], [ 1440, 5854 ], [ 1500, 34 ], [ 1500, 112 ], [ 1512, 437 ], [ 1512, 779 ], [ 1512, 780 ], [ 1512, 781 ], [ 1560, 13 ], 
  [ 1560, 146 ], [ 1560, 147 ], [ 1560, 148 ], [ 1560, 149 ], [ 1620, 71 ], [ 1620, 262 ], [ 1620, 263 ], [ 1620, 264 ], [ 1620, 418 ], [ 1680, 397 ], 
  [ 1680, 398 ], [ 1680, 399 ], [ 1680, 400 ], [ 1680, 401 ], [ 1680, 402 ], [ 1680, 403 ], [ 1680, 404 ], [ 1680, 405 ], [ 1680, 406 ], [ 1680, 407 ], 
  [ 1680, 408 ], [ 1680, 409 ], [ 1680, 924 ], [ 1680, 925 ], [ 1680, 926 ], [ 1680, 927 ], [ 1680, 928 ], [ 1680, 929 ], [ 1680, 930 ], [ 1680, 931 ], 
  [ 1680, 932 ], [ 1740, 9 ], [ 1800, 328 ], [ 1800, 555 ], [ 1800, 556 ], [ 1800, 557 ], [ 1800, 558 ], [ 1800, 559 ], [ 1800, 560 ], [ 1800, 561 ], 
  [ 1800, 562 ], [ 1800, 563 ], [ 1848, 127 ], [ 1860, 19 ], [ 1920, 240417 ], [ 1920, 240418 ], [ 1920, 240419 ], [ 1920, 240420 ], [ 1920, 240421 ], 
  [ 1920, 240422 ], [ 1920, 240423 ], [ 1920, 240424 ], [ 1920, 240425 ], [ 1920, 240426 ], [ 1920, 240427 ], [ 1920, 240428 ], [ 1920, 240429 ], 
  [ 1920, 240430 ], [ 1920, 240431 ], [ 1920, 240432 ], [ 1920, 240433 ], [ 1920, 240434 ], [ 1920, 240435 ], [ 1920, 240436 ], [ 1920, 240437 ], 
  [ 1920, 240438 ], [ 1920, 240439 ], [ 1920, 240440 ], [ 1920, 240441 ], [ 1920, 240442 ], [ 1920, 240443 ], [ 1920, 240444 ], [ 1920, 240445 ], 
  [ 1920, 240446 ], [ 1920, 240447 ], [ 1920, 240448 ], [ 1920, 240449 ], [ 1920, 240450 ], [ 1920, 240451 ], [ 1920, 240452 ], [ 1920, 240453 ], 
  [ 1920, 240454 ], [ 1920, 240455 ], [ 1920, 240456 ], [ 1920, 240457 ], [ 1920, 240458 ], [ 1920, 240459 ], [ 1920, 240460 ], [ 1920, 240461 ], 
  [ 1920, 240462 ], [ 1920, 240463 ], [ 1920, 240464 ], [ 1920, 240465 ], [ 1920, 240466 ], [ 1920, 240467 ], [ 1920, 240468 ], [ 1920, 240469 ], 
  [ 1920, 240470 ], [ 1920, 240471 ], [ 1920, 240472 ], [ 1920, 240473 ], [ 1920, 240474 ], [ 1920, 240475 ], [ 1920, 240476 ], [ 1920, 240477 ], 
  [ 1920, 240478 ], [ 1920, 240479 ], [ 1920, 240480 ], [ 1920, 240481 ], [ 1920, 240482 ], [ 1920, 240483 ], [ 1920, 240484 ], [ 1920, 240485 ], 
  [ 1920, 240486 ], [ 1920, 240487 ], [ 1920, 240488 ], [ 1920, 240489 ], [ 1920, 240490 ], [ 1920, 240491 ], [ 1920, 240492 ], [ 1920, 240493 ], 
  [ 1920, 240494 ], [ 1920, 240495 ], [ 1920, 240496 ], [ 1920, 240497 ], [ 1920, 240498 ], [ 1920, 240499 ], [ 1920, 240500 ], [ 1920, 240501 ], 
  [ 1920, 240502 ], [ 1920, 240503 ], [ 1920, 240504 ], [ 1920, 240505 ], [ 1920, 240506 ], [ 1920, 240507 ], [ 1920, 240508 ], [ 1920, 240509 ], 
  [ 1920, 240510 ], [ 1920, 240511 ], [ 1920, 240512 ], [ 1920, 240513 ], [ 1920, 240514 ], [ 1920, 240515 ], [ 1920, 240516 ], [ 1920, 240517 ], 
  [ 1920, 240518 ], [ 1920, 240519 ], [ 1920, 240520 ], [ 1920, 240521 ], [ 1920, 240522 ], [ 1920, 240523 ], [ 1920, 240524 ], [ 1920, 240525 ], 
  [ 1920, 240526 ], [ 1920, 240527 ], [ 1920, 240528 ], [ 1920, 240529 ], [ 1920, 240530 ], [ 1920, 240531 ], [ 1920, 240532 ], [ 1920, 240533 ], 
  [ 1920, 240534 ], [ 1920, 240535 ], [ 1920, 240536 ], [ 1920, 240537 ], [ 1920, 240538 ], [ 1920, 240539 ], [ 1920, 240540 ], [ 1920, 240541 ], 
  [ 1920, 240542 ], [ 1920, 240543 ], [ 1920, 240544 ], [ 1920, 240545 ], [ 1920, 240546 ], [ 1920, 240547 ], [ 1920, 240548 ], [ 1920, 240549 ], 
  [ 1920, 240550 ], [ 1920, 240551 ], [ 1920, 240552 ], [ 1920, 240553 ], [ 1920, 240554 ], [ 1920, 240555 ], [ 1920, 240556 ], [ 1920, 240557 ], 
  [ 1920, 240558 ], [ 1920, 240559 ], [ 1920, 240560 ], [ 1920, 240561 ], [ 1920, 240562 ], [ 1920, 240563 ], [ 1920, 240564 ], [ 1920, 240565 ], 
  [ 1920, 240566 ], [ 1920, 240567 ], [ 1920, 240568 ], [ 1920, 240569 ], [ 1920, 240570 ], [ 1920, 240571 ], [ 1920, 240572 ], [ 1920, 240573 ], 
  [ 1920, 240574 ], [ 1920, 240575 ], [ 1920, 240576 ], [ 1920, 240577 ], [ 1920, 240578 ], [ 1920, 240579 ], [ 1920, 240580 ], [ 1920, 240581 ], 
  [ 1920, 240582 ], [ 1920, 240583 ], [ 1920, 240584 ], [ 1920, 240585 ], [ 1920, 240586 ], [ 1920, 240587 ], [ 1920, 240588 ], [ 1920, 240589 ], 
  [ 1920, 240590 ], [ 1920, 240591 ], [ 1920, 240592 ], [ 1920, 240593 ], [ 1920, 240594 ], [ 1920, 240595 ], [ 1920, 240596 ], [ 1920, 240597 ], 
  [ 1920, 240598 ], [ 1920, 240599 ], [ 1920, 240600 ], [ 1920, 240601 ], [ 1920, 240602 ], [ 1920, 240603 ], [ 1920, 240604 ], [ 1920, 240605 ], 
  [ 1920, 240606 ], [ 1920, 240607 ], [ 1920, 240608 ], [ 1920, 240609 ], [ 1920, 240610 ], [ 1920, 240611 ], [ 1920, 240612 ], [ 1920, 240613 ], 
  [ 1920, 240614 ], [ 1920, 240615 ], [ 1920, 240616 ], [ 1920, 240617 ], [ 1920, 240618 ], [ 1920, 240619 ], [ 1920, 240620 ], [ 1920, 240621 ], 
  [ 1920, 240622 ], [ 1920, 240623 ], [ 1920, 240624 ], [ 1920, 240625 ], [ 1920, 240626 ], [ 1920, 240627 ], [ 1920, 240628 ], [ 1920, 240629 ], 
  [ 1920, 240630 ], [ 1920, 240631 ], [ 1920, 240632 ], [ 1920, 240633 ], [ 1920, 240634 ], [ 1920, 240635 ], [ 1920, 240636 ], [ 1920, 240637 ], 
  [ 1920, 240638 ], [ 1920, 240639 ], [ 1920, 240640 ], [ 1920, 240641 ], [ 1920, 240642 ], [ 1920, 240643 ], [ 1920, 240644 ], [ 1920, 240645 ], 
  [ 1920, 240646 ], [ 1920, 240647 ], [ 1920, 240648 ], [ 1920, 240649 ], [ 1920, 240650 ], [ 1920, 240651 ], [ 1920, 240652 ], [ 1920, 240653 ], 
  [ 1920, 240654 ], [ 1920, 240655 ], [ 1920, 240656 ], [ 1920, 240657 ], [ 1920, 240658 ], [ 1920, 240659 ], [ 1920, 240660 ], [ 1920, 240661 ], 
  [ 1920, 240662 ], [ 1920, 240663 ], [ 1920, 240664 ], [ 1920, 240665 ], [ 1920, 240666 ], [ 1920, 240667 ], [ 1920, 240668 ], [ 1920, 240669 ], 
  [ 1920, 240670 ], [ 1920, 240671 ], [ 1920, 240672 ], [ 1920, 240673 ], [ 1920, 240674 ], [ 1920, 240675 ], [ 1920, 240676 ], [ 1920, 240677 ], 
  [ 1920, 240678 ], [ 1920, 240679 ], [ 1920, 240680 ], [ 1920, 240681 ], [ 1920, 240682 ], [ 1920, 240683 ], [ 1920, 240684 ], [ 1920, 240685 ], 
  [ 1920, 240686 ], [ 1920, 240687 ], [ 1920, 240688 ], [ 1920, 240689 ], [ 1920, 240690 ], [ 1920, 240691 ], [ 1920, 240692 ], [ 1920, 240693 ], 
  [ 1920, 240694 ], [ 1920, 240695 ], [ 1920, 240696 ], [ 1920, 240697 ], [ 1920, 240698 ], [ 1920, 240699 ], [ 1920, 240700 ], [ 1920, 240701 ], 
  [ 1920, 240702 ], [ 1920, 240703 ], [ 1920, 240704 ], [ 1920, 240705 ], [ 1920, 240706 ], [ 1920, 240707 ], [ 1920, 240708 ], [ 1920, 240709 ], 
  [ 1920, 240710 ], [ 1920, 240711 ], [ 1920, 240712 ], [ 1920, 240713 ], [ 1920, 240714 ], [ 1920, 240715 ], [ 1920, 240716 ], [ 1920, 240717 ], 
  [ 1920, 240718 ], [ 1920, 240719 ], [ 1920, 240720 ], [ 1920, 240721 ], [ 1920, 240722 ], [ 1920, 240723 ], [ 1920, 240724 ], [ 1920, 240725 ], 
  [ 1920, 240726 ], [ 1920, 240727 ], [ 1920, 240728 ], [ 1920, 240729 ], [ 1920, 240730 ], [ 1920, 240731 ], [ 1920, 240732 ], [ 1920, 240733 ], 
  [ 1920, 240734 ], [ 1920, 240735 ], [ 1920, 240736 ], [ 1920, 240737 ], [ 1920, 240738 ], [ 1920, 240739 ], [ 1920, 240740 ], [ 1920, 240741 ], 
  [ 1920, 240742 ], [ 1920, 240743 ], [ 1920, 240744 ], [ 1920, 240745 ], [ 1920, 240746 ], [ 1920, 240747 ], [ 1920, 240748 ], [ 1920, 240749 ], 
  [ 1920, 240750 ], [ 1920, 240751 ], [ 1920, 240752 ], [ 1920, 240753 ], [ 1920, 240754 ], [ 1920, 240755 ], [ 1920, 240756 ], [ 1920, 240757 ], 
  [ 1920, 240758 ], [ 1920, 240759 ], [ 1920, 240760 ], [ 1920, 240761 ], [ 1920, 240762 ], [ 1920, 240763 ], [ 1920, 240764 ], [ 1920, 240765 ], 
  [ 1920, 240766 ], [ 1920, 240767 ], [ 1920, 240768 ], [ 1920, 240769 ], [ 1920, 240770 ], [ 1920, 240771 ], [ 1920, 240772 ], [ 1920, 240773 ], 
  [ 1920, 240774 ], [ 1920, 240775 ], [ 1920, 240776 ], [ 1920, 240777 ], [ 1920, 240778 ], [ 1920, 240779 ], [ 1920, 240780 ], [ 1920, 240781 ], 
  [ 1920, 240782 ], [ 1920, 240783 ], [ 1920, 240784 ], [ 1920, 240785 ], [ 1920, 240786 ], [ 1920, 240787 ], [ 1920, 240788 ], [ 1920, 240789 ], 
  [ 1920, 240790 ], [ 1920, 240791 ], [ 1920, 240792 ], [ 1920, 240793 ], [ 1920, 240794 ], [ 1920, 240795 ], [ 1920, 240796 ], [ 1920, 240797 ], 
  [ 1920, 240798 ], [ 1920, 240799 ], [ 1920, 240800 ], [ 1920, 240801 ], [ 1920, 240802 ], [ 1920, 240803 ], [ 1920, 240804 ], [ 1920, 240805 ], 
  [ 1920, 240806 ], [ 1920, 240807 ], [ 1920, 240808 ], [ 1920, 240809 ], [ 1920, 240810 ], [ 1920, 240811 ], [ 1920, 240812 ], [ 1920, 240813 ], 
  [ 1920, 240814 ], [ 1920, 240815 ], [ 1920, 240816 ], [ 1920, 240817 ], [ 1920, 240818 ], [ 1920, 240819 ], [ 1920, 240820 ], [ 1920, 240821 ], 
  [ 1920, 240822 ], [ 1920, 240823 ], [ 1920, 240824 ], [ 1920, 240825 ], [ 1920, 240826 ], [ 1920, 240827 ], [ 1920, 240828 ], [ 1920, 240829 ], 
  [ 1920, 240830 ], [ 1920, 240831 ], [ 1920, 240832 ], [ 1920, 240833 ], [ 1920, 240834 ], [ 1920, 240835 ], [ 1920, 240836 ], [ 1920, 240837 ], 
  [ 1920, 240838 ], [ 1920, 240839 ], [ 1920, 240840 ], [ 1920, 240841 ], [ 1920, 240842 ], [ 1920, 240843 ], [ 1920, 240844 ], [ 1920, 240845 ], 
  [ 1920, 240846 ], [ 1920, 240847 ], [ 1920, 240848 ], [ 1920, 240849 ], [ 1920, 240850 ], [ 1920, 240851 ], [ 1920, 240852 ], [ 1920, 240853 ], 
  [ 1920, 240854 ], [ 1920, 240855 ], [ 1920, 240856 ], [ 1920, 240857 ], [ 1920, 240858 ], [ 1920, 240859 ], [ 1920, 240860 ], [ 1920, 240861 ], 
  [ 1920, 240862 ], [ 1920, 240863 ], [ 1920, 240864 ], [ 1920, 240865 ], [ 1920, 240866 ], [ 1920, 240867 ], [ 1920, 240868 ], [ 1920, 240869 ], 
  [ 1920, 240870 ], [ 1920, 240871 ], [ 1920, 240872 ], [ 1920, 240873 ], [ 1920, 240874 ], [ 1920, 240875 ], [ 1920, 240876 ], [ 1920, 240877 ], 
  [ 1920, 240878 ], [ 1920, 240879 ], [ 1920, 240880 ], [ 1920, 240881 ], [ 1920, 240882 ], [ 1920, 240883 ], [ 1920, 240884 ], [ 1920, 240885 ], 
  [ 1920, 240886 ], [ 1920, 240887 ], [ 1920, 240888 ], [ 1920, 240889 ], [ 1920, 240890 ], [ 1920, 240891 ], [ 1920, 240892 ], [ 1920, 240893 ], 
  [ 1920, 240894 ], [ 1920, 240895 ], [ 1920, 240896 ], [ 1920, 240897 ], [ 1920, 240898 ], [ 1920, 240899 ], [ 1920, 240900 ], [ 1920, 240901 ], 
  [ 1920, 240902 ], [ 1920, 240903 ], [ 1920, 240904 ], [ 1920, 240905 ], [ 1920, 240906 ], [ 1920, 240907 ], [ 1920, 240908 ], [ 1920, 240909 ], 
  [ 1920, 240910 ], [ 1920, 240911 ], [ 1920, 240912 ], [ 1920, 240913 ], [ 1920, 240914 ], [ 1920, 240915 ], [ 1920, 240916 ], [ 1920, 240917 ], 
  [ 1920, 240918 ], [ 1920, 240919 ], [ 1920, 240920 ], [ 1920, 240921 ], [ 1920, 240922 ], [ 1920, 240923 ], [ 1920, 240924 ], [ 1920, 240925 ], 
  [ 1920, 240926 ], [ 1920, 240927 ], [ 1920, 240928 ], [ 1920, 240929 ], [ 1920, 240930 ], [ 1920, 240931 ], [ 1920, 240932 ], [ 1920, 240933 ], 
  [ 1920, 240934 ], [ 1920, 240935 ], [ 1920, 240936 ], [ 1920, 240937 ], [ 1920, 240938 ], [ 1920, 240939 ], [ 1920, 240940 ], [ 1920, 240941 ], 
  [ 1920, 240942 ], [ 1920, 240943 ], [ 1920, 240944 ], [ 1920, 240945 ], [ 1920, 240946 ], [ 1920, 240947 ], [ 1920, 240948 ], [ 1920, 240949 ], 
  [ 1920, 240950 ], [ 1920, 240951 ], [ 1920, 240952 ], [ 1920, 240953 ], [ 1920, 240954 ], [ 1920, 240955 ], [ 1920, 240956 ], [ 1920, 240957 ], 
  [ 1920, 240958 ], [ 1920, 240959 ], [ 1920, 240960 ], [ 1920, 240961 ], [ 1920, 240962 ], [ 1920, 240963 ], [ 1920, 240964 ], [ 1920, 240965 ], 
  [ 1920, 240966 ], [ 1920, 240967 ], [ 1920, 240968 ], [ 1920, 240969 ], [ 1920, 240970 ], [ 1920, 240971 ], [ 1920, 240972 ], [ 1920, 240973 ], 
  [ 1920, 240974 ], [ 1920, 240975 ], [ 1920, 240976 ], [ 1920, 240977 ], [ 1920, 240978 ], [ 1920, 240979 ], [ 1920, 240980 ], [ 1920, 240981 ], 
  [ 1920, 240982 ], [ 1920, 240983 ], [ 1920, 240984 ], [ 1920, 240985 ], [ 1920, 240986 ], [ 1920, 240987 ], [ 1920, 240988 ], [ 1920, 240989 ], 
  [ 1920, 240990 ], [ 1920, 240991 ], [ 1920, 240992 ], [ 1920, 240993 ], [ 1920, 240994 ], [ 1920, 240995 ], [ 1920, 240996 ], [ 1920, 240997 ], 
  [ 1920, 240998 ], [ 1920, 240999 ], [ 1920, 241000 ], [ 1920, 241001 ], [ 1920, 241002 ], [ 1920, 241003 ], [ 1920, 241004 ], [ 1980, 57 ], [ 1980, 58 ] 
 ];

LogTo("GAPlog.txt");
