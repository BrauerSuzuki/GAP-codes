ElementsC:=function(G) #returns set of representatives for conjugacy classes of G
return List(ConjugacyClasses(G),Representative);
end;

SubgroupsC:=function(G) #returns set of representatives for conjugacy classes of subgroups of G
return List(ConjugacyClassesSubgroups(G),Representative);
end;

PermCol:=function(M,g) #permute columns of matrix M with permutation g
local T;
	T:=List(TransposedMat(M));
	T:=Permuted(T,g);
	return TransposedMat(T);
end;

ActPerm:=function(M,g) #permute rows and columns of square matrix M simultaneously with permutation g
	return TransposedMat(Permuted(TransposedMat(Permuted(M,g)),g));
end;

InvPS:=function(a,d) #approximate inverse of power series with coefficients a=(a_0,…) where a_0\ne 0, up to d coefficients
local s,b,i;
	if a[1]=0 then Error("Power series not invertible"); fi;
	s:=Size(a);
	b:=[1/a[1]];
	for i in [2..d-1] do
		b[i]:=-Sum([1..Minimum(i-1,s-1)],j->a[j+1]*b[i-j])/a[1];
	od;
	return b;
end;

GroupDeterminant:=function(G) #compute the group determinant of G as a multivariant polynomial, very slow
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

LoadPackage("anupq");
1536to512:=function(id) #returns IdGroup(SylowSubgroup(SmallGroup(1536,id),2))[2]
local G,P,F,H;
	if id<=10494213 then return id; fi; #nilpotent groups
	G:=SmallGroup(1536,id);
	P:=SylowSubgroup(G,2);
	F:=PqStandardPresentation(P);
	H:=PcGroupFpGroup(F);
	return IdStandardPresented512Group(H)[2];
end;

Id512:=function(G) #returns IdGroup(G) where G has order 512
local F,H;
	F:=PqStandardPresentation(G);
	H:=PcGroupFpGroup(F);
	return IdStandardPresented512Group(H);
end;

PPart:=function(n,p) #returns p-part of n
	if n=0 then
		return infinity;
	else
		return p^Valuation(n,p);
	fi;
end;

PPN:=function(n,p) #returns p'-part of n
	return n/p^Valuation(n,p);
end;

PadicExp:=function(n,p) #recursive function to compute the p-adic expansion of n
	if n<0 or p<2 then Error(n," must be non-negative and ",p," must be at least 2"); fi;
	if n<p then
		return [n];
	else
		return Concatenation(PadicExp(Int(n/p),p),[n mod p]);
	fi;
end;

IsRationalGroup:=function(G) #check if G is a rational group (character table is rational-valued)
local pi;
	if IsSolvable(G) then
		pi:=PrimeDivisors(Size(G));
		if not IsSubset([2,3,5],pi) then return false; fi; #Gow
		if Exponent(G) mod 25=0 or Index(G,PCore(G,5)) mod 5=0 then return false; fi; #Hegedüs
	fi;
	return Size(RationalClasses(G))=NrConjugacyClasses(G);
end;

GGtoNF:=function(G) #convert Galois group G to number field
local n,res;	
	n:=Characteristic(One(G));
	res:=List(Elements(G),Int);
	return NF(n,res);
end;

Qg:=function(G,g) #compute Q(g)=Q(chi(g):chi in Irr(G)) where g in G
local rc,gg;	
	rc:=RationalClass(G,g);
	gg:=GaloisGroup(rc);
	return GGtoNF(gg);
end;

LoadPackage("grape",false);;
HasStronglyP:=function(G,p) #check if G has a strongly p-embedded complement, needs package "grape"
local P,S,g;
	if Size(G) mod p<>0 or Size(PCore(G,p))>1 then return false; fi;
	P:=SylowSubgroup(G,p);
	if IsCyclic(P) or IsQuaternionGroup(P) then return true; fi;
	S:=List(ConjugacyClassSubgroups(G,P));
	g:=Graph(Group(()),S,OnPoints,{x,y}->Size(Intersection(x,y))>1,true );
	return not IsConnectedGraph(g);
end;

HallPoly:=function(lam,mu,q) #returns the Hall polynomial in q with respect to partitions mu \subseteq lam
local lam2,mu2;
	lam2:=AssociatedPartition(lam);
	mu2:=Concatenation(AssociatedPartition(mu),0*[1..lam[1]-mu[1]+1]);
	return Product([1..lam[1]],i->q^(mu2[i+1]*(lam2[i]-mu2[i]))*GaussianCoefficient(lam2[i]-mu2[i+1],mu2[i]-mu2[i+1],q));
end;

NrSubgroups:=function(lam,n,q) #returns the number of subgroups of order q^n in the abelian group of type lam
local F,mu;
	F:=Filtered(Partitions(n),mu->Size(mu)<=Size(lam) and ForAll([1..Size(mu)],i->mu[i]<=lam[i]));
	return Sum(F,mu->HallPoly(lam,mu,q));
end;

PPCore:=function(G,p) #returns p'-core of G
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

PResidue:=function(G,p) #returns p-residue of G
local L;
L:=Filtered(ElementsC(G),x->Order(x) mod p<>0);
return NormalClosure(G,Subgroup(G,L));
end;

PPrimeResidue:=function(G,p) #returns p'-residue of G
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

SubgroupComplement:=function(G,H) #returns complement of H in G or fail if there is none
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

PLength:=function(G,p) #returns p-length of p-solvable group G
local N;
	if not IsPSolvable(G,p) then return fail; fi;
	if Size(G) mod p<>0 then return 0; fi;
	N:=PPCore(G,p);
	if Size(N)>1 then return PLength(G/N,p); else return 1+PLength(G/PCore(G,p),p); fi;
end;

FusionNumber:=function(ct,p,b) #fusion number of b-th p-block defined in my paper "Character tables and defect groups"
local pb,pos,M,F,d,ed,ed2,i,j;
	pb:=PrimeBlocks(ct,p);
	pos:=Positions(pb.block,b);
	M:=MutableMatrix(Irr(ct){pos});;
	M:=MutableMatrix(TransposedMat(M)*ComplexConjugate(M));;
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

IsFrobeniusGroup:=function(G) #check wether G is a Frobenius group
local N;
	N:=FittingSubgroup(G);
	if Size(N) in [1,Size(G)] or Gcd(Size(N),Index(G,N))>1 then return false; fi;
	if NrConjugacyClasses(G)=NrConjugacyClasses(G/N)+(NrConjugacyClasses(N)-1)/Index(G,N) then
		return true;
	else
		return false;
	fi;
end;

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

Binomial2:=function(n,k) #binomial coefficient "n choose k" where n is any complex number
	return Product([1..k],i->(n-i+1)/i); 
end;

Number2Latex:=function(n) #transforms 120 into LaTeX 2^3\cdot 3\cdot 5, experimental
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

EDchar:=function(ct) #returns e(G) of group G with character table ct, from my paper "The reciprocal character of the conjugation action"
local f,S,x,c;
	f:=ClassFunction(ct,List(SizesCentralizers(ct),x->x^-1));
	S:=List(Irr(ct),c->ScalarProduct(c,f));
	return Lcm(List(S,DenominatorRat));
end;

EDchar2:=function(ct) #different algorithm
local f,x;
	f:=List(SizesConjugacyClasses(ct),x->x^2);
	return Gcd(List(Irr(ct),x->List(x)*f));
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

SemidihedralGroup:=function(n) #returns semidihedral group SD_n as permutation group, certainly not very efficient
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
local pb,d,pos,deg;
	pb:=PrimeBlocks(ct,p);
	d:=pb.defect[b];
	if d<2 then return true; fi;
	pos:=Positions(pb.block,b);
	deg:=List(Irr(ct){pos},c->DegreeOverPrimeField(Field(c))) mod p^(d-1);
	return 0 in deg;
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
	M:=MutableMatrix(Irr(ct){pos});;
	M:=MutableMatrix(TransposedMat(M)*ComplexConjugate(M));;
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

IsMetacyclic2Group:=function(G) #check if G is metacyclic 2-group
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

IsMetacyclic:=function(G) #check if G is metacyclic
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

IsBicyclic2Group:=function(G) #check if G=<x><y> for some x,y in G
local M;
	if RankPGroup(G)>2 then return false; fi;
	M:=MaximalSubgroups(G);
	if Size(Filtered(M,IsMetacyclic))=2 then return true; fi;
	return false;
end;

IsBicyclic:=function(G) #check if G=<x><y> for some x,y in G
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

IsMinimalNonabelian:=function(G) #check if G is non-abelian, but every proper subgroup is abelian
	if IsAbelian(G) then return false; fi;
	return ForAll(MaximalSubgroupClassReps(G),IsAbelian);
end;

MNA:=function(r,s,p) #returns minimal non-abelian p-group <x,y,z|x^{p^r}=y^{p^s}=z^p=[x,z]=[y,z]=1,[x,y]=z>
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

CentralProductDefault:=function(G,H) #construct central product G*H if there is a canonical choice for the isomorphism Z(G)->Z(H)
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

AllNondirectCentralProducts:=function(G,H) #returns all central products G*H except those of the form GxK with K\le H
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

IsPositiveDefinite:=function(M) #check if matrix M is positive definite, Decartes rule of signs
local p,l,i;
	if not TransposedMat(M)=M then Error("Matrix must be symmetric"); fi;
	p:=CharacteristicPolynomial(M);
	l:=CoefficientsOfUnivariatePolynomial(p);
	if ForAll([1..Size(l)-1],i->l[i]*l[i+1]<0) then return true; else return false; fi;
end;

IsPositiveSemidefinite:=function(M) #check if matrix M is positive semidefinite
local p,l,i;
	if not TransposedMat(M)=M then Error("Matrix must be symmetric"); fi;
	p:=CharacteristicPolynomial(M);
	l:=List(CoefficientsOfUnivariatePolynomial(p));
	while l[1]=0 do Remove(l,1); od;
	if ForAll([1..Size(l)-1],i->l[i]*l[i+1]<0) then return true; else return false; fi;
end;

IsSymmetricMat:=function(M) #check if matrix M is symmetric
return M=TransposedMat(M);
end;

OuterAutomorphismGroup:=function(G)
local A;
	A:=AutomorphismGroup(G);
	return A/InnerAutomorphismsAutomorphismGroup(A);
end;

PRank:=function(G) #returns largest rank of an abelian subgroup of p-group G
	local f,H;
	if IsAbelian(G) then return RankPGroup(G); else
	f:=NaturalHomomorphismByNormalSubgroupNC(G,Center(G));
	return Maximum(List(Filtered(List(SubgroupsC(G/Center(G)),H->PreImage(f,H)),IsAbelian),RankPGroup)); fi;
end;

HasMaximalClass:=function(G) #check if p-group G has maximal nilpotency class
	if not IsPGroup(G) then Error(G," must be a p-group!"); fi;
	if Size(FactorsInt(Size(G)))-NilpotencyClassOfGroup(G)=1 then return true; else return false; fi;
end;

Gamma1:=function(G) #compute characteristic maximal subgroup gamma_1(G) where G is p-group of maximal class
	local LC,f;
	if not HasMaximalClass(G) then Error(G, "must be a p-group of maximal class!"); fi;
	LC:=LowerCentralSeries(G);
	f:=NaturalHomomorphismByNormalSubgroupNC(G,LC[4]);
	return PreImage(f,Centralizer(G/LC[4],Image(f,LC[2])));
end;

IsExceptionalGroup:=function(G) #check if p-group G of maximal class is exceptional
	local n;
	if not HasMaximalClass(G) then Error(G, "must be a p-group of maximal class!"); fi;
	n:=Size(FactorsInt(Size(G)));
	if n<5 then Error(G, "must have order at least p^5!"); fi;
	if PrimePGroup(G)<5 or n>PrimePGroup(G)+1 or n mod 2=1 then return false; fi;
	if Gamma1(G)=Centralizer(G,LowerCentralSeries(G)[n-2]) then return false; else return true; fi;
end;

Extracti:=function(i,size) #auxiliary function of BlockInfo
if IsList(i) then return Size(Intersection([1..size],i[1])); else return i; fi;
end;

BlockInfo:=function(ct,p,def) #prints summary of p-blocks of ct, if def=true then defect groups are computed (takes time)
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

NrBrauerChars:=function(ct,p,nr) #compute number of Brauer characters of nr-th p-block of ct
local L,L2,i,A;
	L:=Positions(PrimeBlocks(ct,p).block,nr);
	L2:=PositionsProperty(OrdersClassRepresentatives(ct),i->i mod p<>0);
  A:=IntegralizedMat(Irr(ct){L}{L2}).mat; #Rank is faster for integral matrices
  return Rank(A);
end;

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

Cartanmatrix:=function(ct,p,nr) #compute Cartan matrix of nr-th p-block of character table ct up to basic sets (does not need Brauer characters)
local L,L2,i,Q,A;
	L:=Positions(PrimeBlocks(ct,p).block,nr);
	L2:=PositionsProperty(OrdersClassRepresentatives(ct),i->i mod p=0);
	A:=Irr(ct){L}{L2};
	Q:=NullspaceIntMat(IntegralizedMat(A).mat);
	return LLLReducedGramMat(Q*TransposedMat(Q)).remainder; #ReduceQF(Q*TransposedMat(Q));
end;

#Magma: CartanMatrix(G,F) faster
CartanMatrixFG:=function(F,G) #compute Cartan matrix of finite group G over field F with meataxe
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

DecompositionBS:=function(ct,p,nr) #compute decomposition matrix of nr-th p-block of ct up to basic sets
local L,L2,i,Q,A;
	L:=Positions(PrimeBlocks(ct,p).block,nr);
	L2:=PositionsProperty(OrdersClassRepresentatives(ct),i->i mod p=0);
  A:=Irr(ct){L}{L2};
	Q:=NullspaceIntMat(IntegralizedMat(A).mat);
	return TransposedMat(Q); 
end;

GeneralizedDecomposition:=function(G,ct,u,i)
#compute generalized decomposition matrix of i-th p-block of G with respect to p-element u, up to basic sets
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

GeneralizedDecomposition2:=function(G,ct,u,i) #alternative algorithm taking possible class fusion into account
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

MatchUp:=function(P,Q,s,PM) #auxiliary function for UpToBasicSets
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

Matrix2Latex:=function(M) #convert matrix to Latex pmatrix with dots for 0
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

LoewyLength:=function(A) #compute Loewy length of algebra A
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

ThJ:=function(P) #returns Thompson subgroup of p-group P
local m;
m:=Maximum(List(Filtered(SubgroupsC(P),IsAbelian),Size));
return Subgroup(P,Union(Filtered(AllSubgroups(P),H->Size(H)=m and IsAbelian(H))));
end;

reps:=function(G,N) #returns set of representatives for the non-trivial cosets of N in G
local x;
	return Filtered(RightTransversal(G,N),x->not x in N);
end;

CompositionFactors:=function(G) #returns composition factors of G
local cs;
	cs:=CompositionSeries(G);
	return List([1..Size(cs)-1],i->cs[i]/cs[i+1]);
end;

PPrimeSubgroups:=function(G,p) #returns p'-subgroups of G, not necessarily reduced to conjugation
local f,npp,L,q,Q,SGQ,H,R,N,pre;
	if Size(G)<10^4 then return Filtered(SubgroupsC(G),H->Size(H) mod p<>0); fi; #brute force
	if Size(G) mod p<>0 then return SubgroupsC(G); fi; #no other way
	if IsSolvable(G) then return SubgroupsC(SylowComplement(G,p)); fi;
	R:=PResidue(G,p);
	if R<>G then return PPrimeSubgroups(R,p); fi;
	R:=PCore(G,p);
	if Size(R)>1 then
		f:=NaturalHomomorphismByNormalSubgroupNC(G,R);
		return List(PPrimeSubgroups(Image(f),p),Q->PreImage(f,Q));
	fi;
	npp:=Size(G)/p^Valuation(Size(G),p); #p'-part of |G|
	if p>2 and ForAny(CompositionFactors(G),c->npp mod Size(c)=0) then Info(InfoWarning,1,"Nonsolvable p'-subgroups not considered!"); fi;
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

bysize:=function(n,m) #auxiliary
	return Size(n)<Size(m);
end;

InducedRep:=function(G,H,f,q) #return the induced representation f^G where f is matrix rep for H\le G in F_q
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

CharacterAlgebra:=function(G,p) #compute F_pIrr(G) where p is prime
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

CenterOfGroupAlgebra:=function(G,p) #compute Z(F_pG) where p is prime, G can be group or character table
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

PSections:=function(ct,p) #compute p-sections of G
local ords,L,i,psec;
	ords:=OrdersClassRepresentatives(ct);
	L:=List([1..NrConjugacyClasses(ct)],i->PowerMap(ct,ords[i]/p^Valuation(ords[i],p),i));
	psec:=[];
	for i in AsSet(L) do
		Add(psec,Positions(L,i));
	od;
	return psec;
end;

ClassBlocks:=function(ct,p) #class blocks of ct defined in my paper "Remarks on Harada’s Conjecture"
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

DefectOfCB:=function(ct,p,C) #defect group of class blocks
local G,El,Syl,m,i,x;
	G:=UnderlyingGroup(ct);
	El:=List(ConjugacyClasses(ct),Representative);
	Syl:=List(C,i->SylowSubgroup(Centralizer(G,El[i]),p));
	m:=Maximum(List(Syl,Size));
	return First(Syl,x->Order(x)=m);
end;

NilpotentBlocks:=function(ct,p)
#returns list of positions of nilpotent p-blocks in character table ct, Warning: based on a conjecture by Malle-Navarro
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

lB1Blocks:=function(ct,p) #returns list of positions of non-nilpotent p-blocks B with l(B)=1
	local pb,bl,b; 
	pb:=PrimeBlocks(ct,p);
	bl:=Difference([1..Size(pb.defect)],NilpotentBlocks(ct,p));
	return Filtered(bl,b->NrBrauerChars(ct,p,b)=1);
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

IsQuasiPrimitiveBlock:=function(G,p,i) #checks if i-th p-block of G is quasiprimitive
local ct,N,ctN;
	ct:=CharacterTable(G);
	for N in NormalSubgroups(G) do
		ctN:=CharacterTable(N);
		if Size(CoveredBlocks(ct,p,i,ctN))>1 then return false; fi;
	od;
	return true;
end;

Sturm:=function(P,a,b) #returns number of distinct real roots of polynomial P in interval (a,b] using Storm's method
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

#the pairs (a,b) such that PrimitiveGroup(a,b) is a sporadic transitive linear group of degree b (appearing in Hering's classification)
SporLinGroups:=[[25,15],[25,18],[25,19],[49,25],[49,29],[121,39],[121,42],[121,56],[121,57],[19^2,86],[23^2,59],[29^2,106],[29^2,110],[59^2,84],[16,20],[81,71],[81,90],[81,99],[81,130],[81,129],[81,124],[81,126],[81,127],[81,128],[3^6,396]];

#orders <2000 of non-solvable groups
NonsolvableOrders:=[ 60, 120, 168, 180, 240, 300, 336, 360, 420, 480, 504, 540, 600, 660, 672, 
  720, 780, 840, 900, 960, 1008, 1020, 1080, 1092, 1140, 1176, 1200, 1260, 
  1320, 1344, 1380, 1440, 1500, 1512, 1560, 1620, 1680, 1740, 1800, 1848, 
  1860, 1920, 1980 ];

#list of names of simple groups in the character table library
CTSimple:=[ "A5", "L3(2)", "A6", "L2(8)", "L2(11)", "L2(13)", "L2(17)", "A7", "L2(19)", "L2(16)", "L3(3)", "U3(3)", "L2(23)", "L2(25)", "M11", 
  "L2(27)", "L2(29)", "L2(31)", "L3(4)", "A8", "L2(37)", "U4(2)", "Sz(8)", "L2(32)", "L2(41)", "L2(43)", "L2(47)", "L2(49)", "U3(4)", "L2(53)", "M12", 
  "L2(59)", "L2(61)", "U3(5)", "L2(67)", "J1", "L2(71)", "A9", "L2(73)", "L2(79)", "L2(64)", "L2(81)", "L2(83)", "L2(89)", "L3(5)", "M22", "L2(97)", 
  "L2(101)", "L2(103)", "J2", "L2(107)", "L2(109)", "L2(113)", "L2(121)", "L2(125)", "S4(4)", "S6(2)", "A10", "L3(7)", "U4(3)", "G2(3)", "S4(5)", "U3(8)", 
  "U3(7)", "L4(3)", "L5(2)", "M23", "U5(2)", "L3(8)", "2F4(2)'", "A11", "Sz(32)", "L3(9)", "U3(9)", "HS", "J3", "U3(11)", "S4(7)", "O8+(2)", "O8-(2)", 
  "3D4(2)", "L3(11)", "A12", "M24", "G2(4)", "McL", "L4(4)", "U4(4)", "S4(8)", "S4(9)", "A13", "He", "S6(3)", "O7(3)", "G2(5)", "L4(5)", "U6(2)", "R(27)", 
  "U4(5)", "L6(2)", "A14", "S8(2)", "Ru", "L5(3)", "U5(3)", "Suz", "ON", "Co3", "A15", "S6(4)", "O8+(3)", "O8-(3)", "A16", "O10+(2)", "O10-(2)", "Co2", 
  "L4(9)", "U5(4)", "Fi22", "L7(2)", "A17", "U7(2)", "S6(5)", "O7(5)", "HN", "A18", "F4(2)", "S10(2)", "Ly", "A19", "S8(3)", "O9(3)", "Th", "Fi23", "Co1", 
  "L8(2)", "J4", "O10-(3)", "U6(4)", "2E6(2)", "O8+(7)", "S12(2)", "E6(2)", "2F4(8)", "F3+", "B", "M" ];

#list of names of almost simple groups in the character table library
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

#list of names of sporadic simple groups in the character table library
CTSporadic:=[ "M11", "M12", "J1", "M22", "J2", "M23", "HS", "J3", "M24", "McL", "He", "Ru", "Suz", "ON", "Co3", "Co2", "Fi22", "HN", "Ly", "Th", "Fi23", "Co1", "J4", "F3+", "B", "M" ];

#list of names of non-solvable groups in the character table library
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
