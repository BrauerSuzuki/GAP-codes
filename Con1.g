#tested on GAP 4.8.10
LoadPackage("hecke");

ScopesCores:=function(p,w) #returns representatives of the Scope cores of p-blocks with weight w without conjugate cores
local L,cores,a,part,l,i,EnumerateAbaci;

	EnumerateAbaci:=function(L,p,w) #auxiliary (recursive) function to enumerate abaci
	local L2,i,a;
		if L=[] then L:=List([0..w-1],i->[i]); return EnumerateAbaci(L,p,w); fi;
		if Size(L[1])=p-1 then return L; fi;
		L2:=[];
		for a in L do
			Append(L2,List([0..a[Size(a)]+w-1],i->Concatenation(a,[i])));
		od;
		return EnumerateAbaci(L2,p,w);
	end;

	L:=EnumerateAbaci([],p,w); #list of core abaci
	cores:=[]; #list of cores
	for a in L do #construct partition from abacus a
		part:=[];
		l:=0; #initial length of partition part
		for i in [1..(p-1)*p*(w-1)-1] do #possible first hook lengths
			if i mod p<>0 and a[RemInt(i,p)]>Int(i/p) then 
				Add(part,i-l); 
				l:=l+1;
			fi;
		od;
		part:=Reversed(part);
		if part=[] or (not AssociatedPartition(part) in cores) then AddSet(cores,part); fi;
	od;
	SortBy(cores,Sum);
	return cores;
end;

PartitionsWithCore:=function(p,core,w) #returns partitions with given core and weight
	return Reversed(SortedList(List(PartitionTuples(w,p),lam->CombineEQuotientECore(p,lam,core))));
end;	

JantzenSchaper:=function(p,core,w) #returns decomposition matrix of p-block with given core and weight w<4
local B,regB,hooks,lam,lam2,Hlam,h,pairs,c,dec,Co,i,j,k;
	B:=PartitionsWithCore(p,core,w); 
	regB:=Filtered(B,part->IsERegular(p,part)); 
	hooks:=[];
	for lam in B do
		lam2:=AssociatedPartition(lam);
		Hlam:=[];
		for i in [1..Size(lam)] do
			for j in [1..lam[i]] do
				h:=lam[i]+lam2[j]-i-j+1;
				if h mod p=0 then Add(Hlam,[i,j,h,(lam2[j]-i) mod 2]); fi;
			od;
		od;
		Add(hooks,Hlam);
	od;
	Co:=NullMat(Size(B),Size(B));
	for i in [1..Size(B)] do
		for j in [1..i-1] do
			pairs:=Filtered(Cartesian(hooks[i],hooks[j]),c->c[1][3]=c[2][3] and RemoveRimHook(B[i],c[1][1],c[1][2])=RemoveRimHook(B[j],c[2][1],c[2][2]));
			Co[i][j]:=-Sum(pairs,c->(-1)^(c[1][4]+c[2][4])*Valuation(c[1][3],p));
		od;
	od;
	dec:=NullMat(Size(B),Size(regB));
	for i in [1..Size(B)] do
		for j in [1..Size(regB)] do
			if B[i]=regB[j] then dec[i][j]:=1; elif 
				Sum([1..i-1],k->dec[k][j]*Co[i][k])>0 then dec[i][j]:=1;
			fi;
		od;
	od;
	return dec;
end;

#example session:
p:=7;;
w:=2;;
L:=List(ScopesCores(p,w),c->JantzenSchaper(p,c,w));; #decomposition matrices of 7-blocks of weight 2
ForAny(Combinations(L,2),c->TransformingPermutations(c[1],c[2])<>fail); #check if pairwise not Morita equivalent
#computation can be speed up (especially for larger p and w) by first comparing row sums and column sums of decomposition matrices (instead of the more expensive TransformingPermutation) and code can run in parallel

#The following functions are not necessary, but may be of interest
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
