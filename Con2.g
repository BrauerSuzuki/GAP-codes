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

HookLengths:=function(part) #returns list of hook lengths for each box in Young diagram
local hl,part2,i,j;
	if part=[] then return []; fi;
	hl:=[];
	part2:=AssociatedPartition(part);
	for i in [1..Size(part)] do
		hl[i]:=[];
		for j in [1..part[i]] do
			hl[i][j]:=part[i]+part2[j]-i-j+1;
		od;
	od;
	return hl;
end;

PSign:=function(p,part) #returns the p-sign of the partition part
local s,hl,a,perm,z,i;
	s:=Size(part);
	hl:=List([0..s-1],i->part[s-i]+i); #first colum hook length = beta-set
	a:=List([0..p-1],i->Filtered(hl,x->x mod p=i)); #abacus upslided
	perm:=[];
	z:=0;
	while Size(perm)<s do
		if IsBound(a[(z mod p)+1][Int(z/p)+1]) then Add(perm,a[(z mod p)+1][Int(z/p)+1]); fi;
		z:=z+1;
	od;
	return SignPerm(MappingPermListList(hl,perm));
end;

PDash:=function(n,p) #returns the p'-part of the integer n
	return n/p^Valuation(n,p); 
end;

DegreeWrSym:=function(lam,p) #returns character degree of partition p-tuple lam in C_p\wr S_w 
local w,mu,prod;
	w:=Sum(Concatenation(lam));
	prod:=Product(lam,mu->Product(Concatenation(HookLengths(mu))));
	return Factorial(w)/prod;
end;

ClassSizeWrSym:=function(lam,p) #returns class size of partition p-tuple lam in C_p\wr S_w
local w,mu,prod;
	w:=Sum(Concatenation(lam));
	prod:=Product(lam,mu->p^Size(mu)*Product(Collected(mu),c->c[1]^c[2]*Factorial(c[2])));
	return Factorial(w)*p^w/prod;
end;

#replacement for CombineEQuotientCore (in hecke package) which has a minor bug
CoreQuotient2Partition:=function(p,core,quot) #returns partition with given p-core and p-quotient
local s,hl,w,d,beta,a,b,i,j,x,abacus;
	if not IsECore(p,core) then Error(core," is not a ",p," core"); fi;
	s:=Size(core);
	hl:=List([1..s],i->core[i]+s-i); #first column hook lengths
	w:=Maximum(List(quot,Size)); #maximal number of beads on runners
	d:=p*w+((-s) mod p);
	beta:=hl+List(hl,i->d); #construct beta-size of large enough size = 0 (mod p)
	for i in [1..d] do Add(beta,d-i); od; 
	a:=List([0..p-1],i->Number(beta,x->x mod p=i)); #count beads on runners
	b:=List(quot,lam->List([1..Size(lam)],i->lam[i]+Size(lam)-i)); #beta-set from quot
	for i in [1..p] do 
		d:=a[i]-Size(b[i]);
		b[i]:=b[i]+List(b[i],j->d); #make beta-set b[i] long enough
		for j in [1..d] do Add(b[i],d-j); od;
	od;
	abacus:=Union(List([1..p],i->List(b[i],j->j*p+(i-1)))); #abacus of desired partition
	return Reversed(Filtered(List([1..Size(abacus)],i->abacus[i]-i+1),i->i>0));
end;

#let ct be the character table of G\wr S_n where G is a finite group with character table tbl
#the following code (provided by Thomas Breuer) computes the columns of ct corresponding to the partition tuples with empty first component
#This uses much less memory than computing the full table via 
MatCharsWreathSymmetricRest:= function( tbl, n)
    local tbl_irreducibles,
          i, j, k, m, r, s, t, pm, res, col, scheme, np, charCol, hooks,
          pts, partitions,
globalpos, parapos;

    r:= NrConjugacyClasses( tbl );
    tbl_irreducibles:= List( Irr( tbl ), ValuesOfClassFunction );

    #  encode partition tuples by positions of partitions.
    partitions:= List([1..n], Partitions);
    pts:= [];
    for i in [1..n] do
       pts[i]:= PartitionTuples(i, r);
       for j in [1..Length(pts[i])] do
	 np:= [[], []];
	 for t in pts[i][j] do
	    s:= Sum( t, 0 );
	    Add(np[1], s);
	    if s = 0 then
	       Add(np[2], 1);
	    else
	       Add(np[2], Position( partitions[s], t, 0 ));
	    fi;
	 od;
	 pts[i][j]:= np;
       od;
    od;

parapos:= PositionsProperty( PartitionTuples( n, r ), x -> x[1] = [] );
IsSSortedList( parapos );  # PositionsProperty should always set IsSSortedList!

    scheme:= InductionScheme(n);

    #  how to encode a hook.
    hooks:= function(np, n)
       local res, i, k, l, ni, pi, sign;

       res:= [];
       for i in [1..r] do
	 res[i]:= List([1..n], x-> []);
       od;

       for i in [1..r] do
	 ni:= np[1][i]; pi:= np[2][i];
	 for k in [1..ni] do
	    for l in scheme[ni][pi][k] do
	       np[1][i]:= ni-k; 
	       if l < 0 then
		  np[2][i]:= -l;
		  sign:= -1;
	       else
		  np[2][i]:= l;
		  sign:= 1;
	       fi;
	       if k = n then
		  Add(res[i][k], sign);
	       else
		  Add(res[i][k], sign * Position(pts[n-k], np));
	       fi;
	    od;
	 od;
	 np[1][i]:= ni; np[2][i]:= pi;
       od;
       return res;
    end;

    #  collect hook encodings.
    res:= [];
    Info( InfoCharacterTable, 2, "Scheme:" );
    for i in [1..n] do
       Info( InfoCharacterTable, 2, i );
       res[i]:= [];
       for np in pts[i] do
	 Add(res[i], hooks(np, i));
       od;
    od;
    scheme:= res;

    #  how to construct a new column.
    charCol:= function(n, t, k, p)
       local i, j, col, pi, val;

       col:= [];
       for pi in scheme[n] do
	 val:= 0;
	 for j in [1..r] do
	    for i in pi[j][k] do
	       if i < 0 then
		  val:= val - tbl_irreducibles[j][p] * t[-i];
	       else
		  val:= val + tbl_irreducibles[j][p] * t[i];
	       fi;
	    od;
	 od;
	 Add(col, val);
       od;
       return col;
    end;

    #  construct the columns.
    pm:= List([1..n-1], x->[]);
    Info( InfoCharacterTable, 2, "Cycles:" );
    for m in [1..QuoInt(n,2)] do 

       # the $m$-cycle in all possible places
       Info( InfoCharacterTable, 2, m );
       for i in [1..r] do
	 s:= [1..n]*0+1;
	 s[m]:= i;
	 Add(pm[m], rec(col:= charCol(m, [1], m, i), pos:= s));
       od;

       # add the $m$-cycle to everything you know
       for k in [m+1..n-m] do
	 for t in pm[k-m] do
	    for i in [t.pos[m]..r] do
	       s:= ShallowCopy(t.pos);
	       s[m]:= i;
	       Add(pm[k], rec(col:= charCol(k, t.col, m, i), pos:= s));
	    od;
	 od;
       od;
    od;

    #  collect and transpose.
globalpos:= 0;
    np:= Length(scheme[n]);
    res:= List([1..np], x-> []);
    Info( InfoCharacterTable, 2, "Tables:" );
    for k in [1..n-1] do
       Info( InfoCharacterTable, 2, k );
       for t in pm[n-k] do
	 for i in [t.pos[k]..r] do 
globalpos:= globalpos + 1;
if globalpos in parapos then
	    col:= charCol(n, t.col, k, i);
	    for j in [1..np] do
	       Add(res[j], col[j]);
	    od;
fi;
	 od;
       od;
    od;

    for i in [1..r] do
globalpos:= globalpos + 1;
if globalpos in parapos then
       col:= charCol(n, [1], n, i);
       for j in [1..np] do
	 Add(res[j], col[j]);
       od;
fi;
    od;

    return res;

end;

#example session:
p:=2;;
w:=10;;
ct:=MatCharsWreathSymmetricRest(CharacterTable("cyclic",p),w);;
chars:=Filtered(PartitionTuples(w,p),lam->Sum(lam[1])>w/2 and DegreeWrSym(lam,p) mod p<>0);; #=\Delta (notation from paper)
charpos:=List(chars,t->Position(PartitionTuples(w,p),t));;
W:=ct{charpos};;
classes:=Filtered(PartitionTuples(w,p),lam->lam[1]=[]);;
M0:=PDash(p^w*Factorial(w),p)^-1*W*DiagonalMat(List(classes,c->ClassSizeWrSym(c,p)))*TransposedMat(W);; #M^0 in paper but without p-signs!
l:=Size(M0);;
L:=[];;
for core in ScopesCores(p,w) do
	D:=List(chars,x->PSign(p,CoreQuotient2Partition(p,core,x)));
	Q:=MutableCopyMat(M0);
	for i in [1..l] do for j in [1..i-1] do Q[i][j]:=D[i]*D[j]*M0[i][j]; Q[j][i]:=Q[i][j]; od; od; #adding the signs to M^0
	if ForAll(L,x->TransformingPermutations(x,Q)=fail) then Add(L,Q); else Print("no\n"); fi;
od;

p:=3;;
w:=10;;
ct:=MatCharsWreathSymmetricRest(CharacterTable("cyclic",p),w);;
chars:=Filtered(PartitionTuples(w,p),lam->DegreeWrSym(lam,p) mod p<>0);; #height 0 characters
charpos:=List(chars,t->Position(PartitionTuples(w,p),t));;
W:=ct{charpos};;
classes:=Filtered(PartitionTuples(w,p),lam->lam[1]=[]);;
M0:=PDash(p^w*Factorial(w),p)^-1*W*DiagonalMat(List(classes,c->ClassSizeWrSym(c,p)))*TransposedMat(W);; #=M^0 in paper
l:=Size(M0);;
L:=[];;
for core in ScopesCores(p,w) do
	D:=List(chars,x->PSign(p,CoreQuotient2Partition(p,core,x)));
	Q:=MutableCopyMat(M0);
	for i in [1..l] do #adding the signs to M^0
		for j in [1..i-1] do 
			if D[i]<>D[j] then Q[i][j]:=-M0[i][j]; Q[j][i]:=Q[i][j]; fi; 
		od; 
	od; 
	if ForAll(L,x->TransformingPermutations(x,Q)=fail) then Add(L,Q); else Print("no\n"); fi;
od;

p:=2;;
w:=2^4;;
ct:=CharacterTable("symmetric",w);;
char:=PositionsProperty(Irr(ct),c->c[1] mod p<>0);;
part:=Partitions(w){char};;
W:=MutableMatrix(Irr(ct){char});;
d:=Sum([0..LogInt(w,p)],i->Int(w/p^i));; #p-part of (pw)!
M0:=W*DiagonalMat(List([1..NrPartitions(w)],c->SizesCentralizers(ct)[c]^-1*p^(d-Size(Partitions(w)[c]))))*TransposedMat(W);;
l:=Size(M0);;
L:=[];;
for core in ScopesCores(p,w) do
	D:=List(part,c->PSign(p,CoreQuotient2Partition(p,core,[[],c])));
	Q:=NullMat(l,l);
	for i in [1..l] do for j in [1..l] do Q[i][j]:=D[i]*D[j]*M0[i][j]; od; od;
	if ForAll(L,x->TransformingPermutations(x,Q)=fail) then Add(L,Q); else Print("no\n"); fi;
od;
