#The following code checks the conjecture of Cantarero-Combariza for a fusion system
#on a Sylow p-subgroup P of a finite group G. We use the fact that every 
#G-invariant character of P is a restriction of a generalized character of G.
#This was proved in my paper "Fusion invariant character of p-groups".

LoadPackage("nconvex"); #this requires some libraries and compiled GAP packages
#For documentaion see https://homalg-project.github.io/NConvex/doc/chap6_mj.html#X84237872798DB501

CCConjecture:=function(G,p)
local P,ct,ctP,Rest,A,H,Ind,deg,c,x;
	P:=SylowSubgroup(G,p);
	ct:=CharacterTable(G);
	ctP:=CharacterTable(P);
	Rest:=List(Irr(ct), c->RestrictedClassFunction(c,ctP)); #chi_P for chi in Irr(G)
	A:=List(Rest, r->List(Irr(ctP), l->ScalarProduct(r,l))); #List of multiplicities of constituents
	A:=TransposedMat(A);
	H:=SolveEqualitiesAndInequalitiesOverIntergers([],[],A,[1..Size(A)]*0)[2]; #find Hilbert basis of {x:Ax >= 0}
	Ind:=H*TransposedMat(A); #compute the indecomposable characters as lists of multiplicities
	deg:=List(Irr(ctP), c->c[1]); #multiplicities of the regular character
	return ForAll(Ind, c->ForAll(deg-c, x->x>=0)); 
end;

G:=PrimitiveGroup(22,2);
CCConjecture(G,2);
