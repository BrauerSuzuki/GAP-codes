LoadPackage("nconvex"); #this requires some libraries and compiled GAP packages
#We use the fact that every indecomposable G-invariant character of P is a restriction of a generalized character.
#This was proved in my paper "Fusion invariant character of p-groups".

CCConjecture:=function(G,p)
local P,ct,ctP,Rest,A,H,Ind,deg,c,x;
	P:=SylowSubgroup(G,p);
	ct:=CharacterTable(G);
	ctP:=CharacterTable(P);
	Rest:=List(Irr(ct),c->RestrictedClassFunction(c,ctP)); #chi_P for chi in Irr(G)
	A:=List(Rest,r->List(Irr(ctP),l->ScalarProduct(r,l))); #List of multiplicities of constituents
	A:=Set(A,a->a/Gcd(a)); #we may replay a multiple m*chi by chi
	A:=TransposedMat(A);
	H:=SolveEqualitiesAndInequalitiesOverIntergers([],[],A,[1..Size(A)]*0)[2]; #find Z-basis for x with Ax >= 0
	Ind:=H*TransposedMat(A); #compute the indecomposable characters as list of multiplicities
	deg:=List(Irr(ctP),c->c[1]); #multiplicities of the regular character
	return Filtered(Ind,c->ForAny(deg-c,x->x<0)); #return those which are not summands of the regular character
end;

G:=PrimitiveGroup(22,2);
CCConjecture(G,2);
