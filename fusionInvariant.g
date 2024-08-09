#The following code checks the conjecture of Cantarero-Combariza for a fusion system
#on a Sylow p-subgroup P of a finite group G. We use the fact that every 
#G-invariant character of P is a restriction of a generalized character of G.
#This was proved in my paper "Fusion invariant character of p-groups".

LoadPackage("nconvex",false); #this requires some libraries and compiled GAP packages
#For documentaion see https://homalg-project.github.io/NConvex/doc/chap6_mj.html#X84237872798DB501

CCConjecture:=function(G,p)
local P,ct,ctP,Rest,A,H,Ind,deg,c,x;
	P:=SylowSubgroup(G,p);
	ct:=CharacterTable(G);
	ctP:=CharacterTable(P);
	Rest:=Set(Irr(ct), c->RestrictedClassFunction(c,ctP)); #chi_P for chi in Irr(G)
	A:=MatScalarProducts(Rest,Irr(ctP));
	H:=SolveEqualitiesAndInequalitiesOverIntergers([],[],A,[1..Size(A)]*0)[2]; #find Hilbert basis of {x:Ax >= 0}
	Ind:=H*TransposedMat(A); #compute the indecomposable characters as lists of multiplicities
	deg:=List(Irr(ctP), c->c[1]); #multiplicities of the regular character
	return ForAll(Ind, c->ForAll(deg-c, x->x>=0)); 
end;

G:=PrimitiveGroup(22,2);
CCConjecture(G,2);

#Just for the reviewer: Here are the deg and Ind variables in the given example:
#deg = [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 8, 8 ]
#Ind =
#[ [  0,  0,  0,  3,  0,  3,  2,  0,  1,  0,  1,  0,  0,  0,  1,  1,  3,  1,  3,  1,  2,  3,  2,  1,  3,  0,  3,  1,  4,  3,  4,  4,  7,  8 ],
#  [  0,  0,  0,  1,  0,  1,  1,  0,  1,  0,  0,  0,  0,  1,  1,  0,  1,  0,  1,  1,  1,  1,  1,  0,  1,  0,  1,  0,  1,  1,  2,  1,  2,  3 ],
#  [  0,  0,  0,  0,  0,  0,  1,  0,  1,  1,  0,  0,  0,  2,  1,  0,  0,  0,  0,  2,  1,  0,  1,  0,  0,  1,  0,  0,  0,  1,  2,  0,  1,  2 ],
#  [  0,  0,  0,  2,  1,  1,  1,  0,  1,  0,  0,  0,  0,  0,  2,  1,  2,  1,  2,  1,  1,  2,  2,  1,  2,  0,  1,  1,  3,  2,  3,  2,  5,  5 ],
#  [  0,  0,  1,  2,  0,  2,  1,  0,  1,  0,  1,  0,  0,  0,  0,  1,  2,  1,  2,  1,  2,  2,  1,  1,  2,  0,  2,  1,  3,  2,  3,  3,  5,  6 ],
#  [  0,  0,  0,  1,  1,  0,  1,  0,  1,  1,  0,  0,  0,  1,  2,  1,  1,  1,  1,  2,  1,  1,  2,  1,  1,  1,  0,  1,  2,  2,  3,  1,  4,  4 ],
#  [  0,  0,  1,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  1,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  1 ],
#  [  0,  1,  0,  1,  0,  2,  1,  0,  0,  0,  1,  0,  0,  0,  0,  0,  2,  0,  1,  0,  1,  1,  1,  0,  1,  0,  2,  0,  2,  1,  1,  2,  3,  3 ],
#  [  0,  0,  3,  2,  1,  1,  0,  0,  2,  0,  1,  0,  0,  0,  0,  2,  2,  2,  2,  2,  3,  2,  1,  2,  2,  0,  1,  2,  4,  2,  4,  3,  6,  7 ],
#  [  0,  1,  0,  0,  0,  1,  1,  0,  0,  1,  1,  0,  0,  1,  0,  0,  1,  0,  0,  1,  1,  0,  1,  0,  0,  1,  1,  0,  1,  1,  1,  1,  2,  2 ],
#  [  0,  1,  2,  1,  1,  1,  0,  0,  1,  0,  1,  0,  0,  0,  0,  1,  2,  1,  1,  1,  2,  1,  1,  1,  1,  0,  1,  1,  3,  1,  2,  2,  4,  4 ],
#  [  0,  0,  0,  2,  2,  0,  1,  0,  1,  1,  0,  0,  0,  0,  3,  2,  2,  2,  2,  2,  1,  2,  3,  2,  2,  1,  0,  2,  4,  3,  4,  2,  7,  6 ],
#  [  0,  0,  1,  1,  1,  0,  0,  0,  1,  0,  0,  0,  0,  0,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  0,  0,  1,  2,  1,  2,  1,  3,  3 ],
#  [  0,  2,  1,  0,  1,  1,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  2,  0,  0,  0,  1,  0,  1,  0,  0,  0,  1,  0,  2,  0,  0,  1,  2,  1 ],
#  [  0,  1,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  1,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  1,  0,  0,  0,  1,  0 ],
#  [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  1,  0,  1,  0,  1,  1,  1,  0,  1,  2,  1 ],
#  [  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  1,  0,  0,  1,  0,  1,  0,  0,  1,  1,  1,  1,  2 ],
#  [  0,  0,  0,  1,  0,  1,  1,  0,  0,  1,  1,  0,  0,  0,  0,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  2,  2,  2,  2,  4,  4 ],
#  [  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#  [  0,  0,  0,  0,  0,  0,  1,  0,  0,  2,  1,  0,  0,  1,  0,  1,  0,  1,  0,  2,  1,  0,  1,  1,  0,  2,  0,  1,  1,  2,  2,  1,  3,  3 ],
#  [  0,  0,  2,  1,  1,  0,  0,  0,  1,  1,  1,  0,  0,  0,  0,  2,  1,  2,  1,  2,  2,  1,  1,  2,  1,  1,  0,  2,  3,  2,  3,  2,  5,  5 ],
#  [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#  [  0,  1,  1,  0,  1,  0,  0,  0,  0,  1,  1,  0,  0,  0,  0,  1,  1,  1,  0,  1,  1,  0,  1,  1,  0,  1,  0,  1,  2,  1,  1,  1,  3,  2 ],
#  [  0,  0,  0,  1,  1,  0,  1,  0,  0,  2,  1,  0,  0,  0,  1,  2,  1,  2,  1,  2,  1,  1,  2,  2,  1,  2,  0,  2,  3,  3,  3,  2,  6,  5 ],
#  [  0,  0,  1,  1,  1,  0,  1,  0,  0,  3,  2,  0,  0,  0,  0,  3,  1,  3,  1,  3,  2,  1,  2,  3,  1,  3,  0,  3,  4,  4,  4,  3,  8,  7 ] ]


