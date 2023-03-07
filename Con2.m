//tested on Magma 2.23-10
//construct 2-blocks of weight 3 and cores (1) and (2,1)
G:=SymmetricGroup(7);
PIM:=ProjectiveIndecomposableModules(G,FiniteField(2));
AbsoluteCartanMatrix(G,FiniteField(2));
A0:=BasicAlgebraOfBlockAlgebra([PIM[1],PIM[4],PIM[5]]);

G:=SymmetricGroup(9);
PIM:=ProjectiveIndecomposableModules(G,FiniteField(2));
AbsoluteCartanMatrix(G,FiniteField(2));
A1:=BasicAlgebraOfBlockAlgebra([PIM[2],PIM[6],PIM[8]]);
IsIsomorphic(A0,A1); //basic algebras are isomorphic
