//alle primitiven Permutationsgruppen vom Grad $<2^{12}$, die weder $2$-transitiv noch vom Typ (A) sind (Satz 8.23)
PG:=PrimitiveGroupProcess([1..4095], func<G|(Transitivity(G) eq 1) and (not IsAffine(G))>); 
while not IsEmpty(PG) do
	G:=Current(PG);
	S:=Stabiliser(G,1); //$G_\omega$
	OrbRep:=OrbitRepresentatives(S); //Bahnen von $G_\omega$
 	for orb in OrbRep do
		if #[x[1] : x in OrbRep | x[1] eq orb[1]] gt 1 then //kommt der Subgrad orb[1] mindestens zweimal vor? 
			b,x:=IsConjugate(G,1,orb[2]);
			o2:=1^(x^(-1)); //ein Element in $\Delta^*$
			//ist ($\Delta\ne\Delta^*$ und) $G_\omega\cap G_{\Delta}\ne G_\omega\cap G_{\Delta^*}$, dann gebe G aus
			if (not IsConjugate(S,orb[2],o2)) and (OrbitKernel(S,Orbit(S,orb[2])) ne OrbitKernel(S,Orbit(S,o2))) then CurrentLabel(PG); end if;
		end if;
	end for;
	Advance(~PG);
end while;
