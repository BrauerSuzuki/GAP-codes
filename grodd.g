InfoSimpleOrder:=NewInfoClass("InfoSimpleOrder");;
SetInfoLevel(InfoSimpleOrder,1); #Wie viel Info soll ausgegeben werden?

IsSquareFree:=function(n)
	return PrimeDivisors(n)=FactorsInt(n);
end;

SubdegreeCheck:=function(p,d,r,norm)
#Eingabe: $\N_G(P)\le H$ mit $|H|=r$, $|G:H|=d$; falls norm = true, dann ist $H=\N_G(P)$
#Ausgabe: false, falls wie zeigen können, dass $H$ nicht maximal in $G$ ist; sonst true
local parts,i,part,l;
	if IsPrimeInt(d) then return false; fi; #Satz 7.4
	if IsPrimePowerInt(r) then return false; fi; #Lemma 10.22
	#bestimme mögliche Subgrade mit Hilfe von Satz 10.26
	parts:=Filtered(DivisorsInt(r),i->(i mod p=0) and (not i in [3,5,9,17,257,65537]) and ((not IsSquareFree(i)) or ForAll(PrimeDivisors(r),j->(i*Phi(i)) mod j=0)));
	if IsEmpty(parts) then return false; fi;
	#durchlaufe mögliche Konstellationen der Subgrade
	for part in RestrictedPartitions((d-1)/2,parts) do
		Sort(part);
		l:=Size(part);
		if ForAny(part,i->Gcd(i,part[l])=1) then continue; fi; #Satz 8.10
		if ForAny([2..l],i->part[i]>(part[1]-1)*part[i-1]) then continue; fi; #Satz 8.9
		if IsPrime(part[1]) and (r mod (part[1]^2)=0) then continue; fi; #Satz 8.20
		if IsPrime(part[l]) and (part[l]*(part[l]-1)) mod r<>0 then continue; fi; #Satz 8.22
		if norm and (r mod (p^2)=0) and ForAll(part,i->i mod (p^2)<>0) then continue; fi; #Lemma 10.28
		if norm and (p=3) and (Valuation(r,3)=3) and ForAll(part,i->i mod (3^3)<>0) then continue; fi; #Lemma 10.28
		if norm and (p=3) and (Valuation(r,3)=4) and ((r*d) mod 13<>0) and ForAll(part,i->i mod (3^4)<>0) then continue; fi; #Lemma 10.28
		if 25 in part and PrimeDivisors(r/25)<>[3] then continue; fi; #Satz 10.26
		if 27 in part and PrimeDivisors(r)<>[3,13] then continue; fi; #Satz 10.26
		if ForAny(part,i->IsSquareFree(i) and Gcd(i,Phi(i))=1 and r mod (i^2)=0) then continue; fi; #Satz 10.26
		#if l=1 and ForAny(PrimeDivisors(d),i->i mod 4=1 and r mod i<>0) then continue; fi; #Lemma A.16
		Info(InfoSimpleOrder,4,"p = ",p," d = ",d," = ",StringPP(d)," r = ",r," = ",StringPP(r)," subdegrees = ",part);
		return true;
	od;
	return false;
end;

ChainCheck:=function(p,d,r,norm)
#Eingabe: Wie in SubdegreeCheck
#Ausgabe: false, falls wir zeigen können, dass $H$ in einer maximalen Untergruppe vom Index $<100$ liegt; sonst true
local l,x,M;
	if d<100 then return false; fi;
	if SubdegreeCheck(p,d,r,norm) then 
		Info(InfoSimpleOrder,3,"p = ",p," r = ",r," = ",StringPP(r)," is maximal");
		return true; 
	fi;
	M:=Filtered(DivisorsInt(d),x->IsPrimePowerInt(x) and x<d and x mod p=1);
	if IsEmpty(M) then return false; fi;
	return ForAny(M,l->ChainCheck(p,d/l,r*l,false));
end;

IsSimpleGroupOrder:=function(n)
#Eingabe: Eine ungerade Zahl $n$
#Ausgabe: true, falls es eine einfache Gruppe der Ordnung $n$ gibt
#false, falls es keine einfache Gruppe der Ordnung $n$ gibt
#unknown, falls wir nichts beweisen können
local p,mult,m,d,i,x,q,ordersp,revprime,nr,j,r,L,min,pdiff;
	if n=1 then return false; fi;
	if IsPrime(n) then return true; fi; #einfache Gruppe von Primzahlordnung
	ordersp:=[];
	revprime:=Reversed(PrimeDivisors(n)); #umgekehrte Reihenfolge, da schneller
	for nr in [1..Size(revprime)] do
		p:=revprime[nr];
		ordersp[nr]:=[]; #mögliche Normalisatorordnungen
		mult:=Valuation(n,p); #Vielfachheit von $p$ in $n$
		m:=n/p^mult;
		for d in DivisorsInt(m) do
			if d>100 and d mod p=1 #Sylow + Satz 10.30
				and 
				(Gcd(m/d,Product([1..mult],i->p^i-1))>1 or (mult>2 and Gcd(d,Product([2..mult-1],i->p^i-1))>1)) #Lemma 10.18
				and
				ChainCheck(p,d,n/d,true) #Liegt $\N_G(P)$ in einer maximalen Untergruppe mit Index $>100$?
				and
				((d mod (p^2)=1) or mult=1 or ForAny(DivisorsInt(m),i->i>1 and i mod p=1 and m/i>100)) #Existiert~$\N_G(P\cap Q)$?
			then Add(ordersp[nr],n/d); fi;
		od;
		if ordersp[nr]=[] then return false; fi;
	od;
	for nr in [1..Size(revprime)] do #vergleiche verschiedene Primteiler
		if Size(ordersp[nr])>1 then continue; fi; #Analyse zu komplex
		d:=ordersp[nr][1];
		pdiff:=Filtered([1..Size(revprime)],i->i<>nr and d mod (revprime[i]^Valuation(n,revprime[i]))=0);
		for i in pdiff do
			min:=Product(PrimeDivisors(d),q->q^Minimum(Filtered( [0..Valuation(d,q)],j->(q^(Valuation(d,q)-j)) mod revprime[i]=1)));
			ordersp[i]:=Filtered(ordersp[i],r->r mod min=0);
			if ordersp[i]=[] then return false; fi;
		od;
	od;
	L:=List([1..Size(revprime)],i->[revprime[i],ordersp[i]]);
	Info(InfoSimpleOrder,2,"n = ",n," = ",StringPP(n)," ",L);
	return "unknown"; #verbleibende Ordnungen
end;

L:=Filtered([1..10^6],n->IsOddInt(n) and IsSimpleGroupOrder(n)="unknown");

AllSubdegrees:=function(p,d,r,norm)
#Wie SubdegreeCheck nur werden diesmal alle möglichen Subgrade ausgegeben
local parts,i,part,l;
	if IsPrimeInt(d) then return false; fi;
	if IsPrimePowerInt(r) then return false; fi;
	parts:=Filtered(DivisorsInt(r),i->(i mod p=0) and (not i in [3,5,9,17,257,65537]) and (not IsSquareFree(i) or ForAll(PrimeDivisors(r),j->(i*Phi(i)) mod j=0)));
	if IsEmpty(parts) then return false; fi;
	for part in RestrictedPartitions((d-1)/2,parts) do
		Sort(part);
		l:=Size(part);
		if ForAny(part,i->Gcd(i,part[l])=1) then continue; fi;
		if ForAny([2..l],i->part[i]>(part[1]-1)*part[i-1]) then continue; fi;
		if IsPrime(part[1]) and (r mod (part[1]^2)=0) then continue; fi;
		if IsPrime(part[l]) and (part[l]*(part[l]-1)) mod r<>0 then continue; fi;
		if norm and (r mod (p^2)=0) and ForAll(part,i->i mod (p^2)<>0) then continue; fi;
		if norm and (p=3) and (Valuation(r,3)=3) and ForAll(part,i->i mod (3^3)<>0) then continue; fi;
		if norm and (p=3) and (Valuation(r,3)=4) and ((r*d) mod 13<>0) and ForAll(part,i->i mod (3^4)<>0) then continue; fi;
		if 25 in part and PrimeDivisors(r/25)<>[3] then continue; fi;
		if 27 in part and PrimeDivisors(r)<>[3,13] then continue; fi;
		if ForAny(part,i->IsSquareFree(i) and Gcd(i,Phi(i))=1 and r mod (i^2)=0) then continue; fi;
		#if l=1 and ForAny(PrimeDivisors(d),i->i mod 4=1 and r mod i<>0) then continue; fi; #Lemma A.16
		if not 15 in part then Print("p = ",p," d = ",d," r = ",r," subdegrees = ",part,"\n"); fi;
	od;
end;
