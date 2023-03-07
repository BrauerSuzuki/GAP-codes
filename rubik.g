#Mit Abbildung A.2 lassen sich die Erzeuger der Zauberwürfelgruppe leicht angeben. 
#Siehe auch http://www.gap-system.org/Doc/Examples/rubik.html

G:=Group(
( 1, 3, 8, 6)( 2, 5, 7, 4)( 9,33,25,17)(10,34,26,18)(11,35,27,19),
( 9,11,16,14)(10,13,15,12)( 1,17,41,40)( 4,20,44,37)( 6,22,46,35),
(17,19,24,22)(18,21,23,20)( 6,25,43,16)( 7,28,42,13)( 8,30,41,11),
(25,27,32,30)(26,29,31,28)( 3,38,43,19)( 5,36,45,21)( 8,33,48,24),
(33,35,40,38)(34,37,39,36)( 3, 9,46,32)( 2,12,47,29)( 1,14,48,27),
(41,43,48,46)(42,45,47,44)(14,22,30,38)(15,23,31,39)(16,24,32,40)); 

#Die Symmetriegruppe des Würfels wird von $d_4$ und $sd_3$ erzeugt (Notation aus Beweis von Satz 11.3):
S:=Group(
(1,27,48,14)(2,29,47,12)(3,32,46,9)(4,26,45,15)(5,31,44,10)(6,25,43,16)
(7,28,42,13)(8,30,41,11)(17,19,24,22)(18,21,23,20)(33,38,40,35)(34,36,
39,37),
(1,14,38,43,25,17)(2,15,36,42,26,20)(3,16,33,41,27,22)(4,12,39,45,28,
18)(5,13,34,44,29,23)(6,9,40,48,30,19)(7,10,37,47,31,21)(8,11,35,46,
32,24));

Sum(S,x->Size(Centralizer(G,x)))/Size(S); #Burnsides Lemma
