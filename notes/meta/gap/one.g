# one case:  DID1 DID2 PAIRIDX UEXP  passed via environment-substituted globals
F := GF(27);; z := PrimitiveRoot(F);;
B := Basis(AsVectorSpace(GF(3), F));;
IntCoeffs := function(v) return List(Coefficients(B, v), c -> IntFFE(c)); end;;
Subst := function(w, a, g)
  local ex, res, i;
  ex := LetterRepAssocWord(w); res := One(a);
  for i in ex do
    if   i =  1 then res := res*a;   elif i = -1 then res := res*a^-1;
    elif i =  2 then res := res*g;   elif i = -2 then res := res*g^-1; fi;
  od;
  return res;
end;;
D := SmallGroup(DID1, DID2);;
A := First(NormalSubgroups(D), N -> Size(N) = DID1/3 and IsAbelian(N));;
reps := Filtered(Elements(D), t -> Order(t)=3);;
pairs := [];;
for x in reps do
  if Size(Centralizer(A,x)) = 1 then
    for gg in reps do
      if Subgroup(D,[x,gg]) = D and IsConjugate(D,x,gg) then Add(pairs,[x,gg]); fi;
    od;
  fi;
od;
aut := AutomorphismGroup(D);; orb := []; keep := [];;
for pr in pairs do
  if not pr in orb then
    Add(keep, pr);
    UniteSet(orb, Set(List(Elements(aut), al -> [Image(al,pr[1]), Image(al,pr[2])])));
  fi;
od;
ok := PAIRIDX <= Length(keep);;
if ok then pr := keep[PAIRIDX]; else pr := keep[1]; Print("NOPAIR ",Length(keep),"\n"); fi;
if ok then
drels := RelatorsOfFpGroup(Image(IsomorphismFpGroupByGenerators(D, pr)));;

Fr := FreeGroup("a","b","c","u","g");;
a:=Fr.1;; b:=Fr.2;; c:=Fr.3;; u:=Fr.4;; g:=Fr.5;; gens:=[a,b,c];;
rels := [ a^3,b^3,c^3, Comm(a,b),Comm(a,c),Comm(b,c), u^13, g^3 ];;
for i in [1..3] do
  row := IntCoeffs( BasisVectors(B)[i] * z^2 );
  Add(rels, u*gens[i]*u^-1 * (a^row[1]*b^row[2]*c^row[3])^-1);
od;
Add(rels, g*u*g^-1 * (u^UEXP)^-1);
for w in drels do Add(rels, Subst(w, a, g)); od;
Gam := Fr/rels;;
H := Subgroup(Gam, [Gam.1,Gam.2,Gam.3,Gam.4]);;
sz := Size(Gam);;
Print("D=[",DID1,",",DID2,"] pair=",PAIRIDX," uexp=",UEXP,
      "  |Gamma|=", sz, "  |H_image|=", Size(H),
      "  Hembeds=", Size(H)=351, "\n");
if sz < infinity and Size(H) = 351 then
  dd := Subgroup(Gam, [Gam.1, Gam.5]);
  Print("   |<x,g>| = ", Size(dd), "  target |D| = ", DID1,
        "   *** CANDIDATE WITNESS ***\n");
fi;
fi;
QUIT;
