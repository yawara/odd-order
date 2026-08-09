# Enumerate candidate D = A : C3  (A abelian 3'-group, C3 acting fixed-point-freely),
# together with generating pairs (x,g) of order 3 with <x,g> = D.
FrobeniusCandidates := function(maxorder)
  local res, n, m, i, D, A, cls, x, g, ok, pairs, reps;
  res := [];
  for n in [4..maxorder] do
    if n mod 3 <> 0 then continue; fi;
    m := n/3;
    if m mod 3 = 0 or m = 1 then continue; fi;
    for i in [1..NrSmallGroups(n)] do
      D := SmallGroup(n, i);
      A := First(NormalSubgroups(D), N -> Size(N) = m and IsAbelian(N));
      if A = fail then continue; fi;
      pairs := [];
      reps := Filtered(Elements(D), t -> Order(t) = 3);
      for x in reps do
        if Size(Centralizer(A, x)) <> 1 then continue; fi;
        for g in reps do
          if Subgroup(D, [x,g]) = D and IsConjugate(D, x, g) then
            Add(pairs, [x,g]);
          fi;
        od;
      od;
      if Length(pairs) > 0 then
        Add(res, rec(D := D, id := [n,i], A := A, pairs := pairs));
      fi;
    od;
  od;
  return res;
end;;

SetInfoLevel(InfoWarning,0);
cands := FrobeniusCandidates(60);;
for r in cands do
  Print("D = SmallGroup", r.id, "  |D| = ", Size(r.D),
        "  kernel ", StructureDescription(r.A),
        "  struct ", StructureDescription(r.D),
        "  #(x,g) pairs = ", Length(r.pairs), "\n");
od;
QUIT;
