############################################################
# BG App.C Problem 1 (Peterfalvi): can (B) hold for p = 3 ?
# Reduction: (B) holds <=> exists G >= H = P:U and g in N_G(U) with |g| = 3
#            such that <x,g> is a finite Frobenius group with abelian
#            3'-kernel and complement of order 3 (x in P of order 3).
############################################################

IsGoodPair := function(D, x)
  local n, m, A;
  n := Size(D);
  if n mod 3 <> 0 then return false; fi;
  m := n/3;
  if m mod 3 = 0 then return false; fi;
  if m = 1 then return false; fi;
  for A in NormalSubgroups(D) do
    if Size(A) = m and IsAbelian(A) and Size(Centralizer(A, x)) = 1 then
      return true;
    fi;
  od;
  return false;
end;

FindWitness := function(G, U, x)
  local N, g, D;
  N := Normalizer(G, U);
  if Size(N) mod 3 <> 0 then return fail; fi;
  for g in N do
    if Order(g) = 3 then
      D := Subgroup(G, [x, g]);
      if IsGoodPair(D, x) then return g; fi;
    fi;
  od;
  return fail;
end;

# Borel-like pairs (P,U): P elem abelian of order p^q inside a Sylow p-subgroup,
# U of order (p^q-1)/(p-1) in N_G(P) acting fixed-point-freely on P.
FindBorels := function(G, p, q)
  local pq, u, S, subs, res, P, N, U, seen, cP;
  pq := p^q;
  u  := (pq-1)/(p-1);
  S  := SylowSubgroup(G, p);
  if Size(S) mod pq <> 0 then return []; fi;
  if Size(S) = pq then subs := [S];
  else subs := Filtered(List(ConjugacyClassesSubgroups(S), Representative),
                        A -> Size(A) = pq and IsElementaryAbelian(A));
  fi;
  res := []; seen := [];
  for P in subs do
    if not IsElementaryAbelian(P) then continue; fi;
    N := Normalizer(G, P);
    if Size(N) mod u <> 0 then continue; fi;
    U := SylowSubgroup(N, Factors(u)[1]);
    if Size(U) <> u then
      U := First(List(ConjugacyClassesSubgroups(N), Representative),
                 V -> Size(V) = u and IsCyclic(V));
      if U = fail then continue; fi;
    fi;
    if not IsCyclic(U) then continue; fi;
    if Size(Centralizer(P, U)) <> 1 then continue; fi;
    Add(res, rec(P := P, U := U));
  od;
  return res;
end;

TestGroup := function(name, G)
  local bs, b, g, P, U, x;
  Print("=== ", name, "   |G| = ", Size(G), "\n");
  bs := FindBorels(G, 3, 3);
  if Length(bs) = 0 then Print("    no H = C3^3 : C13 inside\n"); return false; fi;
  for b in bs do
    P := b.P; U := b.U;
    x := First(Elements(P), t -> Order(t) = 3);
    Print("    H found;  |N_G(U)| = ", Size(Normalizer(G, U)), " -> ");
    g := FindWitness(G, U, x);
    if g = fail then Print("no witness\n");
    else Print("*** WITNESS *** g = ", g, "\n"); return true; fi;
  od;
  return false;
end;
