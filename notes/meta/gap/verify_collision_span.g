# INDEPENDENT verification of the "collision-span" obstruction (ChatGPT 2026-08-11, verified by us).
#
# Setup: a(t), b(t) = a(t)^g, d(t) = a(t)^{g^2} are the three layers; R(v) reads
#   d(t^{E^2}) b(t^E) a(t) = 1   (t in U),  E = odd lift of e mod 3^q - 1.
# (1)  d(r) = a(-r^E) b(-r^{E^2}),   d(-r) = d(r)^{-1} = b(r^{E^2}) a(r^E)      (r in U)
# (2)  d(z) = a(-p^E z^E) b(K(p) z^{E^2}) a((p-1)^E z^E)   for p in T, z in U,
#      where T = {p in U : p-1 in U}, K(p) = (p-1)^{E^2} - p^{E^2}
# (3)  a collision D(p) = D(r) (D(p) = p^E - (p-1)^E), delta = r^E - p^E, gives
#      b(K(r) z^{E^2}) = b(K(p) z^{E^2})^{a(-delta z^E)}
# (4)  if delta in U, take z = (delta^{-1})^{E^2}: then delta z^E = 1 and
#      b(S(p,r))^{a(-1)} = b(T(p,r)),  S(p,r) = K(p) z^{E^2}.
# CRITERION: if the S(p,r) span F over F_3 then B^{a(-1)} <= B, so a(-1) normalizes B;
# conjugating by U gives all a(-u^{-1}), which span A, so A <= N_G(B), so N = AB is a
# finite 3-group -- contradicting Theorem 2 (N perfect, nontrivial).
#
# This script searches for collisions by random sampling and reports the F_3-rank of the S's.

SizeScreen([512, 24]);;
CubeRoots := function(n)
  local fac, mods, rootsList, pp, p, a, m, g, roots, res, newres, i, x, r, M;
  fac := Collected(Factors(n));
  mods := []; rootsList := [];
  for pp in fac do
    p := pp[1]; a := pp[2]; m := p^a;
    if p = 3 then roots := Filtered([0..m-1], k -> PowerMod(k, 3, m) = 1);
    elif (p-1) mod 3 <> 0 then roots := [1];
    else g := PrimitiveRootMod(m);
         roots := Set(List([0..2], k -> PowerMod(g, k*Phi(m)/3, m)));
    fi;
    Add(mods, m); Add(rootsList, roots);
  od;
  res := [0]; M := 1;
  for i in [1..Length(mods)] do
    newres := [];
    for x in res do for r in rootsList[i] do
      Add(newres, ChineseRem([M, mods[i]], [x, r]));
    od; od;
    M := M * mods[i]; res := Set(newres);
  od;
  return Set(List(res, x -> x mod n));
end;;

RunQ := function(q, nsamples)
  local Q, n, NN, F, one, IsInU, frob, es, e, E, E2, D, K, dict, p, r, i, coll,
        delta, z, S, rows, B3, rank, tries, found, val, lst, Ssets;
  Q := 3^q; n := (Q-1)/2; NN := Q-1; F := GF(Q); one := One(F);
  IsInU := x -> not IsZero(x) and x^n = one;
  frob := Set(List([0..q-1], j -> 3^j mod n));
  es := Filtered(CubeRoots(n), k -> k <> 1 and not (k in frob));
  Print("=== q = ", q, "  Q = ", Q, "  n = ", n, "  exotic exponents: ", Length(es), "\n");
  B3 := Basis(AsVectorSpace(GF(3), F));
  for e in es do
    if IsOddInt(e) then E := e; else E := e + n; fi;
    if PowerMod(E, 3, NN) <> 1 then
      Print("  e = ", e, ": ODD LIFT FAILS E^3 <> 1 mod Q-1 -- ABORT\n"); continue;
    fi;
    E2 := (E*E) mod NN;
    D := p -> p^E - (p-one)^E;
    K := p -> (p-one)^E2 - p^E2;
    dict := NewDictionary(one, true);
    rows := []; coll := 0;
    for i in [1..nsamples] do
      p := Random(F);
      if IsZero(p) or not IsInU(p) then continue; fi;
      if IsZero(p-one) or not IsInU(p-one) then continue; fi;
      val := D(p);
      lst := LookupDictionary(dict, val);
      if lst = fail then
        AddDictionary(dict, val, [p]);
      else
        for r in lst do
          delta := p^E - r^E;               # r plays the earlier role, p the new one
          if IsZero(delta) or not IsInU(delta) then continue; fi;
          coll := coll + 1;
          z := (delta^-1)^E2;
          S := K(r) * z^E2;                 # S(r,p) with the collision pair (r,p)
          Add(rows, Coefficients(B3, S));
        od;
        Add(lst, p);
      fi;
      if Length(rows) >= 3*q and RankMat(rows) = q then break; fi;
    od;
    if Length(rows) = 0 then rank := 0; else rank := RankMat(rows); fi;
    Print("RESULT q=", q, " e=", e, " rank=", rank, " of ", q, " full=", rank = q, "\n");
  od;
end;;

RunQ(19, 4000000);
QUIT;
