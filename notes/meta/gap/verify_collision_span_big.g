# collision-span for larger q, using two structural speed-ups discovered 2026-08-11:
#  (i)  T = {p : p, p-1 in U} is exactly {(u + u^-1)^2 : u^2 <> 1}  (Lemma B's parametrisation:
#       (u-u^-1)^2 and (u+u^-1)^2 = (u-u^-1)^2 + 1 are both squares) -- so elements of T can be
#       GENERATED with no square tests, halving the cost per sample.
#  (ii) the S's are Frobenius-closed:  S(p^3, r^3) = S(p,r)^3, because p^3 - 1 = (p-1)^3 and
#       cubing is additive.  So ONE usable collision contributes its whole Frobenius orbit
#       {S, S^3, ..., S^{3^(q-1)}}, and the span is a Frobenius-stable subspace.
SizeScreen([512, 24]);;
CubeRoots := function(n)
  local fac, mods, rootsList, pp, p, a, m, g, roots, res, newres, i, x, r, M;
  fac := Collected(Factors(n)); mods := []; rootsList := [];
  for pp in fac do
    p := pp[1]; a := pp[2]; m := p^a;
    if p = 3 then roots := Filtered([0..m-1], k -> PowerMod(k, 3, m) = 1);
    elif (p-1) mod 3 <> 0 then roots := [1];
    else g := PrimitiveRootMod(m); roots := Set(List([0..2], k -> PowerMod(g, k*Phi(m)/3, m))); fi;
    Add(mods, m); Add(rootsList, roots);
  od;
  res := [0]; M := 1;
  for i in [1..Length(mods)] do
    newres := [];
    for x in res do for r in rootsList[i] do Add(newres, ChineseRem([M, mods[i]], [x, r])); od; od;
    M := M * mods[i]; res := Set(newres);
  od;
  return Set(List(res, x -> x mod n));
end;;

RunBig := function(q, nsamples)
  local Q, n, NN, F, one, IsInU, frob, es, e, E, E2, dict, u, p, pm, i, r, delta, z, S, T3,
        rows, B3, j, val, lst, done, coll;
  Q := 3^q; n := (Q-1)/2; NN := Q-1; F := GF(Q); one := One(F);
  IsInU := x -> not IsZero(x) and x^n = one;
  frob := Set(List([0..q-1], j -> 3^j mod n));
  es := Filtered(CubeRoots(n), k -> k <> 1 and not (k in frob));
  Print("=== q = ", q, "  exotic exponents: ", Length(es), "\n");
  B3 := Basis(AsVectorSpace(GF(3), F));
  for e in es do
    if IsOddInt(e) then E := e; else E := e + n; fi;
    E2 := (E*E) mod NN;
    dict := NewDictionary(one, true);
    rows := []; coll := 0; done := false;
    for i in [1..nsamples] do
      u := Random(F);
      if IsZero(u) then continue; fi;
      p := (u + u^-1)^2;                  # p in T automatically; p - 1 = (u - u^-1)^2
      pm := (u - u^-1)^2;
      if IsZero(p) or IsZero(pm) then continue; fi;
      val := p^E - pm^E;                  # D_E(p)
      lst := LookupDictionary(dict, val);
      if lst = fail then AddDictionary(dict, val, [p]);
      else
        for r in lst do
          if r = p then continue; fi;
          delta := p^E - r^E;
          if IsZero(delta) or not IsInU(delta) then continue; fi;
          coll := coll + 1;
          S := ((r - one)^E2 - r^E2) * (delta^-1)^E;    # S(r,p) = K(r) * delta^{-E}
          T3 := S;
          for j in [1..q] do Add(rows, Coefficients(B3, T3)); T3 := T3^3; od;
          if RankMat(rows) = q then done := true; fi;
        od;
        Add(lst, p);
      fi;
      if done then break; fi;
    od;
    Print("RESULT q=", q, " e=", e, " collisions=", coll, " samples=", i,
          " rank=", RankMat(rows), " of ", q, " full=", RankMat(rows) = q, "\n");
  od;
end;;

RunBig(13, 200000);
RunBig(19, 2000000);
RunBig(29, 60000000);
QUIT;
