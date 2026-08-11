# TRACE OBSTRUCTION (ChatGPT 2026-08-11, verified by us):
#   In a witness, EVERY collision has Tr(S) = 0 where S = K_E(p) * delta^{-E}.
#   Hence ONE collision with Tr(S) <> 0 already contradicts hypothesis (B).
# This replaces the rank/spanning computation by a single trace evaluation.
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

RunTrace := function(q, nsamples)
  local Q, n, NN, F, one, IsInU, Tr, frob, es, e, E, E2, dict, u, p, pm, i, j, k, val, orb, canon,
        lst, entry, r, rk, delta, S, t, coll, done;
  Q := 3^q; n := (Q-1)/2; NN := Q-1; F := GF(Q); one := One(F);
  IsInU := x -> not IsZero(x) and x^n = one;
  Tr := function(x) local s, y, j; s := Zero(F); y := x;
    for j in [1..q] do s := s + y; y := y^3; od; return s; end;
  frob := Set(List([0..q-1], j -> 3^j mod n));
  es := Filtered(CubeRoots(n), k -> k <> 1 and not (k in frob));
  Print("=== q = ", q, "  exotic exponents: ", Length(es), "\n");
  for e in es do
    if IsOddInt(e) then E := e; else E := e + n; fi;
    E2 := (E*E) mod NN;
    dict := NewDictionary(one, true);
    coll := 0; done := false;
    for i in [1..nsamples] do
      u := Random(F);
      if IsZero(u) then continue; fi;
      p := (u + u^-1)^2; pm := (u - u^-1)^2;
      if IsZero(p) or IsZero(pm) then continue; fi;
      val := p^E - pm^E;
      if IsZero(val) then continue; fi;
      orb := []; canon := val;
      for j in [1..q] do Add(orb, canon); canon := canon^3; od;
      canon := Minimum(orb);
      lst := LookupDictionary(dict, canon);
      if lst = fail then AddDictionary(dict, canon, [[p, val]]);
      else
        for entry in lst do
          r := entry[1]; rk := entry[2]; k := 0;
          while k < q and rk <> val do rk := rk^3; r := r^3; k := k + 1; od;
          if rk <> val or r = p then continue; fi;
          delta := p^E - r^E;
          if IsZero(delta) or not IsInU(delta) then continue; fi;
          coll := coll + 1;
          S := ((r - one)^E2 - r^E2) * (delta^-1)^E;
          t := Tr(S);
          if not IsZero(t) then
            Print("RESULT q=", q, " e=", e, " DECISIVE: collision #", coll, " has Tr(S)=", t,
                  " (samples=", i, ")\n");
            done := true; break;
          fi;
        od;
        Add(lst, [p, val]);
      fi;
      if done then break; fi;
    od;
    if not done then
      Print("RESULT q=", q, " e=", e, " no decisive collision in ", nsamples,
            " samples (collisions seen: ", coll, ")\n");
    fi;
  od;
end;;

RunTrace(7, 100000);
RunTrace(13, 200000);
RunTrace(19, 2000000);
RunTrace(29, 20000000);
QUIT;
