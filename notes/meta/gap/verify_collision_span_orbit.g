# collision-span for q = 29 using Frobenius-orbit hashing.
#   D(p^3) = D(p)^3, so canon(D(p)) := the orbit {D(p)^{3^j}} identifies collisions up to
#   Frobenius: if canon(D(p)) = canon(D(r)) then D(p) = D(r)^{3^k} = D(r^{3^k}) for some k,
#   i.e. (p, r^{3^k}) is a genuine collision.  The birthday space shrinks by a factor q.
# Also uses T = {(u + u^-1)^2 : u^2 <> 1} to generate Paley-set elements without square tests.
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

RunOrbit := function(q, nsamples)
  local Q, n, NN, F, one, IsInU, frob, es, e, E, E2, dict, u, p, pm, i, j, k, val, orb, canon,
        lst, entry, r, rk, delta, z, S, T3, rows, B3, done, coll;
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
      p := (u + u^-1)^2; pm := (u - u^-1)^2;
      if IsZero(p) or IsZero(pm) then continue; fi;
      val := p^E - pm^E;
      if IsZero(val) then continue; fi;
      # canonical representative of the Frobenius orbit of val
      orb := []; canon := val;
      for j in [1..q] do Add(orb, canon); canon := canon^3; od;
      canon := Minimum(orb);
      lst := LookupDictionary(dict, canon);
      if lst = fail then AddDictionary(dict, canon, [[p, val]]);
      else
        for entry in lst do
          # find k with D(r)^{3^k} = val, then r^{3^k} collides with p
          r := entry[1]; rk := entry[2];
          k := 0;
          while k < q and rk <> val do rk := rk^3; r := r^3; k := k + 1; od;
          if rk <> val then continue; fi;
          if r = p then continue; fi;
          delta := p^E - r^E;
          if IsZero(delta) or not IsInU(delta) then continue; fi;
          coll := coll + 1;
          S := ((r - one)^E2 - r^E2) * (delta^-1)^E;
          T3 := S;
          for j in [1..q] do Add(rows, Coefficients(B3, T3)); T3 := T3^3; od;
          if RankMat(rows) = q then done := true; fi;
        od;
        Add(lst, [p, val]);
      fi;
      if done then break; fi;
    od;
    Print("RESULT q=", q, " e=", e, " collisions=", coll, " samples=", i,
          " rank=", RankMat(rows), " of ", q, " full=", RankMat(rows) = q, "\n");
  od;
end;;

RunOrbit(31, 12000000);

QUIT;
