# Ito-covering evidence at q = 7, 13, 19 (sampled), plus the density of the core set
#   Z = { z : z, z-1, z^e - 1 all nonzero squares }
# to which the first two conditions of the covering reduce.
CubeRoots := function(n)
  local fac, mods, rootsList, pp, p, a, m, g, roots, res, newres, i, x, r, M;
  fac := Collected(Factors(n));
  mods := []; rootsList := [];
  for pp in fac do
    p := pp[1]; a := pp[2]; m := p^a;
    if p = 3 then
      roots := Filtered([0..m-1], k -> PowerMod(k, 3, m) = 1);
    elif (p-1) mod 3 <> 0 then
      roots := [1];
    else
      g := PrimitiveRootMod(m);
      roots := Set(List([0..2], k -> PowerMod(g, k*Phi(m)/3, m)));
    fi;
    Add(mods, m); Add(rootsList, roots);
  od;
  res := [0]; M := 1;
  for i in [1..Length(mods)] do
    newres := [];
    for x in res do
      for r in rootsList[i] do
        Add(newres, ChineseRem([M, mods[i]], [x, r]));
      od;
    od;
    M := M * mods[i];
    res := Set(newres);
  od;
  return Set(List(res, x -> x mod n));
end;;

RunOne := function(q)
  local Q, n, F, one, IsInU, frob, es, e, e2, hit, trials, i, z, f, fails, used,
        samples, b, a, found, k, a1, r1, r2;
  Q := 3^q; n := (Q-1)/2; F := GF(Q); one := One(F);
  IsInU := x -> not IsZero(x) and x^n = one;
  frob := Set(List([0..q-1], j -> 3^j mod n));
  es := Filtered(CubeRoots(n), k -> k <> 1 and not (k in frob));
  Print("q = ", q, "  n = ", n, "  non-Frobenius cube roots: ", Length(es), "\n");
  for e in es do
    e2 := (e*e) mod n;
    hit := 0; trials := 2000;
    for i in [1..trials] do
      z := Random(F);
      if not IsZero(z) and IsInU(z) and not IsZero(z-one) and IsInU(z-one)
         and not IsZero(z^e-one) and IsInU(z^e-one) then hit := hit + 1; fi;
    od;
    f := function(b, a)
      local s, t, u;
      if IsZero(b) or IsZero(a) then return fail; fi;
      if not IsInU(-b) then return fail; fi;
      if not IsInU(-a) then return fail; fi;
      s := (-b)^e; t := (-a)^e2; u := s + t;
      if not IsInU(u) then return fail; fi;
      return [ s^e - u^e, t^e2 - u^e2 ];
    end;
    fails := 0; used := 0; samples := 60;
    for i in [1..samples] do
      repeat b := Random(F); until not IsZero(b) and IsInU(-b);
      repeat a := Random(F); until not IsZero(a);
      found := false;
      for k in [1..400] do
        a1 := Random(F);
        r1 := f(b, a1);
        if r1 = fail then continue; fi;
        r2 := f(r1[2], a - a1);
        if r2 <> fail then found := true; used := used + k; break; fi;
      od;
      if not found then fails := fails + 1; fi;
    od;
    Print("  e = ", e, ":  density(Z) approx ", Float(hit/trials),
          " (heuristic 0.125);  covering ", samples - fails, "/", samples,
          ", avg tries ", Int(used/Maximum(1, samples-fails)), "\n");
  od;
end;;

for q in [7, 13, 19] do RunOne(q); od;
QUIT;
