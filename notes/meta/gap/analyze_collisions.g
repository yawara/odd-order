# EXHAUSTIVE STRUCTURE OF THE COLLISIONS (2026-08-11).
#
# Goal: understand WHY collisions of D(p) = p^E - (p-1)^E exist inside the Paley set
#   T = { p : p and p-1 both nonzero squares },
# which is the one remaining gap (B1) of BG App.C Problem 1 for general q.
#
# Two facts we already know analytically:
#   (i)  E is ODD, hence D(1-p) = D(p) for EVERY p   (because (-z)^E = -z^E):
#            D(1-p) = (1-p)^E - (-p)^E = (1-p)^E + p^E = p^E - (p-1)^E = D(p).
#        So D is automatically 2-to-1 on F.  But 1-p = -(p-1) is a NON-square whenever
#        p-1 is a square, so the partner of a point of T never lies in T:
#            p in T  <=>  p, p-1 squares      1-p in T''  <=>  1-p, -p both non-squares.
#        T is exactly designed to dodge the free collision.  (B1) asks for an EXTRA one.
#   (ii) D(p^3) = D(p)^3, so collisions come in Frobenius orbits.
#
# This script enumerates T exhaustively for small q and reports:
#   * the fibre-size distribution of D|_T  (2 = one extra collision, 3, 4, ...);
#   * how many collisions have delta = p^E - r^E a square (the ones the criterion can use);
#   * whether r is an anharmonic image of p (the 6 maps p, 1-p, 1/p, 1/(1-p), (p-1)/p, p/(p-1))
#     or a Frobenius power of one -- i.e. whether the extra collisions are explained by a
#     symmetry we could exhibit by hand;
#   * the distribution of Tr(S) over the usable collisions (the (B2) side).
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

Analyze := function(q)
  local Q, n, NN, F, one, IsU, Tr, T, frob, es, e, E, E2, vals, pairs, i, j, k, fib, fibs,
        p, r, delta, S, t, usable, traces, anharm, names, hit, mi, img, z, nsame, tot;
  Q := 3^q; n := (Q-1)/2; NN := Q-1; F := GF(Q); one := One(F);
  IsU := x -> not IsZero(x) and x^n = one;
  Tr := function(x) local s, y, j; s := Zero(F); y := x;
    for j in [1..q] do s := s + y; y := y^3; od; return s; end;
  T := Filtered(AsSSortedList(F), z -> IsU(z) and IsU(z - one));
  frob := Set(List([0..q-1], j -> 3^j mod n));
  es := Filtered(CubeRoots(n), z -> z <> 1 and not (z in frob));
  Print("=== q = ", q, "  |F| = ", Q, "  |T| = ", Length(T),
        "  exotic exponents: ", Length(es), "\n");
  names := ["1-p", "1/p", "1/(1-p)", "(p-1)/p", "p/(p-1)"];
  for e in es do
    if IsOddInt(e) then E := e; else E := e + n; fi;
    E2 := (E*E) mod NN;
    vals := List(T, z -> z^E - (z - one)^E);
    pairs := List([1..Length(T)], z -> [vals[z], z]);
    Sort(pairs);
    # group into fibres
    fibs := []; i := 1;
    while i <= Length(pairs) do
      j := i;
      while j < Length(pairs) and pairs[j+1][1] = pairs[i][1] do j := j + 1; od;
      if j > i then Add(fibs, List([i..j], k -> T[pairs[k][2]])); fi;
      i := j + 1;
    od;
    usable := 0; traces := []; anharm := List([1..5], z -> 0); nsame := 0; tot := 0;
    for fib in fibs do
      for i in [1..Length(fib)] do
        for j in [i+1..Length(fib)] do
          p := fib[i]; r := fib[j]; tot := tot + 1;
          # anharmonic / Frobenius relation?
          for mi in [1..5] do
            if   mi = 1 then img := one - p;
            elif mi = 2 then img := p^-1;
            elif mi = 3 then img := (one - p)^-1;
            elif mi = 4 then img := (p - one) * p^-1;
            else             img := p * (p - one)^-1; fi;
            hit := false; z := img;
            for k in [1..q] do if z = r then hit := true; fi; z := z^3; od;
            if hit then anharm[mi] := anharm[mi] + 1; fi;
          od;
          z := p; for k in [1..q] do if z = r then nsame := nsame + 1; fi; z := z^3; od;
          delta := p^E - r^E;
          if not IsZero(delta) and IsU(delta) then
            usable := usable + 1;
            S := ((r - one)^E2 - r^E2) * (delta^-1)^E;
            Add(traces, Tr(S));
          fi;
        od;
      od;
    od;
    Print("  e=", e, "  fibre sizes: ", Collected(List(fibs, Length)),
          "  |pairs|=", tot, "  usable(delta square)=", usable, "\n");
    Print("     anharmonic hits (up to Frobenius) ", names, " = ", anharm,
          "   r in Frobenius orbit of p: ", nsame, "\n");
    Print("     Tr(S) distribution over usable pairs: ", Collected(traces), "\n");
  od;
end;;

Analyze(7);
Analyze(13);
QUIT;
