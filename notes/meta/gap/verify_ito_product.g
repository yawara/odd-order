# BG App.C Problem 1: test whether the relation family forces N = A*B (product of two
# abelian subgroups), which by Ito's theorem would make N metabelian -- contradicting
# perfectness (Theorem 2) and settling the remaining open case.
#
# Relation (derived from R(v), proved): for s, t, s+t in U,
#   beta(-s^{e^2}) * alpha(-t^e) = alpha(s^e - (s+t)^e) * beta(t^{e^2} - (s+t)^{e^2}).
# So the pair (b,a) = (-s^{e^2}, -t^e) is "directly good": beta(b)alpha(a) in A*B.
# Test (I): for every b with -b in U and every a, is there a1 with (b,a1) directly good
# and (B1(b,a1), a-a1) directly good?  (Then BA is contained in AB, and Ito closes it.)

q := 7;;
Q := 3^q;;
n := (Q-1)/2;;
F := GF(Q);;
els := AsList(F);;
one := One(F);;
IsInU := x -> not IsZero(x) and x^n = one;

es := Filtered([1..n-1], k -> (k^3 mod n) = 1);;
Print("q = ", q, "  n = ", n, "  cube roots of 1 mod n: ", es, "\n");
frob := Set(List([0..q-1], j -> 3^j mod n));;
Print("<3> mod n (first few): ", frob{[1..Minimum(q,10)]}, "\n");

TestExponent := function(e)
  local e2, f, nonsq, tested, ok, bad, b, a, a1, r1, r2, found, aReps, nu;
  e2 := (e*e) mod n;
  f := function(b, a)
    local s, t, u;
    if IsZero(b) or IsZero(a) then return fail; fi;
    if not IsInU(-b) then return fail; fi;
    if not IsInU(-a) then return fail; fi;
    s := (-b)^e;
    t := (-a)^e2;
    u := s + t;
    if not IsInU(u) then return fail; fi;
    return [ s^e - u^e, t^e2 - u^e2 ];
  end;
  # representatives of a up to the U-action: a square and a non-square
  nu := First(els, x -> not IsZero(x) and not IsInU(x));
  aReps := [ one, nu ];
  tested := 0; ok := 0; bad := [];
  for b in els do
    if IsZero(b) or not IsInU(-b) then continue; fi;
    for a in aReps do
      tested := tested + 1;
      found := false;
      for a1 in els do
        r1 := f(b, a1);
        if r1 = fail then continue; fi;
        if a1 = a then found := true; break; fi;   # a2 = 0 is trivially good
        r2 := f(r1[2], a - a1);
        if r2 <> fail then found := true; break; fi;
      od;
      if found then ok := ok + 1; else Add(bad, [b, a]); fi;
    od;
  od;
  Print("  e = ", e, " (e in <3>: ", e in frob, "):  tested ", tested,
        ", 2-step covered ", ok, ", failures ", Length(bad), "\n");
  if Length(bad) > 0 then
    Print("    first failures: ", bad{[1..Minimum(3,Length(bad))]}, "\n");
  fi;
end;

for e in es do TestExponent(e); od;
QUIT;
