# Same test as verify_ito_product.g, but for q = 13 (the smallest OPEN case), by random sampling.
q := 13;;
Q := 3^q;;
n := (Q-1)/2;;
F := GF(Q);;
one := One(F);;
IsInU := x -> not IsZero(x) and x^n = one;
Print("q = ", q, "  Q = ", Q, "  n = ", n, "\n");

es := Filtered([1..n-1], k -> PowerMod(k, 3, n) = 1);;
frob := Set(List([0..q-1], j -> 3^j mod n));;
Print("cube roots of 1 mod n: ", es, "\n");
Print("which are Frobenius powers: ", Filtered(es, k -> k in frob), "\n");

RandField := function()
  return Random(F);
end;

TestExponent := function(e, samples, tries)
  local e2, f, i, b, a, a1, r1, r2, found, fails, used, k;
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
  fails := 0; used := 0;
  for i in [1..samples] do
    repeat b := RandField(); until not IsZero(b) and IsInU(-b);
    repeat a := RandField(); until not IsZero(a);
    found := false;
    for k in [1..tries] do
      a1 := RandField();
      r1 := f(b, a1);
      if r1 = fail then continue; fi;
      r2 := f(r1[2], a - a1);
      if r2 <> fail then found := true; used := used + k; break; fi;
    od;
    if not found then fails := fails + 1; fi;
  od;
  Print("  e = ", e, " (Frobenius power: ", e in frob, "):  samples ", samples,
        ", failures ", fails, ", avg tries ", Int(used/Maximum(1, samples-fails)), "\n");
end;

for e in es do
  if not (e in frob) then TestExponent(e, 200, 400); fi;
od;
QUIT;
