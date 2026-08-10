SizeScreen([250,64]);
Check := function(q)
  local F, one, sq, T, S, sumT, V, B, r1, r2, Vp;
  F := GF(3^q); one := One(F);
  sq := Set(List(Filtered(Elements(F), z -> z <> Zero(F)), z -> z^2));
  S := sq;
  T := Filtered(sq, s -> (s + one) in sq);
  sumT := Sum(T);
  B := Basis(AsVectorSpace(GF(3), F));
  r1 := RankMat(List(T, s -> Coefficients(B, s)));
  # V+ := span { v + v^-1 : v in S }
  Vp := Set(List(S, v -> v + v^-1));
  r2 := RankMat(List(Vp, s -> Coefficients(B, s)));
  Print("q=", q, "  Sum(T) = ", sumT, "  (= -1 ? ", sumT = -one, ")",
        "   rank(T) = ", r1, "/", q,
        "   |{v+v^-1}| = ", Length(Vp), "  rank{v+v^-1} = ", r2, "/", q, "\n");
end;
for q in [3,5,7,11] do Check(q); od;
QUIT;
