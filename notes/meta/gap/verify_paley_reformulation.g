SizeScreen([250,64]);
# T = { s : s と s+1 が共に平方 } の言い換え検証
#   s ∈ T ⟺ s = a², s+1 = b² ⟹ (b-a)(b+a) = 1、u := b-a とすると
#   char 3 では a = u - u⁻¹, b = -(u + u⁻¹), s = (u - u⁻¹)² = u² + u⁻² + 1
#   v := u² (平方元) と置くと T = { v + v⁻¹ + 1 : v ∈ S, v ≠ 1 }
Check := function(q)
  local F, one, sq, T, S, T2, v, gal, stable, B, W, r;
  F := GF(3^q); one := One(F);
  sq := Set(List(Filtered(Elements(F), z -> z <> Zero(F)), z -> z^2));
  T := Filtered(sq, s -> (s + one) in sq);
  S := sq;
  T2 := Set(List(Filtered(S, v -> v <> one), v -> v + v^-1 + one));
  B := Basis(AsVectorSpace(GF(3), F));
  r := RankMat(List(T, s -> Coefficients(B, s)));
  # Galois 安定性: Frobenius が T を保つか
  stable := ForAll(T, s -> (s^3) in T);
  Print("q=", q, "  |T|=", Length(T), "  |{v+v^-1+1}|=", Length(T2),
        "  T = {v+v^-1+1} ? ", T = T2,
        "  Frobenius-stable ? ", stable,
        "  rank=", r, "/", q, "\n");
end;
for q in [3,5,7,11] do Check(q); od;
QUIT;
