# verify_gn.g — BG App.C Problem 1 (p = 3): 万能完備化 Gamma_e の独立検証
#
# ChatGPT Work (GPT-5.6 Sol / ウルトラ, 2026-08-10) が主張した否定的解決を、
# こちら側で一から組み直して確かめるためのスクリプト。issue 0180 参照。
#
# 論法 (紙の部分):
#   witness (G, sigma, Q, y) があるとする。g = x^y, c = x^{-1} g = [x,y] とおくと
#     * c in A := <x,g> cap Q     (A は可換 3'-群)
#     * A は可換で x-不変ゆえ [c, c^x] = 1
#     * g = x c は位数 3 ゆえ (x c)^3 = 1
#     * g は U を正規化し、その作用は u -> u^e (e^3 = 1 mod |U|)
#   よって G = <H, g> は
#     Gamma_e = < H, z | [z, z^x] = 1, (x z)^3 = 1, (x z) u (x z)^{-1} = u^e >
#   の商 (z -> c)。したがって Gamma_e で z^3 = 1 なら任意の witness で c^3 = 1、
#   しかし c は 3'-群 A の元だから c = 1、すなわち g = x。これは x が U を
#   正規化しないこと (H が Frobenius, N_H(U) = U) に矛盾する。
#   ⟹ Gamma_e で z^3 = 1 を全ての e について確かめれば、その q は否定で確定する。
#   (G の有限性は一切使っていない。)
#
SizeScreen([250,64]);   # 出力を折り返さない

# 使い方: ~/gap-4.16.0/gap -q -b -o 8g < verify_gn.g

GammaPres := function(q, e)
  # 万能完備化 Gamma_e の有限表示を返す。x = a1 = F_3 の 1 による平行移動。
  local F, B, bv, theta, M, n, d, FR, gens, a, u, z, rels, i, j, k, w, x, g;
  d := q;
  F := GF(3^q);
  B := Basis(AsVectorSpace(GF(3), F));
  bv := BasisVectors(B);
  n := (3^q - 1)/2;
  theta := PrimitiveRoot(F)^2;          # ノルム 1 部分群 U の生成元 (位数 n)
  if Order(theta) <> n then Error("theta order"); fi;
  if bv[1] <> One(F) then Error("basis[1] is not 1"); fi;
  M := List(bv, v -> Coefficients(B, theta*v));
  FR := FreeGroup(Concatenation(List([1..d], i -> Concatenation("a", String(i))),
                                ["u", "z"]));
  gens := GeneratorsOfGroup(FR);
  a := gens{[1..d]};  u := gens[d+1];  z := gens[d+2];
  rels := [];
  for i in [1..d] do Add(rels, a[i]^3); od;
  for i in [1..d] do for j in [i+1..d] do Add(rels, Comm(a[i], a[j])); od; od;
  Add(rels, u^n);
  for i in [1..d] do                    # u a_i u^-1 = theta * (i 番目の基底)
    w := One(FR);
    for k in [1..d] do w := w * a[k]^IntFFE(M[i][k]); od;
    Add(rels, u * a[i] * u^-1 * w^-1);
  od;
  x := a[1];
  g := x * z;
  Add(rels, Comm(z, z^x));              # A は可換
  Add(rels, g^3);                       # g = x z は位数 3 を割る
  Add(rels, g * u * g^-1 * u^(-e));     # g は U を u -> u^e で正規化
  return FR / rels;
end;

CubeRootsMod := function(n)
  return Filtered([1..n-1], e -> GcdInt(e, n) = 1 and (e^3 - 1) mod n = 0);
end;

RunQ := function(q)
  local n, e, G, gens, sz, zz, oz, H, hs;
  n := (3^q - 1)/2;
  Print("=== q = ", q, "   |P| = 3^", q, " = ", 3^q,
        "   |U| = ", n, "   |H| = ", 3^q * n, "\n");
  Print("    exponents e with e^3 = 1 mod ", n, ": ", CubeRootsMod(n), "\n");
  for e in CubeRootsMod(n) do
    G := GammaPres(q, e);
    gens := GeneratorsOfGroup(G);
    sz := Size(G);
    zz := gens[q+2];
    oz := Order(zz);
    H := Subgroup(G, gens{[1..q+1]});
    hs := Size(H);
    Print("  e = ", e,
          "  |Gamma| = ", sz,
          "  |H image| = ", hs,
          "  [Gamma:H] = ", sz/hs,
          "  order(z) = ", oz,
          "  z^3 = 1 ? ", 3 mod oz = 0, "\n");
  od;
end;

RunQ(3);

QUIT;
