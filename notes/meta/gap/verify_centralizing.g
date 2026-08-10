# verify_centralizing.g — BG App.C Problem 1 (p = 3): 中心化作用の場合の人手証明の検証
#
# issue 0180。2026-08-10。ChatGPT の q = 3 計算 (verify_gn.g で再現済) を踏まえて
# こちらで見つけた「一般の奇素数 q に対する人手証明」の各ステップを機械で確かめる。
#
# 証明の骨子 (G の中で完結する。万能完備化も合同枚挙も要らない):
#   x = sigma(P_0) の生成元 (位数 3)、g = x^y、c = x^{-1} g = [x,y] in Q とする。
#   (S1) c, c^x in Q (可換) ゆえ [c, c^x] = 1。
#   (S2) 語の恒等式: x^3 = g^3 = 1 のとき [x^{-1}g, (x^{-1}g)^x] = (g x)^3。
#        ⟹ (g x)^3 = 1。
#   (S3) g が sigma(U) を中心化する場合、(g x)^3 = 1 を v in sigma(U) で共役して
#        (g s)^3 = 1  (s in S := U を F の部分集合と見たもの = 平方元全体)。
#   (S4) s, t, s+t in S なら [t, s^g] = 1。
#        (証明: (g s)^3 = 1 は s^{g^2} s^g s = 1 と同値。s, t, s+t の 3 本と
#         P, P^g が可換なことだけから、消去して [s^g, t] = 1 が出る。)
#   (S5) t = x = 1 と取ると、T := { s in F : s と s+1 が共に平方 } の元 s について
#        [x, s^g] = 1。C := { v in P : [x, v^g] = 1 } は部分群だから T が F を張れば
#        C = P、特に [x, x^g] = 1。
#   (S6) [x, x^g] = 1 と (g x)^3 = 1 から c^3 = 1。c は 3'-群 Q の元ゆえ c = 1、
#        すなわち g = x。しかし <g> = sigma(P_0)^y は sigma(U) を正規化し、
#        sigma(P_0) は正規化しない (H は Frobenius, N_H(U) = U)。矛盾。
#
# ⟹ 残るのは補題「T は F_{3^q} を F_3 上張る」。|T| = (3^q - 3)/4 で、
#    Weil 評価より 3^q > 32 で任意の超平面からはみ出す。q = 3 だけ直接確認する。
#
SizeScreen([250,64]);   # 出力を折り返さない

# 使い方: ~/gap-4.16.0/gap -q -b < verify_centralizing.g

# --- (A) 語の恒等式 [x^{-1}g, (x^{-1}g)^x] = (gx)^3  (x^3 = g^3 = 1 の下で) ------

CheckWordIdentity := function()
  local G, reps, x, g, i, ok, c, cx;
  ok := true;
  for G in [SymmetricGroup(6), SymmetricGroup(7), AlternatingGroup(8), SL(2,7)] do
    for i in [1..300] do
      x := Random(G); g := Random(G);
      if Order(x) = 3 and Order(g) = 3 then
        c  := x^-1*g;
        cx := c^x;
        if Comm(c, cx) <> (g*x)^3 then ok := false; fi;
      fi;
    od;
  od;
  Print("(A) word identity [x^-1 g, (x^-1 g)^x] = (gx)^3 on order-3 pairs: ", ok, "\n");
end;

# --- (B) 補題: T = { s : s, s+1 ともに平方 } は F_{3^q} を F_3 上張るか ---------

CheckSpanning := function(q)
  local F, Q, sq, T, s, V, r, expected;
  F := GF(3^q); Q := 3^q;
  sq := Set(List(Filtered(Elements(F), z -> z <> Zero(F)), z -> z^2));
  T := Filtered(sq, s -> (s + One(F)) in sq);
  expected := (Q-3)/4;
  V := List(T, s -> Coefficients(Basis(AsVectorSpace(GF(3), F)), s));
  r := RankMat(V);
  Print("(B) q = ", q, "  |F| = ", Q,
        "  |T| = ", Length(T), " (expected ", expected, ": ", Length(T) = expected, ")",
        "  rank_F3(T) = ", r, " / ", q, "  spans = ", r = q, "\n");
end;

# --- (C) (S4) の検証: s, t, s+t in S ならば [t, s^g] = 1 ------------------------
#     万能完備化 Gamma_1 (q = 3) の中で実際に確かめる。

GammaOne := function(q)
  local F, B, bv, theta, M, n, d, FR, gens, a, u, z, rels, i, j, k, w, x, g;
  d := q; F := GF(3^q);
  B := Basis(AsVectorSpace(GF(3), F)); bv := BasisVectors(B);
  n := (3^q-1)/2; theta := PrimitiveRoot(F)^2;
  M := List(bv, v -> Coefficients(B, theta*v));
  FR := FreeGroup(Concatenation(List([1..d], i -> Concatenation("a", String(i))), ["u","z"]));
  gens := GeneratorsOfGroup(FR);
  a := gens{[1..d]}; u := gens[d+1]; z := gens[d+2];
  rels := [];
  for i in [1..d] do Add(rels, a[i]^3); od;
  for i in [1..d] do for j in [i+1..d] do Add(rels, Comm(a[i],a[j])); od; od;
  Add(rels, u^n);
  for i in [1..d] do
    w := One(FR);
    for k in [1..d] do w := w * a[k]^IntFFE(M[i][k]); od;
    Add(rels, u*a[i]*u^-1*w^-1);
  od;
  x := a[1]; g := x*z;
  Add(rels, Comm(z, z^x));
  Add(rels, g^3);
  Add(rels, g*u*g^-1*u^-1);            # e = 1: g は U を中心化
  return [FR/rels, d];
end;

CheckInGamma := function(q)
  local pair, G, d, gens, x, g, z, u, P, sz, s, t, badST, C, i, j;
  pair := GammaOne(q); G := pair[1]; d := pair[2];
  gens := GeneratorsOfGroup(G);
  x := gens[1]; u := gens[d+1]; z := gens[d+2]; g := x*z;
  sz := Size(G);
  Print("(C) q = ", q, "  |Gamma_1| = ", sz,
        "  order(z) = ", Order(z),
        "  [x, x^g] = 1 ? ", Comm(x, g^-1*x*g) = One(G),
        "  (g*x)^3 = 1 ? ", (g*x)^3 = One(G),
        "\n");
  # S := U の共役軌道 = { x^(u^k) }。s, t, s+t in S の全ペアで [t, s^g] = 1 を確認。
  P := List([0..(3^q-1)/2-1], k -> x^(u^k));
  badST := 0;
  for i in [1..Length(P)] do
    for j in [1..Length(P)] do
      if P[i]*P[j] in P then                    # s + t in S
        if Comm(P[j], g^-1*P[i]*g) <> One(G) then badST := badST + 1; fi;
      fi;
    od;
  od;
  Print("    (S4) pairs with s,t,s+t in S violating [t, s^g] = 1 : ", badST, "\n");
end;

CheckWordIdentity();
for q in [3,5,7,11,13] do CheckSpanning(q); od;
CheckInGamma(3);

QUIT;
