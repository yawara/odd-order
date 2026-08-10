# verify_noncentral.g — BG App.C Problem 1: 非中心化作用 (e ∉ ⟨3⟩) の場合
#
# issue 0180、2026-08-10。中心化作用 (より一般に e ∈ ⟨3⟩) は
# notes/bg/appC_problem1_centralizing_case.md で全 q 決着した。残るのは e ∉ ⟨3⟩。
#
# 決定的な事実: ⟨3⟩ ≤ (Z/n)^× (n = (3^q−1)/2) は位数 q なので、位数 3 の e が
# Frobenius 冪 3^j になるのは q = 3 のときだけ。e = 3^j なら s ↦ s^e は F 上加法的で
# 中心化の場合の証明がそのまま通る。q ≥ 7 では通らない。
#
# ここで測る 2 つの量:
#
# (I) 関係格子  L_e := span_{F_3} { (s, s^e, s^{e²}) : s ∈ S } ≤ V ⊕ V ⊕ V   (V = F, dim q)
#     witness では (gx)³ = 1 を U で共役して
#         (s^{e²})^{g²} · (s^e)^g · s = 1   (s ∈ S)
#     が出る。N := ⟨P, P^g, P^{g²}⟩ のアーベル化で π_i(v) := (v^{g^i} の像) と置くと
#     Φ(a,b,c) := π₀(a)+π₁(b)+π₂(c) は F_3-線形で L_e を消す。
#     ⟹ **L_e = V³ なら Φ ≡ 0、すなわち P, P^g, P^{g²} ⊆ [N,N]、つまり N は完全群**。
#     P ≠ 1 なので N ≠ 1。⟹ witness をもつ G は可解でない。特に
#     **有限奇位数群は (奇数位数定理により可解なので) witness になれない**。
#     e = 3^j (加法的) のときは dim L_e = q にしかならない (Φ の核が 2q 次元) ので、
#     この論法は e ∉ ⟨3⟩ 専用。
#
# (II) 万能完備化 Γ_e における H = ⟨P,u⟩ の指数。3 が出れば H̄ ◁ Γ_e (|H̄| は奇数ゆえ
#     S₃ への像は C₃)、よって P̄ ◁ Γ_e で P̄^g = P̄、つまり N = P̄ は可換。
#     (I) と合わせて P̄ = [P̄,P̄] = 1 ⟹ **H が Γ_e に埋まらない ⟹ witness 無し**。
#     q = 7 で実測。
#
SizeScreen([250,64]);

# 使い方: ~/gap-4.16.0/gap -q -b -o 12g < verify_noncentral.g

GammaPres := function(q, e)
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
  Add(rels, g*u*g^-1*u^(-e));
  return FR/rels;
end;

# 位数 3 の単元 e (mod n) を **全部** CRT で構成する。
# (Z/n)^× の 3-階数が 2 以上だと位数 3 の元は 2 個では済まないので、素冪ごとの
# 立方根 (1, w, w²) の全組合せを取る。
AllOrd3Units := function(n)
  local f, mods, choices, p, a, m, r, w, i, tuples, t, e, res;
  f := Collected(FactorsInt(n)); mods := []; choices := [];
  for i in [1..Length(f)] do
    p := f[i][1]; a := f[i][2]; m := p^a; Add(mods, m);
    if (p-1) mod 3 = 0 or (p = 3 and a >= 2) then
      r := PrimitiveRootMod(m); w := PowerModInt(r, Phi(m)/3, m);
      Add(choices, [1, w, PowerModInt(w, 2, m)]);
    else
      Add(choices, [1]);
    fi;
  od;
  tuples := Cartesian(choices);
  res := [];
  for t in tuples do
    e := ChineseRem(mods, t);
    if e <> 1 then Add(res, e); fi;
  od;
  return Set(res);
end;

FrobeniusPowers := function(q)
  local n; n := (3^q-1)/2;
  return Set(List([0..q-1], j -> PowerModInt(3, j, n)));
end;

# (I) 関係格子の次元。S の元を 4q+40 個取れば十分 (rank は単調ゆえ部分集合で 3q に達すれば確定)
LatticeRank := function(q, e)
  local F, B, n, gen, s, L, i, cnt;
  n := (3^q-1)/2; F := GF(3^q); B := Basis(AsVectorSpace(GF(3), F));
  gen := PrimitiveRoot(F)^2;                    # U の生成元
  L := []; s := One(F); cnt := Minimum(n, 4*q+40);
  for i in [1..cnt] do
    Add(L, Concatenation(Coefficients(B, s),
                         Coefficients(B, s^e),
                         Coefficients(B, s^(e^2 mod n))));
    s := s * gen;
  od;
  return RankMat(L);
end;

RunLattice := function(q)
  local n, es, e, r, frob, allfull;
  n := (3^q-1)/2;
  if Phi(n) mod 3 <> 0 then
    Print("q=", q, "  n=", n, "   3 does not divide phi(n)  ==> only e=1 (settled by hand)\n");
    return;
  fi;
  es := AllOrd3Units(n); frob := FrobeniusPowers(q); allfull := true;
  Print("q=", q, "  n=", n, "   #{e : ord(e)=3} = ", Length(es), "\n");
  for e in es do
    r := LatticeRank(q, e);
    if r <> 3*q then allfull := false; fi;
    Print("      e=", e, "   e in <3> ? ", e in frob,
          "   dim L_e = ", r, " / ", 3*q, "   FULL ? ", r = 3*q, "\n");
  od;
  Print("      ==> all order-3 exponents give FULL lattice ? ", allfull, "\n");
end;

# (II) Γ_e における H の指数 (q = 7 のみ; 大きい q は u^n の関係子が重い)
RunIndex := function(q)
  local n, e, G, gens, H;
  n := (3^q-1)/2; e := AllOrd3Units(n)[1];
  G := GammaPres(q, e); gens := GeneratorsOfGroup(G);
  H := Subgroup(G, gens{[1..q+1]});
  Print("q=", q, "  e=", e, "   [Gamma_e : H] = ", Index(G, H), "\n");
end;

Print("--- (I) relation lattice ---\n");
for q in [3,5,7,13,19,29,31,41] do RunLattice(q); od;
Print("--- (II) index of H in the universal completion ---\n");
RunIndex(7);

QUIT;
