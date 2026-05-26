---
id: 36
slug: stuck-7-6-step-7
title: "Discharge Isaacs Thm 7.6 Step 7 axiom"
created: 2026-05-27
---

# Discharge Isaacs Thm 7.6 Step 7 axiom

## 背景

§7B Steps 2-6 + Step 8 のブリッジ補題は landed (commits a5ff31c, ed9a9ab).
Step 7 (mmd L3884-3892 = Isaacs p.213-214 の最終 contradiction 引数) だけが
未着で, `OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main` に
`thompsonJ_le_opCore_of_normal_J_hypotheses` という `axiom` で placeholder.

これを discharge することで `normal_J` (Isaacs Thm 7.6) は完全 axiom-free
(`#assert_only_allowed_axioms` を通る) になる.

## 書籍での議論

Isaacs FGT p.213-214 (mmd L3884-3892):

設定:
- (i)-(v) の Thm 7.6 仮説.
- `L := O_p(G)`, `V := Z(L)`, `A ∈ E(P)` で `A ⊄ L` (反証用).
- Step 1: `Z(P) ≤ L`, `C_G(L) ≤ L`.
- Step 2-3: `D := A ⊓ L`, `|A : D| = p` (elementary abelian + L = O_p で
  Hall-Higman 3.21 から `G/L` の p-成分が自明).
- Step 4: `D` は `V` に自明に作用 (Step 5-6 で landed).
- Step 5-6: `A/D` の `V` への作用が自明 (Ch.6 Thm 6.20 + Ch.4 Cor 4.35).

Step 7 の中身 (axiom):
- Step 5-6 の結論「A が V 全体に自明作用」⇒ `A ≤ C_G(V) = C_G(Z(L))`.
- `Z(P) ≤ Z(L)` (Step 1 で `Z(P) ≤ L` かつ Z(P) は全 P と可換, ゆえに L と可換).
- ゆえに `C_G(Z(L)) ≤ C_G(Z(P)) = P` (hypothesis v).
- A ≤ P (既知) かつ A が V に自明作用を組合せて, `A · Ω₁(V)` を E(P) の元
  として再構成し maxElemAbelianIn の最大性に矛盾.

## やること

- [ ] `notes/isaacs/ch07_thompson.md` に Step 7 の詳細 strategy を書く
- [ ] `actionCommutator` (Ch.4) と `MulAut.conjNormal` (mathlib) で A の
      V への conjugation action を formalize
- [ ] Step 5-6 application: Ch.4 Cor 4.35
      (`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`)
      + Ch.6 Thm 6.20 (`isCyclic_of_faithful_trivial_on_proper_invariant`)
      を実際に使って「[A, V] = 1」を導出
- [ ] Step 7 counting: A · Ω₁(Z(L)) の elementary abelian 拡大が
      `maxElemAbelianIn P p` の最大性に矛盾することを示す
- [ ] `axiom thompsonJ_le_opCore_of_normal_J_hypotheses` を `theorem` に格上げ
- [ ] `OddOrder/AxiomsCheck.lean` に `normal_J` を追加して axiom-free を CI gate

## 完了条件

- `axiom thompsonJ_le_opCore_of_normal_J_hypotheses` が `theorem` に置換され
  `lake build OddOrder` が通る
- `OddOrder.Isaacs.Ch07.normal_J` が `#assert_only_allowed_axioms` で通る

## 参照

- commits a5ff31c (Step 2-4 structural bridges), ed9a9ab (Step 5-6 + Step 8)
- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean` §7B section
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean:3437` Cor 4.35
- `OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean:3015` Thm 6.20
- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean:2516` Thm 7.5
- Isaacs FGT pp.209-214, mmd L3832-3896
