---
id: 9404
slug: huppert-ii-satz32-solvable-2transitive
title: "CLAIM: Huppert II Satz 3.2 — 2-transitive 群の可解正規核と elementary abelian regular normal subgroup"
created: 2026-07-21
---

# CLAIM: Huppert II Satz 3.2 — 2-transitive 群の可解正規核と elementary abelian regular normal subgroup

**claim 主体**: lane c。**consumer**: Pf App.C Prop 1 (`NearFields.lean`
`rankOne_affine_nearField`, 残 sorry 1) の前提 (iii)。lane b の issue 2053
(Pf II Theorem B campaign) が Prop 1 を消費予定 — (ii) Brauer–Suzuki は 9318 (b) が
別途 claim 済、本 issue は (iii) を c が分担する。

## 背景 — Pf App.C Prop 1 の証明 (p. 137, pdftotext 07.0 実読 2026-07-21)

Prop 1 (2-rank 1 ⟹ affine near-field model) の証明の前提 4 つ:

1. [H] III Satz 8.2: 2-rank 1 ⟹ Sylow 2 は cyclic or generalized quaternion —
   **実質既存**: `Isaacs.Ch06.isCyclic_or_two_quaternion_of_subgroups_card_prime_unique`
   (Thm 6.11)。`RankOneHypothesis.two_rank_one` (order-4 elementary abelian 不在) からの
   橋のみ要。
2. **Brauer–Suzuki** `G = O_{2'}(G)·C_G(u)` — **未形式化、issue 9318 (lane b claim)**。
   Prop 1 はこれに gated。
3. Feit–Thompson: `O_{2'}(G)` solvable — **repo 完成済** (`feitThompson`)。
4. **[H] II Satz 3.2** (本 issue): 2-transitive faithful G + 可解な非自明正規部分群
   (Pf の適用では transitive な `O_{2'}(G)`) ⟹ G は elementary abelian で
   Ω 上 regular な正規部分群 F を持つ (⟹ `G = F ⋊ Stab(ω)`)。

## statement 案 (Burnside/Galois 標準形)

```lean
-- 新 leaf OddOrder/GroupTheory/SolvableTwoTransitive.lean (同 commit で OddOrder.lean 配線)
theorem exists_elementaryAbelian_regular_normal_of_two_pretransitive
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [FaithfulSMul G Ω]
    (h2 : MulAction.IsMultiplyPretransitive G Ω 2)
    {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) (hsolv : IsSolvable ↥N) :
    ∃ (p : ℕ) (F : Subgroup G), p.Prime ∧ F.Normal ∧ F ≤ N ∧
      IsElementaryAbelian p F ∧   -- repo 既存述語を実測して合わせる
      (∀ ω : Ω, MulAction.stabilizer G ω ⊓ F = ⊥) ∧  -- regular = transitive + free; 符号化は実装時に確定
      MulAction.IsPretransitive F Ω
```

## 証明 (標準、全部品の所在は着手時実測)

1. 2-pretransitive ⟹ `IsPreprimitive` (mathlib `MultipleTransitivity` /
   Isaacs Ch08 に前例; 無ければ短い直接証明)。
2. preprimitive ⟹ 非自明正規部分群は transitive (mathlib Primitive.lean の
   quasipreprimitive / orbit-is-block 論法)。⟹ N transitive。
3. G-minimal normal F ≤ N を取る (finite)。F ≤ N solvable ⟹ F solvable ⟹
   F' < F かつ F' char F ⊴ G ⟹ F' = ⊥ ⟹ F abelian; minimality + Ω₁ 論法で
   elementary abelian (repo の chief-factor/minimal-normal 部品を実測:
   Isaacs Ch03 / AppA の chiefFactor 系)。
4. F normal nontrivial ⟹ transitive (step 2)。abelian + transitive + faithful ⟹
   regular (stabilizer 内の元は全点固定 ⟹ 1)。

## 事前検索 (claim-before-build, 2026-07-21)

- repo: `IsPreprimitive` 使用は Isaacs Ch08 (lane b) + Suzuki/Simplicity のみ、
  Huppert II 3.2 相当の定理は無い (grep `regular.*normal|elementaryAbelian.*regular`)。
- mathlib: `Primitive.lean` に IsPreprimitive/IsQuasipreprimitive、
  `MultipleTransitivity.lean` に IsMultiplyPretransitive — Satz 3.2 自体は無い。
- open 9xxx: 9318 (Brauer–Suzuki, b) は前提 (ii) 側で別物。9133 残債とは独立。

## 完了条件

上記定理が sorry-free / axiom-clean で landing、Prop 1 の docstring の前提リスト
(iii) が解消済みに更新される。(Prop 1 本体の discharge は 9318 (ii) 完成後。)

## 参照

- `references/peterfalvi/pdftotext/07.0_pp_137_138_On_Near-Fields.txt` (Prop 1 証明)。
- `OddOrder/Peterfalvi/Appendices/NearFields.lean:744` (残 sorry)、`:652`
  (`RankOneHypothesis` — (A1) = `IsMultiplyPretransitive G Ω 2`, (A2) = faithful)。
- issue 2053 (lane b, consumer) / 9318 (lane b, 前提 (ii))。

## ✅ 2026-07-22 landed — close

- `OddOrder/GroupTheory/SolvableTwoTransitive.lean` (156 行, commit 877b1026f):
  `exists_elementaryAbelian_regular_normal_of_isMultiplyPretransitive` +
  `stabilizer_inf_eq_bot_of_isMulCommutative_of_isPretransitive`。
  leaf build green (2219 jobs)、#print axioms = propext/Classical.choice/Quot.sound のみ。
- `OddOrder.lean` 配線済 (同 commit)。NearFields Prop 1 docstring の前提リスト更新済
  ((iii) 解消、残 gate = (ii) Brauer–Suzuki issue 9318 のみ)。
- statement メモ: regular 性は `IsPretransitive F Ω` + `∀ ω, stabilizer G ω ⊓ F = ⊥` の
  対で供給 (consumer 側で `G = F ⋊ Stab(ω)` を標準導出)。elementary abelian は
  `IsMulCommutative ↥F` + `∀ x ∈ F, x^p = 1` + `IsPGroup p ↥F` の 3 述語で明示。
