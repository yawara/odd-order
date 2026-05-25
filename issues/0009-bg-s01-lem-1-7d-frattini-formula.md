---
id: 9
slug: bg-s01-lem-1-7d-frattini-formula
title: "BG §1 Lemma 1.7(d) Frattini 生成公式を完成する"
created: 2026-05-25
---

# BG §1 Lemma 1.7(d) Frattini 生成公式を完成する

## 背景

BG §1 Lemma 1.7(d) は有限 p-群 `R` について `Φ(R) = ⟨R', x^p | x ∈ R⟩` を主張する。
現状は `OddOrder.GroupTheory.FrattiniPGroup.commutator_sup_pow_closure_le_frattini`
で `⟨R', x^p⟩ ≤ Φ(R)` の向きだけが完了し、`S01_Solvable.lean` に BG-facing theorem
として露出済み。

逆向きは、`K = commutator R ⊔ Subgroup.closure (Set.range (fun x => x ^ p))` と置き、
`R/K` が elementary abelian であることを示して、Ch.4 Lemma 4.5
`frattini_le_iff_isElementaryAbelian_quotient_of_pgroup` から `Φ(R) ≤ K` を得るのが自然。

## やること

- [ ] `OddOrder.GroupTheory.FrattiniPGroup` に `frattini_le_commutator_sup_pow_closure`
      方向を追加する。
- [ ] `commutator_sup_pow_closure_eq_frattini` の等号版を追加する。
- [ ] `OddOrder.BG.Ch1.S01` に BG Lemma 1.7(d) 完全形を露出する。

## 完了条件

- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。
- `S01_Solvable.lean` の Lemma 1.7(d) コメントから「逆向き deferred」が消える。

## 参照

- `OddOrder/GroupTheory/FrattiniPGroup.lean`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder.Isaacs.Ch04.frattini_le_iff_isElementaryAbelian_quotient_of_pgroup`
- commit `3ca59cf` (BG §1: expose Frattini Lemma 1.7 completions)
