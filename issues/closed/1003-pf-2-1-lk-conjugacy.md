---
id: 1003
slug: pf-2-1-lk-conjugacy
title: "Peterfalvi (2.1): L−K の元は xW₂ (x∈W₁^#) に L-共役 (certain-type 構造定理)"
created: 2026-06-12
---

# Peterfalvi (2.1): L−K の元は xW₂ (x∈W₁^#) に L-共役 (certain-type 構造定理)

## 背景

Pf §6 (4.8) の証明で、conclusion 1 (`Supp(μ_ij−μ_ik) ⊆ A₀`) の support 論法に必要。
session 31 (2026-06-12) で **critical-path blocker** と判明:

- conclusion 3 (FT-critical な isometry 恒等式 `(μ_ij−μ_ik)^τ = δ_j(ω_ij^σ−ω_ik^σ)`) は
  conclusion 1 に依存する。理由: LHS の τ (`h.tau : S04.FullDadeIsometryData dade0`) の domain は
  **A₀ 上 supported な CF(L)** (`full_map_eq_of_mem_V` の入力は `SupportedOnV`)。
  μ_ij−μ_ik を τ に渡すには `Supp⊆A₀` (=conclusion 1) が前提。
- conclusion 1 は **(2.1)** を要し、(2.1) は S04/S05/S06 に未形式化 (`V_subset_sharp` のみ存在)。

⟹ (2.1) は conclusion 1・conclusion 3 双方の前提。Task #4 / notes/peterfalvi/s06_dade_certain_subgroup.md
「session 31」参照。

## 命題 (Peterfalvi (2.1))

`Hypothesis ↥L` (= (4.2) for ↥L; `L = K ⋊ W₁`, `W₁` cyclic Hall, `W₂ = C_K(x)` cyclic for
`x ∈ W₁^#`, `W = W₁ × W₂` odd) のもとで:

> L−K の各元は L-共役で `x·W₂` (ある `x ∈ W₁^#`) の元に入る。

(4.8) の使い所: `z ∈ L−K` ⟹ z は xW₂ に L-共役 ⟹ z が Supp(μ_ij−μ_ik) 内なら、
xW₂ の W₁-部分 (=x) では step(2) [vanish on W₁] で値 0 ⟹ z の共役は x·W₂^# ⊆ V (=W−(W₁∪W₂))
⟹ `z ∈ V^L`。一方 `Supp∩K ⊆ A` は (4.7)。合わせて `Supp ⊆ A₀ = A ∪ V^L`。

## やること

- [ ] (2.1) を Lean statement 化 (`Hypothesis ↥L` or `CertainTypeHypothesis` 上の補題)
- [ ] **derivability 調査を先に**: 既存 API から導けるか —
  - `centralizer_eq_sup` (C_L(x)=W for x∈W₁^#, session 20)
  - `isComplement` (L = K ⋊ W₁)、`coprime_card_W1_card_W2`、`card_W_eq` (|W|=w₁·w₂)
  - counting: `|L−K| = |K|·(w₁−1)`、共役類の大きさ。
  - 導ければ conclusion 1 leaf 内の補題で済む; 重ければ独自 leaf (例 `S06_CertainTypeStructure.lean`)。
- [ ] (2.1) を使って conclusion 1 `certainType_diff_supp_subset_A0` を証明
  (step(2) `certainType_apply_eq_of_mem_W1` + (4.7) `chiRestrict_apply_eq_zero_of_not_mem_union` /
   `induce_…` + L↔G V-bridge: A₀ の V^L は ambient `tic.V`、`tic_W1`/`tic_W2`/`L.subtype` で橋渡し)

## 完了条件

(2.1) が Lean 補題として証明され (sorry-free, axiom-clean)、conclusion 1 がそれを用いて閉じる。
最終的に S06_CertainTypeIsometry の (4.8) conclusion 1 が landed。

## 参照

- notes/peterfalvi/s06_dade_certain_subgroup.md 「session 31」(critical finding) + 「session 30」(PDF proof)
- OddOrder/Peterfalvi/S06_CertainTypeIsometry.lean (step(1)(2) landed)
- OddOrder/Peterfalvi/S06_DadeIsometryCertain.lean (`Hypothesis`/`CertainTypeHypothesis` 構造, centralizer_eq_sup)
- OddOrder/Peterfalvi/S06_CertainHypothesis46.lean (A₀ = A∪V^L, tic 二層)
- commits 268d0940 (step1), 26e92857 (step2)
