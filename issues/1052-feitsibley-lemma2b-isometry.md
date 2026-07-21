---
id: 1052
slug: feitsibley-lemma2b-isometry
title: "FeitSibley Lemma 2(b) isometry: ℤ[𝒮]° 上の誘導等長性 (Isaacs 7.7)"
created: 2026-07-21
---

# FeitSibley Lemma 2(b) isometry: ℤ[𝒮]° 上の誘導等長性 (Isaacs 7.7)

lane a frontier (文書順、Lemma 2(a) = issue 1051 の次)。
`induction_isometry_on_degree_zero` (FeitSibley.lean) の isometry 節 sorry を close する。
integrality / degree-zero 節は証明済 (`tau_mem_ZIrr` / `tau_apply_one`)。

## 調査結果 (2026-07-21): 既存 infra で閉じる — 新規 TI port 不要

理論の docstring が言う「repo の TI-isometry 材料は未特殊化」は**陳腐化**。
**`inner_induce_eq_of_isTISubset` (InducedCharacter.lean:746) が Isaacs 7.7 isometry
そのもの**:

```
(hTI : IsTISubset A H) (hθ : ∀ x : ↥H, ↑x ∉ A → θ x = 0) (hψ : ...) :
  ⟨Ind_H^G θ, Ind_H^G ψ⟩ = ⟨θ, ψ⟩
```

`IsTISubset A L : ∀ g, (∃ a ∈ A, g·a·g⁻¹ ∈ A) → g ∈ L` (TISubset.lean:73)。

## やること (上流から)

- [ ] **TI 補題** `Hypothesis.isTISubset_Q_sdiff_one : IsTISubset ((Q : Set G) \ {1}) H`:
  対偶 `of_disjoint_conj` でなく直接 — g で overlap (a ∈ Q\{1}, g·a·g⁻¹ ∈ Q\{1}) を仮定、
  g ∉ H なら `Q_trivial_intersection g` で Q ⊓ Q.map (conj g) = ⊥。g·a·g⁻¹ は Q (overlap) と
  Q.map (conj g) (a ∈ Q) の両方に属す ⟹ = 1 ⟹ a = 1、a ≠ 1 に矛盾。
- [ ] **span 消滅補題**: φ ∈ zSpan 𝒮 ⟹ ∀ x : ↥H, ↑x ∉ Q → φ x = 0。
  `Submodule.span_induction` (性質 {f | ∀ x, ↑x ∉ Q → f x = 0} は加法/smul 閉) +
  `apply_eq_zero_of_mem_Sset_of_not_mem_Q` (777ad1a7d)。
- [ ] **off-A 消滅の組立**: φ ∈ zSpan 𝒮, φ(1) = 0 ⟹ ∀ x : ↥H, ↑x ∉ Q\{1} → φ x = 0
  (↑x ∉ Q は span 消滅; ↑x = 1 は Subtype 単射で x = 1 → hφ1)。
- [ ] **isometry 節 close**: `hyp.tau φ = ClassFunction.induce hyp.H φ` (tau_apply rfl) で
  `inner_induce_eq_of_isTISubset hyp.H hTI hθoff hψoff` に配線。
  instance: [Fintype ↥hyp.H] ✓ section / [Invertible (Nat.card G : ℂ)] ✓ /
  [Invertible (Nat.card ↥hyp.H : ℂ)] ✓。

## 参照

- `OddOrder/Peterfalvi/Appendices/FeitSibley.lean` `induction_isometry_on_degree_zero` (sorry)
- `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean:746`
  (`inner_induce_eq_of_isTISubset`), `OddOrder/GroupTheory/TISubset.lean:73` (`IsTISubset`)
- issue 1051 (closed, Lemma 2(a)), commit 777ad1a7d (𝒮 の H−Q 消滅)
- 下流: Lemma 2(c) (:1050 付近) / Theorem (`feit_sibley_coherence`)
