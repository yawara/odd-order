/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCorePart1

/-!
# Peterfalvi §5/§8: the norm-weighted (5.6) coherence-break engine

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§5 (Theorem 5.6, under the abstract Hypothesis 5.2), in the **norm-weighted** form needed for the
certain-type case (B) of (6.8.3).

The existing X-chain machinery (`XAdjoinStepInput` / `xAdjoinStep` / `crux1_of_memberFamily` in
`S08_CoherenceCorePart1`) bakes in *orthonormality* of the member family
(`hmemortho i j = if i = j then 1 else 0`) and the unweighted degree bound `2a < ∑ deg²`.  That is
the special case `‖χᵢ‖² = 1` of Theorem (5.6); it suffices for case (A) (Frobenius), where every
member of the coherent set `S₁` is irreducible.

In case (B) the coherent set `S₁` contains **reducible** certain-type columns `μⱼ` (each with
`‖μⱼ‖² > 1`), so the genuine Peterfalvi (5.6) — with the `‖χᵢ‖²`-weighted projection coefficients
`1/‖χᵢ‖²` and the weighted bound `2a < ∑ deg²/‖χᵢ‖²` — is required (ChatGPT/Pro-verified that there
is *no* sidestep; see `notes/peterfalvi/s08_6_8_3_reducibleS_chatgpt_answer.md` Q1–Q4).  The
weighting is localized to the **member family** `χmem`; the break pair `χ, χ̄` and the anchor `χmem i₁`
remain irreducible (norm one) in the (6.8.3) application, so their fields are unchanged.

This file develops that weighted engine additively (the unweighted version is preserved for case A):

* `XAdjoinStepInputW` — the bundled input with `χmem : ι → ClassFunction ↥L ℂ` general, the
  orthogonality `⟨χmem i, χmem j⟩ = if i = j then ⟨χmem i, χmem i⟩ else 0`, and the weighted degree
  bound `2a < ∑ deg² / ‖χmem i‖²`.
* (to come) `crux1_of_memberFamilyW`, `xAdjoinStepW`, `coherentDegreeSqNormBound_of_not_coherentW`.

Plan of record: `notes/peterfalvi/s56_reweighting_plan.md`.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped Classical

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- **Norm-weighted (5.6) X-adjoin input.**  The weighted analogue of `XAdjoinStepInput`: the member
family `χmem : ι → ClassFunction ↥L ℂ` is a family of (possibly reducible) characters of `S₁`, with

* orthogonality `⟨χmem i, χmem j⟩ = if i = j then ⟨χmem i, χmem i⟩ else 0` (the diagonal is the
  squared norm `‖χmem i‖²`, not forced to `1`);
* anchor `χmem i₁` irreducible (`hanchorNorm : ⟨χmem i₁, χmem i₁⟩ = 1`), of degree-ratio `1`;
* the **weighted** degree bound `2a < ∑_{i∈s} deg(i)² / ‖χmem i‖²`.

The break member `χ` is irreducible (norm one) as in the unweighted version.  Compare
`XAdjoinStepInput` (the `‖χmem i‖² = 1` special case used in case (A)). -/
structure XAdjoinStepInputW {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) where
  hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ)
  hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1
  hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ).conj = 1
  hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0
  hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0
  hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0
  hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0
  ι : Type
  s : Finset ι
  /-- The member family — **general** (possibly reducible) characters of `S₁`. -/
  χmem : ι → ClassFunction ↥L ℂ
  deg : ι → ℕ
  i₁ : ι
  hi₁ : i₁ ∈ s
  hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i)
  hmemdiffsupp : ∀ i ∈ s, ((χmem i).conj - χmem i).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemdegdiffsupp : ∀ i ∈ s, (χmem i - deg i • χmem i₁).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemS1 : ∀ i ∈ s, χmem i ∈ S₁
  hmembarS1 : ∀ i ∈ s, (χmem i).conj ∈ S₁
  hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i) (χmem i).conj = 0
  /-- Orthogonality with the **squared-norm diagonal** `‖χmem i‖²` (not forced to `1`). -/
  hmemortho : ∀ i ∈ s, ∀ j ∈ s,
    ClassFunction.inner (χmem i) (χmem j) =
      if i = j then ClassFunction.inner (χmem i) (χmem i) else 0
  /-- The anchor is irreducible: `‖χmem i₁‖² = 1`. -/
  hanchorNorm : ClassFunction.inner (χmem i₁) (χmem i₁) = 1
  a : ℕ
  hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • χmem i₁).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
    (hyp.fullDadeIsometryData hconj) ((χ : ClassFunction ↥L ℂ) - a • χmem i₁) ∈ ZIrr G
  ha1 : deg i₁ = 1
  /-- The **norm-weighted** degree bound `2a < ∑ deg(i)² / ‖χmem i‖²`. -/
  hDeg : 2 * (a : ℝ) <
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / (ClassFunction.inner (χmem i) (χmem i)).re
  hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
    (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {χmem i₁})

/-- **Orthogonal integer projection onto a norm-weighted `ZIrr` family.**  The weighted analogue of
`exists_indexed_intProjection_of_orthonormal_ZIrr`: for `φ ∈ ℤ[Irr G]` and a family
`vc : ι → ClassFunction G ℂ` of `ZIrr`-members that are pairwise *orthogonal* with squared norms
`mc i = ⟨vc i, vc i⟩` (`horth i j = if i=j then mc i else 0`, `mc i > 0`), the inner products
`⟨φ, vc i⟩ = cZ i` are integers and `φ` decomposes as `φ = ∑ (cZ i / mc i)·vc i + Z` with the
remainder `Z` orthogonal to every `vc i`.  Unlike the orthonormal case the coefficients
`cZ i / mc i` are *rational* (the integer `cZ i` divided by the squared norm) — exactly the
`1/‖χᵢ‖²` projection coefficient of Peterfalvi (5.6) (mmd 04.7; ChatGPT Q4). -/
theorem exists_indexed_projection_of_orthogonal_ZIrr {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {ι : Type*} (s : Finset ι) (vc : ι → ClassFunction G ℂ) (mc : ι → ℝ)
    (hvcZ : ∀ i ∈ s, vc i ∈ ZIrr G) (hmc_pos : ∀ i ∈ s, 0 < mc i)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (vc i) (vc j) = if i = j then (mc i : ℂ) else 0) :
    ∃ (cZ : ι → ℤ) (Z : ClassFunction G ℂ),
      (∀ i ∈ s, ClassFunction.inner φ (vc i) = (cZ i : ℂ)) ∧
      φ = (∑ i ∈ s, (((cZ i : ℝ) / mc i : ℝ) : ℂ) • vc i) + Z ∧
      ∀ i ∈ s, ClassFunction.inner Z (vc i) = 0 := by
  classical
  have hint : ∀ i ∈ s, ∃ n : ℤ, ClassFunction.inner φ (vc i) = (n : ℂ) :=
    fun i hi => ClassFunction.inner_mem_ZIrr_int hφ (hvcZ i hi)
  choose! cZ hcZ using hint
  refine ⟨cZ, φ - ∑ i ∈ s, (((cZ i : ℝ) / mc i : ℝ) : ℂ) • vc i, hcZ, by abel, ?_⟩
  intro i hi
  rw [ClassFunction.inner_sub_left]
  have hsum : ClassFunction.inner (∑ j ∈ s, (((cZ j : ℝ) / mc j : ℝ) : ℂ) • vc j) (vc i)
      = (cZ i : ℂ) := by
    rw [inner_sum_left, Finset.sum_eq_single i]
    · rw [ClassFunction.inner_smul_left, horth i hi i hi, if_pos rfl]
      have hmci : (mc i : ℂ) ≠ 0 := by exact_mod_cast (hmc_pos i hi).ne'
      push_cast
      field_simp
    · intro j hj hji
      rw [ClassFunction.inner_smul_left, horth j hj i hi, if_neg hji, mul_zero]
    · intro hni; exact absurd hi hni
  rw [hsum, hcZ i hi, sub_self]

end OddOrder.Peterfalvi.S08
