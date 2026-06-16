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

end OddOrder.Peterfalvi.S08
