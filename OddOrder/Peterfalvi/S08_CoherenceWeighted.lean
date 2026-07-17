/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceCorePart1
import OddOrder.Peterfalvi.S08_RetargetReducible

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
weighting is localized to the **member family** `χmem`; the break pair `χ, χ̄` and the anchor
`χmem i₁`
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
  hmemdegdiffsupp : ∀ i ∈ s, (χmem i - deg i • χmem i₁).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  hmemS1 : ∀ i ∈ s, χmem i ∈ S₁
  /-- The member squared norms `mc i = ‖χmem i‖²` (explicit, as in `xAdjoinStepW`). -/
  mc : ι → ℝ
  hmempos : ∀ i ∈ s, 0 < mc i
  /-- Orthogonality with the **squared-norm diagonal** `mc i = ‖χmem i‖²` (not forced to `1`). -/
  hmemortho : ∀ i ∈ s, ∀ j ∈ s,
    ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0
  /-- The anchor is irreducible: `mc i₁ = 1`. -/
  hanchorNorm : mc i₁ = 1
  /-- Per-member ν-aux decomposition `Dmem i : CharacterPsiDecomposition τ (χmem i) 0` — for case (B)
  built from `certainTypeR`/`certainTypeDecompositionDa` (reducible columns) or
  `memberExtensionDecomposition` (irreducibles). -/
  Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
    (χmem i) 0
  /-- The (5.2.e) cross-family orthogonality `R(χmem i) ⊥ R(χ)`. -/
  hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj χ hrealχ
        hdiffsuppχ)
  /-- The running-extension agreement `(Dmem i).tau1 = ν`. -/
  htau1Dmem : ∀ i (hi : i ∈ s), (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i)
  a : ℕ
  hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • χmem i₁).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup A L
  htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
    (hyp.fullDadeIsometryData hconj) ((χ : ClassFunction ↥L ℂ) - a • χmem i₁) ∈ ZIrr G
  ha1 : deg i₁ = 1
  /-- The **norm-weighted** degree bound `2a < ∑ deg(i)² / mc i`. -/
  hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i
  hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
    (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {χmem i₁})
  hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
    Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
      {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
       (χ : ClassFunction ↥L ℂ) - a • χmem i₁})

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

/-- **Norm-weighted crux1** (Peterfalvi (5.6.1)/(5.6.2) for a reducible member family).  The weighted
analogue of `crux1_of_memberFamily`: the member family `χmem` is orthogonal with real squared norms
`mc i` (`hmemortho i j = if i=j then mc i else 0`), the anchor is irreducible (`hanchorNorm : mc i₁
= 1`), and the degree bound is the **weighted** `2a < ∑ deg(i)²/mc i`.  Then the crux inner product
`⟨τ(χ−a·χ₁), ν χ₁⟩ = −a`.

The proof is the orthonormal `crux1` with `1 ↦ mc i`: the orthogonal projection
(`exists_indexed_projection_of_orthogonal_ZIrr`) gives integer `cZ i = ⟨Da.Y, ν χᵢ⟩` and the
*rational* expansion `Da.Y = ∑ (cZ i/mc i)·ν χᵢ + Z`; with `cZ i = a·[i=i₁] − (a+μ)·deg i` and the
anchor norm `mc i₁ = 1`, this is the `λ`-form `∑ (a·[i=i₁] − λ·rc i)·ν χᵢ` with `λ = a+μ`,
`rc i = deg i/mc i`; the (5.6.2) engine `lambda_eq_zero_and_Z_eq_zero` (already norm-general) then
forces `λ = 0`, i.e. `μ = −a`.  Here `∑ rc² · mc = ∑ deg²/mc` is the weighted bound. -/
theorem crux1_of_memberFamilyW {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (_hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData
        hconj))
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ) {a : ℕ}
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ
      (χ : ClassFunction ↥L ℂ) (a • χmem i₁))
    (hDaY_ZIrr : Da.Y ∈ ZIrr G)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0)
    (hanchorNorm : mc i₁ = 1)
    (hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ))
    (hμZ : τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i) :
    ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
      (hS₁.extension (χmem i₁)) = -(a : ℂ) := by
  classical
  have hνZ : ∀ i ∈ s, hS₁.extension (χmem i) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr (χmem i) (Submodule.subset_span (hmemS1 i hi))
  obtain ⟨μ, hμeq⟩ := ClassFunction.inner_mem_ZIrr_int hμZ (hνZ i₁ hi₁)
  -- the `ν`-images are orthogonal with the same norms `mc i`
  have horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (hS₁.extension (χmem i)) (hS₁.extension (χmem j)) =
        if i = j then (mc i : ℂ) else 0 := by
    intro i hi j hj
    rw [hS₁.extension_inner_eq (χmem i) (χmem j) (Submodule.subset_span (hmemS1 i hi))
      (Submodule.subset_span (hmemS1 j hj)), hmemortho i hi j hj]
  -- orthogonal integer projection of `Da.Y`
  obtain ⟨cZ, Z, hcZval, hYsum, hZortho⟩ :=
    exists_indexed_projection_of_orthogonal_ZIrr hDaY_ZIrr s
      (fun i => hS₁.extension (χmem i)) mc hνZ hmempos horth
  set lam : ℤ := (a : ℤ) + μ with hlam_def
  -- coefficient identification `cZ i = a·[i=i₁] − λ·deg i` (in `ℂ`)
  have hcoeff_eq : ∀ i ∈ s, (cZ i : ℂ) =
      (a : ℂ) * (if i = i₁ then 1 else 0) - (lam : ℂ) * (deg i : ℂ) := by
    intro i hi
    rw [← hcZval i hi, hcoeffval i hi, hμeq, hlam_def]; push_cast; ring
  -- the `λ`-form of `Da.Y`, with `rc i = deg i / mc i`
  have hY : Da.Y =
      (∑ i ∈ s, (((a : ℝ) * (if i = i₁ then 1 else 0)
        - (lam : ℝ) * ((deg i : ℝ) / mc i) : ℝ) : ℂ) • hS₁.extension (χmem i)) + Z := by
    rw [hYsum]; congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hmi : mc i ≠ 0 := (hmempos i hi).ne'
    congr 1
    rw [Complex.ofReal_inj]
    by_cases h : i = i₁
    · subst h
      have hci := hcoeff_eq i hi
      rw [if_pos rfl] at hci
      have hciR : (cZ i : ℝ) = (a : ℝ) - (lam : ℝ) * (deg i : ℝ) := by
        have : (cZ i : ℂ) = (a : ℂ) - (lam : ℂ) * (deg i : ℂ) := by rw [hci]; ring
        exact_mod_cast this
      rw [if_pos rfl, hanchorNorm, hciR]; field_simp
    · have hci := hcoeff_eq i hi
      rw [if_neg h] at hci
      have hciR : (cZ i : ℝ) = -((lam : ℝ) * (deg i : ℝ)) := by
        have : (cZ i : ℂ) = -((lam : ℂ) * (deg i : ℂ)) := by rw [hci]; ring
        exact_mod_cast this
      rw [if_neg h, hciR]; field_simp; ring
  -- the anchor norm computation `‖a·χ₁‖² = a²·mc i₁`
  have hψ : (ClassFunction.inner (a • χmem i₁ : ClassFunction ↥L ℂ) (a • χmem i₁)).re
      = (a : ℝ) ^ 2 * mc i₁ := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁), ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl,
      star_natCast]
    rw [show (a : ℂ) * ((a : ℂ) * (mc i₁ : ℂ)) = (((a : ℝ) ^ 2 * mc i₁ : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  -- (5.6.2) integer forcing: `λ = a + μ = 0`
  obtain ⟨hlam0, -⟩ := Da.lambda_eq_zero_and_Z_eq_zero s i₁ hi₁ (a : ℝ) lam Z
    (fun i => hS₁.extension (χmem i)) mc (fun i => (deg i : ℝ) / mc i)
    hY horth hZortho hψ
    (by simp only [ha1, hanchorNorm, Nat.cast_one]; norm_num)
    (by positivity)
    (by
      refine hDeg.trans_le (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i hi => ?_
      have hmi : mc i ≠ 0 := (hmempos i hi).ne'
      field_simp)
  have hμval : μ = -(a : ℤ) := by simp only [hlam_def] at hlam0; omega
  rw [hμeq, hμval]; push_cast; ring

/-- **Norm-weighted (5.6) forward adjoin engine (general members).**

The weighted analogue of `xAdjoinStep` (case A), generalized so the member family `χmem` may
contain **reducible** characters: the per-member ν-aux decompositions `Dmem i` and the family
orthogonalities `hortho_mem`/`htau1Dmem` are taken as **parameters** rather than constructed from
`memberExtensionDecomposition` (which is irreducible-only, requiring `χmem i : IrreducibleCharacter`
via the Dade family `dadeOrthonormalCharacterImageFamilyOfDiff`).

This is exactly the split Peterfalvi (5.6) needs for case (B) of (6.8.3): the break pair `χ, χ̄` and
the anchor `χmem i₁` stay irreducible (norm one), while a non-anchor member may be a reducible
certain-type column `μⱼ` whose orthonormal image family `R(μⱼ)` is supplied by the §6 σ-isometry
(Peterfalvi (5.3.b)).  Each `Dmem i : CharacterPsiDecomposition τ (χmem i) 0` carries that family in
`(Dmem i).imageFamily`, the running extension as `(Dmem i).tau1 = ν` (`htau1Dmem`), and the (5.2.e)
cross-family orthogonality `R(χmem i) ⊥ R(χ)` (`hortho_mem`).

* For an irreducible member, `Dmem i = memberExtensionDecomposition …`, `hortho_mem i =
  dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal …`, `htau1Dmem i = rfl` — recovering the
  case-A instantiation.
* For a reducible certain-type column, `Dmem i` is built via `ofProjection` from the σ-image family
  `R(μⱼ)` ((5.3.b)); this is the remaining §5↔§6 bridge.

The weighting enters only through `mc` (the member norms `‖χmem i‖²`), the weighted orthogonality
`hmemortho`, and the weighted degree bound `hDeg : 2a < ∑ deg² / mc`, all threaded into
`crux1_of_memberFamilyW`. -/
noncomputable def xAdjoinStepW
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    (hanchorNorm : mc i₁ = 1)
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (χmem i) 0)
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj χ hrealχ
        hdiffsuppχ))
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- The trivially-derived orthogonalities `χ, χ̄ ⊥ a·χ₁` for the χ-decomposition `Da`.
  have hχaχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ)
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχ_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  have hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχbar_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  -- The χ-decomposition for the degree-matched difference `χ − a·χ₁`.
  -- (`let`, not `have`/`set`, so `Da.tau1 = τ` / `Da.imageFamily = R(χ)` reduce definitionally.)
  let Da := OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp hconj χ hrealχ hdiffsuppχ
    hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar
  -- `Da.X ∈ ZIrr` (integer combination of the orthonormal `R(χ)` family) ⟹ `Da.Y ∈ ZIrr`.
  have hDaX_ZIrr : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    refine Submodule.sum_mem _ (fun α hα => ?_)
    rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  have hYeq : Da.Y = Da.X - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) := by
    have h : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) = Da.X - Da.Y :=
      Da.tau1_image
    rw [h]; abel
  have hDaY_ZIrr : Da.Y ∈ ZIrr G := by
    rw [hYeq]; exact Submodule.sub_mem _ hDaX_ZIrr htau1_memaχ
  have hchi1chi1 : ClassFunction.inner (χmem i₁ : ClassFunction ↥L ℂ)
      (χmem i₁ : ClassFunction ↥L ℂ) = 1 := by
    rw [hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl]; exact_mod_cast hanchorNorm
  -- (5.2.e) `⟨Da.X, ν χᵢ⟩ = 0` per member.
  have hXortho : ∀ i ∈ s, ClassFunction.inner Da.X (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      0 :=
    fun i hi =>
      inner_decomposition_X_extension_member_eq_zero hS₁ Da (Dmem i hi) (hortho_mem i hi)
        (htau1Dmem i hi)
  -- (5.6.1) cross-term `hfound` per member (`inner_dade_extension_of_supported`).
  have hfound : ∀ i ∈ s, ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ))) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ))
        ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)) := fun i hi => by
    refine inner_dade_extension_of_supported hyp hconj hS₁ hdiffasuppχ ?_
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- The (5.6.1) member coefficient `⟨Da.Y, ν χᵢ⟩` in the `lambda_eq_zero_and_Z_eq_zero` form.
  have hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y
      (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
            ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
          (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ))) * (deg i : ℂ) := by
    intro i hi
    have key := inner_Y_extension_member_eq hyp hconj hS₁ χ hYeq (hXortho i hi) (hfound i hi)
      (hχ_S1 _ (hmemS1 i hi)) (hχ_S1 _ (hmemS1 i₁ hi₁)) hchi1chi1
    rw [hmemortho i₁ hi₁ i hi] at key
    rw [key]
    rcases eq_or_ne i i₁ with h | h
    · subst h; simp [hanchorNorm]
    · rw [if_neg h, if_neg (fun hc : i₁ = i => h hc.symm)]
  -- crux1 via the λ-form collapse.
  have hcrux1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = -(a : ℂ) :=
    crux1_of_memberFamilyW hyp hconj
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
      hS₁ (χ : ClassFunction ↥L ℂ) s (fun i => (χmem i : ClassFunction ↥L ℂ)) deg i₁ hi₁ Da
      hDaY_ZIrr hmemS1
      mc hmempos hmemortho hanchorNorm hcoeffval htau1_memaχ ha1 hDeg
  -- crux2 clean: `⟨τ(χ − χ̄), ν χ₁⟩ = 0` from `R(χ) ⊥ R(χ₁)`.
  have hcrux2 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, Da.imageFamily.image_eq,
      OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_zero (fun α hα =>
        OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily
          (Dmem i₁ hi₁) (hortho_mem i₁ hi₁) (htau1Dmem i₁ hi₁) hα), star_zero]
  -- `(χ − χ̄)^τ ∈ ZIrr` from the `R(χ)` family (`image_eq`); `(χ − a·χ₁)^τ ∈ ZIrr` is
  -- `htau1_memaχ`.
  have hτdiffZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G := by
    rw [Da.imageFamily.image_eq]
    exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα)
  -- Adjoin via the (T8.11 option A) bridge.
  exact retarget_isCoherent_of_extensionImage hyp hconj
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
    hS₁ χ hdiffsuppχ hdiffasuppχ hχχ hχbarχbar hχχbar hχbarχ hchi1chi1 hχ_S1 hχbar_S1
    (hmemS1 i₁ hi₁) htau1_memaχ hτdiffZ hcrux1 hcrux2 hSgen hgen

/-- **Norm-weighted (5.6) forward adjoin engine, reducible BREAK (`‖χ‖² ≠ 1`).**

The `‖χ‖² ≠ 1` analogue of `xAdjoinStepW`: the **break** pair `{χ, χ̄}` may itself be a
reducible certain-type column (`‖χ‖² = w₁ > 1`), not just the non-anchor members.  The break
decomposition `Da : CharacterPsiDecomposition τ χ (a·χ₁)` is therefore taken as a **parameter**
(constructed by `certainTypeDecompositionDa` from the (5.3.b) σ-image family `R(μ_j)`), rather than
built internally by `decompositionDaFromDadeOfDiff` (irreducible-only, via the conjugate-pair Dade
family `dadeOrthonormalCharacterImageFamilyOfDiff`).  The break image family `R(χ) = Da.imageFamily`
then feeds the (5.2.e) cross-family orthogonality `hortho_mem` and the crux-2 vanishing.

The only extra hypothesis over `xAdjoinStepW` is `hDatau1 : Da.tau1 = τ` (the break
decomposition's auxiliary isometry is the Dade base map itself — holds by `rfl` for
`certainTypeDecompositionDa`), used to read the (5.4) image equation `τ(χ − a·χ₁) = Da.X − Da.Y`
(`hYeq`) off `Da.tau1_image`.  The norm-1 hypotheses `hχχ`/`hχbarχbar` of `xAdjoinStepW` become the
non-vanishing `hχχne`/`hχbarχbarne`, and the bridge is the reducible
`retarget_isCoherent_of_extensionImage_k`. -/
noncomputable def xAdjoinStepW_k
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ)
    (hdiffsuppχ : (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχbarχbarne : ClassFunction.inner χ.conj χ.conj ≠ 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    (hanchorNorm : mc i₁ = 1)
    {a : ℕ}
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (χmem i) 0)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      χ (a • χmem i₁))
    (hDatau1 : Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj))
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily)
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    (hdiffasuppχ : (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {χ - χ.conj, χ - a • (χmem i₁ : ClassFunction ↥L ℂ)})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- `Da.X ∈ ZIrr` (integer combination of the supplied orthonormal `R(χ) = Da.imageFamily`).
  have hDaX_ZIrr : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    refine Submodule.sum_mem _ (fun α hα => ?_)
    rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  -- (5.4) image equation, read off `Da.tau1_image` via `hDatau1 : Da.tau1 = τ`.
  have hYeq : Da.Y = Da.X - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)) := by
    have h := Da.tau1_image
    rw [hDatau1] at h
    rw [h]; abel
  have hDaY_ZIrr : Da.Y ∈ ZIrr G := by
    rw [hYeq]; exact Submodule.sub_mem _ hDaX_ZIrr htau1_memaχ
  have hchi1chi1 : ClassFunction.inner (χmem i₁ : ClassFunction ↥L ℂ)
      (χmem i₁ : ClassFunction ↥L ℂ) = 1 := by
    rw [hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl]; exact_mod_cast hanchorNorm
  -- (5.2.e) `⟨Da.X, ν χᵢ⟩ = 0` per member.
  have hXortho : ∀ i ∈ s,
      ClassFunction.inner Da.X (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) = 0 :=
    fun i hi =>
      inner_decomposition_X_extension_member_eq_zero hS₁ Da (Dmem i hi) (hortho_mem i hi)
        (htau1Dmem i hi)
  -- (5.6.1) cross-term `hfound` per member.
  have hfound : ∀ i ∈ s, ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ))) =
      ClassFunction.inner (χ - a • (χmem i₁ : ClassFunction ↥L ℂ))
        ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)) := fun i hi => by
    refine inner_dade_extension_of_supported hyp hconj hS₁ hdiffasuppχ ?_
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- The (5.6.1) member coefficient `⟨Da.Y, ν χᵢ⟩`.
  have hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y
      (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
            (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)))
          (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ))) * (deg i : ℂ) := by
    intro i hi
    have key := inner_Y_extension_member_eq hyp hconj hS₁ χ hYeq (hXortho i hi) (hfound i hi)
      (hχ_S1 _ (hmemS1 i hi)) (hχ_S1 _ (hmemS1 i₁ hi₁)) hchi1chi1
    rw [hmemortho i₁ hi₁ i hi] at key
    rw [key]
    rcases eq_or_ne i i₁ with h | h
    · subst h; simp [hanchorNorm]
    · rw [if_neg h, if_neg (fun hc : i₁ = i => h hc.symm)]
  -- crux1 via the weighted λ-form collapse.
  have hcrux1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = -(a : ℂ) :=
    crux1_of_memberFamilyW hyp hconj
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
      hS₁ χ s (fun i => (χmem i : ClassFunction ↥L ℂ)) deg i₁ hi₁ Da hDaY_ZIrr hmemS1
      mc hmempos hmemortho hanchorNorm hcoeffval htau1_memaχ ha1 hDeg
  -- crux2 clean: `⟨τ(χ − χ̄), ν χ₁⟩ = 0` from `R(χ) = Da.imageFamily ⊥ R(χ₁)`.
  have hcrux2 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)
        (χ - χ.conj))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, Da.imageFamily.image_eq,
      OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_zero (fun α hα =>
        OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily
          (Dmem i₁ hi₁) (hortho_mem i₁ hi₁) (htau1Dmem i₁ hi₁) hα), star_zero]
  -- `(χ − χ̄)^τ ∈ ZIrr` from the break image family `Da.imageFamily`.
  have hτdiffZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      (χ - χ.conj) ∈ ZIrr G := by
    rw [Da.imageFamily.image_eq]
    exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα)
  -- Adjoin via the reducible-break (5.6.3) bridge.
  exact retarget_isCoherent_of_extensionImage_k hyp hconj
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)) rfl
    hS₁ χ χ.conj hdiffsuppχ hdiffasuppχ hχχne hχbarχbarne hχχbar hχbarχ hchi1chi1 hχ_S1 hχbar_S1
    (hmemS1 i₁ hi₁) htau1_memaχ hτdiffZ hcrux1 hcrux2 hSgen hgen

/-- **The per-step weighted X-adjoin** (bundled form).  A `XAdjoinStepInputW` yields the coherence of
`S₁ ∪ {χ, χ̄}` — the weighted analogue of `XAdjoinStepInput.adjoin`, for the (weighted) X-chain fold
`coherentOfPairChainCover`.  Pure pass-through to `xAdjoinStepW`. -/
noncomputable def XAdjoinStepInputW.adjoin
    {A : Set G}
    {hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L} {hconj : hyp.HConjInvariant}
    {S₁ : Set (ClassFunction ↥L ℂ)}
    {hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L)}
    {χ : IrreducibleCharacter ↥L} (inp : XAdjoinStepInputW hyp hconj hS₁ χ) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
  xAdjoinStepW hyp hconj hS₁ χ inp.hrealχ inp.hdiffsuppχ inp.hχχ inp.hχbarχbar inp.hχχbar
    inp.hχbarχ inp.hχ_S1 inp.hχbar_S1 inp.s inp.χmem inp.deg inp.i₁ inp.hi₁
    inp.hmemdegdiffsupp inp.hmemS1 inp.mc inp.hmempos inp.hmemortho inp.hanchorNorm
    inp.Dmem inp.hortho_mem inp.htau1Dmem inp.hdiffasuppχ inp.htau1_memaχ inp.ha1 inp.hDeg
    inp.hSgen inp.hgen

/-- **Norm-weighted (5.6) degree-square bound (contrapositive of `xAdjoinStepW`).**

The norm-weighted Peterfalvi (5.6) inequality: if `S₁` is coherent but `S₁ ∪ {χ, χ̄}` is **not**,
then
the weighted degree-square sum is bounded by twice the degree ratio,
`∑_{i∈s} deg(i)² / ‖χmem i‖² ≤ 2a`.  This is the reducible-member generalization of
`coherentDegreeSumBound_of_not_coherent` (the case-A `‖χmem i‖² = 1` specialization, with conclusion
`∑ deg² ≤ 2a`).

Pure contrapositive of the forward engine `xAdjoinStepW`: were the bound to fail
(`2a < ∑ deg²/mc`), `xAdjoinStepW` would produce coherence of `S₁ ∪ {χ, χ̄}`, contradicting `hnc`.
All the per-member decomposition data (`Dmem`/`hortho_mem`/`htau1Dmem`) is threaded through
unchanged — for case (B) it is supplied per member from `certainTypeDecompositionDa`/`certainTypeR`
(reducible certain-type columns) and `memberExtensionDecomposition` (irreducible members). -/
theorem coherentDegreeSqNormBound_of_not_coherentW
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    (hanchorNorm : mc i₁ = 1)
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (χmem i) 0)
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj χ hrealχ
        hdiffsuppχ))
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)}))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨xAdjoinStepW hyp hconj hS₁ χ hrealχ hdiffsuppχ hχχ hχbarχbar hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemdegdiffsupp hmemS1 mc hmempos hmemortho hanchorNorm
    Dmem hortho_mem htau1Dmem hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

/-- **Norm-weighted (5.6) degree-square bound, reducible BREAK (contrapositive of `xAdjoinStepW_k`).**

The `‖χ‖² ≠ 1` analogue of `coherentDegreeSqNormBound_of_not_coherentW`: if `S₁` is coherent but
`S₁ ∪ {χ, χ̄}` is **not** — for a possibly **reducible** break `χ` whose decomposition `Da` is
supplied as a parameter — then the weighted degree-square sum is bounded,
`∑ deg(i)²/‖χmem i‖² ≤ 2a`.
Pure contrapositive of the reducible-break forward engine `xAdjoinStepW_k`. -/
theorem coherentDegreeSqNormBound_of_not_coherentW_k
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ)
    (hdiffsuppχ : (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχbarχbarne : ClassFunction.inner χ.conj χ.conj ≠ 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (mc i : ℂ) else 0)
    (hanchorNorm : mc i₁ = 1)
    {a : ℕ}
    (Dmem : ∀ i ∈ s, OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (χmem i) 0)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      χ (a • χmem i₁))
    (hDatau1 : Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj))
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily)
    (htau1Dmem : ∀ i (hi : i ∈ s),
      (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    (hdiffasuppχ : (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData hconj)
      (χ - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {χ - χ.conj, χ - a • (χmem i₁ : ClassFunction ↥L ℂ)}))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      (S₁ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨xAdjoinStepW_k hyp hconj hS₁ χ hdiffsuppχ hχχne hχbarχbarne hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemdegdiffsupp hmemS1 mc hmempos hmemortho hanchorNorm
    Dmem Da hDatau1 hortho_mem htau1Dmem hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

/-- **(T-A2, norm-weighted) The X-family coherence chain fold.**

The weighted analogue of `xChainCoherent`: folds the per-step weighted adjoin `xAdjoinStepW` (via
`XAdjoinStepInputW.adjoin`) over a degree-monotone conjugate-pair cover of `X`, from a coherent base
`S₀` — for case (B), the reducible certain-type column set `certainTypeSet`, coherent via
`certainTypeSet_isCoherent_tau_canonical`.  Each step adjoins the irreducible pair `(χs i, χ̄s i)` to
the accumulator `pairUnion S₀ pair i` through the bundled weighted input `hstep i`, whose member
family ranges over the **(possibly reducible)** accumulator members — exactly the case-(B) X-chain
the unweighted `xChainCoherent` cannot express (its `XAdjoinStepInput` bakes in member
orthonormality
`‖χmem i‖² = 1`, which fails on the reducible columns).

The construction of `hstep` (the per-step `XAdjoinStepInputW`) from the certain-type column data —
`certainTypeMemberDecomposition` for the reducible-column members,
`certainTypeR_imageSet_orthogonal_
dadeOfDiff` for their cross-family orthogonality, `memberExtensionDecomposition` for the
already-adjoined irreducibles — is the remaining per-step obligation; this fold packages it into the
full `X`-coherence `cX`. -/
noncomputable def xChainCoherentW
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hconj : hyp.HConjInvariant)
    {X S₀ : Set (ClassFunction ↥L ℂ)}
    (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
    (χs : ℕ → IrreducibleCharacter ↥L)
    (hpair0 : ∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ))
    (hpair1 : ∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj)
    (hS₀ : S₀ ⊆ X)
    (hpairs : ∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆ X)
    (hcover : ∀ χ ∈ X, χ ∈ S₀ ∨ ∃ j, j < N ∧ χ ∈ OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
    (h0 : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      S₀ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (hstep : ∀ i, i < N → ∀ (hcoh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) S₀ pair i)
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L)),
      XAdjoinStepInputW hyp hconj hcoh (χs i)) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj))
      X (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
  OddOrder.Peterfalvi.S07.coherentOfPairChainCover pair N hS₀ hpairs hcover h0
    (fun i hi hcoh => by
      rw [OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair (hpair0 i hi) (hpair1 i hi)]
      exact (hstep i hi hcoh).adjoin)

end OddOrder.Peterfalvi.S08
