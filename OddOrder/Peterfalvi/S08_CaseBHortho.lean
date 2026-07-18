/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CaseBCoherence2

/-!
# Peterfalvi §8: case (B) — certain-type column vs break-pair cross-orthogonality

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8 (the **(6.8.2)** branch), feeding the norm-weighted (5.6) `X`-adjoin engine.

This leaf supplies the **(5.2.e) cross-family orthogonality** `R(μ_j) ⊥ R(χ)` between

* the reducible certain-type column image family `certainTypeR h46 hχ₂ hdeg` (the
  signed `σ`-images `R(μ_j) = {δ_j ω_{ij}^σ, −δ_j ω_{ik}^σ}` of Peterfalvi (5.3.b)), and
* the irreducible break character's Dade difference family
  `dadeOrthonormalCharacterImageFamilyOfDiff` (the two-element `R(χ) = {ε·μ, −ε·ν}`),

stated at the `imageSet` level.  It is the certain-type counterpart of
`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` (irreducible–irreducible) and the
`hortho_mem` ingredient of the norm-weighted (5.6) `xAdjoinStepW` engine.

The proof mirrors the V-vanishing technique of
`inner_coherent_extension_certainTypeOmegaSigma_eq_zero` (`S08_CaseBCoherence2`): each member
`α = (±δ_j)·ω_{ij}^σ` of `R(μ_j)` is a scalar multiple of a `chiFam`
(`certainTypeOmegaSigma_eq_chiFam`),
each member `β = c·ξ` of `R(χ)` (`ξ ∈ {μ, ν} ⊆ Irr G`) is one half of the two-element break pair,
and
the break difference `c·ξ − c'·ξ' = (χ − χ̄)^τ` vanishes on the `(ticVdiff h46)`-exceptional set `V`
(`tau_apply_eq_zero_of_mem_ticVdiffV`, since `χ − χ̄` is `H^#`-supported).  The disjointness machine
`inner_smul_chiFam_eq_zero_of_diff_vanishOnV` then gives `⟨c·ξ, ω_{ij}^σ⟩ = 0`, and conjugate
symmetry transports it to `⟨α, β⟩ = 0`.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(5.2.e) certain-type column vs break-pair cross-orthogonality** (Peterfalvi §8, case (B)). -/
theorem certainTypeR_imageSet_orthogonal_dadeOfDiff
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ∀ α ∈ (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).imageSet,
    ∀ β ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dade hyp.hconj χ
        hrealχ hdiffsuppχ).imageSet,
      ClassFunction.inner α β = 0 := by
  classical
  -- `hmin`: `2 < min(w₁, w₂)` for the `ticVdiff` exceptional structure.
  have hmin : 2 < min (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W1)
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W2) := by
    have h1 := (OddOrder.Peterfalvi.S06.ticVdiff h46).three_le_card_W1
    have h2 := (OddOrder.Peterfalvi.S06.ticVdiff h46).three_le_card_W2
    omega
  -- **Core disjointness brick.**  For any column `χ₂'`, row `i`, and a normalized orthonormal pair
  -- `ξ, ξ'` whose signed difference `c·ξ − c'·ξ'` vanishes on `V`, the σ-image `ω_{ij}^σ` is
  -- orthogonal to `c·ξ`.
  have key : ∀ (χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ)
      (i : Fin (Nat.card h46.W1)) {c c' : ℂ} {ξ ξ' : ClassFunction G ℂ},
      ξ ∈ ZIrr G → ClassFunction.inner ξ ξ = 1 → ξ' ∈ ZIrr G → ClassFunction.inner ξ' ξ' = 1 →
      ClassFunction.inner ξ ξ' = 0 → c ≠ 0 →
      (∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, (c • ξ - c' • ξ') v = 0) →
      ClassFunction.inner (c • ξ)
        (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂' i) = 0 := by
    intro χ₂' i c c' ξ ξ' hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish
    rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam]
    exact inner_smul_chiFam_eq_zero_of_diff_vanishOnV (OddOrder.Peterfalvi.S06.ticVdiff h46) rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46) hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish
      hmin _
  -- `(χ − χ̄)^τ` vanishes on `V` (`χ − χ̄` is `H^#`-supported).
  have hsuppsub : ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
        -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) by abel,
      ClassFunction.support_neg]
    exact hdiffsuppχ
  have htauvanish : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      hyp.tau ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) v = 0 :=
    fun v hv => tau_apply_eq_zero_of_mem_ticVdiffV hyp h46 hHK hsuppsub hv
  -- Capture the underlying two-element `CharacterDifferenceImage` `R(χ) = {ε·μ, −ε·ν}` abstractly
  -- (its `(1.4)` proof obligations are inferred by `rfl`), so we never reconstruct them by hand.
  obtain ⟨cd, hcd⟩ :
      ∃ cd : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
          (hyp.dade.fullDadeIsometryData hyp.hconj)) (χ : ClassFunction ↥L ℂ),
        OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dade hyp.hconj χ
            hrealχ hdiffsuppχ
          = cd.toOrthonormalImage := ⟨_, rfl⟩
  -- `R(χ).image_eq` rewritten in `ε·μ − ε·ν` form, equal to `(χ − χ̄)^τ`, hence vanishing on `V`.
  have hcdimg : hyp.tau ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)
      = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction := by
    rw [SibleyDadeHypothesis.tau, cd.image_eq, smul_sub, Int.cast_smul_eq_zsmul,
      Int.cast_smul_eq_zsmul]
  -- The `ZIrr`/orthonormality facts for `μ, ν`.
  have hμZ : cd.muClassFunction ∈ ZIrr G := cd.mu.mem_ZIrr
  have hνZ : cd.nuClassFunction ∈ ZIrr G := cd.nu.mem_ZIrr
  have hμ1 : ClassFunction.inner cd.muClassFunction cd.muClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.mu; rwa [if_pos rfl] at h
  have hν1 : ClassFunction.inner cd.nuClassFunction cd.nuClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.nu; rwa [if_pos rfl] at h
  have hμν : ClassFunction.inner cd.muClassFunction cd.nuClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.nu; rwa [if_neg cd.distinct] at h
  have hνμ : ClassFunction.inner cd.nuClassFunction cd.muClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.mu
    rwa [if_neg (Ne.symm cd.distinct)] at h
  have hsignC : (cd.sign : ℂ) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  have hnsignC : (-(cd.sign : ℂ)) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  -- Destructure α and β.
  intro α hα β hβ
  rw [hcd] at hβ
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage,
    Finset.mem_insert, Finset.mem_singleton] at hβ
  simp only [OddOrder.Peterfalvi.S06.certainTypeR, Finset.mem_image] at hα
  obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
  -- The two `(χ − χ̄)^τ`-vanishing facts for the two signed pairs `(μ, ν)` / `(ν, μ)`.
  have hvanishμν : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      ((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) v = 0 := by
    intro v hv; rw [← hcdimg]; exact htauvanish v hv
  have hvanishνμ : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      ((-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction) v = 0 := by
    intro v hv
    rw [show (-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction
        = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction by
      rw [neg_smul, neg_smul]; abel]
    exact hvanishμν v hv
  -- Normalize the `ℤ`-smul break-pair members `ε·μ`, `−ε·ν` to `ℂ`-smul (matching `key`).
  have hμcast : cd.sign • cd.muClassFunction = (cd.sign : ℂ) • cd.muClassFunction :=
    (Int.cast_smul_eq_zsmul ℂ cd.sign cd.muClassFunction).symm
  have hνcast : (-cd.sign) • cd.nuClassFunction = (-(cd.sign : ℂ)) • cd.nuClassFunction := by
    rw [← Int.cast_smul_eq_zsmul ℂ (-cd.sign) cd.nuClassFunction, Int.cast_neg]
  -- For each `β = ε·μ` or `−ε·ν`, and each `α = (±δ_j)·ω^σ`, reduce via conjugate symmetry and
  -- `key`.
  rcases hβ with rfl | rfl <;> cases b <;>
    simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
  -- Case β = ε·μ, α = δ_j·ω_{χ₂,i}^σ.
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  -- Case β = ε·μ, α = −δ_j·ω_{χ₂⁻¹,i}^σ.
  · rw [hμcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν, mul_zero, star_zero]
  -- Case β = −ε·ν, α = δ_j·ω_{χ₂,i}^σ.
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]
  -- Case β = −ε·ν, α = −δ_j·ω_{χ₂⁻¹,i}^σ.
  · rw [hνcast, OddOrder.RepresentationTheory.inner_conj_symm,
      OddOrder.RepresentationTheory.inner_smul_right,
      key χ₂⁻¹ i hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ, mul_zero, star_zero]

/-- **(5.2.e) irreducible break-pair vs certain-type column cross-orthogonality** `R(χ) ⊥ R(μ_j)`.
The `R(μ_j) ⊥ R(χ)` lemma `certainTypeR_imageSet_orthogonal_dadeOfDiff` with the two families
swapped, by conjugate symmetry of the inner product.  This is the member-side ingredient when the
**break** is a reducible certain-type column (the family roles are reversed from the
irreducible-break
`caseB_member_orthoDatum`): an irreducible member `x = Ind θ` has image family `R(x) =
dadeOrthonormalCharacterImageFamilyOfDiff`, which must be orthogonal to the column break's
`R(μ_j) = certainTypeR`. -/
theorem dadeOfDiff_imageSet_orthogonal_certainTypeR
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ∀ α ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dade hyp.hconj χ
        hrealχ hdiffsuppχ).imageSet,
    ∀ β ∈ (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ hdeg).imageSet,
      ClassFunction.inner α β = 0 := by
  intro α hα β hβ
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    certainTypeR_imageSet_orthogonal_dadeOfDiff hyp h46 hHK hχ₂ hdeg χ hrealχ hdiffsuppχ β hβ α hα,
    star_zero]

end OddOrder.Peterfalvi.S08
