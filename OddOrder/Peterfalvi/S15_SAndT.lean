/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_BridgeCharacter
import OddOrder.Peterfalvi.S16_PairingCoherence
import OddOrder.Peterfalvi.S16_PairingBessel
import OddOrder.Peterfalvi.S16_GridExpansion
import OddOrder.Peterfalvi.S15_SAndTGrid

/-!
# TAIL — (13.19.c) dichotomy + (14.5) complement exclusion

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT` (2000-line limit, issues 0103/0102/0111).
The (13.19) producer / grid-facts layer moved to `S15_SAndTGrid` (imported below); this module
holds the (13.19.c) dichotomy (`typeI_caseC_dichotomy`, parity core, the two case bounds) and
the Peterfalvi (14.5) exclusion of the small complement `E = W₁`.

The (13.19) grid data is stated against the (12.6) coherence bundle `S16.TypeICoherent78Data L`
(existence: `TypeICoherent78Data.nonempty`); `coh.extension` is the honest coherent extension `τ₁`.
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! #### (13.19.c) dichotomy — the isolated deep obligation

We prove `typeI_caseC_dichotomy` for the **distinguished coherent-family member** `ζ_0 = dataL.zeta 0`
(so the §7.8 `betaDecomp`/`normEstimates` of the bundle apply directly), and pass `ζ_0` as the
producer's `φ`.  The pieces: the bridge `β_L^τ = (dataL.h78 hG).beta`, the parity core
`⟨β_S^τ, ζ_0^{τ₁}⟩ + ⟨β_L^τ, η_{01}⟩ ≡ 1 (mod 2)`, and the two case bounds. -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Bridge**: `β_L^τ = τ₁(Ind_H^L 1_H − ζ_0)` at the distinguished member `ζ_0 = dataL.zeta 0` is
literally the §7.8 `beta` of the bundle (`(dataL.h78 hG).beta = τ(Ind_H^L 1_H − ζ_0)`).  Both are
the Dade image of `Ind_H^L 1_H − ζ_0`; the §9 `Hypothesis71.τ` and the §7 `tau` agree on supported
inputs (`toHypothesis71_tau_apply`), and `ζ_{ind1H} = Ind_H^L 1_H` (`dataL.triv`). -/
theorem typeIBetaL_zeta0_eq_h78_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) :
    typeIBetaL dataL.typeIHyp (dataL.zeta 0) = (dataL.h78 hG).beta := by
  haveI := dataL.kernelIn_normal
  rw [OddOrder.Peterfalvi.S09.Hypothesis78.beta_def]
  change dataL.typeIHyp.tau _ = dataL.typeIHyp.toHypothesis71.τ _
  rw [dataL.typeIHyp.toHypothesis71_tau_apply]
  apply congrArg dataL.typeIHyp.tau
  change ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
      (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L)) - dataL.zeta 0
    = (dataL.h78 hG).hyp76.zeta (dataL.h78 hG).ind1H
      - (dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct
  rw [dataL.h78_ind1H_eq, dataL.h78_zeta_eq, dataL.h78_zetaDistinct_eq, dataL.h78_zeta_eq]
  congr 1
  -- `Ind_H^L 1_H = ζ_{ind1H}` (`θ ind1H = 1_H`, `dataL.triv`)
  change ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
      (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L))
    = ClassFunction.induce dataL.kernelIn (dataL.θ dataL.ind1H : ClassFunction _ ℂ)
  rw [dataL.triv, IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  rfl

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) parity core** (Coq `odd_bSphi_bLeta`): at the distinguished member `ζ_0`,
the S-pairing `bSphi = ⟨β_S^τ, ζ_0^{τ₁}⟩` and the `η`-pairing `bLeta = ⟨β_L^τ, η_{01}⟩` are
integers whose **sum is odd**.  From `0 = ⟨β_L^τ, β_S^τ⟩` (disjoint support (13.19.a)),
`β_L^τ = 1 − ζ_0^{τ₁} + Δ_L` (the §7.8 residual `delta`), `β_S^τ = 1 − η_{01} + Γ_S`
((13.18.c) `gammaGrid_defGamma`), and `⟨Δ_L, Γ_S⟩` even (`cfdot_real_vchar_even`: both real
virtual characters orthogonal to `1_G`). -/
theorem typeI_caseC_parity [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) :
    ∃ nS nL : ℤ,
      ClassFunction.inner (tauSbetaGrid hG hyp)
          (dataL.coh.extension (dataL.zeta 0)) = (nS : ℂ) ∧
        ClassFunction.inner (typeIBetaL dataL.typeIHyp (dataL.zeta 0))
            (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
          = (nL : ℂ) ∧
        Odd (nS + nL) := by
  classical
  -- Abbreviations (kept as explicit terms to avoid `set`-fold clashes with lemma outputs).
  have hj1lt : (1 : ℕ) < hyp.p := by have := hyp.three_le_p; omega
  -- `ζ_0^{τ₁} = ν(ζ_0)` (definitional bridge).
  have hνζ : (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct)
      = dataL.coh.extension (dataL.zeta 0) := rfl
  -- ZIrr memberships.
  have hζextZ : dataL.coh.extension (dataL.zeta 0) ∈ OddOrder.RepresentationTheory.ZIrr G :=
    dataL.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)))
  have hΓSZ : GammaGrid hG hyp ∈ OddOrder.RepresentationTheory.ZIrr G :=
    gammaGrid_mem_ZIrr hG hnoV hyp
  have hβLZ : (dataL.h78 hG).beta ∈ OddOrder.RepresentationTheory.ZIrr G :=
    (dataL.h78 hG).beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (dataL.h78_ind_mem_ZIrr hG) (dataL.h78_zeta_irreducible hG)
  have hη01Z : hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩ ∈ OddOrder.RepresentationTheory.ZIrr G :=
    OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp _ _
  -- `β_S^τ = Γ_S + 1 − η_{01}`  ((13.18.c) `gammaGrid_defGamma`).
  have hβSdecomp : tauSbetaGrid hG hyp
      = GammaGrid hG hyp + OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩ := by
    have h := gammaGrid_defGamma hG hnoV hyp ⟨1, hj1lt⟩ (by simp)
    rw [tauSbetaGrid, ← h]; abel
  -- `Δ_L = β_L^τ − 1 + ζ_0^{τ₁}`, hence `β_L^τ = 1 − ζ_0^{τ₁} + Δ_L`.
  have hΔ : (dataL.h78 hG).delta
      = (dataL.h78 hG).beta - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        + dataL.coh.extension (dataL.zeta 0) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis78.delta, hνζ]
  have hβLdecomp : (dataL.h78 hG).beta
      = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G - dataL.coh.extension (dataL.zeta 0)
        + (dataL.h78 hG).delta := by rw [hΔ]; abel
  -- The two output integers.
  obtain ⟨nS, hnS⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hΓSZ hζextZ
  obtain ⟨nL, hnL⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hβLZ hη01Z
  -- `⟨Δ_L, Γ_S⟩` is an even integer  (`cfdot_real_vchar_even`, both real virtual `⊥ 1`).
  obtain ⟨z, a, b, hz, ha, hb, heven⟩ := cfdot_real_vchar_even hG.odd
    (dataL.delta_mem_ZIrr hG) (dataL.delta_isReal hG) hΓSZ (gammaGrid_real hG hnoV hyp)
  have hΔ_one : ClassFunction.inner (dataL.h78 hG).delta
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 :=
    (dataL.h78 hG).delta_orth_one (dataL.betaDecomp hG)
  have hΓS_one : ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := gammaGrid_orthogonal_one hG hnoV hyp
  have ha0 : a = 0 := by
    rw [show (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G from rfl, hΔ_one] at ha
    exact_mod_cast ha
  have hb0 : b = 0 := by
    rw [show (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G from rfl, hΓS_one] at hb
    exact_mod_cast hb
  have hzeven : Even z := by rw [ha0, hb0] at heven; simpa using heven
  -- vanishing inner products.
  have hζ_one : ClassFunction.inner (dataL.coh.extension (dataL.zeta 0))
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    rw [← hνζ]; exact (dataL.h78 hG).zetaImage_orth_one (dataL.betaDecomp hG)
  have hζ_eta : ClassFunction.inner (dataL.coh.extension (dataL.zeta 0))
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩) = 0 :=
    coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
      (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) _ _
  have h_one_ext : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (dataL.coh.extension (dataL.zeta 0)) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hζ_one, star_zero]
  have h_eta_ext : ClassFunction.inner (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩)
      (dataL.coh.extension (dataL.zeta 0)) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hζ_eta, star_zero]
  have hone_eta : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩) = 0 := by
    have h00 : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ := by
      rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl
    rw [h00, OddOrder.Peterfalvi.S16.eta_orthonormal hyp,
      if_neg (by rintro ⟨-, h2⟩; exact absurd (congrArg Fin.val h2) (by simp))]
  have hone_one : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 1 :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one
  -- reversed-direction pieces.
  have h_one_ΓS : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (GammaGrid hG hyp) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hΓS_one, star_zero]
  have h_ζext_ΓS : ClassFunction.inner (dataL.coh.extension (dataL.zeta 0))
      (GammaGrid hG hyp) = (nS : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hnS,
      star_intCast]
  -- `⟨Δ_L, η_{01}⟩ = ⟨β_L^τ, η_{01}⟩ = nL`.
  have hΔ_eta : ClassFunction.inner (dataL.h78 hG).delta
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩) = (nL : ℂ) := by
    rw [hΔ, ClassFunction.inner_add_left, ClassFunction.inner_sub_left, hone_eta, hζ_eta,
      sub_zero, add_zero, hnL]
  -- `⟨β_S^τ, ζ_0^{τ₁}⟩ = ⟨Γ_S, ζ_0^{τ₁}⟩ = nS`.
  have hbS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
      = (nS : ℂ) := by
    rw [hβSdecomp, ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
      hnS, h_one_ext, h_eta_ext, add_zero, sub_zero]
  refine ⟨nS, nL, hbS, by rw [typeIBetaL_zeta0_eq_h78_beta hG dataL]; exact hnL, ?_⟩
  -- degree of the distinguished member.
  have hdeg0 : dataL.zeta 0 (1 : ↥L)
      = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  -- Parity: `0 = ⟨β_L^τ, β_S^τ⟩ = 1 − nS − nL + z`, hence `nS + nL = 1 + z` is odd.
  have hdisj : ClassFunction.inner ((dataL.h78 hG).beta) (tauSbetaGrid hG hyp) = 0 := by
    rw [← typeIBetaL_zeta0_eq_h78_beta hG dataL]
    exact OddOrder.RepresentationTheory.ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_betaS_disjoint_support hG hnoV hyp dataL.typeIHyp _
        (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) hdeg0)
  have hkey : (0 : ℂ) = 1 - (nS : ℂ) - (nL : ℂ) + (z : ℂ) := by
    have e := hdisj
    rw [hβLdecomp, hβSdecomp] at e
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_add_right, ClassFunction.inner_sub_right] at e
    rw [hone_one, hone_eta, h_one_ΓS, hζ_one, hζ_eta, h_ζext_ΓS, hΔ_one, hΔ_eta, ← hz] at e
    linear_combination -e
  have hInt : nS + nL = 1 + z := by
    have h2 : ((nS + nL : ℤ) : ℂ) = ((1 + z : ℤ) : ℂ) := by push_cast; linear_combination hkey
    exact_mod_cast h2
  rw [hInt]
  obtain ⟨k, hk⟩ := hzeven
  exact ⟨k, by omega⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) case (c2) bound**: if `bLeta = ⟨β_L^τ, η_{01}⟩ ≠ 0` (the `η`-parity is odd),
then `p ≤ e`.  The §7.8 residual `Γ_L = betaDecomp.Gamma` has `⟨Γ_L, η_{0j}⟩ = bLeta` for every
`j ≠ 0` (from `beta_eq`, row constancy (13.19.c), and `1/ζ_0^{τ₁}/W_L ⊥ η`), so the Bessel
inequality against `‖Γ_L‖² ≤ e − 1` ((7.8.b) `normEstimates`) over the `p − 1` orthonormal
`η_{0j}` gives `(p − 1)·bLeta² ≤ ‖Γ_L‖² ≤ e − 1`, hence `p − 1 ≤ e − 1`. -/
theorem typeI_caseC_bound_c2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nL : ℤ)
    (hnL : ClassFunction.inner (typeIBetaL dataL.typeIHyp (dataL.zeta 0))
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = (nL : ℂ))
    (hnL0 : nL ≠ 0) :
    hyp.p ≤ ((maxNilpotentNormalHall L).subgroupOf L).index := by
  classical
  haveI := dataL.kernelIn_normal
  have hp0 : (0 : ℕ) < hyp.p := hyp.p_prime.pos
  -- `e = [L:H]` in the two forms.
  have he_eq : (dataL.h78 hG).complementIndex = ((maxNilpotentNormalHall L).subgroupOf L).index := by
    rw [dataL.complementIndex_eq hG]
    congr 1
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  -- degree hypothesis for the row-constancy citation.
  have hdeg0 : dataL.zeta 0 (1 : ↥L)
      = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  -- `Γ_L = β_L^τ − 1 + ζ_0^{τ₁} − a·W_L`.
  have hΓ_eq : (dataL.betaDecomp hG).Gamma
      = (dataL.h78 hG).beta - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        + (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct))
        - ((dataL.betaDecomp hG).a : ℂ) • (dataL.h78 hG).weightedNuSum := by
    rw [(dataL.betaDecomp hG).beta_eq]; abel
  -- `⟨Γ_L, η_{0j}⟩ = nL`  for every `j ≠ 0`.
  have hXη : ∀ (j : Fin hyp.p), (j : ℕ) ≠ 0 →
      ClassFunction.inner (dataL.betaDecomp hG).Gamma (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        = (nL : ℂ) := by
    intro j hj
    -- `⟨β_L^τ, η_{0j}⟩ = ⟨β_L^τ, η_{01}⟩ = nL`  (row constancy).
    have hβη : ClassFunction.inner ((dataL.h78 hG).beta) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        = (nL : ℂ) := by
      rw [← typeIBetaL_zeta0_eq_h78_beta hG dataL,
        typeIBetaL_eta_row_constant hG hnoV hyp dataL.typeIHyp (dataL.zeta 0)
          (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) hdeg0 j
          ⟨1, by have := hyp.three_le_p; omega⟩ hj (by simp), hnL]
    -- `⟨1, η_{0j}⟩ = 0`  (`η_{00} = 1`, orthonormal).
    have h1η : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [show OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ by
        rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp,
        if_neg (by rintro ⟨-, h2⟩; exact hj (congrArg Fin.val h2).symm)]
    -- `⟨ζ_0^{τ₁}, η_{0j}⟩ = 0`  (coherent image `⊥ η`).
    have hζη : ClassFunction.inner
        ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct)))
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [show (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct))
          = dataL.coh.extension (dataL.zeta 0) from rfl]
      exact coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
        (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) _ _
    -- `⟨W_L, η_{0j}⟩ = 0`  (each coherent image `⊥ η`).
    have hWη : ClassFunction.inner ((dataL.h78 hG).weightedNuSum)
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [show (dataL.h78 hG).weightedNuSum
          = ∑ i ∈ (Finset.univ.erase (dataL.h78 hG).ind1H),
              ((dataL.h78 hG).hyp76.zeta i (1 : ↥L) /
                ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct) (1 : ↥L) *
                  ClassFunction.inner ((dataL.h78 hG).hyp76.zeta i)
                    ((dataL.h78 hG).hyp76.zeta i))) •
                (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i) from rfl,
        inner_sum_left _ _ _]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [ClassFunction.inner_smul_left,
        show (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)
          = dataL.coh.extension (dataL.zeta i) from rfl,
        coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
          (dataL.zeta_mem_Sset (by
            rw [← dataL.h78_ind1H_eq hG]; exact (Finset.mem_erase.mp hi).1)) _ _, mul_zero]
    rw [hΓ_eq, ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
      ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hβη, h1η, hζη, hWη,
      mul_zero, sub_zero, add_zero, sub_zero]
  -- Bessel bridge over the `p − 1` orthonormal `η_{0j}` (`j ≠ 0`).
  set B : Finset (Fin hyp.p) := Finset.univ.erase ⟨0, hyp.p_prime.pos⟩ with hB
  have hcardB : B.card = hyp.p - 1 := by
    rw [hB, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hbound := (dataL.normEstimates hG).gamma_norm_sq_le (dataL.smallIndex hG)
  have happly := OddOrder.Peterfalvi.S09.sum_rat_weights_le_of_orthogonal_integer_decomposition
    (ι := Fin hyp.p) B (fun j => hyp.eta ⟨0, hyp.q_prime.pos⟩ j) (fun _ => nL) (fun _ => (1 : ℚ))
    ((dataL.betaDecomp hG).Gamma)
    ((dataL.betaDecomp hG).Gamma
      - ∑ j ∈ B, (((nL : ℝ) : ℂ)) • hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
    (((dataL.h78 hG).complementIndex : ℚ) - 1)
    (by abel)
    (fun i _ j _ => by
      rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp]
      by_cases hij : i = j
      · rw [if_pos ⟨rfl, hij⟩, if_pos hij]; norm_num
      · rw [if_neg (fun h => hij h.2), if_neg hij])
    (fun j hj => by
      have hj0 : (j : ℕ) ≠ 0 := by
        rintro h0; exact (Finset.mem_erase.mp hj).1 (Fin.ext h0)
      rw [ClassFunction.inner_sub_left, inner_sum_left,
        Finset.sum_eq_single_of_mem j hj (fun k _ hkj => by
          rw [ClassFunction.inner_smul_left,
            OddOrder.Peterfalvi.S16.eta_orthonormal hyp,
            if_neg (by rintro ⟨-, h2⟩; exact hkj h2), mul_zero]),
        ClassFunction.inner_smul_left,
        OddOrder.Peterfalvi.S16.eta_orthonormal hyp, if_pos ⟨rfl, rfl⟩, mul_one,
        hXη j hj0]
      push_cast; ring)
    (fun _ _ => by norm_num)
    (fun _ _ => hnL0)
    (by
      calc (ClassFunction.inner ((dataL.betaDecomp hG).Gamma)
              ((dataL.betaDecomp hG).Gamma)).re
          = (dataL.h78 hG).gammaNormSq (dataL.betaDecomp hG) := rfl
        _ ≤ ((dataL.h78 hG).complementIndex : ℝ) - 1 := hbound
        _ = (((((dataL.h78 hG).complementIndex : ℚ) - 1 : ℚ)) : ℝ) := by push_cast; ring)
  -- `∑ 1 = p − 1 ≤ e − 1`, hence `p ≤ e`.
  rw [Finset.sum_const, hcardB, nsmul_eq_mul, mul_one] at happly
  have hpe : ((hyp.p : ℚ) - 1) ≤ ((dataL.h78 hG).complementIndex : ℚ) - 1 := by
    have : ((hyp.p - 1 : ℕ) : ℚ) = (hyp.p : ℚ) - 1 := by
      rw [Nat.cast_sub hp0]; norm_num
    rwa [this] at happly
  rw [← he_eq]
  have : (hyp.p : ℚ) ≤ ((dataL.h78 hG).complementIndex : ℚ) := by linarith
  exact_mod_cast this

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`φ`-invariance identity** for the (13.19.c) dichotomy: for a degree-`e` member
`φ ∈ 𝓛`, the coherent-image difference equals the `β_L^τ` difference,
`φ^{τ₁} − ζ_0^{τ₁} = β_L^τ(ζ_0) − β_L^τ(φ)`.  Both sides are `τ₁(φ − ζ_0)`: `φ = ζ_k` with
`d_k = 1` (equal degree, `exists_zeta_index_of_mem_Sset` + `zeta_deg`), so `φ − ζ_0` is
`A(L)`-supported (`psi_support`), where the coherent extension agrees with `τ = typeIHyp.tau`
(`extends_on_supported`); and `β_L^τ(ζ_0) − β_L^τ(φ) = τ(Ind − ζ_0) − τ(Ind − φ) = τ(φ − ζ_0)`
by linearity.  This is the sole bridge from the `ζ_0`-based parity core/case bounds to the
producer's arbitrary degree-`e` `φ`. -/
theorem coh_extension_sub_zeta0_eq_typeIBetaL_sub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    dataL.coh.extension φ - dataL.coh.extension (dataL.zeta 0)
      = typeIBetaL dataL.typeIHyp (dataL.zeta 0) - typeIBetaL dataL.typeIHyp φ := by
  classical
  haveI := dataL.kernelIn_normal
  obtain ⟨k, hk_ne, hkφ⟩ := exists_zeta_index_of_mem_Sset hG dataL hφ
  -- `ζ_0(1) = e`, hence `d_k = 1` (equal degree).
  have hζ01 : dataL.zeta 0 (1 : ↥L) = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  have hidx_ne : (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hdk1 : dataL.d k = 1 := by
    have hzk := dataL.zeta_deg k
    rw [hkφ, hdeg, hζ01] at hzk
    have hmul : dataL.d k * (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)
        = 1 * (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
      rw [one_mul]; exact hzk.symm
    exact mul_right_cancel₀ hidx_ne hmul
  -- `φ − ζ_0 ∈ zSupportedSpan 𝓛 A`.
  have hmem : (φ - dataL.zeta 0) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan dataL.typeIHyp.Sset dataL.typeIHyp.A := by
    refine (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff).mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hφ)
        (Submodule.subset_span (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero))), ?_⟩
    have hval : φ - dataL.zeta 0 = dataL.zeta k - dataL.d k • dataL.zeta 0 := by
      rw [hkφ, hdk1, one_smul]
    rw [hval]
    exact dataL.psi_support hG k
  -- Both sides equal `τ(φ − ζ_0)`.
  have hR : dataL.coh.extension φ - dataL.coh.extension (dataL.zeta 0)
      = dataL.typeIHyp.tau (φ - dataL.zeta 0) := by
    rw [← map_sub]; exact dataL.coh.extends_on_supported _ hmem
  have hL : typeIBetaL dataL.typeIHyp (dataL.zeta 0) - typeIBetaL dataL.typeIHyp φ
      = dataL.typeIHyp.tau (φ - dataL.zeta 0) := by
    simp only [typeIBetaL]
    rw [← map_sub]
    congr 1
    abel
  rw [hR, hL]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) `β_S`-pairing `φ`-invariance**: `(β_S^τ, φ^{τ₁}) = (β_S^τ, ζ_0^{τ₁})` for any
degree-`e` member `φ ∈ 𝓛`.  The difference is `(β_S^τ, β_L^τ(ζ_0) − β_L^τ(φ))`
(`coh_extension_sub_zeta0_eq_typeIBetaL_sub`), and each `(β_S^τ, β_L^τ(ψ))` vanishes by the
(13.19.a) support disjointness (`typeIBetaL_betaS_disjoint_support`). -/
theorem tauSbetaGrid_inner_coh_extension_eq_zeta0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension φ)
      = ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0)) := by
  classical
  haveI := dataL.kernelIn_normal
  have hζ01 : dataL.zeta 0 (1 : ↥L) = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  have hid := coh_extension_sub_zeta0_eq_typeIBetaL_sub hG dataL φ hφ hdeg
  rw [← sub_eq_zero, ← ClassFunction.inner_sub_right, hid, ClassFunction.inner_sub_right,
    ClassFunction.inner_eq_zero_of_disjoint_support
      (Disjoint.symm (typeIBetaL_betaS_disjoint_support hG hnoV hyp dataL.typeIHyp _
        (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) hζ01)),
    ClassFunction.inner_eq_zero_of_disjoint_support
      (Disjoint.symm (typeIBetaL_betaS_disjoint_support hG hnoV hyp dataL.typeIHyp _ hφ hdeg)),
    sub_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) `β_L`-`η`-pairing `φ`-invariance**: `(β_L^τ(φ), η_{0j}) = (β_L^τ(ζ_0), η_{0j})`
for any degree-`e` member `φ ∈ 𝓛`.  The difference is `(β_L^τ(φ) − β_L^τ(ζ_0), η_{0j})`, and
`β_L^τ(φ) − β_L^τ(ζ_0) = ζ_0^{τ₁} − φ^{τ₁}` (`coh_extension_sub_zeta0_eq_typeIBetaL_sub`);
each coherent image is `⊥ η` ((13.19.b) `coherent_extension_orthogonal_eta_of_mem_Sset`). -/
theorem typeIBetaL_inner_eta_eq_zeta0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) (j : Fin hyp.p) :
    ClassFunction.inner (typeIBetaL dataL.typeIHyp φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
      = ClassFunction.inner (typeIBetaL dataL.typeIHyp (dataL.zeta 0))
          (hyp.eta ⟨0, hyp.q_prime.pos⟩ j) := by
  classical
  have hid := coh_extension_sub_zeta0_eq_typeIBetaL_sub hG dataL φ hφ hdeg
  have hid' : typeIBetaL dataL.typeIHyp φ - typeIBetaL dataL.typeIHyp (dataL.zeta 0)
      = dataL.coh.extension (dataL.zeta 0) - dataL.coh.extension φ := by
    rw [show (typeIBetaL dataL.typeIHyp φ - typeIBetaL dataL.typeIHyp (dataL.zeta 0))
        = -(typeIBetaL dataL.typeIHyp (dataL.zeta 0) - typeIBetaL dataL.typeIHyp φ) from
          (neg_sub _ _).symm,
      ← hid, neg_sub]
  rw [← sub_eq_zero, ← ClassFunction.inner_sub_left, hid', ClassFunction.inner_sub_left,
    coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
      (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) _ _,
    coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _ hφ _ _, sub_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`(β_S^τ, ζ_i^{τ₁}) = d_i·bSphi`** (`i ≠ ind1H`): the `β_S^τ`-pairing is constant along the
`L`-family up to degree.  For `i ≠ 0` the difference `ζ_i^{τ₁} − d_i ζ_0^{τ₁} = τ(ζ_i − d_i ζ_0)`
(`hagree`) is an `Ã(L)`-supported Dade image, disjoint from `supp β_S^τ` ((13.19.a)); for `i = 0`
it is `bSphi` (`d_0 = 1`). -/
theorem inner_tauSbetaGrid_coh_ext_zeta_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta i))
      = dataL.d i * (nS : ℂ) := by
  classical
  haveI := dataL.kernelIn_normal
  by_cases hi0 : i = 0
  · subst hi0
    rw [dataL.d_zero_eq_one, one_mul]; exact hnS
  · have hsupp : (dataL.coh.extension (dataL.zeta i)
        - dataL.d i • dataL.coh.extension (dataL.zeta 0)).support
        ⊆ dataL.typeIHyp.dadeData.dade.dadeSupport := by
      have hagree := dataL.hagree hG i hi0 hi
      rw [← hagree]
      intro g hg
      rw [ClassFunction.mem_support] at hg
      by_contra hgnot
      have hdade := (dataL.typeIHyp.dadeData.dade.fullDadeIsometryData
        dataL.typeIHyp.hconj).toDadeIsometryData.isDadeMap
      exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)
    have hzero : ClassFunction.inner (tauSbetaGrid hG hyp)
        (dataL.coh.extension (dataL.zeta i)
          - dataL.d i • dataL.coh.extension (dataL.zeta 0)) = 0 := by
      apply ClassFunction.inner_eq_zero_of_disjoint_support
      rw [tauSbetaGrid]
      exact (dadeSupport_betaGrid_disjoint_support hG hnoV hyp dataL.typeIHyp _ hsupp
        ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)).symm
    rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
      dataL.d_star, hnS, sub_eq_zero] at hzero
    exact hzero

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`(Γ_S, ζ_i^{τ₁}) = bSphi·d_i`** (`i ≠ ind1H`): the `η`-orthogonal residual `Γ_S = GammaGrid`
pairs with the `L`-family exactly as `β_S^τ` does — `Γ_S = β_S^τ − 1 + η_{01}` (`gammaGrid_defGamma`),
and the `1_G`/`η_{01}` parts are orthogonal to the coherent image (`(betaDecomp).orth_one`,
(13.19.b)). -/
theorem inner_gammaGrid_coh_ext_zeta_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner (GammaGrid hG hyp) (dataL.coh.extension (dataL.zeta i))
      = (nS : ℂ) * dataL.d i := by
  classical
  have hGdecomp : GammaGrid hG hyp = tauSbetaGrid hG hyp
      - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
    have h := gammaGrid_defGamma hG hnoV hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)
    rw [tauSbetaGrid, ← h]
  have hi_h78 : i ≠ (dataL.h78 hG).ind1H := by rw [dataL.h78_ind1H_eq]; exact hi
  have h1 : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (dataL.coh.extension (dataL.zeta i)) = 0 := by
    rw [show dataL.coh.extension (dataL.zeta i)
        = (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i) from rfl,
      OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm,
      (dataL.betaDecomp hG).orth_one i hi_h78, star_zero]
  have hη : ClassFunction.inner
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (dataL.coh.extension (dataL.zeta i)) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm,
      coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
        (dataL.zeta_mem_Sset hi) _ _,
      star_zero]
  rw [hGdecomp, ClassFunction.inner_add_left, ClassFunction.inner_sub_left, h1, hη,
    inner_tauSbetaGrid_coh_ext_zeta_eq hG hnoV hyp dataL nS hnS hi, sub_zero, add_zero, mul_comm]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) case (c1) bound**: if `bSphi = (β_S^τ, ζ_0^{τ₁}) ≠ 0` (the S-parity is odd),
then `(|H| − 1)/e ≤ (u − 1)/q`.  The `η`-orthogonal projection `Y = bSphi·Σ d_i ζ_i^{τ₁}` of
`Γ_S = GammaGrid` (coefficients `(Γ_S, ζ_i^{τ₁}) = bSphi·d_i`,
`inner_gammaGrid_coh_ext_zeta_eq`) satisfies the (13.18.d) bound `‖Y‖² ≤ (u−1)/q`
(`gammaGrid_Y_norm_bound`); with `‖Y‖² = bSphi²·Σ d_i²`, `Σ d_i² = (|H|−1)/e`
(`card_index_mul_sum_induced_family_degree_sq`), and `bSphi² ≥ 1`, this gives the bound.
Mirror of the M-side `bessel_bound_of_inner_beta_zeta_ne_zero` (S16_PairingBessel). -/
theorem typeI_caseC_bound_c1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    (hnS0 : nS ≠ 0) :
    (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
      ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) := by
  classical
  haveI := dataL.kernelIn_normal
  -- index/card bridges to `kernelIn`.
  have he_eq : (dataL.kernelIn).index = ((maxNilpotentNormalHall L).subgroupOf L).index := by
    show ((dataL.typeIHyp.typeI.typeF.H).subgroupOf L).index = _
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  have hcard_eq : Nat.card ↥dataL.kernelIn = Nat.card ↥dataL.typeIHyp.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv
  -- the weighted `L`-family vector `v = Σ d_i ζ_i^{τ₁}`.
  set v : ClassFunction G ℂ := ∑ i ∈ Finset.univ.erase dataL.ind1H,
    dataL.d i • dataL.coh.extension (dataL.zeta i) with hvdef
  -- orthonormality of the `ζ_i^{τ₁}`.
  have hON : ∀ i ∈ Finset.univ.erase dataL.ind1H, ∀ j ∈ Finset.univ.erase dataL.ind1H,
      ClassFunction.inner (dataL.coh.extension (dataL.zeta i))
        (dataL.coh.extension (dataL.zeta j)) = if i = j then 1 else 0 := by
    intro i hi j hj
    rw [dataL.nu_isometry i j (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact IsIrreducibleCharacter.inner_self_eq_one
        (dataL.zeta_irreducible_at hG (Finset.mem_erase.mp hi).1)
    · rw [if_neg hij]
      exact OddOrder.Peterfalvi.S09.Cert.induce_family_orthogonal_of_injective dataL.kernelIn dataL.θ dataL.inj i j hij
  -- `⟨v, v⟩ = Σ d_i²`.
  have hvv : ClassFunction.inner v v
      = ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hvdef, inner_sum_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ClassFunction.inner_smul_left, inner_sum_right,
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
        rw [OddOrder.RepresentationTheory.inner_smul_right, hON i hi j hj,
          if_neg (Ne.symm hji), mul_zero]),
      OddOrder.RepresentationTheory.inner_smul_right, hON i hi i hi, if_pos rfl,
      dataL.d_star, mul_one, sq]
  -- `Σ d_i² = (|kernelIn| − 1)/e`  (degree-square sum).
  have hidx_ne : ((dataL.kernelIn).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hdeg_sum := card_index_mul_sum_induced_family_degree_sq dataL.hFrob dataL.θ
    dataL.ind1H dataL.triv dataL.inj dataL.cover
  have hSval : ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2
      = ((Nat.card ↥dataL.kernelIn : ℂ) - 1) / ((dataL.kernelIn).index : ℂ) := by
    rw [eq_div_iff hidx_ne, mul_comm]
    exact hdeg_sum
  -- `⟨GammaGrid, v⟩ = nS·Σ d_i²`.
  have hGv : ClassFunction.inner (GammaGrid hG hyp) v
      = (nS : ℂ) * ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hvdef, inner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [OddOrder.RepresentationTheory.inner_smul_right, dataL.d_star,
      inner_gammaGrid_coh_ext_zeta_eq hG hnoV hyp dataL nS hnS (Finset.mem_erase.mp hi).1, sq]
    ring
  -- the projection `Y = nS • v` and the complement `X = GammaGrid − Y`.
  set Y : ClassFunction G ℂ := (nS : ℂ) • v with hYdef
  -- `Y ⊥ η`.
  have hYeta : ∀ (a : Fin hyp.q) (b : Fin hyp.p), ClassFunction.inner Y (hyp.eta a b) = 0 := by
    intro a b
    rw [hYdef, hvdef, ClassFunction.inner_smul_left, inner_sum_left]
    rw [Finset.sum_eq_zero fun i hi => by
      rw [ClassFunction.inner_smul_left,
        coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
          (dataL.zeta_mem_Sset (Finset.mem_erase.mp hi).1) a b, mul_zero], mul_zero]
  -- `⟨Y, Y⟩ = nS²·Σ d_i²`.
  have hYY : ClassFunction.inner Y Y
      = (nS : ℂ) ^ 2 * ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hYdef, ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hvv, show star ((nS : ℂ)) = (nS : ℂ) by simp]
    ring
  -- `⟨GammaGrid − Y, Y⟩ = 0`.
  have hXY : ClassFunction.inner (GammaGrid hG hyp - Y) Y = 0 := by
    rw [ClassFunction.inner_sub_left, hYY, hYdef,
      OddOrder.RepresentationTheory.inner_smul_right, hGv,
      show star ((nS : ℂ)) = (nS : ℂ) by simp]
    ring
  -- the (13.18.d) bound.
  have hbound := gammaGrid_Y_norm_bound hG hnoV hyp (GammaGrid hG hyp - Y) Y (by abel) hXY hYeta
  -- the real value `Sr = (|kernelIn| − 1)/e` of `Σ d_i²`.
  set Sr : ℝ := ((Nat.card ↥dataL.kernelIn : ℝ) - 1) / ((dataL.kernelIn).index : ℝ) with hSrdef
  have hSc : (∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2) = (Sr : ℂ) := by
    rw [hSval, hSrdef]; push_cast; ring
  have hYYre : (ClassFunction.inner Y Y).re = (nS : ℝ) ^ 2 * Sr := by
    rw [hYY, hSc,
      show (nS : ℂ) ^ 2 * (Sr : ℂ) = (((nS : ℝ) ^ 2 * Sr : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [hYYre] at hbound
  -- positivity facts.
  have hidx_pos : (0 : ℝ) < ((dataL.kernelIn).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcard1 : (1 : ℝ) ≤ (Nat.card ↥dataL.kernelIn : ℝ) := by exact_mod_cast Nat.card_pos
  have hSr_nonneg : (0 : ℝ) ≤ Sr := by
    rw [hSrdef]; exact div_nonneg (by linarith) hidx_pos.le
  have hnS_sq : (1 : ℝ) ≤ (nS : ℝ) ^ 2 := by
    have hint : (1 : ℤ) ≤ nS ^ 2 := by
      nlinarith [Int.one_le_abs hnS0, sq_abs nS]
    exact_mod_cast hint
  -- `Sr ≤ nS²·Sr = ‖Y‖² ≤ (u−1)/q`.
  have hfinal_R : Sr ≤ (((hyp.u : ℚ) - 1) / (hyp.q : ℚ) : ℝ) :=
    le_trans (le_mul_of_one_le_left hSr_nonneg hnS_sq) hbound
  -- `1 ≤ u` (from `|U| = u·c`).
  have hu_pos : 1 ≤ hyp.u := by
    have hcard : 0 < Nat.card ↥hyp.U := Nat.card_pos
    rw [hyp.card_U_eq_uc] at hcard
    rcases Nat.eq_zero_or_pos hyp.u with h0 | h0
    · rw [h0, zero_mul] at hcard; exact absurd hcard (lt_irrefl 0)
    · exact h0
  -- cast the ℝ inequality back to the ℚ goal (through `kernelIn`).
  rw [← hcard_eq, ← he_eq]
  have hcard_ne : 1 ≤ Nat.card ↥dataL.kernelIn := Nat.card_pos
  have goal_R : ((((Nat.card ↥dataL.kernelIn - 1 : ℕ) : ℚ)
        / ((dataL.kernelIn).index : ℚ)) : ℝ)
      ≤ ((((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) : ℝ) := by
    have e1 : ((((Nat.card ↥dataL.kernelIn - 1 : ℕ) : ℚ)
        / ((dataL.kernelIn).index : ℚ)) : ℝ) = Sr := by
      rw [hSrdef, Nat.cast_sub hcard_ne]; push_cast; ring
    have e2 : ((((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) : ℝ)
        = (((hyp.u : ℚ) - 1) / (hyp.q : ℚ) : ℝ) := by
      rw [Nat.cast_sub hu_pos]; push_cast; ring
    rw [e1, e2]; exact hfinal_R
  exact_mod_cast goal_R

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) S-side dichotomy**: `(Γ_S, φ^{τ₁}) + (Γ_L, η_{01}) ≡ 1 (mod 2)` (from
`0 = (β_L^τ, β_S^τ)` via (13.19.a)/(13.18.a) and the evenness of `(Γ_L, Γ_S)` ((13.18.c)+(1.1))),
so one of (c1) `(β_S^τ, φ^{τ₁}) ≡ 1` — in which case (13.18.d) with `Γ_S`'s `𝓛^{τ₁}`-expansion
bounds `(|H|−1)/e = Σaᵢ² ≤ (u−1)/q` — or (c2) `(β_L^τ, η_{0j}) ≡ 1`, in which case the
`η`-coefficient parity forces `p ≤ e`.

Assembled from the `ζ_0`-based parity core (`typeI_caseC_parity`) and case bounds
(`typeI_caseC_bound_c1`/`typeI_caseC_bound_c2`) via the two `φ`-invariance bridges
(`tauSbetaGrid_inner_coh_extension_eq_zeta0`, `typeIBetaL_inner_eta_eq_zeta0`) and the
row constancy (`typeIBetaL_eta_row_constant`): `Odd (nS + nL)` dispatches to (c1) when `nS`
is odd, else `nL` is odd and (c2) holds. -/
theorem typeI_caseC_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ dataL.typeIHyp.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (OddIntegerInner (tauSbetaGrid _hG hyp) (dataL.coh.extension φ) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
          / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))) ∨
      ((∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner (typeIBetaL dataL.typeIHyp φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧
        hyp.p ≤ ((maxNilpotentNormalHall L).subgroupOf L).index) := by
  classical
  obtain ⟨nS, nL, hnS, hnL, hodd⟩ := typeI_caseC_parity _hG hnoV hyp dataL
  by_cases hSodd : Odd nS
  · -- case (c1): the S-pairing `(β_S^τ, φ^{τ₁})` is odd.
    -- ambient bridge (built before the instance-quantifier `intro`, to avoid re-elaboration).
    have hbridge : ClassFunction.inner (tauSbetaGrid _hG hyp) (dataL.coh.extension φ) = (nS : ℂ) :=
      (tauSbetaGrid_inner_coh_extension_eq_zeta0 _hG hnoV hyp dataL φ _hφ _hdeg).trans hnS
    refine Or.inl ⟨⟨nS, hSodd, ?_⟩, typeI_caseC_bound_c1 _hG hnoV hyp dataL nS hnS
      (by rintro rfl; obtain ⟨m, hm⟩ := hSodd; omega)⟩
    intro _ _
    convert hbridge using 2 <;> first | rfl | exact Subsingleton.elim _ _
  · -- case (c2): `nS` even, so `nL` is odd and `p ≤ e`.
    have hLodd : Odd nL := by
      rw [Int.not_odd_iff_even] at hSodd
      obtain ⟨a, ha⟩ := hSodd
      obtain ⟨b, hb⟩ := hodd
      exact ⟨b - a, by omega⟩
    have hnL0 : nL ≠ 0 := by rintro rfl; obtain ⟨m, hm⟩ := hLodd; omega
    -- ambient bridge: `(β_L^τ(φ), η_{0j}) = nL` for every `j ≠ 0` (row constancy + `φ`-invariance).
    have hbridge : ∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        ClassFunction.inner (typeIBetaL dataL.typeIHyp φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = (nL : ℂ) := by
      intro j hj
      rw [typeIBetaL_eta_row_constant _hG hnoV hyp dataL.typeIHyp φ _hφ _hdeg j
          ⟨1, by have := hyp.three_le_p; omega⟩ hj (by norm_num),
        typeIBetaL_inner_eta_eq_zeta0 _hG hnoV hyp dataL φ _hφ _hdeg
          ⟨1, by have := hyp.three_le_p; omega⟩]
      exact hnL
    refine Or.inr ⟨fun j hj => ⟨nL, hLodd, ?_⟩,
      typeI_caseC_bound_c2 _hG hnoV hyp dataL nL hnL hnL0⟩
    intro _ _
    convert hbridge j hj using 2 <;> first | rfl | exact Subsingleton.elim _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) T-side dichotomy** (S↔T swapped): the `typeI_caseC_dichotomy` instance at
`hyp.swap` — the swap's `tauSbetaGrid` is definitionally `tauTbetaGrid` (both are the
`'A0(T)`-Dade image of `Ind_{QW₂}^T 1 − ν_{10}`), its `u/q` are `v/p`, and its `η`-row-`0`
axis is the `η`-column-`0` axis.  Requires the `Tdata` reconciliations (supplied by the
producer from `reconciled_typePData_T`), so the swap's `A₀(T)`-carrier matches the one in
`tauTbetaGrid`'s statement.  The swap's structural input `IsMulCommutative ↥V` (13.2.a at `T`)
is derived here from `hT2` via the BG type dictionary (`proposition_type_classification` (b))
and `isMulCommutative_V` (issue 9096 bundle split). -/
theorem typeI_caseC_dual_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T) (Tdata : TypePData hyp.T)
    (hU : Tdata.U = hyp.V) (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ dataL.typeIHyp.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (OddIntegerInner (tauTbetaGrid _hG hyp hT2 Tdata) (dataL.coh.extension φ) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
          / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))) ∨
      ((∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner (typeIBetaL dataL.typeIHyp φ) (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧
        hyp.q ≤ ((maxNilpotentNormalHall L).subgroupOf L).index) :=
  typeI_caseC_dichotomy _hG hnoV
    (hyp.swap hT2
      (isMulCommutative_V _hG hyp
        ((OddOrder.BG.Ch4.S16.proposition_type_classification _hG hyp.T_maximal).2.1.mpr hT2))
      Tdata hU hW1 hW2 (hyp.nuGridSupply _hG))
    dataL φ _hφ _hdeg

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §13 producer for Peterfalvi (13.19).**  The Tier-A structure — `e = [L:H]`
(definitionally), the family `𝓛 = dataL.typeIHyp.Sset`, a chosen degree-`e` member `φ`
(`exists_Sset_apply_one_eq_index`), and the bridge images `β_L = typeIBetaL`,
`β_S = tauSbetaGrid`, `β_T = tauTbetaGrid` — is genuinely constructed; the (13.19.a)/(13.19.b)
facts are **proven** (`typeIBetaL_betaS_disjoint_support`,
`coherent_extension_orthogonal_eta_of_mem_Sset`); the remaining deep (13.19.c) facts are the
isolated `φ`-parametric obligations above, consumed field-by-field. -/
noncomputable def typeIOrthogonalityGridData_of_coherent78 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) :
    TypeIOrthogonalityGridData hyp dataL :=
  { e := ((maxNilpotentNormalHall L).subgroupOf L).index
    e_eq_index := rfl
    Lset := dataL.typeIHyp.Sset
    phi := Classical.choose (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)
    phi_mem := (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
    phi_degree_eq_e :=
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    betaL := typeIBetaL dataL.typeIHyp
      (Classical.choose (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp))
    betaS := tauSbetaGrid _hG hyp
    betaT := tauTbetaGrid _hG hyp hT2
      (Classical.choose (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp))
    disjoint_support := typeIBetaL_betaS_disjoint_support _hG hnoV hyp dataL.typeIHyp _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    betaL_eq := typeIBetaL_eq_tau_induce_sub dataL.typeIHyp _
    Ltau_orthogonal_eta := coherent_extension_orthogonal_eta_of_mem_Sset _hG hnoV hyp dataL _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
    betaL_eta0_row_constant := typeIBetaL_eta_row_constant _hG hnoV hyp dataL.typeIHyp _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    betaL_eta0_col_constant := typeIBetaL_eta_col_constant _hG hnoV hyp hT2 dataL.typeIHyp _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    caseC := typeI_caseC_dichotomy _hG hnoV hyp dataL _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2
    caseC_dual := typeI_caseC_dual_dichotomy _hG hnoV hyp hT2
      (Classical.choose (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp))
      (Classical.choose_spec (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp)).1
      (Classical.choose_spec (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp)).2.1
      (Classical.choose_spec (OddOrder.Peterfalvi.S15.reconciled_typePData_T _hG hyp)).2.2
      dataL _
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).1
      (Classical.choose_spec (exists_Sset_apply_one_eq_index _hG hnoV dataL.typeIHyp)).2 }

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19)**: a type-I maximal subgroup has `𝓛^{τ₁}` orthogonal to the `eta_ij`,
`(β_L^τ, η_{0j})` constant along each zero axis, and on each zero axis one of the two (13.19.c)
cases — the faithful conjunction forms `(c1) = parity ∧ degree bound` and
`(c2) = η-axis odd-parity ∧ p ≤ e` — holds.

De-opacified (W3 §15): the honest §14 content — the (12.6) coherence bundle
`S16.TypeICoherent78Data L` (`TypeICoherent78Data.nonempty`) with its (12.1) Dade setup
`typeISetup = dataL.typeIHyp` and genuine coherent extension `τ₁ = dataL.coh.extension` —
is constructed here;
the opaque `Prop` fields of `TypeIOrthogonalityData` are instantiated to the **genuine** (13.19)
statements.  `betaL_eta_independent` is instantiated to the faithful (13.19.c) first clause — the
zero-axis **constancy** of `(β_L^τ, η_{0j})`/`(β_L^τ, η_{i0})` (NOT orthogonality: in case (c2)
these inner products are odd).  The dichotomy implication fields (`caseC1_bound`,
`caseC2_eta0j_odd`, dual) are the conjunction projections.  The grid-dependent atoms come from the
faithful producer `typeIOrthogonalityGridData_of_coherent78`, whose type is the genuine (13.19)
grid content. -/
theorem typeI_orthogonality_dichotomy [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L) :
    ∃ data : TypeIOrthogonalityData hyp L,
      data.disjoint_support ∧ data.Ltau_orthogonal_eta ∧
        data.betaL_eta_independent ∧
          (data.caseC1 ∨ data.caseC2) ∧
            (data.caseC1_dual ∨ data.caseC2_dual) := by
  -- (12.1)/(12.6)/(14.*): the type-I maximal `L` carries a genuine coherence bundle.
  obtain ⟨dataL⟩ := OddOrder.Peterfalvi.S16.TypeICoherent78Data.nonempty _hG hnoV hLmax hLI
  -- The grid/Dade atoms and facts (the single deep obligation).
  let g := typeIOrthogonalityGridData_of_coherent78 _hG hnoV hyp hT2 dataL
  -- Assemble `TypeIOrthogonalityData` with the genuine opaque-`Prop` choices and
  -- conjunction-projection dichotomy implication fields.
  refine ⟨{ typeISetup := dataL.typeIHyp
            e := g.e
            e_eq_index := ((maxNilpotentNormalHall L).subgroupOf L).index = g.e
            Lset := g.Lset
            tau1 := dataL.coh.extension
            phi := g.phi
            phi_mem := g.phi_mem
            phi_degree_eq_e := g.phi_degree_eq_e
            betaL := g.betaL
            betaS := g.betaS
            disjoint_support := Disjoint g.betaL.support g.betaS.support
            Ltau_orthogonal_eta :=
              ∀ (i : Fin hyp.q) (j : Fin hyp.p),
                ClassFunction.inner (dataL.coh.extension g.phi) (hyp.eta i j) = 0
            betaL_eta_independent :=
              (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
                  ClassFunction.inner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
                    = ClassFunction.inner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j')) ∧
              (∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
                ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
                  ClassFunction.inner g.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
                    = ClassFunction.inner g.betaL (hyp.eta i' ⟨0, hyp.p_prime.pos⟩))
            caseC1 :=
              OddIntegerInner g.betaS (dataL.coh.extension g.phi) ∧
                (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                  ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))
            caseC2 :=
              (∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ g.e
            caseC2_eta0j_odd := fun h => h.1
            caseC1_bound := fun h => h.2
            caseC1_dual :=
              OddIntegerInner g.betaT (dataL.coh.extension g.phi) ∧
                (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) / (g.e : ℚ) ≤
                  ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))
            caseC2_dual :=
              (∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
                OddIntegerInner g.betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧ hyp.q ≤ g.e
            caseC2_dual_etai0_odd := fun h => h.1
            caseC1_dual_bound := fun h => h.2 },
    g.disjoint_support, g.Ltau_orthogonal_eta,
    ⟨g.betaL_eta0_row_constant, g.betaL_eta0_col_constant⟩, g.caseC, g.caseC_dual⟩

/-! ### Peterfalvi (14.5): exclusion of the small complement `E = W₁`

The (13.17.c) dichotomy leaves two shapes for the `W₁`-containing Frobenius complement `E` of a
type-I maximal `L ⊇ N_G(U)`: `E = W₁` (i.e. `E ≤ Q`) or `|E| = pq`.  The small branch is **not**
excluded at (13.17) — Peterfalvi rules it out only in the §14 endgame: (14.5) applies the
(13.19.c) dichotomy under the `q < p` normalization, and closes with `S` being of type II
(`N_G(U) ⊄ S`).  The earlier repo statement of `complement_not_le_Q` as an unconditional
(13.17)-cluster fact was an over-claim (Coq `FTtypeII_support_facts` (c) keeps the disjunction;
issue-3003 pattern); the faithful (14.5) form and its two consumers live here, downstream of the
(13.19) grid data they consume. -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.5), core exclusion**: under the §14 normalization `q < p` and the type-II
fact `N_G(U) ⊄ S`, the `W₁`-containing Frobenius complement `E` of the type-I maximal
`L ⊇ N_G(U)` is not contained in `Q`.

*Proof (Pf p.87).*  If `E ≤ Q` then `E = E ⊓ Q = W₁` (`complement_inf_Q_eq_W1`), so the
Fitting-kernel index of `L` is `e = |W₁| = q < p`.  The (13.19.c) dichotomy
(`typeIOrthogonalityGridData_of_coherent78`) then cannot hold in case (c2) (which forces
`p ≤ e`), so the (c1) bound `(|H|−1)/e ≤ (u−1)/q` holds with `e = q`, giving `|H| ≤ u`.  With
`U ≤ H` ((13.17.b), hypothesis `hUH`) and `u ≤ |U|` this forces `H = U`, so
`L = H ⋊ E = U W₁ ≤ S` — contradicting `N_G(U) ≤ L` and `N_G(U) ⊄ S`. -/
theorem complement_not_le_Q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    ¬ frob.complement.map L.subtype ≤ hyp.Q := by
  intro hle
  -- `E ≤ Q` collapses `E` to `E ⊓ Q = W₁` (the proven (13.17.c) half)
  have hEW1 : frob.complement.map L.subtype = hyp.W1 := by
    have h := complement_inf_Q_eq_W1 _hG hyp hTTypeII frob hW1E
    rwa [inf_eq_left.mpr hle] at h
  -- hence the Fitting-kernel index of `L` is `|E| = |W₁| = q`
  have hEcard : Nat.card ↥frob.complement = hyp.q := by
    rw [show Nat.card ↥frob.complement
          = Nat.card ↥(frob.complement.map L.subtype) from
        Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
          L.subtype_injective).toEquiv, hEW1]
    exact hyp.q_eq_card_W1.symm
  have hindex : ((maxNilpotentNormalHall L).subgroupOf L).index = hyp.q := by
    rw [typeIFrobenius_kernel_index_eq_complement frob, hEcard]
  -- the (13.19) grid data for `L`
  obtain ⟨dataL⟩ := OddOrder.Peterfalvi.S16.TypeICoherent78Data.nonempty _hG hnoV hLmax hLI
  have hHL : dataL.typeIHyp.H = maxNilpotentNormalHall L := dataL.typeIHyp.typeI.typeF.H_eq
  set g := typeIOrthogonalityGridData_of_coherent78 _hG hnoV hyp hT2 dataL with hgdef
  have he_q : g.e = hyp.q := by rw [← g.e_eq_index, hindex]
  -- case (c2) is impossible: `p ≤ e = q < p`
  rcases g.caseC with ⟨-, hbound⟩ | ⟨-, hpe⟩
  swap
  · rw [he_q] at hpe
    omega
  -- case (c1): `(|H|−1)/q ≤ (u−1)/q` forces `|H| ≤ u ≤ |U| ≤ |H|`, so `H = U`
  rw [he_q] at hbound
  have hq0 : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hle_nat : Nat.card ↥dataL.typeIHyp.H - 1 ≤ hyp.u - 1 := by
    have h : ((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) ≤ ((hyp.u - 1 : ℕ) : ℚ) := by
      have hmul := mul_le_mul_of_nonneg_right hbound hq0.le
      rwa [div_mul_cancel₀ _ hq0.ne', div_mul_cancel₀ _ hq0.ne'] at hmul
    exact_mod_cast h
  have hupos : 0 < hyp.u := by
    rcases Nat.eq_zero_or_pos hyp.u with h0 | h
    · exfalso
      have hcard := hyp.card_U_eq_uc
      rw [h0, Nat.zero_mul] at hcard
      exact absurd hcard Nat.card_pos.ne'
    · exact h
  have hu_le_U : hyp.u ≤ Nat.card ↥hyp.U := by
    rw [hyp.card_U_eq_uc]
    have hc : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
    exact Nat.le_mul_of_pos_right _ hc
  have hU_le_H : Nat.card ↥hyp.U ≤ Nat.card ↥(maxNilpotentNormalHall L) :=
    Subgroup.card_le_of_le hUH
  have hHpos : 0 < Nat.card ↥dataL.typeIHyp.H := Nat.card_pos
  have hcard_eq : Nat.card ↥(maxNilpotentNormalHall L) = Nat.card ↥hyp.U := by
    rw [← hHL] at hU_le_H ⊢
    omega
  have hUeq : maxNilpotentNormalHall L = hyp.U :=
    (Subgroup.eq_of_le_of_card_ge hUH (le_of_eq hcard_eq)).symm
  -- `L = H ⊔ E = U ⊔ W₁ ≤ S`, contradicting `N_G(U) ≤ L` with `N_G(U) ⊄ S`
  have hsup : (maxNilpotentNormalHall L).subgroupOf L ⊔ frob.complement = ⊤ := by
    have h := frob.frobenius.isComplement.sup_eq_top
    rwa [frob.typeI.typeF.H_eq] at h
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by
      rw [hyp.S_deriv_eq_PU]; exact le_sup_right
    exact h1.trans (Subgroup.map_subtype_le _)
  have hW1S : hyp.W1 ≤ hyp.S := by
    have h1 : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    rw [hyp.W_eq_inter] at h1
    exact h1.trans inf_le_left
  have hLS : L ≤ hyp.S := by
    have hLtop : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hLtop, ← hsup, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.subgroupOf_map_subtype]
      refine inf_le_left.trans ?_
      rw [hUeq]
      exact hUS
    · rw [hEW1]
      exact hW1S
  exact hNUS (hNUL.trans hLS)

/-- **Peterfalvi (14.5) order consequence.**  Under the (14.5) hypotheses the `W₁`-containing
Frobenius complement `E` of `L` has order `p q`.

*Proof (Pf p.82/p.87).*  `E ⊆ Q W₂` (`complement_le_QW2`), and `Q ⋊ W₂` has `Q ◁ Q W₂` with
`[Q W₂ : Q] = |W₂| = p` (`Q_W2_structure`).  The relative index `[E : E ∩ Q]` divides
`[Q W₂ : Q] = p` (normal-subgroup relative index inside `↥(Q W₂)`) and is `≠ 1` by the (14.5)
exclusion `E ⊄ Q` (`complement_not_le_Q`), hence `= p`; with `E ∩ Q = W₁` of order `q`
(`complement_inf_Q_eq_W1`), `|E| = |E ∩ Q| · [E : E ∩ Q] = q p`. -/
theorem complement_card_eq_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q := by
  set Em := frob.complement.map L.subtype with hEm
  set Hg := hyp.Q ⊔ hyp.W2 with hHg
  -- `E ∩ Q = W₁` (proven (13.17.c) half); the (14.5) exclusion `E ⊄ Q`.
  have hInf := complement_inf_Q_eq_W1 _hG hyp hTTypeII frob hW1E
  have hnle := complement_not_le_Q _hG hnoV hyp hTTypeII hT2 hqp hNUS hLmax hLI hNUL hUH frob hW1E
  -- `E ⊆ Q W₂` (Huppert step) and the `Q ⋊ W₂` structure.
  have hEH : Em ≤ Hg := complement_le_QW2 _hG hyp hTTypeII frob hW1E
  obtain ⟨hWnorm, hdisj, _⟩ := Q_W2_structure _hG hyp hTTypeII
  have hQleH : hyp.Q ≤ Hg := le_sup_left
  -- `|E ∩ Q| = |W₁| = q`.
  have hInfCard : Nat.card ↥(Em ⊓ hyp.Q) = hyp.q := by rw [hInf]; exact hyp.q_eq_card_W1.symm
  -- `Q ◁ Q W₂` (as `Q W₂ ≤ N_G(Q)`).
  haveI hQnorm : (hyp.Q.subgroupOf Hg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleH).mpr (sup_le Subgroup.le_normalizer hWnorm)
  -- `|Q W₂| = |Q| · p`.
  have hHcard : Nat.card ↥Hg = Nat.card ↥hyp.Q * hyp.p := by
    have h := OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
      (show hyp.W2 ⊓ hyp.Q = ⊥ by rw [inf_comm]; exact hdisj)
    rw [hHg, sup_comm, h, ← hyp.p_eq_card_W2]
    exact mul_comm _ _
  have hQpos : 0 < Nat.card ↥hyp.Q := Nat.card_pos
  -- `[Q W₂ : Q] = p`.
  have hindexH : (hyp.Q.subgroupOf Hg).index = hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Hg)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleH).toEquiv, hHcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hQpos hmul
  -- `[E : E ∩ Q] = Q.relIndex E` divides `[Q W₂ : Q] = p`, and is `≠ 1` (`E ⊄ Q`), hence `= p`.
  have hdvd : hyp.Q.relIndex Em ∣ hyp.p := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (H := hyp.Q.subgroupOf Hg)
      (K := Em.subgroupOf Hg)
    rwa [Subgroup.relIndex_subgroupOf hEH, hindexH] at h1
  have hne1 : hyp.Q.relIndex Em ≠ 1 := fun h => hnle (Subgroup.relIndex_eq_one.mp h)
  have hrel : hyp.Q.relIndex Em = hyp.p :=
    (hyp.p_prime.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  -- `|E| = |E ∩ Q| · [E : E ∩ Q] = q · p`.
  have hEmcard : Nat.card ↥Em = hyp.q * hyp.p := by
    have hmul := Subgroup.card_mul_index (hyp.Q.subgroupOf Em)
    rw [show (hyp.Q.subgroupOf Em).index = hyp.p from hrel, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.Q ≤ Em)).toEquiv,
      hInfCard] at hmul
    exact hmul.symm
  -- transfer `|E.map| = |E|`.
  rw [show Nat.card ↥frob.complement = Nat.card ↥Em from
    Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv, hEmcard]
  exact mul_comm _ _

/-- **Peterfalvi (14.5), full form**: the `W₁`-containing Frobenius complement of the type-I
subgroup `L` over `N_G(U)` has order `p q` and contains a conjugate `W₂^y` (`y ∈ Q`).

Assembled from the order argument (`complement_card_eq_pq`) and the group-theoretic `∃ y`
extraction (`exists_mem_conj_W2_le_of_dvd_card`, Schur–Zassenhaus), the latter fed `E ⊆ Q W₂`
by the Huppert step (`complement_le_QW2`).  The `W₁ ⊆ E` hypothesis records Peterfalvi's choice
"let `E` be a complement to `H` in `L` such that `W₁ ⊂ E`". -/
theorem typeI_overNormalizer_complement [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S)
    {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G) (hLI : IsTypeI L)
    (hNUL : Subgroup.normalizer (hyp.U : Set G) ≤ L)
    (hUH : hyp.U ≤ maxNilpotentNormalHall L)
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    Nat.card ↥frob.complement = hyp.p * hyp.q ∧
      ∃ y ∈ hyp.Q, (MulAut.conj y • hyp.W2 : Subgroup G) ≤
        frob.complement.map L.subtype := by
  have hcard := complement_card_eq_pq _hG hnoV hyp hTTypeII hT2 hqp hNUS hLmax hLI hNUL hUH
    frob hW1E
  refine ⟨hcard, ?_⟩
  obtain ⟨hWnorm, hdisj, hpQ⟩ := Q_W2_structure _hG hyp hTTypeII
  have hEQW2 := complement_le_QW2 _hG hyp hTTypeII frob hW1E
  -- `Q` is solvable: `Q = T_F ≤ T < ⊤`.
  haveI hQsolv : IsSolvable ↥hyp.Q := by
    have hQT : hyp.Q ≤ hyp.T := by
      rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
    have hTlt : hyp.T < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1
    exact _hG.solvable_of_lt_top hyp.Q (lt_of_le_of_lt hQT hTlt)
  -- `p ∣ |E.map| = |E| = p q`.
  have hpE : hyp.p ∣ Nat.card ↥(frob.complement.map L.subtype) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective frob.complement L.subtype
      L.subtype_injective).toEquiv.symm, hcard]
    exact dvd_mul_right hyp.p hyp.q
  exact exists_mem_conj_W2_le_of_dvd_card hWnorm hQsolv hdisj hyp.p_prime
    hyp.p_eq_card_W2.symm hpQ hEQW2 hpE

/-- **Peterfalvi (14.5), packaged**: if `S` is type II (with the §14 normalization `q < p` and
the type-II consequence `N_G(U) ⊄ S`), a maximal subgroup over `N_G(U)` is type-I Frobenius,
contains `U` in its kernel, and its `W₁`-containing complement has order `p q` with a conjugate
`W₂^y` inside.  Assembled from the type-I existence (13.17.a/b,
`exists_typeI_maximal_overNormalizer_U`), a `W₁`-containing Frobenius decomposition
(`exists_typeIFrobeniusData_W1_le`), and the (14.5) complement structure
(`typeI_overNormalizer_complement`). -/
theorem typeII_overNormalizer_frobenius [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hSTypeII : IsTypeII hyp.S) (hTTypeII : IsTypeII hyp.T)
    (hT2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T)
    (hqp : hyp.q < hyp.p)
    (hNUS : ¬ Subgroup.normalizer (hyp.U : Set G) ≤ hyp.S) :
    ∃ data : TypeIOverNormalizerData hyp,
      data.frobenius.kernel_eq_MF ∧ (hyp.U ≤ data.H) := by
  obtain ⟨L, hLmax, hLtypeI, hNUL, hUH⟩ :=
    exists_typeI_maximal_overNormalizer_U _hG hnoV hyp hSTypeII hTTypeII
  obtain ⟨frob, hker, hW1E⟩ := exists_typeIFrobeniusData_W1_le _hG hnoV hyp hLmax hLtypeI hNUL
  obtain ⟨hcard, hy⟩ := typeI_overNormalizer_complement _hG hnoV hyp hTTypeII hT2 hqp hNUS
    hLmax hLtypeI hNUL hUH frob hW1E
  exact ⟨⟨L, maxNilpotentNormalHall L, hLmax, rfl, hNUL, frob, hUH, hcard, hy⟩, hker, hUH⟩

end OddOrder.Peterfalvi.S15
