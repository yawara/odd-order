/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_PairingCoherence
import OddOrder.GroupTheory.RepresentationTheory.InducedDegreeSum

/-!
# Peterfalvi (14.14), the pairing Bessel bounds

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Section 16, pp. 90--91, proof of (14.14).

Downstream of the (7.9) dichotomy (`S16_PairingCoherence.pairing_dichotomy`), each
branch turns into a size bound.  Say `(β_M, φ^{τ₁}) = a ≠ 0` (the `L`-side family is
paired): every `L`-family member satisfies `(β_M, φ_i^ν) = d_i·a` (the difference
`ψ_i = φ_i − d_iφ` is a Dade image supported in `Ã(L)`, disjoint from
`supp β_M ⊆ Ã(M)`), and the (7.8.a) residual `Γ_M` picks up the same coefficients
(the family-wide cross-orthogonality kills `1_G`, `ζ_M^ν` and the weighted `M`-sum).
Bessel for the orthonormal `{φ_i^ν}` against `‖Γ_M‖² ≤ e_M − 1` ((7.8.b)) then gives

`(h_L − 1)/e_L = Σ d_i² ≤ e_M − 1`,

Peterfalvi's `Σ a_i² = (h−1)/pq ≤ pq − 1` (the degree-square sum is
`card_index_mul_sum_induced_family_degree_sq`).

Main results:

* `TypeICoherent78Data.normEstimates` — the (7.8.b) `NormEstimates` (both the
  `ζ`-lower bound and the residual bound `‖Γ‖² ≤ e − 1`) for the bundle.
* `TypeICoherent78Data.smallIndex` — `2e + 1 ≤ h` (Frobenius, odd order).
* `bessel_bound_of_inner_beta_zeta_ne_zero` — the single-branch Bessel bound.
* `pairing_bounds_of_nonconjugate` — the (14.14) dichotomy of bounds.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S09
open OddOrder.Peterfalvi.S09.Cert
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)
variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- `e = [L : H]` as the `subgroupOf` index (bundle form). -/
theorem complementIndex_eq :
    (data.h78 hG).complementIndex = (data.kernelIn).index :=
  complementIndex_eq_subgroupOf_index (data.h78 hG)

/-- `h = |H|` (bundle form). -/
theorem kernelOrder_eq :
    (data.h78 hG).kernelOrder = Nat.card ↥data.kernelIn := by
  rw [show (data.h78 hG).kernelOrder = Nat.card data.kernel from rfl]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.kernel_le).toEquiv).symm

/-- **`ζ_{ind1H}(1) = e`** (the induced principal degree). -/
theorem zeta_ind1H_apply_one :
    (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) (1 : ↥L)
      = ((data.h78 hG).complementIndex : ℂ) := by
  haveI := data.kernelIn_normal
  rw [data.complementIndex_eq hG]
  change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ) (1 : ↥L)
    = ((data.kernelIn).index : ℂ)
  rw [data.triv]
  exact induce_trivialChar_apply_eq_index data.kernelIn (Subgroup.one_mem _)

/-- **`‖ζ_{ind1H}‖² = e`** (the induced principal norm). -/
theorem zeta_ind1H_normSq :
    ClassFunction.inner ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H))
      ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H))
      = ((data.h78 hG).complementIndex : ℂ) := by
  haveI := data.kernelIn_normal
  rw [data.complementIndex_eq hG]
  change ClassFunction.inner
      (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ))
      (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ))
    = ((data.kernelIn).index : ℂ)
  rw [data.triv]
  exact induce_trivialChar_normSq_eq_index data.kernelIn

/-- **`ζ_0(1) = e`** (the distinguished degree, bundle form). -/
theorem zeta_zero_apply_one :
    (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.h78 hG).complementIndex : ℂ) := by
  rw [data.complementIndex_eq hG]
  exact data.deg0

/-- **The (7.8) source-side norm evaluation** `‖Ind 1_H − ζ‖² = e + 1`. -/
theorem sourceDiffNormEvaluation :
    (data.h78 hG).SourceDiffNormEvaluation := by
  haveI := data.kernelIn_normal
  refine (data.h78 hG).sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
    (data.zeta_ind1H_normSq hG) ?_ ?_ (data.h78_zeta_irreducible hG)
  · exact induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj 0 data.ind1H
      (Ne.symm data.ind1H_ne_zero)
  · exact induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj data.ind1H 0
      data.ind1H_ne_zero

/-- **The (1.5.d) family degree-square sum** in the `star` form consumed by the
(7.8.b) `NormEstimates` producer: `Σ_{i ≠ ind1H} ζ_i(1)·(ζ_i(1))*/‖ζ_i‖² = (h−1)·e`. -/
theorem degree_sum_star :
    (∑ i ∈ (Finset.univ.erase (data.h78 hG).ind1H),
        (data.h78 hG).hyp76.zeta i (1 : ↥L)
          * star ((data.h78 hG).hyp76.zeta i (1 : ↥L)) /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i))
      = (((data.h78 hG).kernelOrder : ℂ) - 1) * ((data.h78 hG).complementIndex : ℂ) := by
  haveI := data.kernelIn_normal
  have hstar : ∀ i ∈ Finset.univ.erase (data.h78 hG).ind1H,
      (data.h78 hG).hyp76.zeta i (1 : ↥L)
          * star ((data.h78 hG).hyp76.zeta i (1 : ↥L)) /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i)
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) ^ 2 /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i) := by
    intro i _
    have hreal : star ((data.h78 hG).hyp76.zeta i (1 : ↥L))
        = (data.h78 hG).hyp76.zeta i (1 : ↥L) := by
      rw [data.h78_zeta_eq]
      exact induce_apply_one_star data.kernelIn (data.θ i)
    rw [hreal, sq]
  have h := family_degree_sum data.kernelIn data.θ data.inj data.cover data.ind1H data.triv
  calc (∑ i ∈ (Finset.univ.erase (data.h78 hG).ind1H),
        (data.h78 hG).hyp76.zeta i (1 : ↥L)
          * star ((data.h78 hG).hyp76.zeta i (1 : ↥L)) /
          ClassFunction.inner ((data.h78 hG).hyp76.zeta i) ((data.h78 hG).hyp76.zeta i))
      = ∑ i ∈ (Finset.univ.erase (data.h78 hG).ind1H),
          (data.h78 hG).hyp76.zeta i (1 : ↥L) ^ 2 /
            ClassFunction.inner ((data.h78 hG).hyp76.zeta i)
              ((data.h78 hG).hyp76.zeta i) := Finset.sum_congr rfl hstar
    _ = ((data.kernelIn).index : ℂ) * ((Nat.card ↥data.kernelIn : ℂ) - 1) := h
    _ = (((data.h78 hG).kernelOrder : ℂ) - 1) * ((data.h78 hG).complementIndex : ℂ) := by
        rw [data.complementIndex_eq hG, data.kernelOrder_eq hG]
        ring

/-- **`2e + 1 ≤ h`** (`smallIndex`): the Frobenius kernel of odd order is more than
twice the complement. -/
theorem smallIndex : (data.h78 hG).smallIndex := by
  haveI := data.kernelIn_normal
  have hKodd : Odd (Nat.card ↥data.kernelIn) :=
    (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)).of_dvd_nat
      (Subgroup.card_subgroup_dvd_card _)
  have hCodd : Odd (Nat.card ↥data.C) :=
    (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)).of_dvd_nat
      (Subgroup.card_subgroup_dvd_card data.C)
  have hfrobB := OddOrder.Peterfalvi.S14.frobenius_two_mul_card_complement_add_one_le_card_kernel
    data.hFrob hKodd hCodd data.hFrob.ne_bot_kernel
  change 2 * (data.h78 hG).complementIndex + 1 ≤ (data.h78 hG).kernelOrder
  have hcompl : Nat.card ↥data.kernelIn * Nat.card ↥data.C = Nat.card ↥L :=
    data.hFrob.isComplement.card_mul_card
  have hce : (data.h78 hG).complementIndex = Nat.card ↥data.C := by
    change Nat.card ↥L / Nat.card data.kernel = Nat.card ↥data.C
    rw [show Nat.card data.kernel = Nat.card ↥data.kernelIn from
        (data.kernelOrder_eq hG) ▸ rfl,
      ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
  rw [data.kernelOrder_eq hG, hce]
  exact hfrobB

/-- `d_{ind1H} = 1` for the constructor-computed `hyp76.d`. -/
theorem hyp76_d_ind1H_eq_one : (data.h78 hG).hyp76.d ((data.h78 hG).ind1H) = 1 := by
  haveI := data.kernelIn_normal
  change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ) (1 : ↥L) /
      ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) = 1
  rw [← data.zeta_deg_match, div_self (induce_apply_one_ne_zero _ (data.θ 0))]

/-- The coherence agreement in constructor-computed `d`/`psiSupp` form (the
`hagree'` input of the `cCoeff` evaluations). -/
theorem hagree_hyp76 (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∀ i : Fin (data.n + 1), i ≠ 0 → i ≠ (data.h78 hG).ind1H →
      (data.h78 hG).hyp76.hyp71.τ ((data.h78 hG).hyp76.psiSupp i)
        = (data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)
          - (data.h78 hG).hyp76.d i • (data.h78 hG).nu ((data.h78 hG).hyp76.zeta 0) := by
  haveI := data.kernelIn_normal
  intro i hi0 hii
  have hz0 : ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (data.θ 0)
  have hdeq : (data.h78 hG).hyp76.d i = data.d i := by
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) = data.d i
    rw [div_eq_iff hz0]; exact data.zeta_deg i
  have hsub : (data.h78 hG).hyp76.psiSupp i
      = (⟨data.zeta i - data.d i • data.zeta 0, data.psi_support hG i⟩ :
        OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ
          (typeIA L data.typeIHyp.typeI) L) := by
    apply Subtype.ext
    change data.zeta i - (data.h78 hG).hyp76.d i • data.zeta 0
      = data.zeta i - data.d i • data.zeta 0
    rw [hdeq]
  rw [hsub, hdeq]
  exact data.hagree hG i hi0 hii

/-- **The (7.8.b) quadratic norm identity** `‖ζ_0^{νρ}‖² = Q(a) + (1 − e/h)` for the
bundle (the `hzeta` input of `NormEstimates`), discharged from the Dade-family facts
exactly as in `zetaNuRhoNormSqGeOfDade`. -/
theorem zetaNuRhoNormSq_eq_normQuad (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).zetaNuRhoNormSq =
      (data.h78 hG).normQuadraticCorrection (data.betaDecomp hG) +
        (1 - ((data.h78 hG).complementIndex : ℝ) / ((data.h78 hG).kernelOrder : ℝ)) := by
  haveI := data.kernelIn_normal
  have hz0 : ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) ≠ 0 :=
    induce_apply_one_ne_zero _ (data.θ 0)
  have hz0_compl : ClassFunction.induce data.kernelIn
      (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) = ((data.h78 hG).complementIndex : ℂ) :=
    data.zeta_zero_apply_one hG
  refine zetaNuRhoNormSq_eq_normQuad_of_facts (data.h78 hG) (data.betaDecomp hG) rfl
    (induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj) ?_ ?_ ?_ ?_ ?_
    (data.zeta_ind1H_normSq hG) (data.zeta_ind1H_apply_one hG) ?_
  · -- `c_{ind1H} = a − 1`.
    rw [cCoeff_nu_zeta_zero_ind1H_eq (data.h78 hG) (data.h78 hG).nu rfl
      (data.hyp76_d_ind1H_eq_one hG)]
    show ClassFunction.inner (data.h78 hG).beta
        ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta 0)) = ((data.betaDecomp hG).a : ℂ) - 1
    have ha := Classical.choose_spec (exists_betaDecomp_a (data.h78 hG)
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (data.θ 0).property.mem_ZIrr))
      (data.coh.extension_mem_ZIrr _ (Submodule.subset_span
        (data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)))))
    have hBDa : ((data.betaDecomp hG).a : ℂ)
        = ClassFunction.inner (data.h78 hG).beta
            ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta 0)) + 1 := ha
    rw [hBDa]; ring
  · -- `c_i = −d_i` for the non-distinguished, non-`ind1H` indices.
    exact fun i hi0 hii => cCoeff_nu_zeta_zero_eq_neg_d (data.h78 hG).hyp76 (data.h78 hG).nu
      (data.hagree_hyp76 hG) (data.h78 hG).nu_isometry (Ne.symm data.ind1H_ne_zero)
      (fun i hi => induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj i 0 hi)
      data.zeta_zero_norm_one i hi0 hii
  · -- `d_i` is real.
    intro i
    change star (ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L))
      = ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L)
    rw [star_div₀, induce_apply_one_star, induce_apply_one_star]
  · -- `ζ_i(1)` is real.
    exact fun i => induce_apply_one_star data.kernelIn (data.θ i)
  · -- `d_i = ζ_i(1)/e`.
    intro i
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) /
        ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L)
      = ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L)
        / ((data.h78 hG).complementIndex : ℂ)
    rw [hz0_compl]
  · -- The `Ioi`-sum `G = e(h−1) − e²`.
    rw [data.complementIndex_eq hG,
      show ((data.h78 hG).kernelOrder : ℂ) = (Nat.card ↥data.kernelIn : ℂ) from by
        rw [data.kernelOrder_eq hG]]
    exact family_degree_sum_Ioi data.kernelIn data.θ data.inj data.cover data.ind1H
      data.ind1H_ne_zero data.triv
      (by rw [← data.complementIndex_eq hG]; exact hz0_compl) data.zeta_zero_norm_one

/-- **The (7.8.b) `NormEstimates` of the bundle**: both the `ζ`-lower bound
`1 − e/h ≤ ‖ζ_0^{νρ}‖²` and the residual bound `‖Γ‖² ≤ e − 1`. -/
theorem normEstimates (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).NormEstimates (data.betaDecomp hG) := by
  haveI := data.kernelIn_normal
  refine (data.h78 hG).normEstimates_of_irreducible_source_data (data.betaDecomp hG)
    (data.sourceDiffNormEvaluation hG) ?_ ?_ (data.zeta_zero_apply_one hG)
    (data.degree_sum_star hG) (data.zetaNuRhoNormSq_eq_normQuad hG)
  · -- Every non-`ind1H` member is irreducible.
    intro i hi
    exact data.zeta_irreducible_at hG (Finset.mem_erase.mp hi).1
  · -- Distinct indices give distinct characters.
    intro i _ j _ hij
    intro heq
    exact hij (data.inj heq)

/-- `d_0 = 1` (the distinguished source is linear: `ζ_0(1) = e = [L:H]·θ_0(1)`). -/
theorem d_zero_eq_one : data.d 0 = 1 := by
  haveI := data.kernelIn_normal
  have h := data.zeta_deg 0
  have hz0 : data.zeta 0 (1 : ↥L) ≠ 0 := induce_apply_one_ne_zero _ (data.θ 0)
  have h2 : data.d 0 * data.zeta 0 (1 : ↥L) = 1 * data.zeta 0 (1 : ↥L) := by
    rw [one_mul, ← h]
  exact mul_right_cancel₀ hz0 h2

/-- `d_i` is a positive natural (the source degree). -/
theorem exists_d_natCast (i : Fin (data.n + 1)) :
    ∃ m : ℕ, 0 < m ∧ data.d i = (m : ℂ) := by
  obtain ⟨m, hm, hcast⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  exact ⟨m, hm, hcast⟩

/-- `star (d_i) = d_i`. -/
theorem d_star (i : Fin (data.n + 1)) : star (data.d i) = data.d i := by
  obtain ⟨m, -, hm⟩ := data.exists_d_natCast i
  rw [hm, star_natCast]

end TypeICoherent78Data

section Pairing

variable [Finite G] {L M : Subgroup G}
variable (dataL : TypeICoherent78Data L) (dataM : TypeICoherent78Data M)
variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

omit [Finite G] in
/-- Left additivity of the inner product over a finite sum. -/
private theorem inner_sum_left' {ι : Type*} [Fintype G] [Invertible (Nat.card G : ℂ)]
    (s : Finset ι) (f : ι → ClassFunction G ℂ) (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (∑ i ∈ s, f i) ψ = ∑ i ∈ s, ClassFunction.inner (f i) ψ := by
  rw [OddOrder.RepresentationTheory.inner_conj_symm, inner_sum_right, star_sum]
  exact Finset.sum_congr rfl fun i _ =>
    (OddOrder.RepresentationTheory.inner_conj_symm ψ (f i)).symm

/-- **The `β`-pairing is constant along the family** (Peterfalvi's
`(β_M^τ, (φ_i − a_iφ)^τ) = 0`): for `i ≠ ind1H` on the `L`-side,
`⟨β_M, φ_i^ν⟩ = d_i·⟨β_M, φ_0^ν⟩` — the difference `ψ_i^{τ₁}` is a Dade image in
`Ã(L)`, disjoint from `supp β_M ⊆ Ã(M)`. -/
theorem inner_beta_nu_zeta_eq
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner ((dataM.h78 hG).beta)
        ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i))
      = dataL.d i * ClassFunction.inner ((dataM.h78 hG).beta)
          ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)) := by
  haveI := dataL.kernelIn_normal
  by_cases hi0 : i = 0
  · subst hi0
    rw [dataL.d_zero_eq_one, one_mul]
    rfl
  -- `⟨β_M, τ₁ψ_i⟩ = 0` by the disjoint Dade supports.
  have hdisj := (hypothesis79OfNonconjugate dataL dataM hG hL hM hnc).dadeSupport_disjoint
  have hpsi_img_supp : ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)
      - dataL.d i • (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)).support
      ⊆ (dataL.h78 hG).hyp76.hyp71.hyp.dadeSupport := by
    have hagree := dataL.hagree hG i hi0 hi
    change (dataL.coh.extension (dataL.zeta i)
      - dataL.d i • dataL.coh.extension (dataL.zeta 0)).support
      ⊆ dataL.typeIHyp.dadeData.dade.dadeSupport
    rw [← hagree]
    intro g hg
    rw [ClassFunction.mem_support] at hg
    by_contra hgnot
    have hdade := (dataL.typeIHyp.dadeData.dade.fullDadeIsometryData
      dataL.typeIHyp.hconj).toDadeIsometryData.isDadeMap
    exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)
  have hzero : ClassFunction.inner ((dataM.h78 hG).beta)
      ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)
        - dataL.d i • (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)) = 0 := by
    apply ClassFunction.inner_eq_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp hdisj.symm
      ((dataM.h78 hG).beta_support_subset_dadeSupport hg₁)
      (hpsi_img_supp hg₂)
  rw [ClassFunction.inner_sub_right,
    OddOrder.RepresentationTheory.inner_smul_right, dataL.d_star, sub_eq_zero] at hzero
  exact hzero

/-- Reversed orientation of `pair_cross_orthogonal`: `⟨χ_j^ν, φ_i^ν⟩ = 0`. -/
theorem pair_cross_orthogonal'
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H)
    {j : Fin (dataM.n + 1)} (hj : j ≠ dataM.ind1H) :
    ClassFunction.inner ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j))
      ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)) = 0 := by
  rw [OddOrder.RepresentationTheory.inner_conj_symm,
    pair_cross_orthogonal dataL dataM hG hL hM hnc hi hj, star_zero]

/-- **The residual `Γ_M` pairs with the `L`-family exactly as `β_M` does**: for
`i ≠ ind1H`, `⟨Γ_M, φ_i^ν⟩ = d_i·a` where `a = ⟨β_M, φ_0^ν⟩` — the `1_G`, `ζ_M^ν`,
and weighted-`M`-sum components of `β_M` are all orthogonal to the `L`-family. -/
theorem inner_gamma_nu_zeta_eq
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner ((dataM.betaDecomp hG).Gamma)
        ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i))
      = dataL.d i * ClassFunction.inner ((dataM.h78 hG).beta)
          ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)) := by
  haveI := dataL.kernelIn_normal
  have hi_h78 : i ≠ (dataL.h78 hG).ind1H := by rw [dataL.h78_ind1H_eq]; exact hi
  set phi := (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i) with hphi
  -- `Γ_M = β_M − 1_G + ζ_M^ν − a_M•W_M` from the (7.8.a) decomposition.
  have hβ := (dataM.betaDecomp hG).beta_eq
  have hΓ_eq : (dataM.betaDecomp hG).Gamma
      = (dataM.h78 hG).beta - Hypothesis71.constOne G
        + (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta ((dataM.h78 hG).zetaDistinct))
        - ((dataM.betaDecomp hG).a : ℂ) • (dataM.h78 hG).weightedNuSum := by
    rw [hβ]; abel
  -- `⟨1_G, φ_i^ν⟩ = 0` (conjugate of the `L`-side `orth_one`).
  have h1G : ClassFunction.inner (Hypothesis71.constOne G) phi = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      (dataL.betaDecomp hG).orth_one i hi_h78, star_zero]
  -- `⟨ζ_M^ν, φ_i^ν⟩ = 0` (family-wide cross-orthogonality, `j = 0`).
  have hzetaM : ClassFunction.inner
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta ((dataM.h78 hG).zetaDistinct)))
      phi = 0 :=
    pair_cross_orthogonal' dataL dataM hG hL hM hnc hi (Ne.symm dataM.ind1H_ne_zero)
  -- `⟨W_M, φ_i^ν⟩ = 0` (cross-orthogonality against every `M`-member).
  have hWM : ClassFunction.inner ((dataM.h78 hG).weightedNuSum) phi = 0 := by
    rw [show (dataM.h78 hG).weightedNuSum
        = ∑ j ∈ (Finset.univ.erase (dataM.h78 hG).ind1H),
            ((dataM.h78 hG).hyp76.zeta j (1 : ↥M) /
              ((dataM.h78 hG).hyp76.zeta ((dataM.h78 hG).zetaDistinct) (1 : ↥M) *
                ClassFunction.inner ((dataM.h78 hG).hyp76.zeta j)
                  ((dataM.h78 hG).hyp76.zeta j))) •
              (dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j) from rfl,
      inner_sum_left' _ _ _]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [ClassFunction.inner_smul_left,
      pair_cross_orthogonal' dataL dataM hG hL hM hnc hi
        (by rw [← dataM.h78_ind1H_eq hG]; exact (Finset.mem_erase.mp hj).1),
      mul_zero]
  rw [hΓ_eq, ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, h1G, hzetaM, ClassFunction.inner_smul_left, hWM, mul_zero,
    sub_zero, add_zero, sub_zero]
  exact inner_beta_nu_zeta_eq dataL dataM hG hL hM hnc hi

/-- **The single-branch (14.14) Bessel bound**: if `⟨β_M, φ^{τ₁}⟩ ≠ 0` (the
`L`-family is paired by the `M`-side `β`), then `(h_L − 1)/e_L ≤ e_M − 1`.
The `L`-family Bessel inequality against `‖Γ_M‖² ≤ e_M − 1` ((7.8.b)), with the
degree-square sum `Σ d_i² = (h_L − 1)/e_L`
(`card_index_mul_sum_induced_family_degree_sq`). -/
theorem bessel_bound_of_inner_beta_zeta_ne_zero
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    (hpair : ClassFunction.inner ((dataM.h78 hG).beta)
        ((dataL.h78 hG).nu
          ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct))) ≠ 0) :
    ((Nat.card ↥dataL.kernelIn : ℚ) - 1) / (((dataL.kernelIn).index : ℕ) : ℚ)
      ≤ (((dataM.h78 hG).complementIndex : ℕ) : ℚ) - 1 := by
  classical
  haveI := dataL.kernelIn_normal
  haveI := dataM.kernelIn_normal
  -- The pairing value is an integer `a ≠ 0`.
  have hβZ : (dataM.h78 hG).beta ∈ ZIrr G :=
    (dataM.h78 hG).beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (dataM.h78_ind_mem_ZIrr hG) (dataM.h78_zeta_irreducible hG)
  have hζZ : (dataL.h78 hG).nu
      ((dataL.h78 hG).hyp76.zeta ((dataL.h78 hG).zetaDistinct)) ∈ ZIrr G :=
    (dataL.h78 hG).nu_zetaDistinct_mem_ZIrr_of_isCoherent
      (dataL.isCoherentSourceSet hG) rfl
  obtain ⟨a, ha⟩ := ClassFunction.inner_mem_ZIrr_int hβZ hζZ
  have ha_ne : a ≠ 0 := by
    intro h0
    apply hpair
    rw [ha, h0, Int.cast_zero]
  -- The weighted family vector `v = Σ d_i φ_i^ν` and its coefficients.
  set v : ClassFunction G ℂ := ∑ i ∈ Finset.univ.erase dataL.ind1H,
    dataL.d i • ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i)) with hv
  -- Pairwise orthonormality of the `φ_i^ν`.
  have hON : ∀ i ∈ Finset.univ.erase dataL.ind1H, ∀ j ∈ Finset.univ.erase dataL.ind1H,
      ClassFunction.inner ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i))
        ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta j))
      = if i = j then 1 else 0 := by
    intro i hi j hj
    rw [(dataL.h78 hG).nu_isometry i j (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact (dataL.h78 hG).zeta_inner_self_eq_one_of_irreducible
        (dataL.zeta_irreducible_at hG (Finset.mem_erase.mp hi).1)
    · rw [if_neg hij]
      exact induce_family_orthogonal_of_injective dataL.kernelIn dataL.θ dataL.inj i j hij
  -- `⟨v, v⟩ = Σ d_i²`.
  have hS : ClassFunction.inner v v
      = ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hv, inner_sum_left']
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ClassFunction.inner_smul_left, inner_sum_right]
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
      rw [OddOrder.RepresentationTheory.inner_smul_right, hON i hi j hj,
        if_neg (Ne.symm hji), mul_zero])]
    rw [OddOrder.RepresentationTheory.inner_smul_right, hON i hi i hi, if_pos rfl,
      dataL.d_star, mul_one, sq]
  -- `Σ d_i² = (h_L − 1)/e_L` (the degree-square sum, ℂ-level).
  have hidx_ne : ((dataL.kernelIn).index : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := dataL.kernelIn))
  have hdeg_sum := card_index_mul_sum_induced_family_degree_sq dataL.hFrob dataL.θ
    dataL.ind1H dataL.triv dataL.inj dataL.cover
  have hSval : ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2
      = ((Nat.card ↥dataL.kernelIn : ℂ) - 1) / ((dataL.kernelIn).index : ℂ) := by
    rw [eq_div_iff hidx_ne, mul_comm]
    exact hdeg_sum
  -- `⟨Γ_M, v⟩ = a·Σ d_i²`.
  have hΓv : ClassFunction.inner ((dataM.betaDecomp hG).Gamma) v
      = (a : ℂ) * ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hv, inner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [OddOrder.RepresentationTheory.inner_smul_right, dataL.d_star,
      inner_gamma_nu_zeta_eq dataL dataM hG hL hM hnc (Finset.mem_erase.mp hi).1,
      show ClassFunction.inner ((dataM.h78 hG).beta)
          ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta 0)) = (a : ℂ) from ha,
      sq]
    ring
  -- Assemble the rational Bessel bound with a singleton index family.
  set m : ℚ := ((Nat.card ↥dataL.kernelIn : ℚ) - 1) / (((dataL.kernelIn).index : ℕ) : ℚ)
    with hm
  have hm_cast : (m : ℂ) = ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hSval, hm]
    push_cast
    rfl
  have hbound := (dataM.normEstimates hG).gamma_norm_sq_le (dataM.smallIndex hG)
  -- Apply the singleton orthogonal-integer Bessel bridge (7.10 machinery).
  have happly := sum_rat_weights_le_of_orthogonal_integer_decomposition
    (ι := Unit) Finset.univ (fun _ => v) (fun _ => a) (fun _ => m)
    ((dataM.betaDecomp hG).Gamma)
    ((dataM.betaDecomp hG).Gamma - ((a : ℝ) : ℂ) • v)
    ((((dataM.h78 hG).complementIndex : ℕ) : ℚ) - 1)
    (by rw [Fintype.sum_unique (fun _ : Unit => (((a : ℝ) : ℂ)) • v)]; abel)
    (fun i _ j _ => by
      rw [if_pos (Subsingleton.elim i j)]
      exact hS.trans hm_cast.symm)
    (fun i _ => by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hΓv, hS]
      push_cast
      ring)
    (fun i _ => by
      rw [hm]
      have hcard : (1 : ℚ) ≤ (Nat.card ↥dataL.kernelIn : ℚ) := by
        exact_mod_cast Nat.card_pos
      have hidx : (0 : ℚ) < (((dataL.kernelIn).index : ℕ) : ℚ) := by
        exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      exact div_nonneg (by linarith) hidx.le)
    (fun i _ => ha_ne)
    (by
      calc (ClassFunction.inner ((dataM.betaDecomp hG).Gamma)
              ((dataM.betaDecomp hG).Gamma)).re
          = (dataM.h78 hG).gammaNormSq (dataM.betaDecomp hG) := rfl
        _ ≤ ((dataM.h78 hG).complementIndex : ℝ) - 1 := hbound
        _ = (((((dataM.h78 hG).complementIndex : ℕ) : ℚ) - 1 : ℚ) : ℝ) := by push_cast; ring)
  rwa [Fintype.sum_unique (fun _ : Unit => m)] at happly

/-- **Peterfalvi (14.14), the two-sided pairing bounds**: for a non-conjugate type-I
pair, either `(h_M − 1)/e_M ≤ e_L − 1` (the `M`-family is paired by `β_L`) or
`(h_L − 1)/e_L ≤ e_M − 1` (the `L`-family is paired by `β_M`).  The (7.9) dichotomy
routed through the single-branch Bessel bound on each side. -/
theorem pairing_bounds_of_nonconjugate
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M) :
    ((Nat.card ↥dataM.kernelIn : ℚ) - 1) / (((dataM.kernelIn).index : ℕ) : ℚ)
        ≤ (((dataL.h78 hG).complementIndex : ℕ) : ℚ) - 1 ∨
      ((Nat.card ↥dataL.kernelIn : ℚ) - 1) / (((dataL.kernelIn).index : ℕ) : ℚ)
        ≤ (((dataM.h78 hG).complementIndex : ℕ) : ℚ) - 1 := by
  have hnc' : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup M L :=
    fun h => hnc h.symm
  rcases pairing_dichotomy dataL dataM hG hL hM hnc with hfirst | hsecond
  · -- `⟨β_L, ζ_M^ν⟩ ≠ 0`: Bessel with the roles swapped.
    exact Or.inl (bessel_bound_of_inner_beta_zeta_ne_zero dataM dataL hG hM hL hnc' hfirst)
  · -- `⟨β_M, ζ_L^ν⟩ ≠ 0`.
    exact Or.inr (bessel_bound_of_inner_beta_zeta_ne_zero dataL dataM hG hL hM hnc hsecond)

end Pairing

end OddOrder.Peterfalvi.S16
