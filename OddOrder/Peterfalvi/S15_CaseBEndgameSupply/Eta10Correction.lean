/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CharacterDegreeEngines

/-!
# Peterfalvi §13 (pp. 81–83) — the `T`-side `η₁₀` correction supply

This file constructs the `(T,Q^#)` chosen base used in Peterfalvi (13.8).  The base is not
assumed to induce irreducibly.  Following the completed argument in `PFsection13.v`, it is a
different reducible `ν`-row whose `τ₁T`-image is orthogonal to `η₁₀`: row `2` in the clean
branch and row `1` in the exceptional three-row flip branch.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

section /- (13.3.c), (13.5), (13.8): the chosen `Q^#` base (pp. 78–83) -/

open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.8), the coefficient-zero chosen `Q^#` base**: choose a nonzero
`ν`-row different from the row paired with `η₁₀`, transport its `QD`-source to `Q` using
`D = ⊥`, and retain both `Q ⊄ Ker φ₀` and
`⟨τ₁T(Ind_Q^T φ₀), η₁₀⟩ = 0`.

This is the faithful case-B replacement for an unavailable assumption that `Ind_Q^T φ₀`
itself be irreducible. -/
theorem Hypothesis.exists_qSharpBase_orthogonal_eta10_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hD : hyp.D = ⊥) :
    ∃ φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥(hyp.Q.subgroupOf hyp.T),
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)) ∧
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
            (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ))) hyp.eta10 = 0 := by
  classical
  let i₁ : Fin hyp.q := ⟨1, hyp.q_prime.one_lt⟩
  have h2lt : 2 < hyp.q := by
    have := hyp.three_le_q
    omega
  let i₂ : Fin hyp.q := ⟨2, h2lt⟩
  have hi₁0 : i₁ ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) one_ne_zero
  have hi₂0 : i₂ ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hi₂1 : i₂ ≠ i₁ := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hetaRowZero : ∀ a : Fin hyp.q, a ≠ i₁ →
      ClassFunction.inner (∑ j : Fin hyp.p, hyp.eta a j) hyp.eta10 = 0 := by
    intro a ha
    rw [show hyp.eta10 = hyp.eta i₁ ⟨0, hyp.p_prime.pos⟩ from rfl,
      OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hyp.eta_orthonormal a i₁ j ⟨0, hyp.p_prime.pos⟩,
      if_neg (fun h => ha h.1)]
  obtain ⟨s, hs0, hsOrth⟩ : ∃ s : Fin hyp.q,
      s ≠ ⟨0, hyp.q_prime.pos⟩ ∧
        ClassFunction.inner
          (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (∑ j : Fin hyp.p, hyp.nu s j)) hyp.eta10 = 0 := by
    rcases hyp.tau1T_ofHonest_nuRow_formula hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief with
      hclean | ⟨_hq3, hflip⟩
    · refine ⟨i₂, hi₂0, ?_⟩
      rw [hclean i₂ hi₂0]
      exact hetaRowZero i₂ hi₂1
    · refine ⟨i₁, hi₁0, ?_⟩
      rw [hflip i₁ i₂ hi₁0 hi₂0 (fun h => hi₂1 h.symm),
        ClassFunction.inner_neg_left, hetaRowZero i₂ hi₂1, neg_zero]
  have hKQ : hyp.K.subgroupOf hyp.T = hyp.Q.subgroupOf hyp.T := by
    have h : hyp.K = hyp.Q := by
      change hyp.Q ⊔ hyp.D = hyp.Q
      rw [hD, sup_bot_eq]
    rw [h]
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  haveI hQnorm : (hyp.Q.subgroupOf hyp.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mpr (by
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T)
  obtain ⟨θs, hθsirr, -, hνeqK⟩ := hyp.nu_i_isIndQD hG pins s hs0
  set θsQ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ :=
    ClassFunction.compHom (MulEquiv.subgroupCongr hKQ.symm).toMonoidHom θs with hθsQdef
  have hθsQirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter θsQ :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hKQ.symm).surjective hθsirr
  have hνeqQ : (∑ j : Fin hyp.p, hyp.nu s j)
      = ClassFunction.induce (hyp.Q.subgroupOf hyp.T) θsQ := by
    rw [hνeqK]
    exact (OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKQ.symm θs).symm
  set data := hyp.toTypesIIIIIIVSetupT hG hvd with hdata
  set HU : Subgroup ↥hyp.T := huSub data with hHU
  have hHUeq : HU = (derivedInG hyp.T).subgroupOf hyp.T :=
    huSub_eq_derivedInG_subgroupOf data
  have hQle : hyp.Q.subgroupOf hyp.T ≤ HU := by
    rw [hHUeq]
    refine Subgroup.subgroupOf_mono hyp.T ?_
    rw [hyp.T_deriv_eq_QV]
    exact le_sup_left
  have hνmem : (∑ j : Fin hyp.p, hyp.nu s j) ∈ sSet data :=
    sOf_subset_sSet data chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief s hs0)
  have hQkerNu : ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (∑ j : Fin hyp.p, hyp.nu s j)) := by
    intro hsub
    obtain ⟨ξ, hξ, hξeq⟩ := hνmem
    have hξker : ¬ ((hInHu data : Set ↥HU) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (ξ : ClassFunction ↥HU ℂ)) := hξ
    obtain ⟨x, hxIn, hxKer⟩ := Set.not_subset.mp hξker
    have hxQ : ((x : ↥hyp.T)) ∈ hyp.Q.subgroupOf hyp.T := by
      have hxH : ((x : ↥hyp.T)) ∈ data.H.subgroupOf hyp.T :=
        Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hxIn)
      rwa [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd] at hxH
    have hxker2 : ((x : ↥hyp.T)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce HU (ξ : ClassFunction ↥HU ℂ)) := by
      have hx := hsub hxQ
      rwa [hξeq, induceHU_eq_induce data] at hx
    have hdesc := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      ξ.isIrreducible x.2 hxker2
    exact hxKer (by simpa using hdesc)
  have hθsQfull : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf
      (hyp.Q.subgroupOf hyp.T) : Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θsQ) := by
    intro hker
    apply hQkerNu
    rw [hνeqQ]
    exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf le_rfl θsQ hker
  refine ⟨⟨θsQ, hθsQirr⟩, hθsQfull, ?_⟩
  rw [← hνeqQ]
  exact hsOrth

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.8), distinguished `T`-side index with an honestly selected base**:
the coefficient-zero `ν`-row base supplies the base condition of
`exists_muT_index_core_of_base_condition`, yielding the nonzero distinguished index and all
coefficient, norm, and degree conclusions without an irreducibly induced base hypothesis. -/
theorem Hypothesis.exists_muT_index_caseB_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hD : hyp.D = ⊥) (hQcomm : IsMulCommutative ↥hyp.Q) :
    ∃ (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
          ↥(hyp.Q.subgroupOf hyp.T))
        (i₁ : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1)) (δ : ℤ),
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)) ∧
      0 < i₁ ∧
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁)) ∧
      δ ^ 2 = 1 ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁ = (δ : ℂ) ∧
      (∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i)) →
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i = 0) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁ = (hyp.p : ℂ) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁ 1
        = ((hyp.p * hyp.v : ℕ) : ℂ) := by
  obtain ⟨φ₀, hφ₀Q, hφ₀orth⟩ :=
    hyp.exists_qSharpBase_orthogonal_eta10_core hG hnoV pins hvd hTP Tdata hU hW1 hW2
      chief hD
  obtain ⟨i₁, δ, hi₁, hi₁Q, hδ, hc, hmid, hnorm, hdeg⟩ :=
    hyp.exists_muT_index_core_of_base_condition hG hnoV pins hvd hTP Tdata hU hW1 hW2
      chief hD hQcomm φ₀ hφ₀Q (Or.inr hφ₀orth)
  exact ⟨φ₀, i₁, δ, hφ₀Q, hi₁, hi₁Q, hδ, hc, hmid, hnorm, hdeg⟩

open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5)/(13.8), Core `T`-side correction package**: under `D = ⊥` and
commutative `Q`, the honestly selected coefficient-zero base yields the normalized
distinguished row `ζ`, the `Q`-kernel tail `α`, the point formula on `Q^#`, the exact first
term `|T'| - v²`, and the `(q^p-1)α(1)²` inflation bound. -/
theorem Hypothesis.exists_caseB_data_eta10_T_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hQcomm : IsMulCommutative ↥hyp.Q)
    (pins : NuGridSupplyData hyp) :
    ∃ (ζ α : ↥hyp.T → ℂ) (α1 δ : ℤ),
      (∀ x : ↥hyp.T, x ∉ hyp.Q.subgroupOf hyp.T → ζ x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        ζ x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1,
        hyp.eta10 ↑x = (δ : ℂ) * ζ x + α x) ∧
      ((∑ x : ↥hyp.T, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2
        = (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) ∧
      ((ζ 1 * (starRingEnd ℂ) (α 1)).re = (hyp.v : ℝ) * (α1 : ℝ)) ∧
      δ ^ 2 = 1 ∧
      ((hyp.q ^ hyp.p - 1 : ℕ) : ℝ) * ((α1 : ℤ) : ℝ) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1, ‖α x‖ ^ 2 := by
  have hnoV := OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one hG
  have hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T := hyp.T_isTypeP hG
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T hG hyp
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.toTypesIIIIIIVSetupT hG hvd)
  obtain ⟨φ₀, i₁, δ, _hφ₀Q, hi₁pos, hi₁ker, hδ2, hi₁c, hmiddle, hnormP, hdeg⟩ :=
    hyp.exists_muT_index_caseB_core hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief hD hQcomm
  obtain ⟨α1, hα1⟩ := hyp.exists_etaT_alphaFun_one_int_core hG hvd hQcomm φ₀
  let H76 := Q_sharp_hypothesis76_base hG hyp hvd φ₀
  have hpC : (hyp.p : ℂ) ≠ 0 := by
    exact_mod_cast (show hyp.p ≠ 0 from hyp.p_prime.ne_zero)
  have hpR : (hyp.p : ℝ) ≠ 0 := by
    exact_mod_cast (show hyp.p ≠ 0 from hyp.p_prime.ne_zero)
  have hvanishZ : ∀ x : ↥hyp.T, x ∉ hyp.Q.subgroupOf hyp.T → H76.zeta i₁ x = 0 :=
    fun x hx => H76.zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  refine ⟨fun x => ((hyp.p : ℂ))⁻¹ * H76.zeta i₁ x,
    hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10, α1, δ,
    ?_, ?_, ?_, ?_, ?_, hδ2, ?_⟩
  · intro x hx
    show ((hyp.p : ℂ))⁻¹ * H76.zeta i₁ x = 0
    rw [hvanishZ x hx, mul_zero]
  · have hfull := hypothesis76_zeta_inner_alphaFun_eq_zero H76
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 i₁ hi₁ker
    have hext : (∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        H76.zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x))
        = ∑ x : ↥hyp.T, H76.zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (· ∈ hyp.Q.subgroupOf hyp.T)
        (fun x => H76.zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x))]
      have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.Q.subgroupOf hyp.T),
          H76.zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [hvanishZ x (Finset.mem_filter.mp hx).2, zero_mul]
      rw [h0, add_zero]
    calc
      ∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
          ((hyp.p : ℂ))⁻¹ * H76.zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x)
          = ((hyp.p : ℂ))⁻¹ * ∑ x ∈ Finset.univ.filter
              (· ∈ hyp.Q.subgroupOf hyp.T), H76.zeta i₁ x * (starRingEnd ℂ)
                (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [hext, hfull, mul_zero]
  · intro x hx
    obtain ⟨hx1, hxmem⟩ := Finset.mem_erase.mp hx
    have hxQ : (↑x : G) ∈ hyp.Q :=
      Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxmem).2
    have hxsharp : (↑x : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) := by
      refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxQ, ?_⟩
      intro h1
      exact hx1 (Subtype.ext h1)
    have hpt := hypothesis76_point_formula H76 (fun _ => rfl)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 i₁ hi₁pos hi₁ker hmiddle x hxsharp
    have htail : (∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
          (fun i => (hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
        (star (H76.cCoeff hyp.eta10 i) / H76.zetaNormSq i) * H76.zeta i x)
        = hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x := rfl
    rw [hpt, htail, hi₁c, star_intCast, hnormP]
    ring
  · have hpars : ((∑ x : ↥hyp.T, ‖H76.zeta i₁ x‖ ^ 2 : ℝ) : ℂ)
        = (Nat.card ↥hyp.T : ℂ) * (hyp.p : ℂ) := by
      rw [sum_normSq_eq_card_mul_inner, ← OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq,
        hnormP]
    have hparsR : ∑ x : ↥hyp.T, ‖H76.zeta i₁ x‖ ^ 2
        = (Nat.card ↥hyp.T : ℝ) * (hyp.p : ℝ) := by
      exact_mod_cast hpars
    have hscale : ∀ x : ↥hyp.T,
        ‖((hyp.p : ℂ))⁻¹ * H76.zeta i₁ x‖ ^ 2
          = ((hyp.p : ℝ))⁻¹ ^ 2 * ‖H76.zeta i₁ x‖ ^ 2 := by
      intro x
      rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    have hζ1 : ‖((hyp.p : ℂ))⁻¹ * H76.zeta i₁ 1‖ ^ 2 = (hyp.v : ℝ) ^ 2 := by
      rw [hdeg, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
      rw [show ((hyp.p * hyp.v : ℕ) : ℝ) = (hyp.p : ℝ) * (hyp.v : ℝ) from by
        push_cast; ring]
      field_simp
    have hTp : (Nat.card ↥hyp.T : ℝ)
        = (Nat.card ↥(derivedInG hyp.T) : ℝ) * (hyp.p : ℝ) := by
      exact_mod_cast hyp.card_T_eq_deriv_mul_p hG
    rw [Finset.sum_congr rfl (fun x _ => hscale x), ← Finset.mul_sum, hparsR, hζ1, hTp]
    field_simp
  · have hζ1v : ((hyp.p : ℂ))⁻¹ * H76.zeta i₁ 1 = ((hyp.v : ℕ) : ℂ) := by
      rw [hdeg, show ((hyp.p * hyp.v : ℕ) : ℂ) = (hyp.p : ℂ) * (hyp.v : ℂ) from by
        push_cast; ring]
      field_simp
    show ((((hyp.p : ℂ))⁻¹ * H76.zeta i₁ 1) *
        (starRingEnd ℂ) (hypothesis76AlphaFun H76
          (hyp.Q.subgroupOf hyp.T) hyp.eta10 1)).re = (hyp.v : ℝ) * (α1 : ℝ)
    rw [hζ1v, hα1]
    rw [show ((hyp.v : ℕ) : ℂ) = (((hyp.v : ℕ) : ℝ) : ℂ) from by push_cast; ring,
      show ((α1 : ℤ) : ℂ) = (((α1 : ℤ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  · have hF : ∀ x : ↥hyp.T,
        x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1 ↔
          ((x : G) ∈ H76.H ∧ x ≠ 1) := by
      intro x
      rw [Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨h1, -, h2⟩
        exact ⟨Subgroup.mem_subgroupOf.mp h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr h2⟩
    have hP'H : ∀ x : ↥hyp.T, x ∈ hyp.Q.subgroupOf hyp.T → (x : G) ∈ H76.H :=
      fun x hx => Subgroup.mem_subgroupOf.mp hx
    have hinfl := hypothesis76AlphaFun_inflation H76 (hyp.Q.subgroupOf hyp.T)
      hyp.eta10 _ hF hP'H
    have hQT : hyp.Q ≤ hyp.T := by
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
    have hcardQT : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = hyp.q ^ hyp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv]
      exact hyp.card_Q_eq_qp hG
    have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p :=
      Nat.one_le_pow _ _ (by have := hyp.three_le_q; omega)
    have hcoeff : ((Nat.card ↥(hyp.Q.subgroupOf hyp.T) : ℝ)) - 1
        = ((hyp.q ^ hyp.p - 1 : ℕ) : ℝ) := by
      rw [hcardQT, Nat.cast_sub hqp1]
      norm_num
    have hval : ‖hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 1‖ ^ 2
        = ((α1 : ℤ) : ℝ) ^ 2 := by
      rw [hα1, Complex.norm_intCast, sq_abs]
    rw [← hval, ← hcoeff]
    exact hinfl

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.8), honest `T`-side norm bound**:
`∑_{x∈Q^#}|η₁₀(x)|² ≥ |T'| - v²` from the coefficient-zero chosen-base correction.
The two Case-B structural values are explicit inputs, and commutativity is precisely the
abelian half of the `Q` elementary-abelian conclusion used by the chosen-family engine. -/
theorem Hypothesis.eta10_Qsharp_norm_lower_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥)
    (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  classical
  obtain ⟨ζ, α, α1, δ, hvanish, hinner, hχ, hfirstTerm, hcross, hδ, hinfl⟩ :=
    hyp.exists_caseB_data_eta10_T_core hG hD hQcomm pins
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hu := hyp.two_mul_v_le hv
  have hengine : (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1,
          ‖hyp.eta10 ↑x‖ ^ 2 := by
    have h := caseB_eta01_norm_bound (S := ↥hyp.T) (hyp.Q.subgroupOf hyp.T)
      ζ α (fun x => hyp.eta10 ↑x)
      (Pm1 := hyp.q ^ hyp.p - 1) (u := hyp.v)
      (firstTerm := (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      (α1 := α1) (δ := δ)
      hvanish (by convert hinner using 2 <;> congr!)
      (fun x hx => hχ x (by convert hx using 2 <;> congr!))
      hfirstTerm hcross hδ
      (by convert hinfl using 2 <;> congr!) hu
    convert h using 2 <;> congr!
  rwa [sum_apply_erase_one_filter_subgroupOf hQT
    (fun y => ‖hyp.eta10 y‖ ^ 2)] at hengine

end

end OddOrder.Peterfalvi.S15
