/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.HSharpChosenBase
import OddOrder.Peterfalvi.S15_CharacterDegreeEngines

/-!
# Peterfalvi §13 (pp. 80–83) — Core-typed `λ` correction supply

This file constructs the S-side ingredients of Peterfalvi (13.5)/(13.6) from the honest
`CharacterDegreeCore` and conditional `LambdaClusterData`.  The correction itself is the
generic `hypothesis76AlphaFun` for the chosen-base `(S, H^#)` family; only the S-side
coefficient integrality, support, and coherence inputs are specialized here.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

section /- (13.5)–(13.6): the chosen-base λ correction (pp. 80–83) -/

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5.a), chosen-base coefficient integrality**: every (7.7.a)
coefficient of a virtual character is an integer.  The chosen base does not affect the proof:
`H = PC` is abelian, so all family degrees agree and each Dade-image difference is a virtual
character. -/
theorem H_sharp_hypothesis76_base_cCoeff_int [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) :
    ∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      ∃ z : ℤ, (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff χ i = (z : ℂ) := by
  classical
  intro i
  set K : Subgroup ↥hyp.S := (H_sharp_hypothesis76_base hG hyp φ₀).H.subgroupOf hyp.S
    with hKdef
  haveI hKnorm : K.Normal := H_sharp_subgroupOf_normal hyp
  have hHS : hyp.H ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by
        rw [hyp.S_deriv_eq_PU]
        exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]
      exact le_trans inf_le_left hUS
  haveI hKcomm : IsMulCommutative ↥K := by
    have hH := hyp.H_mulCommutative hG
    have e := Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76_base hG hyp φ₀).H ≤ hyp.S from hHS)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hH.is_comm.comm (e a) (e b))⟩⟩
  have hzetaOne : ∀ j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hindex : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : (H_sharp_hypothesis76_base hG hyp φ₀).d i = 1 := by
    have h := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_one_eq_d_mul i
    rw [hzetaOne i, hzetaOne 0] at h
    field_simp at h
    exact h.symm
  have hzetaZ : ∀ j : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta j ∈ ZIrr ↥hyp.S := by
    intro j
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced j
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr K (θ.2.mem_ZIrr)
  have hpsiZ :
      ((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i : ClassFunction ↥hyp.S ℂ)
        ∈ ZIrr ↥hyp.S := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1, one_smul]
    exact Submodule.sub_mem _ (hzetaZ i) (hzetaZ 0)
  have htauEq : (H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
      = ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
          (H_sharp_hconj hG hyp)).toDadeIsometryData.toDadeMap := rfl
  have hpres : (H_sharp_hypothesis76_base hG hyp φ₀).hyp71.τ
      ((H_sharp_hypothesis76_base hG hyp φ₀).psiSupp i) ∈ ZIrr G := by
    rw [htauEq]
    exact ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData
      (H_sharp_hconj hG hyp)).preserves_virtualCharacters _ hpsiZ
  rw [OddOrder.Peterfalvi.S09.Hypothesis76.cCoeff]
  exact ClassFunction.inner_mem_ZIrr_int hpres hχ

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5.a), chosen-base orthogonality**: `λ` is orthogonal to its
`P`-kernel correction tail.  The abstract (7.6) orthogonality supplies the full `S`-sum;
`λ`'s chosen family member vanishes outside `H`, so this is the filtered sum used in (13.6). -/
theorem lambda_alphaFun_inner_zero_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
      lam.lambda x * (starRingEnd ℂ)
        (hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) x)) = 0 := by
  classical
  obtain ⟨i₁, -, hi₁ker, hi₁eq, -, -⟩ :=
    core.exists_lambda_index_base hG lam φ₀ hφ₀P hφ₀ne
  have hvanish : ∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → lam.lambda x = 0 := by
    intro x hx
    rw [← hi₁eq]
    exact (H_sharp_hypothesis76_base hG hyp φ₀).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  have hext :
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
        lam.lambda x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
            (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) x))
        = ∑ x : ↥hyp.S, lam.lambda x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
            (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) x) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (· ∈ hyp.H.subgroupOf hyp.S)]
    have hzero : ∑ x ∈ Finset.univ.filter
        (fun x => ¬ x ∈ hyp.H.subgroupOf hyp.S),
        lam.lambda x * (starRingEnd ℂ)
          (hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
            (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) x) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hvanish x (Finset.mem_filter.mp hx).2, zero_mul]
    rw [hzero, add_zero]
  rw [hext]
  have hfull := hypothesis76_zeta_inner_alphaFun_eq_zero
    (H_sharp_hypothesis76_base hG hyp φ₀) (hyp.P.subgroupOf hyp.S)
    (core.tau1S lam.lambda) i₁ hi₁ker
  rwa [hi₁eq] at hfull

open scoped FiniteInduce in
/-- **Peterfalvi (13.6), `λ(xy)=0` in chosen-base form**: the chosen family member for
`λ` vanishes off `H`, while the mixed product `x·y` has order divisible by `q` and therefore
cannot lie in `H`. -/
theorem LambdaClusterData.apply_mul_eq_zero_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda)
    {x y : G} (hx : x ∈ hyp.W2) (hy : y ∈ hyp.W1) (hy1 : y ≠ 1)
    (hxyS : x * y ∈ hyp.S) :
    lam.lambda ⟨x * y, hxyS⟩ = 0 := by
  obtain ⟨i₁, -, -, hi₁eq⟩ := lam.exists_hSharpFamilyIndex_base hG φ₀ hφ₀ne
  rw [← hi₁eq]
  refine (H_sharp_hypothesis76_base hG hyp φ₀).zeta_eq_zero_of_not_mem_H i₁ _
    (fun hmem => ?_)
  have hmem' : x * y ∈ hyp.H := by
    rwa [show (H_sharp_hypothesis76_base hG hyp φ₀).H = hyp.H from rfl] at hmem
  have hyq : orderOf y = hyp.q := by
    have h2 : orderOf y = orderOf (⟨y, hy⟩ : ↥hyp.W1) :=
      orderOf_injective hyp.W1.subtype Subtype.coe_injective ⟨y, hy⟩
    have h1 : orderOf (⟨y, hy⟩ : ↥hyp.W1) ∣ hyp.q := by
      rw [hyp.q_eq_card_W1]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hyp.q_prime).mp h1 with h | h
    · exact absurd (congrArg Subtype.val (orderOf_eq_one_iff.mp h)) hy1
    · rw [h2, h]
  have hxord : orderOf x ∣ hyp.p := by
    have h2 : orderOf x = orderOf (⟨x, hx⟩ : ↥hyp.W2) :=
      orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨x, hx⟩
    rw [h2, hyp.p_eq_card_W2]
    exact orderOf_dvd_natCard _
  have hcomm : Commute y x := hyp.W1_commutes_W2 y hy x hx
  have hcop : Nat.Coprime (orderOf y) (orderOf x) := by
    rw [hyq]
    exact Nat.Coprime.coprime_dvd_right hxord
      ((Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr (Ne.symm hyp.p_ne_q))
  have hqdvd : hyp.q ∣ orderOf (x * y) := by
    rw [show x * y = y * x from hcomm.eq.symm,
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hyq]
    exact dvd_mul_right _ _
  have hdvdH : orderOf (x * y) ∣ Nat.card ↥hyp.H := by
    have h2 : orderOf (x * y) = orderOf (⟨x * y, hmem'⟩ : ↥hyp.H) :=
      orderOf_injective hyp.H.subtype Subtype.coe_injective ⟨x * y, hmem'⟩
    rw [h2]
    exact orderOf_dvd_natCard _
  exact hyp.q_not_dvd_card_H hG (hqdvd.trans hdvdH)

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.6), Core form of `λ^{τ₁}(xy)=0`**: the honest coherence field
gives orthogonality against every `η`-grid member for the nonkernel inducing character of
`λ`; (3.2.d) then gives vanishing on the regular mixed section. -/
theorem lambda_tau1_apply_mul_eq_zero_core [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis (G := G)} (core : CharacterDegreeCore hyp)
    (lam : LambdaClusterData hyp)
    {x y : G} (hx : x ∈ hyp.W2) (hy : y ∈ hyp.W1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    core.tau1S lam.lambda (x * y) = 0 := by
  obtain ⟨θ, hθirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  have hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  have hW1W : hyp.W1 ≤ hyp.W := by
    rw [hyp.W_eq_join]
    exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by
    rw [hyp.W_eq_join]
    exact le_sup_right
  have hcomm : Commute y x := hyp.W1_commutes_W2 y hy x hx
  have hnot : x * y ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := by
    rw [show x * y = y * x from hcomm.eq.symm]
    exact hyp.mul_notMem_W1_union_W2 hy hx hy1 hx1
  refine hyp.vanish_of_inner_eta_eq_zero (core.tau1S lam.lambda) (fun i j => ?_)
    (mul_mem (hW2W hx) (hW1W hy)) hnot
  rw [hlamEq]
  exact core.tau1S_induce_inner_eta i j θ hθirr hθP (hlamEq ▸ lam.lambda_irreducible)

open scoped FiniteInduce in
/-- **Peterfalvi (13.5.a), `α(1) ∈ ℤ` in Core form**: generic correction
integrality applied to the chosen-base family and the integer coefficient supply above. -/
theorem CharacterDegreeCore.exists_lambda_alphaFun_one_int_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S)) :
    ∃ m : ℤ, hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) 1 = (m : ℂ) := by
  exact hypothesis76AlphaFun_one_int (H_sharp_hypothesis76_base hG hyp φ₀)
    (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
    (H_sharp_hypothesis76_base_cCoeff_int hG hyp φ₀
      (lambda_tau1_norm_one_core core lam).1)

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.6), chosen-base congruence**: the correction value at `1` is an
integer multiple of `q`.  At nonidentity `x ∈ W₂` the point formula identifies the
correction with `λ^{τ₁}(x) - λ(x)`.  Comparing both characters at `x` and `yx`, for
nonidentity `y ∈ W₁`, makes that integer divisible by `1 - ε` for a primitive `q`-th root;
(1.10.b) then gives divisibility by `q`. -/
theorem CharacterDegreeCore.exists_lambda_alphaFun_one_qb_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    ∃ b : ℤ, hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) 1
        = (hyp.q : ℂ) * (b : ℂ) := by
  classical
  obtain ⟨m, hm⟩ := core.exists_lambda_alphaFun_one_int_base hG lam φ₀
  obtain ⟨i₁, hi₁pos, hi₁ker, hi₁eq, hi₁c, hmiddle⟩ :=
    core.exists_lambda_index_base hG lam φ₀ hφ₀P hφ₀ne
  obtain ⟨hZtau, -, hnormLam⟩ := lambda_tau1_norm_one_core core lam
  obtain ⟨x', hx'⟩ : ∃ x' : ↥hyp.W2, x' ≠ 1 := by
    haveI : Nontrivial ↥hyp.W2 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.p_eq_card_W2]; exact hyp.p_prime.one_lt)
    exact exists_ne 1
  obtain ⟨y', hy'⟩ : ∃ y' : ↥hyp.W1, y' ≠ 1 := by
    haveI : Nontrivial ↥hyp.W1 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.q_eq_card_W1]; exact hyp.q_prime.one_lt)
    exact exists_ne 1
  have hxW2 : (x' : G) ∈ hyp.W2 := x'.2
  have hyW1 : (y' : G) ∈ hyp.W1 := y'.2
  have hx1 : (x' : G) ≠ 1 := fun h => hx' (Subtype.ext h)
  have hy1 : (y' : G) ≠ 1 := fun h => hy' (Subtype.ext h)
  have hxP : (x' : G) ∈ hyp.P := W2_le_P hG hyp hxW2
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hxS : (x' : G) ∈ hyp.S := hPS hxP
  have hxH : (x' : G) ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.H) hxP
  have hWS : hyp.W ≤ hyp.S := by
    rw [hyp.W_eq_inter]
    exact inf_le_left
  have hW1W : hyp.W1 ≤ hyp.W := by
    rw [hyp.W_eq_join]
    exact le_sup_left
  have hyS : (y' : G) ∈ hyp.S := hWS (hW1W hyW1)
  have hns : (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁ = 1 := by
    rw [show (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁
      = ClassFunction.inner ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)
        ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁) from rfl, hi₁eq]
    exact hnormLam
  have hpf : core.tau1S lam.lambda (x' : G)
      = lam.lambda ⟨(x' : G), hxS⟩
        + hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) ⟨(x' : G), hxS⟩ := by
    have h := hypothesis76_point_formula (H_sharp_hypothesis76_base hG hyp φ₀)
      (fun _ => rfl) (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
      i₁ hi₁pos hi₁ker hmiddle ⟨(x' : G), hxS⟩
      (by rw [OddOrder.Peterfalvi.S04.mem_sharp]; exact ⟨hxH, hx1⟩)
    rwa [hi₁c, hns, star_one, div_one, one_mul, hi₁eq] at h
  have hZlam : lam.lambda ∈ ZIrr ↥hyp.S := by
    rw [← hi₁eq]
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced i₁
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _ (θ.2.mem_ZIrr)
  have hε : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / hyp.q)) hyp.q :=
    Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne'
  set ε : ℂ := Complex.exp (2 * Real.pi * Complex.I / hyp.q) with hεdef
  have hyq : (y' : G) ^ hyp.q = 1 := by
    have h1 : y' ^ hyp.q = 1 := by
      rw [hyp.q_eq_card_W1]
      exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
  have hcommG : Commute (y' : G) (x' : G) :=
    hyp.W1_commutes_W2 _ hyW1 _ hxW2
  obtain ⟨z₂, hz₂int, hz₂⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hZtau hyq hcommG
  have htau0 : core.tau1S lam.lambda ((y' : G) * (x' : G)) = 0 := by
    rw [hcommG.eq]
    exact lambda_tau1_apply_mul_eq_zero_core core lam hxW2 hyW1 hx1 hy1
  have hyqS : (⟨(y' : G), hyS⟩ : ↥hyp.S) ^ hyp.q = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hyq
  have hcommS : Commute (⟨(y' : G), hyS⟩ : ↥hyp.S)
      (⟨(x' : G), hxS⟩ : ↥hyp.S) := Subtype.ext hcommG.eq
  obtain ⟨z₁, hz₁int, hz₁⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hZlam hyqS hcommS
  have hlam0 : lam.lambda
      ((⟨(y' : G), hyS⟩ : ↥hyp.S) * ⟨(x' : G), hxS⟩) = 0 := by
    have hmulS : ((⟨(y' : G), hyS⟩ : ↥hyp.S) * ⟨(x' : G), hxS⟩ : ↥hyp.S)
        = ⟨(x' : G) * (y' : G), mul_mem hxS hyS⟩ := Subtype.ext hcommG.eq
    rw [hmulS]
    exact lam.apply_mul_eq_zero_base hG φ₀ hφ₀ne hxW2 hyW1 hy1 _
  have hconst := hypothesis76AlphaFun_const (H_sharp_hypothesis76_base hG hyp φ₀)
    (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
    ⟨(x' : G), hxS⟩ (Subgroup.mem_subgroupOf.mpr hxP)
  have hcast : ((m : ℤ) : ℂ) = (1 - ε) * (z₁ - z₂) := by
    rw [htau0, zero_sub] at hz₂
    rw [hlam0, zero_sub] at hz₁
    have e1 : core.tau1S lam.lambda (x' : G) = -((1 - ε) * z₂) := by
      linear_combination -hz₂
    have e2 : lam.lambda ⟨(x' : G), hxS⟩ = -((1 - ε) * z₁) := by
      linear_combination -hz₁
    have e3 : hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
        (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) ⟨(x' : G), hxS⟩
          = (1 - ε) * (z₁ - z₂) := by
      have e4 := hpf
      rw [e1, e2] at e4
      linear_combination -e4
    calc
      (m : ℂ) = hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) 1 := hm.symm
      _ = hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
            ⟨(x' : G), hxS⟩ := hconst.symm
      _ = (1 - ε) * (z₁ - z₂) := e3
  have hdvd : (hyp.q : ℤ) ∣ m :=
    OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hyp.q_prime hε
      (hz₁int.sub hz₂int) hcast
  obtain ⟨b, hb⟩ := hdvd
  refine ⟨b, ?_⟩
  calc
    hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
        (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) 1 = (m : ℂ) := hm
    _ = (((hyp.q : ℤ) * b : ℤ) : ℂ) := by rw [hb]
    _ = (hyp.q : ℂ) * (b : ℂ) := by
      push_cast
      rfl

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5.c), S-side chosen-base specialization** of the generic correction
inflation bound. -/
theorem H_sharp_hypothesis76_base_alphaFun_inflation [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S)) (χ : ClassFunction G ℂ) :
    ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) *
        ‖hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) χ 1‖ ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
            (hyp.P.subgroupOf hyp.S) χ x‖ ^ 2 := by
  let F : Finset ↥hyp.S := (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1
  have hF : ∀ x : ↥hyp.S, x ∈ F ↔
      ((x : G) ∈ (H_sharp_hypothesis76_base hG hyp φ₀).H ∧ x ≠ 1) := by
    intro x
    rw [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hx1, -, hxH⟩
      exact ⟨Subgroup.mem_subgroupOf.mp hxH, hx1⟩
    · rintro ⟨hxH, hx1⟩
      exact ⟨hx1, Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr hxH⟩
  have hPH : ∀ x : ↥hyp.S, x ∈ hyp.P.subgroupOf hyp.S →
      (x : G) ∈ (H_sharp_hypothesis76_base hG hyp φ₀).H := by
    intro x hx
    exact (le_sup_left : hyp.P ≤ hyp.H) (Subgroup.mem_subgroupOf.mp hx)
  have hinfl := hypothesis76AlphaFun_inflation
    (H_sharp_hypothesis76_base hG hyp φ₀) (hyp.P.subgroupOf hyp.S) χ F hF hPH
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hcard : Nat.card ↥(hyp.P.subgroupOf hyp.S) = hyp.p ^ hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
    exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hone : (1 : ℕ) ≤ hyp.p ^ hyp.q :=
    Nat.one_le_pow _ _ (by have := hyp.three_le_p; omega)
  have hcoeff : ((Nat.card ↥(hyp.P.subgroupOf hyp.S) : ℝ)) - 1
      = ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) := by
    rw [hcard, Nat.cast_sub hone]
    norm_num
  rw [← hcoeff]
  simpa [F] using hinfl

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5.a,c), honest `λ` correction package**: choose the nonkernel base
from the reducible Core column, then assemble the point formula, orthogonality,
`α(1) = qb`, and inflation estimate for `λ^{τ₁}`.  The chosen base is internal to the proof;
the exported datum depends only on `CharacterDegreeCore` and `LambdaClusterData`. -/
theorem CharacterDegreeCore.exists_caseB_data_lambda_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    ∃ (α : ↥hyp.S → ℂ) (b : ℤ),
      (∀ x : ↥hyp.S, x ∉ hyp.H.subgroupOf hyp.S → lam.lambda x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S),
        lam.lambda x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
        core.tau1S lam.lambda ↑x = lam.lambda x + α x) ∧
      α 1 = (hyp.q : ℂ) * (b : ℂ) ∧
      ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
            ‖α x‖ ^ 2 := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨φ₀, hφ₀P, hφ₀ne⟩ := core.exists_hSharpBase_ne_lambda lam
  obtain ⟨i₁, hi₁pos, hi₁ker, hi₁eq, hi₁c, hmiddle⟩ :=
    core.exists_lambda_index_base hG lam φ₀ hφ₀P hφ₀ne
  obtain ⟨-, -, hinnerLam⟩ := lambda_tau1_norm_one_core core lam
  obtain ⟨b, hb⟩ := core.exists_lambda_alphaFun_one_qb_base
    hG lam φ₀ hφ₀P hφ₀ne
  refine ⟨hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
    (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda), b, ?_, ?_, ?_, hb, ?_⟩
  · intro x hx
    rw [← hi₁eq]
    exact (H_sharp_hypothesis76_base hG hyp φ₀).zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  · exact lambda_alphaFun_inner_zero_base hG core lam φ₀ hφ₀P hφ₀ne
  · intro x hx
    obtain ⟨hx1, hxmem⟩ := Finset.mem_erase.mp hx
    have hxH : (↑x : G) ∈ hyp.H :=
      Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxmem).2
    have hxsharp : (↑x : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) := by
      refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxH, ?_⟩
      intro h1
      exact hx1 (Subtype.ext h1)
    have hpt := hypothesis76_point_formula (H_sharp_hypothesis76_base hG hyp φ₀)
      (fun _ => rfl) (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
      i₁ hi₁pos hi₁ker hmiddle x hxsharp
    rw [hpt, hi₁c]
    have hnorm1 : (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁ = 1 := by
      rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hi₁eq]
      exact hinnerLam
    rw [hnorm1, hi₁eq, star_one, div_one, one_mul]
    rfl
  · have hinfl := H_sharp_hypothesis76_base_alphaFun_inflation hG hyp φ₀
      (core.tau1S lam.lambda)
    rw [hb] at hinfl
    have hval : ‖(hyp.q : ℂ) * (b : ℂ)‖ ^ 2
        = ((hyp.q : ℝ) * (b : ℝ)) ^ 2 := by
      rw [norm_mul, mul_pow, Complex.norm_natCast, Complex.norm_intCast, sq_abs]
      ring
    rw [hval] at hinfl
    exact hinfl

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.6), honest Core form**:
`∑_{x∈H^#}|λ^{τ₁}(x)|² ≥ |S| - λ(1)²`, with `λ(1)=uq`.
The proof feeds the constructed (13.5) correction package into the abstract Case-B norm
engine, then transports the subgroup sum to the ambient sharp set. -/
theorem CharacterDegreeCore.lambda_tau1_sharp_norm_lower_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
          ‖core.tau1S lam.lambda x‖ ^ 2 := by
  classical
  obtain ⟨α, b, hvanish, hinner, hχ, hα1, hinfl⟩ :=
    core.exists_caseB_data_lambda_core hG lam
  obtain ⟨-, -, hinnerLam⟩ := lambda_tau1_norm_one_core core lam
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by
      rw [hyp.S_deriv_eq_PU]
      exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  have hHS : hyp.H ≤ hyp.S := by
    show hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]
      exact le_trans inf_le_left hUS
  have hT : ∑ x : ↥hyp.S, ‖lam.lambda x‖ ^ 2
      = ((Nat.card ↥hyp.S : ℕ) : ℝ) := by
    have h := sum_normSq_eq_card_mul_inner (H := ↥hyp.S) lam.lambda
    rw [hinnerLam, mul_one] at h
    exact_mod_cast h
  have hlamOne : lam.lambda 1 = ((hyp.u * hyp.q : ℕ) : ℂ) := lam.lambda_degree
  have hzetaOne : ‖lam.lambda 1‖ ^ 2
      = (((hyp.u * hyp.q : ℕ) : ℝ)) ^ 2 := by
    rw [hlamOne, Complex.norm_natCast]
  have hcross : (lam.lambda 1 * (starRingEnd ℂ) (α 1)).re
      = ((hyp.u * hyp.q : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) := by
    have hval : lam.lambda 1 * (starRingEnd ℂ) (α 1)
        = ((((hyp.u * hyp.q : ℕ) : ℝ) * ((hyp.q : ℝ) * (b : ℝ)) : ℝ) : ℂ) := by
      rw [hlamOne, hα1, map_mul]
      push_cast [map_natCast, map_intCast]
      ring
    rw [hval, Complex.ofReal_re]
  have hlam1 : ((hyp.u * hyp.q : ℕ) : ℝ)
      = (hyp.u : ℝ) * (hyp.q : ℝ) := by
    push_cast
    ring
  have hu := hyp.two_mul_u_le hG
  have hengine : (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.H.subgroupOf hyp.S)).erase 1,
          ‖core.tau1S lam.lambda ↑x‖ ^ 2 := by
    have h := caseB_lambda_norm_bound (S := ↥hyp.S) (hyp.H.subgroupOf hyp.S)
      (fun x => lam.lambda x) α (fun x => core.tau1S lam.lambda ↑x)
      (Scard := Nat.card ↥hyp.S) (Pm1 := hyp.p ^ hyp.q - 1)
      (u := hyp.u) (q := hyp.q) (lam1 := ((hyp.u * hyp.q : ℕ) : ℝ)) (b := b)
      hvanish (by convert hinner using 2)
      (fun x hx => hχ x (by convert hx using 2))
      hT hzetaOne hcross hlam1
      (by convert hinfl using 2; congr!) hu
    convert h using 2; congr!
  rwa [sum_apply_erase_one_filter_subgroupOf hHS
    (fun y => ‖core.tau1S lam.lambda y‖ ^ 2)] at hengine

end

end OddOrder.Peterfalvi.S15
