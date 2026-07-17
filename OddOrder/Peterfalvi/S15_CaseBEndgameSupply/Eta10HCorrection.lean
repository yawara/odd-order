/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.LambdaCorrection
import OddOrder.Peterfalvi.S15_SAndT_Setup.Canonicalization

/-!
# Peterfalvi §13 (pp. 82–84) — Core-typed H-side `η₁₀` correction

This file reconstructs the (13.7) correction and norm estimate from the honest
`CharacterDegreeCore`.  The (7.6) family is based at a `P`-nonkernel irreducible supplied
by the reducible Core column, so the guarded coefficient-vanishing theorem applies.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

section /- (13.5), (13.7): the chosen-base H-side η₁₀ correction -/

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.7), nonzero correction at the identity** for a chosen
`P`-nonkernel (7.6) base.  The correction is constant on `P`; evaluating at a nonidentity
element of `W₂ ≤ P` and applying the (1.10) primitive-root congruence rules out zero. -/
theorem Hypothesis.eta10_alphaCF_one_ne_zero_base_core [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ))) :
    hypothesis76AlphaCF (H_sharp_hypothesis76_base hG hyp φ₀)
        (hyp.P.subgroupOf hyp.S) hyp.eta10 1 ≠ 0 := by
  classical
  intro hzero
  obtain ⟨y', hy'⟩ : ∃ y' : ↥hyp.W2, y' ≠ 1 := by
    haveI : Nontrivial ↥hyp.W2 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.p_eq_card_W2]; exact hyp.p_prime.one_lt)
    exact exists_ne 1
  have hyW2 : (y' : G) ∈ hyp.W2 := y'.2
  have hy1 : (y' : G) ≠ 1 := fun h => hy' (Subtype.ext h)
  have hyP : (y' : G) ∈ hyp.P := W2_le_P hG hyp hyW2
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hyS : (y' : G) ∈ hyp.S := hPS hyP
  have hyH : (y' : G) ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.H) hyP
  have hval : hyp.eta10 ((⟨(y' : G), hyS⟩ : ↥hyp.S) : G)
      = hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) hyp.eta10 ⟨(y' : G), hyS⟩ :=
    hypothesis76_point_formula_kernel_only (H_sharp_hypothesis76_base hG hyp φ₀)
      (fun _ => rfl) (hyp.P.subgroupOf hyp.S) hyp.eta10
      (fun i _ hiP => eta10_cCoeff_base_eq_zero hG core φ₀ hφ₀P i hiP)
      ⟨(y' : G), hyS⟩
      (by rw [OddOrder.Peterfalvi.S04.mem_sharp]; exact ⟨hyH, hy1⟩)
  have hconst := hypothesis76AlphaFun_const (H_sharp_hypothesis76_base hG hyp φ₀)
    (hyp.P.subgroupOf hyp.S) hyp.eta10 ⟨(y' : G), hyS⟩
    (Subgroup.mem_subgroupOf.mpr hyP)
  have halpha0 : hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) hyp.eta10 1 = 0 := by
    simpa using hzero
  have heta0 : hyp.eta10 (y' : G) = 0 := hval.trans (hconst.trans halpha0)
  obtain ⟨z, hzint, hz⟩ := hyp.eta10_apply_sub_one_integral
    (Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne') hyW2 hy1
  rw [heta0, zero_sub] at hz
  have hdvd : (hyp.q : ℤ) ∣ (-1 : ℤ) :=
    OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hyp.q_prime
      (Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne') hzint
      (by exact_mod_cast hz)
  have hle : (hyp.q : ℤ) ≤ 1 := Int.le_of_dvd one_pos (dvd_neg.mp hdvd)
  have hq := hyp.q_prime.one_lt
  omega

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5)/(13.7), honest Core `η₁₀` correction package on `H^#`**:
choose a `P`-nonkernel base from the Core, realize the kernel tail as a virtual character
on `H`, and assemble its integral Parseval data, inflation bound, and abelian equality case. -/
theorem CharacterDegreeCore.exists_caseB_data_eta10_H_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) :
    ∃ (α : G → ℂ) (d n s : ℕ),
      (∀ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, hyp.eta10 x = α x) ∧
      (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖α x‖ ^ 2 = (s : ℝ)) ∧
      1 ≤ n ∧ s + d ^ 2 = Nat.card ↥hyp.H * n ∧
      (hyp.p ^ hyp.q - 1) * d ^ 2 ≤ s ∧ (n = 1 → d ^ 2 = 1) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨φ₀, hφ₀P⟩ := core.exists_hSharpBase
  set αS : ↥hyp.S → ℂ :=
    hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) hyp.eta10 with hαSdef
  have hHS : hyp.H ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by
        rw [hyp.S_deriv_eq_PU]
        exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    change hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]
      exact le_trans inf_le_left hUS
  refine ⟨fun g => if h : g ∈ hyp.S then αS ⟨g, h⟩ else 0, ?_⟩
  set K : Subgroup ↥hyp.S :=
    (H_sharp_hypothesis76_base hG hyp φ₀).H.subgroupOf hyp.S with hKdef
  haveI : Fintype ↥K := FiniteInduce.finiteSubFintype K
  set F : Finset ↥hyp.S := (Finset.univ.filter (· ∈ K)).erase 1 with hFdef
  have hFK : ∀ x : ↥hyp.S, x ∈ F ↔ (x ∈ K ∧ x ≠ 1) := fun x => by
    rw [hFdef, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h2, h1⟩,
      fun ⟨h2, h1⟩ => ⟨h1, Finset.mem_univ _, h2⟩⟩
  have hFH : ∀ x : ↥hyp.S, x ∈ F ↔ ((x : G) ∈ hyp.H ∧ x ≠ 1) := fun x => by
    rw [hFK]
    exact and_congr_left (fun _ => Subgroup.mem_subgroupOf)
  set ψ : ClassFunction ↥K ℂ :=
    ClassFunction.restrict K
      (hypothesis76AlphaCF (H_sharp_hypothesis76_base hG hyp φ₀)
        (hyp.P.subgroupOf hyp.S) hyp.eta10) with hψdef
  have hψZ : ψ ∈ ZIrr ↥K :=
    hypothesis76AlphaCF_restrict_mem_ZIrr
      (H_sharp_hypothesis76_base hG hyp φ₀) (hyp.P.subgroupOf hyp.S) hyp.eta10
      (H_sharp_hypothesis76_base_cCoeff_int hG hyp φ₀ hyp.eta10_mem_ZIrr)
  obtain ⟨n, hn⟩ := exists_nat_inner_self_of_mem_ZIrr hψZ
  obtain ⟨z, hz⟩ := OddOrder.Algebra.exists_int_apply_one_of_mem_ZIrr hψZ
  have hψ1 : ψ 1 = αS 1 := by
    rw [hψdef, ClassFunction.restrict_apply, OneMemClass.coe_one,
      hypothesis76AlphaCF_apply, hαSdef]
  have hcardK : Nat.card ↥K = Nat.card ↥hyp.H := by
    rw [hKdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show (H_sharp_hypothesis76_base hG hyp φ₀).H ≤ hyp.S from hHS)).toEquiv
  set d : ℕ := z.natAbs with hddef
  have hagree : ∀ k : ↥K, αS ↑k = ψ k := fun k => by
    rw [hψdef, ClassFunction.restrict_apply, hypothesis76AlphaCF_apply, hαSdef]
  have hbook := sum_finset_sharp_normSq_eq (K := K) F hFK αS ψ hagree hn
  have hα1 : ‖αS 1‖ ^ 2 = (d : ℝ) ^ 2 := by
    have h2 : ((d : ℕ) : ℝ) ^ 2 = ((z : ℝ)) ^ 2 := by
      rw [hddef]
      have h0 : (((z.natAbs ^ 2 : ℕ) : ℤ) : ℝ) = ((z ^ 2 : ℤ) : ℝ) := by
        exact_mod_cast Int.natAbs_sq z
      push_cast at h0
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact h0
    rw [← hψ1, hz, Complex.norm_intCast, sq_abs, ← h2]
  have hsharp_nonneg : (0 : ℝ) ≤ ∑ x ∈ F, ‖αS x‖ ^ 2 :=
    Finset.sum_nonneg (fun x _ => by positivity)
  have hd2n : d ^ 2 ≤ Nat.card ↥hyp.H * n := by
    have h0 := hsharp_nonneg
    rw [hbook] at h0
    have h1 : (d : ℝ) ^ 2 ≤ (Nat.card ↥hyp.H : ℝ) * (n : ℝ) := by
      rw [← hα1, ← hcardK]
      linarith [h0]
    exact_mod_cast h1
  set s : ℕ := Nat.card ↥hyp.H * n - d ^ 2 with hsdef
  have hsval : (s : ℝ) =
      (Nat.card ↥hyp.H : ℝ) * (n : ℝ) - (d : ℝ) ^ 2 := by
    rw [hsdef, Nat.cast_sub hd2n]
    push_cast
    ring
  have hFsum : ∑ x ∈ F, ‖αS x‖ ^ 2 = (s : ℝ) := by
    rw [hbook, hα1, hsval, hcardK]
  have hglue := sum_finset_sharp_transport (K := hyp.H) (L := hyp.S) hHS F hFH
    (fun g : G => ‖if h : g ∈ hyp.S then αS ⟨g, h⟩ else 0‖ ^ 2)
  have hGside : ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
      ‖if h : x ∈ hyp.S then αS ⟨x, h⟩ else 0‖ ^ 2 = (s : ℝ) := by
    rw [← hglue, ← hFsum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [dif_pos x.2]
  refine ⟨d, n, s, ?_, hGside, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxH, hx1⟩ := (Set.Finite.mem_toFinset _).mp hx
    have hxS : x ∈ hyp.S := hHS hxH
    change hyp.eta10 x = if h : x ∈ hyp.S then αS ⟨x, h⟩ else 0
    rw [dif_pos hxS]
    have hxsharp : ((⟨x, hxS⟩ : ↥hyp.S) : G) ∈
        OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) :=
      OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxH, hx1⟩
    have hpt := hypothesis76_point_formula_kernel_only
      (H_sharp_hypothesis76_base hG hyp φ₀) (fun _ => rfl)
      (hyp.P.subgroupOf hyp.S) hyp.eta10
      (fun i _ hiP => eta10_cCoeff_base_eq_zero hG core φ₀ hφ₀P i hiP)
      ⟨x, hxS⟩ hxsharp
    rw [hpt]
    rfl
  · by_contra hn0
    push Not at hn0
    have hn00 : n = 0 := by omega
    subst hn00
    have hzero : ∑ k : ↥K, ‖ψ k‖ ^ 2 = 0 := by
      have h := sum_normSq_eq_card_mul_inner (H := ↥K) ψ
      rw [hn] at h
      have h0 : ((∑ k : ↥K, ‖ψ k‖ ^ 2 : ℝ) : ℂ) = 0 := by
        rw [h]
        push_cast
        ring
      exact_mod_cast h0
    have hψ10 : ψ 1 = 0 := by
      have h1 : ‖ψ 1‖ ^ 2 = 0 := by
        have hle : ‖ψ 1‖ ^ 2 ≤ ∑ k : ↥K, ‖ψ k‖ ^ 2 :=
          Finset.single_le_sum (f := fun k : ↥K => ‖ψ k‖ ^ 2)
            (fun k _ => by positivity) (Finset.mem_univ 1)
        have hge : (0 : ℝ) ≤ ‖ψ 1‖ ^ 2 := by positivity
        linarith [hzero ▸ hle]
      have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      simpa using h2
    refine hyp.eta10_alphaCF_one_ne_zero_base_core hG core φ₀ hφ₀P ?_
    simpa [hψdef, ClassFunction.restrict_apply] using hψ10
  · omega
  · have hinfl := H_sharp_hypothesis76_base_alphaFun_inflation
      hG hyp φ₀ hyp.eta10
    have hHbase : (H_sharp_hypothesis76_base hG hyp φ₀).H = hyp.H := rfl
    have h1 : ((hyp.p ^ hyp.q - 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 ≤ (s : ℝ) := by
      rw [← hα1, ← hFsum]
      simpa [F, K, hαSdef, hHbase] using hinfl
    exact_mod_cast h1
  · intro hn1
    subst hn1
    have hn' : ClassFunction.inner ψ ψ = 1 := by
      rw [hn]
      norm_num
    obtain ⟨ε, ξ, hε, hψeq⟩ :=
      OddOrder.RepresentationTheory.exists_zsmul_irreducibleCharacter_of_inner_self_one
        hψZ hn'
    haveI : IsMulCommutative ↥K := by
      have hH := hyp.H_mulCommutative hG
      have e := Subgroup.subgroupOfEquivOfLe
        (show (H_sharp_hypothesis76_base hG hyp φ₀).H ≤ hyp.S from hHS)
      exact ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul]
        exact hH.is_comm.comm (e a) (e b))⟩⟩
    have hξ1 : (ξ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        ξ.2
    have hz2 : (z : ℂ) = (ε : ℂ) := by
      rw [← hz, hψeq,
        show ((ε • (ξ : ClassFunction ↥K ℂ)) 1) =
            (ε : ℂ) * (ξ : ClassFunction ↥K ℂ) 1 from by
          rw [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.smul_apply],
        hξ1, mul_one]
    have hzε : z = ε := by exact_mod_cast hz2
    rcases hε with h | h <;>
      · rw [hddef, hzε, h]
        rfl

open scoped Classical in
/-- **Peterfalvi (13.7), honest Core form**:
`∑_{x∈H^#}|η₁₀(x)|² ≥ |H| - 1`.  The character-theoretic correction data are constructed
above and the remaining implication is the abstract integral norm engine
`caseB_eta_norm_bound`. -/
theorem CharacterDegreeCore.eta10_Hsharp_norm_lower_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) :
    (Nat.card ↥hyp.H : ℝ) - 1
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖hyp.eta10 x‖ ^ 2 := by
  obtain ⟨α, d, n, s, hχ, hs, hn, hParseval, hInflation, habelian⟩ :=
    core.exists_caseB_data_eta10_H_core hG
  have hH1 : 1 ≤ Nat.card ↥hyp.H :=
    Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hP2 : 2 ≤ hyp.p ^ hyp.q - 1 + 1 := by
    have h1 : 3 ≤ hyp.p ^ hyp.q := by
      calc 3 ≤ hyp.p := hyp.three_le_p
        _ ≤ hyp.p ^ hyp.q := Nat.le_self_pow hyp.q_prime.ne_zero _
    omega
  haveI : Fintype G := Fintype.ofFinite G
  exact caseB_eta_norm_bound (S := G) α (fun x => hyp.eta10 x)
    ((Set.toFinite (sharpSubgroup hyp.H)).toFinset)
    (Hcard := Nat.card ↥hyp.H) (P := hyp.p ^ hyp.q - 1 + 1)
    (d := d) (n := n) (s := s) hH1 (fun x hx => hχ x hx) hs hP2 hn
    hParseval (by simpa using hInflation) habelian

end

end OddOrder.Peterfalvi.S15
