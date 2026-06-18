/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_NormSet
import OddOrder.Peterfalvi.S15_SAndT
import OddOrder.Peterfalvi.S16_NonExistenceGCore

/-!
# Peterfalvi Section 16: Non-existence of G — tail (14.3)--(14.16)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 16, pp. 87--92.

This file holds the tail of Section 16: the subgroup `L` over `N_G(U)`
((14.3)--(14.7)), the case-B character cascade, the orthogonality switch, and
the final field-normalizer structure theorem `field_normalizer_structure`
(Peterfalvi (14.2)) together with `nonexistence_of_G`.  The section hypothesis
`Hypothesis`, the `FieldNormalizerData` structure, and the BG Appendix C
finite-field model machinery live in the frozen upstream core
`OddOrder.Peterfalvi.S16_NonExistenceGCore` (hub prefix-split 2026-06-15).
-/

namespace OddOrder.Peterfalvi.S16
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]

/-! ## (14.3)--(14.7): the subgroup `L` over `N_G(U)` -/

/-- **Peterfalvi (14.3)**: the type-I maximal subgroup `L` containing `N_G(U)`,
its Fitting kernel `H`, the Dade extension, and the three virtual characters
`beta_S`, `beta_T`, and `beta_L`. -/
structure LHypothesis (hyp : Hypothesis (G := G)) where
  L : Subgroup G
  H : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  normalizer_U_le_L : Subgroup.normalizer (hyp.base.U : Set G) ≤ L
  H_eq_LF : H = maxNilpotentNormalHall L
  Lset : Set (ClassFunction ↥L ℂ)
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G
  phi : ClassFunction ↥L ℂ
  e : ℕ
  e_eq_index : Prop
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaS : ClassFunction G ℂ
  betaT : ClassFunction G ℂ
  betaL : ClassFunction G ℂ
  betaS_formula : Prop
  betaS_formula_holds : betaS_formula
  betaT_formula : Prop
  betaT_formula_holds : betaT_formula
  betaL_formula : Prop
  betaL_formula_holds : betaL_formula
  L_semidirect_formula : G → Prop
  U_characteristic_in_H : Prop
  typeI_data : OddOrder.Peterfalvi.S15.TypeIOverNormalizerData hyp.base
  typeI_data_L_eq : typeI_data.L = L
  typeI_data_H_eq : typeI_data.H = H
  typeI_complement_card_eq_pq :
    Nat.card ↥typeI_data.frobenius.complement = hyp.base.p * hyp.base.q

namespace LHypothesis

/-- The subgroup `L` supplied in **Peterfalvi (14.3)** is type I, as witnessed
by the Frobenius data inherited from (13.17). -/
theorem isTypeI {hyp : Hypothesis (G := G)} (Ldata : LHypothesis hyp) :
    IsTypeI Ldata.L := by
  rw [← Ldata.typeI_data_L_eq]
  exact ⟨Ldata.typeI_data.frobenius.typeI⟩

end LHypothesis

/-- Carrier for the case-(9.7.b) conclusion applied to `T` in Peterfalvi
(14.4). -/
structure CaseBForTData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  D_eq_bot : hyp.base.D = ⊥
  v_eq : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)

namespace CaseBForTData

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
odd. -/
theorem v_odd {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    Odd hyp.base.v := by
  rw [data.v_eq]
  exact hyp.tSide_cyclotomic_quotient_odd

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
positive. -/
theorem v_pos {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    0 < hyp.base.v :=
  Odd.pos data.v_odd

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
nonzero. -/
theorem v_ne_zero {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    hyp.base.v ≠ 0 :=
  ne_of_gt data.v_pos

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, `v` is
coprime to `q - 1`. -/
theorem v_coprime_q_sub_one {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    Nat.Coprime hyp.base.v (hyp.base.q - 1) := by
  rw [data.v_eq]
  exact hyp.tSide_cyclotomic_quotient_coprime

/-- In the T-side case-(9.7.b) conclusion of **Peterfalvi (14.4)**, every
positive divisor of `v` is `1 mod p`. -/
theorem divisor_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    ∀ x : ℕ, x ≠ 0 → x ∣ hyp.base.v → x ≡ 1 [MOD hyp.base.p] := by
  intro x hx hxdvd
  apply hyp.tSide_cyclotomic_quotient_divisor_modEq_one x hx
  rw [data.v_eq] at hxdvd
  exact hxdvd

end CaseBForTData

/-- **Peterfalvi (14.4)**: case (9.7.b) holds for `T`, and
`v = (q^p - 1) / (q - 1)`. -/
theorem caseB_for_T [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧
        hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
  sorry

/-- **Peterfalvi (14.5)**: after conjugating `W_2` by some element of `Q`,
`L` splits as `H semidirect (W_1 W_2^y)`. -/
theorem exists_y_L_structure [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ y : G, y ∈ hyp.base.Q ∧ Ldata.L_semidirect_formula y := by
  sorry

/-- Carrier for the case-(9.7.b) conclusion applied to `S` in Peterfalvi
(14.6). -/
structure CaseBForSData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  order : OddOrder.Peterfalvi.S15.CaseBOrderUData hyp.base caseB_formula
  U_rank_obstruction : Prop
  U_rank_obstruction_holds : U_rank_obstruction

namespace CaseBForSData

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
`p ≡ 1 mod q` branch gives the divided cyclotomic value of `u`. -/
theorem u_eq_of_p_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) :=
  data.order.u_eq_of_p_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
non-`p ≡ 1 mod q` branch gives the full cyclotomic value of `u`. -/
theorem u_eq_of_not_modEq_one {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  data.order.u_eq_of_not_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, `u` is at
most the full cyclotomic quotient.  The `p ≡ 1 mod q` branch divides that
quotient by the additional factor `q`; the other branch is equality. -/
theorem u_le_full_cyclotomic {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hp1_pos : 0 < hyp.base.p - 1 := by
      have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
      omega
    have hden_le : hyp.base.p - 1 ≤ hyp.base.q * (hyp.base.p - 1) := by
      have hqpos : 1 ≤ hyp.base.q := hyp.base.q_prime.one_le
      nlinarith [Nat.mul_le_mul_right (hyp.base.p - 1) hqpos]
    exact Nat.div_le_div_left hden_le hp1_pos
  · rw [data.u_eq_of_not_modEq_one hmod]

end CaseBForSData

/-- **Peterfalvi (14.6)**: case (9.7.b) holds for `S`. -/
theorem caseB_for_S [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) :
    ∃ data : CaseBForSData hyp, data.caseB_formula := by
  sorry

/-- **Peterfalvi (14.7)**: if `U` is characteristic in `H`, then the final
field-normalizer configuration (14.2) holds. -/
theorem field_normalizer_of_U_characteristic [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (hchar : Ldata.U_characteristic_in_H) :
    Nonempty (FieldNormalizerData hyp) := by
  sorry

/-! ## (14.8)--(14.9): the key inequality and `T` is type II -/

/-- A small explicit upper bound for `e`, used to keep Peterfalvi (14.8.a)
inside elementary arithmetic/log estimates. -/
private theorem real_exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h :=
    Complex.exp_bound_sq (0 : ℂ) ((1 : ℝ) : ℂ) (by norm_num : ‖((1 : ℝ) : ℂ)‖ ≤ 1)
  rw [Complex.exp_zero] at h
  norm_num at h
  change ‖Complex.exp (((1 : ℝ) : ℂ)) - 1 - 1‖ ≤ (1 : ℝ) at h
  have hsq : ‖Complex.exp (((1 : ℝ) : ℂ)) - 1 - 1‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
  simp [Complex.exp_re, Complex.exp_im] at hsq
  have hupper : Real.exp 1 - 2 ≤ 1 := by nlinarith
  linarith

/-- Taylor's quadratic upper bound for `exp` on `[0,1]`, in the weak form
needed for Peterfalvi (14.8.a). -/
private theorem real_exp_le_quadratic {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hxnorm : ‖((x : ℝ) : ℂ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have h := Complex.exp_bound_sq (0 : ℂ) ((x : ℝ) : ℂ) hxnorm
  rw [Complex.exp_zero] at h
  have hnorm : ‖Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ)‖ ≤ x ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0, pow_two] using h
  have hre := Complex.re_le_norm (Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ))
  have hre_eq :
      (Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ)).re = Real.exp x - 1 - x := by
    simp [Complex.exp_re]
  have hdiff : Real.exp x - 1 - x ≤ x ^ 2 := by
    rw [← hre_eq]
    exact hre.trans hnorm
  linarith

private theorem one_add_inv_le_log_of_five_le {q : ℕ} (hq : 5 ≤ q) :
    1 + (1 / (q : ℝ)) ≤ Real.log q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  rw [Real.le_log_iff_exp_le hqpos]
  have hqge : (5 : ℝ) ≤ q := by exact_mod_cast hq
  calc
    Real.exp (1 + 1 / (q : ℝ)) = Real.exp 1 * Real.exp (1 / (q : ℝ)) := by
      rw [Real.exp_add]
    _ ≤ 3 * (1 + 1 / (q : ℝ) + (1 / (q : ℝ)) ^ 2) := by
      have hsmall : Real.exp (1 / (q : ℝ)) ≤
          1 + 1 / (q : ℝ) + (1 / (q : ℝ)) ^ 2 :=
        real_exp_le_quadratic (by positivity) (by
          field_simp [hqpos.ne']
          exact_mod_cast (le_trans (by norm_num : 1 ≤ 5) hq))
      exact mul_le_mul real_exp_one_le_three hsmall (Real.exp_nonneg _) (by norm_num)
    _ ≤ q := by
      have hs : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg _
      have hcube : 5 * (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by nlinarith [hqge, hs]
      have hquad : 3 * ((q : ℝ) * ((q : ℝ) + 1) + 1) ≤ 5 * (q : ℝ) ^ 2 := by
        nlinarith [hqge, hs]
      field_simp [hqpos.ne']
      nlinarith [hcube, hquad]

private theorem log_div_succ_lt_of_five_le {p q : ℕ} (hq : 5 ≤ q) (hqp : q < p) :
    Real.log (p : ℝ) / ((p : ℝ) + 1) < Real.log (q : ℝ) / ((q : ℝ) + 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  have hppos : (0 : ℝ) < p := hqpos.trans (by exact_mod_cast hqp)
  have hdenp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hdenq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  rw [div_lt_div_iff₀ hdenp hdenq]
  have hratio_pos : (0 : ℝ) < (p : ℝ) / (q : ℝ) := div_pos hppos hqpos
  have hratio_ne : (p : ℝ) / (q : ℝ) ≠ 1 := by
    intro h
    field_simp [hqpos.ne'] at h
    have hpq : p = q := by exact_mod_cast h
    omega
  have hlog_ratio := Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
  have hlog_div := Real.log_div hppos.ne' hqpos.ne'
  have hlogp_bound : Real.log (p : ℝ) < Real.log (q : ℝ) + ((p : ℝ) / (q : ℝ) - 1) := by
    nlinarith [hlog_ratio, hlog_div]
  have hmul := mul_lt_mul_of_pos_right hlogp_bound hdenq
  have hlogq_lower : ((q : ℝ) + 1) / (q : ℝ) ≤ Real.log (q : ℝ) := by
    have h := one_add_inv_le_log_of_five_le hq
    field_simp [hqpos.ne'] at h ⊢
    exact h
  have hupper :
      (Real.log (q : ℝ) + ((p : ℝ) / (q : ℝ) - 1)) * ((q : ℝ) + 1) ≤
        Real.log (q : ℝ) * ((p : ℝ) + 1) := by
    have hpq_nonneg : 0 ≤ (p : ℝ) - (q : ℝ) := by
      have hpqle : (q : ℝ) ≤ p := by exact_mod_cast (le_of_lt hqp)
      linarith
    have hlogq_lower' : (q : ℝ) + 1 ≤ Real.log (q : ℝ) * (q : ℝ) := by
      rwa [div_le_iff₀ hqpos] at hlogq_lower
    have hmul_nonneg :
        ((p : ℝ) - (q : ℝ)) * ((q : ℝ) + 1) ≤
          ((p : ℝ) - (q : ℝ)) * (Real.log (q : ℝ) * (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogq_lower' hpq_nonneg
    field_simp [hqpos.ne']
    nlinarith [hmul_nonneg]
  exact hmul.trans_le hupper

private theorem q_pow_gt_p_pow_of_five_le {p q : ℕ} (hq : 5 ≤ q) (hqp : q < p) :
    p ^ (q + 1) < q ^ (p + 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  have hppos : (0 : ℝ) < p := hqpos.trans (by exact_mod_cast hqp)
  have hdenp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hdenq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hfrac := log_div_succ_lt_of_five_le (p := p) (q := q) hq hqp
  rw [div_lt_div_iff₀ hdenp hdenq] at hfrac
  have hlogpow : Real.log (((p : ℝ) ^ (q + 1))) < Real.log (((q : ℝ) ^ (p + 1))) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    nlinarith [hfrac]
  have hreal : ((p : ℝ) ^ (q + 1)) < ((q : ℝ) ^ (p + 1)) :=
    (Real.log_lt_log_iff (pow_pos hppos _) (pow_pos hqpos _)).mp hlogpow
  exact_mod_cast hreal

private theorem fourth_lt_three_pow_succ {p : ℕ} (hp : 5 ≤ p) :
    p ^ 4 < 3 ^ (p + 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hstep : (p + 1) ^ 4 < 3 * p ^ 4 := by
        have hpz : (5 : ℤ) ≤ p := by exact_mod_cast hp
        have hz : ((p + 1 : ℤ) ^ 4 < 3 * (p : ℤ) ^ 4) := by
          nlinarith [hpz, sq_nonneg ((p : ℤ) - 5), sq_nonneg ((p : ℤ) - 4),
            sq_nonneg ((p : ℤ) - 3), sq_nonneg ((p : ℤ) - 2),
            sq_nonneg ((p : ℤ) - 1), sq_nonneg (p : ℤ)]
        exact_mod_cast hz
      calc
        (p + 1) ^ 4 < 3 * p ^ 4 := hstep
        _ < 3 * 3 ^ (p + 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 3 ^ (p + 2) := by
          rw [show p + 2 = p + 1 + 1 by omega, pow_succ]
          ring

private theorem q_pow_gt_p_pow_of_q_eq_three {p q : ℕ} (hq : q = 3) (hp : 5 ≤ p) :
    p ^ (q + 1) < q ^ (p + 1) := by
  subst q
  simpa using fourth_lt_three_pow_succ hp

/-- **Peterfalvi (14.8.a)**: for odd prime parameters with `q < p`,
`q^(p+1)` strictly dominates `p^(q+1)`. -/
theorem q_pow_gt_p_pow {p q : ℕ} (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hqp : q < p) :
    q ^ (p + 1) > p ^ (q + 1) := by
  by_cases hq3 : q = 3
  · have hp5 : 5 ≤ p := by
      have hp4 : p ≠ 4 := by
        intro hp4
        subst p
        rcases hpodd with ⟨k, hk⟩
        omega
      omega
    exact q_pow_gt_p_pow_of_q_eq_three hq3 hp5
  · have hq_ne_two : q ≠ 2 := by
      intro hq2
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    have hq_three : 3 ≤ q := by
      have htwo : 2 ≤ q := hq.two_le
      omega
    have hq_ne_four : q ≠ 4 := by
      intro hq4
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    have hq5 : 5 ≤ q := by omega
    exact q_pow_gt_p_pow_of_five_le hq5 hqp

namespace Hypothesis

/-- The arithmetic part of **Peterfalvi (14.8)** under the Section 16
hypothesis bundle. -/
theorem q_pow_gt_p_pow (hyp : Hypothesis (G := G)) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) :=
  OddOrder.Peterfalvi.S16.q_pow_gt_p_pow hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p

end Hypothesis

private theorem cyclotomic_quotient_sub_one_ge_pow_pred {q p : ℕ}
    (hq2 : 2 ≤ q) (hp2 : 2 ≤ p) :
    ((q ^ (p - 1) : ℕ) : ℚ) ≤ (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) := by
  have hsum_eq : ∑ k ∈ Finset.range p, q ^ k = (q ^ p - 1) / (q - 1) :=
    Nat.geomSum_eq hq2 p
  have hle_rest : q ^ (p - 1) ≤ ∑ k ∈ Finset.range (p - 1), q ^ (k + 1) := by
    have hlast_mem : p - 2 ∈ Finset.range (p - 1) := by
      simp
      omega
    have hnonneg : ∀ k ∈ Finset.range (p - 1), 0 ≤ q ^ (k + 1) := by
      intro k _hk
      exact Nat.zero_le _
    have hsingle := Finset.single_le_sum hnonneg hlast_mem
    simpa [show p - 2 + 1 = p - 1 by omega] using hsingle
  have hsum_succ : ∑ k ∈ Finset.range p, q ^ k =
      (∑ k ∈ Finset.range (p - 1), q ^ (k + 1)) + 1 := by
    rw [show p = (p - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    simp
  have hle_sum : q ^ (p - 1) + 1 ≤ ∑ k ∈ Finset.range p, q ^ k := by
    rw [hsum_succ]
    omega
  have hnat : q ^ (p - 1) ≤ (q ^ p - 1) / (q - 1) - 1 := by
    rw [← hsum_eq]
    omega
  exact_mod_cast hnat

private theorem cyclotomic_quotient_modEq_one_mod_base {p q : ℕ}
    (hp2 : 2 ≤ p) (hqpos : 0 < q) :
    (p ^ q - 1) / (p - 1) ≡ 1 [MOD p] := by
  have hsum_eq : ∑ k ∈ Finset.range q, p ^ k = (p ^ q - 1) / (p - 1) :=
    Nat.geomSum_eq hp2 q
  rw [← hsum_eq]
  rw [show q = (q - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  have hzero : (∑ k ∈ Finset.range (q - 1), p ^ (k + 1)) ≡ 0 [MOD p] := by
    rw [Nat.modEq_zero_iff_dvd]
    refine Finset.dvd_sum fun k _hk => ?_
    exact dvd_pow_self p (Nat.succ_ne_zero k)
  simpa using hzero.add_right 1

private theorem cyclotomic_quotient_sub_one_lt_div {p q : ℕ} (hp2 : 2 ≤ p) :
    (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) <
      (p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : 0 < 2) hp2
  have hp1_pos_nat : 0 < p - 1 := by omega
  have hden_pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by exact_mod_cast hp1_pos_nat
  have hdiv : p - 1 ∣ p ^ q - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow p 1 q
  have hcast_div : (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) =
      ((p ^ q - 1 : ℕ) : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
    exact Nat.cast_div hdiv (ne_of_gt hden_pos)
  have hsub_le : (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) ≤
      (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le ((p ^ q - 1) / (p - 1)) 1
  have hnum_nat : p ^ q - 1 < p ^ q := by
    have hpq_pos : 0 < p ^ q := pow_pos hp_pos q
    omega
  have hnum : ((p ^ q - 1 : ℕ) : ℚ) < (p ^ q : ℚ) := by exact_mod_cast hnum_nat
  have hquot_lt : (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) <
      (p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
    rw [hcast_div]
    exact div_lt_div_of_pos_right hnum hden_pos
  exact lt_of_le_of_lt hsub_le hquot_lt

private theorem mul_pred_lt_three_pow_pred {p : ℕ} (hp : 5 ≤ p) :
    p * (p - 1) < 3 ^ (p - 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hstep : (p + 1) * p < 3 * (p * (p - 1)) := by
        have hfactor : p + 1 < 3 * (p - 1) := by omega
        have hmul := Nat.mul_lt_mul_of_pos_right hfactor (by omega : 0 < p)
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      calc
        (p + 1) * ((p + 1) - 1) = (p + 1) * p := by rw [Nat.add_sub_cancel_right]
        _ < 3 * (p * (p - 1)) := hstep
        _ < 3 * 3 ^ (p - 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 3 ^ p := by
          calc
            3 * 3 ^ (p - 1) = 3 ^ (p - 1) * 3 := by rw [mul_comm]
            _ = 3 ^ ((p - 1) + 1) := by rw [pow_succ]
            _ = 3 ^ p := by rw [show (p - 1) + 1 = p by omega]

private theorem p_mul_q_lt_q_pow_pred_of_five_le {p q : ℕ}
    (hp5 : 5 ≤ p) (hq3 : 3 ≤ q) (hqp : q < p) :
    p * q < q ^ (p - 1) := by
  have hq_le_pred : q ≤ p - 1 := by omega
  have hpq_le : p * q ≤ p * (p - 1) := Nat.mul_le_mul_left p hq_le_pred
  have hpq_lt_three : p * q < 3 ^ (p - 1) :=
    lt_of_le_of_lt hpq_le (mul_pred_lt_three_pow_pred hp5)
  have hthree_le_qpow : 3 ^ (p - 1) ≤ q ^ (p - 1) :=
    Nat.pow_le_pow_left hq3 (p - 1)
  exact lt_of_lt_of_le hpq_lt_three hthree_le_qpow

private theorem two_mul_sq_lt_pow_pred_of_odd_lt {p q : ℕ}
    (hpodd : Odd p) (hqodd : Odd q) (hq3 : 3 ≤ q) (hqp : q < p) :
    2 * q * q < p ^ (q - 1) := by
  by_cases hq_three : q = 3
  · subst q
    have hp_gt_three : 3 < p := by simpa using hqp
    have hp5 : 5 ≤ p := by
      have hp_ne_four : p ≠ 4 := by
        intro hp4
        have hodd : Odd 4 := by simpa [hp4] using hpodd
        rcases hodd with ⟨k, hk⟩
        omega
      omega
    have hpow2 : 2 * 3 * 3 < p ^ 2 := by
      nlinarith
    simpa using hpow2
  · have hq5 : 5 ≤ q := by
      have hq_ne_four : q ≠ 4 := by
        intro hq4
        have hodd : Odd 4 := by simpa [hq4] using hqodd
        rcases hodd with ⟨k, hk⟩
        omega
      omega
    have hq_pos : 0 < q := by omega
    have hq_sq_pos : 0 < q * q := Nat.mul_pos hq_pos hq_pos
    have htwo_lt_qsq : 2 < q * q := by nlinarith
    have hlt_q4 : 2 * (q * q) < (q * q) * (q * q) :=
      Nat.mul_lt_mul_of_pos_right htwo_lt_qsq hq_sq_pos
    have hq4_le_p4 : q ^ 4 ≤ p ^ 4 :=
      Nat.pow_le_pow_left (Nat.le_of_lt hqp) 4
    have hp_pos : 0 < p := by omega
    have hp4_le : p ^ 4 ≤ p ^ (q - 1) :=
      Nat.pow_le_pow_right hp_pos (by omega : 4 ≤ q - 1)
    calc
      2 * q * q = 2 * (q * q) := by ring
      _ < (q * q) * (q * q) := hlt_q4
      _ = q ^ 4 := by ring
      _ ≤ p ^ 4 := hq4_le_p4
      _ ≤ p ^ (q - 1) := hp4_le

namespace CaseBForTData

/-- The T-side case-(9.7.b) cyclotomic value in **Peterfalvi (14.4)** is already
larger than `p q`.  This is the cyclotomic lower consequence consumed by the
norm-cascade contradiction in (14.11.4). -/
theorem pq_lt_v {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    hyp.base.p * hyp.base.q < hyp.base.v := by
  have hpow : hyp.base.p * hyp.base.q < hyp.base.q ^ (hyp.base.p - 1) :=
    p_mul_q_lt_q_pow_pred_of_five_le hyp.five_le_p hyp.base.three_le_q hyp.q_lt_p
  have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
    (q := hyp.base.q) (p := hyp.base.p) hyp.base.q_prime.two_le hyp.base.p_prime.two_le
  have hle : hyp.base.q ^ (hyp.base.p - 1) ≤
      (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) - 1 := by
    exact_mod_cast hleQ
  rw [data.v_eq]
  exact lt_of_lt_of_le (lt_of_lt_of_le hpow hle)
    (Nat.sub_le ((hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)) 1)

/-- The T-side case-(9.7.b) lower bound also gives the size hypothesis
`v > 2 p` needed in the (14.11.4) norm cascade. -/
theorem two_p_lt_v {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    2 * hyp.base.p < hyp.base.v := by
  have hq_gt_two : 2 < hyp.base.q := by
    have hq3 : 3 ≤ hyp.base.q := hyp.base.three_le_q
    omega
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hmul : hyp.base.p * 2 < hyp.base.p * hyp.base.q :=
    Nat.mul_lt_mul_of_pos_left hq_gt_two hp_pos
  have h2p_lt_pq : 2 * hyp.base.p < hyp.base.p * hyp.base.q := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact lt_trans h2p_lt_pq data.pq_lt_v

end CaseBForTData

namespace CaseBForSData

/-- The S-side case-(9.7.b) cyclotomic value in **Peterfalvi (14.6)** is larger
than `2 q`.  This is the S-side size input consumed by the norm-cascade
contradiction in (14.11.4), including the additional division by `q` in the
`p ≡ 1 mod q` branch. -/
theorem two_q_lt_u {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    2 * hyp.base.q < hyp.base.u := by
  have hpow_sq :
      2 * hyp.base.q * hyp.base.q < hyp.base.p ^ (hyp.base.q - 1) :=
    two_mul_sq_lt_pow_pred_of_odd_lt hyp.base.p_odd hyp.base.q_odd
      hyp.base.three_le_q hyp.q_lt_p
  have hq_gt_one : 1 < hyp.base.q := hyp.base.q_prime.one_lt
  have htwoq_pos : 0 < 2 * hyp.base.q :=
    Nat.mul_pos (by norm_num) hyp.base.q_prime.pos
  have htwoq_lt_twoqq : 2 * hyp.base.q < 2 * hyp.base.q * hyp.base.q := by
    have hmul := Nat.mul_lt_mul_of_pos_left hq_gt_one htwoq_pos
    simpa [mul_assoc] using hmul
  have hpow : 2 * hyp.base.q < hyp.base.p ^ (hyp.base.q - 1) :=
    lt_trans htwoq_lt_twoqq hpow_sq
  have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
    (q := hyp.base.p) (p := hyp.base.q) hyp.base.p_prime.two_le hyp.base.q_prime.two_le
  have hle : hyp.base.p ^ (hyp.base.q - 1) ≤
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 := by
    exact_mod_cast hleQ
  have hfull_gt_twoq :
      2 * hyp.base.q < (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le hpow hle)
      (Nat.sub_le ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) 1)
  have hfull_gt_twoqq :
      2 * hyp.base.q * hyp.base.q <
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le hpow_sq hle)
      (Nat.sub_le ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) 1)
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hdvd : hyp.base.q ∣ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
      OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
        hyp.base.p_prime hmod
    have hlt_div :
        2 * hyp.base.q <
          (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q := by
      rw [Nat.lt_div_iff_mul_lt' hdvd]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfull_gt_twoqq
    rw [show (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q by
      rw [Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm]]
    exact hlt_div
  · rw [data.u_eq_of_not_modEq_one hmod]
    exact hfull_gt_twoq

end CaseBForSData

/-- Arithmetic bridge for **Peterfalvi (14.8)**: under the Section 16 prime
ordering `q < p`, the T-side full cyclotomic quotient gives a strictly larger
`(v - 1) / p` ratio than the S-side full cyclotomic quotient gives for
`(u - 1) / q`. -/
theorem cyclotomic_ratio_gt_of_q_lt_p {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p) :
    (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) / (p : ℚ) >
      (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) / (q : ℚ) := by
  have hpow : q ^ (p + 1) > p ^ (q + 1) :=
    OddOrder.Peterfalvi.S16.q_pow_gt_p_pow hq hpodd hqodd hqp
  have hq2 : 2 ≤ q := hq.two_le
  have hp2 : 2 ≤ p := hp.two_le
  have hqpos_nat : 0 < q := hq.pos
  have hppos_nat : 0 < p := hp.pos
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hp1_pos_nat : 0 < p - 1 := by omega
  have hp1pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by exact_mod_cast hp1_pos_nat
  have hp_pred_ge_q : q ≤ p - 1 := by omega
  have hmain_nat : p ^ (q + 1) < (p - 1) * q ^ p := by
    have hmul : q ^ (p + 1) ≤ (p - 1) * q ^ p := by
      rw [pow_succ, mul_comm (q ^ p) q]
      exact Nat.mul_le_mul_right (q ^ p) hp_pred_ge_q
    exact lt_of_lt_of_le hpow hmul
  have hmain : (p : ℚ) ^ (q + 1) < (((p - 1 : ℕ) : ℚ)) * (q : ℚ) ^ p := by
    exact_mod_cast hmain_nat
  have hmain' : (p ^ q : ℚ) * (p : ℚ) <
      (q ^ (p - 1) : ℚ) * ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) := by
    have hp_pow : (p : ℚ) ^ (q + 1) = (p : ℚ) ^ q * (p : ℚ) := by
      rw [pow_succ]
    have hq_pow : (q : ℚ) ^ p = (q : ℚ) ^ (p - 1) * (q : ℚ) := by
      calc
        (q : ℚ) ^ p = (q : ℚ) ^ ((p - 1) + 1) := by
          exact congrArg (fun n : ℕ => (q : ℚ) ^ n) (by omega : p = (p - 1) + 1)
        _ = (q : ℚ) ^ (p - 1) * (q : ℚ) := by rw [pow_succ]
    norm_num [Nat.cast_pow] at hmain ⊢
    nlinarith
  have hleft_lower := cyclotomic_quotient_sub_one_ge_pow_pred (q := q) (p := p) hq2 hp2
  have hright_upper := cyclotomic_quotient_sub_one_lt_div (p := p) (q := q) hp2
  have hcompare_core : (p ^ q : ℚ) / ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) <
      (q ^ (p - 1) : ℚ) / (p : ℚ) := by
    rw [div_lt_div_iff₀]
    · simpa [Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hmain'
    · positivity
    · exact hppos
  calc
    (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) / (q : ℚ)
        < ((p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ))) / (q : ℚ) :=
          div_lt_div_of_pos_right hright_upper hqpos
    _ = (p ^ q : ℚ) / ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) := by
          field_simp [hqpos.ne', hp1pos.ne']
    _ < (q ^ (p - 1) : ℚ) / (p : ℚ) := hcompare_core
    _ ≤ (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) / (p : ℚ) := by
          exact div_le_div_of_nonneg_right (by simpa [Nat.cast_pow] using hleft_lower)
            (le_of_lt hppos)

/-- The ratio comparison in **Peterfalvi (14.8)** from the two case-(9.7.b)
cyclotomic order conclusions. -/
theorem key_ratio_inequality_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) :
    (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  have hqpos : (0 : ℚ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right Sdata.u_le_full_cyclotomic 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  rw [Tdata.v_eq]
  exact lt_of_le_of_lt hu_div hratio

/-- **Peterfalvi (14.8)** from materialized case-(9.7.b) data on both sides.
This is the proven consumer form of `key_inequality`: once Sections (14.4) and
(14.6) provide the T- and S-side `CaseB` data, the remaining comparison is pure
arithmetic. -/
theorem key_inequality_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  exact ⟨hyp.q_pow_gt_p_pow, key_ratio_inequality_of_caseB_data Tdata Sdata⟩

/-- **Peterfalvi (14.8)** consumer form for the exact output shapes of
`caseB_for_T` and `caseB_for_S`.  This keeps the future proof of
`key_inequality` focused on constructing the structural `CaseB` data. -/
theorem key_inequality_of_caseB_outputs {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact key_inequality_of_caseB_data Tdata Sdata

/-- **Peterfalvi (14.8)**: the strict exponential inequality and its
character-theoretic corollary comparing `(v - 1) / p` and `(u - 1) / q`. -/
theorem key_inequality [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  refine ⟨hyp.q_pow_gt_p_pow, ?_⟩
  sorry

/-- **Peterfalvi (14.9)**: the subgroup `T` is of Type II. -/
theorem T_typeII [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    IsTypeII hyp.base.T := by
  sorry

/-! ## (14.10)--(14.11): the subgroup `M` over `N_G(V)` -/

/-- **Peterfalvi (14.10)**: the type-I maximal subgroup `M` containing
`N_G(V)`, its Fitting kernel `K`, the Dade extension, and `beta_M`. -/
structure MHypothesis (hyp : Hypothesis (G := G)) where
  M : Subgroup G
  K : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  normalizer_V_le_M : Subgroup.normalizer (hyp.base.V : Set G) ≤ M
  K_eq_MF : K = maxNilpotentNormalHall M
  Mset : Set (ClassFunction ↥M ℂ)
  tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  tau1 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G
  psi : ClassFunction ↥M ℂ
  e : ℕ
  k : ℕ
  e_eq_index : Prop
  k_eq_card_K : k = Nat.card ↥K
  psi_mem : psi ∈ Mset
  psi_degree_eq_e : psi 1 = (e : ℂ)
  betaM : ClassFunction G ℂ
  betaM_formula : Prop
  betaM_formula_holds : betaM_formula
  G0 : Set G
  generic_bound_formula : G → Prop
  betaM_expansion_formula : Prop
  final_norm_contradiction : Prop

/-- The displayed rational inequality produced by the norm calculation in
**Peterfalvi (14.11.4)**, after substituting `e = p q`.  It is kept concrete so
future character-theoretic producers can target the exact arithmetic consumer
without adding another opaque proposition. -/
def normCascadeBound (hyp : Hypothesis (G := G)) (k : ℕ) : Prop :=
  (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
    ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
      2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)

/-- Pure arithmetic estimate used in **Peterfalvi (14.11.4)**.  Once the
norm calculation reduces the error terms to `2 / (p q) + 1 / (u q) + 1 / (v p)`,
the Section 16 size assumptions `u > 2q`, `v > 2p`, and `q < p` bound that error
strictly by `1 / q`. -/
theorem norm_error_terms_lt_inv_q {p q u v : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v) :
    (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
        1 / ((v * p : ℕ) : ℚ) < 1 / (q : ℚ) := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hupos_nat : 0 < u := by omega
  have hvpos_nat : 0 < v := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hupos : (0 : ℚ) < u := by exact_mod_cast hupos_nat
  have hvpos : (0 : ℚ) < v := by exact_mod_cast hvpos_nat
  have hq3q : (3 : ℚ) ≤ q := by exact_mod_cast hq3
  have hqpq : (q : ℚ) < p := by exact_mod_cast hqp
  have huq : (2 : ℚ) * q < u := by exact_mod_cast hu
  have hvp : (2 : ℚ) * p < v := by exact_mod_cast hv
  have hterm1 : (2 : ℚ) / ((p * q : ℕ) : ℚ) < 2 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    exact div_lt_div_of_pos_left (by norm_num) (mul_pos hqpos hqpos)
      (mul_lt_mul_of_pos_right hqpq hqpos)
  have hterm2 : (1 : ℚ) / ((u * q : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hden : (2 : ℚ) * q * q < u * q := by nlinarith [huq, hqpos]
    have hcore : (1 : ℚ) / (u * q) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hterm3 : (1 : ℚ) / ((v * p : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hsq : (q : ℚ) * q < p * p := by nlinarith [hqpq, hqpos, hppos]
    have hden : (2 : ℚ) * q * q < v * p := by nlinarith [hsq, hvp, hppos]
    have hcore : (1 : ℚ) / (v * p) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hsum :
      (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ) <
        2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) := by
    nlinarith [hterm1, hterm2, hterm3]
  have hsum_eq :
      2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) = 3 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    field_simp [hqpos.ne']
    ring
  have hthree_le : (3 : ℚ) / ((q * q : ℕ) : ℚ) ≤ 1 / (q : ℚ) := by
    norm_num [Nat.cast_mul]
    have hmul_nonneg : 0 ≤ (q : ℚ) * ((q : ℚ) - 3) :=
      mul_nonneg (le_of_lt hqpos) (sub_nonneg.mpr hq3q)
    field_simp [hqpos.ne']
    nlinarith [hmul_nonneg]
  nlinarith [hsum, hsum_eq, hthree_le]

/-- Arithmetic endpoint for **Peterfalvi (14.11.4)**.  If the norm calculation
has already yielded the displayed bound from the text, then the lower bound
`k > 2 p v` and the cyclotomic lower consequence `p q < v` are contradictory. -/
theorem norm_cascade_contradiction {p q u v k : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v)
    (hk : 2 * p * v < k) (hvlarge : p * q < v)
    (hbound :
      (1 : ℚ) / (p : ℚ) + 1 / (q : ℚ) ≤
        ((p * q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((p * q : ℕ) : ℚ) +
          1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ)) :
    False := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hvpos_nat : 0 < v := by omega
  have hkpos_nat : 0 < k := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hkpos : (0 : ℚ) < k := by exact_mod_cast hkpos_nat
  have hsmall := norm_error_terms_lt_inv_q (p := p) (q := q) (u := u) (v := v)
    hq3 hqp hu hv
  have hpinv_lt : (1 : ℚ) / (p : ℚ) < ((p * q : ℕ) : ℚ) / (k : ℚ) := by
    nlinarith [hbound, hsmall]
  have hk_lt : (k : ℚ) < (p : ℚ) * (p : ℚ) * (q : ℚ) := by
    field_simp [Nat.cast_mul, hppos.ne', hqpos.ne', hkpos.ne'] at hpinv_lt
    norm_num [Nat.cast_mul] at hpinv_lt
    nlinarith [hpinv_lt]
  have hk_gt : ((2 * p * v : ℕ) : ℚ) < k := by exact_mod_cast hk
  have hvlargeq : ((p * q : ℕ) : ℚ) < v := by exact_mod_cast hvlarge
  norm_num [Nat.cast_mul] at hk_gt hvlargeq
  nlinarith [hk_lt, hk_gt, hvlargeq, hppos]

/-- **Peterfalvi (14.11.4)** arithmetic consumer with the T-side case-(9.7.b)
data already materialized.  The T-side data supplies both `p q < v` and
`2 p < v`, so the remaining inputs are exactly the S-side lower bound on `u`,
the `k > 2 p v` lower bound, and the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_T_caseB {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (hu : 2 * hyp.base.q < hyp.base.u) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction hyp.base.three_le_q hyp.q_lt_p hu
    Tdata.two_p_lt_v hk Tdata.pq_lt_v hbound

/-- **Peterfalvi (14.11.4)** arithmetic consumer with both case-(9.7.b) data
packages materialized.  The S-side data supplies `2 q < u`; the T-side data
supplies `2 p < v` and `p q < v`. -/
theorem norm_cascade_contradiction_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction_of_T_caseB Tdata Sdata.two_q_lt_u hk hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact output shapes of
`caseB_for_T` and `caseB_for_S`.  It leaves only the lower bound on `k` and the
concrete displayed norm inequality as inputs. -/
theorem norm_cascade_contradiction_of_caseB_outputs {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k) (hbound : normCascadeBound hyp k) :
    False := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact norm_cascade_contradiction_of_caseB_data Tdata Sdata hk hbound

/-- **Peterfalvi (14.11.4)** consumer after the first numerical output of
`main_size_bounds` has supplied `k > 2 p v`.  The remaining non-arithmetic work
is precisely to produce the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_main_size_bound {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v)
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_caseB_data Tdata Sdata hsize hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact three-part numerical output
of **Peterfalvi (14.11.1)**.  Only the first component, `k > 2 p v`, is needed
by the norm-cascade contradiction; the remaining components stay available to
match the theorem output without weakening its shape. -/
theorem norm_cascade_contradiction_of_caseB_data_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_main_size_bound Tdata Sdata Mdata hsize.1 hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact output shapes of
`caseB_for_T`, `caseB_for_S`, and `main_size_bounds`. -/
theorem norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact norm_cascade_contradiction_of_caseB_data_main_size_bounds Tdata Sdata Mdata
    hsize hbound

/-- **Peterfalvi (14.11.1)**: if `K != V`, then `k` is large and the quotient
bound dominates `(v - 1) / p`. -/
theorem main_size_bounds [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≥
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  sorry

/-- **Peterfalvi (14.11.2)**: under `K != V`, `e = p q`, and
`beta_M^tau` is a signed sum of the `eta_ij` with one character removed. -/
theorem betaM_expansion [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.e = hyp.base.p * hyp.base.q ∧ Mdata.betaM_expansion_formula := by
  sorry

/-- **Peterfalvi (14.11.3)**: on the generic set `G_0`, the extended character
`psi^tau_1` has absolute value at least one. -/
theorem generic_character_bound [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) :
    ∀ g : G, g ∈ Mdata.G0 → Mdata.generic_bound_formula g := by
  sorry

/-- **Peterfalvi (14.11.2)+(14.11.3) ⇒ (14.11.4)**: the character-theoretic norm
calculation.  Combining the `beta_M^tau` expansion (14.11.2) with the generic
lower bound `|psi^tau_1| ≥ 1` (14.11.3) and the Frobenius inner-product formula
(7.5) yields the displayed rational inequality `normCascadeBound hyp k`.  This is
the *sole* genuinely character-theoretic input to the (14.11.4) contradiction;
everything downstream of it is the arithmetic cascade already discharged in
`norm_cascade_contradiction`. -/
theorem normCascadeBound_of_charData [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Mdata : MHypothesis hyp) (hne : Mdata.K ≠ hyp.base.V) :
    normCascadeBound hyp Mdata.k := by
  -- (14.11.2): `e = p q` together with the signed `eta_ij` expansion of `beta_M^tau`.
  have _hbeta := betaM_expansion _hG hyp Mdata hne
  -- (14.11.3): the generic lower bound `|psi^tau_1(g)| ≥ 1` on `G_0`.
  have _hgen := generic_character_bound _hG hyp Mdata
  sorry

/-- **Peterfalvi (14.11.4)**: the norm inequality cascade contradicts `K != V`.

This is now a transparent composition rather than an opaque obligation: the
case-(9.7.b) outputs of `caseB_for_T` (14.4) and `caseB_for_S` (14.6) supply the
T-side/S-side cyclotomic size data, `main_size_bounds` (14.11.1) supplies
`k > 2 p v`, and `normCascadeBound_of_charData` (14.11.2)--(14.11.3) supplies the
displayed norm inequality.  The arithmetic consumer
`norm_cascade_contradiction_of_caseB_outputs_main_size_bounds` then closes the
cascade.  The only remaining genuine `sorry`s are the named producers above. -/
theorem contradiction_of_K_ne_V [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    False :=
  norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
    (caseB_for_T _hG hyp) (caseB_for_S _hG hyp Ldata) Mdata
    (main_size_bounds _hG hyp Mdata hne)
    (normCascadeBound_of_charData _hG hyp Mdata hne)

/-- **Peterfalvi (14.11)**: `K = V` and `|M : K| = p q`.

The `K = V` half is now a genuine consequence of the (14.11.1)--(14.11.4)
contradiction: assuming `K ≠ V` invokes `contradiction_of_K_ne_V`.  The index
computation `|M : K| = p q` (here `Mdata.e = p q`) is the remaining genuine
obligation; note `betaM_expansion`'s `e = p q` is unavailable here because it
is conditioned on `K ≠ V`, so the equal-index value under `K = V` needs the
type-I structure of `M` directly. -/
theorem K_eq_V_index_pq [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp) :
    Mdata.K = hyp.base.V ∧ Mdata.e = hyp.base.p * hyp.base.q := by
  refine ⟨?_, ?_⟩
  · -- (14.11.1)--(14.11.4): `K ≠ V` is contradictory.
    by_contra hne
    exact contradiction_of_K_ne_V _hG hyp Ldata Mdata hne
  · -- `|M : K| = p q` from the type-I structure of `M` (still to be supplied).
    sorry

/-! ## (14.12)--(14.16): comparing `L` and `M` -/

/-- **Peterfalvi (14.12)**: if `L` is conjugate to `M`, then the final
field-normalizer configuration (14.2) holds. -/
theorem field_normalizer_of_L_conj_M [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp) (Mdata : MHypothesis hyp)
    (hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M) :
    Nonempty (FieldNormalizerData hyp) := by
  sorry

/-- **Peterfalvi (14.13)**: the final comparison case assumes `L` and `M` are
not conjugate and sets `h = |H|`. -/
structure NonConjugateHypothesis (hyp : Hypothesis (G := G)) where
  Ldata : LHypothesis hyp
  Mdata : MHypothesis hyp
  not_conj : ¬ ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
  h : ℕ
  h_eq_card_H : h = Nat.card ↥Ldata.H

namespace NonConjugateHypothesis

/-- **Peterfalvi (14.13)**: since `h = |H|` and `H` is a subgroup of the
minimal odd-order group, `h` is odd. -/
theorem h_odd [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    Odd nc.h := by
  rw [nc.h_eq_card_H]
  exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card nc.Ldata.H)

/-- **Peterfalvi (14.5)** cardinal consequence: `u` divides `h = |H|`.
The subgroup `U` lies in the Fitting kernel `H` of the type-I subgroup over
`N_G(U)`, while (13.12) gives `c = 1`; hence `|U| = u` and `u ∣ |H|`. -/
theorem u_dvd_h [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    hyp.base.u ∣ nc.h := by
  rw [nc.h_eq_card_H]
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base, mul_one]
  have hU_le_H : hyp.base.U ≤ nc.Ldata.H := by
    rw [← nc.Ldata.typeI_data_H_eq]
    exact nc.Ldata.typeI_data.U_le_H
  have hdvd : Nat.card ↥hyp.base.U ∣ Nat.card ↥nc.Ldata.H :=
    Subgroup.card_dvd_of_le hU_le_H
  simpa [hU_card] using hdvd

/-- **Peterfalvi (14.5)** cardinal congruences for `h = |H|`.  The type-I
Frobenius structure has kernel `M_F = H`; by (14.5) its complement has order
`p q`.  Isaacs Lemma 6.1 gives `|H| ≡ 1 mod |C|`, hence both congruences
modulo `p` and modulo `q`. -/
theorem h_modEq_one_mod_p_and_q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    nc.h ≡ 1 [MOD hyp.base.p] ∧ nc.h ≡ 1 [MOD hyp.base.q] := by
  let H0 : Subgroup G := nc.Ldata.typeI_data.frobenius.typeI.typeF.H
  have hH0_eq_typeI_H : H0 = nc.Ldata.typeI_data.H := by
    dsimp [H0]
    rw [nc.Ldata.typeI_data.frobenius.typeI.typeF.H_eq,
      nc.Ldata.typeI_data.H_eq_LF]
  have hH0_eq_H : H0 = nc.Ldata.H :=
    hH0_eq_typeI_H.trans nc.Ldata.typeI_data_H_eq
  have hkernel_card :
      Nat.card ↥(H0.subgroupOf nc.Ldata.typeI_data.L) = Nat.card ↥nc.Ldata.H := by
    have hH0_card :
        Nat.card ↥(H0.subgroupOf nc.Ldata.typeI_data.L) = Nat.card ↥H0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
        dsimp [H0]
        exact nc.Ldata.typeI_data.frobenius.typeI.typeF.H_le)).toEquiv
    rw [hH0_card, hH0_eq_H]
  have hmod_pq : nc.h ≡ 1 [MOD hyp.base.p * hyp.base.q] := by
    have hmod := nc.Ldata.typeI_data.frobenius.frobenius.card_kernel_modEq_one
    rw [hkernel_card, nc.Ldata.typeI_complement_card_eq_pq] at hmod
    rwa [nc.h_eq_card_H]
  exact ⟨hmod_pq.of_dvd (dvd_mul_right hyp.base.p hyp.base.q),
    hmod_pq.of_dvd (dvd_mul_left hyp.base.q hyp.base.p)⟩

end NonConjugateHypothesis

namespace Hypothesis

/-- **Peterfalvi (14.5)** fixed-point-free cardinal consequence for `U`:
`u ≡ 1 mod q`.  The Frobenius action of `W₁` on `U` gives
`|U| ≡ 1 mod |W₁|`; using (13.12), `|U| = u`, and the definition
`q = |W₁|` gives the stated congruence. -/
theorem u_modEq_one_mod_q [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.u ≡ 1 [MOD hyp.base.q] := by
  rcases OddOrder.Peterfalvi.S15.basic_structure _hG hyp.base with ⟨data, _hdata⟩
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base, mul_one]
  have hU_sub_card :
      Nat.card ↥(hyp.base.U.subgroupOf (hyp.base.U ⊔ hyp.base.W1)) =
        Nat.card ↥hyp.base.U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : hyp.base.U ≤ hyp.base.U ⊔ hyp.base.W1)).toEquiv
  have hW1_sub_card :
      Nat.card ↥(hyp.base.W1.subgroupOf (hyp.base.U ⊔ hyp.base.W1)) =
        Nat.card ↥hyp.base.W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : hyp.base.W1 ≤ hyp.base.U ⊔ hyp.base.W1)).toEquiv
  have hmod := data.UW1_frobenius.card_kernel_modEq_one
  rwa [hU_sub_card, hW1_sub_card, hU_card, ← hyp.base.q_eq_card_W1] at hmod

end Hypothesis

/-- The two alternatives of **Peterfalvi (14.14)**. -/
structure OrthogonalitySwitchData {hyp : Hypothesis (G := G)}
    (nc : NonConjugateHypothesis hyp) where
  caseA : Prop
  caseA_bound :
    caseA →
      (((nc.h - 1 : ℕ) : ℚ) / (hyp.base.p * hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ))
  caseB : Prop
  caseB_params : caseB → hyp.base.q = 3 ∧ hyp.base.p = 5

namespace CaseBForSData

/-- **Peterfalvi (14.15)**: the congruence part of the non-full branch.  From
`h = u * x`, the congruence `h ≡ 1 mod p` supplied by (14.5), and the
fixed-point-free congruence `x ≡ 1 mod q`, the divided cyclotomic formula gives
`x ≡ q mod p`; hence `x = q + n p` for some `n`, and then `n ≡ 1 mod q`. -/
theorem exists_x_decomposition_of_nonfull_card_congruences
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (Sdata : CaseBForSData hyp)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hx_mod_q : x ≡ 1 [MOD hyp.base.q]) :
    ∃ n : ℕ, x = hyp.base.q + n * hyp.base.p ∧ n ≡ 1 [MOD hyp.base.q] := by
  let C : ℕ := (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)
  have hmod : hyp.base.p ≡ 1 [MOD hyp.base.q] := by
    by_contra hnot_mod
    exact hu_not_full (Sdata.u_eq_of_not_modEq_one hnot_mod)
  have hC_dvd : hyp.base.q ∣ C := by
    dsimp [C]
    exact OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
      hyp.base.p_prime hmod
  have hu_div : hyp.base.u = C / hyp.base.q := by
    rw [Sdata.u_eq_of_p_modEq_one hmod]
    dsimp [C]
    rw [Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (hyp.base.p - 1) hyp.base.q]
  have hq_u : hyp.base.q * hyp.base.u = C := by
    rw [hu_div, Nat.mul_comm, Nat.div_mul_cancel hC_dvd]
  have hq_h : hyp.base.q * nc.h = C * x := by
    rw [hh_eq, ← mul_assoc, hq_u]
  have hC_mod_p : C ≡ 1 [MOD hyp.base.p] := by
    dsimp [C]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hqh_mod : hyp.base.q * nc.h ≡ hyp.base.q [MOD hyp.base.p] := by
    simpa [mul_one] using hh_mod_p.mul_left hyp.base.q
  rw [hq_h] at hqh_mod
  have hCx_mod : C * x ≡ x [MOD hyp.base.p] := by
    simpa [one_mul] using hC_mod_p.mul_right x
  have hx_mod_p : x ≡ hyp.base.q [MOD hyp.base.p] := hCx_mod.symm.trans hqh_mod
  have hq_le_x : hyp.base.q ≤ x := by
    by_contra hnot
    have hx_lt_q : x < hyp.base.q := Nat.lt_of_not_ge hnot
    have hx_eq_q : x = hyp.base.q :=
      Nat.ModEq.eq_of_lt_of_lt hx_mod_p (lt_trans hx_lt_q hyp.q_lt_p) hyp.q_lt_p
    omega
  rcases (Nat.modEq_iff_exists_eq_add hq_le_x).mp hx_mod_p.symm with
    ⟨n, hx_eq_add⟩
  have hx_eq : x = hyp.base.q + n * hyp.base.p := by
    simpa [mul_comm] using hx_eq_add
  have hnp_mod : n * hyp.base.p ≡ n [MOD hyp.base.q] := by
    simpa [mul_one] using hmod.mul_left n
  have hq_zero : hyp.base.q ≡ 0 [MOD hyp.base.q] := by
    rw [Nat.modEq_zero_iff_dvd]
  have hx_mod_n : x ≡ n [MOD hyp.base.q] := by
    rw [hx_eq]
    simpa using hq_zero.add hnp_mod
  exact ⟨n, hx_eq, hx_mod_n.symm.trans hx_mod_q⟩

/-- **Peterfalvi (14.15)**: in the non-full S-side cyclotomic branch, the
`h = u * x` decomposition and the fixed-point-free congruence estimate give the
lower comparison `p^q < h - 1`.  The proof follows the paragraph
`x > p q`, hence `h > p * (p^q - 1)/(p - 1) > p^q + 1`, with the divided
cyclotomic formula for `u` supplied by **Peterfalvi (13.15)**. -/
theorem p_pow_lt_h_sub_one_of_nonfull_decomposition
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (Sdata : CaseBForSData hyp)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x n : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hx_eq : x = hyp.base.q + n * hyp.base.p)
    (hn_mod : n ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    hyp.base.p ^ hyp.base.q < nc.h - 1 := by
  let C : ℕ := (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)
  have hmod : hyp.base.p ≡ 1 [MOD hyp.base.q] := by
    by_contra hnot_mod
    exact hu_not_full (Sdata.u_eq_of_not_modEq_one hnot_mod)
  have hC_dvd : hyp.base.q ∣ C := by
    dsimp [C]
    exact OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
      hyp.base.p_prime hmod
  have hu_div : hyp.base.u = C / hyp.base.q := by
    rw [Sdata.u_eq_of_p_modEq_one hmod]
    dsimp [C]
    rw [Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm (hyp.base.p - 1) hyp.base.q]
  have hq_u : hyp.base.q * hyp.base.u = C := by
    rw [hu_div, Nat.mul_comm, Nat.div_mul_cancel hC_dvd]
  have hC_sub_ge : hyp.base.p ^ (hyp.base.q - 1) ≤ C - 1 := by
    have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
      (q := hyp.base.p) (p := hyp.base.q)
      hyp.base.p_prime.two_le hyp.base.q_prime.two_le
    dsimp [C]
    exact_mod_cast hleQ
  have hpow_pred_pos : 0 < hyp.base.p ^ (hyp.base.q - 1) :=
    pow_pos hyp.base.p_prime.pos _
  have hC_ge : hyp.base.p ^ (hyp.base.q - 1) + 1 ≤ C := by omega
  have hC_pos : 0 < C := by omega
  have hp_mul_C_gt : hyp.base.p ^ hyp.base.q + 1 < hyp.base.p * C := by
    have hq_pos : 0 < hyp.base.q := hyp.base.q_prime.pos
    have hmul_le :
        hyp.base.p * (hyp.base.p ^ (hyp.base.q - 1) + 1) ≤
          hyp.base.p * C :=
      Nat.mul_le_mul_left hyp.base.p hC_ge
    have hpow_mul :
        hyp.base.p * hyp.base.p ^ (hyp.base.q - 1) = hyp.base.p ^ hyp.base.q := by
      calc
        hyp.base.p * hyp.base.p ^ (hyp.base.q - 1) =
            hyp.base.p ^ (hyp.base.q - 1) * hyp.base.p := by rw [mul_comm]
        _ = hyp.base.p ^ ((hyp.base.q - 1) + 1) := by rw [pow_succ]
        _ = hyp.base.p ^ hyp.base.q := by rw [show hyp.base.q - 1 + 1 = hyp.base.q by omega]
    have hle : hyp.base.p ^ hyp.base.q + hyp.base.p ≤ hyp.base.p * C := by
      calc
        hyp.base.p ^ hyp.base.q + hyp.base.p =
            hyp.base.p * (hyp.base.p ^ (hyp.base.q - 1) + 1) := by
          rw [mul_add, mul_one, hpow_mul]
        _ ≤ hyp.base.p * C := hmul_le
    nlinarith [hle, hyp.base.p_prime.one_lt]
  have hx_min : hyp.base.q + (1 + hyp.base.q) * hyp.base.p ≤ x :=
    hyp.x_ge_caseA_min_of_decomposition_modEq_and_odd hx_eq hn_mod hx_odd
  have hx_gt_pq : hyp.base.p * hyp.base.q < x := by
    nlinarith [hx_min, hyp.base.p_prime.pos, hyp.base.q_prime.pos]
  have hq_h : hyp.base.q * nc.h = C * x := by
    rw [hh_eq, ← mul_assoc, hq_u]
  have hpC_lt_h : hyp.base.p * C < nc.h := by
    have hCx_gt : C * (hyp.base.p * hyp.base.q) < C * x :=
      Nat.mul_lt_mul_of_pos_left hx_gt_pq hC_pos
    have hq_lt : hyp.base.q * (hyp.base.p * C) < hyp.base.q * nc.h := by
      calc
        hyp.base.q * (hyp.base.p * C) = C * (hyp.base.p * hyp.base.q) := by ring
        _ < C * x := hCx_gt
        _ = hyp.base.q * nc.h := hq_h.symm
    exact Nat.lt_of_mul_lt_mul_left hq_lt
  have hpq_add_lt_h : hyp.base.p ^ hyp.base.q + 1 < nc.h :=
    lt_trans hp_mul_C_gt hpC_lt_h
  omega

end CaseBForSData

namespace OrthogonalitySwitchData

/-- The exceptional branch in **Peterfalvi (14.14)** is already in the
`q = 3` situation, so the Section 16 `m > 49/100` bound is available for later
use in the final comparison. -/
theorem m_gt_49_hundredths_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (hcaseB : data.caseB) :
    hyp.base.m > (49 / 100 : ℚ) := by
  exact hyp.m_gt_49_hundredths_of_q_eq_three (data.caseB_params hcaseB).1

/-- In the exceptional branch of **Peterfalvi (14.14)**, the S-side congruence
branch `p ≡ 1 mod q` is impossible: the branch has `(q,p) = (3,5)`, and
`5` is not `1 mod 3`. -/
theorem not_p_modEq_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (hcaseB : data.caseB) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] := by
  intro hmod
  have hparams := data.caseB_params hcaseB
  have hmod' : 5 ≡ 1 [MOD 3] := by
    simpa [hparams.1, hparams.2] using hmod
  unfold Nat.ModEq at hmod'
  norm_num at hmod'

/-- In the exceptional branch of **Peterfalvi (14.14)**, the S-side case-(9.7.b)
order data is forced into its full cyclotomic branch.  This is the consumer form
needed for **Peterfalvi (14.15)**. -/
theorem u_eq_full_cyclotomic_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  Sdata.u_eq_of_not_modEq_one (data.not_p_modEq_one_of_caseB hcaseB)

/-- Numerically, the exceptional branch of **Peterfalvi (14.14)** gives
`u = (5^3 - 1)/(5 - 1) = 31`, once the S-side case-(9.7.b) order data has been
materialized. -/
theorem u_eq_thirty_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB) :
    hyp.base.u = 31 := by
  have hparams := data.caseB_params hcaseB
  have hu := data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB
  rw [hparams.1, hparams.2] at hu
  norm_num at hu
  exact hu

/-- Numerically, the exceptional branch of **Peterfalvi (14.14)** gives
`v = (3^5 - 1)/(3 - 1) = 121`, once the T-side case-(9.7.b) order data from
(14.4) has been materialized. -/
theorem v_eq_one_twenty_one_of_caseB {hyp : Hypothesis (G := G)}
    {nc : NonConjugateHypothesis hyp} (data : OrthogonalitySwitchData nc)
    (Tdata : CaseBForTData hyp) (hcaseB : data.caseB) :
    hyp.base.v = 121 := by
  have hparams := data.caseB_params hcaseB
  rw [Tdata.v_eq, hparams.1, hparams.2]
  norm_num

/-- **Peterfalvi (14.15)**: the case-(a) bound of (14.14) turns a lower
bound `p^q < h - 1` into the key inequality `p^(q - 2) < q^2`. -/
theorem p_pow_q_sub_two_lt_q_sq_of_p_pow_lt_h_sub_one
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseA : data.caseA)
    (hpow_lt_h : hyp.base.p ^ hyp.base.q < nc.h - 1) :
    hyp.base.p ^ (hyp.base.q - 2) < hyp.base.q ^ 2 := by
  have hbound := data.caseA_bound hcaseA
  have hpq_pos_nat : 0 < hyp.base.p * hyp.base.q :=
    Nat.mul_pos hyp.base.p_prime.pos hyp.base.q_prime.pos
  have hpq_posQ : (0 : ℚ) < (hyp.base.p * hyp.base.q : ℚ) := by
    exact_mod_cast hpq_pos_nat
  have hmul := mul_le_mul_of_nonneg_right hbound (le_of_lt hpq_posQ)
  have hleQ : ((nc.h - 1 : ℕ) : ℚ) ≤
      (hyp.base.p * hyp.base.q : ℚ) * ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) := by
    rw [div_mul_cancel₀ _ (ne_of_gt hpq_posQ)] at hmul
    nlinarith [hmul]
  have hsub_ltQ : ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) <
      (hyp.base.p * hyp.base.q : ℚ) := by
    have hsub_lt : hyp.base.p * hyp.base.q - 1 < hyp.base.p * hyp.base.q := by omega
    exact_mod_cast hsub_lt
  have hpow_ltQ : ((hyp.base.p ^ hyp.base.q : ℕ) : ℚ) < ((nc.h - 1 : ℕ) : ℚ) := by
    exact_mod_cast hpow_lt_h
  have hright_lt_sq :
      (hyp.base.p * hyp.base.q : ℚ) * ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) <
        (hyp.base.p * hyp.base.q : ℚ) * (hyp.base.p * hyp.base.q : ℚ) :=
    mul_lt_mul_of_pos_left hsub_ltQ hpq_posQ
  have hpq_sqQ : ((hyp.base.p ^ hyp.base.q : ℕ) : ℚ) <
      ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ^ 2 := by
    calc
      ((hyp.base.p ^ hyp.base.q : ℕ) : ℚ) < ((nc.h - 1 : ℕ) : ℚ) := hpow_ltQ
      _ ≤ (hyp.base.p * hyp.base.q : ℚ) *
          ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) := hleQ
      _ < (hyp.base.p * hyp.base.q : ℚ) * (hyp.base.p * hyp.base.q : ℚ) :=
        hright_lt_sq
      _ = ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ^ 2 := by
        norm_num [Nat.cast_mul, pow_two]
  have hpq_sq_nat : hyp.base.p ^ hyp.base.q < (hyp.base.p * hyp.base.q) ^ 2 := by
    exact_mod_cast hpq_sqQ
  exact p_pow_sub_two_lt_q_sq_of_pow_lt_mul_sq hyp.base.q_prime.two_le hpq_sq_nat

/-- **Peterfalvi (14.15)**: the final numerical contradiction for the
case-(a) branch of (14.14). Once the bound is specialized to `(q,p) = (3,7)`,
it is incompatible with `h ≥ 31 * 19`. -/
theorem caseA_bound_contradiction_of_h_ge_thirty_one_mul_nineteen
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseA : data.caseA)
    (hq3 : hyp.base.q = 3) (hp7 : hyp.base.p = 7) (hh : 31 * 19 ≤ nc.h) :
    False := by
  have hbound := data.caseA_bound hcaseA
  rw [hq3, hp7] at hbound
  norm_num at hbound
  have hleQ : ((nc.h - 1 : ℕ) : ℚ) ≤ 420 := by nlinarith [hbound]
  have hle : nc.h - 1 ≤ 420 := by exact_mod_cast hleQ
  have hge : 588 ≤ nc.h - 1 := by omega
  omega

/-- **Peterfalvi (14.15)**: arithmetic spine of the non-full cyclotomic
case-(a) branch. Once the preceding group-theoretic part of the paragraph has
supplied `p ≡ 1 mod q`, the lower comparison `p^q < h - 1`, and
`h ≥ 31 * 19`, the case-(a) bound forces `q = 3`, then `p = 7`, and finally
the numerical contradiction `31 * 19 - 1 ≤ 20 * 21`. -/
theorem caseA_contradiction_of_p_modEq_one_and_h_bounds
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseA : data.caseA)
    (hmod : hyp.base.p ≡ 1 [MOD hyp.base.q])
    (hpow_lt_h : hyp.base.p ^ hyp.base.q < nc.h - 1)
    (hh : 31 * 19 ≤ nc.h) :
    False := by
  have hpq2 := data.p_pow_q_sub_two_lt_q_sq_of_p_pow_lt_h_sub_one hcaseA hpow_lt_h
  have hq3 := hyp.q_eq_three_of_p_pow_q_sub_two_lt_q_sq hpq2
  have hp_lt_q_sq : hyp.base.p < hyp.base.q ^ 2 := by
    simpa [hq3] using hpq2
  have hp7 :=
    hyp.p_eq_seven_of_q_eq_three_modEq_one_and_lt_q_sq hq3 hmod hp_lt_q_sq
  exact data.caseA_bound_contradiction_of_h_ge_thirty_one_mul_nineteen
    hcaseA hq3 hp7 hh

/-- **Peterfalvi (14.15)**: the non-full cyclotomic branch of the case-(a)
comparison.  If `u` is not the full cyclotomic quotient, then the S-side
case-(9.7.b) order formula puts us in the `p ≡ 1 mod q` branch and gives the
divided cyclotomic value of `u`.  Together with the `h = u * x` decomposition
and the fixed-point-free congruence/parity estimate for `x`, the case-(a) bound
forces `q = 3`, `p = 7`, `u = 19`, `x ≥ 31`, and hence the final numerical
contradiction. -/
theorem caseA_contradiction_of_nonfull_u_data
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x n : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hx_eq : x = hyp.base.q + n * hyp.base.p)
    (hn_mod : n ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    False := by
  have hmod : hyp.base.p ≡ 1 [MOD hyp.base.q] := by
    by_contra hnot_mod
    exact hu_not_full (Sdata.u_eq_of_not_modEq_one hnot_mod)
  have hpow_lt_h :=
    Sdata.p_pow_lt_h_sub_one_of_nonfull_decomposition
      hu_not_full hh_eq hx_eq hn_mod hx_odd
  have hpq2 := data.p_pow_q_sub_two_lt_q_sq_of_p_pow_lt_h_sub_one hcaseA hpow_lt_h
  have hq3 := hyp.q_eq_three_of_p_pow_q_sub_two_lt_q_sq hpq2
  have hp_lt_q_sq : hyp.base.p < hyp.base.q ^ 2 := by
    simpa [hq3] using hpq2
  have hp7 :=
    hyp.p_eq_seven_of_q_eq_three_modEq_one_and_lt_q_sq hq3 hmod hp_lt_q_sq
  have hu19 : hyp.base.u = 19 := by
    have hu := Sdata.u_eq_of_p_modEq_one hmod
    rw [hq3, hp7] at hu
    norm_num at hu
    exact hu
  have hx_min : hyp.base.q + (1 + hyp.base.q) * hyp.base.p ≤ x :=
    hyp.x_ge_caseA_min_of_decomposition_modEq_and_odd hx_eq hn_mod hx_odd
  have hx31 : 31 ≤ x := by
    have hx := hx_min
    rw [hq3, hp7] at hx
    norm_num at hx
    exact hx
  have hh_ge : 31 * 19 ≤ nc.h := by
    rw [hh_eq, hu19]
    nlinarith [hx31]
  exact data.caseA_bound_contradiction_of_h_ge_thirty_one_mul_nineteen
    hcaseA hq3 hp7 hh_ge

/-- **Peterfalvi (14.15)**: consumer form of the non-full case-(a) branch with
only the cardinal/congruence inputs left from (14.5) and the fixed-point-free
`W₁` action.  The congruence theorem above derives `x = q + n p` and
`n ≡ 1 mod q`; the numerical part then closes the case-(a) contradiction. -/
theorem caseA_contradiction_of_nonfull_card_congruences
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    {x : ℕ} (hh_eq : nc.h = hyp.base.u * x)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hx_mod_q : x ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    False := by
  rcases Sdata.exists_x_decomposition_of_nonfull_card_congruences
      hu_not_full hh_eq hh_mod_p hx_mod_q with ⟨n, hx_eq, hn_mod⟩
  exact data.caseA_contradiction_of_nonfull_u_data
    Sdata hcaseA hu_not_full hh_eq hx_eq hn_mod hx_odd

/-- **Peterfalvi (14.15)**: quotient form of the non-full case-(a) branch.
Once the group-theoretic part of (14.5) has supplied `u ∣ h`, `h ≡ 1 mod p`,
and the fixed-point-free congruence for the quotient `x = h / u`, the oddness
of `x` is no longer an input: it follows from `h = |H|` in the ambient
odd-order group. -/
theorem caseA_contradiction_of_nonfull_card_divisibility
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hx_mod_q_of_quotient :
      ∀ x : ℕ, nc.h = hyp.base.u * x → x ≡ 1 [MOD hyp.base.q]) :
    False := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := hx_mod_q_of_quotient x hh_eq
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  exact data.caseA_contradiction_of_nonfull_card_congruences
    Sdata hcaseA hu_not_full hh_eq hh_mod_p hx_mod_q hx_odd

/-- **Peterfalvi (14.15)**: fixed-point-free cardinal-congruence form of the
non-full case-(a) branch.  If the `W₁` action gives both `h ≡ 1 mod q` and
`u ≡ 1 mod q`, then for any quotient decomposition `h = u * x` the quotient
itself satisfies `x ≡ 1 mod q`, which is the congruence used in the displayed
`x = q + n p` calculation. -/
theorem caseA_contradiction_of_nonfull_fpf_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q]) :
    False := by
  exact data.caseA_contradiction_of_nonfull_card_divisibility
    _hG Sdata hcaseA hu_not_full hu_dvd_h hh_mod_p (fun x hh_eq => by
      have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
        simpa [one_mul] using hu_mod_q.mul_right x
      have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
        rw [hh_eq]
        exact hux_mod_q
      exact hh_mod_x.symm.trans hh_mod_q)

/-- **Peterfalvi (14.16)**: the case-(a) branch cannot occur when `H` is
properly larger than `U`, once (14.15) and the fixed-point-free cardinal
congruences have been materialized.  The proof follows Peterfalvi's paragraph:
`x ≡ 1 mod p q` and odd `x ≠ 1` give `x > 2 p q`; the case-(a) bound then
forces `2 u < p q`, contradicting `u ≡ 1 mod p q` and `u > 2 q`. -/
theorem caseA_contradiction_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_full : hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    False := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p] := by
    rw [hu_full]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hx_mod_p : x ≡ 1 [MOD hyp.base.p] := by
    have hux_mod_p : hyp.base.u * x ≡ x [MOD hyp.base.p] := by
      simpa [one_mul] using hu_mod_p.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.p] := by
      rw [hh_eq]
      exact hux_mod_p
    exact hh_mod_x.symm.trans hh_mod_p
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := by
    have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
      simpa [one_mul] using hu_mod_q.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
      rw [hh_eq]
      exact hux_mod_q
    exact hh_mod_x.symm.trans hh_mod_q
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  have hx_gt : 2 * (hyp.base.p * hyp.base.q) < x :=
    hyp.quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
      hx_mod_p hx_mod_q hx_odd (hx_ne_one_of_quotient x hh_eq)
  have hu_pos : 0 < hyp.base.u := by
    have h2q := Sdata.two_q_lt_u
    omega
  have h_lower : 2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h := by
    have hmul :
        hyp.base.u * (2 * (hyp.base.p * hyp.base.q)) < hyp.base.u * x :=
      Nat.mul_lt_mul_of_pos_left hx_gt hu_pos
    rw [hh_eq]
    nlinarith
  have hbound := data.caseA_bound hcaseA
  have hpq_pos_nat : 0 < hyp.base.p * hyp.base.q :=
    Nat.mul_pos hyp.base.p_prime.pos hyp.base.q_prime.pos
  have hpq_posQ : (0 : ℚ) < (hyp.base.p * hyp.base.q : ℚ) := by
    exact_mod_cast hpq_pos_nat
  have hmul_bound := mul_le_mul_of_nonneg_right hbound (le_of_lt hpq_posQ)
  have h_upper_Q : ((nc.h - 1 : ℕ) : ℚ) ≤
      (hyp.base.p * hyp.base.q : ℚ) *
        ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ) := by
    rw [div_mul_cancel₀ _ (ne_of_gt hpq_posQ)] at hmul_bound
    nlinarith [hmul_bound]
  have h_upper_sub : nc.h - 1 ≤
      (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) := by
    exact_mod_cast h_upper_Q
  have h_upper : nc.h ≤
      (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) + 1 := by
    omega
  have htwo_u_lt_pq : 2 * hyp.base.u < hyp.base.p * hyp.base.q := by
    by_contra hnot
    have hpq_le_2u : hyp.base.p * hyp.base.q ≤ 2 * hyp.base.u :=
      Nat.le_of_not_gt hnot
    have hpq_sq_le :
        (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) ≤
          (hyp.base.p * hyp.base.q) * (2 * hyp.base.u) :=
      Nat.mul_le_mul_left (hyp.base.p * hyp.base.q) hpq_le_2u
    have hupper_lt_sq :
        (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) + 1 <
          (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) := by
      have hpq_gt_one : 1 < hyp.base.p * hyp.base.q := by
        nlinarith [hyp.base.p_prime.one_lt, hyp.base.q_prime.one_lt]
      have hs :
          (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) =
            (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q - 1) +
              (hyp.base.p * hyp.base.q) := by
        rw [← Nat.mul_succ]
        have : (hyp.base.p * hyp.base.q - 1).succ = hyp.base.p * hyp.base.q := by
          omega
        rw [this]
      rw [hs]
      omega
    nlinarith [hpq_sq_le, h_lower, h_upper, hupper_lt_sq]
  have hpq_coprime : Nat.Coprime hyp.base.p hyp.base.q :=
    (Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q
  have hu_mod_pq : hyp.base.u ≡ 1 [MOD hyp.base.p * hyp.base.q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hpq_coprime).mp ⟨hu_mod_p, hu_mod_q⟩
  have hu_gt_one : 1 < hyp.base.u := by
    have h2q := Sdata.two_q_lt_u
    nlinarith [hyp.base.q_prime.one_lt]
  rcases (Nat.modEq_iff_exists_eq_add (le_of_lt hu_gt_one)).mp hu_mod_pq.symm with
    ⟨t, hu_eq⟩
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    rw [ht0, mul_zero, add_zero] at hu_eq
    omega
  have ht_ge_one : 1 ≤ t := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht_ne_zero)
  have hu_ge_pq_add_one : hyp.base.p * hyp.base.q + 1 ≤ hyp.base.u := by
    rw [hu_eq]
    have hmul := Nat.mul_le_mul_left (hyp.base.p * hyp.base.q) ht_ge_one
    nlinarith
  nlinarith [htwo_u_lt_pq, hu_ge_pq_add_one]

/-- **Peterfalvi (14.16)**: cardinal/congruence lower bound for the proper
`H > U` alternative.  From `h = u x`, the full cyclotomic value for `u`, and
the fixed-point-free congruences, the quotient satisfies `x ≡ 1 mod p q`; if
`x ≠ 1`, oddness forces `x > 2 p q`, hence `h > 2 p q u`. -/
theorem h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (hu_full : hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p] := by
    rw [hu_full]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hx_mod_p : x ≡ 1 [MOD hyp.base.p] := by
    have hux_mod_p : hyp.base.u * x ≡ x [MOD hyp.base.p] := by
      simpa [one_mul] using hu_mod_p.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.p] := by
      rw [hh_eq]
      exact hux_mod_p
    exact hh_mod_x.symm.trans hh_mod_p
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := by
    have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
      simpa [one_mul] using hu_mod_q.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
      rw [hh_eq]
      exact hux_mod_q
    exact hh_mod_x.symm.trans hh_mod_q
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  have hx_gt : 2 * (hyp.base.p * hyp.base.q) < x :=
    hyp.quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
      hx_mod_p hx_mod_q hx_odd (hx_ne_one_of_quotient x hh_eq)
  have hu_pos : 0 < hyp.base.u := Odd.pos (Nat.odd_mul.mp hux_odd).1
  have hmul :
      hyp.base.u * (2 * (hyp.base.p * hyp.base.q)) < hyp.base.u * x :=
    Nat.mul_lt_mul_of_pos_left hx_gt hu_pos
  rw [hh_eq]
  nlinarith

/-- **Peterfalvi (14.16)**: the numerical gap in the exceptional branch.  If
case-(b) has `(q,p)=(3,5)` and `H > U`, then the lower bound `h > 2 p q u`
gives `(h - 1)/(p q) > (v - 1)/p`; the concrete values `u=31`, `v=121` also
give `(v - 1)/p > (u - 1)/q`. -/
theorem caseB_gap_inequalities_of_h_gt_two_mul_pq_mul_u
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Tdata : CaseBForTData hyp)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB)
    (hh_lower : 2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h) :
    (((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  have hparams := data.caseB_params hcaseB
  have hu31 := data.u_eq_thirty_one_of_caseB Sdata hcaseB
  have hv121 := data.v_eq_one_twenty_one_of_caseB Tdata hcaseB
  have hh930 : 930 < nc.h := by
    have h := hh_lower
    rw [hparams.1, hparams.2, hu31] at h
    norm_num at h
    exact h
  have hh_sub_ge : 930 ≤ nc.h - 1 := by omega
  constructor
  · have hgeQ : (930 : ℚ) ≤ ((nc.h - 1 : ℕ) : ℚ) := by
      exact_mod_cast hh_sub_ge
    have hgt : (24 : ℚ) < ((nc.h - 1 : ℕ) : ℚ) / 15 := by
      nlinarith
    rw [hparams.1, hparams.2, hv121]
    norm_num
    exact hgt
  · rw [hparams.1, hparams.2, hu31, hv121]
    norm_num

/-- **Peterfalvi (14.16)**: the S-side gap in the exceptional branch
excludes case-(c1) of (13.19.c).  After identifying the Type-I kernel with the
current `H` and the complement index with `p q`, the inequality
`(h - 1)/(p q) > (v - 1)/p > (u - 1)/q` is exactly the strict negation of the
case-(c1) bound, so the parity alternative (c2) must hold. -/
theorem typeI_caseC2_of_caseB_sSide_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1 ∨ orth.caseC2)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    orth.caseC2 := by
  apply orth.caseC2_of_gap hcases
  rw [hH, he]
  exact hvu.trans hhv

/-- **Peterfalvi (14.16)**: the T-side gap in the exceptional branch excludes
the dual case-(c1) of (13.19.c).  This is the symmetric input producing the
`eta_i0` parity congruences. -/
theorem typeI_caseC2_of_caseB_tSide_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1_dual ∨ orth.caseC2_dual)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) :
    orth.caseC2_dual := by
  apply orth.caseC2_dual_of_gap hcases
  rw [hH, he]
  exact hhv

/-- **Peterfalvi (14.16)**: the two numerical gaps in case-(b) force both
(13.19.c2) parity alternatives, the S-side one for the `eta_0j` row and the
T-side swapped one for the `eta_i0` column. -/
theorem typeI_caseC2_pair_of_caseB_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1 ∨ orth.caseC2)
    (hcases_dual : orth.caseC1_dual ∨ orth.caseC2_dual)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    orth.caseC2 ∧ orth.caseC2_dual := by
  exact ⟨typeI_caseC2_of_caseB_sSide_gap orth hcases hH he hhv hvu,
    typeI_caseC2_of_caseB_tSide_gap orth hcases_dual hH he hhv⟩

/-- **Peterfalvi (14.16)**: after the case-(b) gaps force both alternatives
(13.19.c2), the usable character output is odd integer pairing on the two
zero-axis families `eta_0j` and `eta_i0`. -/
theorem typeI_eta_axes_odd_of_caseB_gap
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L)
    (hcases : orth.caseC1 ∨ orth.caseC2)
    (hcases_dual : orth.caseC1_dual ∨ orth.caseC2_dual)
    (hH : Nat.card ↥orth.typeISetup.H = nc.h)
    (he : orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    (∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)) ∧
      (∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
          (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
  exact orth.eta_axes_odd_of_caseC2_pair
    (typeI_caseC2_pair_of_caseB_gap orth hcases hcases_dual hH he hhv hvu)

/-- **Peterfalvi (14.16)**: combining the actual (13.19) Type-I
orthogonality output for `L` with the case-(b) numerical gaps gives the two
zero-axis odd pairings needed for the final `eta_ij` expansion.  The remaining
inputs identify the abstract kernel and complement index in the (13.19) data
with the `H` and `p q` already fixed in Section 16. -/
theorem exists_typeI_eta_axes_odd_of_caseB_gap
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (hH_of_orth :
      ∀ orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L,
        Nat.card ↥orth.typeISetup.H = nc.h)
    (he_of_orth :
      ∀ orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L,
        orth.e = hyp.base.p * hyp.base.q)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    ∃ orth : OddOrder.Peterfalvi.S15.TypeIOrthogonalityData hyp.base nc.Ldata.L,
      (∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
          OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
            (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)) ∧
        (∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
          OddOrder.Peterfalvi.S15.OddIntegerInner orth.betaL
            (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
  rcases OddOrder.Peterfalvi.S15.typeI_orthogonality_dichotomy
      _hG hyp.base nc.Ldata.L_maximal nc.Ldata.isTypeI with
    ⟨orth, horth⟩
  exact ⟨orth, typeI_eta_axes_odd_of_caseB_gap orth horth.2.2.2.1 horth.2.2.2.2
    (hH_of_orth orth) (he_of_orth orth) hhv hvu⟩

/-- **Peterfalvi (14.16)**: character-theoretic endpoint of the exceptional
case.  The two strict gap inequalities let (13.19.c) be applied on both the
S- and T-sides, giving the same signed `eta_ij` expansion as in (14.11.2) for
`beta_L^tau`; this contradicts the nonzero pairing in case-(b) of (14.14).
This is the remaining genuinely character-theoretic frontier of (14.16). -/
theorem caseB_character_contradiction_of_gap_inequalities
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (hcaseB : data.caseB)
    (hhv :
      ((nc.h - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (hvu :
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) :
    False := by
  -- (13.19.c) applied to `S` and `T`, followed by the (14.11.2)-style
  -- signed `eta_ij` expansion of `beta_L^tau`.
  sorry

/-- **Peterfalvi (14.16)**: consumer form of the exceptional case-(b) branch
under `H > U`.  All numerical work in the paragraph is discharged here; only
the named character-theoretic endpoint remains as a producer. -/
theorem caseB_contradiction_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Tdata : CaseBForTData hyp)
    (Sdata : CaseBForSData hyp) (hcaseB : data.caseB)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    False := by
  have hu_full := data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB
  have hh_lower := h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
    _hG hu_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q hx_ne_one_of_quotient
  rcases data.caseB_gap_inequalities_of_h_gt_two_mul_pq_mul_u
      Tdata Sdata hcaseB hh_lower with ⟨hhv, hvu⟩
  exact data.caseB_character_contradiction_of_gap_inequalities _hG hcaseB hhv hvu

end OrthogonalitySwitchData

/-- **Peterfalvi (14.14)**: either the `beta_M`--`phi` pairing is nonzero and
`(h - 1) / p q <= p q - 1`, or the `beta_L`--`psi` pairing is nonzero and
`(q,p) = (3,5)`. -/
theorem orthogonality_switch [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (nc : NonConjugateHypothesis hyp) :
    ∃ data : OrthogonalitySwitchData nc, data.caseA ∨ data.caseB := by
  sorry

/-- **Peterfalvi (14.14)--(14.15)**: the full `u` value once the
cardinality consequences of (14.5) have been materialized.  The case-(b)
alternative of (14.14) is already full by the S-side order data; in case (a),
assuming the non-full value contradicts the fixed-point-free cardinal
congruences for `H` and `U`. -/
theorem u_final_value_of_fpf_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp)
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q]) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases orthogonality_switch _hG hyp nc with ⟨data, hcase⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  rcases hcase with hcaseA | hcaseB
  · by_contra hu_not_full
    exact data.caseA_contradiction_of_nonfull_fpf_card_congruences
      _hG Sdata hcaseA hu_not_full hu_dvd_h hh_mod_p hh_mod_q hu_mod_q
  · exact data.u_eq_full_cyclotomic_of_caseB Sdata hcaseB

/-- **Peterfalvi (14.15)**: `u` has the full cyclotomic value
`(p^q - 1) / (p - 1)`.

The proof consumes the cardinal consequences of (14.5): `u ∣ h`, the two
Frobenius-kernel congruences for `h`, and the fixed-point-free cardinal
congruence for `U`.  The arithmetic contradiction is packaged in
`u_final_value_of_fpf_card_congruences`. -/
theorem u_final_value [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  exact u_final_value_of_fpf_card_congruences _hG hyp nc (nc.u_dvd_h _hG)
    hh_mod_p hh_mod_q (hyp.u_modEq_one_mod_q _hG)

/-- **Peterfalvi (14.16)**: in the non-conjugate case, the kernel `H` is
exactly `U`. -/
theorem H_eq_U [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (nc : NonConjugateHypothesis hyp) :
    nc.Ldata.H = hyp.base.U := by
  by_contra hHU
  rcases orthogonality_switch _hG hyp nc with ⟨data, hcase⟩
  rcases caseB_for_T _hG hyp with ⟨Tdata, _hT_caseB, _hv_eq⟩
  rcases caseB_for_S _hG hyp nc.Ldata with ⟨Sdata, _hS_caseB⟩
  have hu_full := u_final_value _hG hyp nc
  rcases nc.h_modEq_one_mod_p_and_q _hG with ⟨hh_mod_p, hh_mod_q⟩
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, OddOrder.Peterfalvi.S15.c_eq_one _hG hyp.base, mul_one]
  have hU_le_H : hyp.base.U ≤ nc.Ldata.H := by
    rw [← nc.Ldata.typeI_data_H_eq]
    exact nc.Ldata.typeI_data.U_le_H
  have hx_ne_one_of_quotient :
      ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1 := by
    intro x hh_eq hx1
    have hH_card_eq_U_card : Nat.card ↥nc.Ldata.H = Nat.card ↥hyp.base.U := by
      rw [← nc.h_eq_card_H, hh_eq, hx1, mul_one, hU_card]
    have hU_eq_H : hyp.base.U = nc.Ldata.H :=
      Subgroup.eq_of_le_of_card_ge hU_le_H (le_of_eq hH_card_eq_U_card)
    exact hHU hU_eq_H.symm
  rcases hcase with hcaseA | hcaseB
  · exact data.caseA_contradiction_of_full_u_card_congruences
      _hG Sdata hcaseA hu_full (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient
  · exact data.caseB_contradiction_of_full_u_card_congruences
      _hG Tdata Sdata hcaseB (nc.u_dvd_h _hG) hh_mod_p hh_mod_q
      (hyp.u_modEq_one_mod_q _hG) hx_ne_one_of_quotient

/-- **Peterfalvi (14.3)**: a type-I maximal subgroup `L` over `N_G(U)` together
with its Dade data exists.  This packages (13.17) (the type-I-over-normalizer
Frobenius structure `S15.typeII_overNormalizer_frobenius`) with the Dade isometry
`τ`, its extension `τ₁`, the degree-`|L:H|` character `φ`, and the virtual
characters `β_S`, `β_T`, `β_L` of (14.3).  The construction is gated on the §13
character theory (Dade isometry + type-I structure). -/
theorem exists_LHypothesis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (LHypothesis hyp) := by
  sorry

/-- **Peterfalvi (14.10)**: a type-I maximal subgroup `M` over `N_G(V)` together
with its Dade data exists.  Symmetric to `exists_LHypothesis`, packaging (13.17)
for the `V`-side with the Dade data and the virtual character `β_M` of (14.10).
Gated on the §13 character theory. -/
theorem exists_MHypothesis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (MHypothesis hyp) := by
  sorry

/-- **Peterfalvi (14.16)**→(14.7) bridge: if the Fitting kernel `H` of `L`
coincides with `U`, then `U` is characteristic in `H` (it is `H` itself).  This
is what lets the non-conjugate case `H = U` of (14.16) feed back into (14.7). -/
theorem U_characteristic_of_H_eq_U {hyp : Hypothesis (G := G)}
    (Ldata : LHypothesis hyp) (hHU : Ldata.H = hyp.base.U) :
    Ldata.U_characteristic_in_H := by
  sorry

/-- **Peterfalvi (14.2)**: the field-normalizer configuration follows from the
Section 16 hypotheses.

This assembles Peterfalvi's concluding paragraph "By (14.12), (14.16) and (14.7),
the proof of Theorem (14.2) is complete."  Take the type-I subgroup `L` over
`N_G(U)` ((14.3), `exists_LHypothesis`) and split on whether `U` is characteristic
in `H`:

* if it is, (14.7) `field_normalizer_of_U_characteristic` finishes;
* otherwise take the type-I subgroup `M` over `N_G(V)` ((14.10),
  `exists_MHypothesis`) and split on whether `L` is conjugate to `M`:
  * if it is, (14.12) `field_normalizer_of_L_conj_M` finishes;
  * otherwise (14.13)–(14.16) `H_eq_U` give `H = U`, so `U` is characteristic in
    `H` (`U_characteristic_of_H_eq_U`), contradicting the branch assumption. -/
theorem field_normalizer_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hyp
  by_cases hchar : Ldata.U_characteristic_in_H
  · exact field_normalizer_of_U_characteristic _hG hyp Ldata hchar
  · obtain ⟨Mdata⟩ := exists_MHypothesis _hG hyp
    by_cases hconj : ∃ g : G, MulAut.conj g • Ldata.L = Mdata.M
    · exact field_normalizer_of_L_conj_M _hG hyp Ldata Mdata hconj
    · exact absurd
        (U_characteristic_of_H_eq_U Ldata
          (H_eq_U _hG hyp
            { Ldata := Ldata, Mdata := Mdata, not_conj := hconj,
              h := Nat.card ↥Ldata.H, h_eq_card_H := rfl }))
        hchar

/-- **Peterfalvi Section 16 + BG Appendix C**: BG Appendix C turns the
field-normalizer configuration into `p <= q`, contradicting (14.1). -/
theorem nonexistence_of_G [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (bgAppendixC : FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q) :
    False := by
  rcases field_normalizer_structure hG hyp with ⟨data⟩
  exact (not_lt_of_ge (bgAppendixC data)) hyp.q_lt_p

end OddOrder.Peterfalvi.S16
