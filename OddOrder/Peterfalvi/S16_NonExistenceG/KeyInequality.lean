import OddOrder.Peterfalvi.S16_NonExistenceG.SubgroupL

/-!
# Peterfalvi (14.8)-(14.9) — key inequality, T is type II

Split from the former monolithic `OddOrder.Peterfalvi.S16_NonExistenceG` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S16
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]


/-! ## (14.8)--(14.9): the key inequality and `T` is type II -/


theorem cyclotomic_quotient_modEq_one_mod_base {p q : ℕ}
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

/-- **Peterfalvi (14.7) value argument** (arithmetic core).  In case (9.7.b), the
`p ≡ 1 mod q` branch of (13.15) is incompatible with `u ≡ 1 mod p` — the congruence the
fixed-point-free action of `W₂^y` on `U` supplies in (14.7).  In that branch
`q · u = (p^q-1)/(p-1) ≡ 1 mod p` (geometric sum), so `q ≡ q·u ≡ 1 mod p` (using
`u ≡ 1 mod p`), forcing `p ∣ q - 1` against `q < p`.  Hence `u` takes its full cyclotomic
value and `q ∤ (p-1)` (i.e. `¬ p ≡ 1 mod q`).  Reduces the (14.7) value argument to the single
fixed-point-free congruence `u ≡ 1 mod p`; cites the (sorried) case-(b) data `CaseBForSData`. -/
theorem u_eq_full_of_caseB_of_u_modEq_one_mod_p {hyp : Hypothesis (G := G)}
    (Sdata : CaseBForSData hyp) (hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p]) :
    hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) ∧
      ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] := by
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · exfalso
    have hqdvd : hyp.base.q ∣ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
      OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one hyp.base.p_prime hmod
    have hu_div : hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q := by
      rw [Sdata.u_eq_of_p_modEq_one hmod, Nat.div_div_eq_div_mul,
        Nat.mul_comm (hyp.base.p - 1) hyp.base.q]
    have hqu : hyp.base.q * hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
      rw [hu_div, Nat.mul_div_cancel' hqdvd]
    have hC_mod : (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) ≡ 1 [MOD hyp.base.p] :=
      cyclotomic_quotient_modEq_one_mod_base hyp.base.p_prime.two_le hyp.base.q_prime.pos
    have hqu_mod : hyp.base.q * hyp.base.u ≡ 1 [MOD hyp.base.p] := by rw [hqu]; exact hC_mod
    have hqu_mod2 : hyp.base.q * hyp.base.u ≡ hyp.base.q * 1 [MOD hyp.base.p] :=
      Nat.ModEq.mul_left hyp.base.q hu_mod_p
    have hq_mod : hyp.base.q ≡ 1 [MOD hyp.base.p] := by
      have h := hqu_mod2.symm.trans hqu_mod
      simpa using h
    have hp_dvd : hyp.base.p ∣ hyp.base.q - 1 :=
      (Nat.modEq_iff_dvd' hyp.base.q_prime.one_lt.le).mp hq_mod.symm
    have hqpos : 0 < hyp.base.q - 1 := by have := hyp.base.three_le_q; omega
    have hple : hyp.base.p ≤ hyp.base.q - 1 := Nat.le_of_dvd hqpos hp_dvd
    have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
    omega
  · exact ⟨Sdata.u_eq_of_not_modEq_one hmod, hmod⟩

/-- **(14.7) assembly from the fixed-point-free congruence.**  The tightest reduction of (14.7):
given the (14.7) fixed-point-free congruence `u ≡ 1 mod p` (the `W₂^y`-on-`U` input), `U` cyclic,
`W₂ ≤ P`, and part (14.2)(b), the field-normalizer data exists.  The value argument
`u_eq_full_of_caseB_of_u_modEq_one_mod_p` turns `u ≡ 1 mod p` into `u = (p^q-1)/(p-1)` and
`q ∤ (p-1)` (using the case-(b) certificate `caseB_for_S Ldata`), which then feed
`field_normalizer_of_U_characteristic_of_inputs`.  The cardinal substitution uses the Core
λ-dichotomy endpoint for (13.12). -/
theorem field_normalizer_of_U_characteristic_of_fpf [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (Ldata : LHypothesis hyp)
    (hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p])
    (hW2_le_P : hyp.base.W2 ≤ hyp.base.P)
    (hQ_elemAb : IsElementaryAbelian hyp.base.q ↥hyp.base.Q)
    (hW2_norm_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G))
    (yQ : G) (hyQ_mem : yQ ∈ hyp.base.Q)
    (hW2_conj_y : MulAut.conj yQ • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)) :
    Nonempty (FieldNormalizerData hyp) := by
  obtain ⟨Sdata, _⟩ := caseB_for_S hG hyp Ldata
  obtain ⟨hu_full, hnot_mod⟩ := u_eq_full_of_caseB_of_u_modEq_one_mod_p Sdata hu_mod_p
  -- bridge `|U| = u` via (13.12) `c = 1`
  have hU_card : Nat.card ↥hyp.base.U = hyp.base.u := by
    rw [hyp.base.card_U_eq_uc, hyp.base.c_eq_one_of_lambda_dichotomy hG, mul_one]
  have hcyc : Nat.Coprime
      ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) (hyp.base.p - 1) :=
    OddOrder.Peterfalvi.S15.cyclotomic_quotient_coprime_of_not_modEq_one
      hyp.base.p_prime hyp.base.q_prime hnot_mod
  exact field_normalizer_of_U_characteristic_of_inputs hG hyp (hU_card.trans hu_full)
    hW2_le_P hcyc hQ_elemAb hW2_norm_Q yQ hyQ_mem hW2_conj_y


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
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) := by
  -- (14.8) is the proven arithmetic consumer `key_inequality_of_caseB_outputs`
  -- fed by the (14.4) T-side and (14.6) S-side case-(9.7.b) data.  The S-side
  -- data `caseB_for_S` needs an `LHypothesis`, supplied by `exists_LHypothesis`.
  obtain ⟨Ldata⟩ := exists_LHypothesis _hG hnoV hncH0C hyp
  exact key_inequality_of_caseB_outputs (caseB_for_T _hG hyp) (caseB_for_S _hG hyp Ldata)

end OddOrder.Peterfalvi.S16
