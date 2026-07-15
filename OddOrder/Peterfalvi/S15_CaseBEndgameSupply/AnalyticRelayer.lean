/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.Eta10HCorrection
import OddOrder.Peterfalvi.S15_CaseBEndgameSupply.Eta10Correction

/-!
# Peterfalvi §13 (pp. 84–86) — Core-typed analytic norm estimates

This file relayers Peterfalvi (13.9)–(13.10) below the honest character-degree supply.
The norm estimates use `CharacterDegreeCore`, `LambdaClusterData`, and explicit case-B
structural facts, avoiding the overstrong legacy `CharacterDegreeData` carrier.
-/

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

section /- (13.10.1): the lambda estimate -/

open scoped FiniteInduce in
/-- **Peterfalvi (13.6) + Parseval, Core form**: the first analytic estimate in (13.10).

The norm-one virtual character and the sharp norm bound are the honest Core outputs
`lambda_tau1_norm_one_core` and `lambda_tau1_sharp_norm_lower_core`.  The two case-B
values are explicit inputs; `|Q| = q^p` is the unconditional (13.2.b) theorem. -/
theorem CharacterDegreeCore.analyticEstimate_lambda_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    (1 : ℚ) ≥ 1 / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset (core.tau1S lam.lambda) / (Nat.card G : ℚ) + 1
        - (hyp.u : ℚ) * (hyp.q : ℚ) / ((hyp.c : ℚ) * (hyp.p : ℚ) ^ hyp.q) := by
  classical
  obtain ⟨hZ, hn, -⟩ := lambda_tau1_norm_one_core core lam
  have hQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p := hyp.card_Q_eq_qp hG
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  set φ : ClassFunction G ℂ := core.tau1S lam.lambda with hφdef
  have hsplit := hyp.global_normSq_split hG φ hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖φ 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharp := core.lambda_tau1_sharp_norm_lower_core hG lam
  rw [← hφdef] at hsharp
  have hQnonneg : (0 : ℝ) ≤ (hyp.T.index : ℝ)
      * ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2 := by
    have h1 : (0 : ℝ) ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2 :=
      Finset.sum_nonneg fun x _ => by positivity
    positivity
  have hGal := OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZ
    hyp.G0Finset_cyclicClosed
  have hspec := normSqSumQ_spec hGal
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hGeq : (Nat.card G : ℝ)
      = (hyp.p : ℝ) ^ hyp.q * ((hyp.u : ℝ) * (hyp.c : ℝ)) * (hyp.q : ℝ)
        * (hyp.S.index : ℝ) := by
    have h := hyp.S.card_mul_index
    rw [hyp.card_S_val hG] at h
    exact_mod_cast h.symm
  have hc0 : (0 : ℝ) < (hyp.c : ℝ) := by
    have : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
    exact_mod_cast this
  have hp0 : (0 : ℝ) < (hyp.p : ℝ) := by
    have := hyp.three_le_p
    exact_mod_cast (by omega : 0 < hyp.p)
  rw [ge_iff_le, ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspec]
  set s : ℝ := ∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2 with hsdef
  set w : ℝ := (hyp.u : ℝ) * (hyp.q : ℝ) /
    ((hyp.c : ℝ) * (hyp.p : ℝ) ^ hyp.q) with hwdef
  have hwg : w * (Nat.card G : ℝ) =
      (hyp.S.index : ℝ) * ((hyp.u : ℝ) * (hyp.q : ℝ)) ^ 2 := by
    rw [hwdef, hGeq]
    field_simp
  have hSidx0 : (0 : ℝ) ≤ (hyp.S.index : ℝ) := by positivity
  have hkey : 1 + s ≤ w * (Nat.card G : ℝ) := by
    rw [hwg]
    have hSGeq : (hyp.S.index : ℝ) * (Nat.card ↥hyp.S : ℝ) = (Nat.card G : ℝ) := by
      exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
    have huq : ((hyp.u * hyp.q : ℕ) : ℝ) = (hyp.u : ℝ) * (hyp.q : ℝ) := by
      push_cast
      ring
    rw [huq] at hsharp
    have hHbound := mul_le_mul_of_nonneg_left hsharp hSidx0
    rw [nsmul_eq_mul, nsmul_eq_mul] at hsplit
    linarith [hsplit, hone, hHbound, hQnonneg, hSGeq]
  have hdiv : (1 + s) / (Nat.card G : ℝ) ≤ w :=
    (div_le_iff₀ hg0).mpr (by linarith [hkey])
  calc 1 / (Nat.card G : ℝ) + s / (Nat.card G : ℝ) + 1 - w
      = (1 + s) / (Nat.card G : ℝ) + 1 - w := by rw [add_div]
    _ ≤ w + 1 - w := by linarith [hdiv]
    _ = 1 := by ring

end

section /- (13.10.2): the eta10 estimate -/

open scoped FiniteInduce in
/-- **Peterfalvi (13.7)+(13.8), Core form**: the second analytic estimate in (13.10).

The `H^#` and `Q^#` lower bounds are supplied by the two chosen-base correction
packages.  The latter uses exactly the explicit case-B facts and commutativity of `Q`;
the remaining cardinal identities are derived in place. -/
theorem CharacterDegreeCore.analyticEstimate_eta_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    (1 : ℚ) ≥ 1 / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ)
        + ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ)
        + (1 / (hyp.p : ℚ) - 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1))
          + 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1) * (hyp.q : ℚ) ^ hyp.p)) := by
  classical
  have hQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p := hyp.card_Q_eq_qp hG
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  have hZ := hyp.eta10_mem_ZIrr
  have hn := hyp.eta10_inner_self_one
  have hsplit := hyp.global_normSq_split hG hyp.eta10 hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖hyp.eta10 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharpH := core.eta10_Hsharp_norm_lower_core hG
  have hsharpQ := hyp.eta10_Qsharp_norm_lower_core hG hD hv hQcomm pins
  have hGal := OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZ
    hyp.G0Finset_cyclicClosed
  have hspec := normSqSumQ_spec hGal
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p := Nat.one_le_pow _ _ (by omega)
  have hdvd : (hyp.q - 1) ∣ (hyp.q ^ hyp.p - 1) := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.q 1 hyp.p
  have hvq : (hyp.v : ℝ) * ((hyp.q : ℝ) - 1) = (hyp.q : ℝ) ^ hyp.p - 1 := by
    have h := Nat.div_mul_cancel hdvd
    rw [← hv] at h
    have := congrArg (Nat.cast (R := ℝ)) h
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ hyp.q), Nat.cast_sub hqp1] at this
    convert this using 2
  have hderivT : (Nat.card ↥(derivedInG hyp.T) : ℝ) =
      (hyp.q : ℝ) ^ hyp.p * (hyp.v : ℝ) := by
    have h := hyp.card_deriv_T_eq hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hTval : (Nat.card ↥hyp.T : ℝ) =
      (hyp.q : ℝ) ^ hyp.p * (hyp.v : ℝ) * (hyp.p : ℝ) := by
    have h := hyp.card_T_eq hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hSGeq : (hyp.S.index : ℝ) * (Nat.card ↥hyp.S : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
  have hTGeq : (hyp.T.index : ℝ) * (Nat.card ↥hyp.T : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.T) hyp.T.index ▸ hyp.T.card_mul_index
  have hS0 : (0 : ℝ) < (Nat.card ↥hyp.S : ℝ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.S)
  have hT0 : (0 : ℝ) < (Nat.card ↥hyp.T : ℝ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.T)
  have hSidx0 : (0 : ℝ) < (hyp.S.index : ℝ) := by
    rcases (Nat.cast_pos (α := ℝ)).mpr (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := hyp.S))) with h
    exact h
  have hTidx0 : (0 : ℝ) < (hyp.T.index : ℝ) := by
    rcases (Nat.cast_pos (α := ℝ)).mpr (Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := hyp.T))) with h
    exact h
  have hp0 : (0 : ℝ) < (hyp.p : ℝ) := by exact_mod_cast (by omega : 0 < hyp.p)
  have hq10 : (0 : ℝ) < (hyp.q : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (hyp.q : ℝ) := by exact_mod_cast hq3
    linarith
  have hqp0 : (0 : ℝ) < (hyp.q : ℝ) ^ hyp.p := by
    have : (0 : ℝ) < (hyp.q : ℝ) := by exact_mod_cast (by omega : 0 < hyp.q)
    positivity
  have hv0 : (0 : ℝ) < (hyp.v : ℝ) := by exact_mod_cast (by omega : 0 < hyp.v)
  rw [ge_iff_le, ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspec]
  set s : ℝ := ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 with hsdef
  set sH : ℝ := ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
    ‖hyp.eta10 x‖ ^ 2 with hsHdef
  set sQ : ℝ := ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset,
    ‖hyp.eta10 x‖ ^ 2 with hsQdef
  rw [nsmul_eq_mul, nsmul_eq_mul] at hsplit
  set TT : ℝ := 1 / (hyp.p : ℝ) - 1 / ((hyp.p : ℝ) * ((hyp.q : ℝ) - 1))
      + 1 / ((hyp.p : ℝ) * ((hyp.q : ℝ) - 1) * (hyp.q : ℝ) ^ hyp.p) with hTTdef
  have hveq : (hyp.v : ℝ) = ((hyp.q : ℝ) ^ hyp.p - 1) / ((hyp.q : ℝ) - 1) := by
    rw [eq_div_iff hq10.ne']
    exact hvq
  have hTT : TT = ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) /
      (Nat.card ↥hyp.T : ℝ) := by
    rw [hTTdef, hderivT, hTval, hveq]
    have hqp1' : (1 : ℝ) < (hyp.q : ℝ) ^ hyp.p := by
      have h1 : (1 : ℕ) < hyp.q ^ hyp.p := by
        calc 1 < hyp.q := by omega
          _ ≤ hyp.q ^ hyp.p := Nat.le_self_pow (by omega) _
      exact_mod_cast h1
    have hnum0 : (hyp.q : ℝ) ^ hyp.p - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hH1 : (1 : ℕ) ≤ Nat.card ↥hyp.H := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hterm3 : ((Nat.card ↥hyp.H - 1 : ℕ) : ℝ) / (Nat.card ↥hyp.S : ℝ)
      = (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1) / (Nat.card G : ℝ) := by
    rw [← hSGeq, Nat.cast_sub hH1, Nat.cast_one,
      mul_div_mul_left _ _ hSidx0.ne']
  have hterm4 : TT = (hyp.T.index : ℝ)
      * ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) /
        (Nat.card G : ℝ) := by
    rw [hTT, ← hTGeq, mul_div_mul_left _ _ hTidx0.ne']
  have hbound : 1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
      + (hyp.T.index : ℝ) *
        ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)
      ≤ (Nat.card G : ℝ) := by
    have hHb := mul_le_mul_of_nonneg_left hsharpH hSidx0.le
    have hQb := mul_le_mul_of_nonneg_left hsharpQ hTidx0.le
    nlinarith [hsplit, hone, hHb, hQb]
  rw [hterm3, hterm4]
  have hfinal : (1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
      + (hyp.T.index : ℝ) *
        ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)) /
      (Nat.card G : ℝ) ≤ 1 := by
    rw [div_le_one hg0]
    exact hbound
  calc 1 / (Nat.card G : ℝ) + s / (Nat.card G : ℝ)
        + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1) / (Nat.card G : ℝ)
        + (hyp.T.index : ℝ) *
            ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) /
              (Nat.card G : ℝ)
      = (1 + s + (hyp.S.index : ℝ) * ((Nat.card ↥hyp.H : ℝ) - 1)
          + (hyp.T.index : ℝ) *
            ((Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2)) /
          (Nat.card G : ℝ) := by
        rw [add_div, add_div, add_div]
    _ ≤ 1 := hfinal

end

section /- (13.9.a): disjoint-cover counting -/

/-- **Peterfalvi (13.9.a), explicit case-B facts form**: the four-piece disjoint-cover
counting identity.  This is the legacy `analyticCounting_disjointCover` proof with the
uninhabitable character-degree obtain removed; only the two genuine (13.4) values are
passed in. -/
theorem Hypothesis.analyticCounting_disjointCover_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    (1 : ℚ) = 1 / (Nat.card G : ℚ) + (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ)
        + ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ)
        + ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p := hyp.card_Q_eq_qp hG
  have hd1 : hyp.d = 1 := by rw [hyp.d_eq_card_D, hD, Subgroup.card_bot]
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  have hqp_ge : hyp.q * hyp.q ≤ hyp.q ^ hyp.p := by
    calc hyp.q * hyp.q = hyp.q ^ 2 := (sq hyp.q).symm
      _ ≤ hyp.q ^ hyp.p := Nat.pow_le_pow_right (by omega) (by omega)
  have hv2 : 2 ≤ hyp.v := by
    rw [hv, Nat.le_div_iff_mul_le (by omega : 0 < hyp.q - 1)]
    have h3q : 3 * hyp.q ≤ hyp.q * hyp.q := Nat.mul_le_mul_right _ hq3
    omega
  have hvd : hyp.v * hyp.d ≠ 1 := by rw [hd1, mul_one]; omega
  have hsplit := hyp.card_univ_split hG hQ hvd
  have key : (Nat.card G : ℚ) = 1 + (hyp.G0Finset.card : ℚ)
      + (hyp.S.index : ℚ) * ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ)
      + (hyp.T.index : ℚ) * ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) := by
    exact_mod_cast hsplit
  have hG0 : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos (α := G)
  have hS0 : (0 : ℚ) < (Nat.card ↥hyp.S : ℚ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.S)
  have hT0 : (0 : ℚ) < (Nat.card ↥hyp.T : ℚ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.T)
  have hSidx : (hyp.S.index : ℚ) * (Nat.card ↥hyp.S : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
  have hTidx : (hyp.T.index : ℚ) * (Nat.card ↥hyp.T : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.T) hyp.T.index ▸ hyp.T.card_mul_index
  have hSidx0 : (hyp.S.index : ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hSidx
    exact hG0.ne' hSidx.symm
  have hTidx0 : (hyp.T.index : ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hTidx
    exact hG0.ne' hTidx.symm
  have hq1 : (1 : ℕ) ≤ hyp.q := by omega
  have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p := Nat.one_le_pow _ _ (by omega)
  have hdvd : (hyp.q - 1) ∣ (hyp.q ^ hyp.p - 1) := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.q 1 hyp.p
  have hvq : (hyp.v : ℚ) * ((hyp.q : ℚ) - 1) = (hyp.q : ℚ) ^ hyp.p - 1 := by
    have h := Nat.div_mul_cancel hdvd
    rw [← hv] at h
    have := congrArg (Nat.cast (R := ℚ)) h
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hqp1] at this
    convert this using 2
  have hTval : (Nat.card ↥hyp.T : ℚ) =
      (hyp.q : ℚ) ^ hyp.p * (hyp.v : ℚ) * (hyp.p : ℚ) := by
    have h := hyp.card_T_eq hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hQ1 : ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) = (hyp.q : ℚ) ^ hyp.p - 1 := by
    rw [hQ, Nat.cast_sub hqp1]
    push_cast
    ring
  have hterm3 : ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ) / (Nat.card ↥hyp.S : ℚ)
      = (hyp.S.index : ℚ) * ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ) /
        (Nat.card G : ℚ) := by
    rw [← hSidx, mul_div_mul_left _ _ hSidx0]
  have hv0 : (hyp.v : ℚ) ≠ 0 := by
    have : (2 : ℚ) ≤ (hyp.v : ℚ) := by exact_mod_cast hv2
    linarith
  have hq10 : (hyp.q : ℚ) - 1 ≠ 0 := by
    have : (3 : ℚ) ≤ (hyp.q : ℚ) := by exact_mod_cast hq3
    linarith
  have hp0 : (hyp.p : ℚ) ≠ 0 := by
    have : (3 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hp3
    linarith
  have hqp0 : (hyp.q : ℚ) ^ hyp.p ≠ 0 := by
    have : (1 : ℚ) ≤ (hyp.q : ℚ) ^ hyp.p := by exact_mod_cast hqp1
    linarith
  have hterm4 : ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p)
      = (hyp.T.index : ℚ) * ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) /
        (Nat.card G : ℚ) := by
    rw [hQ1, ← hvq, ← hTidx, hTval]
    field_simp
  rw [hterm3, hterm4, ← add_div, ← add_div, ← add_div, ← key, div_self hG0.ne']

end

section /- (13.9.a): nonvanishing on the generic set -/

/-- **Peterfalvi (13.9.a), Core form**: on `G₀`, `λ^{τ₁}` and `η₁₀` do not
vanish simultaneously.  The proof uses the Core/cluster off-`H^#` formula, the regular
value formula, and the four-corner grid relation; no monolithic character-degree carrier
is involved. -/
theorem CharacterDegreeCore.G0_nonvanishing_dichotomy_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    ∀ x ∈ hyp.G0Finset, core.tau1S lam.lambda x ≠ 0 ∨ hyp.eta10 x ≠ 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro x hxF
  have hxG0 : x ∈ hyp.G0 := (Set.Finite.mem_toFinset _).mp hxF
  obtain ⟨hx1, hxH, hxQ⟩ := (hyp.mem_G0_iff x).mp hxG0
  by_cases hreg : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))
  · right
    obtain ⟨w, hwmem, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hreg
    obtain ⟨hwW, hwnot⟩ := hwmem
    have hconjval : hyp.eta10 x = hyp.eta10 w := by
      rw [← hg]
      exact (OddOrder.RepresentationTheory.ClassFunction.of_isConj hyp.eta10
        (isConj_iff.mpr ⟨g, rfl⟩)).symm
    have hval : hyp.eta10 w =
        hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨w, hwW⟩ := by
      rw [show hyp.eta10 = hyp.eta ⟨1, hyp.q_prime.one_lt⟩
        ⟨0, hyp.p_prime.pos⟩ from rfl, hyp.eta_eq_tau_omega]
      exact hyp.tau3_apply_of_regular _ _ hwW hwnot
    rw [hconjval, hval]
    intro h0
    have hmul := hyp.omega_mul ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩
      ⟨w, hwW⟩ ⟨w, hwW⟩⁻¹
    rw [mul_inv_cancel, hyp.omega_apply_one, h0, zero_mul] at hmul
    exact one_ne_zero hmul
  · by_contra hboth
    push Not at hboth
    obtain ⟨hl0, he0⟩ := hboth
    obtain ⟨δ, hδ, hlam⟩ :=
      lambda_tau1_apply_eq_of_not_mem_H_sat_core hG core lam hxH
    have hδ0 : (δ : ℂ) ≠ 0 := by
      rcases hδ with rfl | rfl <;> norm_num
    have hsum0 : ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x = 0 := by
      have h := hlam.symm.trans hl0
      exact (mul_eq_zero.mp h).resolve_left hδ0
    have he10 : hyp.tau3 (hyp.omega ⟨1, hyp.q_prime.one_lt⟩
        ⟨0, hyp.p_prime.pos⟩) x = 0 := by
      rw [← hyp.eta_eq_tau_omega]
      exact he0
    have hrow := hyp.eta_row_vanish_of_one_zero x he10
    have hcol1ne : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠
        ⟨0, hyp.p_prime.pos⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) one_ne_zero
    have hfc : ∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
        hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x
          = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1 := by
      intro i hi
      have h4 := hyp.eta_fourcorner_vanish i ⟨1, hyp.p_prime.one_lt⟩ hi hcol1ne x hreg
      rw [hrow i hi] at h4
      rw [hyp.eta_eq_tau_omega, hyp.eta_eq_tau_omega]
      linear_combination h4
    have hsplit : (0 : ℂ) =
        (hyp.q : ℂ) * hyp.eta ⟨0, hyp.q_prime.pos⟩
          ⟨1, hyp.p_prime.one_lt⟩ x - ((hyp.q : ℂ) - 1) := by
      have hqpos : 0 < hyp.q := hyp.q_prime.pos
      have hcard : (Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q)).card = hyp.q - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]
      calc (0 : ℂ) = ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x :=
            hsum0.symm
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ∑ i ∈ Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q),
                hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ∑ _i ∈ Finset.univ.erase (⟨0, hqpos⟩ : Fin hyp.q),
                (hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1) := by
          congr 1
          exact Finset.sum_congr rfl (fun i hi => hfc i (Finset.ne_of_mem_erase hi))
        _ = hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            + ((hyp.q - 1 : ℕ) : ℂ)
              * (hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x - 1) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ = (hyp.q : ℂ) * hyp.eta ⟨0, hqpos⟩ ⟨1, hyp.p_prime.one_lt⟩ x
            - ((hyp.q : ℂ) - 1) := by
          have h1 : ((hyp.q - 1 : ℕ) : ℂ) = (hyp.q : ℂ) - 1 := by
            rw [Nat.cast_sub hyp.q_prime.one_lt.le, Nat.cast_one]
          rw [h1]
          ring
    have hZ : hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ ∈ ZIrr G := by
      rw [hyp.eta_eq_tau_omega]
      exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)
    have hint := OddOrder.Algebra.isIntegral_apply_of_mem_ZIrr hZ x
    have hcast : (((hyp.q : ℤ) - 1 : ℤ) : ℂ) =
        ((hyp.q : ℤ) : ℂ) *
          hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hyp.p_prime.one_lt⟩ x := by
      push_cast
      linear_combination hsplit
    have hdvd := OddOrder.RepresentationTheory.int_dvd_of_intCast_eq_mul_isIntegral
      (by exact_mod_cast hyp.q_prime.pos.ne' : (hyp.q : ℤ) ≠ 0) hint hcast
    have hone : (hyp.q : ℤ) ∣ 1 := by
      have h2 : (hyp.q : ℤ) ∣ (hyp.q : ℤ) - ((hyp.q : ℤ) - 1) :=
        dvd_sub dvd_rfl hdvd
      simpa using h2
    have := Int.le_of_dvd one_pos hone
    have := hyp.q_prime.one_lt
    omega

end

section /- (13.9.b): the Galois-integrality estimate -/

open scoped FiniteInduce in
/-- **Peterfalvi (13.9.b), Core form**: the generic-set proportion is bounded by
the two normalized squared-norm sums.  The two nonvanishing loci cover `G₀` by
`G0_nonvanishing_dichotomy_core`; cyclic closure and Isaacs Lemma 3.14 bound each
locus by the corresponding virtual-character norm sum. -/
theorem CharacterDegreeCore.analyticEstimate_galois_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ)
      ≤ normSqSumQ hyp.G0Finset (core.tau1S lam.lambda) / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ) := by
  classical
  obtain ⟨hZlam, -, -⟩ := lambda_tau1_norm_one_core core lam
  have hZeta := hyp.eta10_mem_ZIrr
  set φ : ClassFunction G ℂ := core.tau1S lam.lambda with hφdef
  set A : Finset G := hyp.G0Finset.filter (fun y => φ y ≠ 0) with hA
  set B : Finset G := hyp.G0Finset.filter (fun y => hyp.eta10 y ≠ 0) with hB
  have hdich := core.G0_nonvanishing_dichotomy_core hG lam
  have hcover : hyp.G0Finset ⊆ A ∪ B := by
    intro x hx
    rcases hdich x hx with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hx, by rw [← hφdef] at h; exact h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hcard : hyp.G0Finset.card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  have hgeA : (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
    sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed hZlam
      (filter_ne_zero_cyclicClosed hZlam hyp.G0Finset_cyclicClosed)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  have hgeB : (B.card : ℝ) ≤ ∑ x ∈ B, ‖hyp.eta10 x‖ ^ 2 :=
    sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed hZeta
      (filter_ne_zero_cyclicClosed hZeta hyp.G0Finset_cyclicClosed)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  have hsubA : ∑ x ∈ A, ‖φ x‖ ^ 2 ≤ ∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => by positivity)
  have hsubB : ∑ x ∈ B, ‖hyp.eta10 x‖ ^ 2 ≤
      ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => by positivity)
  have hspecLam := normSqSumQ_spec
    (OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZlam
      hyp.G0Finset_cyclicClosed)
  have hspecEta := normSqSumQ_spec
    (OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZeta
      hyp.G0Finset_cyclicClosed)
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspecLam, hspecEta, ← add_div]
  have hnum : (hyp.G0Finset.card : ℝ) ≤
      (∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2) +
        ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 := by
    have hcard' : (hyp.G0Finset.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
      exact_mod_cast hcard
    linarith [hgeA, hgeB, hsubA, hsubB]
  gcongr

end

section /- (13.10): assembly and arithmetic -/

/-- **Peterfalvi (13.6)–(13.9), Core form**: the four honest estimates consumed by
the arithmetic core of (13.10).  Every character-theoretic input is expressed through
`CharacterDegreeCore` and `LambdaClusterData`; the case-B structure is explicit. -/
theorem CharacterDegreeCore.analyticInequalityEstimates_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    ∃ slam seta g0 HS : ℚ,
      (1 : ℚ) ≥ 1 / (Nat.card G : ℚ) + slam + 1
          - (hyp.u : ℚ) * (hyp.q : ℚ) / ((hyp.c : ℚ) * (hyp.p : ℚ) ^ hyp.q) ∧
        (1 : ℚ) ≥ 1 / (Nat.card G : ℚ) + seta + HS
          + (1 / (hyp.p : ℚ) - 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1))
            + 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1) * (hyp.q : ℚ) ^ hyp.p)) ∧
        (1 : ℚ) = 1 / (Nat.card G : ℚ) + g0 + HS
          + ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p) ∧
        g0 ≤ slam + seta := by
  exact ⟨normSqSumQ hyp.G0Finset (core.tau1S lam.lambda) / (Nat.card G : ℚ),
    normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ),
    (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ),
    ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ),
    core.analyticEstimate_lambda_core hG lam hD hv,
    core.analyticEstimate_eta_core hG hD hv hQcomm pins,
    hyp.analyticCounting_disjointCover_of_caseB_facts hG hD hv,
    core.analyticEstimate_galois_core hG lam⟩

/-- **Peterfalvi (13.10), honest Core endpoint**: explicit case-B facts and the
Core/cluster character data force `u/c > m p^(q-1)/q`.

Unlike the legacy endpoint, this theorem returns the mathematical inequality directly;
it does not manufacture a `NormCascadeData` record whose proof flags carry no content. -/
theorem CharacterDegreeCore.analytic_inequality_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ) := by
  obtain ⟨slam, seta, g0, HS, h1, h2, h3, h139b⟩ :=
    core.analyticInequalityEstimates_core hG lam hD hv hQcomm pins
  have hc0 : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hgi : (0 : ℚ) < 1 / (Nat.card G : ℚ) := by
    have : 0 < Nat.card G := Nat.card_pos
    positivity
  have hpq : ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) =
      (hyp.p : ℚ) ^ (hyp.q - 1) := by
    push_cast
    ring
  rw [hpq]
  exact analytic_inequality_arith hyp.p_prime.two_le hyp.q_prime.two_le hc0
    h1 h2 h3 h139b hgi rfl rfl rfl hyp.m_eq

end

end OddOrder.Peterfalvi.S15
