/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_NormSet
import OddOrder.Peterfalvi.S15_SAndT

/-!
# S16_CoreLemmas

Prefix-split from `OddOrder.Peterfalvi.S16_NonExistenceGCore` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# Peterfalvi Section 16: Non-existence of G

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Section 16, pp. 87--92.

This is the final character-theoretic section of Peterfalvi's proof.  It
continues the `S,T` setup of Section 15, adds the standing inequality `q < p`,
and derives the field-normalizer configuration stated in Peterfalvi (14.2).
Together with Bender--Glauberman Appendix C, that configuration forces
`p <= q`, contradicting the section hypothesis.

The file is a scaffold for (14.1)--(14.16).  The substantial Dade-isometry,
orthogonality, and numerical arguments are exposed as named theorem statements
and proposition fields, so the final integration point with BG Appendix C is
already explicit.
-/

namespace OddOrder.Peterfalvi.S16
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]

/-! ## (14.1)--(14.2): section hypothesis and final target -/

/-- **Peterfalvi (14.1)**: Section 16 continues Hypothesis (13.1) and assumes
`q < p`. -/
structure Hypothesis where
  base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)
  q_lt_p : base.q < base.p

namespace Hypothesis

/-- Under **Peterfalvi (14.1)**, the two prime parameters are distinct. -/
theorem p_ne_q (hyp : Hypothesis (G := G)) : hyp.base.p ≠ hyp.base.q := by
  exact ne_of_gt hyp.q_lt_p

/-- Under **Peterfalvi (14.1)**, the larger prime parameter is at least `5`. -/
theorem five_le_p (hyp : Hypothesis (G := G)) : 5 ≤ hyp.base.p := by
  have hp_gt_three : 3 < hyp.base.p := lt_of_le_of_lt hyp.base.three_le_q hyp.q_lt_p
  have hp_ne_four : hyp.base.p ≠ 4 := by
    intro hp4
    have hodd : Odd 4 := by simpa [hp4] using hyp.base.p_odd
    rcases hodd with ⟨k, hk⟩
    omega
  omega

/-- In the prime field `ZMod p`, the scalar `2` is nonzero because the standing
prime `p` is odd. -/
theorem zmod_two_ne_zero (hyp : Hypothesis (G := G)) :
    (2 : ZMod hyp.base.p) ≠ 0 := by
  intro hzero
  have hp_dvd_two : hyp.base.p ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 hyp.base.p).mp hzero
  rcases (Nat.dvd_prime Nat.prime_two).mp hp_dvd_two with hp_eq_one | hp_eq_two
  · exact hyp.base.p_prime.ne_one hp_eq_one
  · exact hyp.base.p_ne_two hp_eq_two

/-- **Peterfalvi (14.15)**: the inequality `p^(q - 2) < q^2` is
impossible in the Section 16 ordering unless `q = 3`. -/
theorem q_eq_three_of_p_pow_q_sub_two_lt_q_sq
    (hyp : Hypothesis (G := G))
    (hlt : hyp.base.p ^ (hyp.base.q - 2) < hyp.base.q ^ 2) :
    hyp.base.q = 3 := by
  by_contra hq_ne_three
  have hq5 : 5 ≤ hyp.base.q := by
    have hq3le : 3 ≤ hyp.base.q := hyp.base.three_le_q
    have hq_ne_four : hyp.base.q ≠ 4 := by
      intro hq4
      have hodd : Odd 4 := by simpa [hq4] using hyp.base.q_odd
      rcases hodd with ⟨k, hk⟩
      omega
    omega
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hpow3_le : hyp.base.p ^ 3 ≤ hyp.base.p ^ (hyp.base.q - 2) :=
    Nat.pow_le_pow_right hp_pos (by omega : 3 ≤ hyp.base.q - 2)
  have hq2_lt_p3 : hyp.base.q ^ 2 < hyp.base.p ^ 3 := by
    have hq2_lt_p2 : hyp.base.q ^ 2 < hyp.base.p ^ 2 :=
      Nat.pow_lt_pow_left hyp.q_lt_p (by norm_num : 2 ≠ 0)
    have hp2_lt_p3 : hyp.base.p ^ 2 < hyp.base.p ^ 3 := by
      nlinarith [hyp.base.p_prime.one_lt]
    exact lt_trans hq2_lt_p2 hp2_lt_p3
  exact (lt_irrefl (hyp.base.q ^ 2))
    (lt_of_lt_of_le hq2_lt_p3 (le_trans hpow3_le (le_of_lt hlt)))

/-- **Peterfalvi (14.15)**: after the case-(a) inequality forces `q = 3`
and `p < q^2`, the congruence `p ≡ 1 mod q` leaves only `p = 7`. -/
theorem p_eq_seven_of_q_eq_three_modEq_one_and_lt_q_sq
    (hyp : Hypothesis (G := G))
    (hq3 : hyp.base.q = 3) (hmod : hyp.base.p ≡ 1 [MOD hyp.base.q])
    (hp_lt_q_sq : hyp.base.p < hyp.base.q ^ 2) :
    hyp.base.p = 7 := by
  have hp_lt_nine : hyp.base.p < 9 := by
    simpa [hq3] using hp_lt_q_sq
  have hp_ge_five : 5 ≤ hyp.base.p := hyp.five_le_p
  have hmod3 : hyp.base.p % 3 = 1 := by
    unfold Nat.ModEq at hmod
    simpa [hq3] using hmod
  interval_cases hyp.base.p
  · norm_num at hmod3
  · norm_num at hmod3
  · rfl
  · norm_num at hmod3

/-- **Peterfalvi (13.11), used in Section 16**: in the `q = 3` branch, the
Section 16 ordering `q < p` gives the missing `p ≥ 5`, so the concrete analytic
parameter satisfies `m > 49/100`. -/
theorem m_gt_49_hundredths_of_q_eq_three (hyp : Hypothesis (G := G))
    (hq3 : hyp.base.q = 3) :
    hyp.base.m > (49 / 100 : ℚ) := by
  exact hyp.base.m_gt_49_hundredths_of_q_eq_three_of_five_le_p hq3 hyp.five_le_p

/-- The congruence used in **Peterfalvi (14.4)**: from `q < p` and `q` prime,
`q` cannot be `1 mod p`. -/
theorem q_not_modEq_one_mod_p (hyp : Hypothesis (G := G)) :
    ¬ hyp.base.q ≡ 1 [MOD hyp.base.p] := by
  intro hmod
  have hp_gt_one : 1 < hyp.base.p := hyp.base.q_prime.one_lt.trans hyp.q_lt_p
  have hq_eq_one : hyp.base.q = 1 :=
    Nat.ModEq.eq_of_lt_of_lt hmod hyp.q_lt_p hp_gt_one
  exact hyp.base.q_prime.ne_one hq_eq_one

/-- **Peterfalvi (14.15)**: the parity and congruence estimate for the
integer `x` in the non-full branch.  If `x = q + n p`, the fixed-point-free
congruence gives `n ≡ 1 mod q`; since `p` and `q` are odd, oddness of `x`
forces `n` even.  Thus `n` cannot be `0` or `1`, and the congruence then gives
`n ≥ q + 1`, hence `x ≥ q + (1 + q) p`. -/
theorem x_ge_caseA_min_of_decomposition_modEq_and_odd
    (hyp : Hypothesis (G := G)) {x n : ℕ}
    (hx_eq : x = hyp.base.q + n * hyp.base.p)
    (hn_mod : n ≡ 1 [MOD hyp.base.q]) (hx_odd : Odd x) :
    hyp.base.q + (1 + hyp.base.q) * hyp.base.p ≤ x := by
  have hn_even : Even n := by
    by_contra hn_not_even
    have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_not_even
    have hnp_odd : Odd (n * hyp.base.p) := hn_odd.mul hyp.base.p_odd
    have hx_even : Even x := by
      rw [hx_eq]
      exact hyp.base.q_odd.add_odd hnp_odd
    exact (Nat.not_even_iff_odd.mpr hx_odd) hx_even
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have hmod0 : 0 ≡ 1 [MOD hyp.base.q] := by
      simpa [hn0] using hn_mod
    have hzero_eq_one : 0 = 1 :=
      Nat.ModEq.eq_of_lt_of_lt hmod0 hyp.base.q_prime.pos hyp.base.q_prime.one_lt
    omega
  have hn_ne_one : n ≠ 1 := by
    intro hn1
    rw [hn1] at hn_even
    norm_num at hn_even
  have hn_gt_one : 1 < n := by omega
  have hn_ge : 1 + hyp.base.q ≤ n := hn_mod.symm.add_le_of_lt hn_gt_one
  rw [hx_eq]
  nlinarith [Nat.mul_le_mul_right hyp.base.p hn_ge]

/-- **Peterfalvi (14.16)**: the parity estimate for the quotient `x = h / u`.
If `x ≡ 1` modulo both `p` and `q`, then CRT gives `x ≡ 1 mod p q`;
oddness and `x ≠ 1` force the first nontrivial possibility to be beyond
`2 p q`. -/
theorem quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
    (hyp : Hypothesis (G := G)) {x : ℕ}
    (hx_mod_p : x ≡ 1 [MOD hyp.base.p])
    (hx_mod_q : x ≡ 1 [MOD hyp.base.q])
    (hx_odd : Odd x) (hx_ne_one : x ≠ 1) :
    2 * (hyp.base.p * hyp.base.q) < x := by
  have hpq_coprime : Nat.Coprime hyp.base.p hyp.base.q :=
    (Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q
  have hx_mod_pq : x ≡ 1 [MOD hyp.base.p * hyp.base.q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hpq_coprime).mp ⟨hx_mod_p, hx_mod_q⟩
  have hx_ge_one : 1 ≤ x := by
    rcases hx_odd with ⟨k, hk⟩
    omega
  rcases (Nat.modEq_iff_exists_eq_add hx_ge_one).mp hx_mod_pq.symm with ⟨n, hx_eq⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    rw [hn0, mul_zero, add_zero] at hx_eq
    exact hx_ne_one hx_eq
  have hpq_odd : Odd (hyp.base.p * hyp.base.q) :=
    hyp.base.p_odd.mul hyp.base.q_odd
  have hn_even : Even n := by
    by_contra hn_not_even
    have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_not_even
    have hpqn_odd : Odd ((hyp.base.p * hyp.base.q) * n) :=
      hpq_odd.mul hn_odd
    have hx_even : Even x := by
      rw [hx_eq]
      exact (by norm_num : Odd 1).add_odd hpqn_odd
    exact (Nat.not_even_iff_odd.mpr hx_odd) hx_even
  have hn_ge_two : 2 ≤ n := by
    rcases hn_even with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      by_contra hk_not_pos
      have hk0 : k = 0 := by omega
      subst k
      omega
    omega
  rw [hx_eq]
  nlinarith [Nat.mul_le_mul_left (hyp.base.p * hyp.base.q) hn_ge_two]

/-- The T-side cyclotomic quotient from **Peterfalvi (14.4)** is odd. -/
theorem tSide_cyclotomic_quotient_odd (hyp : Hypothesis (G := G)) :
    Odd ((hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)) :=
  OddOrder.Peterfalvi.S15.cyclotomic_quotient_odd
    hyp.base.q_prime hyp.base.q_odd hyp.base.p_odd

/-- The T-side cyclotomic quotient from **Peterfalvi (14.4)** is coprime to
`q - 1`. -/
theorem tSide_cyclotomic_quotient_coprime (hyp : Hypothesis (G := G)) :
    Nat.Coprime ((hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
      (hyp.base.q - 1) :=
  OddOrder.Peterfalvi.S15.cyclotomic_quotient_coprime_of_not_modEq_one
    hyp.base.q_prime hyp.base.p_prime hyp.q_not_modEq_one_mod_p

/-- Every positive divisor of the T-side cyclotomic quotient from
**Peterfalvi (14.4)** is `1 mod p`. -/
theorem tSide_cyclotomic_quotient_divisor_modEq_one (hyp : Hypothesis (G := G)) :
    ∀ x : ℕ, x ≠ 0 →
      x ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) →
        x ≡ 1 [MOD hyp.base.p] :=
  OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one
    hyp.base.q_prime hyp.base.p_prime hyp.q_not_modEq_one_mod_p

end Hypothesis

-- de-privated for the hub prefix-split (2026-06-15): referenced from the tail file
-- `S16_NonExistenceG.lean` (Peterfalvi (14.x) numerics); see CLAUDE.md「private をファイル跨ぎで使わない」.
theorem p_pow_sub_two_lt_q_sq_of_pow_lt_mul_sq {p q : ℕ}
    (hq2 : 2 ≤ q) (hlt : p ^ q < (p * q) ^ 2) :
    p ^ (q - 2) < q ^ 2 := by
  have hpow_eq : p ^ q = p ^ (q - 2) * p ^ 2 := by
    calc
      p ^ q = p ^ ((q - 2) + 2) := by rw [show (q - 2) + 2 = q by omega]
      _ = p ^ (q - 2) * p ^ 2 := by rw [pow_add]
  have hmul_eq : (p * q) ^ 2 = p ^ 2 * q ^ 2 := by ring
  rw [hpow_eq, hmul_eq] at hlt
  rw [mul_comm (p ^ (q - 2)) (p ^ 2)] at hlt
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- The concrete norm relation produced by the generator-relation argument in
**BG Appendix C, Lemma C.3**, expressed at the Peterfalvi Section 16 interface.
For every `a` in the norm set `E`, the relation should give `N(2 * a - 1) = 1`;
BG then converts this finite-field statement into `a⁻¹ ∈ E`. -/
def appCNormSetGeneratorRelation (hyp : Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  ∀ a : GaloisField hyp.base.p hyp.base.q,
    a ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q →
      OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q
        ((2 : GaloisField hyp.base.p hyp.base.q) * a - 1) = 1

/-- The field-element one-step twisted-inverse output of
**BG Appendix C, Lemma C.3, Step 4**, expressed at the Peterfalvi Section 16
interface.  This is closest to the line in BG proving `(a⁻¹)^{t^3} ∈ E` for
`a ∈ E`; the unit-group formulation used for the final odd iteration is derived
from this. -/
def appCNormSetTwistedFieldStep (hyp : Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  ∃ φ : MulAut (GaloisField hyp.base.p hyp.base.q)ˣ,
    φ ^ hyp.base.p = 1 ∧
      OddOrder.BG.AppC.NormSet.normSetETwistedFieldStep
        (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.pos φ

/-- The one-step twisted-inverse output of **BG Appendix C, Lemma C.3, Step 4**,
expressed at the Peterfalvi Section 16 interface.  This is closer to the group
calculation in BG: for a field automorphism of `p`-power order, every
`u ∈ E` is sent to `φ(u⁻¹) ∈ E`. -/
def appCNormSetTwistedUnitStep (hyp : Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  ∃ φ : MulAut (GaloisField hyp.base.p hyp.base.q)ˣ,
    φ ^ hyp.base.p = 1 ∧
      ∀ u : (GaloisField hyp.base.p hyp.base.q)ˣ,
        ((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) ∈
          OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q →
          ((OddOrder.BG.AppC.NormSet.twistedInv φ u :
              (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) ∈
            OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q

/-- The same one-step output, narrowed to the concrete norm-one unit group `U`.
This matches the actual BG Step 4 action by conjugation with `t`; no extension to
all of `𝔽_{p^q}ˣ` is required. -/
def appCNormSetTwistedNormOneStep (hyp : Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  ∃ φ : MulAut (OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q),
    φ ^ hyp.base.p = 1 ∧
      OddOrder.BG.AppC.NormSet.normSetETwistedNormOneStep
        (p := hyp.base.p) (q := hyp.base.q) φ

/-- The field-element Step 4 output implies the unit-group Step 4 output used by
BG's final odd-iterate argument. -/
theorem appCNormSetTwistedUnitStep_of_field_step
    (hyp : Hypothesis (G := G)) :
    appCNormSetTwistedFieldStep hyp → appCNormSetTwistedUnitStep hyp := by
  intro htwist
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rcases htwist with ⟨φ, hφp, hstep⟩
  exact ⟨φ, hφp,
    OddOrder.BG.AppC.NormSet.twisted_unit_step_of_twisted_field_step
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.pos φ hstep⟩

/-- The BG Step 4 twisted-inverse output implies the norm relation currently
consumed by `FieldNormalizerData`.  This keeps the S16 producer obligation close
to the group-theoretic calculation while preserving the downstream AppC
interface. -/
theorem appCNormSetGeneratorRelation_of_twisted_unit_step
    (hyp : Hypothesis (G := G)) :
    appCNormSetTwistedUnitStep hyp → appCNormSetGeneratorRelation hyp := by
  intro htwist
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rcases htwist with ⟨φ, hφp, hstep⟩
  exact OddOrder.BG.AppC.NormSet.forall_normN_two_mul_sub_one_of_twisted_unit_step
    (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.pos hyp.base.p_odd φ hφp hstep

/-- The norm-one Step 4 output implies the norm relation consumed by AppC. -/
theorem appCNormSetGeneratorRelation_of_twisted_normOne_step
    (hyp : Hypothesis (G := G)) :
    appCNormSetTwistedNormOneStep hyp → appCNormSetGeneratorRelation hyp := by
  intro htwist
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rcases htwist with ⟨φ, hφp, hstep⟩
  exact OddOrder.BG.AppC.NormSet.forall_normN_two_mul_sub_one_of_twisted_normOne_step
    (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.pos hyp.base.p_odd φ hφp hstep

/-- The concrete Frobenius group `H = P \rtimes U` from BG Appendix C,
with Peterfalvi Section 16 parameters. -/
abbrev fieldNormalizerFrobeniusGroup (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup hyp.base.p hyp.base.q

/-- The additive kernel `P ≤ H` in the concrete BG Frobenius group. -/
noncomputable def fieldNormalizerKernel (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp).range

/-- The prime-field additive line `P₀ ≤ P` inside the concrete BG Frobenius
group, generated by `1 : F_{p^q}`. -/
noncomputable def fieldNormalizerPrimeLine (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneFrobeniusSubspaceKernel hyp.base.p hyp.base.q
    (Submodule.span (ZMod hyp.base.p)
      ({(1 : GaloisField hyp.base.p hyp.base.q)} :
        Set (GaloisField hyp.base.p hyp.base.q)))

/-- The norm-one complement `U ≤ H` inside the concrete BG Frobenius group. -/
noncomputable def fieldNormalizerComplement (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  (SemidirectProduct.inr :
      OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp).range

/-- In the concrete BG Frobenius group `P ⋊ U`, the additive kernel and the
norm-one complement meet trivially. -/
theorem fieldNormalizerKernel_inf_complement_eq_bot (hyp : Hypothesis (G := G)) :
    fieldNormalizerKernel hyp ⊓ fieldNormalizerComplement hyp = ⊥ := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  apply le_antisymm ?_ bot_le
  intro x hx
  rcases hx.1 with ⟨p, rfl⟩
  rcases hx.2 with ⟨u, hu⟩
  have hp : p = 1 := by
    have hleft := congrArg
      (fun g : fieldNormalizerFrobeniusGroup hyp => g.left) hu
    simpa using hleft.symm
  subst p
  simp

/-- In the concrete BG Frobenius group `P ⋊ U`, the additive kernel and
norm-one complement generate the whole group. -/
theorem fieldNormalizerKernel_sup_complement_eq_top (hyp : Hypothesis (G := G)) :
    fieldNormalizerKernel hyp ⊔ fieldNormalizerComplement hyp = ⊤ := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  apply le_antisymm le_top
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact Subgroup.mul_mem_sup ⟨g.left, rfl⟩ ⟨g.right, rfl⟩

/-- The concrete norm-one unit group used as the BG complement before transport
through the field-normalizer embedding. -/
abbrev fieldNormalizerNormOneUnits (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q

/-- The concrete norm-one complement has more than one element.  This is the
lightweight cardinality input needed to turn BG Appendix C, Lemma C.3 Step 2
into the assertion that the prime line `P₀` cannot normalize `U`, without
importing the class-sum file. -/
theorem fieldNormalizerNormOneUnits_card_gt_one (hyp : Hypothesis (G := G)) :
    1 < Nat.card (fieldNormalizerNormOneUnits hyp) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
  have hq0 : hyp.base.q ≠ 0 := hyp.base.q_prime.ne_zero
  have hq2 : 2 ≤ hyp.base.q := by
    have hq3 : 3 ≤ hyp.base.q := hyp.base.three_le_q
    omega
  rw [OddOrder.BG.AppC.NormSet.normOneUnits_card hyp.base.p hyp.base.q hq0,
    ← Nat.geomSum_eq hp2 hyp.base.q]
  have hrange : Finset.range 2 ⊆ Finset.range hyp.base.q := by
    intro k hk
    exact Finset.mem_range.mpr (by
      have hk2 : k < 2 := Finset.mem_range.mp hk
      exact Nat.lt_of_lt_of_le hk2 hq2)
  have hle :
      (∑ k ∈ Finset.range 2, hyp.base.p ^ k) ≤
        ∑ k ∈ Finset.range hyp.base.q, hyp.base.p ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange
      (fun _ _ _ => Nat.zero_le _)
  have htwo : 1 < (∑ k ∈ Finset.range 2, hyp.base.p ^ k) := by
    simp
    omega
  exact htwo.trans_le hle

/-- There is a nonidentity norm-one unit in the concrete complement. -/
theorem exists_fieldNormalizerNormOneUnit_ne_one (hyp : Hypothesis (G := G)) :
    ∃ u : fieldNormalizerNormOneUnits hyp, u ≠ 1 := by
  haveI : Nontrivial (fieldNormalizerNormOneUnits hyp) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (fieldNormalizerNormOneUnits_card_gt_one hyp)
  exact exists_ne 1

/-- The distinguished nonidentity element of the prime-field line `P₀`,
corresponding to `1 : F_{p^q}` in BG Appendix C. -/
noncomputable def fieldNormalizerPrimeLineGenerator (hyp : Hypothesis (G := G)) :
    fieldNormalizerFrobeniusGroup hyp :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  SemidirectProduct.inl
    (Multiplicative.ofAdd (1 : GaloisField hyp.base.p hyp.base.q))

/-- The element of the concrete prime-field line corresponding to a scalar
`c : ZMod p`. -/
noncomputable def fieldNormalizerPrimeLineElement (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) : fieldNormalizerFrobeniusGroup hyp :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  SemidirectProduct.inl
    (Multiplicative.ofAdd
      (algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c))

/-- Prime-line scalar elements lie in the concrete subgroup `P₀`. -/
theorem fieldNormalizerPrimeLineElement_mem (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) :
    fieldNormalizerPrimeLineElement hyp c ∈ fieldNormalizerPrimeLine hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [fieldNormalizerPrimeLineElement, fieldNormalizerPrimeLine]
  rw [OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl]
  have h1 : (1 : GaloisField hyp.base.p hyp.base.q) ∈
      Submodule.span (ZMod hyp.base.p)
        ({(1 : GaloisField hyp.base.p hyp.base.q)} :
          Set (GaloisField hyp.base.p hyp.base.q)) :=
    Submodule.subset_span (by simp)
  simpa [Algebra.smul_def] using
    (Submodule.smul_mem
      (Submodule.span (ZMod hyp.base.p)
        ({(1 : GaloisField hyp.base.p hyp.base.q)} :
          Set (GaloisField hyp.base.p hyp.base.q))) c h1)

/-- The scalar `1` element is the distinguished prime-line generator. -/
theorem fieldNormalizerPrimeLineElement_one (hyp : Hypothesis (G := G)) :
    fieldNormalizerPrimeLineElement hyp 1 = fieldNormalizerPrimeLineGenerator hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerPrimeLineElement, fieldNormalizerPrimeLineGenerator]

/-- Prime-line scalar elements invert by negating the scalar. -/
theorem fieldNormalizerPrimeLineElement_neg (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) :
    fieldNormalizerPrimeLineElement hyp (-c) =
      (fieldNormalizerPrimeLineElement hyp c)⁻¹ := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerPrimeLineElement]

/-- The distinguished generator lies in the concrete prime-field line `P₀`. -/
theorem fieldNormalizerPrimeLineGenerator_mem (hyp : Hypothesis (G := G)) :
    fieldNormalizerPrimeLineGenerator hyp ∈ fieldNormalizerPrimeLine hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [fieldNormalizerPrimeLineGenerator, fieldNormalizerPrimeLine]
  rw [OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl]
  exact Submodule.subset_span (by simp)

/-- The distinguished generator of `P₀` is nontrivial. -/
theorem fieldNormalizerPrimeLineGenerator_ne_one (hyp : Hypothesis (G := G)) :
    fieldNormalizerPrimeLineGenerator hyp ≠ 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro h
  have hfield : (1 : GaloisField hyp.base.p hyp.base.q) = 0 :=
    ofAdd_eq_one.mp (SemidirectProduct.inl_inj.mp h)
  exact one_ne_zero hfield

/-- The distinguished generator of `P₀` has order dividing `p`. -/
theorem fieldNormalizerPrimeLineGenerator_pow_p (hyp : Hypothesis (G := G)) :
    (fieldNormalizerPrimeLineGenerator hyp) ^ hyp.base.p = 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  haveI : CharP (GaloisField hyp.base.p hyp.base.q) hyp.base.p := by
    rw [← Algebra.charP_iff (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q)
      hyp.base.p]
    exact ZMod.charP hyp.base.p
  dsimp [fieldNormalizerPrimeLineGenerator]
  let inlHom :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inl
  rw [← map_pow inlHom, ← map_one inlHom, SemidirectProduct.inl_inj]
  rw [← ofAdd_nsmul]
  congr
  simp

/-- The additive kernel of the concrete BG Frobenius group, with the local
`Fact p.Prime` bundled into the abbreviation. -/
abbrev fieldNormalizerAdditiveGroup (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q

/-- The concrete `p`-power Frobenius on the additive kernel of BG's model
`P ⋊ U`, written multiplicatively via `Multiplicative`. -/
noncomputable def fieldNormalizerAdditiveFrobeniusHom (hyp : Hypothesis (G := G)) :
    fieldNormalizerAdditiveGroup hyp →* fieldNormalizerAdditiveGroup hyp where
  toFun x := Multiplicative.ofAdd (x.toAdd ^ hyp.base.p)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp [hyp.base.p_prime.ne_zero]
  map_mul' x y := by
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    apply Multiplicative.toAdd.injective
    exact (OddOrder.BG.AppC.NormSet.add_pow_p
      hyp.base.p hyp.base.q x.toAdd y.toAdd).symm

/-- The concrete `p`-power Frobenius on the norm-one complement. -/
noncomputable def fieldNormalizerNormOneFrobeniusHom (hyp : Hypothesis (G := G)) :
    fieldNormalizerNormOneUnits hyp →* fieldNormalizerNormOneUnits hyp where
  toFun u := u ^ hyp.base.p
  map_one' := by simp
  map_mul' u v := by
    rw [mul_pow]

/-- The concrete `p`-power Frobenius of BG's semidirect product
`P ⋊ U`: it sends `(x,u)` to `(x^p,u^p)`. -/
noncomputable def fieldNormalizerFrobeniusHom (hyp : Hypothesis (G := G)) :
    fieldNormalizerFrobeniusGroup hyp →* fieldNormalizerFrobeniusGroup hyp :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  SemidirectProduct.map
    (fieldNormalizerAdditiveFrobeniusHom (G := G) hyp)
    (fieldNormalizerNormOneFrobeniusHom (G := G) hyp)
    (by
      intro u
      ext x
      apply Multiplicative.toAdd.injective
      change (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) * x) ^ hyp.base.p =
            (((u ^ hyp.base.p : fieldNormalizerNormOneUnits hyp) :
                  (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * x ^ hyp.base.p
      simpa [map_pow] using
        (mul_pow (((u : (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q)) x hyp.base.p))

@[simp]
theorem fieldNormalizerFrobeniusHom_inl (hyp : Hypothesis (G := G))
    (x : fieldNormalizerAdditiveGroup hyp) :
    fieldNormalizerFrobeniusHom hyp (SemidirectProduct.inl x) =
      SemidirectProduct.inl (Multiplicative.ofAdd (x.toAdd ^ hyp.base.p)) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerFrobeniusHom, fieldNormalizerAdditiveFrobeniusHom]

@[simp]
theorem fieldNormalizerFrobeniusHom_inr (hyp : Hypothesis (G := G))
    (u : fieldNormalizerNormOneUnits hyp) :
    fieldNormalizerFrobeniusHom hyp
        (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) =
      SemidirectProduct.inr (u ^ hyp.base.p) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerFrobeniusHom, fieldNormalizerNormOneFrobeniusHom]

/-- The concrete Frobenius fixes the prime-field line pointwise. -/
theorem fieldNormalizerFrobeniusHom_primeLineElement (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) :
    fieldNormalizerFrobeniusHom hyp (fieldNormalizerPrimeLineElement hyp c) =
      fieldNormalizerPrimeLineElement hyp c := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rw [fieldNormalizerPrimeLineElement, fieldNormalizerFrobeniusHom_inl,
    SemidirectProduct.inl_inj]
  change (algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c) ^
      hyp.base.p = algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c
  rw [← map_pow, ZMod.pow_card]

/-- The concrete Frobenius fixes the distinguished prime-line generator. -/
theorem fieldNormalizerFrobeniusHom_primeLineGenerator (hyp : Hypothesis (G := G)) :
    fieldNormalizerFrobeniusHom hyp (fieldNormalizerPrimeLineGenerator hyp) =
      fieldNormalizerPrimeLineGenerator hyp := by
  simpa [fieldNormalizerPrimeLineElement_one] using
    fieldNormalizerFrobeniusHom_primeLineElement (G := G) hyp 1

/-- The concrete Frobenius fixes every integer power of the distinguished
prime-line generator. -/
theorem fieldNormalizerFrobeniusHom_primeLineGenerator_zpow
    (hyp : Hypothesis (G := G)) (n : ℤ) :
    fieldNormalizerFrobeniusHom hyp ((fieldNormalizerPrimeLineGenerator hyp) ^ n) =
      (fieldNormalizerPrimeLineGenerator hyp) ^ n := by
  rw [map_zpow, fieldNormalizerFrobeniusHom_primeLineGenerator]

/-- The two conclusions of **Peterfalvi (14.2)**, packaged in the form consumed
by BG Appendix C.  The finite-field model is now carried as a concrete
monomorphism from BG's Frobenius group `H = P \rtimes U` into `G`, together with
its image identifications. -/
structure FieldNormalizerData (hyp : Hypothesis (G := G)) where
  sigma : fieldNormalizerFrobeniusGroup hyp →* G
  sigma_injective : Function.Injective sigma
  sigma_P_eq_P : (fieldNormalizerKernel hyp).map sigma = hyp.base.P
  sigma_P0_eq_W2 : (fieldNormalizerPrimeLine hyp).map sigma = hyp.base.W2
  sigma_U_eq_U : (fieldNormalizerComplement hyp).map sigma = hyp.base.U
  cyclotomic_coprime :
    Nat.Coprime
      ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
      (hyp.base.p - 1)
  Q_elementaryAbelian : IsElementaryAbelian hyp.base.q ↥hyp.base.Q
  W2_normalizes_Q : hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.Q : Set G)
  y : G
  y_mem_Q : y ∈ hyp.base.Q
  W2_conj_y_normalizes_U :
    MulAut.conj y • hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G)

namespace FieldNormalizerData

/-- The BG element `s ∈ P₀#`, transported to `G` through the concrete
field-normalizer monomorphism. -/
noncomputable def s {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) : G :=
  data.sigma (fieldNormalizerPrimeLineGenerator hyp)

/-- The transported element `s` lies in Peterfalvi's subgroup `W₂ = σ(P₀)`. -/
theorem s_mem_W2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ∈ hyp.base.W2 := by
  rw [← data.sigma_P0_eq_W2]
  exact ⟨fieldNormalizerPrimeLineGenerator hyp,
    fieldNormalizerPrimeLineGenerator_mem hyp, rfl⟩

/-- The transported element `s` lies in the transported additive kernel `P`. -/
theorem s_mem_P {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ∈ hyp.base.P := by
  rw [← data.sigma_P_eq_P]
  refine ⟨fieldNormalizerPrimeLineGenerator hyp, ?_, rfl⟩
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [fieldNormalizerPrimeLineGenerator, fieldNormalizerKernel]
  exact ⟨Multiplicative.ofAdd (1 : GaloisField hyp.base.p hyp.base.q), rfl⟩

/-- Integer powers of `s` remain in `P`. -/
theorem s_zpow_mem_P {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (n : ℤ) :
    data.s ^ n ∈ hyp.base.P :=
  hyp.base.P.zpow_mem data.s_mem_P n

/-- Integer powers of `s` lie in `PU`. -/
theorem s_zpow_mem_P_sup_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℤ) :
    data.s ^ n ∈ hyp.base.P ⊔ hyp.base.U :=
  (le_sup_left : hyp.base.P ≤ hyp.base.P ⊔ hyp.base.U) (data.s_zpow_mem_P n)

/-- Integer powers of the transported generator `s` are exactly the corresponding
points of the concrete prime-field line. -/
theorem s_zpow_eq_primeLineElement {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℤ) :
    data.s ^ n =
      data.sigma (fieldNormalizerPrimeLineElement hyp (n : ZMod hyp.base.p)) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  calc
    data.s ^ n = data.sigma ((fieldNormalizerPrimeLineGenerator hyp) ^ n) := by
      rw [s, map_zpow]
    _ = data.sigma (fieldNormalizerPrimeLineElement hyp (n : ZMod hyp.base.p)) := by
      congr 1
      dsimp [fieldNormalizerPrimeLineElement, fieldNormalizerPrimeLineGenerator]
      rw [← map_zpow (SemidirectProduct.inl :
        OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
          fieldNormalizerFrobeniusGroup hyp)]
      rw [SemidirectProduct.inl_inj]
      rw [← ofAdd_zsmul]
      congr 1
      simp [zsmul_eq_mul]

/-- The `s^{-2}` factor in BG C.3 Step 4 is the `-2` point of the concrete
prime-field line after transport by `σ`. -/
theorem s_zpow_neg_two_eq_primeLineElement_neg_two
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ^ (-2 : ℤ) =
      data.sigma (fieldNormalizerPrimeLineElement hyp (-2 : ZMod hyp.base.p)) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [s, fieldNormalizerPrimeLineElement, fieldNormalizerPrimeLineGenerator]
  let F := GaloisField hyp.base.p hyp.base.q
  let H := fieldNormalizerFrobeniusGroup hyp
  have hpow_two :
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) ^ 2 =
        SemidirectProduct.inl (Multiplicative.ofAdd (2 : F)) := by
    rw [pow_two, ← map_mul (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →* H)]
    congr
    apply Multiplicative.toAdd.injective
    change (1 : F) + 1 = 2
    ring
  have hneg_two :
      (algebraMap (ZMod hyp.base.p) F (-2 : ZMod hyp.base.p)) = -(2 : F) := by
    simp only [map_neg, map_ofNat]
  rw [← map_zpow]
  congr
  rw [zpow_neg, hneg_two]
  change ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) ^ 2)⁻¹ =
    SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))
  have hpow_two_inv := congrArg Inv.inv hpow_two
  exact hpow_two_inv.trans (by simp [F])

/-- The transported element `s` is nontrivial. -/
theorem s_ne_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ≠ 1 := by
  intro hs
  exact fieldNormalizerPrimeLineGenerator_ne_one hyp
    (data.sigma_injective (by simpa [s] using hs))

/-- The transported prime-line generator has `p`-th power equal to `1`. -/
theorem s_pow_p_eq_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ^ hyp.base.p = 1 := by
  simpa [s] using congrArg data.sigma (fieldNormalizerPrimeLineGenerator_pow_p hyp)

/-- The transported generator `s` has exact order `p`. -/
theorem s_orderOf_eq_p {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    orderOf data.s = hyp.base.p := by
  have hdiv : orderOf data.s ∣ hyp.base.p :=
    orderOf_dvd_of_pow_eq_one data.s_pow_p_eq_one
  rcases hyp.base.p_prime.eq_one_or_self_of_dvd (orderOf data.s) hdiv with h | h
  · exact False.elim (data.s_ne_one (orderOf_eq_one_iff.mp h))
  · exact h

/-- The transported prime line `W₂ = σ(P₀)` is generated by the distinguished
nonidentity element `s`.  This is the `P₀ = ⟨s⟩` input in BG Appendix C. -/
theorem W2_eq_zpowers_s {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.W2 = Subgroup.zpowers data.s := by
  have hsle : Subgroup.zpowers data.s ≤ hyp.base.W2 :=
    Subgroup.zpowers_le.mpr data.s_mem_W2
  haveI : Finite hyp.base.W2 := Nat.finite_of_card_ne_zero (by
    rw [← hyp.base.p_eq_card_W2]
    exact hyp.base.p_prime.ne_zero)
  have hcard : Nat.card ↥hyp.base.W2 ≤ Nat.card ↥(Subgroup.zpowers data.s) := by
    rw [Nat.card_zpowers, data.s_orderOf_eq_p, hyp.base.p_eq_card_W2]
  exact (Subgroup.eq_of_le_of_card_ge hsle hcard).symm

/-- The transported prime line `W₂ = σ(P₀)` lies in Peterfalvi's additive kernel
`P`. -/
theorem W2_le_P {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.W2 ≤ hyp.base.P := by
  rw [data.W2_eq_zpowers_s]
  exact Subgroup.zpowers_le.mpr data.s_mem_P

/-- The transported prime line `W₂ = σ(P₀)` is a `p`-group of order `p`. -/
theorem W2_isPGroup {hyp : Hypothesis (G := G)} (_data : FieldNormalizerData hyp) :
    IsPGroup hyp.base.p hyp.base.W2 := by
  haveI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  haveI : Finite hyp.base.W2 := Nat.finite_of_card_ne_zero (by
    rw [← hyp.base.p_eq_card_W2]
    exact hyp.base.p_prime.ne_zero)
  rw [IsPGroup.iff_card]
  exact ⟨1, by rw [pow_one, hyp.base.p_eq_card_W2]⟩

/-- The transported prime-line generator normalizes `Q`. -/
theorem s_normalizes_Q {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ∈ Subgroup.normalizer (hyp.base.Q : Set G) :=
  data.W2_normalizes_Q data.s_mem_W2

/-- The concrete norm-one complement transported through `σ` onto Peterfalvi's
subgroup `U`. -/
noncomputable def normOneUnitsToU {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : fieldNormalizerNormOneUnits hyp →* hyp.base.U :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  { toFun := fun u =>
      ⟨data.sigma (SemidirectProduct.inr u), by
        rw [← data.sigma_U_eq_U]
        exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩⟩
    map_one' := by
      ext
      simp
    map_mul' := by
      intro u v
      ext
      simp }

/-- The transported norm-one complement map is injective. -/
theorem normOneUnitsToU_injective {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : Function.Injective data.normOneUnitsToU := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro u v h
  have hsig : data.sigma (SemidirectProduct.inr u) = data.sigma (SemidirectProduct.inr v) :=
    congrArg Subtype.val h
  exact SemidirectProduct.inr_injective (data.sigma_injective hsig)

/-- The transported norm-one complement map is onto Peterfalvi's `U`. -/
theorem normOneUnitsToU_surjective {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : Function.Surjective data.normOneUnitsToU := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro u
  have hu : (u : G) ∈ (fieldNormalizerComplement hyp).map data.sigma := by
    rw [data.sigma_U_eq_U]
    exact u.property
  rcases hu with ⟨x, hxU, hx⟩
  rcases hxU with ⟨u0, rfl⟩
  refine ⟨u0, ?_⟩
  ext
  exact hx

/-- The concrete norm-one unit group is isomorphic to Peterfalvi's subgroup `U`
through the field-normalizer embedding. -/
noncomputable def normOneUnitsEquivU {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : fieldNormalizerNormOneUnits hyp ≃* hyp.base.U :=
  MulEquiv.ofBijective data.normOneUnitsToU
    ⟨data.normOneUnitsToU_injective, data.normOneUnitsToU_surjective⟩

/-- The transported additive kernel `P` and complement `U` meet trivially in
`G`.  This is the S16-facing form of the `U ∩ P = 1` input used when BG
Appendix C, Lemma C.3 Step 4 reads equations modulo `P`. -/
theorem P_inf_U_eq_bot {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.P ⊓ hyp.base.U = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxP : x ∈ (fieldNormalizerKernel hyp).map data.sigma := by
    rw [data.sigma_P_eq_P]
    exact hx.1
  have hxU : x ∈ (fieldNormalizerComplement hyp).map data.sigma := by
    rw [data.sigma_U_eq_U]
    exact hx.2
  rcases hxP with ⟨p, hpP, hp⟩
  rcases hxU with ⟨u, huU, hu⟩
  have hpu : p = u := data.sigma_injective (by
    rw [hp, hu])
  have hp_inter : p ∈ fieldNormalizerKernel hyp ⊓ fieldNormalizerComplement hyp := by
    exact ⟨hpP, by rwa [hpu]⟩
  have hp_one : p = 1 := by
    have hp_bot : p ∈ (⊥ : Subgroup (fieldNormalizerFrobeniusGroup hyp)) := by
      rw [← fieldNormalizerKernel_inf_complement_eq_bot hyp]
      exact hp_inter
    simpa [Subgroup.mem_bot] using hp_bot
  rw [Subgroup.mem_bot]
  rw [← hp, hp_one, map_one]

/-- The image of the concrete Frobenius group is the subgroup generated by the
transported additive kernel `P` and complement `U`. -/
theorem P_sup_U_eq_sigma_top {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.P ⊔ hyp.base.U =
      (⊤ : Subgroup (fieldNormalizerFrobeniusGroup hyp)).map data.sigma := by
  calc
    hyp.base.P ⊔ hyp.base.U =
        (fieldNormalizerKernel hyp).map data.sigma ⊔
          (fieldNormalizerComplement hyp).map data.sigma := by
      rw [data.sigma_P_eq_P, data.sigma_U_eq_U]
    _ = (fieldNormalizerKernel hyp ⊔ fieldNormalizerComplement hyp).map data.sigma := by
      rw [Subgroup.map_sup]
    _ = (⊤ : Subgroup (fieldNormalizerFrobeniusGroup hyp)).map data.sigma := by
      rw [fieldNormalizerKernel_sup_complement_eq_top hyp]


/-- The norm-one complement has order prime to `p`.  In BG Appendix C terms,
`|U| = 1 + p + ... + p^{q-1}`, so the `U`-coordinate of any `p`-element in
`P ⋊ U` must be trivial. -/
theorem fieldNormalizerNormOneUnits_card_coprime_p (hyp : Hypothesis (G := G)) :
    Nat.Coprime hyp.base.p (Nat.card (fieldNormalizerNormOneUnits hyp)) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
  have hq0 : hyp.base.q ≠ 0 := hyp.base.q_prime.ne_zero
  rw [OddOrder.BG.AppC.NormSet.normOneUnits_card hyp.base.p hyp.base.q hq0,
    ← Nat.geomSum_eq hp2 hyp.base.q]
  have hq_pos : 0 < hyp.base.q := hyp.base.q_prime.pos
  have hsum :
      (∑ k ∈ Finset.range hyp.base.q, hyp.base.p ^ k) =
        (∑ k ∈ Finset.range (hyp.base.q - 1), hyp.base.p ^ (k + 1)) + 1 := by
    rw [show hyp.base.q = (hyp.base.q - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    simp
  rw [hsum, add_comm]
  have hdiv :
      hyp.base.p ∣
        ∑ k ∈ Finset.range (hyp.base.q - 1), hyp.base.p ^ (k + 1) := by
    exact Finset.dvd_sum fun k _ => dvd_pow_self hyp.base.p (Nat.succ_ne_zero k)
  rw [Nat.coprime_add_iff_left hdiv]
  exact Nat.coprime_one_right hyp.base.p

/-- Every element of the concrete additive kernel `P ≤ P⋊U` has `p`-th power
`1`. -/
theorem fieldNormalizerKernel_pow_p_eq_one {hyp : Hypothesis (G := G)}
    {x : fieldNormalizerFrobeniusGroup hyp} (hx : x ∈ fieldNormalizerKernel hyp) :
    x ^ hyp.base.p = 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  haveI : CharP (GaloisField hyp.base.p hyp.base.q) hyp.base.p := by
    rw [← Algebra.charP_iff (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q)
      hyp.base.p]
    exact ZMod.charP hyp.base.p
  rcases hx with ⟨a, rfl⟩
  let inlHom :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inl
  rw [← map_pow inlHom, ← map_one inlHom, SemidirectProduct.inl_inj]
  rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
  congr
  simp

/-- In the concrete Frobenius group `P⋊U`, a `p`-element has trivial
`U`-coordinate. -/
theorem fieldNormalizerFrobeniusGroup_right_eq_one_of_pow_p_eq_one
    {hyp : Hypothesis (G := G)} (x : fieldNormalizerFrobeniusGroup hyp)
    (hx : x ^ hyp.base.p = 1) :
    (SemidirectProduct.rightHom x : fieldNormalizerNormOneUnits hyp) = 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hright_pow :
      (SemidirectProduct.rightHom x : fieldNormalizerNormOneUnits hyp) ^ hyp.base.p = 1 := by
    have h := congrArg
      (SemidirectProduct.rightHom :
        fieldNormalizerFrobeniusGroup hyp →* fieldNormalizerNormOneUnits hyp) hx
    rw [map_pow] at h
    simpa using h
  have horder_p : orderOf (SemidirectProduct.rightHom x : fieldNormalizerNormOneUnits hyp) ∣
      hyp.base.p := orderOf_dvd_of_pow_eq_one hright_pow
  have horder_card :
      orderOf (SemidirectProduct.rightHom x : fieldNormalizerNormOneUnits hyp) ∣
        Nat.card (fieldNormalizerNormOneUnits hyp) :=
    orderOf_dvd_natCard (SemidirectProduct.rightHom x : fieldNormalizerNormOneUnits hyp)
  have horder_one : orderOf (SemidirectProduct.rightHom x : fieldNormalizerNormOneUnits hyp) = 1 :=
    Nat.eq_one_of_dvd_coprimes (fieldNormalizerNormOneUnits_card_coprime_p hyp)
      horder_p horder_card
  exact orderOf_eq_one_iff.mp horder_one

/-- The concrete `p`-torsion in `P⋊U` is contained in the additive kernel `P`.
This is the semidirect-product core of BG's assertion `P char PU`. -/
theorem fieldNormalizerFrobeniusGroup_mem_kernel_of_pow_p_eq_one
    {hyp : Hypothesis (G := G)} (x : fieldNormalizerFrobeniusGroup hyp)
    (hx : x ^ hyp.base.p = 1) :
    x ∈ fieldNormalizerKernel hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hright := fieldNormalizerFrobeniusGroup_right_eq_one_of_pow_p_eq_one
    (G := G) (hyp := hyp) x hx
  have hright' : x.right = 1 := by
    simpa [SemidirectProduct.rightHom_eq_right] using hright
  refine ⟨x.left, ?_⟩
  calc
    SemidirectProduct.inl x.left =
        (SemidirectProduct.inl x.left : fieldNormalizerFrobeniusGroup hyp) * 1 := by simp
    _ = (SemidirectProduct.inl x.left : fieldNormalizerFrobeniusGroup hyp) *
        SemidirectProduct.inr x.right := by rw [hright']; simp
    _ = x := SemidirectProduct.inl_left_mul_inr_right x

/-- Transported form: every element of Peterfalvi's `P` has `p`-th power `1`. -/
theorem P_pow_p_eq_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x : G} (hx : x ∈ hyp.base.P) :
    x ^ hyp.base.p = 1 := by
  rw [← data.sigma_P_eq_P] at hx
  rcases hx with ⟨h, hhK, hh⟩
  have hhpow := fieldNormalizerKernel_pow_p_eq_one (G := G) (hyp := hyp) hhK
  calc
    x ^ hyp.base.p = (data.sigma h) ^ hyp.base.p := by rw [hh]
    _ = data.sigma (h ^ hyp.base.p) := by rw [map_pow]
    _ = 1 := by rw [hhpow, map_one]

/-- Transported form of `P char PU`: the `p`-torsion in `PU` lies in `P`. -/
theorem mem_P_of_mem_P_sup_U_of_pow_p_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x : G} (hxPU : x ∈ hyp.base.P ⊔ hyp.base.U) (hxp : x ^ hyp.base.p = 1) :
    x ∈ hyp.base.P := by
  have hxrange : x ∈ (⊤ : Subgroup (fieldNormalizerFrobeniusGroup hyp)).map data.sigma := by
    rwa [← data.P_sup_U_eq_sigma_top]
  rcases hxrange with ⟨h, _hhtop, hh⟩
  have hhp : h ^ hyp.base.p = 1 := data.sigma_injective (by
    calc
      data.sigma (h ^ hyp.base.p) = (data.sigma h) ^ hyp.base.p := by rw [map_pow]
      _ = x ^ hyp.base.p := by rw [hh]
      _ = 1 := hxp
      _ = data.sigma 1 := by rw [map_one])
  have hhK := fieldNormalizerFrobeniusGroup_mem_kernel_of_pow_p_eq_one
    (G := G) (hyp := hyp) h hhp
  rw [← data.sigma_P_eq_P]
  exact ⟨h, hhK, hh⟩

/-- BG Appendix C Step 3, `P char PU` in normalizer form: anything normalizing
`PU` also normalizes its additive kernel `P`. -/
theorem normalizer_P_sup_U_le_normalizer_P
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    Subgroup.normalizer ((hyp.base.P ⊔ hyp.base.U : Subgroup G) : Set G) ≤
      Subgroup.normalizer (hyp.base.P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hxP
    have hxPU : x ∈ hyp.base.P ⊔ hyp.base.U := (le_sup_left : hyp.base.P ≤
      hyp.base.P ⊔ hyp.base.U) hxP
    have hconjPU : g * x * g⁻¹ ∈ hyp.base.P ⊔ hyp.base.U := (hg x).mp hxPU
    have hxpow : x ^ hyp.base.p = 1 := data.P_pow_p_eq_one hxP
    have hconjpow : (g * x * g⁻¹) ^ hyp.base.p = 1 := by
      have h := congrArg (MulAut.conj g) hxpow
      rw [map_pow] at h
      simpa [MulAut.conj_apply] using h
    exact data.mem_P_of_mem_P_sup_U_of_pow_p_eq_one hconjPU hconjpow
  · intro hxconjP
    have hconjPU : g * x * g⁻¹ ∈ hyp.base.P ⊔ hyp.base.U :=
      (le_sup_left : hyp.base.P ≤ hyp.base.P ⊔ hyp.base.U) hxconjP
    have hxPU : x ∈ hyp.base.P ⊔ hyp.base.U := (hg x).mpr hconjPU
    have hconjpow : (g * x * g⁻¹) ^ hyp.base.p = 1 := data.P_pow_p_eq_one hxconjP
    have hxpow : x ^ hyp.base.p = 1 := by
      have h := congrArg (MulAut.conj g⁻¹) hconjpow
      rw [map_pow] at h
      have hback : MulAut.conj g⁻¹ (g * x * g⁻¹) = x := by
        simp
        group
      rw [hback] at h
      simpa [MulAut.conj_apply] using h
    exact data.mem_P_of_mem_P_sup_U_of_pow_p_eq_one hxPU hxpow

/-- BG Appendix C, Lemma C.3 Step 3 irreducibility bridge: any subgroup of
`PU` that contains `U` is either `U` or all of `PU`.  This transports the
concrete irreducibility theorem for `P⋊U` through `σ`. -/
theorem subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) {X : Subgroup G}
    (hUle : hyp.base.U ≤ X) (hXle : X ≤ hyp.base.P ⊔ hyp.base.U)
    (hne : X ≠ hyp.base.U) :
    X = hyp.base.P ⊔ hyp.base.U := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  let XH : Subgroup (fieldNormalizerFrobeniusGroup hyp) := X.comap data.sigma
  have hXrange : X ≤ data.sigma.range := by
    intro x hx
    have hxPU : x ∈ hyp.base.P ⊔ hyp.base.U := hXle hx
    rw [data.P_sup_U_eq_sigma_top] at hxPU
    simpa using hxPU
  have hUleH : fieldNormalizerComplement hyp ≤ XH := by
    intro g hg
    have hgU : data.sigma g ∈ hyp.base.U := by
      rw [← data.sigma_U_eq_U]
      exact ⟨g, hg, rfl⟩
    exact hUle hgU
  have hUleH' :
      (SemidirectProduct.inr : fieldNormalizerNormOneUnits hyp →*
        fieldNormalizerFrobeniusGroup hyp).range ≤ XH := by
    simpa [fieldNormalizerComplement] using hUleH
  have hneH : XH ≠ fieldNormalizerComplement hyp := by
    intro hXH
    apply hne
    have hmapX : XH.map data.sigma = X := Subgroup.map_comap_eq_self hXrange
    calc
      X = XH.map data.sigma := hmapX.symm
      _ = (fieldNormalizerComplement hyp).map data.sigma := by rw [hXH]
      _ = hyp.base.U := data.sigma_U_eq_U
  have htopH : XH = ⊤ :=
    OddOrder.BG.AppC.NormSet.normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime data.cyclotomic_coprime
      XH hUleH' (by simpa [fieldNormalizerComplement] using hneH)
  have hmapX : XH.map data.sigma = X := Subgroup.map_comap_eq_self hXrange
  calc
    X = XH.map data.sigma := hmapX.symm
    _ = (⊤ : Subgroup (fieldNormalizerFrobeniusGroup hyp)).map data.sigma := by rw [htopH]
    _ = hyp.base.P ⊔ hyp.base.U := data.P_sup_U_eq_sigma_top.symm

/-- BG Appendix C, Lemma C.3 Step 1 inside the concrete `P⋊U`: every element is
`u s₁ v` with `u,v∈U` and `s₁∈P₀`. -/
theorem exists_normOne_primeLine_normOne {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (g : fieldNormalizerFrobeniusGroup hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u v : fieldNormalizerNormOneUnits hyp,
      g = (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simpa [fieldNormalizerPrimeLineElement] using
    OddOrder.BG.AppC.NormSet.normOneFrobenius_exists_inr_primeLine_inr
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime data.cyclotomic_coprime
      (s := (1 : GaloisField hyp.base.p hyp.base.q)) one_ne_zero g

/-- BG Appendix C, Lemma C.3 Step 1 transported to `G`: every element of `PU`
can be written as the `σ`-image of `u s₁ v`. -/
theorem exists_sigma_normOne_primeLine_normOne_of_mem_PU
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x : G} (hx : x ∈ hyp.base.P ⊔ hyp.base.U) :
    ∃ c : ZMod hyp.base.p, ∃ u v : fieldNormalizerNormOneUnits hyp,
      x = data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp) := by
  have hxmap : x ∈ (⊤ : Subgroup (fieldNormalizerFrobeniusGroup hyp)).map data.sigma := by
    rw [← data.P_sup_U_eq_sigma_top]
    exact hx
  rcases hxmap with ⟨g, _hg_top, hg⟩
  rcases data.exists_normOne_primeLine_normOne g with ⟨c, u, v, hgdec⟩
  refine ⟨c, u, v, ?_⟩
  calc
    x = data.sigma g := hg.symm
    _ = data.sigma ((SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v) := by
      rw [hgdec]
    _ = data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp) := by
      simp [map_mul]

/-- BG Appendix C, Lemma C.3 Step 2 inside concrete `P⋊U`: if
`s₁ u s₂` lies in the complement, then either both prime-line factors are
trivial or the complement factor is trivial and the prime-line factors cancel. -/
theorem generatorRelation_step2_primeLine {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {c d : ZMod hyp.base.p}
    (u : fieldNormalizerNormOneUnits hyp)
    (hmem : (fieldNormalizerPrimeLineElement hyp c *
        (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          fieldNormalizerPrimeLineElement hyp d) ∈ fieldNormalizerComplement hyp) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hmem_original :
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd
            ((algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c) *
              (1 : GaloisField hyp.base.p hyp.base.q))) : fieldNormalizerFrobeniusGroup hyp) *
        SemidirectProduct.inr u *
          SemidirectProduct.inl
            (Multiplicative.ofAdd
              ((algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) d) *
                (1 : GaloisField hyp.base.p hyp.base.q)))) ∈
        (SemidirectProduct.inr : fieldNormalizerNormOneUnits hyp →*
          fieldNormalizerFrobeniusGroup hyp).range := by
    simpa [fieldNormalizerPrimeLineElement, fieldNormalizerComplement] using hmem
  exact
    OddOrder.BG.AppC.NormSet.normOneFrobenius_generatorRelation_step2_primeLine
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime data.cyclotomic_coprime
      (s := (1 : GaloisField hyp.base.p hyp.base.q)) one_ne_zero
      (c := c) (d := d) u hmem_original

/-- BG Appendix C, Lemma C.3 Step 2 transported to `G`: the same alternative can
be read from membership of the transported product in `U`. -/
theorem generatorRelation_step2_primeLine_of_sigma_mem_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {c d : ZMod hyp.base.p} (u : fieldNormalizerNormOneUnits hyp)
    (hmem : data.sigma (fieldNormalizerPrimeLineElement hyp c) *
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp d) ∈ hyp.base.U) :
    (c = 0 ∧ d = 0) ∨ (u = 1 ∧ c + d = 0) := by
  have hmem_map : data.sigma (fieldNormalizerPrimeLineElement hyp c) *
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp d) ∈
      (fieldNormalizerComplement hyp).map data.sigma := by
    rwa [data.sigma_U_eq_U]
  rcases hmem_map with ⟨g, hgU, hg⟩
  let prodH : fieldNormalizerFrobeniusGroup hyp :=
    fieldNormalizerPrimeLineElement hyp c *
      (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp d
  have hprod_sigma : data.sigma prodH =
      data.sigma (fieldNormalizerPrimeLineElement hyp c) *
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp d) := by
    simp [prodH, map_mul]
  have hg_eq : g = prodH := data.sigma_injective (by
    rw [hg, hprod_sigma])
  have hmemH : prodH ∈ fieldNormalizerComplement hyp := by
    simpa [← hg_eq] using hgU
  exact data.generatorRelation_step2_primeLine u hmemH

/-- The chosen nonidentity element `s ∈ P₀` cannot normalize `U`.  Otherwise a
nontrivial norm-one unit `u` would give `s u s⁻¹ ∈ U`, and BG Appendix C,
Lemma C.3 Step 2 forces `u = 1`. -/
theorem s_not_normalizes_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    data.s ∉ Subgroup.normalizer (hyp.base.U : Set G) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro hsN
  rcases exists_fieldNormalizerNormOneUnit_ne_one hyp with ⟨u, hu_ne⟩
  have huU :
      data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  have hconjU :
      data.s *
          data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
            data.s⁻¹ ∈ hyp.base.U :=
    (Subgroup.mem_normalizer_iff.mp hsN
      (data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp))).mp huU
  have hsigma_inv :
      data.sigma (fieldNormalizerPrimeLineElement hyp (-1)) = data.s⁻¹ := by
    rw [fieldNormalizerPrimeLineElement_neg hyp (1 : ZMod hyp.base.p)]
    simp [s, fieldNormalizerPrimeLineElement_one]
  have hmem_step :
      data.sigma (fieldNormalizerPrimeLineElement hyp 1) *
          data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp (-1)) ∈ hyp.base.U := by
    simpa [s, fieldNormalizerPrimeLineElement_one, hsigma_inv] using hconjU
  have hstep :=
    data.generatorRelation_step2_primeLine_of_sigma_mem_U
      (c := (1 : ZMod hyp.base.p)) (d := (-1 : ZMod hyp.base.p)) u hmem_step
  rcases hstep with hzero | hone
  · have h1_ne_zero : (1 : ZMod hyp.base.p) ≠ 0 := one_ne_zero
    exact h1_ne_zero hzero.1
  · exact hu_ne hone.1

end FieldNormalizerData
end OddOrder.Peterfalvi.S16
