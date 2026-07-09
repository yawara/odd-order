/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_NormSet
import OddOrder.Peterfalvi.S15_SAndT

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

/-- Consequently the transported prime line `W₂ = P₀` is not contained in
`N_G(U)`.  This is the Step 3 obstruction BG uses after forcing
`P₁ = P₀`. -/
theorem W2_not_le_normalizer_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    ¬ hyp.base.W2 ≤ Subgroup.normalizer (hyp.base.U : Set G) := by
  intro hW2
  exact data.s_not_normalizes_U (hW2 data.s_mem_W2)

/-- Applying the norm-one/unit equivalence is just `σ` on the concrete
semidirect-product complement. -/
theorem normOneUnitsEquivU_apply_coe {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (u : fieldNormalizerNormOneUnits hyp) :
    (data.normOneUnitsEquivU u : G) = data.sigma (SemidirectProduct.inr u) := by
  rfl

/-- Equality of `σ`-images reflects the additive-kernel coordinate in the
concrete semidirect product. -/
theorem sigma_eq_left_eq {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {g h : fieldNormalizerFrobeniusGroup hyp} (heq : data.sigma g = data.sigma h) :
    g.left = h.left :=
  congrArg (fun x : fieldNormalizerFrobeniusGroup hyp => x.left)
    (data.sigma_injective heq)

/-- Equality of `σ`-images reflects the norm-one complement coordinate in the
concrete semidirect product.  This is the precise "mod `P`" reading used in BG
Appendix C, Lemma C.3 Step 4. -/
theorem sigma_eq_right_eq {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {g h : fieldNormalizerFrobeniusGroup hyp} (heq : data.sigma g = data.sigma h) :
    g.right = h.right :=
  congrArg (fun x : fieldNormalizerFrobeniusGroup hyp => x.right)
    (data.sigma_injective heq)

/-- Semidirect normal forms remain unique after applying the field-normalizer
embedding `σ`. -/
theorem sigma_eq_iff_left_right_eq {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {g h : fieldNormalizerFrobeniusGroup hyp} :
    data.sigma g = data.sigma h ↔ g.left = h.left ∧ g.right = h.right := by
  constructor
  · intro heq
    exact ⟨data.sigma_eq_left_eq heq, data.sigma_eq_right_eq heq⟩
  · rintro ⟨hleft, hright⟩
    apply congrArg data.sigma
    apply SemidirectProduct.ext
    · exact hleft
    · exact hright

/-- The conjugate prime-line subgroup `P₁` used in BG Appendix C, expressed
with Lean left-conjugation convention. -/
noncomputable def P1 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    Subgroup G :=
  MulAut.conj data.y • hyp.base.W2

/-- The BG element `t`, the `y`-conjugate of `s` in Lean convention. -/
noncomputable def t {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) : G :=
  MulAut.conj data.y data.s

/-- The transported conjugate generator lies in `P₁`. -/
theorem t_mem_P1 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ∈ data.P1 := by
  dsimp [P1, t]
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  convert data.s_mem_W2 using 1
  simp
  group

/-- The conjugate generator `t` is nontrivial. -/
theorem t_ne_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ≠ 1 := by
  intro ht
  exact data.s_ne_one ((MulAut.conj data.y).injective (by simpa [t] using ht))

/-- The conjugate generator `t` has `p`-th power equal to `1`. -/
theorem t_pow_p_eq_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ^ hyp.base.p = 1 := by
  simpa [t, map_pow] using congrArg (MulAut.conj data.y) data.s_pow_p_eq_one

/-- The conjugate generator `t` has exact order `p`. -/
theorem t_orderOf_eq_p {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    orderOf data.t = hyp.base.p := by
  have hdiv : orderOf data.t ∣ hyp.base.p :=
    orderOf_dvd_of_pow_eq_one data.t_pow_p_eq_one
  rcases hyp.base.p_prime.eq_one_or_self_of_dvd (orderOf data.t) hdiv with h | h
  · exact False.elim (data.t_ne_one (orderOf_eq_one_iff.mp h))
  · exact h

/-- The conjugate prime line `P₁ = P₀^y` is generated by the conjugate generator
`t = s^y`. -/
theorem P1_eq_zpowers_t {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.P1 = Subgroup.zpowers data.t := by
  rw [P1, data.W2_eq_zpowers_s, Subgroup.pointwise_smul_def]
  simp [t]

/-- The conjugate prime line `P₁` is a `p`-group of order `p`. -/
theorem P1_isPGroup {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    IsPGroup hyp.base.p data.P1 := by
  haveI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  haveI : Finite data.P1 := Nat.finite_of_card_ne_zero (by
    rw [data.P1_eq_zpowers_t, Nat.card_zpowers, data.t_orderOf_eq_p]
    exact hyp.base.p_prime.ne_zero)
  rw [IsPGroup.iff_card]
  exact ⟨1, by rw [data.P1_eq_zpowers_t, Nat.card_zpowers, data.t_orderOf_eq_p, pow_one]⟩

/-- The conjugate generator `t = ysy⁻¹` lies in `QW₂`.  Indeed
`ysy⁻¹ = (ysy⁻¹s⁻¹)s`, the first factor is in `Q` because `y ∈ Q` and `s`
normalizes `Q`, and the second factor is in `W₂`. -/
theorem t_mem_Q_sup_W2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ∈ hyp.base.Q ⊔ hyp.base.W2 := by
  have hy_inv : data.y⁻¹ ∈ hyp.base.Q := inv_mem data.y_mem_Q
  have hsy : data.s * data.y⁻¹ * data.s⁻¹ ∈ hyp.base.Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp data.s_normalizes_Q data.y⁻¹).mp hy_inv
  have hq : data.y * data.s * data.y⁻¹ * data.s⁻¹ ∈ hyp.base.Q := by
    simpa [mul_assoc] using mul_mem data.y_mem_Q hsy
  have hprod : (data.y * data.s * data.y⁻¹ * data.s⁻¹) * data.s ∈
      hyp.base.Q ⊔ hyp.base.W2 := by
    exact mul_mem
      ((le_sup_left : hyp.base.Q ≤ hyp.base.Q ⊔ hyp.base.W2) hq)
      ((le_sup_right : hyp.base.W2 ≤ hyp.base.Q ⊔ hyp.base.W2) data.s_mem_W2)
  convert hprod using 1
  dsimp [t]
  group

/-- The conjugate prime line `P₁` lies in `QW₂`.  This is the subgroup-level
form of the preceding semidirect-product decomposition of `t`. -/
theorem P1_le_Q_sup_W2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.P1 ≤ hyp.base.Q ⊔ hyp.base.W2 := by
  rw [data.P1_eq_zpowers_t]
  exact Subgroup.zpowers_le.mpr data.t_mem_Q_sup_W2

/-- The same containment as `P1_le_Q_sup_W2`, in the `W₂Q` order used by the
product/Sylow argument in BG Appendix C Step 3. -/
theorem P1_le_W2_sup_Q {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.P1 ≤ hyp.base.W2 ⊔ hyp.base.Q := by
  intro x hx
  have hx' := data.P1_le_Q_sup_W2 hx
  simpa [sup_comm] using hx'

/-- Since `p` is odd, any subgroup containing `t²` also contains `t`.  This is
the cyclic-generation step in BG Appendix C, Lemma C.3 Step 3. -/
theorem t_mem_of_t_sq_mem {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {N : Subgroup G} (ht2 : data.t ^ 2 ∈ N) :
    data.t ∈ N := by
  rcases hyp.base.p_odd with ⟨k, hp⟩
  have ht_pow : (data.t ^ 2) ^ (k + 1) = data.t := by
    calc
      (data.t ^ 2) ^ (k + 1) = data.t ^ (2 * (k + 1)) := by rw [pow_mul]
      _ = data.t ^ (hyp.base.p + 1) := by
        congr 1
        omega
      _ = data.t := by
        rw [pow_succ, data.t_pow_p_eq_one, one_mul]
  simpa [ht_pow] using N.pow_mem ht2 (k + 1)

/-- If `t²` normalizes `P`, then the whole conjugate prime line `P₁ = ⟨t⟩`
normalizes `P`.  This is the next BG Step 3 consequence after `P char PU`. -/
theorem P1_le_normalizer_P_of_t_sq_mem
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (ht2 : data.t ^ 2 ∈ Subgroup.normalizer (hyp.base.P : Set G)) :
    data.P1 ≤ Subgroup.normalizer (hyp.base.P : Set G) := by
  rw [data.P1_eq_zpowers_t]
  exact Subgroup.zpowers_le.mpr (data.t_mem_of_t_sq_mem ht2)

/-- `P₁` normalizes Peterfalvi subgroup `U`, as required in BG C.3 Step 3. -/
theorem P1_normalizes_U {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.P1 ≤ Subgroup.normalizer (hyp.base.U : Set G) := by
  simpa [P1] using data.W2_conj_y_normalizes_U

/-- BG Appendix C, Lemma C.3 Step 3 contradiction endpoint: the conjugate
prime line `P₁` cannot equal the original prime line `P₀ = W₂`, because `P₁`
normalizes `U` while `W₂` cannot be contained in `N_G(U)`. -/
theorem P1_ne_W2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.P1 ≠ hyp.base.W2 := by
  intro hP1
  exact data.W2_not_le_normalizer_U (by
    intro x hxW2
    exact data.P1_normalizes_U (by simpa [hP1] using hxW2))

/-- The symmetric form of `P1_ne_W2`, useful when BG has derived `P₀ = P₁`. -/
theorem W2_ne_P1 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.W2 ≠ data.P1 := by
  intro hW2
  exact data.P1_ne_W2 hW2.symm

/-- The conjugate generator `t` normalizes `U`. -/
theorem t_normalizes_U {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
  data.P1_normalizes_U data.t_mem_P1

/-- Powers of the conjugate generator `t` normalize `U`. -/
theorem t_pow_normalizes_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℕ) :
    data.t ^ n ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
  pow_mem data.t_normalizes_U n

/-- Integer powers of the conjugate generator `t` normalize `U`. -/
theorem t_zpow_normalizes_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℤ) :
    data.t ^ n ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
  (Subgroup.normalizer (hyp.base.U : Set G)).zpow_mem data.t_normalizes_U n

/-- Conjugating a concrete norm-one complement element by any integer power of
`t` remains in the transported subgroup `U`. -/
theorem t_zpow_conj_sigma_inr_mem_U {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℤ) (u : fieldNormalizerNormOneUnits hyp) :
    data.t ^ n * data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        (data.t ^ n)⁻¹ ∈ hyp.base.U := by
  have huU :
      data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (data.t_zpow_normalizes_U n)
    (data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp))).mp huU

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` membership bridge: any expression
`s^m (u)^{t^n} s^r` with `u ∈ U` lies in `PU`. -/
theorem s_zpow_mul_t_zpow_conj_sigma_inr_mul_s_zpow_mem_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m n r : ℤ) (u : fieldNormalizerNormOneUnits hyp) :
    data.s ^ m *
          (data.t ^ n *
            data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
              (data.t ^ n)⁻¹) *
        data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := by
  have hm : data.s ^ m ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U m
  have hmid :
      data.t ^ n * data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          (data.t ^ n)⁻¹ ∈ hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U)
      (data.t_zpow_conj_sigma_inr_mem_U n u)
  have hr : data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U r
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hm hmid) hr

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` decomposition bridge: expressions
of the form `s^m (u)^{t^n} s^r` admit the Step 1 `u₁ s₁ v₁` normal form. -/
theorem exists_step4_decomposition_of_zpow_tConj_normOne
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m n r : ℤ) (u : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
      data.s ^ m *
            (data.t ^ n *
              data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
                (data.t ^ n)⁻¹) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_t_zpow_conj_sigma_inr_mul_s_zpow_mem_P_sup_U m n r u)


/-- BG Appendix C, Lemma C.3 Step 3 intersection dichotomy before the final
contradiction: if `g` normalizes `U`, then `(PU) ∩ (PU)^g` is either `U` or
all of `PU`. -/
theorem P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) {g : G}
    (hgU : g ∈ Subgroup.normalizer (hyp.base.U : Set G)) :
    (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj g • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.U ∨
      (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj g • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.P ⊔ hyp.base.U := by
  let X : Subgroup G :=
    (hyp.base.P ⊔ hyp.base.U) ⊓ (MulAut.conj g • (hyp.base.P ⊔ hyp.base.U))
  have hUle : hyp.base.U ≤ X := by
    intro u hu
    refine ⟨(le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hu, ?_⟩
    have hU_image : MulAut.conj g '' (hyp.base.U : Set G) = hyp.base.U :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp hgU
    have hu_image : u ∈ MulAut.conj g '' (hyp.base.U : Set G) := by
      rw [hU_image]
      exact hu
    rcases hu_image with ⟨u0, hu0, hu0_eq⟩
    have hu0_PU : u0 ∈ hyp.base.P ⊔ hyp.base.U :=
      (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hu0
    rw [← hu0_eq]
    exact Set.smul_mem_smul_set hu0_PU
  by_cases hX : X = hyp.base.U
  · left
    exact hX
  · right
    exact data.subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U hUle inf_le_left hX

/-- The same Step 3 intersection dichotomy for powers of the chosen conjugate
generator `t`. -/
theorem P_sup_U_inf_conj_t_pow_eq_U_or_eq_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) (n : ℕ) :
    (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj (data.t ^ n) • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.U ∨
      (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj (data.t ^ n) • (hyp.base.P ⊔ hyp.base.U)) =
          hyp.base.P ⊔ hyp.base.U :=
  data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
    (data.t_pow_normalizes_U n)

/-- Conjugation by `t` as an automorphism of Peterfalvi's subgroup `U`. -/
noncomputable def tConjUAut {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : MulAut hyp.base.U :=
  hyp.base.U.normalizerMonoidHom ⟨data.t, data.t_normalizes_U⟩

/-- The subgroup automorphism `tConjUAut` is ambient conjugation by `t`. -/
theorem tConjUAut_apply_coe {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (u : hyp.base.U) :
    (data.tConjUAut u : G) = data.t * (u : G) * data.t⁻¹ := by
  rfl

/-- The `t`-conjugation automorphism of `U` has `p`-th power equal to `1`. -/
theorem tConjUAut_pow_p_eq_one {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : data.tConjUAut ^ hyp.base.p = 1 := by
  have ht_norm :
      (⟨data.t, data.t_normalizes_U⟩ : Subgroup.normalizer (hyp.base.U : Set G)) ^
          hyp.base.p = 1 := by
    ext
    exact data.t_pow_p_eq_one
  rw [tConjUAut, ← map_pow, ht_norm, map_one]

/-- Conjugation by `t`, transported back to the concrete norm-one unit group. -/
noncomputable def tConjNormOneUnitsAut {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : MulAut (fieldNormalizerNormOneUnits hyp) :=
  (MulAut.congr data.normOneUnitsEquivU).symm data.tConjUAut

/-- The transported `t`-conjugation automorphism has `p`-th power equal to `1`. -/
theorem tConjNormOneUnitsAut_pow_p_eq_one {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : data.tConjNormOneUnitsAut ^ hyp.base.p = 1 := by
  rw [tConjNormOneUnitsAut,
    ← map_pow ((MulAut.congr data.normOneUnitsEquivU).symm) data.tConjUAut hyp.base.p,
    data.tConjUAut_pow_p_eq_one, map_one]

/-- The transported automorphism agrees with conjugation by `t` after applying
`σ` to the concrete complement. -/
theorem normOneUnitsEquivU_tConjNormOneUnitsAut {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (u : fieldNormalizerNormOneUnits hyp) :
    data.normOneUnitsEquivU (data.tConjNormOneUnitsAut u) =
      data.tConjUAut (data.normOneUnitsEquivU u) := by
  simp [tConjNormOneUnitsAut]

/-- After transporting back to the concrete complement, the `t`-automorphism is
ambient conjugation of `σ(inr u)`. -/
theorem normOneUnitsEquivU_tConjNormOneUnitsAut_apply_coe
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u : fieldNormalizerNormOneUnits hyp) :
    (data.normOneUnitsEquivU (data.tConjNormOneUnitsAut u) : G) =
      data.t * data.sigma (SemidirectProduct.inr u) * data.t⁻¹ := by
  calc
    (data.normOneUnitsEquivU (data.tConjNormOneUnitsAut u) : G) =
        (data.tConjUAut (data.normOneUnitsEquivU u) : G) := by
      rw [data.normOneUnitsEquivU_tConjNormOneUnitsAut]
    _ = data.t * (data.normOneUnitsEquivU u : G) * data.t⁻¹ :=
      data.tConjUAut_apply_coe (data.normOneUnitsEquivU u)
    _ = data.t * data.sigma (SemidirectProduct.inr u) * data.t⁻¹ := by
      rw [data.normOneUnitsEquivU_apply_coe]

/-- Iterating the transported `t`-automorphism agrees with conjugation by
the corresponding natural power of `t` after applying `σ` to the concrete
complement. -/
theorem normOneUnitsEquivU_tConjNormOneUnitsAut_pow_apply_coe
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    (data.normOneUnitsEquivU ((data.tConjNormOneUnitsAut ^ n) u) : G) =
      data.t ^ n * data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        (data.t ^ n)⁻¹ := by
  induction n with
  | zero =>
      simp [data.normOneUnitsEquivU_apply_coe]
  | succ n ih =>
      calc
        (data.normOneUnitsEquivU ((data.tConjNormOneUnitsAut ^ (n + 1)) u) : G) =
            data.t *
                (data.normOneUnitsEquivU ((data.tConjNormOneUnitsAut ^ n) u) : G) *
              data.t⁻¹ := by
          rw [pow_succ']
          exact data.normOneUnitsEquivU_tConjNormOneUnitsAut_apply_coe
            ((data.tConjNormOneUnitsAut ^ n) u)
        _ = data.t *
              (data.t ^ n *
                data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
                  (data.t ^ n)⁻¹) *
            data.t⁻¹ := by
          rw [ih]
        _ = data.t ^ (n + 1) *
              data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
                (data.t ^ (n + 1))⁻¹ := by
          group

/-- The natural-power conjugate of a concrete complement element is the `σ`
image of the corresponding power of the transported norm-one automorphism. -/
theorem t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    data.t ^ n * data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        (data.t ^ n)⁻¹ =
      data.sigma
        (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
          fieldNormalizerFrobeniusGroup hyp) := by
  rw [← data.normOneUnitsEquivU_apply_coe ((data.tConjNormOneUnitsAut ^ n) u)]
  exact (data.normOneUnitsEquivU_tConjNormOneUnitsAut_pow_apply_coe n u).symm

/-- Natural-power form of the Step 4 conjugation rewrite: the middle
`(u)^{t^n}` term can be read as the concrete norm-one unit obtained by iterating
`tConjNormOneUnitsAut`. -/
theorem s_zpow_mul_t_pow_conj_sigma_inr_mul_s_zpow_eq_sigma_inr_tConjNormOneUnitsAut_pow
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    data.s ^ m *
          (data.t ^ n *
            data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
              (data.t ^ n)⁻¹) *
        data.s ^ r =
      data.s ^ m *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r := by
  rw [data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow n u]

/-- Natural-power variant of the Step 4 `(C.5)` membership bridge, with the
middle term already expressed in the concrete norm-one complement. -/
theorem s_zpow_mul_sigma_inr_tConjNormOneUnitsAut_pow_mul_s_zpow_mem_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    data.s ^ m *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := by
  have hm : data.s ^ m ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U m
  have hmidU :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u),
      ⟨(data.tConjNormOneUnitsAut ^ n) u, rfl⟩, rfl⟩
  have hmid :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hmidU
  have hr : data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U r
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hm hmid) hr

/-- Natural-power variant of the Step 4 `(C.5)` decomposition bridge: after
rewriting `(u)^{t^n}` as a concrete iterate of `tConjNormOneUnitsAut`, the term
still admits Step 1 `u₁ s₁ v₁` normal form. -/
theorem exists_step4_decomposition_of_zpow_tConjNormOneUnitsAut_pow
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
      data.s ^ m *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_sigma_inr_tConjNormOneUnitsAut_pow_mul_s_zpow_mem_P_sup_U m r n u)


/-- BG Appendix C, Lemma C.3 Step 4 "mod `P`" bridge: once a natural-power
`(C.5)` term is written in Step 1 normal form, applying the right projection of
the concrete semidirect product reads off the complement equation. -/
theorem right_component_of_step4_tConjNormOneUnitsAut_pow_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (n : ℕ) (u u₁ v₁ : fieldNormalizerNormOneUnits hyp)
    (c : ZMod hyp.base.p)
    (hdec : data.s ^ m *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    (data.tConjNormOneUnitsAut ^ n) u = u₁ * v₁ := by
  have hmP : data.s ^ m ∈ hyp.base.P := data.s_zpow_mem_P m
  rw [← data.sigma_P_eq_P] at hmP
  rcases hmP with ⟨pm, hpmP, hpm⟩
  have hrP : data.s ^ r ∈ hyp.base.P := data.s_zpow_mem_P r
  rw [← data.sigma_P_eq_P] at hrP
  rcases hrP with ⟨pr, hprP, hpr⟩
  have hpm_right : SemidirectProduct.rightHom pm = 1 := by
    rcases hpmP with ⟨x, rfl⟩
    simp
  have hpr_right : SemidirectProduct.rightHom pr = 1 := by
    rcases hprP with ⟨x, rfl⟩
    simp
  have hline_right :
      SemidirectProduct.rightHom (fieldNormalizerPrimeLineElement hyp c) = 1 := by
    simp [fieldNormalizerPrimeLineElement]
  have hσ :
      data.sigma
          (pm *
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) * pr) =
        data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
    calc
      data.sigma
          (pm *
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
              fieldNormalizerFrobeniusGroup hyp) * pr) =
          data.s ^ m *
              data.sigma
                (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n) u) :
                  fieldNormalizerFrobeniusGroup hyp) *
            data.s ^ r := by
        simp [map_mul, hpm, hpr]
      _ = data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp c) *
              data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
        simp [map_mul]
  have hH := data.sigma_injective hσ
  have hright := congrArg (SemidirectProduct.rightHom :
      fieldNormalizerFrobeniusGroup hyp →* fieldNormalizerNormOneUnits hyp) hH
  simpa [map_mul, hpm_right, hpr_right, hline_right, mul_assoc] using hright

/-- BG Appendix C, Lemma C.3 Step 4 final specialization: the first equation of
`(C.5)` at `k = 3` has a Step 1 normal form.  This is the entry point for the
final paragraph, where `u` is instantiated with the norm-one unit represented by
`a ∈ E`. -/
theorem exists_step4_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
      data.s *
            data.sigma
              (SemidirectProduct.inr
                ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
  simpa using
    data.exists_step4_decomposition_of_zpow_tConjNormOneUnitsAut_pow
      (m := (1 : ℤ)) (r := (-2 : ℤ)) (n := 3) (u := u⁻¹)

/-- The `mod P` reading of the `k = 3` first `(C.5)` equation: the middle term
`u^{-1}` conjugated by `t^3` has complement component `u₁ * v₁`. -/
theorem right_component_of_step4_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u u₁ v₁ : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    (data.tConjNormOneUnitsAut ^ 3) u⁻¹ = u₁ * v₁ := by
  have hdec' : data.s ^ (1 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
    simpa using hdec
  simpa using
    data.right_component_of_step4_tConjNormOneUnitsAut_pow_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ)) (n := 3) (u := u⁻¹)
      (u₁ := u₁) (v₁ := v₁) (c := c) hdec'

/-- BG Appendix C, Lemma C.3 Step 4 final paragraph, finite-field reading:
if a first `k = 3` normal form has middle prime-line factor `s^{-1}`,
then its additive coordinate gives `N(2*w-1)=1` for the middle complement
element `w`. -/
theorem normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (w u₁ v₁ : fieldNormalizerNormOneUnits hyp)
    (hdec : data.s *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q
      ((2 : GaloisField hyp.base.p hyp.base.q) *
          (((w : fieldNormalizerNormOneUnits hyp) :
              (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) - 1) = 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  let F := GaloisField hyp.base.p hyp.base.q
  let H := fieldNormalizerFrobeniusGroup hyp
  have hline_neg_one :
      fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) : H) := by
    simp [fieldNormalizerPrimeLineElement, F]
  have hline_neg_two :
      fieldNormalizerPrimeLineElement hyp (-2 : ZMod hyp.base.p) =
        (SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F))) : H) := by
    simp [fieldNormalizerPrimeLineElement, F, map_neg, map_ofNat]
  have hσ :
      data.sigma
          ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) *
              SemidirectProduct.inr w *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))) =
        data.sigma
          ((SemidirectProduct.inr u₁ : H) *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) *
              SemidirectProduct.inr v₁) := by
    calc
      data.sigma
          ((SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) *
              SemidirectProduct.inr w *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F)))) =
          data.s * data.sigma (SemidirectProduct.inr w : H) * data.s ^ (-2 : ℤ) := by
        have hs :
            data.s =
              data.sigma
                (SemidirectProduct.inl (Multiplicative.ofAdd (1 : F)) : H) := by
          simp [s, fieldNormalizerPrimeLineGenerator, F]
        have hsneg_two :
            data.s ^ (-2 : ℤ) =
              data.sigma
                (SemidirectProduct.inl (Multiplicative.ofAdd (-(2 : F))) : H) := by
          simpa [hline_neg_two] using data.s_zpow_neg_two_eq_primeLineElement_neg_two
        rw [map_mul, map_mul, hsneg_two, hs]
      _ = data.sigma (SemidirectProduct.inr u₁ : H) *
            data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
              data.sigma (SemidirectProduct.inr v₁ : H) := by
        exact hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : H) *
            SemidirectProduct.inl (Multiplicative.ofAdd (-(1 : F))) *
              SemidirectProduct.inr v₁) := by
        simp [map_mul, hline_neg_one]
  have hH := data.sigma_injective hσ
  simpa [F] using
    OddOrder.BG.AppC.NormSet.normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.ne_zero w u₁ v₁ hH

/-- BG Appendix C, Lemma C.3 Step 4 final paragraph, finite-field reading:
if the first `k = 3` equation of `(C.5)` has middle prime-line factor `s^{-1}`,
then its additive coordinate gives `N(2*w-1)=1` for
`w = (tConjNormOneUnitsAut^3)(u^{-1})`. -/
theorem normN_two_mul_sub_one_of_step4_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u u₁ v₁ : fieldNormalizerNormOneUnits hyp)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q
      ((2 : GaloisField hyp.base.p hyp.base.q) *
          ((((data.tConjNormOneUnitsAut ^ 3) u⁻¹ : fieldNormalizerNormOneUnits hyp) :
              (GaloisField hyp.base.p hyp.base.q)ˣ) :
              GaloisField hyp.base.p hyp.base.q) - 1) = 1 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simpa using
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
      ((data.tConjNormOneUnitsAut ^ 3) u⁻¹) u₁ v₁ hdec

/-- A first `k = 3` coordinate step for every element of `E` implies the
AppC generator relation.  This is the exact S16-facing target left after the
BG C.3 Step 4 argument has shown that the middle prime-line factor in the
relevant normal form is `s^{-1}`. -/
theorem appC_normSet_generator_relation_of_first_k_three_coordinate
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hstep :
      letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
      ∀ w : fieldNormalizerNormOneUnits hyp,
        (((w : fieldNormalizerNormOneUnits hyp) :
            (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q) ∈
          OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q →
          ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
            data.s *
                data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
              data.s ^ (-2 : ℤ) =
            data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
              data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
                data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    appCNormSetGeneratorRelation hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro a ha
  let w : fieldNormalizerNormOneUnits hyp :=
    OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE
      hyp.base.p hyp.base.q hyp.base.q_prime.pos ha
  have hwE :
      (((w : fieldNormalizerNormOneUnits hyp) :
          (GaloisField hyp.base.p hyp.base.q)ˣ) :
          GaloisField hyp.base.p hyp.base.q) ∈
        OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
    simpa [w] using ha
  rcases hstep w hwE with ⟨u₁, v₁, hdec⟩
  have hnorm :=
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition w u₁ v₁ hdec
  simpa [w] using hnorm

/-- The `twistedInv` operation in the norm-one C.3 interface is ambient
conjugation by `t` applied to the inverse complement element. -/
theorem normOneUnitsEquivU_twistedInv_tConjNormOneUnitsAut_apply_coe
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u : fieldNormalizerNormOneUnits hyp) :
    (data.normOneUnitsEquivU
        (OddOrder.BG.AppC.NormSet.twistedInv data.tConjNormOneUnitsAut u) : G) =
      data.t * data.sigma (SemidirectProduct.inr u⁻¹) * data.t⁻¹ := by
  simpa [OddOrder.BG.AppC.NormSet.twistedInv] using
    data.normOneUnitsEquivU_tConjNormOneUnitsAut_apply_coe u⁻¹

/-- To produce the S16 AppC C.3 interface it is enough to prove the norm-set
step for the concrete automorphism induced by conjugation with `t`. -/
theorem appC_twisted_normOne_step_of_tConjNormOneUnitsAut
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    OddOrder.BG.AppC.NormSet.normSetETwistedNormOneStep
        (p := hyp.base.p) (q := hyp.base.q) data.tConjNormOneUnitsAut →
      appCNormSetTwistedNormOneStep hyp := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro hstep
  exact ⟨data.tConjNormOneUnitsAut, data.tConjNormOneUnitsAut_pow_p_eq_one, hstep⟩

/-- The conjugate generator `t` also normalizes `Q`. -/
theorem t_normalizes_Q {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.t ∈ Subgroup.normalizer (hyp.base.Q : Set G) := by
  have hyN : data.y ∈ Subgroup.normalizer (hyp.base.Q : Set G) :=
    Subgroup.le_normalizer data.y_mem_Q
  dsimp [t]
  exact mul_mem (mul_mem hyN data.s_normalizes_Q) (inv_mem hyN)

/-- The first BG commutator factor `s⁻¹t` lies in `Q`. -/
theorem s_inv_mul_t_mem_Q {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    data.s⁻¹ * data.t ∈ hyp.base.Q := by
  have hsN_inv : data.s⁻¹ ∈ Subgroup.normalizer (hyp.base.Q : Set G) :=
    inv_mem data.s_normalizes_Q
  have hconj_y : data.s⁻¹ * data.y * data.s ∈ hyp.base.Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp hsN_inv data.y).mp data.y_mem_Q
  have hy_inv : data.y⁻¹ ∈ hyp.base.Q := inv_mem data.y_mem_Q
  dsimp [t]
  simpa [mul_assoc] using mul_mem hconj_y hy_inv

private theorem inv_pow_mul_pow_mem_of_inv_mul_mem {H : Subgroup G} {a b : G}
    (haN : a ∈ Subgroup.normalizer (H : Set G)) (hrel : a⁻¹ * b ∈ H) :
    ∀ n : ℕ, (a⁻¹) ^ n * b ^ n ∈ H := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have haN_inv : a⁻¹ ∈ Subgroup.normalizer (H : Set G) := inv_mem haN
      have hconj : a⁻¹ * ((a⁻¹) ^ n * b ^ n) * a ∈ H := by
        simpa using (Subgroup.mem_normalizer_iff.mp haN_inv ((a⁻¹) ^ n * b ^ n)).mp ih
      have hprod : (a⁻¹ * ((a⁻¹) ^ n * b ^ n) * a) * (a⁻¹ * b) ∈ H :=
        mul_mem hconj hrel
      convert hprod using 1
      group

/-- The BG commutator factors `(s⁻¹)^n t^n` lie in `Q`. -/
theorem s_inv_pow_mul_t_pow_mem_Q {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℕ) :
    (data.s⁻¹) ^ n * data.t ^ n ∈ hyp.base.Q :=
  inv_pow_mul_pow_mem_of_inv_mul_mem data.s_normalizes_Q data.s_inv_mul_t_mem_Q n

/-- Elements of the transported `Q` commute.  This is the S16-facing form of
BG Appendix C Remark (B)/(X) used in Lemma C.3 Step 4 when rewriting (C.3) to
(C.4). -/
theorem Q_mul_comm {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x y : G} (hx : x ∈ hyp.base.Q) (hy : y ∈ hyp.base.Q) :
    x * y = y * x := by
  simpa using congrArg Subtype.val
    (data.Q_elementaryAbelian.comm ⟨x, hx⟩ ⟨y, hy⟩)

/-- In `W₂Q`, the `Q` factor is normalized by both `W₂` and `Q`. -/
theorem W2_sup_Q_le_normalizer_Q {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    hyp.base.W2 ⊔ hyp.base.Q ≤ Subgroup.normalizer (hyp.base.Q : Set G) :=
  sup_le data.W2_normalizes_Q Subgroup.le_normalizer

/-- The `Q` factor is normal inside the product subgroup `W₂Q`.  This is the
structural input needed before applying the standard p-subgroup/Sylow argument
inside `W₂Q`. -/
theorem Q_subgroupOf_W2_sup_Q_normal {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    (hyp.base.Q.subgroupOf (hyp.base.W2 ⊔ hyp.base.Q)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer data.W2_sup_Q_le_normalizer_Q

/-- Elements of the transported prime line `W₂ = σ(P₀)` have `p`-th power
`1`.  This is the ambient `G` form needed when reading BG Appendix C Step 4
modulo `Q`. -/
theorem W2_pow_p_eq_one {hyp : Hypothesis (G := G)} (_data : FieldNormalizerData hyp)
    {x : G} (hx : x ∈ hyp.base.W2) :
    x ^ hyp.base.p = 1 := by
  haveI : Finite hyp.base.W2 := Nat.finite_of_card_ne_zero (by
    rw [← hyp.base.p_eq_card_W2]
    exact hyp.base.p_prime.ne_zero)
  have hxpow := pow_card_eq_one' (G := hyp.base.W2) (x := (⟨x, hx⟩ : hyp.base.W2))
  have hxpow_coe := congrArg Subtype.val hxpow
  simpa [← hyp.base.p_eq_card_W2] using hxpow_coe

/-- Elements of the transported elementary abelian subgroup `Q` have `q`-th
power `1`, in ambient `G` form. -/
theorem Q_pow_q_eq_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x : G} (hx : x ∈ hyp.base.Q) :
    x ^ hyp.base.q = 1 := by
  simpa using congrArg Subtype.val
    (data.Q_elementaryAbelian.pow_eq_one (⟨x, hx⟩ : hyp.base.Q))

/-- The transported additive kernel `P` and the transported elementary abelian
subgroup `Q` meet trivially.  In BG Appendix C Step 3 this is the first input for
reading `P ∩ QP₀ = P₀`. -/
theorem P_inf_Q_eq_bot {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.P ⊓ hyp.base.Q = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxp : x ^ hyp.base.p = 1 := data.P_pow_p_eq_one hx.1
  have hxq : x ^ hyp.base.q = 1 := data.Q_pow_q_eq_one hx.2
  have horder_p : orderOf x ∣ hyp.base.p := orderOf_dvd_of_pow_eq_one hxp
  have horder_q : orderOf x ∣ hyp.base.q := orderOf_dvd_of_pow_eq_one hxq
  have hpq : Nat.Coprime hyp.base.p hyp.base.q :=
    (Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q
  have horder_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hpq horder_p horder_q
  simpa [Subgroup.mem_bot] using orderOf_eq_one_iff.mp horder_one

/-- BG Appendix C Step 3 product intersection: inside the product subgroup `W₂Q`,
the transported additive kernel `P` meets `W₂Q` exactly in `W₂`.  This is the
Lean form of BG's `P ∩ QP₀ = P₀`. -/
theorem P_inf_W2_sup_Q_eq_W2 {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    hyp.base.P ⊓ (hyp.base.W2 ⊔ hyp.base.Q) = hyp.base.W2 := by
  let H : Subgroup G := hyp.base.W2 ⊔ hyp.base.Q
  apply le_antisymm
  · intro x hx
    have hxP : x ∈ hyp.base.P := hx.1
    have hxH : x ∈ H := hx.2
    haveI : (hyp.base.Q.subgroupOf H).Normal := data.Q_subgroupOf_W2_sup_Q_normal
    have hmem : (⟨x, hxH⟩ : H) ∈
        hyp.base.W2.subgroupOf H ⊔ hyp.base.Q.subgroupOf H := by
      rw [← Subgroup.subgroupOf_sup (le_sup_left : hyp.base.W2 ≤ H)
        (le_sup_right : hyp.base.Q ≤ H), Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_right] at hmem
    obtain ⟨⟨w, _hwH⟩, hw, ⟨q, _hqH⟩, hq, heq⟩ := hmem
    have hxeq : x = w * q := (congrArg Subtype.val heq).symm
    have hwW2 : w ∈ hyp.base.W2 := hw
    have hqQ : q ∈ hyp.base.Q := hq
    have hqP : q ∈ hyp.base.P := by
      have : w⁻¹ * x ∈ hyp.base.P :=
        hyp.base.P.mul_mem (hyp.base.P.inv_mem (data.W2_le_P hwW2)) hxP
      rwa [hxeq, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have hq_one : q = 1 := by
      have : q ∈ hyp.base.P ⊓ hyp.base.Q := ⟨hqP, hqQ⟩
      rw [data.P_inf_Q_eq_bot, Subgroup.mem_bot] at this
      exact this
    rw [hxeq, hq_one, mul_one]
    exact hwW2
  · exact le_inf data.W2_le_P le_sup_left

/-- The same product-intersection statement in BG's displayed `QP₀` order. -/
theorem P_inf_Q_sup_W2_eq_W2 {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    hyp.base.P ⊓ (hyp.base.Q ⊔ hyp.base.W2) = hyp.base.W2 := by
  simpa [sup_comm] using data.P_inf_W2_sup_Q_eq_W2

/-- If the conjugate line `P₁` normalizes `P`, then, since `P₁ ≤ W₂Q`, it also
normalizes `P ∩ W₂Q = W₂`.  This is the formal normalizer step in BG Appendix C
Step 3 before the final Sylow/product p-subgroup contradiction. -/
theorem P1_le_normalizer_W2_of_le_normalizer_P
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hP1P : data.P1 ≤ Subgroup.normalizer (hyp.base.P : Set G)) :
    data.P1 ≤ Subgroup.normalizer (hyp.base.W2 : Set G) := by
  let H : Subgroup G := hyp.base.W2 ⊔ hyp.base.Q
  intro x hxP1
  have hxNP : x ∈ Subgroup.normalizer (hyp.base.P : Set G) := hP1P hxP1
  have hxH : x ∈ H := data.P1_le_W2_sup_Q hxP1
  have hxNH : x ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hxH
  rw [Subgroup.mem_normalizer_iff] at hxNP hxNH ⊢
  intro y
  constructor
  · intro hyW2
    have hyInf : y ∈ hyp.base.P ⊓ H := by
      rw [data.P_inf_W2_sup_Q_eq_W2]
      exact hyW2
    rw [← data.P_inf_W2_sup_Q_eq_W2]
    exact ⟨(hxNP y).mp hyInf.1, (hxNH y).mp hyInf.2⟩
  · intro hconjW2
    have hconjInf : x * y * x⁻¹ ∈ hyp.base.P ⊓ H := by
      rw [data.P_inf_W2_sup_Q_eq_W2]
      exact hconjW2
    rw [← data.P_inf_W2_sup_Q_eq_W2]
    exact ⟨(hxNP y).mpr hconjInf.1, (hxNH y).mpr hconjInf.2⟩

/-- The transported prime line and the transported elementary abelian `Q` meet
trivially.  This is the BG Appendix C Step 4 `P₀ ∩ Q = 1` input after
identifying `P₀` with `W₂ = σ(P₀)`. -/
theorem W2_inf_Q_eq_bot {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    hyp.base.W2 ⊓ hyp.base.Q = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxW2 : x ∈ hyp.base.W2 := hx.1
  have hxQ : x ∈ hyp.base.Q := hx.2
  have hxp : x ^ hyp.base.p = 1 := data.W2_pow_p_eq_one hxW2
  have hxq : x ^ hyp.base.q = 1 := data.Q_pow_q_eq_one hxQ
  have horder_p : orderOf x ∣ hyp.base.p := orderOf_dvd_of_pow_eq_one hxp
  have horder_q : orderOf x ∣ hyp.base.q := orderOf_dvd_of_pow_eq_one hxq
  have hpq : Nat.Coprime hyp.base.p hyp.base.q :=
    (Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q
  have horder_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hpq horder_p horder_q
  simpa [Subgroup.mem_bot] using orderOf_eq_one_iff.mp horder_one

/-- The orders of `W₂ = σ(P₀)` and `Q` are coprime: `|W₂| = p` is prime, `|Q|`
is a power of `q`, and `p ≠ q`.  This is the coprimality input to BG Appendix C
Remark (X)'s coprime decomposition `Q = C_Q(P₀) × ⁅Q, P₀⁆` (Isaacs Thm 4.34 /
BG Prop 1.6(d)), used in the Lemma C.3 Step 4 kernel argument. -/
theorem W2_card_coprime_Q_card [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    Nat.Coprime (Nat.card ↥hyp.base.W2) (Nat.card ↥hyp.base.Q) := by
  haveI : Fact hyp.base.q.Prime := ⟨hyp.base.q_prime⟩
  have hW2 : Nat.card ↥hyp.base.W2 = hyp.base.p := hyp.base.p_eq_card_W2.symm
  obtain ⟨k, hQ⟩ : ∃ k, Nat.card ↥hyp.base.Q = hyp.base.q ^ k :=
    ⟨_, data.Q_elementaryAbelian.card_eq_pow_finrank⟩
  rw [hW2, hQ]
  exact ((Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q).pow_right k

/-- If `P₁` normalizes `W₂`, then the product `W₂P₁` is a p-subgroup of `W₂Q`.
Since `Q` is p-prime and `|W₂| = p`, the p-part of `W₂Q` has order exactly `p`,
so `P₁ = W₂`.  This is the final product/Sylow argument in BG Appendix C Step 3. -/
theorem P1_eq_W2_of_le_normalizer_W2 [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hP1W2 : data.P1 ≤ Subgroup.normalizer (hyp.base.W2 : Set G)) :
    data.P1 = hyp.base.W2 := by
  let R : Subgroup G := hyp.base.W2 ⊔ data.P1
  let H : Subgroup G := hyp.base.W2 ⊔ hyp.base.Q
  haveI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hR_p : IsPGroup hyp.base.p R := by
    exact IsPGroup.to_sup_of_normal_left' data.W2_isPGroup data.P1_isPGroup hP1W2
  obtain ⟨k, hR_card⟩ := (IsPGroup.iff_card (p := hyp.base.p) (G := R)).mp hR_p
  have hW2_le_R : hyp.base.W2 ≤ R := le_sup_left
  have hR_le_H : R ≤ H := sup_le le_sup_left data.P1_le_W2_sup_Q
  have hW2_card_le_R : Nat.card ↥hyp.base.W2 ≤ Nat.card ↥R :=
    Subgroup.card_le_of_le hW2_le_R
  have hk_pos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hp_le_one : hyp.base.p ≤ 1 := by
      simpa [hR_card, hk0, pow_zero, hyp.base.p_eq_card_W2] using hW2_card_le_R
    exact (not_lt_of_ge hp_le_one) hyp.base.p_prime.one_lt
  have hR_dvd_H : Nat.card ↥R ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hR_le_H
  have hH_card : Nat.card ↥H = hyp.base.p * Nat.card ↥hyp.base.Q := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card hyp.base.W2 hyp.base.Q
    have hcarrier : (↑H : Set G) = (↑hyp.base.W2 * ↑hyp.base.Q : Set G) := by
      simpa [H] using
        Subgroup.coe_mul_of_left_le_normalizer_right
          hyp.base.W2 hyp.base.Q data.W2_normalizes_Q
    rw [data.W2_inf_Q_eq_bot, Subgroup.card_bot, mul_one,
      ← hyp.base.p_eq_card_W2, ← hcarrier] at hcard
    simpa [H, Nat.card_coe_set_eq] using hcard
  have hpk_dvd : hyp.base.p ^ k ∣ hyp.base.p * Nat.card ↥hyp.base.Q := by
    simpa [hR_card, hH_card] using hR_dvd_H
  have hQ_coprime_p : Nat.Coprime (Nat.card ↥hyp.base.Q) hyp.base.p := by
    simpa [hyp.base.p_eq_card_W2] using (data.W2_card_coprime_Q_card).symm
  have hpk_coprime_Q : Nat.Coprime (hyp.base.p ^ k) (Nat.card ↥hyp.base.Q) :=
    hQ_coprime_p.symm.pow_left k
  have hpk_dvd_p : hyp.base.p ^ k ∣ hyp.base.p :=
    Nat.Coprime.dvd_of_dvd_mul_right hpk_coprime_Q hpk_dvd
  have hk_le_one : k ≤ 1 := by
    exact (Nat.pow_dvd_pow_iff_le_right hyp.base.p_prime.one_lt).mp
      (by simpa [pow_one] using hpk_dvd_p)
  have hk_eq_one : k = 1 := le_antisymm hk_le_one (Nat.succ_le_of_lt hk_pos)
  have hR_card_eq_W2 : Nat.card ↥R = Nat.card ↥hyp.base.W2 := by
    rw [hR_card, hk_eq_one, pow_one, hyp.base.p_eq_card_W2]
  have hW2_eq_R : hyp.base.W2 = R := by
    exact Subgroup.eq_of_le_of_card_ge hW2_le_R (by rw [hR_card_eq_W2])
  have hP1_le_W2 : data.P1 ≤ hyp.base.W2 := by
    intro x hx
    have hxR : x ∈ R := (le_sup_right : data.P1 ≤ R) hx
    simpa [hW2_eq_R] using hxR
  have hP1_card : Nat.card ↥data.P1 = hyp.base.p := by
    rw [data.P1_eq_zpowers_t, Nat.card_zpowers, data.t_orderOf_eq_p]
  exact Subgroup.eq_of_le_of_card_ge hP1_le_W2 (by
    rw [← hyp.base.p_eq_card_W2, hP1_card])


/-- The conjugation action of `W₂ = σ(P₀)` on the normal elementary abelian
subgroup `Q`, restricted to `↥Q`.  This is the coprime action used to
instantiate BG Appendix C Remark (X)'s decomposition `Q = C_Q(P₀) × ⁅Q, P₀⁆`
(Isaacs Thm 4.34 / BG Prop 1.6(d)) in the Lemma C.3 Step 4 kernel argument. -/
noncomputable def w2ConjQAut {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    ↥hyp.base.W2 →* MulAut ↥hyp.base.Q :=
  (Subgroup.normalizerMonoidHom (H := hyp.base.Q)).comp
    (Subgroup.inclusion data.W2_normalizes_Q)

/-- **BG Appendix C, Remark (X)** (Isaacs Thm 4.34 / BG Prop 1.6(d)): under the
coprime conjugation action of `W₂` on the elementary abelian `Q`, the fixed
points `C_Q(W₂)` and the action commutator `⁅Q, W₂⁆` meet trivially.  This is the
fixed-point-free input to the BG Lemma C.3 Step 4 kernel argument: an element of
`⁅Q, W₂⁆` fixed by `W₂` (equivalently, centralizing the prime line) is trivial. -/
theorem w2ConjQAut_fixedPoints_inf_actionCommutator_eq_bot [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    Subgroup.fixedPointsOfMulAut data.w2ConjQAut ⊓
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut = ⊥ := by
  letI : CommGroup ↥hyp.base.Q :=
    { (inferInstance : Group ↥hyp.base.Q) with
      mul_comm := data.Q_elementaryAbelian.comm }
  exact OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian
    data.w2ConjQAut data.W2_card_coprime_Q_card

/-- **BG Appendix C, Lemma C.3 Step 4 fixed-point-free input**: an element of the
action commutator `⁅Q, W₂⁆` fixed by the whole `W₂`-action is trivial.  Since
`W₂` is generated by `s`, this is BG's statement that `s` acts without nonzero
fixed points on `⁅Q, P₀⁆`, the key to inverting `(s⁻¹ - 1)` in the kernel step. -/
theorem w2ConjQAut_eq_one_of_mem_actionCommutator_of_fixed [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {x : ↥hyp.base.Q}
    (hx : x ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut)
    (hfix : ∀ w : ↥hyp.base.W2, data.w2ConjQAut w x = x) :
    x = 1 := by
  have hmem : x ∈ Subgroup.fixedPointsOfMulAut data.w2ConjQAut ⊓
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut :=
    ⟨Subgroup.mem_fixedPointsOfMulAut.mpr hfix, hx⟩
  rw [data.w2ConjQAut_fixedPoints_inf_actionCommutator_eq_bot] at hmem
  simpa using hmem

/-- The `W₂`-conjugation action on `Q`, read in the ambient group `G`: it is
genuine conjugation `w x w⁻¹`. -/
theorem w2ConjQAut_apply_coe {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (w : ↥hyp.base.W2) (x : ↥hyp.base.Q) :
    ((data.w2ConjQAut w x : ↥hyp.base.Q) : G) = (w : G) * (x : G) * (w : G)⁻¹ := rfl

/-- **BG Appendix C, Remark (XI)**: we may assume `y ∈ ⁅Q, P₀⁆`.  Writing the
coprime decomposition `Q = ⁅Q,W₂⁆ · C_Q(W₂)`, the centralizer component `yC` of
`y` commutes with `s ∈ W₂`, so the conjugate generator `t = y s y⁻¹` is already
produced by the action-commutator component `yD ∈ ⁅Q, W₂⁆`: `t = yD s yD⁻¹`. -/
theorem exists_yD_mem_actionCommutator_conj_s_eq_t [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    ∃ yD : ↥hyp.base.Q,
      yD ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ∧
        MulAut.conj (yD : G) data.s = data.t := by
  letI : CommGroup ↥hyp.base.Q :=
    { (inferInstance : Group ↥hyp.base.Q) with
      mul_comm := data.Q_elementaryAbelian.comm }
  have hsup : OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ⊔
      Subgroup.fixedPointsOfMulAut data.w2ConjQAut = ⊤ := by
    rw [sup_comm]
    exact OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      data.W2_card_coprime_Q_card (Or.inr inferInstance)
  have hmem : (⟨data.y, data.y_mem_Q⟩ : ↥hyp.base.Q) ∈
      OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ⊔
        Subgroup.fixedPointsOfMulAut data.w2ConjQAut := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨yD, hyD, yC, hyC, hyDyC⟩ := hmem
  refine ⟨yD, hyD, ?_⟩
  have hyC_s : (yC : G) * data.s = data.s * (yC : G) := by
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hyC ⟨data.s, data.s_mem_W2⟩
    have hcoe := congrArg (Subtype.val) hfix
    rw [data.w2ConjQAut_apply_coe] at hcoe
    exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
  have hconj_raw : (yC : G) * data.s * (yC : G)⁻¹ = data.s := by
    rw [hyC_s]; group
  have hy_coe : (data.y : G) = (yD : G) * (yC : G) := by
    have h := congrArg (Subtype.val) hyDyC
    simpa using h.symm
  show MulAut.conj (yD : G) data.s = MulAut.conj data.y data.s
  rw [MulAut.conj_apply, MulAut.conj_apply, hy_coe, mul_inv_rev,
    show (yD : G) * (yC : G) * data.s * ((yC : G)⁻¹ * (yD : G)⁻¹)
        = (yD : G) * ((yC : G) * data.s * (yC : G)⁻¹) * (yD : G)⁻¹ by group,
    hconj_raw]

/-- **BG Appendix C, Lemma C.3 Step 4, the `s^a` notation**: conjugating the
prime-line generator `s` by `σ(inr a)` (`a ∈ U`) acts as scalar multiplication by
`a⁻¹` on the additive line, i.e. `σ(inr a)⁻¹ s σ(inr a) = σ(inl (a⁻¹ · 1))`.  This
is the concrete reading of BG's relation `as + bs = 2s ⟹ s^a s^b = s²`. -/
theorem sigma_inr_inv_mul_s_mul_sigma_inr {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (a : fieldNormalizerNormOneUnits hyp) :
    letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
    (data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
        data.sigma (SemidirectProduct.inr a) =
      data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd
        (((((a⁻¹ : fieldNormalizerNormOneUnits hyp) :
            (GaloisField hyp.base.p hyp.base.q)ˣ) :
            GaloisField hyp.base.p hyp.base.q)) *
          (1 : GaloisField hyp.base.p hyp.base.q)))) := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  rw [s, fieldNormalizerPrimeLineGenerator, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv]
  have h := OddOrder.BG.AppC.NormSet.normOneFrobenius_conj_inl
    (p := hyp.base.p) (q := hyp.base.q) a⁻¹
    (1 : GaloisField hyp.base.p hyp.base.q)
  rw [inv_inv] at h
  exact h

/-- The BG factors `(s⁻¹)^m t^m` and `(s⁻¹)^n t^n` commute because both lie
in `Q`. -/
theorem s_inv_pow_mul_t_pow_mul_comm {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (m n : ℕ) :
    ((data.s⁻¹) ^ m * data.t ^ m) * ((data.s⁻¹) ^ n * data.t ^ n) =
      ((data.s⁻¹) ^ n * data.t ^ n) * ((data.s⁻¹) ^ m * data.t ^ m) :=
  data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q m) (data.s_inv_pow_mul_t_pow_mem_Q n)

/-- The opposite first commutator factor `t⁻¹s` lies in `Q`. -/
theorem t_inv_mul_s_mem_Q {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    data.t⁻¹ * data.s ∈ hyp.base.Q := by
  simpa using inv_mem data.s_inv_mul_t_mem_Q

/-- The opposite BG commutator factors `(t⁻¹)^n s^n` lie in `Q`. -/
theorem t_inv_pow_mul_s_pow_mem_Q {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (n : ℕ) :
    (data.t⁻¹) ^ n * data.s ^ n ∈ hyp.base.Q :=
  inv_pow_mul_pow_mem_of_inv_mul_mem data.t_normalizes_Q data.t_inv_mul_s_mem_Q n

/-- The opposite BG factors `(t⁻¹)^m s^m` and `(t⁻¹)^n s^n` commute because
both lie in `Q`. -/
theorem t_inv_pow_mul_s_pow_mul_comm {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (m n : ℕ) :
    ((data.t⁻¹) ^ m * data.s ^ m) * ((data.t⁻¹) ^ n * data.s ^ n) =
      ((data.t⁻¹) ^ n * data.s ^ n) * ((data.t⁻¹) ^ m * data.s ^ m) :=
  data.Q_mul_comm (data.t_inv_pow_mul_s_pow_mem_Q m) (data.t_inv_pow_mul_s_pow_mem_Q n)

/-- The two BG commutator-factor families commute with each other inside `Q`. -/
theorem s_inv_pow_mul_t_pow_mul_comm_t_inv_pow_mul_s_pow
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) (m n : ℕ) :
    ((data.s⁻¹) ^ m * data.t ^ m) * ((data.t⁻¹) ^ n * data.s ^ n) =
      ((data.t⁻¹) ^ n * data.s ^ n) * ((data.s⁻¹) ^ m * data.t ^ m) :=
  data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q m) (data.t_inv_pow_mul_s_pow_mem_Q n)

-- The C.3 generator-relation interface `appC_normSet_generator_relation` is now
-- *derived* from the Step 4 capstone (`s₁ = s⁻¹`) rather than carried as a field;
-- see its definition after `step4Capstone` below.

/-! ### BG Appendix C, Lemma C.3 Step 4: the generator relation `s₁ = s⁻¹`

The remaining mathematical gap of BG Appendix C (mmd L4994–5095): the central
prime-line factor of the relevant `k = 3` normal form is `s⁻¹`.  The argument is
the group-relation chain (C.2)–(C.10), a kernel/fixed-point-free step inside
`End ⁅Q, P₀⁆`, and a final contradiction via Steps 2–3.

We work throughout with the prime-field-line scalar `s^x := σ(inl(ofAdd x))` for a
field scalar `x ∈ 𝔽_{p^q}`; conjugating by `σ(inr a)` (`a ∈ U`) scales by `↑a⁻¹`. -/

section Step4

/-- Local `Fact` instance for the Step 4 development, so that
`GaloisField hyp.base.p hyp.base.q` elaborates in signatures with a field scalar
argument.  Scoped to the section; downstream callers supply their own. -/
local instance factPPrimeStep4 {hyp : Hypothesis (G := G)} : Fact hyp.base.p.Prime :=
  ⟨hyp.base.p_prime⟩

/-- BG Appendix C prime-field-line scalar `s^x`: the additive-line element
`σ(inl(ofAdd x))` for a field scalar `x ∈ 𝔽_{p^q}`.  The distinguished generator is
`s = s^1`, and `s^x · s^y = s^{x+y}`. -/
noncomputable def sScalar {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (x : GaloisField hyp.base.p hyp.base.q) : G :=
  data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd x))

/-- The prime-field-line scalars are additive in the exponent: `s^x · s^y = s^{x+y}`. -/
theorem sScalar_mul {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (x y : GaloisField hyp.base.p hyp.base.q) :
    data.sScalar x * data.sScalar y = data.sScalar (x + y) := by
  rw [sScalar, sScalar, sScalar, ← map_mul data.sigma,
    ← map_mul (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.base.p hyp.base.q →*
        fieldNormalizerFrobeniusGroup hyp),
    ← ofAdd_add]

/-- The trivial scalar `s^0 = 1`. -/
theorem sScalar_zero {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.sScalar 0 = 1 := by
  rw [sScalar, ofAdd_zero, map_one, map_one]

/-- The distinguished generator is the scalar `s = s^1`. -/
theorem s_eq_sScalar_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s = data.sScalar 1 := by
  rw [sScalar, s, fieldNormalizerPrimeLineGenerator]

/-- The field value `↑a ∈ 𝔽_{p^q}` of a norm-one unit `a ∈ U`. -/
def unitVal {hyp : Hypothesis (G := G)} (a : fieldNormalizerNormOneUnits hyp) :
    GaloisField hyp.base.p hyp.base.q :=
  ((a : (GaloisField hyp.base.p hyp.base.q)ˣ) : GaloisField hyp.base.p hyp.base.q)

/-- The field value of an inverse unit is the inverse field value. -/
theorem unitVal_inv {hyp : Hypothesis (G := G)} (a : fieldNormalizerNormOneUnits hyp) :
    unitVal a⁻¹ = (unitVal a)⁻¹ := by
  simp [unitVal]

/-- The field value of a norm-one unit is nonzero. -/
theorem unitVal_ne_zero {hyp : Hypothesis (G := G)} (a : fieldNormalizerNormOneUnits hyp) :
    unitVal a ≠ 0 := by
  simpa [unitVal] using (a : (GaloisField hyp.base.p hyp.base.q)ˣ).ne_zero

/-- Conjugating the prime-line scalar `s^x` by `σ(inr a)` scales the exponent by
`↑a⁻¹`: `σ(inr a)⁻¹ · s^x · σ(inr a) = s^{(↑a⁻¹)·x}`.  This is BG's `s^a` notation. -/
theorem sScalar_conj {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) (x : GaloisField hyp.base.p hyp.base.q) :
    (data.sigma (SemidirectProduct.inr a))⁻¹ * data.sScalar x *
        data.sigma (SemidirectProduct.inr a) =
      data.sScalar (unitVal a⁻¹ * x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv]
  have h := OddOrder.BG.AppC.NormSet.normOneFrobenius_conj_inl
    (p := hyp.base.p) (q := hyp.base.q) a⁻¹ x
  rw [inv_inv] at h
  exact h

/-- Inversion of a prime-line scalar negates the exponent: `(s^x)⁻¹ = s^{-x}`. -/
theorem sScalar_inv {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (x : GaloisField hyp.base.p hyp.base.q) :
    (data.sScalar x)⁻¹ = data.sScalar (-x) := by
  rw [sScalar, sScalar, ← map_inv, ← map_inv, ← ofAdd_neg]

/-- `s⁻¹ = s^{-1}` as a prime-line scalar. -/
theorem s_inv_eq_sScalar_neg_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s⁻¹ = data.sScalar (-1) := by
  rw [s_eq_sScalar_one, sScalar_inv]

/-- `s² = s^2` as a prime-line scalar. -/
theorem s_sq_eq_sScalar_two {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s ^ 2 = data.sScalar 2 := by
  rw [s_eq_sScalar_one, pow_two, sScalar_mul]
  congr 1
  norm_num

/-- The transported prime-line element `σ(P₀ c)` is the scalar `s^{algebraMap c}`. -/
theorem sigma_primeLineElement_eq_sScalar {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (c : ZMod hyp.base.p) :
    data.sigma (fieldNormalizerPrimeLineElement hyp c) =
      data.sScalar
        (algebraMap (ZMod hyp.base.p) (GaloisField hyp.base.p hyp.base.q) c) := by
  rw [sScalar, fieldNormalizerPrimeLineElement]

/-- The central prime-line scalar `s^{-1}` equals `σ(P₀ (-1))`, the middle factor
of the target normal form. -/
theorem sScalar_neg_one_eq_sigma_primeLineElement {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    data.sScalar (-1) =
      data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) := by
  rw [sigma_primeLineElement_eq_sScalar]
  congr 1
  push_cast
  ring

/-- **BG Appendix C, Lemma C.3 Step 4 base relation** (mmd L4994): for norm-one
units `a, b` with `↑a⁻¹ + ↑b⁻¹ = 2`, BG's identity `s^a · s^b = s²`, where the BG
conjugate `s^a = σ(inr a)⁻¹ · s · σ(inr a) = s^{↑a⁻¹}`. -/
theorem sBGConj_mul_sBGConj {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    ((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
          data.sigma (SemidirectProduct.inr a)) *
        ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
          data.sigma (SemidirectProduct.inr b)) =
      data.s ^ 2 := by
  have ha : (data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
      data.sigma (SemidirectProduct.inr a) = data.sScalar (unitVal a⁻¹) := by
    rw [s_eq_sScalar_one, sScalar_conj, mul_one]
  have hb : (data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
      data.sigma (SemidirectProduct.inr b) = data.sScalar (unitVal b⁻¹) := by
    rw [s_eq_sScalar_one, sScalar_conj, mul_one]
  rw [ha, hb, sScalar_mul, hab, s_sq_eq_sScalar_two]

/-- **BG Appendix C, Lemma C.3 Step 4 relation (C.2)** (mmd L4994): for norm-one
units `a, b` with `↑a⁻¹ + ↑b⁻¹ = 2`,
`s⁻² · (σ(inr a)⁻¹ s σ(inr a)) · (σ(inr b)⁻¹ s σ(inr b)) = 1`. -/
theorem relationC2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    data.s ^ (-2 : ℤ) *
        (((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
            data.sigma (SemidirectProduct.inr a)) *
          ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
            data.sigma (SemidirectProduct.inr b))) = 1 := by
  rw [data.sBGConj_mul_sBGConj a b hab, zpow_neg, zpow_two, ← pow_two,
    inv_mul_cancel]

/-- **BG Appendix C, Lemma C.3 Step 4 companion** (mmd L4994): for a norm-one unit
`a` whose inverse field value lies in `E`, BG's companion element `b ∈ E` with
`a + b = 2` exists as a norm-one unit.  Concretely, `↑b⁻¹ = 2 - ↑a⁻¹` (so the base
relation `↑a⁻¹ + ↑b⁻¹ = 2` of `sBGConj_mul_sBGConj` holds), and `↑b⁻¹` again lies in
`E`. -/
theorem exists_companion_of_unitVal_inv_mem_normSetE {hyp : Hypothesis (G := G)}
    (_data : FieldNormalizerData hyp) {a : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q) :
    ∃ b : fieldNormalizerNormOneUnits hyp,
      unitVal a⁻¹ + unitVal b⁻¹ = 2 ∧
        unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hq : 0 < hyp.base.q := hyp.base.q_prime.pos
  have ha2 : (2 - unitVal a⁻¹) ∈
      OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q :=
    OddOrder.BG.AppC.NormSet.two_sub_mem_normSetE hyp.base.p hyp.base.q ha
  have hval : unitVal
      ((OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE
        hyp.base.p hyp.base.q hq ha2)⁻¹)⁻¹ = 2 - unitVal a⁻¹ := by
    rw [inv_inv]
    simp only [unitVal]
    exact OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE_coe
      hyp.base.p hyp.base.q hq ha2
  refine ⟨(OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE
      hyp.base.p hyp.base.q hq ha2)⁻¹, ?_, ?_⟩
  · rw [hval]; ring
  · rw [hval]; exact ha2

/-- **BG Appendix C, Lemma C.3 Step 4 E-membership extraction** (mmd L5090–5094):
if the `k = 3` normal form of `s · σ(inr W) · s⁻²` has central prime-line factor
`s⁻¹`, then the inverse field value `(↑W)⁻¹` lies in the norm set `E`.  This is BG's
final paragraph `v₁ = 2 - W ⟹ N(2 - W) = N(v₁) = 1 ⟹ W ∈ E`, read in the repo's
(inverse) convention so that it is `(↑W)⁻¹` that enters `E`. -/
theorem unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (W u₁ v₁ : fieldNormalizerNormOneUnits hyp)
    (hdec : data.s * data.sigma (SemidirectProduct.inr W) * data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
          data.sigma (SemidirectProduct.inr v₁)) :
    (unitVal W)⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
  have hN :
      OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q
        ((2 : GaloisField hyp.base.p hyp.base.q) * unitVal W - 1) = 1 :=
    data.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition W u₁ v₁ hdec
  have hWnorm :
      OddOrder.BG.AppC.NormSet.normN hyp.base.p hyp.base.q (unitVal W) = 1 :=
    (OddOrder.BG.AppC.NormSet.mem_normOneUnits_iff_normN hyp.base.p hyp.base.q
      hyp.base.q_prime.ne_zero (W : (GaloisField hyp.base.p hyp.base.q)ˣ)).mp W.property
  have hW0 : unitVal W ≠ 0 := unitVal_ne_zero W
  refine ⟨?_, ?_⟩
  · rw [OddOrder.BG.AppC.NormSet.normN_inv, hWnorm, inv_one]
  · have hcalc :
        (2 : GaloisField hyp.base.p hyp.base.q) - (unitVal W)⁻¹ =
          (unitVal W)⁻¹ * ((2 : GaloisField hyp.base.p hyp.base.q) * unitVal W - 1) := by
      field_simp
    rw [hcalc, OddOrder.BG.AppC.NormSet.normN_mul,
      OddOrder.BG.AppC.NormSet.normN_inv, hWnorm, inv_one, one_mul, hN]

/-- **Backward conjugation rewrite**: `(t^n)⁻¹ · σ(inr u) · t^n = σ(inr ((tConj^n)⁻¹ u))`.
This is the inverse-direction companion of
`t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow` (S16), giving BG's
right-conjugation `(u)^{t^n} = t⁻ⁿ u tⁿ` directly.  It lets the BG (C.4) connector
`q`-swap telescoping be carried out on the backward `tConj⁻³` form of `M₁`. -/
theorem t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (n : ℕ) (u : fieldNormalizerNormOneUnits hyp) :
    (data.t ^ n)⁻¹ *
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.t ^ n =
      data.sigma
        (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ n)⁻¹ u) :
          fieldNormalizerFrobeniusGroup hyp) := by
  have hself : (data.tConjNormOneUnitsAut ^ n) ((data.tConjNormOneUnitsAut ^ n)⁻¹ u) = u := by
    simp
  have h := data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow n
    ((data.tConjNormOneUnitsAut ^ n)⁻¹ u)
  rw [hself] at h
  rw [← h]; group

/-- **Backward `k = 3` first `(C.5)` decomposition** (the entry point for the
capstone proof): for any norm-one unit `a`, the backward form
`s · σ(inr ((tConj³)⁻¹ a⁻¹)) · s⁻²` (BG's `s · (a⁻¹)^{t³} · s⁻²`) admits a Step 1
normal form `σ(inr u₁) · σ(P₀ c) · σ(inr v₁)`.  BG's Lemma C.3 Step 4 pins `c = -1`;
that is the content of `Step4Capstone`. -/
theorem exists_step4_first_k_three_inv_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
      data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
  apply data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
  have hs : data.s ∈ hyp.base.P ⊔ hyp.base.U := by
    rw [← zpow_one data.s]; exact data.s_zpow_mem_P_sup_U 1
  have hmidU :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹),
      ⟨(data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹, rfl⟩, rfl⟩
  have hmid :
      data.sigma
          (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
            fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hmidU
  have hr : data.s ^ (-2 : ℤ) ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U (-2)
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hs hmid) hr

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` membership bridge in a neutral form:
any word `s^m · σ(inr w) · s^r`, with the middle term already a concrete
norm-one complement element, lies in `PU`. -/
theorem s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w : fieldNormalizerNormOneUnits hyp) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := by
  have hm : data.s ^ m ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U m
  have hmidU :
      data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr w, ⟨w, rfl⟩, rfl⟩
  have hmid :
      data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.P ⊔ hyp.base.U :=
    (le_sup_right : hyp.base.U ≤ hyp.base.P ⊔ hyp.base.U) hmidU
  have hr : data.s ^ r ∈ hyp.base.P ⊔ hyp.base.U := data.s_zpow_mem_P_sup_U r
  exact (hyp.base.P ⊔ hyp.base.U).mul_mem
    ((hyp.base.P ⊔ hyp.base.U).mul_mem hm hmid) hr

/-- Neutral Step 4 `(C.5)` decomposition bridge: every word
`s^m · σ(inr w) · s^r` admits Step 1 normal form
`σ(inr u) · σ(P₀ c) · σ(inr v)`. -/
theorem exists_step4_sigma_inr_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w : fieldNormalizerNormOneUnits hyp) :
    ∃ c : ZMod hyp.base.p, ∃ u v : fieldNormalizerNormOneUnits hyp,
      data.s ^ m *
            data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ r =
        data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp) :=
  data.exists_sigma_normOne_primeLine_normOne_of_mem_PU
    (data.s_zpow_mul_sigma_inr_mul_s_zpow_mem_P_sup_U m r w)

/-- BG Appendix C, Lemma C.3 Step 4 "mod `P`" bridge in a neutral form: if a
word `s^m · σ(inr w) · s^r` is written in Step 1 normal form `u₁ s₁ v₁`, then the
right component is `w = u₁ v₁`.  This is the reusable right-projection step behind
both the forward and backward `k = 3` `(C.5)` equations. -/
theorem right_component_of_step4_sigma_inr_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w u₁ v₁ : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    w = u₁ * v₁ := by
  have hmP : data.s ^ m ∈ hyp.base.P := data.s_zpow_mem_P m
  rw [← data.sigma_P_eq_P] at hmP
  rcases hmP with ⟨pm, hpmP, hpm⟩
  have hrP : data.s ^ r ∈ hyp.base.P := data.s_zpow_mem_P r
  rw [← data.sigma_P_eq_P] at hrP
  rcases hrP with ⟨pr, hprP, hpr⟩
  have hpm_right : SemidirectProduct.rightHom pm = 1 := by
    rcases hpmP with ⟨x, rfl⟩
    simp
  have hpr_right : SemidirectProduct.rightHom pr = 1 := by
    rcases hprP with ⟨x, rfl⟩
    simp
  have hline_right :
      SemidirectProduct.rightHom (fieldNormalizerPrimeLineElement hyp c) = 1 := by
    simp [fieldNormalizerPrimeLineElement]
  have hσ :
      data.sigma (pm * (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) * pr) =
        data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
    calc
      data.sigma (pm * (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) * pr) =
          data.s ^ m *
              data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
            data.s ^ r := by
        simp [map_mul, hpm, hpr]
      _ = data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp c) *
              data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := hdec
      _ = data.sigma
          ((SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c * SemidirectProduct.inr v₁) := by
        simp [map_mul]
  have hH := data.sigma_injective hσ
  have hright := congrArg (SemidirectProduct.rightHom :
      fieldNormalizerFrobeniusGroup hyp →* fieldNormalizerNormOneUnits hyp) hH
  simpa [map_mul, hpm_right, hpr_right, hline_right, mul_assoc] using hright

/-- BG Appendix C `(C.8)` normal-form transport in neutral form: applying the
concrete `p`-power Frobenius to a `(C.5)` equation keeps the prime-line factor
fixed and raises the three complement terms to their `p`-th powers. -/
theorem frobenius_step4_sigma_inr_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (m r : ℤ) (w u v : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s ^ m *
          data.sigma (SemidirectProduct.inr w : fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v : fieldNormalizerFrobeniusGroup hyp)) :
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
      data.sigma (SemidirectProduct.inr (u ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr (v ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  let g := fieldNormalizerPrimeLineGenerator hyp
  let W : fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inr w
  let U : fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inr u
  let V : fieldNormalizerFrobeniusGroup hyp := SemidirectProduct.inr v
  let S : fieldNormalizerFrobeniusGroup hyp := fieldNormalizerPrimeLineElement hyp c
  have hleft_sigma :
      data.sigma (g ^ m * W * g ^ r) =
        data.s ^ m * data.sigma W * data.s ^ r := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    rfl
  have hright_sigma :
      data.sigma (U * S * V) = data.sigma U * data.sigma S * data.sigma V := by
    rw [map_mul, map_mul]
  have hH : g ^ m * W * g ^ r = U * S * V := by
    apply data.sigma_injective
    calc
      data.sigma (g ^ m * W * g ^ r) =
          data.s ^ m * data.sigma W * data.s ^ r := hleft_sigma
      _ = data.sigma U * data.sigma S * data.sigma V := hdec
      _ = data.sigma (U * S * V) := hright_sigma.symm
  have hpowH := congrArg (fieldNormalizerFrobeniusHom hyp) hH
  have hpowH' :
      g ^ m * (SemidirectProduct.inr (w ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
          g ^ r =
        (SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
          fieldNormalizerPrimeLineElement hyp c *
            (SemidirectProduct.inr (v ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) := by
    simpa [W, U, V, S, g, map_mul, map_pow,
      fieldNormalizerFrobeniusHom_primeLineGenerator,
      fieldNormalizerFrobeniusHom_inr,
      fieldNormalizerFrobeniusHom_primeLineElement] using hpowH
  have hleft_pow_sigma :
      data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
              g ^ r) =
        data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) *
            data.s ^ r := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    rfl
  have hright_pow_sigma :
      data.sigma
          ((SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c *
              (SemidirectProduct.inr (v ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)) =
        data.sigma (SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c) *
            data.sigma (SemidirectProduct.inr (v ^ hyp.base.p) :
              fieldNormalizerFrobeniusGroup hyp) := by
    rw [map_mul, map_mul]
  calc
    data.s ^ m *
          data.sigma (SemidirectProduct.inr (w ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ r =
        data.sigma
          (g ^ m *
            (SemidirectProduct.inr (w ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
              g ^ r) := hleft_pow_sigma.symm
    _ = data.sigma
          ((SemidirectProduct.inr (u ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp) *
            fieldNormalizerPrimeLineElement hyp c *
              (SemidirectProduct.inr (v ^ hyp.base.p) :
                fieldNormalizerFrobeniusGroup hyp)) := by
      rw [hpowH']
    _ = data.sigma (SemidirectProduct.inr (u ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr (v ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := hright_pow_sigma

/-- The `mod P` reading of the backward `k = 3` first `(C.5)` equation: BG's
middle term `(a⁻¹)^{t^3}` has complement component `u₁ * v₁`. -/
theorem right_component_of_step4_first_k_three_inv_decomposition
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a u₁ v₁ : fieldNormalizerNormOneUnits hyp) (c : ZMod hyp.base.p)
    (hdec : data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp)) :
    (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹ = u₁ * v₁ := by
  have hdec' : data.s ^ (1 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c) *
          data.sigma (SemidirectProduct.inr v₁ : fieldNormalizerFrobeniusGroup hyp) := by
    simpa using hdec
  simpa using
    data.right_component_of_step4_sigma_inr_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
      (u₁ := u₁) (v₁ := v₁) (c := c) hdec'

/-- BG Appendix C, Lemma C.3 Step 4 first `(C.5)` factor
`M₁ = s · (a⁻¹)^{t^3} · s⁻²`, in BG's backward conjugation convention. -/
noncomputable def step4M1 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) : G :=
  data.s *
      ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
    (data.s⁻¹) ^ 2

/-- BG Appendix C, Lemma C.3 Step 4 second `(C.5)` factor
`M₂ = s³ · (ab⁻¹)^{t^2} · s⁻¹`. -/
noncomputable def step4M2 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp) : G :=
  data.s ^ 3 *
      ((data.t⁻¹) ^ 2 *
        (data.sigma (SemidirectProduct.inr a) *
          (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
    data.s⁻¹

/-- BG Appendix C, Lemma C.3 Step 4 third `(C.5)` factor
`M₃ = s² · b^t · s⁻³`. -/
noncomputable def step4M3 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (b : fieldNormalizerNormOneUnits hyp) : G :=
  data.s ^ 2 *
      (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
    (data.s⁻¹) ^ 3

/-! ### BG Appendix C (C.4) connector `q`-swaps

The three connector words appearing between the conjugated factors in the BG (C.4)
relation are single `Q`-commutator swaps `qᵢ qⱼ = qⱼ qᵢ` (`qᵢ = (s⁻¹)ⁱ tⁱ ∈ Q`,
`Q` abelian).  Each rewrites a connector to a form whose `t`-powers telescope with
the neighbouring conjugates. -/

/-- BG (C.4) connector 1: `s⁻³ t² s = t⁻¹ s⁻² t³`, by commuting `(s⁻¹)³t³` and
`t⁻¹s` inside the abelian `Q`. -/
theorem connectorC4_one {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.s =
      data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3 :=
  calc
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.s
        = ((data.s⁻¹) ^ 3 * data.t ^ 3) * (data.t⁻¹ * data.s) := by group
    _ = (data.t⁻¹ * data.s) * ((data.s⁻¹) ^ 3 * data.t ^ 3) :=
          data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q 3) data.t_inv_mul_s_mem_Q
    _ = data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3 := by group

/-- BG (C.4) connector 2: `s⁻² t⁻¹ s³ = t⁻³ s t²`, by commuting `(s⁻¹)²t²` and
`(t⁻¹)³s³` inside the abelian `Q`. -/
theorem connectorC4_two {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    (data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3 =
      (data.t⁻¹) ^ 3 * data.s * data.t ^ 2 :=
  calc
    (data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3
        = ((data.s⁻¹) ^ 2 * data.t ^ 2) * ((data.t⁻¹) ^ 3 * data.s ^ 3) := by group
    _ = ((data.t⁻¹) ^ 3 * data.s ^ 3) * ((data.s⁻¹) ^ 2 * data.t ^ 2) :=
          data.Q_mul_comm (data.s_inv_pow_mul_t_pow_mem_Q 2)
            (data.t_inv_pow_mul_s_pow_mem_Q 3)
    _ = (data.t⁻¹) ^ 3 * data.s * data.t ^ 2 := by group

/-- BG (C.4) connector 3: `s⁻¹ t⁻¹ s² = t⁻² s t`, by commuting `s⁻¹t` and
`(t⁻¹)²s²` inside the abelian `Q`. -/
theorem connectorC4_three {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) :
    data.s⁻¹ * data.t⁻¹ * data.s ^ 2 =
      (data.t⁻¹) ^ 2 * data.s * data.t :=
  calc
    data.s⁻¹ * data.t⁻¹ * data.s ^ 2
        = (data.s⁻¹ * data.t) * ((data.t⁻¹) ^ 2 * data.s ^ 2) := by group
    _ = ((data.t⁻¹) ^ 2 * data.s ^ 2) * (data.s⁻¹ * data.t) :=
          data.Q_mul_comm data.s_inv_mul_t_mem_Q (data.t_inv_pow_mul_s_pow_mem_Q 2)
    _ = (data.t⁻¹) ^ 2 * data.s * data.t := by group

/-- **BG Appendix C, Lemma C.3 relation (C.4)** (mmd L4994, PDF p.150): the
backward conjugated `k = 3` relation
`s⁻³ t² M₁ t⁻¹ M₂ t⁻¹ M₃ s³ = 1`, where
`M₁ = s · (t⁻³ σ(inr a)⁻¹ t³) · s⁻²`, `M₂ = s³ · (t⁻² σ(inr (a b⁻¹)) t²) · s⁻¹`,
`M₃ = s² · (t⁻¹ σ(inr b) t) · s⁻³` are BG's `s^{k-2}(a⁻¹)^{t^k}s^{-k+1}` etc.  The
connector words between the conjugated factors `q`-swap (Connectors 1–3) and the
`t`-powers then telescope to `t⁻¹ · (C.2) · t = 1`. -/
theorem relationC4 {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 *
        (data.s *
            ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
          (data.s⁻¹) ^ 2) *
      data.t⁻¹ *
        (data.s ^ 3 *
            ((data.t⁻¹) ^ 2 *
              (data.sigma (SemidirectProduct.inr a) *
                (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
          data.s⁻¹) *
      data.t⁻¹ *
        (data.s ^ 2 *
            (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
          (data.s⁻¹) ^ 3) *
      data.s ^ 3 = 1 := by
  have hC2 := data.relationC2 a b hab
  calc
    (data.s⁻¹) ^ 3 * data.t ^ 2 *
          (data.s *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
            (data.s⁻¹) ^ 2) *
        data.t⁻¹ *
          (data.s ^ 3 *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
            data.s⁻¹) *
        data.t⁻¹ *
          (data.s ^ 2 *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) *
            (data.s⁻¹) ^ 3) *
        data.s ^ 3
        = ((data.s⁻¹) ^ 3 * data.t ^ 2 * data.s) *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
              ((data.s⁻¹) ^ 2 * data.t⁻¹ * data.s ^ 3) *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
              (data.s⁻¹ * data.t⁻¹ * data.s ^ 2) *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) := by
        group
    _ = (data.t⁻¹ * (data.s⁻¹) ^ 2 * data.t ^ 3) *
              ((data.t⁻¹) ^ 3 * (data.sigma (SemidirectProduct.inr a))⁻¹ * data.t ^ 3) *
              ((data.t⁻¹) ^ 3 * data.s * data.t ^ 2) *
              ((data.t⁻¹) ^ 2 *
                (data.sigma (SemidirectProduct.inr a) *
                  (data.sigma (SemidirectProduct.inr b))⁻¹) * data.t ^ 2) *
              ((data.t⁻¹) ^ 2 * data.s * data.t) *
              (data.t⁻¹ * data.sigma (SemidirectProduct.inr b) * data.t) := by
        rw [data.connectorC4_one, data.connectorC4_two, data.connectorC4_three]
    _ = data.t⁻¹ *
          (data.s ^ (-2 : ℤ) *
            (((data.sigma (SemidirectProduct.inr a))⁻¹ * data.s *
                data.sigma (SemidirectProduct.inr a)) *
              ((data.sigma (SemidirectProduct.inr b))⁻¹ * data.s *
                data.sigma (SemidirectProduct.inr b)))) *
          data.t := by
        group
    _ = data.t⁻¹ * 1 * data.t := by rw [hC2]
    _ = 1 := by group

/-- The first BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = (tConj^3)⁻¹ a⁻¹`. -/
theorem step4M1_eq_sigma_inr
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a : fieldNormalizerNormOneUnits hyp) :
    data.step4M1 a =
      data.s *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-2 : ℤ) := by
  unfold step4M1
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    3 a⁻¹]
  simp [map_inv]
  group

/-- The second BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = (tConj^2)⁻¹ (a b⁻¹)`. -/
theorem step4M2_eq_sigma_inr
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp) :
    data.step4M2 a b =
      data.s ^ (3 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-1 : ℤ) := by
  unfold step4M2
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv
    2 (a * b⁻¹)]
  simp [map_mul, map_inv]
  group

/-- The third BG `(C.5)` factor is the neutral `s^m σ(inr w) s^r` word with
`w = tConj⁻¹ b`. -/
theorem step4M3_eq_sigma_inr
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (b : fieldNormalizerNormOneUnits hyp) :
    data.step4M3 b =
      data.s ^ (2 : ℤ) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.s ^ (-3 : ℤ) := by
  unfold step4M3
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 b]
  group

/-- Relation `(C.4)` restated using the named BG `(C.5)` factors. -/
theorem relationC4_step4M {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * data.step4M1 a *
      data.t⁻¹ * data.step4M2 a b * data.t⁻¹ * data.step4M3 b *
        data.s ^ 3 = 1 := by
  simpa [step4M1, step4M2, step4M3] using data.relationC4 a b hab

/-- BG Appendix C, Lemma C.3 Step 4 `(C.5)` normal-form package for the three
terms appearing in the already-proved relation `(C.4)`.  The `hM*` fields state
the Step 1 normal forms of BG's named factors, and the `right*` fields record the
corresponding mod-`P` complement readings. -/
structure Step4C5NormalForms {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (a b : fieldNormalizerNormOneUnits hyp) where
  c1 : ZMod hyp.base.p
  c2 : ZMod hyp.base.p
  c3 : ZMod hyp.base.p
  u1 : fieldNormalizerNormOneUnits hyp
  v1 : fieldNormalizerNormOneUnits hyp
  u2 : fieldNormalizerNormOneUnits hyp
  v2 : fieldNormalizerNormOneUnits hyp
  u3 : fieldNormalizerNormOneUnits hyp
  v3 : fieldNormalizerNormOneUnits hyp
  hM1 :
    data.step4M1 a =
      data.sigma (SemidirectProduct.inr u1 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
          data.sigma (SemidirectProduct.inr v1 : fieldNormalizerFrobeniusGroup hyp)
  hM2 :
    data.step4M2 a b =
      data.sigma (SemidirectProduct.inr u2 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c2) *
          data.sigma (SemidirectProduct.inr v2 : fieldNormalizerFrobeniusGroup hyp)
  hM3 :
    data.step4M3 b =
      data.sigma (SemidirectProduct.inr u3 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c3) *
          data.sigma (SemidirectProduct.inr v3 : fieldNormalizerFrobeniusGroup hyp)
  right1 : (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹ = u1 * v1
  right2 : (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹) = u2 * v2
  right3 : (data.tConjNormOneUnitsAut ^ 1)⁻¹ b = u3 * v3

/-- The three BG `(C.5)` factors in relation `(C.4)` admit compatible Step 1
normal forms and mod-`P` complement readings. -/
theorem exists_step4C5NormalForms
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (a b : fieldNormalizerNormOneUnits hyp) :
    Nonempty (Step4C5NormalForms data a b) := by
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (1 : ℤ)) (r := (-2 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) with
    ⟨c1, u1, v1, h1⟩
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (3 : ℤ)) (r := (-1 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) with
    ⟨c2, u2, v2, h2⟩
  rcases data.exists_step4_sigma_inr_decomposition
      (m := (2 : ℤ)) (r := (-3 : ℤ))
      (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b) with
    ⟨c3, u3, v3, h3⟩
  exact ⟨{
    c1 := c1
    c2 := c2
    c3 := c3
    u1 := u1
    v1 := v1
    u2 := u2
    v2 := v2
    u3 := u3
    v3 := v3
    hM1 := by
      rw [data.step4M1_eq_sigma_inr]
      simpa using h1
    hM2 := by
      rw [data.step4M2_eq_sigma_inr]
      simpa using h2
    hM3 := by
      rw [data.step4M3_eq_sigma_inr]
      simpa using h3
    right1 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (1 : ℤ)) (r := (-2 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
        (u₁ := u1) (v₁ := v1) (c := c1) h1
    right2 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (3 : ℤ)) (r := (-1 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹))
        (u₁ := u2) (v₁ := v2) (c := c2) h2
    right3 :=
      data.right_component_of_step4_sigma_inr_decomposition
        (m := (2 : ℤ)) (r := (-3 : ℤ))
        (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b)
        (u₁ := u3) (v₁ := v3) (c := c3) h3
  }⟩

namespace Step4C5NormalForms

/-- The first normal-form factor `u₁ s₁ v₁` from `(C.5)`. -/
noncomputable def factor1 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) *
    data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
      data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp)

/-- The second normal-form factor `u₂ s₂ v₂` from `(C.5)`. -/
noncomputable def factor2 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp) *
    data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
      data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp)

/-- The third normal-form factor `u₃ s₃ v₃` from `(C.5)`. -/
noncomputable def factor3 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) : G :=
  data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) *
    data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
      data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp)

/-- BG Appendix C `(C.8)` applied to the first `(C.5)` normal form. -/
theorem hM1_frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.step4M1 (a ^ hyp.base.p) =
      data.sigma (SemidirectProduct.inr (forms.u1 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
          data.sigma (SemidirectProduct.inr (forms.v1 ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  have hneutral :
      data.s ^ (1 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
            data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp) := by
    have h := forms.hM1
    rw [data.step4M1_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (1 : ℤ)) (r := (-2 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)
    (u := forms.u1) (v := forms.v1) (c := forms.c1) hneutral
  rw [data.step4M1_eq_sigma_inr]
  simpa [map_pow, map_inv] using hpow

/-- BG Appendix C `(C.8)` applied to the second `(C.5)` normal form. -/
theorem hM2_frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.step4M2 (a ^ hyp.base.p) (b ^ hyp.base.p) =
      data.sigma (SemidirectProduct.inr (forms.u2 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.sigma (SemidirectProduct.inr (forms.v2 ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  have hneutral :
      data.s ^ (3 : ℤ) *
            data.sigma
              (SemidirectProduct.inr
                ((data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹)) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-1 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
            data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp) := by
    have h := forms.hM2
    rw [data.step4M2_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (3 : ℤ)) (r := (-1 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 2)⁻¹ (a * b⁻¹))
    (u := forms.u2) (v := forms.v2) (c := forms.c2) hneutral
  rw [data.step4M2_eq_sigma_inr]
  simpa [map_pow, map_mul, map_inv, mul_pow] using hpow

/-- BG Appendix C `(C.8)` applied to the third `(C.5)` normal form. -/
theorem hM3_frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.step4M3 (b ^ hyp.base.p) =
      data.sigma (SemidirectProduct.inr (forms.u3 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
          data.sigma (SemidirectProduct.inr (forms.v3 ^ hyp.base.p) :
            fieldNormalizerFrobeniusGroup hyp) := by
  have hneutral :
      data.s ^ (2 : ℤ) *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
                fieldNormalizerFrobeniusGroup hyp) *
          data.s ^ (-3 : ℤ) =
        data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
            data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp) := by
    have h := forms.hM3
    rw [data.step4M3_eq_sigma_inr] at h
    simpa using h
  have hpow := data.frobenius_step4_sigma_inr_decomposition
    (m := (2 : ℤ)) (r := (-3 : ℤ))
    (w := (data.tConjNormOneUnitsAut ^ 1)⁻¹ b)
    (u := forms.u3) (v := forms.v3) (c := forms.c3) hneutral
  rw [data.step4M3_eq_sigma_inr]
  simpa [map_pow] using hpow

/-- BG Appendix C `(C.8)` as closure of the whole `(C.5)` normal-form package
under the concrete `p`-power Frobenius. -/
noncomputable def frobenius
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    Step4C5NormalForms data (a ^ hyp.base.p) (b ^ hyp.base.p) where
  c1 := forms.c1
  c2 := forms.c2
  c3 := forms.c3
  u1 := forms.u1 ^ hyp.base.p
  v1 := forms.v1 ^ hyp.base.p
  u2 := forms.u2 ^ hyp.base.p
  v2 := forms.v2 ^ hyp.base.p
  u3 := forms.u3 ^ hyp.base.p
  v3 := forms.v3 ^ hyp.base.p
  hM1 := forms.hM1_frobenius
  hM2 := forms.hM2_frobenius
  hM3 := forms.hM3_frobenius
  right1 := by
    have h := congrArg (fun x => x ^ hyp.base.p) forms.right1
    simpa [map_pow, map_inv, mul_pow] using h
  right2 := by
    have h := congrArg (fun x => x ^ hyp.base.p) forms.right2
    simpa [map_pow, map_mul, map_inv, mul_pow] using h
  right3 := by
    have h := congrArg (fun x => x ^ hyp.base.p) forms.right3
    simpa [map_pow, mul_pow] using h

end Step4C5NormalForms

/-- Relation `(C.4)` after substituting the three `(C.5)` normal forms. -/
theorem relationC4_step4C5NormalForms
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    (data.s⁻¹) ^ 3 * data.t ^ 2 * forms.factor1 *
      data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 * data.s ^ 3 = 1 := by
  have h := data.relationC4_step4M a b hab
  rw [forms.hM1, forms.hM2, forms.hM3] at h
  simpa [Step4C5NormalForms.factor1, Step4C5NormalForms.factor2,
    Step4C5NormalForms.factor3] using h

/-- The first rearranged relation on the way to BG `(C.7)`: multiply `(C.4)` by
`s^3` on the left and `s^{-3}` on the right after substituting `(C.5)`. -/
theorem relationC7_seed
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 =
      1 := by
  have h := data.relationC4_step4C5NormalForms hab forms
  calc
    data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 * data.t⁻¹ * forms.factor3 =
        data.s ^ 3 *
          ((data.s⁻¹) ^ 3 * data.t ^ 2 * forms.factor1 * data.t⁻¹ * forms.factor2 *
            data.t⁻¹ * forms.factor3 * data.s ^ 3) * (data.s ^ 3)⁻¹ := by
      group
    _ = data.s ^ 3 * 1 * (data.s ^ 3)⁻¹ := by rw [h]
    _ = 1 := by group


namespace Step4C5NormalForms

/-- BG `w₁ = v₂^{t⁻¹} u₃` from the rearrangement leading to `(C.7)`. -/
noncomputable def w1 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    fieldNormalizerNormOneUnits hyp :=
  data.tConjNormOneUnitsAut forms.v2 * forms.u3

/-- BG `w₂ = v₃ u₁^{t⁻²}` from the rearrangement leading to `(C.7)`. -/
noncomputable def w2 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    fieldNormalizerNormOneUnits hyp :=
  forms.v3 * (data.tConjNormOneUnitsAut ^ 2) forms.u1

/-- BG `w₃ = v₁ u₂^t` from the rearrangement leading to `(C.7)`. -/
noncomputable def w3 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    fieldNormalizerNormOneUnits hyp :=
  forms.v1 * (data.tConjNormOneUnitsAut ^ 1)⁻¹ forms.u2

/-- Under `(C.8)`, the first `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w1
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w1 = forms.w1 ^ hyp.base.p := by
  simp [frobenius, w1, map_pow, mul_pow]

/-- Under `(C.8)`, the second `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w2
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w2 = forms.w2 ^ hyp.base.p := by
  simp [frobenius, w2, map_pow, mul_pow]

/-- Under `(C.8)`, the third `(C.7)` word is raised to its `p`-th power. -/
theorem frobenius_w3
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.frobenius.w3 = forms.w3 ^ hyp.base.p := by
  simp [frobenius, w3, map_pow, mul_pow]

/-- The ambient reading of `w₁`: `σ(w₁) = t σ(v₂) t⁻¹ σ(u₃)`. -/
theorem sigma_inr_w1 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) =
      data.t * data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp) *
        data.t⁻¹ *
          data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) := by
  unfold Step4C5NormalForms.w1
  simp only [map_mul]
  have hφ :
      data.sigma
          (SemidirectProduct.inr (data.tConjNormOneUnitsAut forms.v2) :
            fieldNormalizerFrobeniusGroup hyp) =
        data.t * data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp) *
          data.t⁻¹ := by
    simpa using
      (data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 1 forms.v2).symm
  rw [hφ]

/-- The ambient reading of `w₂`: `σ(w₂) = σ(v₃) t² σ(u₁) t⁻²`. -/
theorem sigma_inr_w2 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp) =
      data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp) *
        data.t ^ 2 *
          data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) *
            (data.t ^ 2)⁻¹ := by
  unfold Step4C5NormalForms.w2
  simp only [map_mul]
  rw [← data.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow 2 forms.u1]
  group

/-- The ambient reading of `w₃`: `σ(w₃) = σ(v₁) t⁻¹ σ(u₂) t`. -/
theorem sigma_inr_w3 {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp) =
      data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp) *
        data.t⁻¹ * data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp) *
          data.t := by
  unfold Step4C5NormalForms.w3
  simp only [map_mul]
  rw [← data.t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv 1 forms.u2]
  group

/-- The three BG `(C.7)` words are elements of `U`, expressed after applying `σ`. -/
theorem sigma_inr_w_mem_U {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U ∧
      data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp) ∈ hyp.base.U ∧
        data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp) ∈
          hyp.base.U := by
  constructor
  · rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w1, ⟨forms.w1, rfl⟩, rfl⟩
  constructor
  · rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w2, ⟨forms.w2, rfl⟩, rfl⟩
  · rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w3, ⟨forms.w3, rfl⟩, rfl⟩

/-- BG Appendix C `(C.6)` for the first `(C.5)` factor: its prime-line
coordinate cannot be zero.  If `c₁=0`, then the first normal form lies in `U`;
reading the same element as `s · U · s⁻²` and applying Step 2 with prime-line
coordinates `(1,-2)` gives either `1=0` or `-1=0` in `ZMod p`, both impossible. -/
theorem c1_ne_zero {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.c1 ≠ 0 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro hc1
  have hu1 :
      data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.u1, ⟨forms.u1, rfl⟩, rfl⟩
  have hv1 :
      data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.v1, ⟨forms.v1, rfl⟩, rfl⟩
  have hM1U : data.step4M1 a ∈ hyp.base.U := by
    rw [forms.hM1, hc1]
    simpa [fieldNormalizerPrimeLineElement, mul_assoc] using hyp.base.U.mul_mem hu1 hv1
  have hM1_step :
      data.sigma (fieldNormalizerPrimeLineElement hyp (1 : ZMod hyp.base.p)) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-2 : ZMod hyp.base.p)) ∈
          hyp.base.U := by
    have h := hM1U
    rw [data.step4M1_eq_sigma_inr] at h
    have hs_one :
        data.s = data.sigma (fieldNormalizerPrimeLineElement hyp (1 : ZMod hyp.base.p)) := by
      simp [s, fieldNormalizerPrimeLineElement_one]
    have hs_neg_two :
        data.s ^ (-2 : ℤ) =
          data.sigma (fieldNormalizerPrimeLineElement hyp (-2 : ZMod hyp.base.p)) := by
      simpa using data.s_zpow_eq_primeLineElement (-2 : ℤ)
    rw [hs_neg_two] at h
    rw [hs_one] at h
    simpa [mul_assoc] using h
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := (1 : ZMod hyp.base.p)) (d := (-2 : ZMod hyp.base.p))
    ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹) hM1_step
  rcases hstep with hzero | hone
  · exact one_ne_zero hzero.1
  · have hsum : (1 : ZMod hyp.base.p) + -2 = (-1 : ZMod hyp.base.p) := by
      ring
    have hneg : (-1 : ZMod hyp.base.p) = 0 := by
      simpa [hsum] using hone.2
    exact one_ne_zero (neg_eq_zero.mp hneg)

/-- BG Appendix C `(C.6)` for the third `(C.5)` factor: its prime-line
coordinate cannot be zero.  If `c₃=0`, then the third normal form lies in `U`;
reading the same element as `s² · U · s⁻³` and applying Step 2 with prime-line
coordinates `(2,-3)` gives either `2=0` or `-1=0` in `ZMod p`, both impossible. -/
theorem c3_ne_zero {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b) :
    forms.c3 ≠ 0 := by
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro hc3
  have hu3 :
      data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.u3, ⟨forms.u3, rfl⟩, rfl⟩
  have hv3 :
      data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp) ∈
        hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.v3, ⟨forms.v3, rfl⟩, rfl⟩
  have hM3U : data.step4M3 b ∈ hyp.base.U := by
    rw [forms.hM3, hc3]
    simpa [fieldNormalizerPrimeLineElement, mul_assoc] using hyp.base.U.mul_mem hu3 hv3
  have hM3_step :
      data.sigma (fieldNormalizerPrimeLineElement hyp (2 : ZMod hyp.base.p)) *
          data.sigma
            (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) :
              fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp (-3 : ZMod hyp.base.p)) ∈
          hyp.base.U := by
    have h := hM3U
    rw [data.step4M3_eq_sigma_inr] at h
    have hs_two :
        data.s ^ (2 : ℤ) =
          data.sigma (fieldNormalizerPrimeLineElement hyp (2 : ZMod hyp.base.p)) := by
      simpa using data.s_zpow_eq_primeLineElement (2 : ℤ)
    have hs_neg_three :
        data.s ^ (-3 : ℤ) =
          data.sigma (fieldNormalizerPrimeLineElement hyp (-3 : ZMod hyp.base.p)) := by
      simpa using data.s_zpow_eq_primeLineElement (-3 : ℤ)
    rw [hs_two, hs_neg_three] at h
    simpa [mul_assoc] using h
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := (2 : ZMod hyp.base.p)) (d := (-3 : ZMod hyp.base.p))
    ((data.tConjNormOneUnitsAut ^ 1)⁻¹ b) hM3_step
  rcases hstep with hzero | hone
  · exact hyp.zmod_two_ne_zero hzero.1
  · have hsum : (2 : ZMod hyp.base.p) + -3 = (-1 : ZMod hyp.base.p) := by
      ring
    have hneg : (-1 : ZMod hyp.base.p) = 0 := by
      simpa [hsum] using hone.2
    exact one_ne_zero (neg_eq_zero.mp hneg)

end Step4C5NormalForms

/-- BG Appendix C `(C.7)`, obtained by rearranging the `(C.5)` substitution relation and
absorbing the conjugated complement terms into `w₁`, `w₂`, and `w₃`. -/
theorem relationC7
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) * data.t⁻¹ =
      (data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) *
          data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp) *
            data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
              data.sigma
                (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp))⁻¹ := by
  let U1 := data.sigma (SemidirectProduct.inr forms.u1 : fieldNormalizerFrobeniusGroup hyp)
  let V1 := data.sigma (SemidirectProduct.inr forms.v1 : fieldNormalizerFrobeniusGroup hyp)
  let U2 := data.sigma (SemidirectProduct.inr forms.u2 : fieldNormalizerFrobeniusGroup hyp)
  let V2 := data.sigma (SemidirectProduct.inr forms.v2 : fieldNormalizerFrobeniusGroup hyp)
  let U3 := data.sigma (SemidirectProduct.inr forms.u3 : fieldNormalizerFrobeniusGroup hyp)
  let V3 := data.sigma (SemidirectProduct.inr forms.v3 : fieldNormalizerFrobeniusGroup hyp)
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp)
  have hseed :
      data.t ^ 2 * U1 * S1 * V1 * data.t⁻¹ * U2 * S2 * V2 * data.t⁻¹ * U3 * S3 * V3 =
        1 := by
    have h := data.relationC7_seed hab forms
    simpa [Step4C5NormalForms.factor1, Step4C5NormalForms.factor2,
      Step4C5NormalForms.factor3, U1, V1, U2, V2, U3, V3, S1, S2, S3, mul_assoc]
      using h
  have hw1_t : data.t⁻¹ * W1 = V2 * data.t⁻¹ * U3 := by
    dsimp [W1, V2, U3]
    rw [forms.sigma_inr_w1]
    group
  have hw2_t : W2 * data.t ^ 2 = V3 * data.t ^ 2 * U1 := by
    dsimp [W2, V3, U1]
    rw [forms.sigma_inr_w2]
    group
  have hw3_t : W3 * data.t⁻¹ = V1 * data.t⁻¹ * U2 := by
    dsimp [W3, V1, U2]
    rw [forms.sigma_inr_w3]
    group
  have hword :
      data.t ^ 2 * U1 * S1 * W3 * (data.t⁻¹ * S2 * data.t⁻¹) * W1 * S3 * V3 =
        1 := by
    calc
      data.t ^ 2 * U1 * S1 * W3 * (data.t⁻¹ * S2 * data.t⁻¹) * W1 * S3 * V3 =
          data.t ^ 2 * U1 * S1 * (W3 * data.t⁻¹) * S2 *
            (data.t⁻¹ * W1) * S3 * V3 := by
        group
      _ = data.t ^ 2 * U1 * S1 * (V1 * data.t⁻¹ * U2) * S2 *
            (V2 * data.t⁻¹ * U3) * S3 * V3 := by
        rw [hw3_t, hw1_t]
      _ = data.t ^ 2 * U1 * S1 * V1 * data.t⁻¹ * U2 * S2 * V2 * data.t⁻¹ * U3 * S3 * V3 := by
        group
      _ = 1 := hseed
  have hwordPrime :
      (data.t ^ 2 * U1 * S1 * W3) * (data.t⁻¹ * S2 * data.t⁻¹) *
          (W1 * S3 * V3) = 1 := by
    simpa [mul_assoc] using hword
  have hmain : data.t⁻¹ * S2 * data.t⁻¹ =
      (W1 * S3 * W2 * data.t ^ 2 * S1 * W3)⁻¹ := by
    calc
      data.t⁻¹ * S2 * data.t⁻¹ =
          (data.t ^ 2 * U1 * S1 * W3)⁻¹ *
            ((data.t ^ 2 * U1 * S1 * W3) * (data.t⁻¹ * S2 * data.t⁻¹) *
              (W1 * S3 * V3)) * (W1 * S3 * V3)⁻¹ := by
        group
      _ = (data.t ^ 2 * U1 * S1 * W3)⁻¹ * 1 * (W1 * S3 * V3)⁻¹ := by
        rw [hwordPrime]
      _ = ((W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3))⁻¹ := by
        group
      _ = (W1 * S3 * W2 * data.t ^ 2 * S1 * W3)⁻¹ := by
        have hD : W1 * S3 * W2 * data.t ^ 2 * S1 * W3 =
            (W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3) := by
          calc
            W1 * S3 * W2 * data.t ^ 2 * S1 * W3 =
                W1 * S3 * (W2 * data.t ^ 2) * S1 * W3 := by
              group
            _ = W1 * S3 * (V3 * data.t ^ 2 * U1) * S1 * W3 := by
              rw [hw2_t]
            _ = (W1 * S3 * V3) * (data.t ^ 2 * U1 * S1 * W3) := by
              group
        rw [← hD]
  simpa [S1, S2, S3, W1, W2, W3, mul_assoc] using hmain


/-- BG Appendix C `(C.8)` Frobenius entry: if the inverse field values of `a` and
`b` lie in `E` and satisfy the companion equation, then the inverse field values of
`a^p` and `b^p` again lie in `E` and satisfy the same companion equation. -/
theorem unitVal_inv_frobenius_pair
    {hyp : Hypothesis (G := G)} {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2) :
    unitVal (a ^ hyp.base.p)⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q ∧
      unitVal (b ^ hyp.base.p)⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q ∧
        unitVal (a ^ hyp.base.p)⁻¹ + unitVal (b ^ hyp.base.p)⁻¹ = 2 := by
  have hpair := OddOrder.BG.AppC.NormSet.normSetE_frobenius_pair
    hyp.base.p hyp.base.q hyp.base.q_prime.ne_zero ha hb hab
  simpa [unitVal, map_pow] using hpair

/-- BG Appendix C `(C.9)` for the third word: comparing `(C.7)` for `(a,b)`
with `(C.7)` for `(a^p,b^p)` shows that
`S₁ W₃^(p-1) S₁⁻¹` lies in `PU` and its `t²`-conjugate also lies in `PU`. -/
theorem relationC9_w3_mem_P_sup_U_and_conj
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
        fieldNormalizerFrobeniusGroup hyp)
    S1 * W3pow * S1⁻¹ ∈ hyp.base.P ⊔ hyp.base.U ∧
      data.t ^ 2 * (S1 * W3pow * S1⁻¹) * (data.t ^ 2)⁻¹ ∈
        hyp.base.P ⊔ hyp.base.U := by
  classical
  dsimp only
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3p := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let A := W1 * S3 * W2
  let Ap := W1p * S3 * W2p
  let X := S1 * W3pow * S1⁻¹
  have hpow_pair := unitVal_inv_frobenius_pair ha hb hab
  have hC7 := data.relationC7 hab forms
  have hC7p := data.relationC7 hpow_pair.2.2 forms.frobenius
  have hC7' :
      data.t⁻¹ * S2 * data.t⁻¹ = (A * data.t ^ 2 * S1 * W3)⁻¹ := by
    simpa [A, S1, S2, S3, W1, W2, W3, mul_assoc] using hC7
  have hC7p' :
      data.t⁻¹ * S2 * data.t⁻¹ = (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := by
    have hC7p0 := hC7p
    rw [forms.frobenius_w1, forms.frobenius_w2, forms.frobenius_w3] at hC7p0
    simpa [Ap, S1, S2, S3, W1p, W2p, W3p,
      Step4C5NormalForms.frobenius, mul_assoc] using hC7p0
  have hword : A * data.t ^ 2 * S1 * W3 = Ap * data.t ^ 2 * S1 * W3p := by
    have hinv : (A * data.t ^ 2 * S1 * W3)⁻¹ =
        (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := hC7'.symm.trans hC7p'
    exact inv_inj.mp hinv
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hp_eq : hyp.base.p = hyp.base.p - 1 + 1 :=
    (Nat.succ_pred_eq_of_pos hp_pos).symm
  have hW3_pow_mul_inv : W3 ^ hyp.base.p * W3⁻¹ = W3 ^ (hyp.base.p - 1) := by
    conv_lhs =>
      lhs
      rw [hp_eq]
    rw [pow_succ]
    group
  have hW3p_eq : W3p = W3 ^ hyp.base.p := by
    simp [W3p, W3, map_pow]
  have hW3pow_eq : W3pow = W3 ^ (hyp.base.p - 1) := by
    simp [W3pow, W3, map_pow]
  have hW3p_mul_inv : W3p * W3⁻¹ = W3pow := by
    calc
      W3p * W3⁻¹ = W3 ^ hyp.base.p * W3⁻¹ := by rw [hW3p_eq]
      _ = W3 ^ (hyp.base.p - 1) := hW3_pow_mul_inv
      _ = W3pow := hW3pow_eq.symm
  have hApA : Ap⁻¹ * A = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
    calc
      Ap⁻¹ * A = Ap⁻¹ * (A * data.t ^ 2 * S1 * W3) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = Ap⁻¹ * (Ap * data.t ^ 2 * S1 * W3p) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        rw [hword]
      _ = data.t ^ 2 * S1 * (W3p * W3⁻¹) * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = data.t ^ 2 * S1 * W3pow * S1⁻¹ * (data.t ^ 2)⁻¹ := by
        rw [hW3p_mul_inv]
      _ = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
        simp [X]
        group
  have hA_mem : A ∈ PU := by
    change A ∈ hyp.base.P ⊔ hyp.base.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨(SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp forms.c3 * SemidirectProduct.inr forms.w2,
      trivial, ?_⟩
    simp [A, W1, W2, S3, map_mul]
  have hAp_mem : Ap ∈ PU := by
    change Ap ∈ hyp.base.P ⊔ hyp.base.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨(SemidirectProduct.inr (forms.w1 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) *
        fieldNormalizerPrimeLineElement hyp forms.c3 *
          SemidirectProduct.inr (forms.w2 ^ hyp.base.p), trivial, ?_⟩
    simp [Ap, W1p, W2p, S3, map_mul]
  have hX_mem : X ∈ PU := by
    change X ∈ hyp.base.P ⊔ hyp.base.U
    rw [data.P_sup_U_eq_sigma_top]
    refine ⟨fieldNormalizerPrimeLineElement hyp forms.c1 *
        (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
          fieldNormalizerFrobeniusGroup hyp) *
          (fieldNormalizerPrimeLineElement hyp forms.c1)⁻¹, trivial, ?_⟩
    simp [X, S1, W3pow, map_mul, map_inv]
  have hconj_mem : data.t ^ 2 * X * (data.t ^ 2)⁻¹ ∈ PU := by
    have hleft : Ap⁻¹ * A ∈ PU := PU.mul_mem (PU.inv_mem hAp_mem) hA_mem
    rwa [hApA] at hleft
  exact ⟨by simpa [PU, X, S1, W3pow] using hX_mem,
    by simpa [PU, X, S1, W3pow] using hconj_mem⟩


/-- BG Appendix C exact `(C.9)` word equation.  This is the equality displayed
just before `(C.9)`: after comparing `(C.7)` for `(a,b)` with the Frobenius-powered
`(C.7)`, the remaining `w₁/w₂` word is a `t²`-conjugate of
`S₁ W₃^(p-1) S₁⁻¹`. -/
theorem relationC9_w3_word
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
    let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
    let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
    let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
    let W1p := data.sigma
      (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
    let W2p := data.sigma
      (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
    let W3pow := data.sigma
      (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
        fieldNormalizerFrobeniusGroup hyp)
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) * data.t ^ 2 =
      S1 * W3pow * S1⁻¹ := by
  classical
  dsimp only
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W3 := data.sigma (SemidirectProduct.inr forms.w3 : fieldNormalizerFrobeniusGroup hyp)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3p := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let A := W1 * S3 * W2
  let Ap := W1p * S3 * W2p
  let X := S1 * W3pow * S1⁻¹
  have hpow_pair := unitVal_inv_frobenius_pair ha hb hab
  have hC7 := data.relationC7 hab forms
  have hC7p := data.relationC7 hpow_pair.2.2 forms.frobenius
  have hC7' :
      data.t⁻¹ * S2 * data.t⁻¹ = (A * data.t ^ 2 * S1 * W3)⁻¹ := by
    simpa [A, S1, S2, S3, W1, W2, W3, mul_assoc] using hC7
  have hC7p' :
      data.t⁻¹ * S2 * data.t⁻¹ = (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := by
    have hC7p0 := hC7p
    rw [forms.frobenius_w1, forms.frobenius_w2, forms.frobenius_w3] at hC7p0
    simpa [Ap, S1, S2, S3, W1p, W2p, W3p,
      Step4C5NormalForms.frobenius, mul_assoc] using hC7p0
  have hword : A * data.t ^ 2 * S1 * W3 = Ap * data.t ^ 2 * S1 * W3p := by
    have hinv : (A * data.t ^ 2 * S1 * W3)⁻¹ =
        (Ap * data.t ^ 2 * S1 * W3p)⁻¹ := hC7'.symm.trans hC7p'
    exact inv_inj.mp hinv
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hp_eq : hyp.base.p = hyp.base.p - 1 + 1 :=
    (Nat.succ_pred_eq_of_pos hp_pos).symm
  have hW3_pow_mul_inv : W3 ^ hyp.base.p * W3⁻¹ = W3 ^ (hyp.base.p - 1) := by
    conv_lhs =>
      lhs
      rw [hp_eq]
    rw [pow_succ]
    group
  have hW3p_eq : W3p = W3 ^ hyp.base.p := by
    simp [W3p, W3, map_pow]
  have hW3pow_eq : W3pow = W3 ^ (hyp.base.p - 1) := by
    simp [W3pow, W3, map_pow]
  have hW3p_mul_inv : W3p * W3⁻¹ = W3pow := by
    calc
      W3p * W3⁻¹ = W3 ^ hyp.base.p * W3⁻¹ := by rw [hW3p_eq]
      _ = W3 ^ (hyp.base.p - 1) := hW3_pow_mul_inv
      _ = W3pow := hW3pow_eq.symm
  have hApA : Ap⁻¹ * A = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
    calc
      Ap⁻¹ * A = Ap⁻¹ * (A * data.t ^ 2 * S1 * W3) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = Ap⁻¹ * (Ap * data.t ^ 2 * S1 * W3p) * W3⁻¹ * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        rw [hword]
      _ = data.t ^ 2 * S1 * (W3p * W3⁻¹) * S1⁻¹ *
          (data.t ^ 2)⁻¹ := by
        group
      _ = data.t ^ 2 * S1 * W3pow * S1⁻¹ * (data.t ^ 2)⁻¹ := by
        rw [hW3p_mul_inv]
      _ = data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
        simp [X]
        group
  have hleft : W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2 = Ap⁻¹ * A := by
    simp [A, Ap]
    group
  calc
    (data.t ^ 2)⁻¹ * (W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2) *
        data.t ^ 2 =
        (data.t ^ 2)⁻¹ * (Ap⁻¹ * A) * data.t ^ 2 := by
      rw [hleft]
    _ = X := by
      rw [hApA]
      group

/-- After the third word has been killed, exact `(C.9)` and Step 2 force the
remaining two words to satisfy condition `(A)`.  The nontriviality of the third
prime-line factor is the `(C.6)` input, kept explicit here because the global
`C.6` theorem is a separate frontier. -/
theorem relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc3 : forms.c3 ≠ 0) (hw3 : forms.w3 = 1) :
    forms.w1 ^ (hyp.base.p - 1) = 1 ∧ forms.w2 ^ (hyp.base.p - 1) = 1 := by
  classical
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  let W1 := data.sigma (SemidirectProduct.inr forms.w1 : fieldNormalizerFrobeniusGroup hyp)
  let W2 := data.sigma (SemidirectProduct.inr forms.w2 : fieldNormalizerFrobeniusGroup hyp)
  let W1p := data.sigma
    (SemidirectProduct.inr (forms.w1 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W2p := data.sigma
    (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) : fieldNormalizerFrobeniusGroup hyp)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let U1 := (forms.w1 ^ hyp.base.p)⁻¹ * forms.w1
  let L := W2p⁻¹ * S3⁻¹ * W1p⁻¹ * W1 * S3 * W2
  have hC9 := data.relationC9_w3_word ha hb hab forms
  have hC9' : (data.t ^ 2)⁻¹ * L * data.t ^ 2 = S1 * W3pow * S1⁻¹ := by
    simpa [S1, S3, W1, W2, W1p, W2p, W3pow, L, mul_assoc] using hC9
  have hW3pow_one : W3pow = 1 := by
    simp [W3pow, hw3]
  have hL_one : L = 1 := by
    have hconj : (data.t ^ 2)⁻¹ * L * data.t ^ 2 = 1 := by
      simpa [hW3pow_one] using hC9'
    calc
      L = data.t ^ 2 * ((data.t ^ 2)⁻¹ * L * data.t ^ 2) * (data.t ^ 2)⁻¹ := by
        group
      _ = 1 := by
        rw [hconj]
        group
  have hU1_sigma : data.sigma (SemidirectProduct.inr U1 : fieldNormalizerFrobeniusGroup hyp) =
      W1p⁻¹ * W1 := by
    simp [U1, W1p, W1, map_mul, map_inv]
  have hS3_inv : data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c3)) = S3⁻¹ := by
    calc
      data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c3)) =
          data.sigma ((fieldNormalizerPrimeLineElement hyp forms.c3)⁻¹) := by
        rw [fieldNormalizerPrimeLineElement_neg]
      _ = S3⁻¹ := by
        simp [S3]
  have hW2p_mem : W2p ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr (forms.w2 ^ hyp.base.p),
      ⟨forms.w2 ^ hyp.base.p, rfl⟩, rfl⟩
  have hW2_mem : W2 ∈ hyp.base.U := by
    rw [← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr forms.w2, ⟨forms.w2, rfl⟩, rfl⟩
  have hW2_ratio_mem : W2p * W2⁻¹ ∈ hyp.base.U :=
    hyp.base.U.mul_mem hW2p_mem (hyp.base.U.inv_mem hW2_mem)
  have hL' : W2p⁻¹ * (S3⁻¹ * W1p⁻¹ * W1 * S3) * W2 = 1 := by
    simpa [L, mul_assoc] using hL_one
  have hmid_eq : S3⁻¹ * W1p⁻¹ * W1 * S3 = W2p * W2⁻¹ := by
    calc
      S3⁻¹ * W1p⁻¹ * W1 * S3 =
          W2p * (W2p⁻¹ * (S3⁻¹ * W1p⁻¹ * W1 * S3) * W2) * W2⁻¹ := by
        group
      _ = W2p * 1 * W2⁻¹ := by
        rw [hL']
      _ = W2p * W2⁻¹ := by
        group
  have hmid_mem : S3⁻¹ * W1p⁻¹ * W1 * S3 ∈ hyp.base.U := by
    rw [hmid_eq]
    exact hW2_ratio_mem
  have hmem_step : data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c3)) *
        data.sigma (SemidirectProduct.inr U1 : fieldNormalizerFrobeniusGroup hyp) *
          data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) ∈ hyp.base.U := by
    simpa [hS3_inv, hU1_sigma, S3, mul_assoc] using hmid_mem
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := -forms.c3) (d := forms.c3) U1 hmem_step
  have hU1_one : U1 = 1 := by
    rcases hstep with hzero | hone
    · have hc3_zero : forms.c3 = 0 := by
        simpa using (neg_eq_zero.mp hzero.1)
      exact False.elim (hc3 hc3_zero)
    · exact hone.1
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hU1_one' : (forms.w1 ^ hyp.base.p)⁻¹ * forms.w1 = 1 := by
    simpa [U1] using hU1_one
  have hw1p_eq : forms.w1 ^ hyp.base.p = forms.w1 := by
    calc
      forms.w1 ^ hyp.base.p = forms.w1 ^ hyp.base.p * 1 := by simp
      _ = forms.w1 ^ hyp.base.p * ((forms.w1 ^ hyp.base.p)⁻¹ * forms.w1) := by
        rw [hU1_one']
      _ = forms.w1 := by
        group
  have hw1 : forms.w1 ^ (hyp.base.p - 1) = 1 := by
    have hpow : forms.w1 ^ (hyp.base.p - 1) * forms.w1 = forms.w1 ^ hyp.base.p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hp_pos)]
    calc
      forms.w1 ^ (hyp.base.p - 1) =
          (forms.w1 ^ (hyp.base.p - 1) * forms.w1) * forms.w1⁻¹ := by
        group
      _ = forms.w1 ^ hyp.base.p * forms.w1⁻¹ := by
        rw [hpow]
      _ = forms.w1 * forms.w1⁻¹ := by
        rw [hw1p_eq]
      _ = 1 := by
        group
  have hW1_ratio_one : W1p⁻¹ * W1 = 1 := by
    rw [← hU1_sigma, hU1_one]
    simp
  have hW2_ratio_one : W2p⁻¹ * W2 = 1 := by
    calc
      W2p⁻¹ * W2 = W2p⁻¹ * S3⁻¹ * (W1p⁻¹ * W1) * S3 * W2 := by
        rw [hW1_ratio_one]
        group
      _ = 1 := by
        simpa [L, mul_assoc] using hL_one
  have hW2p_eq : W2p = W2 := by
    calc
      W2p = W2p * 1 := by simp
      _ = W2p * (W2p⁻¹ * W2) := by
        rw [hW2_ratio_one]
      _ = W2 := by
        group
  have hw2p_eq : forms.w2 ^ hyp.base.p = forms.w2 := by
    have hinr : (SemidirectProduct.inr (forms.w2 ^ hyp.base.p) :
          fieldNormalizerFrobeniusGroup hyp) = SemidirectProduct.inr forms.w2 :=
      data.sigma_injective (by simpa [W2p, W2] using hW2p_eq)
    exact (SemidirectProduct.inr_inj.mp hinr)
  have hw2 : forms.w2 ^ (hyp.base.p - 1) = 1 := by
    have hpow : forms.w2 ^ (hyp.base.p - 1) * forms.w2 = forms.w2 ^ hyp.base.p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hp_pos)]
    calc
      forms.w2 ^ (hyp.base.p - 1) =
          (forms.w2 ^ (hyp.base.p - 1) * forms.w2) * forms.w2⁻¹ := by
        group
      _ = forms.w2 ^ hyp.base.p * forms.w2⁻¹ := by
        rw [hpow]
      _ = forms.w2 * forms.w2⁻¹ := by
        rw [hw2p_eq]
      _ = 1 := by
        group
  exact ⟨hw1, hw2⟩


/-- BG Appendix C condition `(A)` in S16 form: a norm-one unit with
`(p - 1)`-st power equal to `1` is trivial. -/
theorem normOneUnit_eq_one_of_pow_sub_one_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (u : fieldNormalizerNormOneUnits hyp) (hu : u ^ (hyp.base.p - 1) = 1) :
    u = 1 :=
  OddOrder.BG.AppC.NormSet.normOneUnits_eq_one_of_pow_sub_one_eq_one
    hyp.base.p hyp.base.q hyp.base.q_prime data.cyclotomic_coprime u hu

namespace Step4C5NormalForms

/-- The post-`(C.9)` condition `(A)` step for the three BG words. -/
theorem w_eq_one_of_pow_sub_one_eq_one
    {hyp : Hypothesis (G := G)} {data : FieldNormalizerData hyp}
    {a b : fieldNormalizerNormOneUnits hyp} (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 ^ (hyp.base.p - 1) = 1)
    (hw2 : forms.w2 ^ (hyp.base.p - 1) = 1)
    (hw3 : forms.w3 ^ (hyp.base.p - 1) = 1) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 :=
  ⟨data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w1 hw1,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w2 hw2,
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w3 hw3⟩

end Step4C5NormalForms


/-- BG Appendix C `(C.10)`: once `(C.9)` and condition `(A)` have forced
`w₁ = w₂ = w₃ = 1`, relation `(C.7)` collapses to
`t² s₁ t⁻¹ s₂ t⁻¹ s₃ = 1`. -/
theorem relationC10_of_w_eq_one
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hw1 : forms.w1 = 1) (hw2 : forms.w2 = 1) (hw3 : forms.w3 = 1) :
    data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let S2 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2)
  let S3 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3)
  have hC7 := data.relationC7 hab forms
  rw [hw1, hw2, hw3] at hC7
  simp only [map_one, one_mul, mul_one] at hC7
  calc
    data.t ^ 2 * S1 * data.t⁻¹ * S2 * data.t⁻¹ * S3 =
        data.t ^ 2 * S1 * (data.t⁻¹ * S2 * data.t⁻¹) * S3 := by
      group
    _ = data.t ^ 2 * S1 * (S3 * data.t ^ 2 * S1)⁻¹ * S3 := by
      rw [hC7]
    _ = 1 := by group

/-- BG Appendix C Step 4 after Step 3: once Step 3 supplies the membership
`s₁ w₃^(p-1) s₁⁻¹ ∈ U`, Step 2 and condition `(A)` force
`w₁ = w₂ = w₃ = 1`, and hence `(C.10)`.

The two nonzero hypotheses are the `(C.6)` inputs for the first and third
prime-line factors.  The remaining frontier is to produce the displayed
`U`-membership from the Step 3 intersection theorem. -/
theorem relationC9_w_eq_one_and_relationC10_of_w3_step3_mem_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hw3U :
      data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
          data.sigma
            (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
              fieldNormalizerFrobeniusGroup hyp) *
            (data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1))⁻¹ ∈ hyp.base.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  classical
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let U3 := forms.w3 ^ (hyp.base.p - 1)
  have hS1_inv :
      data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c1)) = S1⁻¹ := by
    calc
      data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c1)) =
          data.sigma ((fieldNormalizerPrimeLineElement hyp forms.c1)⁻¹) := by
        rw [fieldNormalizerPrimeLineElement_neg]
      _ = S1⁻¹ := by
        simp [S1]
  have hU3_sigma :
      data.sigma (SemidirectProduct.inr U3 : fieldNormalizerFrobeniusGroup hyp) =
        W3pow := by
    simp [U3, W3pow]
  have hmem_step :
      data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
          data.sigma (SemidirectProduct.inr U3 : fieldNormalizerFrobeniusGroup hyp) *
            data.sigma (fieldNormalizerPrimeLineElement hyp (-forms.c1)) ∈ hyp.base.U := by
    simpa [S1, W3pow, U3, hS1_inv, hU3_sigma, mul_assoc] using hw3U
  have hstep := data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := forms.c1) (d := -forms.c1) U3 hmem_step
  have hU3_one : U3 = 1 := by
    rcases hstep with hzero | hone
    · exact False.elim (hc1 hzero.1)
    · exact hone.1
  have hw3_pow : forms.w3 ^ (hyp.base.p - 1) = 1 := by
    simpa [U3] using hU3_one
  have hw3 : forms.w3 = 1 :=
    data.normOneUnit_eq_one_of_pow_sub_one_eq_one forms.w3 hw3_pow
  have h12 :=
    data.relationC9_w1_w2_pow_sub_one_eq_one_of_w3_eq_one ha hb hab forms hc3 hw3
  have hwords := forms.w_eq_one_of_pow_sub_one_eq_one h12.1 h12.2 hw3_pow
  have hC10 := data.relationC10_of_w_eq_one hab forms hwords.1 hwords.2.1 hwords.2.2
  exact ⟨hwords.1, hwords.2.1, hwords.2.2, hC10⟩

/-- BG Appendix C Step 4, Step 3 producer in the `U` branch: the concrete `(C.9)`
membership places `S₁ W₃^(p-1) S₁⁻¹` in `PU` and, after applying the inverse Lean
conjugation convention, in `(PU)^{t^{-2}}`.  If Step 3 identifies that
intersection with `U`, the already-landed `(C.9)` collapse gives `w₁=w₂=w₃=1`
and hence `(C.10)`.

This theorem isolates the remaining Step 3 obstruction: after this point the only
missing part of the producer is ruling out the alternative intersection `PU`. -/
theorem relationC9_w_eq_one_and_relationC10_of_w3_step3_inf_eq_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0)
    (hstep3 :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.U) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  classical
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  let S1 := data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1)
  let W3pow := data.sigma
    (SemidirectProduct.inr (forms.w3 ^ (hyp.base.p - 1)) :
      fieldNormalizerFrobeniusGroup hyp)
  let X := S1 * W3pow * S1⁻¹
  have hC9 := data.relationC9_w3_mem_P_sup_U_and_conj ha hb hab forms
  have hX_PU : X ∈ PU := by
    simpa [PU, X, S1, W3pow] using hC9.1
  have hX_conj_PU : data.t ^ 2 * X * (data.t ^ 2)⁻¹ ∈ PU := by
    simpa [PU, X, S1, W3pow] using hC9.2
  have hX_smul : X ∈ MulAut.conj ((data.t ^ 2)⁻¹) • PU := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hsmul : ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • X) =
        data.t ^ 2 * X * (data.t ^ 2)⁻¹ := by
      rw [show ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • X) =
          (MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ X from rfl,
        MulAut.conj_inv_apply]
      group
    rwa [hsmul]
  have hX_inf : X ∈ PU ⊓ (MulAut.conj ((data.t ^ 2)⁻¹) • PU) := ⟨hX_PU, hX_smul⟩
  have hX_U : X ∈ hyp.base.U := by
    have hX_inf' : X ∈ (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) := by
      simpa [PU] using hX_inf
    rwa [hstep3] at hX_inf'
  exact data.relationC9_w_eq_one_and_relationC10_of_w3_step3_mem_U
    ha hb hab forms hc1 hc3 (by simpa [X, S1, W3pow] using hX_U)

/-- BG Appendix C Step 4 after applying Step 3 to the `(C.9)` element: either
`(C.10)` has already been forced, or the only remaining Step 3 obstruction is
the bad branch where the relevant intersection is all of `PU`. -/
theorem relationC9_w_eq_one_and_relationC10_or_step3_inf_eq_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0) :
    (forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1) ∨
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U := by
  classical
  have ht2_norm : data.t ^ 2 ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
    data.t_pow_normalizes_U 2
  have ht2_inv_norm : (data.t ^ 2)⁻¹ ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
    (Subgroup.normalizer (hyp.base.U : Set G)).inv_mem ht2_norm
  have hstep3 := data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U ht2_inv_norm
  rcases hstep3 with hU | hPU
  · left
    exact data.relationC9_w_eq_one_and_relationC10_of_w3_step3_inf_eq_U
      ha hb hab forms hc1 hc3 hU
  · right
    exact hPU

/-- BG Appendix C Step 3 bad branch, first concrete consequence: if the relevant
intersection is all of `PU`, then conjugation by `t²` sends every element of
`PU` back into `PU`.

The following bad-branch lemmas upgrade this inclusion first to `t² ∈ N_G(PU)`
and then, via `P char PU`, to `t² ∈ N_G(P)`.  The remaining Step 3 work is to
pass from `t²` to `P₁ ≤ N_G(P)` and then derive the `P₀=P₁` contradiction. -/
theorem step3_badBranch_t_sq_conj_mem_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    ∀ ⦃x : G⦄, x ∈ hyp.base.P ⊔ hyp.base.U →
      data.t ^ 2 * x * (data.t ^ 2)⁻¹ ∈ hyp.base.P ⊔ hyp.base.U := by
  classical
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  intro x hx
  have hx_inf : x ∈ PU ⊓ (MulAut.conj ((data.t ^ 2)⁻¹) • PU) := by
    rw [hbad]
    simpa [PU] using hx
  have hx_smul : x ∈ MulAut.conj ((data.t ^ 2)⁻¹) • PU := hx_inf.2
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx_smul
  have hsmul : ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • x) =
      data.t ^ 2 * x * (data.t ^ 2)⁻¹ := by
    rw [show ((MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ • x) =
        (MulAut.conj ((data.t ^ 2)⁻¹))⁻¹ x from rfl,
      MulAut.conj_inv_apply]
    group
  rw [hsmul] at hx_smul
  simpa [PU] using hx_smul

/-- BG Appendix C Step 3 bad branch: the previous one-sided inclusion upgrades to
normalization of `PU` because `t²` has finite `p`-power order.  This is the
formal version of BG's line “hence `t₁` normalizes `PU`” for the current
`t₁ = t²` branch. -/
theorem step3_badBranch_t_sq_normalizes_P_sup_U
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    data.t ^ 2 ∈ Subgroup.normalizer ((hyp.base.P ⊔ hyp.base.U : Subgroup G) : Set G) := by
  classical
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  let g : G := data.t ^ 2
  have hinc : ∀ ⦃x : G⦄, x ∈ PU → g * x * g⁻¹ ∈ PU := by
    intro x hx
    simpa [g, PU] using data.step3_badBranch_t_sq_conj_mem_P_sup_U hbad hx
  have hgpow : g ^ hyp.base.p = 1 := by
    calc
      g ^ hyp.base.p = (data.t ^ 2) ^ hyp.base.p := by rfl
      _ = data.t ^ (2 * hyp.base.p) := by rw [pow_mul]
      _ = data.t ^ (hyp.base.p * 2) := by rw [Nat.mul_comm]
      _ = (data.t ^ hyp.base.p) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [data.t_pow_p_eq_one, one_pow]
  have hiter : ∀ (n : ℕ) ⦃x : G⦄, x ∈ PU → g ^ n * x * (g ^ n)⁻¹ ∈ PU := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simpa using hx
    | succ n ih =>
        intro x hx
        have hn := ih hx
        have h := hinc hn
        simpa [pow_succ', mul_assoc] using h
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have g_inv_eq : g⁻¹ = g ^ (hyp.base.p - 1) := by
    have hmul : g ^ (hyp.base.p - 1) * g = 1 := by
      calc
        g ^ (hyp.base.p - 1) * g = g ^ ((hyp.base.p - 1) + 1) := by
          rw [pow_succ]
        _ = g ^ hyp.base.p := by
          rw [Nat.sub_one_add_one_eq_of_pos hp_pos]
        _ = 1 := hgpow
    exact inv_eq_of_mul_eq_one_left hmul
  have hinv_inc : ∀ ⦃x : G⦄, x ∈ PU → g⁻¹ * x * (g⁻¹)⁻¹ ∈ PU := by
    intro x hx
    have h := hiter (hyp.base.p - 1) hx
    simpa [g_inv_eq] using h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hinc hx
  · intro hx
    have hpre := hinv_inc (x := g * x * g⁻¹) hx
    convert hpre using 1
    group

/-- BG Appendix C Step 3 bad branch after `P char PU`: the forced normalization of
`PU` already forces `t²` to normalize the additive kernel `P`. -/
theorem step3_badBranch_t_sq_normalizes_P
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    data.t ^ 2 ∈ Subgroup.normalizer (hyp.base.P : Set G) :=
  data.normalizer_P_sup_U_le_normalizer_P
    (data.step3_badBranch_t_sq_normalizes_P_sup_U hbad)

/-- BG Appendix C Step 3 bad branch after cyclic generation: since `P₁=⟨t⟩` and
`p` is odd, the normalization of `P` by `t²` forces all of `P₁` to normalize
`P`. -/
theorem step3_badBranch_P1_le_normalizer_P
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    data.P1 ≤ Subgroup.normalizer (hyp.base.P : Set G) :=
  data.P1_le_normalizer_P_of_t_sq_mem
    (data.step3_badBranch_t_sq_normalizes_P hbad)

/-- BG Appendix C Step 3 bad branch after `P ∩ W₂Q = W₂`: the forced
normalization of `P` by `P₁`, together with `P₁ ≤ W₂Q`, forces `P₁` to normalize
`W₂ = P ∩ W₂Q`. -/
theorem step3_badBranch_P1_le_normalizer_W2
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    data.P1 ≤ Subgroup.normalizer (hyp.base.W2 : Set G) :=
  data.P1_le_normalizer_W2_of_le_normalizer_P
    (data.step3_badBranch_P1_le_normalizer_P hbad)

/-- BG Appendix C Step 3 bad branch is impossible: it forces `P₁ = W₂`, while
`P₁` normalizes `U` and `W₂` does not. -/
theorem step3_badBranch_false [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hbad :
      (hyp.base.P ⊔ hyp.base.U) ⊓
          (MulAut.conj ((data.t ^ 2)⁻¹) • (hyp.base.P ⊔ hyp.base.U)) =
        hyp.base.P ⊔ hyp.base.U) :
    False :=
  data.P1_ne_W2
    (data.P1_eq_W2_of_le_normalizer_W2
      (data.step3_badBranch_P1_le_normalizer_W2 hbad))

/-- BG Appendix C Step 4 after Step 3 and the bad-branch contradiction: with the
two `(C.6)` nonzero inputs for the first and third prime-line factors, exact
`(C.9)` no longer leaves a Step 3 alternative.  The dichotomy either gives the
`U` branch, where the existing `(C.9)` collapse forces `w₁=w₂=w₃=1` and `(C.10)`,
or gives the bad branch, now contradictory by `step3_badBranch_false`.

This is the branch-free Step 3/C.10 producer still waiting only for the global
`(C.6)` wiring that supplies `forms.c1 ≠ 0` and `forms.c3 ≠ 0`. -/
theorem relationC9_w_eq_one_and_relationC10_of_c6 [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b)
    (hc1 : forms.c1 ≠ 0) (hc3 : forms.c3 ≠ 0) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 := by
  rcases data.relationC9_w_eq_one_and_relationC10_or_step3_inf_eq_P_sup_U
      ha hb hab forms hc1 hc3 with hC10 | hbad
  · exact hC10
  · exact False.elim (data.step3_badBranch_false hbad)

/-- BG Appendix C Step 4 branch-free `(C.10)` producer: exact `(C.9)`, Step 3,
the bad-branch contradiction, and the `(C.6)` nonzero facts for `c₁` and `c₃`
together force `w₁=w₂=w₃=1` and the displayed `(C.10)` relation. -/
theorem relationC9_w_eq_one_and_relationC10 [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    {a b : fieldNormalizerNormOneUnits hyp}
    (ha : unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hb : unitVal b⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q)
    (hab : unitVal a⁻¹ + unitVal b⁻¹ = 2)
    (forms : Step4C5NormalForms data a b) :
    forms.w1 = 1 ∧ forms.w2 = 1 ∧ forms.w3 = 1 ∧
      data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp forms.c3) = 1 :=
  data.relationC9_w_eq_one_and_relationC10_of_c6
    ha hb hab forms forms.c1_ne_zero forms.c3_ne_zero


/-- **BG Appendix C, Lemma C.3 Step 4 capstone `s₁ = s⁻¹`**, as a statement: for
every norm-one unit `a` whose inverse field value `↑a⁻¹` lies in `E` (so that BG's
companion `b = 2 - ↑a⁻¹` is again a norm-one value), the `k = 3` first normal form
of `s · σ(inr ((tConj⁻³)(a⁻¹))) · s⁻²` has central prime-line factor `s⁻¹`.  This is
the remaining mathematical content; it follows from the (C.2)–(C.10) chain and the
kernel/fixed-point-free argument inside `End ⁅Q, P₀⁆`.

We use the **backward** conjugation `tConj⁻³ = (tConjNormOneUnitsAut ^ 3)⁻¹`, so that
`σ(inr ((tConj⁻³)(a⁻¹))) = t⁻³ σ(inr a⁻¹) t³` matches BG's `(a⁻¹)^{t³}` exactly (BG's
right-conjugation convention `x^{t^k} = t⁻ᵏ x tᵏ`).  This makes the BG (C.4) connector
`q`-swap telescoping (`qⱼ = s⁻ʲtʲ ∈ Q`) port directly; the downstream
`normSetE_eq_inv_of_twisted_normOne_step` is `φ`-agnostic (it only needs `φ^p = 1`,
and `((tConj^3)⁻¹)^p = 1`). -/
def Step4Capstone {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) : Prop :=
  ∀ a : fieldNormalizerNormOneUnits hyp,
    unitVal a⁻¹ ∈ OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q →
      ∃ u₁ v₁ : fieldNormalizerNormOneUnits hyp,
        data.s *
            data.sigma
              (SemidirectProduct.inr ((data.tConjNormOneUnitsAut ^ 3)⁻¹ a⁻¹)) *
          data.s ^ (-2 : ℤ) =
        data.sigma (SemidirectProduct.inr u₁) *
          data.sigma (fieldNormalizerPrimeLineElement hyp (-1 : ZMod hyp.base.p)) *
            data.sigma (SemidirectProduct.inr v₁)

/-- The Step 4 capstone yields BG's one-step twisted-inverse output for the
backward conjugation automorphism `tConj⁻³ = (tConjNormOneUnitsAut ^ 3)⁻¹`:
`a ∈ E ⟹ (a⁻¹)^{t³} ∈ E` (BG's right-conjugation).  We apply the capstone at
`a = u⁻¹` so that its hypothesis `↑(u⁻¹)⁻¹ = ↑u ∈ E` is exactly the input, and the
E-extraction `(↑W)⁻¹ ∈ E` (with `W = (tConj⁻³)(u)`) reads as `↑((tConj⁻³)(u⁻¹)) ∈ E`. -/
theorem normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp)
    (hcap : data.Step4Capstone) :
    OddOrder.BG.AppC.NormSet.normSetETwistedNormOneStep
      (p := hyp.base.p) (q := hyp.base.q) (data.tConjNormOneUnitsAut ^ 3)⁻¹ := by
  intro u hu
  have hcond : unitVal (u⁻¹)⁻¹ ∈
      OddOrder.BG.AppC.NormSet.normSetE hyp.base.p hyp.base.q := by
    rw [inv_inv]; exact hu
  obtain ⟨u₁, v₁, hdec⟩ := hcap u⁻¹ hcond
  have hext := data.unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition
    ((data.tConjNormOneUnitsAut ^ 3)⁻¹ (u⁻¹)⁻¹) u₁ v₁ hdec
  rw [inv_inv, ← unitVal_inv, ← map_inv] at hext
  rw [OddOrder.BG.AppC.NormSet.twistedInv]
  exact hext

/-- The Step 4 capstone supplies the AppC norm-one twisted-inverse output. -/
theorem appCNormSetTwistedNormOneStep_of_capstone {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (hcap : data.Step4Capstone) :
    appCNormSetTwistedNormOneStep hyp := by
  refine ⟨(data.tConjNormOneUnitsAut ^ 3)⁻¹, ?_,
    data.normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone hcap⟩
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul, data.tConjNormOneUnitsAut_pow_p_eq_one,
    one_pow, inv_one]

/-- The Step 4 capstone supplies the AppC generator relation `∀ a ∈ E, N(2a-1)=1`,
without any carrier field.  This is what `appC_normSet_generator_relation` (proved
once `step4Capstone` is available) calls. -/
theorem appC_normSet_generator_relation_of_capstone {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (hcap : data.Step4Capstone) :
    appCNormSetGeneratorRelation hyp :=
  appCNormSetGeneratorRelation_of_twisted_normOne_step hyp
    (data.appCNormSetTwistedNormOneStep_of_capstone hcap)

/-! #### BG Appendix C, Lemma C.3 Step 4: the kernel/fixed-point-free argument

This proves the capstone `s₁ = s⁻¹` from the displayed relation `(C.10)`.  Setting
`t = y⁻¹ s y` with `y ∈ ⁅Q, W₂⁆` (Remark (XI)), BG rewrites `(C.10)` modulo the
abelian group `⁅Q, P₀⁆` (= `⁅Q, W₂⁆`) as `y` lying in the kernel of
`(s⁻¹ + 1 - s₁⁻¹s⁻¹ - s₃)(s⁻¹ - 1)`.  Because `s⁻¹` operates fixed-point-freely on
`⁅Q, P₀⁆` (Remark (X)), the factor `(s⁻¹ - 1)` is injective, so `y` lies in the
kernel of `(s⁻¹ + 1 - s₁⁻¹s⁻¹ - s₃)`; unwinding gives `s₁ t₁⁻¹ t⁻¹ = t⁻¹ t₃⁻¹ s₃`
(`tᵢ = y⁻¹ sᵢ y`).  Steps 2–3 then force `t₁ = t⁻¹`, i.e. `s₁ = s⁻¹`.

We avoid building the endomorphism ring `End ⁅Q, P₀⁆`: BG's "`y ∈ ker(BC)`, `C`
injective ⟹ `y ∈ ker B`" is realised concretely as "`β(Y_B)·Y_B⁻¹ = ⋆` and `⋆ = 1`
⟹ `β(Y_B) = Y_B` ⟹ (fixed-point-free) `Y_B = 1`", where `β` is conjugation by `s`
on the abelian `⁅Q, W₂⁆` and `Y_B` the four-fold `y`-conjugate of BG's `(5074)`. -/

/-- The transported prime-line element `σ(P₀ c)` lies in `W₂`. -/
theorem sigma_primeLineElement_mem_W2 {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (c : ZMod hyp.base.p) :
    data.sigma (fieldNormalizerPrimeLineElement hyp c) ∈ hyp.base.W2 := by
  rw [← data.sigma_P0_eq_W2]
  exact Subgroup.mem_map_of_mem _ (fieldNormalizerPrimeLineElement_mem hyp c)

/-- Any two transported prime-line elements commute (the prime line `P₀` is
abelian). -/
theorem sigma_primeLineElement_commute {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (c d : ZMod hyp.base.p) :
    Commute (data.sigma (fieldNormalizerPrimeLineElement hyp c))
      (data.sigma (fieldNormalizerPrimeLineElement hyp d)) := by
  rw [Commute, SemiconjBy, sigma_primeLineElement_eq_sScalar,
    sigma_primeLineElement_eq_sScalar, sScalar_mul, sScalar_mul, add_comm]

/-- The distinguished generator `s` commutes with every transported prime-line
element. -/
theorem s_commute_sigma_primeLineElement {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (c : ZMod hyp.base.p) :
    Commute data.s (data.sigma (fieldNormalizerPrimeLineElement hyp c)) := by
  have h := data.sigma_primeLineElement_commute 1 c
  rwa [show data.sigma (fieldNormalizerPrimeLineElement hyp 1) = data.s by
    rw [fieldNormalizerPrimeLineElement_one, s, fieldNormalizerPrimeLineGenerator]] at h

/-- **BG Appendix C, Lemma C.3 Step 4: `(C.10)` modulo `Q`** (mmd L5058).  Since
`P₀ ∩ Q = 1` (`W2_inf_Q_eq_bot`) and `t ≡ s` modulo `Q`, the displayed relation
`(C.10)` collapses to `s₁ s₂ s₃ = 1`.  We conjugate `(C.10)` by `y⁻¹` (so each `t`
becomes `s`), telescope the resulting `Q`-cosets to the left, and use that
`P₀`-conjugation normalizes `Q`. -/
theorem step4_sigma_primeLine_prod_eq_one {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {c1 c2 c3 : ZMod hyp.base.p}
    (hC10 : data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp c3) = 1) :
    data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c2) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c3) = 1 := by
  set s1 := data.sigma (fieldNormalizerPrimeLineElement hyp c1) with hs1def
  set s2 := data.sigma (fieldNormalizerPrimeLineElement hyp c2) with hs2def
  set s3 := data.sigma (fieldNormalizerPrimeLineElement hyp c3) with hs3def
  -- The three prime-line factors lie in `W₂`.
  have hs1W : s1 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c1
  have hs2W : s2 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c2
  have hs3W : s3 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c3
  have hprodW : s1 * s2 * s3 ∈ hyp.base.W2 := mul_mem (mul_mem hs1W hs2W) hs3W
  -- `y⁻¹`-conjugates `σᵢ = y⁻¹ sᵢ y`, congruent to `sᵢ` modulo `Q`.
  set σ1 := data.y⁻¹ * s1 * data.y with hσ1def
  set σ2 := data.y⁻¹ * s2 * data.y with hσ2def
  set σ3 := data.y⁻¹ * s3 * data.y with hσ3def
  -- conjugating `(C.10)` by `y⁻¹` turns each `t` into `s` (since `t = y s y⁻¹`).
  have hyt2 : data.y⁻¹ * data.t ^ 2 * data.y = data.s ^ 2 := by
    rw [t, MulAut.conj_apply, pow_two, pow_two]; group
  have hyti : data.y⁻¹ * data.t⁻¹ * data.y = data.s⁻¹ := by
    rw [t, MulAut.conj_apply]; group
  have hconj : data.s ^ 2 * σ1 * data.s⁻¹ * σ2 * data.s⁻¹ * σ3 = 1 := by
    rw [← hyt2, ← hyti, hσ1def, hσ2def, hσ3def,
      show data.y⁻¹ * data.t ^ 2 * data.y * (data.y⁻¹ * s1 * data.y) *
            (data.y⁻¹ * data.t⁻¹ * data.y) * (data.y⁻¹ * s2 * data.y) *
            (data.y⁻¹ * data.t⁻¹ * data.y) * (data.y⁻¹ * s3 * data.y) =
          data.y⁻¹ * (data.t ^ 2 * s1 * data.t⁻¹ * s2 * data.t⁻¹ * s3) * data.y from by group,
      hC10, mul_one, inv_mul_cancel]
  -- each `σᵢ sᵢ⁻¹` lies in `Q`.
  have hQconj : ∀ g ∈ hyp.base.W2, ∀ x ∈ hyp.base.Q, g * x * g⁻¹ ∈ hyp.base.Q :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (data.W2_normalizes_Q hg) x).mp hx
  set q1 := σ1 * s1⁻¹ with hq1def
  set q2 := σ2 * s2⁻¹ with hq2def
  set q3 := σ3 * s3⁻¹ with hq3def
  have hq1Q : q1 ∈ hyp.base.Q := by
    rw [show q1 = data.y⁻¹ * (s1 * data.y * s1⁻¹) from by rw [hq1def, hσ1def]; group]
    exact mul_mem (inv_mem data.y_mem_Q) (hQconj s1 hs1W data.y data.y_mem_Q)
  have hq2Q : q2 ∈ hyp.base.Q := by
    rw [show q2 = data.y⁻¹ * (s2 * data.y * s2⁻¹) from by rw [hq2def, hσ2def]; group]
    exact mul_mem (inv_mem data.y_mem_Q) (hQconj s2 hs2W data.y data.y_mem_Q)
  have hq3Q : q3 ∈ hyp.base.Q := by
    rw [show q3 = data.y⁻¹ * (s3 * data.y * s3⁻¹) from by rw [hq3def, hσ3def]; group]
    exact mul_mem (inv_mem data.y_mem_Q) (hQconj s3 hs3W data.y data.y_mem_Q)
  -- `s`-power and `sᵢ` normalize `Q`.
  have hsN : data.s ∈ Subgroup.normalizer (hyp.base.Q : Set G) := data.s_normalizes_Q
  have hs1N : s1 ∈ Subgroup.normalizer (hyp.base.Q : Set G) := data.W2_normalizes_Q hs1W
  have hs2N : s2 ∈ Subgroup.normalizer (hyp.base.Q : Set G) := data.W2_normalizes_Q hs2W
  -- the telescoped `Q`-element.
  set Q1 := data.s ^ 2 * q1 * (data.s ^ 2)⁻¹ with hQ1def
  set Q2 := data.s ^ 2 * s1 * data.s⁻¹ * q2 * (data.s ^ 2 * s1 * data.s⁻¹)⁻¹ with hQ2def
  set Q3 := data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹ * q3 *
    (data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹)⁻¹ with hQ3def
  have hQ1Q : Q1 ∈ hyp.base.Q :=
    (Subgroup.mem_normalizer_iff.mp (pow_mem hsN 2) q1).mp hq1Q
  have hQ2Q : Q2 ∈ hyp.base.Q :=
    (Subgroup.mem_normalizer_iff.mp
      (mul_mem (mul_mem (pow_mem hsN 2) hs1N) (inv_mem hsN)) q2).mp hq2Q
  have hQ3Q : Q3 ∈ hyp.base.Q :=
    (Subgroup.mem_normalizer_iff.mp
      (mul_mem (mul_mem (mul_mem (mul_mem (pow_mem hsN 2) hs1N) (inv_mem hsN)) hs2N)
        (inv_mem hsN)) q3).mp hq3Q
  -- free-group telescoping identity.
  have hfactor : data.s ^ 2 * σ1 * data.s⁻¹ * σ2 * data.s⁻¹ * σ3 =
      Q1 * Q2 * Q3 * (data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹ * s3) := by
    rw [hQ1def, hQ2def, hQ3def,
      show σ1 = q1 * s1 by rw [hq1def]; group,
      show σ2 = q2 * s2 by rw [hq2def]; group,
      show σ3 = q3 * s3 by rw [hq3def]; group]
    group
  -- collapse the bare `s`-word to `s₁ s₂ s₃` using commutativity of `W₂`.
  have hcollapse : data.s ^ 2 * s1 * data.s⁻¹ * s2 * data.s⁻¹ * s3 = s1 * s2 * s3 := by
    have h1 : Commute (data.s ^ 2) s1 := (data.s_commute_sigma_primeLineElement c1).pow_left 2
    have h2 : Commute data.s s2 := data.s_commute_sigma_primeLineElement c2
    rw [h1.eq]
    rw [show s1 * data.s ^ 2 * data.s⁻¹ = s1 * data.s by group,
      show s1 * data.s * s2 = s1 * (data.s * s2) by group, h2.eq,
      show s1 * (s2 * data.s) * data.s⁻¹ = s1 * s2 by group]
  rw [hcollapse] at hfactor
  -- conclude `s₁ s₂ s₃ ∈ Q`, hence `∈ W₂ ⊓ Q = ⊥`.
  have hprodQ : s1 * s2 * s3 ∈ hyp.base.Q := by
    have hQ0 : Q1 * Q2 * Q3 ∈ hyp.base.Q := mul_mem (mul_mem hQ1Q hQ2Q) hQ3Q
    have hone : Q1 * Q2 * Q3 * (s1 * s2 * s3) = 1 := by rw [← hfactor, hconj]
    have hmem : (Q1 * Q2 * Q3)⁻¹ ∈ hyp.base.Q := inv_mem hQ0
    rwa [inv_eq_of_mul_eq_one_right hone] at hmem
  have : s1 * s2 * s3 ∈ hyp.base.W2 ⊓ hyp.base.Q := ⟨hprodW, hprodQ⟩
  rw [data.W2_inf_Q_eq_bot] at this
  simpa using this

/-- A fixed point of an automorphism is fixed by every integer power of it. -/
theorem zpow_apply_fixed {M : Type*} [Group M] (f : MulAut M) {z : M} (hf : f z = z)
    (m : ℤ) : (f ^ m) z = z := by
  have hfinv : (f⁻¹) z = z := by
    have h1 : (f⁻¹ * f) z = z := by rw [inv_mul_cancel]; rfl
    rwa [MulAut.mul_apply, hf] at h1
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, MulAut.mul_apply, hf, ih]
  | pred k ih => rw [zpow_sub_one, MulAut.mul_apply, hfinv, ih]

/-- **BG Appendix C, Remark (X), `s`-only form**: if `x ∈ ⁅Q, W₂⁆` is fixed by
conjugation by the single generator `s`, then `x = 1`.  Since `W₂ = ⟨s⟩`, being
`s`-fixed is being `W₂`-fixed, and `(X)` (`C_Q(W₂) ∩ ⁅Q,W₂⁆ = 1`) applies. -/
theorem w2ConjQAut_eq_one_of_mem_actionCommutator_of_s_fixed [Finite G]
    {hyp : Hypothesis (G := G)} (data : FieldNormalizerData hyp) {x : ↥hyp.base.Q}
    (hx : x ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut)
    (hsfix : data.w2ConjQAut ⟨data.s, data.s_mem_W2⟩ x = x) :
    x = 1 := by
  apply data.w2ConjQAut_eq_one_of_mem_actionCommutator_of_fixed hx
  intro w
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (⟨data.s, data.s_mem_W2⟩ : ↥hyp.base.W2) ^ n = w := by
    have hwz : (w : G) ∈ Subgroup.zpowers data.s := by
      rw [← data.W2_eq_zpowers_s]; exact w.2
    obtain ⟨n, hn⟩ := hwz
    exact ⟨n, Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hn)⟩
  rw [← hn, map_zpow]
  exact zpow_apply_fixed _ hsfix n

/-- **BG Appendix C, Lemma C.3 Step 4 kernel identity** (mmd L5060–5076): from the
displayed relation `(C.10)`, BG's `y ∈ ⁅Q, W₂⁆` lies in the kernel of
`(s⁻¹ + 1 - s₁⁻¹s⁻¹ - s₃)(s⁻¹ - 1)`; the fixed-point-free action of `s` (Remark (X))
removes the factor `(s⁻¹ - 1)`, leaving `Y_B = 1`, i.e. `s₁ t₁⁻¹ t⁻¹ = t⁻¹ t₃⁻¹ s₃`
where `tᵢ = y⁻¹ sᵢ y`.  We produce this relation with the explicit conjugator `yc`. -/
theorem step4_relation_5076 [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {c1 c2 c3 : ZMod hyp.base.p}
    (hC10 : data.t ^ 2 * data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
        data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp c2) *
          data.t⁻¹ * data.sigma (fieldNormalizerPrimeLineElement hyp c3) = 1) :
    ∃ yc : G, data.t = yc⁻¹ * data.s * yc ∧
      data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
          (yc⁻¹ * (data.sigma (fieldNormalizerPrimeLineElement hyp c1))⁻¹ * yc) * data.t⁻¹ =
        data.t⁻¹ * (yc⁻¹ * (data.sigma (fieldNormalizerPrimeLineElement hyp c3))⁻¹ * yc) *
          data.sigma (fieldNormalizerPrimeLineElement hyp c3) := by
  classical
  letI : CommGroup ↥hyp.base.Q :=
    { (inferInstance : Group ↥hyp.base.Q) with
      mul_comm := data.Q_elementaryAbelian.comm }
  set s1 := data.sigma (fieldNormalizerPrimeLineElement hyp c1) with hs1def
  set s2 := data.sigma (fieldNormalizerPrimeLineElement hyp c2) with hs2def
  set s3 := data.sigma (fieldNormalizerPrimeLineElement hyp c3) with hs3def
  have hs1W : s1 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c1
  have hs3W : s3 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c3
  -- `s₁ s₂ s₃ = 1` (mod-Q collapse), hence `s₂ = s₁⁻¹ s₃⁻¹`.
  have hs123 : s1 * s2 * s3 = 1 := data.step4_sigma_primeLine_prod_eq_one hC10
  have h12 : s1 * s2 = s3⁻¹ := eq_inv_of_mul_eq_one_left hs123
  have hs2eq : s2 = s1⁻¹ * s3⁻¹ := by rw [← h12]; group
  -- Remark (XI): a conjugator `yc = yD⁻¹ ∈ ⁅Q, W₂⁆` with `t = yc⁻¹ s yc`.
  obtain ⟨yD, hyD_mem, hyD_conj⟩ := data.exists_yD_mem_actionCommutator_conj_s_eq_t
  set Yq : ↥hyp.base.Q := yD⁻¹ with hYqdef
  have hYq_mem : Yq ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut := inv_mem hyD_mem
  set yc : G := (Yq : G) with hycdef
  have hyc_eq : yc = (yD : G)⁻¹ := by rw [hycdef, hYqdef, InvMemClass.coe_inv]
  have hty : data.t = yc⁻¹ * data.s * yc := by
    rw [hyc_eq, inv_inv, ← hyD_conj, MulAut.conj_apply]
  refine ⟨yc, hty, ?_⟩
  -- `W₂` elements used as conjugators.
  set sW : ↥hyp.base.W2 := ⟨data.s, data.s_mem_W2⟩ with hsWdef
  set s1W : ↥hyp.base.W2 := ⟨s1, hs1W⟩ with hs1Wdef
  set s3W : ↥hyp.base.W2 := ⟨s3, hs3W⟩ with hs3Wdef
  have hsW_coe : (sW : G) = data.s := rfl
  have hs1W_coe : (s1W : G) = s1 := rfl
  have hs3W_coe : (s3W : G) = s3 := rfl
  -- BG's `Y_B` (the four-fold conjugate, `(5074)`), as an element of `⁅Q, W₂⁆`.
  set YB : ↥hyp.base.Q :=
    (data.w2ConjQAut s3W⁻¹ Yq)⁻¹ * data.w2ConjQAut sW Yq *
      (data.w2ConjQAut (sW * s1W) Yq)⁻¹ * Yq with hYBdef
  have hinv := OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator data.w2ConjQAut
  have hYB_mem : YB ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut := by
    rw [hYBdef]
    exact mul_mem (mul_mem (mul_mem (inv_mem (hinv.smul_mem _ hYq_mem))
      (hinv.smul_mem _ hYq_mem)) (inv_mem (hinv.smul_mem _ hYq_mem))) hYq_mem
  -- `(Y_B : G)` is BG's `s₃⁻¹ t₃ t s₁ t₁⁻¹ t⁻¹` (mmd `(5074)`).
  have hYB_coe : (YB : G) =
      (s3⁻¹ * yc * s3)⁻¹ * (data.s * yc * data.s⁻¹) *
        (data.s * s1 * yc * s1⁻¹ * data.s⁻¹)⁻¹ * yc := by
    rw [hYBdef]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, data.w2ConjQAut_apply_coe,
      hsW_coe, hs1W_coe, hs3W_coe, hycdef]
    group
  -- BG's `(5060)` element `⋆`, the six-fold conjugate product.
  set starQ : ↥hyp.base.Q :=
    Yq⁻¹ * data.w2ConjQAut (sW * sW) Yq * (data.w2ConjQAut (sW * (sW * s1W)) Yq)⁻¹ *
      data.w2ConjQAut (sW * s1W) Yq * (data.w2ConjQAut (sW * s3W⁻¹) Yq)⁻¹ *
        data.w2ConjQAut s3W⁻¹ Yq with hstarQdef
  -- (B) `⋆ = (C.10)`-LHS `= 1` (the `(5060)` regrouping, using `s₂ = s₁⁻¹ s₃⁻¹`).
  have hstarQ_coe : (starQ : G) =
      data.t ^ 2 * s1 * data.t⁻¹ * s2 * data.t⁻¹ * s3 := by
    have hc1 : Commute data.s s1 := data.s_commute_sigma_primeLineElement c1
    have hc3 : Commute data.s s3 := data.s_commute_sigma_primeLineElement c3
    have ht2 : data.t ^ 2 = yc⁻¹ * (data.s * data.s) * yc := by rw [hty, pow_two]; group
    have hti : data.t⁻¹ = yc⁻¹ * data.s⁻¹ * yc := by rw [hty]; group
    -- BG's `(5060)` over-product (the six brackets, before regrouping).
    have hSC : (starQ : G) =
        (yc⁻¹ * (data.s * data.s) * yc) *
          (data.s⁻¹ * data.s⁻¹ * data.s * data.s * s1) *
          (yc⁻¹ * s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1 * yc) *
          (s1⁻¹ * data.s⁻¹ * data.s * s3⁻¹) *
          (yc⁻¹ * s3 * data.s⁻¹ * s3⁻¹ * yc) * s3 := by
      rw [hstarQdef]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, data.w2ConjQAut_apply_coe,
        hsW_coe, hs1W_coe, hs3W_coe, hycdef]
      group
    -- the two `(C.10)` `t⁻¹`-brackets collapse using `[s, sᵢ] = 1`.
    have e3 : s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1 = data.s⁻¹ := by
      rw [show s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1 = s1⁻¹ * data.s⁻¹ * s1 from by group,
        mul_assoc, (hc1.inv_left).eq]; group
    have e5 : s3 * data.s⁻¹ * s3⁻¹ = data.s⁻¹ := by
      rw [(hc3.inv_left.eq).symm]; group
    rw [hSC, ht2, hti, hs2eq,
      show data.s⁻¹ * data.s⁻¹ * data.s * data.s * s1 = s1 from by group,
      show yc⁻¹ * s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1 * yc =
          yc⁻¹ * (s1⁻¹ * data.s⁻¹ * data.s⁻¹ * data.s * s1) * yc from by group,
      e3,
      show s1⁻¹ * data.s⁻¹ * data.s * s3⁻¹ = s1⁻¹ * s3⁻¹ from by group,
      show yc⁻¹ * s3 * data.s⁻¹ * s3⁻¹ * yc = yc⁻¹ * (s3 * data.s⁻¹ * s3⁻¹) * yc from by group,
      e5]
  have hstarQ1 : starQ = 1 := by
    apply Subtype.ext
    rw [hstarQ_coe, hC10, OneMemClass.coe_one]
  -- (A) `(s • Y_B) · Y_B⁻¹ = ⋆` (abelian regrouping inside `⁅Q, W₂⁆`).
  have hA : data.w2ConjQAut sW YB * YB⁻¹ = starQ := by
    have hadd : (Additive.ofMul (data.w2ConjQAut sW YB * YB⁻¹) :
        Additive ↥hyp.base.Q) = Additive.ofMul starQ := by
      rw [hYBdef, hstarQdef]
      simp only [map_mul, map_inv, MulAut.mul_apply, mul_inv_rev, inv_inv, ofMul_mul,
        ofMul_inv]
      abel
    exact Additive.ofMul.injective hadd
  have hβfix : data.w2ConjQAut sW YB = YB :=
    mul_inv_eq_one.mp (by rw [hA]; exact hstarQ1)
  have hYB1 : YB = 1 :=
    data.w2ConjQAut_eq_one_of_mem_actionCommutator_of_s_fixed hYB_mem hβfix
  -- unwind `Y_B = 1` to `(5074)`, hence the `(5076)` relation.
  have hR1 : (s3⁻¹ * yc * s3)⁻¹ * (data.s * yc * data.s⁻¹) *
      (data.s * s1 * yc * s1⁻¹ * data.s⁻¹)⁻¹ * yc = 1 := by
    rw [← hYB_coe, hYB1, OneMemClass.coe_one]
  have hW : s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc) * s1 *
      (yc⁻¹ * s1⁻¹ * yc) * (yc⁻¹ * data.s⁻¹ * yc) = 1 := by
    rw [show s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc) * s1 *
          (yc⁻¹ * s1⁻¹ * yc) * (yc⁻¹ * data.s⁻¹ * yc) =
        (s3⁻¹ * yc * s3)⁻¹ * (data.s * yc * data.s⁻¹) *
          (data.s * s1 * yc * s1⁻¹ * data.s⁻¹)⁻¹ * yc from by group]
    exact hR1
  rw [hty, ← mul_inv_eq_one,
    show s1 * (yc⁻¹ * s1⁻¹ * yc) * (yc⁻¹ * data.s * yc)⁻¹ *
        ((yc⁻¹ * data.s * yc)⁻¹ * (yc⁻¹ * s3⁻¹ * yc) * s3)⁻¹ =
      (s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc))⁻¹ *
        (s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc) * s1 *
          (yc⁻¹ * s1⁻¹ * yc) * (yc⁻¹ * data.s⁻¹ * yc)) *
        (s3⁻¹ * (yc⁻¹ * s3 * yc) * (yc⁻¹ * data.s * yc)) from by group,
    hW, mul_one, inv_mul_cancel]

/-- BG Appendix C, Lemma C.3 Step 3 bad-branch inclusion for a general conjugator
`g`: if `(PU) ∩ (PU)^g = PU`, then conjugation by `g` preserves `PU`. -/
theorem conj_mem_P_sup_U_of_inf_conj_eq {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {g : G}
    (hbad : (hyp.base.P ⊔ hyp.base.U) ⊓
        (MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U)) = hyp.base.P ⊔ hyp.base.U) :
    ∀ ⦃x : G⦄, x ∈ hyp.base.P ⊔ hyp.base.U → g * x * g⁻¹ ∈ hyp.base.P ⊔ hyp.base.U := by
  intro x hx
  have hx_inf : x ∈ (hyp.base.P ⊔ hyp.base.U) ⊓
      (MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U)) := by rw [hbad]; exact hx
  have hx_smul : x ∈ MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U) := hx_inf.2
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx_smul
  have hsmul : ((MulAut.conj g⁻¹)⁻¹ • x) = g * x * g⁻¹ := by
    rw [show ((MulAut.conj g⁻¹)⁻¹ • x) = (MulAut.conj g⁻¹)⁻¹ x from rfl,
      MulAut.conj_inv_apply]; group
  rwa [hsmul] at hx_smul

/-- BG Appendix C, Lemma C.3 Step 3 bad-branch normalization for a general
conjugator `g` of `p`-power order: a one-sided conjugation inclusion of `PU`
upgrades to `g ∈ N_G(PU)`. -/
theorem mem_normalizer_P_sup_U_of_conj_of_pow {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {g : G}
    (hconj : ∀ ⦃x : G⦄, x ∈ hyp.base.P ⊔ hyp.base.U → g * x * g⁻¹ ∈ hyp.base.P ⊔ hyp.base.U)
    (hgp : g ^ hyp.base.p = 1) :
    g ∈ Subgroup.normalizer ((hyp.base.P ⊔ hyp.base.U : Subgroup G) : Set G) := by
  classical
  let PU : Subgroup G := hyp.base.P ⊔ hyp.base.U
  have hiter : ∀ (n : ℕ) ⦃x : G⦄, x ∈ PU → g ^ n * x * (g ^ n)⁻¹ ∈ PU := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; simpa [pow_succ', mul_assoc] using hconj (ih hx)
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have g_inv_eq : g⁻¹ = g ^ (hyp.base.p - 1) := by
    have hmul : g ^ (hyp.base.p - 1) * g = 1 := by
      rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos hp_pos, hgp]
    exact inv_eq_of_mul_eq_one_left hmul
  have hinv_inc : ∀ ⦃x : G⦄, x ∈ PU → g⁻¹ * x * (g⁻¹)⁻¹ ∈ PU := by
    intro x hx
    simpa [g_inv_eq] using hiter (hyp.base.p - 1) hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj hx, fun hx => ?_⟩
  have hpre := hinv_inc (x := g * x * g⁻¹) hx
  convert hpre using 1; group

/-- **BG Appendix C, Lemma C.3 Step 3** (mmd L4988–4992): for `g ∈ P₁^#`,
`(PU) ∩ (PU)^g = U`.  We use the dichotomy `= U ∨ = PU`; the `= PU` branch forces
`g ∈ N_G(PU) ⊆ N_G(P)`, hence (since `g` generates `P₁`) `P₁ ≤ N_G(P)`, giving the
`P₀ = P₁` contradiction `P1_ne_W2`. -/
theorem step3_inf_conj_eq_U_of_mem_P1 [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {g : G} (hg : g ∈ data.P1) (hg1 : g ≠ 1) :
    (hyp.base.P ⊔ hyp.base.U) ⊓ (MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U)) =
      hyp.base.U := by
  rcases data.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
      (inv_mem (data.P1_normalizes_U hg)) with hU | hPU
  · exact hU
  · exfalso
    have hgp : g ^ hyp.base.p = 1 := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (data.P1_eq_zpowers_t ▸ hg)
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        data.t_pow_p_eq_one, one_zpow]
    have hgP : g ∈ Subgroup.normalizer (hyp.base.P : Set G) :=
      data.normalizer_P_sup_U_le_normalizer_P
        (data.mem_normalizer_P_sup_U_of_conj_of_pow
          (data.conj_mem_P_sup_U_of_inf_conj_eq hPU) hgp)
    have horder : orderOf g = hyp.base.p := by
      rcases (hyp.base.p_prime.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hgp))
        with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h
    have hP1g : data.P1 = Subgroup.zpowers g := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_).symm
      rw [Nat.card_zpowers, horder, data.P1_eq_zpowers_t, Nat.card_zpowers,
        data.t_orderOf_eq_p]
    exact data.P1_ne_W2 (data.P1_eq_W2_of_le_normalizer_W2
      (data.P1_le_normalizer_W2_of_le_normalizer_P
        (hP1g ▸ Subgroup.zpowers_le.mpr hgP)))

/-- **BG Appendix C, Lemma C.3 Step 4 conclusion** (mmd L5078–5082): the `(5076)`
relation `s₁ t₁⁻¹ t⁻¹ = t⁻¹ t₃⁻¹ s₃` (`tᵢ = yc⁻¹ sᵢ yc`) forces `t₁ = t⁻¹`, hence
`s₁ = s⁻¹`.  Otherwise `g = t₁⁻¹ t⁻¹ ∈ P₁^#`, and for `u ∈ U^#` the common value
`u^{s₁ t₁⁻¹ t⁻¹} = u^{t⁻¹ t₃⁻¹ s₃}` lies in `(PU) ∩ (PU)^g`, which is `U` by Step 3;
then `u^{s₁} ∈ U^{t t₁} = U`, so Step 2 gives `s₁ = 1`, contradicting `(C.6)`. -/
theorem step4_sigma_primeLine_eq_s_inv [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) {c1 c3 : ZMod hyp.base.p}
    (hc1 : c1 ≠ 0) (hc3 : c3 ≠ 0) (yc : G) (hty : data.t = yc⁻¹ * data.s * yc)
    (hrel : data.sigma (fieldNormalizerPrimeLineElement hyp c1) *
        (yc⁻¹ * (data.sigma (fieldNormalizerPrimeLineElement hyp c1))⁻¹ * yc) * data.t⁻¹ =
      data.t⁻¹ * (yc⁻¹ * (data.sigma (fieldNormalizerPrimeLineElement hyp c3))⁻¹ * yc) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c3)) :
    data.sigma (fieldNormalizerPrimeLineElement hyp c1) = data.s⁻¹ := by
  classical
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  set s1 := data.sigma (fieldNormalizerPrimeLineElement hyp c1) with hs1def
  set s3 := data.sigma (fieldNormalizerPrimeLineElement hyp c3) with hs3def
  have hs1W : s1 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c1
  have hs3W : s3 ∈ hyp.base.W2 := data.sigma_primeLineElement_mem_W2 c3
  -- conjugation by `yc` sends `⟨s⟩ = W₂` into `⟨t⟩ = P₁`.
  have hconj_zpow : ∀ n : ℤ, (yc⁻¹ * data.s * yc) ^ n = yc⁻¹ * data.s ^ n * yc := by
    intro n
    rw [show yc⁻¹ * data.s * yc = MulAut.conj yc⁻¹ data.s from by
      rw [MulAut.conj_apply, inv_inv], ← map_zpow, MulAut.conj_apply, inv_inv]
  have hmem_W2_P1 : ∀ w ∈ hyp.base.W2, yc⁻¹ * w * yc ∈ data.P1 := by
    intro w hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (data.W2_eq_zpowers_s ▸ hw)
    rw [data.P1_eq_zpowers_t, Subgroup.mem_zpowers_iff]
    exact ⟨n, by rw [hty, hconj_zpow, hn]⟩
  have ht1_P1 : yc⁻¹ * s1 * yc ∈ data.P1 := hmem_W2_P1 s1 hs1W
  by_contra hne
  -- `t₁ ≠ t⁻¹`, so `g = t₁⁻¹ t⁻¹ ∈ P₁^#`.
  set g : G := (yc⁻¹ * s1 * yc)⁻¹ * data.t⁻¹ with hgdef
  have hg_P1 : g ∈ data.P1 := mul_mem (inv_mem ht1_P1) (inv_mem data.t_mem_P1)
  have hg1 : g ≠ 1 := by
    intro hg0
    apply hne
    have ht1eq : yc⁻¹ * s1 * yc = data.t⁻¹ :=
      inv_injective (eq_inv_of_mul_eq_one_left (hgdef ▸ hg0))
    have h2 : yc⁻¹ * s1 * yc = yc⁻¹ * data.s⁻¹ * yc := by rw [ht1eq, hty]; group
    exact mul_left_cancel (mul_right_cancel h2)
  -- pick a nontrivial `u ∈ U`.
  obtain ⟨u, hu_ne⟩ := exists_fieldNormalizerNormOneUnit_ne_one hyp
  set U_elt := data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp)
    with hUdef
  have hU_elt : U_elt ∈ hyp.base.U := by
    rw [hUdef, ← data.sigma_U_eq_U]
    exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
  -- `s₁ g = t⁻¹ t₃⁻¹ s₃` (BG (5076)).
  have hs1g : s1 * g = data.t⁻¹ * (yc⁻¹ * s3⁻¹ * yc) * s3 := by
    rw [hgdef,
      show s1 * ((yc⁻¹ * s1 * yc)⁻¹ * data.t⁻¹) =
        s1 * (yc⁻¹ * s1⁻¹ * yc) * data.t⁻¹ from by group]
    exact hrel
  -- the common value `v = u^{s₁ g}`.
  set v : G := (s1 * g)⁻¹ * U_elt * (s1 * g) with hvdef
  -- conjugation by an `N_G(U)` element fixes `U`.
  have hconjU : ∀ h : G, h ∈ Subgroup.normalizer (hyp.base.U : Set G) →
      ∀ x : G, x ∈ hyp.base.U → h * x * h⁻¹ ∈ hyp.base.U :=
    fun h hh x hx => (Subgroup.mem_normalizer_iff.mp hh x).mp hx
  -- `v ∈ (PU)^g` since `g v g⁻¹ = s₁⁻¹ U_elt s₁ ∈ PU`.
  have hv_conj : v ∈ MulAut.conj g⁻¹ • (hyp.base.P ⊔ hyp.base.U) := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have heq : (MulAut.conj g⁻¹)⁻¹ • v = s1⁻¹ * U_elt * s1 := by
      rw [show (MulAut.conj g⁻¹)⁻¹ • v = (MulAut.conj g⁻¹)⁻¹ v from rfl,
        MulAut.conj_inv_apply, hvdef]; group
    rw [heq]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (data.W2_le_P (inv_mem hs1W)))
      (Subgroup.mem_sup_right hU_elt)) (Subgroup.mem_sup_left (data.W2_le_P hs1W))
  -- `v ∈ PU` since `v = u^{t⁻¹ t₃⁻¹ s₃}` and `t, t₃ ∈ N(U)`, `s₃ ∈ P`.
  have hv_PU : v ∈ hyp.base.P ⊔ hyp.base.U := by
    have hvrw : v = s3⁻¹ * ((yc⁻¹ * s3⁻¹ * yc)⁻¹ *
        (data.t * U_elt * data.t⁻¹) * (yc⁻¹ * s3⁻¹ * yc)) * s3 := by
      rw [hvdef, hs1g]; group
    rw [hvrw]
    have h1 : data.t * U_elt * data.t⁻¹ ∈ hyp.base.U :=
      hconjU data.t data.t_normalizes_U U_elt hU_elt
    have ht3i_N : (yc⁻¹ * s3⁻¹ * yc) ∈ Subgroup.normalizer (hyp.base.U : Set G) :=
      data.P1_normalizes_U (hmem_W2_P1 s3⁻¹ (inv_mem hs3W))
    have h2 : (yc⁻¹ * s3⁻¹ * yc)⁻¹ * (data.t * U_elt * data.t⁻¹) *
        ((yc⁻¹ * s3⁻¹ * yc)⁻¹)⁻¹ ∈ hyp.base.U :=
      hconjU _ (inv_mem ht3i_N) _ h1
    rw [inv_inv] at h2
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (data.W2_le_P (inv_mem hs3W)))
      (Subgroup.mem_sup_right h2)) (Subgroup.mem_sup_left (data.W2_le_P hs3W))
  -- by Step 3, `v ∈ U`.
  have hv_U : v ∈ hyp.base.U := by
    have hstep3 := data.step3_inf_conj_eq_U_of_mem_P1 hg_P1 hg1
    rw [← hstep3]; exact ⟨hv_PU, hv_conj⟩
  -- hence `u^{s₁} = s₁⁻¹ U_elt s₁ = g v g⁻¹ ∈ U`.
  have hu_s1 : s1⁻¹ * U_elt * s1 ∈ hyp.base.U := by
    have hconj_v : g * v * g⁻¹ = s1⁻¹ * U_elt * s1 := by rw [hvdef]; group
    rw [← hconj_v]
    exact hconjU g (data.P1_normalizes_U hg_P1) v hv_U
  -- Step 2 forces `s₁ = 1` or `u = 1`, both contradictions.
  have hmem_step : data.sigma (fieldNormalizerPrimeLineElement hyp (-c1)) *
      data.sigma (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) *
        data.sigma (fieldNormalizerPrimeLineElement hyp c1) ∈ hyp.base.U := by
    rw [fieldNormalizerPrimeLineElement_neg, map_inv]
    exact hu_s1
  rcases data.generatorRelation_step2_primeLine_of_sigma_mem_U
    (c := -c1) (d := c1) u hmem_step with hzero | hone
  · exact hc1 hzero.2
  · exact hu_ne hone.1

/-- **BG Appendix C, Lemma C.3 Step 4 capstone `s₁ = s⁻¹`**: the central prime-line
factor of the `k = 3` first normal form is `s⁻¹`.  This is the last gap of BG
Appendix C; combined with the existing finite-field core it discharges
`appC_normSet_generator_relation` without the carrier field. -/
theorem step4Capstone [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) : data.Step4Capstone := by
  intro a ha
  obtain ⟨b, hab, hb⟩ := data.exists_companion_of_unitVal_inv_mem_normSetE ha
  obtain ⟨forms⟩ := data.exists_step4C5NormalForms a b
  have hC10 := (data.relationC9_w_eq_one_and_relationC10 ha hb hab forms).2.2.2
  obtain ⟨yc, hty, h5076⟩ := data.step4_relation_5076 hC10
  have hs1 : data.sigma (fieldNormalizerPrimeLineElement hyp forms.c1) = data.s⁻¹ :=
    data.step4_sigma_primeLine_eq_s_inv forms.c1_ne_zero forms.c3_ne_zero yc hty h5076
  refine ⟨forms.u1, forms.v1, ?_⟩
  rw [← data.step4M1_eq_sigma_inr, forms.hM1, hs1,
    ← data.sScalar_neg_one_eq_sigma_primeLineElement, ← data.s_inv_eq_sScalar_neg_one]

/-- The C.3 generator-relation interface consumed by BG Appendix C
(`∀ a ∈ E, N(2a-1) = 1`), now **derived** from the Step 4 capstone `s₁ = s⁻¹`
rather than carried as the former `appC_twisted_normOne_step` field. -/
theorem appC_normSet_generator_relation [Finite G] {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    appCNormSetGeneratorRelation hyp :=
  data.appC_normSet_generator_relation_of_capstone data.step4Capstone

end Step4

end FieldNormalizerData

end OddOrder.Peterfalvi.S16
