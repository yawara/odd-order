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

private theorem p_pow_sub_two_lt_q_sq_of_pow_lt_mul_sq {p q : ℕ}
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
      (fun _ _ _ => zero_le _)
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
  appC_twisted_normOne_step : appCNormSetTwistedNormOneStep hyp

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

/-- The C.3 generator-relation interface consumed by BG Appendix C, derived from
BG's norm-one twisted-inverse output stored in `FieldNormalizerData`. -/
theorem appC_normSet_generator_relation {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) :
    appCNormSetGeneratorRelation hyp :=
  appCNormSetGeneratorRelation_of_twisted_normOne_step hyp data.appC_twisted_normOne_step

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
**without** the `FieldNormalizerData.appC_twisted_normOne_step` field.  Once the
capstone is proved, this replaces the field-based
`appC_normSet_generator_relation`. -/
theorem appC_normSet_generator_relation_of_capstone {hyp : Hypothesis (G := G)}
    (data : FieldNormalizerData hyp) (hcap : data.Step4Capstone) :
    appCNormSetGeneratorRelation hyp :=
  appCNormSetGeneratorRelation_of_twisted_normOne_step hyp
    (data.appCNormSetTwistedNormOneStep_of_capstone hcap)

end Step4

end FieldNormalizerData

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
  · -- (14.16) case-(b) still needs the `beta_L` character expansion and
    -- contradiction with `(beta_L^tau, psi^tau_1) ≠ 0`.
    sorry

/-- **Peterfalvi (14.2)**: the field-normalizer configuration follows from the
Section 16 hypotheses. -/
theorem field_normalizer_structure [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Nonempty (FieldNormalizerData hyp) := by
  sorry

/-- **Peterfalvi Section 16 + BG Appendix C**: BG Appendix C turns the
field-normalizer configuration into `p <= q`, contradicting (14.1). -/
theorem nonexistence_of_G [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (bgAppendixC : FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q) :
    False := by
  rcases field_normalizer_structure hG hyp with ⟨data⟩
  exact (not_lt_of_ge (bgAppendixC data)) hyp.q_lt_p

end OddOrder.Peterfalvi.S16
