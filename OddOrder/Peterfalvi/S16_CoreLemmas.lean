/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_LemmaC3_Setup
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
  /-- **Peterfalvi (4.3)--(4.9), canonical T-side ν-grid supply.**

  Section 16 is the first layer where the abstract grid in `base` is identified with the
  canonical certain-type construction.  Keeping that identification as an explicit carrier
  field avoids the false generic assertion that every `S15.Hypothesis` determines its ν-grid
  up to row translation (issue 9096). -/
  nuGridSupply :
    @OddOrder.Peterfalvi.S15.NuGridSupplyData G _ base.finiteG base
  q_lt_p : base.q < base.p

namespace Hypothesis

/-- Under **Peterfalvi (14.1)**, the two prime parameters are distinct. -/
theorem p_ne_q (hyp : Hypothesis (G := G)) : hyp.base.p ≠ hyp.base.q := by
  exact ne_of_gt hyp.q_lt_p

/-- `p` is prime, as an instance keyed on the Section 16 hypothesis, so that statements
mentioning `GaloisField hyp.base.p hyp.base.q` elaborate without a local `letI`. -/
instance factHypothesisPPrime (hyp : Hypothesis (G := G)) : Fact hyp.base.p.Prime :=
  ⟨hyp.base.p_prime⟩


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

/-! The Lemma C.3 Step 4 output interface (`normSetGeneratorRelation`,
`normSetTwistedFieldStep`, `normSetTwistedUnitStep`, `normSetTwistedNormOneStep` and the
implications between them) is `(p, q)`-level Appendix C material and now lives in
`OddOrder.BG.AppC_LemmaC3_Setup` (issue 0151). -/

/-- The concrete Frobenius group `H = P \rtimes U` from BG Appendix C,
with Peterfalvi Section 16 parameters. -/
abbrev fieldNormalizerFrobeniusGroup (hyp : Hypothesis (G := G)) : Type _ :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup hyp.base.p hyp.base.q

/-- Abbreviation for BG's norm-one Frobenius kernel at the Section 16 primes. -/
noncomputable abbrev fnKernel (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  BG.AppC.NormSet.normOneFrobeniusKernel hyp.base.p hyp.base.q

/-- Abbreviation for BG's norm-one complement at the Section 16 primes. -/
noncomputable abbrev fnComplement (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  BG.AppC.NormSet.normOneFrobeniusComplement hyp.base.p hyp.base.q

/-- Abbreviation for BG's prime-field line at the Section 16 primes. -/
noncomputable abbrev fnPrimeLine (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  BG.AppC.primeLine hyp.base.p hyp.base.q


/-- The additive kernel `P ≤ H` in the concrete BG Frobenius group. -/
noncomputable def fieldNormalizerKernel (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  fnKernel hyp

/-- The prime-field additive line `P₀ ≤ P` inside the concrete BG Frobenius
group, generated by `1 : F_{p^q}`. -/
noncomputable def fieldNormalizerPrimeLine (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  fnPrimeLine hyp

/-- The norm-one complement `U ≤ H` inside the concrete BG Frobenius group. -/
noncomputable def fieldNormalizerComplement (hyp : Hypothesis (G := G)) :
    Subgroup (fieldNormalizerFrobeniusGroup hyp) :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  fnComplement hyp

/-- In the concrete BG Frobenius group `P ⋊ U`, the additive kernel and the
norm-one complement meet trivially. -/
theorem fieldNormalizerKernel_inf_complement_eq_bot (hyp : Hypothesis (G := G)) :
    fnKernel hyp ⊓ fnComplement hyp = ⊥ := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
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
    fnKernel hyp ⊔ fnComplement hyp = ⊤ := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
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
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
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
  have : Nontrivial (fieldNormalizerNormOneUnits hyp) :=
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
    fieldNormalizerPrimeLineElement hyp c ∈ fnPrimeLine hyp := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [fieldNormalizerPrimeLineElement, fnPrimeLine, OddOrder.BG.AppC.primeLine]
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
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerPrimeLineElement, fieldNormalizerPrimeLineGenerator]

/-- Prime-line scalar elements invert by negating the scalar. -/
theorem fieldNormalizerPrimeLineElement_neg (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) :
    fieldNormalizerPrimeLineElement hyp (-c) =
      (fieldNormalizerPrimeLineElement hyp c)⁻¹ := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerPrimeLineElement]

/-- The distinguished generator lies in the concrete prime-field line `P₀`. -/
theorem fieldNormalizerPrimeLineGenerator_mem (hyp : Hypothesis (G := G)) :
    fieldNormalizerPrimeLineGenerator hyp ∈ fnPrimeLine hyp := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  dsimp [fieldNormalizerPrimeLineGenerator, fnPrimeLine, OddOrder.BG.AppC.primeLine]
  rw [OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl]
  exact Submodule.subset_span (by simp)

/-- The distinguished generator of `P₀` is nontrivial. -/
theorem fieldNormalizerPrimeLineGenerator_ne_one (hyp : Hypothesis (G := G)) :
    fieldNormalizerPrimeLineGenerator hyp ≠ 1 := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  intro h
  have hfield : (1 : GaloisField hyp.base.p hyp.base.q) = 0 :=
    ofAdd_eq_one.mp (SemidirectProduct.inl_inj.mp h)
  exact one_ne_zero hfield

/-- The distinguished generator of `P₀` has order dividing `p`. -/
theorem fieldNormalizerPrimeLineGenerator_pow_p (hyp : Hypothesis (G := G)) :
    (fieldNormalizerPrimeLineGenerator hyp) ^ hyp.base.p = 1 := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have : CharP (GaloisField hyp.base.p hyp.base.q) hyp.base.p := by
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
    let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
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
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerFrobeniusHom, fieldNormalizerAdditiveFrobeniusHom]

@[simp]
theorem fieldNormalizerFrobeniusHom_inr (hyp : Hypothesis (G := G))
    (u : fieldNormalizerNormOneUnits hyp) :
    fieldNormalizerFrobeniusHom hyp
        (SemidirectProduct.inr u : fieldNormalizerFrobeniusGroup hyp) =
      SemidirectProduct.inr (u ^ hyp.base.p) := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simp [fieldNormalizerFrobeniusHom, fieldNormalizerNormOneFrobeniusHom]

/-- The concrete Frobenius fixes the prime-field line pointwise. -/
theorem fieldNormalizerFrobeniusHom_primeLineElement (hyp : Hypothesis (G := G))
    (c : ZMod hyp.base.p) :
    fieldNormalizerFrobeniusHom hyp (fieldNormalizerPrimeLineElement hyp c) =
      fieldNormalizerPrimeLineElement hyp c := by
  let : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
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

/-- The two conclusions of **Peterfalvi (14.2)**, packaged in the form consumed by BG Appendix C.

This is BG's own `AppC.FieldNormalizerData` — hypothesis (B) of Theorem C together with condition
(A) — *pinned* to Peterfalvi's subgroups: the four `_eq` fields record that the abstract `P`, `U`,
`W₂`, `Q` are Section 16's `data.P`, `.U`, `.W2`, `.Q`.  The Lemma C.1--C.3 development is
stated against the abstract parent; the pins are only needed where Section 16 facts about
`hyp.base.*` meet it. -/
structure FieldNormalizerData (hyp : Hypothesis (G := G)) extends
    OddOrder.BG.AppC.FieldNormalizerData hyp.base.p hyp.base.q G where
  /-- The abstract `P = σ(P)` is Peterfalvi's `P`. -/
  P_eq : P = hyp.base.P
  /-- The abstract `U = σ(U)` is Peterfalvi's `U`. -/
  U_eq : U = hyp.base.U
  /-- The abstract `W₂ = σ(P₀)` is Peterfalvi's `W₂`. -/
  W2_eq : W2 = hyp.base.W2
  /-- The abstract `Q` is Peterfalvi's `Q`. -/
  Q_eq : Q = hyp.base.Q

/-! The Lemma C.3 development for `FieldNormalizerData` now lives at the `(p, q)`-abstract
level in `OddOrder.BG.AppC_LemmaC3_Setup`, where it belongs (it is BG Appendix C material,
not Section 16 material).  Since `FieldNormalizerData hyp` extends
`BG.AppC.FieldNormalizerData hyp.base.p hyp.base.q G`, every one of those lemmas remains
reachable from a `data : FieldNormalizerData hyp` by the same dot notation (issue 0151). -/
end OddOrder.Peterfalvi.S16
