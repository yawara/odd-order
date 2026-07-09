/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Set.Card.Arithmetic
import OddOrder.BG.AppC_NormSet
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
import OddOrder.GroupTheory.RepresentationTheory.ClassSumCoefficientFormula
import OddOrder.GroupTheory.RepresentationTheory.ColumnOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.Mathlib.SemidirectProduct
import OddOrder.Peterfalvi.S08_CoherenceTheorems

/-!
# BG Appendix C: Frobenius Class-Sum Bridge

Bender--Glauberman Appendix C, Lemma C.2, pp. 145--152.

This file connects the finite-field pair set in `AppC_NormSet` to the conjugacy
class language used by the class-sum structure constants.  The finite-field leaf
keeps the concrete norm and semidirect-product setup; this file is the first
class-sum dependent layer for the `q >= 5` branch of Lemma C.2.
-/

namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory
open scoped commutatorElement

variable (p q : ℕ)

/-- The additive kernel `P` in the concrete Frobenius group `H = P ⋊ U`. -/
noncomputable def normOneFrobeniusKernel [Fact p.Prime] :
    Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q).range

/-- The norm-one complement `U` in the concrete Frobenius group `H = P ⋊ U`. -/
noncomputable def normOneFrobeniusComplement [Fact p.Prime] :
    Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range

/-- In `H = P ⋊ U`, the additive kernel is normal. -/
theorem normOneFrobeniusKernel_normal [Fact p.Prime] :
    (normOneFrobeniusKernel p q).Normal := by
  unfold normOneFrobeniusKernel normOneFrobeniusGroup
  exact OddOrder.Isaacs.Ch03.inl_range_normal (φ := normOneMulAction p q)

/-- In `H = P ⋊ U`, the additive kernel and norm-one complement are complements. -/
theorem normOneFrobeniusKernel_isComplement_normOneFrobeniusComplement [Fact p.Prime] :
    (normOneFrobeniusKernel p q).IsComplement' (normOneFrobeniusComplement p q) := by
  unfold normOneFrobeniusKernel normOneFrobeniusComplement normOneFrobeniusGroup
  exact OddOrder.Isaacs.Ch03.inl_range_isComplement_inr_range (φ := normOneMulAction p q)

/-- The additive kernel in `H = P ⋊ U` is nontrivial. -/
theorem normOneFrobeniusKernel_ne_bot [Fact p.Prime] :
    normOneFrobeniusKernel p q ≠ ⊥ := by
  intro hbot
  have hmem :
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
        normOneFrobeniusGroup p q) ∈ normOneFrobeniusKernel p q :=
    ⟨Multiplicative.ofAdd (1 : GaloisField p q), rfl⟩
  have h_eq_one :
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
        normOneFrobeniusGroup p q) = 1 := by
    rw [hbot] at hmem
    exact hmem
  have hfield_zero : (1 : GaloisField p q) = 0 :=
    ofAdd_eq_one.mp (SemidirectProduct.inl_inj.mp h_eq_one)
  exact one_ne_zero hfield_zero

/-- If `1 < q`, then the norm-one subgroup has more than one element. -/
theorem normOneUnits_card_gt_one [Fact p.Prime] (hq : 1 < q) :
    1 < Nat.card (normOneUnits p q) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq0 : q ≠ 0 := by omega
  rw [normOneUnits_card p q hq0, ← Nat.geomSum_eq hp2 q]
  have hrange : Finset.range 2 ⊆ Finset.range q := by
    intro k hk
    exact Finset.mem_range.mpr (by
      have hk2 : k < 2 := Finset.mem_range.mp hk
      omega)
  have hle :
      (∑ k ∈ Finset.range 2, p ^ k) ≤ ∑ k ∈ Finset.range q, p ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange
      (fun _ _ _ => Nat.zero_le _)
  have htwo : 1 < (∑ k ∈ Finset.range 2, p ^ k) := by
    simp
    omega
  exact htwo.trans_le hle

/-- The largest term in the geometric sum for `|U|` gives the basic lower bound
`p^(q-1) <= |U|`. -/
theorem pow_sub_one_le_normOneUnits_card [Fact p.Prime] (hq : q ≠ 0) :
    p ^ (q - 1) ≤ Nat.card (normOneUnits p q) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [normOneUnits_card p q hq, ← Nat.geomSum_eq hp2 q]
  exact Finset.single_le_sum (fun k _ => Nat.zero_le (p ^ k)) (by simp; omega)

/-- The two largest terms in the geometric sum for `|U|` give a sharper lower
bound used in the `q >= 5` numerical separation. -/
theorem pow_sub_one_add_pow_sub_two_le_normOneUnits_card [Fact p.Prime] (hq : 2 ≤ q) :
    p ^ (q - 1) + p ^ (q - 2) ≤ Nat.card (normOneUnits p q) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq0 : q ≠ 0 := by omega
  rw [normOneUnits_card p q hq0, ← Nat.geomSum_eq hp2 q]
  have hsubset : ({q - 2, q - 1} : Finset ℕ) ⊆ Finset.range q := by
    intro k hk
    have hk' : k = q - 2 ∨ k = q - 1 := by
      simpa using hk
    rcases hk' with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have hle :
      (∑ k ∈ ({q - 2, q - 1} : Finset ℕ), p ^ k) ≤ ∑ k ∈ Finset.range q, p ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  have hsum :
      (∑ k ∈ ({q - 2, q - 1} : Finset ℕ), p ^ k) =
        p ^ (q - 2) + p ^ (q - 1) := by
    have hne : q - 2 ≠ q - 1 := by omega
    simp [hne, add_comm]
  rw [hsum] at hle
  simpa [add_comm] using hle

/-- For `q >= 5`, the last two terms of `|U| = 1 + p + ... + p^(q-1)`
make `|U|^2` dominate the numerical bound needed for Appendix C Lemma C.2. -/
theorem normOneUnits_card_sq_ge_pow_mul_one_add_pow_sub_two [Fact p.Prime] (hq : 5 ≤ q) :
    p ^ q * (1 + p ^ (q - 2)) ≤ Nat.card (normOneUnits p q) ^ 2 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hU := pow_sub_one_add_pow_sub_two_le_normOneUnits_card p q (by omega)
  have hsqU :
      (p ^ (q - 1) + p ^ (q - 2)) ^ 2 ≤ Nat.card (normOneUnits p q) ^ 2 :=
    Nat.pow_le_pow_left hU 2
  have hb_ge_p2 : p ^ 2 ≤ p ^ (q - 2) :=
    Nat.pow_le_pow_right hp1 (by omega)
  have haux : p ^ 2 ≤ p ^ (q - 2) * (2 * p + 1) :=
    hb_ge_p2.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hpow :
      p ^ q * (1 + p ^ (q - 2)) ≤ (p ^ (q - 1) + p ^ (q - 2)) ^ 2 := by
    have hq1 : q - 1 = q - 2 + 1 := by omega
    have hq2 : q = q - 2 + 2 := by omega
    rw [hq1, hq2]
    simp [pow_add]
    nlinarith [haux]
  exact hpow.trans hsqU

/-- For `q >= 5`, the non-kernel error bound is separated from every possible
coefficient `c <= |U|`.  This is the pure numerical input for the class-sum
bridge in Appendix C Lemma C.2. -/
theorem normOneFrobenius_error_separation_of_five_le [Fact p.Prime] (hq : 5 ≤ q) :
    ∀ c : ℕ, c ≤ Nat.card (normOneUnits p q) →
      (Nat.card (normOneUnits p q) : ℝ) *
          (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) <
        ‖((Nat.card (normOneUnits p q) : ℂ) ^ 3 -
          (c : ℂ) * ((p ^ q : ℕ) : ℂ))‖ := by
  intro c hc
  let U := Nat.card (normOneUnits p q)
  let N := p ^ q
  let B := p ^ (q - 2)
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hU_gt_one : 1 < U := by
    dsimp [U]
    exact normOneUnits_card_gt_one p q (by omega)
  have hU_pos_nat : 0 < U := Nat.lt_trans Nat.zero_lt_one hU_gt_one
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact pow_pos hp_pos q
  have hB_pos_nat : 0 < B := by
    dsimp [B]
    exact pow_pos hp_pos (q - 2)
  have hsq : N * (1 + B) ≤ U ^ 2 := by
    dsimp [U, N, B]
    exact normOneUnits_card_sq_ge_pow_mul_one_add_pow_sub_two p q hq
  have hsq_add : N + N * B ≤ U ^ 2 := by
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using hsq
  have hcN_le_UN : c * N ≤ U * N := Nat.mul_le_mul_right N hc
  have hUN_le_U3 : U * N ≤ U ^ 3 := by
    calc
      U * N ≤ U * (N + N * B) := Nat.mul_le_mul_left U (Nat.le_add_right _ _)
      _ ≤ U * (U ^ 2) := Nat.mul_le_mul_left U hsq_add
      _ = U ^ 3 := by ring
  have hcn_le_U3 : c * N ≤ U ^ 3 := hcN_le_UN.trans hUN_le_U3
  have hdiff_nat_ge : U * N * B ≤ U ^ 3 - c * N := by
    apply Nat.le_sub_of_add_le
    calc
      U * N * B + c * N ≤ U * N * B + U * N := Nat.add_le_add_left hcN_le_UN _
      _ = U * (N + N * B) := by ring
      _ ≤ U * (U ^ 2) := Nat.mul_le_mul_left U hsq_add
      _ = U ^ 3 := by ring
  have hN_lt_Bsq_nat : N < B ^ 2 := by
    dsimp [N, B]
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
  have hN_lt_Bsq_real : (N : ℝ) < (B : ℝ) ^ 2 := by
    exact_mod_cast hN_lt_Bsq_nat
  have hsqrt_lt : √(N : ℝ) < (B : ℝ) := by
    exact (Real.sqrt_lt (by positivity : 0 ≤ (N : ℝ)) (by positivity : 0 ≤ (B : ℝ))).2
      hN_lt_Bsq_real
  have hleft_lt :
      (U : ℝ) * ((N : ℝ) * √(N : ℝ)) < (U : ℝ) * ((N : ℝ) * (B : ℝ)) := by
    have hU_pos_real : 0 < (U : ℝ) := by exact_mod_cast hU_pos_nat
    have hN_pos_real : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
    exact mul_lt_mul_of_pos_left
      (mul_lt_mul_of_pos_left hsqrt_lt hN_pos_real) hU_pos_real
  have hnorm_eq :
      ‖((U : ℂ) ^ 3 - (c : ℂ) * (N : ℂ))‖ = ((U ^ 3 - c * N : ℕ) : ℝ) := by
    have hcomplex :
        ((U : ℂ) ^ 3 - (c : ℂ) * (N : ℂ)) = ((U ^ 3 - c * N : ℕ) : ℂ) := by
      rw [Nat.cast_sub hcn_le_U3]
      norm_num
    rw [hcomplex, Complex.norm_natCast]
  change (U : ℝ) * ((N : ℝ) * √(N : ℝ)) <
    ‖((U : ℂ) ^ 3 - (c : ℂ) * (N : ℂ))‖
  calc
    (U : ℝ) * ((N : ℝ) * √(N : ℝ))
        < (U : ℝ) * ((N : ℝ) * (B : ℝ)) := hleft_lt
    _ = ((U * N * B : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]
      ring_nf
    _ ≤ ((U ^ 3 - c * N : ℕ) : ℝ) := by exact_mod_cast hdiff_nat_ge
    _ = ‖((U : ℂ) ^ 3 - (c : ℂ) * (N : ℂ))‖ := hnorm_eq.symm

/-- If `1 < q`, then the norm-one complement in `H = P ⋊ U` is nontrivial. -/
theorem normOneFrobeniusComplement_ne_bot [Fact p.Prime] (hq : 1 < q) :
    normOneFrobeniusComplement p q ≠ ⊥ := by
  have hcard : 1 < Nat.card (normOneFrobeniusComplement p q) := by
    unfold normOneFrobeniusComplement
    have h := Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inr_injective
      (β := normOneFrobeniusGroup p q))
    exact h ▸ normOneUnits_card_gt_one p q hq
  exact (Subgroup.one_lt_card_iff_ne_bot _).mp hcard

/-- The concrete group `H = P ⋊ U` used in BG Appendix C is a Frobenius group
with additive kernel `P` and norm-one complement `U`. -/
theorem normOneFrobenius_isFrobeniusGroup [Fact p.Prime] (hq : 1 < q) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (normOneFrobeniusGroup p q)
      (normOneFrobeniusKernel p q) (normOneFrobeniusComplement p q) where
  isNormal := normOneFrobeniusKernel_normal p q
  isComplement := normOneFrobeniusKernel_isComplement_normOneFrobeniusComplement p q
  ne_bot_kernel := normOneFrobeniusKernel_ne_bot p q
  ne_bot_complement := normOneFrobeniusComplement_ne_bot p q hq
  conj_frobenius := by
    intro a haA ha n hnN hn hfix
    rcases haA with ⟨u, rfl⟩
    rcases hnN with ⟨x, rfl⟩
    have hx : x.toAdd ≠ (0 : GaloisField p q) := by
      intro hx0
      apply hn
      rw [← ofAdd_toAdd x, hx0, ofAdd_zero, map_one]
    have hfix' :
        SemidirectProduct.inl
            (Multiplicative.ofAdd
              (((u : (GaloisField p q)ˣ) : GaloisField p q) * x.toAdd)) =
          (SemidirectProduct.inl (Multiplicative.ofAdd x.toAdd) :
            normOneFrobeniusGroup p q) := by
      rw [← normOneFrobenius_conj_inl p q u x.toAdd]
      simpa [ofAdd_toAdd] using hfix
    have hmul :
        (((u : (GaloisField p q)ˣ) : GaloisField p q) * x.toAdd) = x.toAdd :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp hfix')
    have huval : ((u : (GaloisField p q)ˣ) : GaloisField p q) = 1 := by
      apply mul_right_cancel₀ hx
      simpa using hmul
    have hu : u = 1 := by
      apply Subtype.ext
      exact Units.ext huval
    exact ha (by simp [hu])

/-- The additive kernel has index `|U|` in the concrete Frobenius group
`H = P ⋊ U`. This is the degree factor for induced characters from `P` to `H`. -/
theorem normOneFrobeniusKernel_index_eq_normOneUnits_card [Fact p.Prime] :
    (normOneFrobeniusKernel p q).index = Nat.card (normOneUnits p q) := by
  have hidx :
      (normOneFrobeniusKernel p q).index =
        Nat.card (normOneFrobeniusComplement p q) :=
    (normOneFrobeniusKernel_isComplement_normOneFrobeniusComplement p q).symm.index_eq_card
  have hcard :
      Nat.card (normOneUnits p q) = Nat.card (normOneFrobeniusComplement p q) :=
    Nat.card_congr (Equiv.ofInjective _ SemidirectProduct.inr_injective
      (β := normOneFrobeniusGroup p q))
  rw [hidx, ← hcard]

/-- The concrete Frobenius group `P ⋊ U` is finite; class-sum coefficients need
a `Fintype` instance.  `SemidirectProduct` is structurally just the product of
its left and right coordinates. -/
noncomputable instance normOneFrobeniusGroup_fintype [Fact p.Prime] :
    Fintype (normOneFrobeniusGroup p q) := by
  letI : Fintype (additiveFieldGroup p q) := Fintype.ofFinite _
  letI : Fintype (normOneUnits p q) := Fintype.ofFinite _
  exact Fintype.ofEquiv (additiveFieldGroup p q × normOneUnits p q)
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => (x.left, x.right)
      left_inv := by intro x; rfl
      right_inv := by intro x; ext <;> rfl }

/-- The concrete semidirect product has order `|P| * |U| = p^q * |U|`. -/
theorem normOneFrobeniusGroup_card_eq [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneFrobeniusGroup p q) = p ^ q * Nat.card (normOneUnits p q) := by
  rw [normOneFrobeniusGroup, SemidirectProduct.card]
  rw [← Nat.card_congr (Multiplicative.ofAdd : GaloisField p q ≃ additiveFieldGroup p q)]
  rw [GaloisField.card p q hq]

/-- Over `ℂ`, the concrete Frobenius-group cardinality is invertible. -/
noncomputable instance normOneFrobeniusGroup_card_invertible [Fact p.Prime] :
    Invertible (Nat.card (normOneFrobeniusGroup p q) : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- The additive kernel is finite as a subtype of the concrete Frobenius group. -/
noncomputable instance normOneFrobeniusKernel_fintype [Fact p.Prime] :
    Fintype (normOneFrobeniusKernel p q) :=
  Fintype.ofFinite _

/-- Over `ℂ`, the additive-kernel cardinality is invertible. -/
noncomputable instance normOneFrobeniusKernel_card_invertible [Fact p.Prime] :
    Invertible (Nat.card (normOneFrobeniusKernel p q) : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- The additive kernel `P` is abelian. -/
noncomputable instance normOneFrobeniusKernel_isMulCommutative [Fact p.Prime] :
    IsMulCommutative (normOneFrobeniusKernel p q) := by
  unfold normOneFrobeniusKernel
  infer_instance

/-- Elements of the additive kernel commute. -/
theorem normOneFrobeniusKernel_mul_comm [Fact p.Prime]
    (x y : normOneFrobeniusKernel p q) :
    x * y = y * x :=
  mul_comm' x y

/-- Irreducible characters of the additive kernel are linear. -/
theorem normOneFrobeniusKernel_irreducibleCharacter_apply_one_eq_one [Fact p.Prime]
    (θ : IrreducibleCharacter (normOneFrobeniusKernel p q)) :
    (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ)
        (1 : normOneFrobeniusKernel p q) = 1 := by
  obtain ⟨V, _, _, _, ρ, hρ, hθ⟩ := θ.isIrreducible
  haveI : Representation.IsIrreducible ρ := hρ
  have hdim : Module.finrank ℂ V = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  change (((θ : ClassFunction (normOneFrobeniusKernel p q) ℂ) :
      normOneFrobeniusKernel p q → ℂ) 1) = 1
  rw [congrFun hθ 1, ρ.char_one, hdim]
  norm_num

/-- Nontrivial irreducible characters of the additive kernel induce irreducibly
to the concrete Frobenius group `H = P ⋊ U`. This is the App C specialization
of Isaacs Theorem 6.34 used to build the q≥5 induced-character family. -/
theorem normOneFrobeniusKernel_induce_isIrreducible [Fact p.Prime] (hq : 1 < q)
    (θ : IrreducibleCharacter (normOneFrobeniusKernel p q))
    (hθ_ne : θ ≠ trivialIrreducibleCharacter (normOneFrobeniusKernel p q)) :
    IsIrreducibleCharacter
      (ClassFunction.induce (normOneFrobeniusKernel p q)
        (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ)) := by
  letI : (normOneFrobeniusKernel p q).Normal := normOneFrobeniusKernel_normal p q
  exact isIrreducibleCharacter_induce_of_frobeniusGroup
    (normOneFrobenius_isFrobeniusGroup p q hq) θ hθ_ne

/-- Degree formula for induced class functions from the additive kernel: the
index factor is the norm-one complement size `|U|`. -/
theorem normOneFrobeniusKernel_induce_apply_one [Fact p.Prime]
    (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ) :
    ClassFunction.induce (normOneFrobeniusKernel p q) θ
        (1 : normOneFrobeniusGroup p q) =
      (Nat.card (normOneUnits p q) : ℂ) *
        θ (1 : normOneFrobeniusKernel p q) := by
  letI : (normOneFrobeniusKernel p q).Normal := normOneFrobeniusKernel_normal p q
  rw [ClassFunction.induce_apply_one, normOneFrobeniusKernel_index_eq_normOneUnits_card]

/-- Irreducible characters induced from the additive kernel have degree `|U|`
in the concrete Frobenius group `H = P ⋊ U`. -/
theorem normOneFrobeniusKernel_induced_irreducible_apply_one_eq_normOneUnits_card [Fact p.Prime]
    (θ : IrreducibleCharacter (normOneFrobeniusKernel p q)) :
    ClassFunction.induce (normOneFrobeniusKernel p q)
        (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ)
        (1 : normOneFrobeniusGroup p q) =
      (Nat.card (normOneUnits p q) : ℂ) := by
  rw [normOneFrobeniusKernel_induce_apply_one,
    normOneFrobeniusKernel_irreducibleCharacter_apply_one_eq_one]
  simp

/-- Induced class functions from the additive kernel vanish off the kernel,
because the kernel is normal. -/
theorem normOneFrobeniusKernel_induce_eq_zero_of_not_mem_kernel [Fact p.Prime]
    (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ)
    {g : normOneFrobeniusGroup p q} (hg : g ∉ normOneFrobeniusKernel p q) :
    ClassFunction.induce (normOneFrobeniusKernel p q) θ g = 0 := by
  letI : (normOneFrobeniusKernel p q).Normal := normOneFrobeniusKernel_normal p q
  exact ClassFunction.induce_eq_zero_of_not_mem_normal θ hg

/-- Equivalently, the support of an induced class function from `P` is contained
in the additive kernel `P`. -/
theorem normOneFrobeniusKernel_induce_support_subset_kernel [Fact p.Prime]
    (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ) :
    (ClassFunction.induce (normOneFrobeniusKernel p q) θ).support ⊆
      normOneFrobeniusKernel p q := by
  letI : (normOneFrobeniusKernel p q).Normal := normOneFrobeniusKernel_normal p q
  exact ClassFunction.support_induce_subset_of_normal (normOneFrobeniusKernel p q) θ

/-- Induced class functions from `P` vanish on nonidentity complement elements. -/
theorem normOneFrobeniusKernel_induce_apply_inr_eq_zero [Fact p.Prime]
    (θ : ClassFunction (normOneFrobeniusKernel p q) ℂ) {u : normOneUnits p q}
    (hu : u ≠ 1) :
    ClassFunction.induce (normOneFrobeniusKernel p q) θ
        (SemidirectProduct.inr u : normOneFrobeniusGroup p q) = 0 := by
  refine normOneFrobeniusKernel_induce_eq_zero_of_not_mem_kernel p q θ ?_
  intro hmem
  rcases hmem with ⟨x, hx⟩
  have hu_eq : u = 1 := by
    symm
    simpa using congrArg SemidirectProduct.right hx
  exact hu hu_eq

/-- A nonzero element of the additive kernel is nontrivial in the concrete
Frobenius group `H = P ⋊ U`. -/
lemma normOneFrobenius_inl_ne_one [Fact p.Prime] {s : GaloisField p q} (hs : s ≠ 0) :
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ≠ 1 := by
  intro h
  exact hs (ofAdd_eq_one.mp (SemidirectProduct.inl_inj.mp h))

/-- When `1 < q`, every additive-kernel element of `H = P ⋊ U` is a commutator.
This is the concrete form of `[P,U]=P` used to show that linear characters of
`H` kill the additive kernel. -/
theorem normOneFrobenius_inl_eq_commutator [Fact p.Prime] (hq : 1 < q)
    (s : GaloisField p q) :
    ∃ x y : normOneFrobeniusGroup p q,
      ⁅x, y⁆ =
        (SemidirectProduct.inl (Multiplicative.ofAdd s) :
          normOneFrobeniusGroup p q) := by
  classical
  haveI : Nontrivial (normOneUnits p q) :=
    Finite.one_lt_card_iff_nontrivial.mp (normOneUnits_card_gt_one p q hq)
  obtain ⟨u, hu⟩ := exists_ne (1 : normOneUnits p q)
  let uval : GaloisField p q := ((u : (GaloisField p q)ˣ) : GaloisField p q)
  have huval : uval ≠ 1 := by
    intro h
    apply hu
    apply Subtype.ext
    apply Units.ext
    simpa [uval] using h
  let denom : GaloisField p q := 1 - uval
  have hdenom : denom ≠ 0 := by
    intro h0
    apply huval
    have h : (1 : GaloisField p q) = uval := sub_eq_zero.mp h0
    exact h.symm
  let t : GaloisField p q := s / denom
  have ht : t - uval * t = s := by
    have hmul : denom * t = s := by
      change denom * (s / denom) = s
      field_simp [hdenom]
    calc
      t - uval * t = (1 - uval) * t := by ring
      _ = denom * t := by rfl
      _ = s := hmul
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd t),
    SemidirectProduct.inr u, ?_⟩
  rw [SemidirectProduct.commutator_inl_inr, SemidirectProduct.inl_inj]
  apply Multiplicative.toAdd.injective
  change (Multiplicative.ofAdd t *
      (normOneMulAction p q u) (Multiplicative.ofAdd t)⁻¹).toAdd = s
  simpa [normOneMulAction_apply, uval, sub_eq_add_neg] using ht

/-- Degree-one irreducible class functions of the concrete Frobenius group are
trivial on the additive kernel. -/
theorem normOneFrobenius_linear_irreducible_apply_inl [Fact p.Prime] (hq : 1 < q)
    {χ : ClassFunction (normOneFrobeniusGroup p q) ℂ}
    (hχ : IsIrreducibleCharacter χ)
    (hχ1 : χ (1 : normOneFrobeniusGroup p q) = 1)
    (s : GaloisField p q) :
    χ (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) = 1 := by
  obtain ⟨x, y, hxy⟩ := normOneFrobenius_inl_eq_commutator p q hq s
  rw [← hxy]
  exact hχ.apply_commutatorElement_eq_one_of_apply_one_eq_one hχ1 x y

/-- Irreducible-character subtype version: if an irreducible character of `H` has
degree one, then it is trivial on the additive kernel. -/
theorem normOneFrobenius_irreducibleCharacter_apply_inl_of_apply_one_eq_one
    [Fact p.Prime] (hq : 1 < q)
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q))
    (hχ1 : (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q) = 1)
    (s : GaloisField p q) :
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) = 1 :=
  normOneFrobenius_linear_irreducible_apply_inl p q hq χ.property hχ1 s

/-- If an irreducible character of the concrete Frobenius group kills the
additive kernel, then it takes its degree value on every additive-kernel
element. -/
theorem normOneFrobenius_apply_inl_eq_apply_one_of_kernel_subset
    [Fact p.Prime]
    {χ : IrreducibleCharacter (normOneFrobeniusGroup p q)}
    (hker : (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ))
    (s : GaloisField p q) :
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) =
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q) := by
  have hmem :
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈
        normOneFrobeniusKernel p q :=
    ⟨Multiplicative.ofAdd s, rfl⟩
  simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using hker hmem

open scoped Classical in
/-- The degree-square sum over irreducible characters whose kernel contains the
additive kernel is the order of the quotient `H/P`, namely `|U|`. -/
theorem normOneFrobenius_sum_kernelCharacter_degree_sq_eq_normOneUnits_card
    [Fact p.Prime] :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)),
      ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q)) ^ 2 =
      (Nat.card (normOneUnits p q) : ℂ) := by
  letI : (normOneFrobeniusKernel p q).Normal := normOneFrobeniusKernel_normal p q
  rw [OddOrder.RepresentationTheory.sumInflatedDegreeSq
    (N := normOneFrobeniusKernel p q)]
  rw [← Subgroup.index_eq_card, normOneFrobeniusKernel_index_eq_normOneUnits_card]

open scoped Classical in
/-- The column-orthogonality contribution at an additive-kernel element from the
irreducible characters killing the additive kernel is exactly `|U|`. -/
theorem normOneFrobenius_sum_kernelCharacter_column_inl_eq_normOneUnits_card
    [Fact p.Prime] (s : GaloisField p q) :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)),
      ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)) *
        star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q))) =
      (Nat.card (normOneUnits p q) : ℂ) := by
  rw [← normOneFrobenius_sum_kernelCharacter_degree_sq_eq_normOneUnits_card p q]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hker := (Finset.mem_filter.mp hχ).2
  rw [normOneFrobenius_apply_inl_eq_apply_one_of_kernel_subset p q hker s]
  obtain ⟨d, _hdpos, hdχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  change ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q)) *
      star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q))) =
    ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q)) ^ 2
  rw [hdχ, star_natCast, sq]

/-- The additive kernel centralizes each of its own elements. This is the easy
inclusion in the concrete centralizer computation used in the q≥5 character
estimate of Lemma C.2. -/
theorem normOneFrobeniusKernel_le_centralizer_inl [Fact p.Prime]
    (s : GaloisField p q) :
    normOneFrobeniusKernel p q ≤
      Subgroup.centralizer
        ({(SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)} : Set (normOneFrobeniusGroup p q)) := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [← map_mul (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q),
    ← map_mul (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q),
    SemidirectProduct.inl_inj]
  exact mul_comm a (Multiplicative.ofAdd s)

/-- In the concrete Frobenius group, the centralizer of a nonzero additive-kernel
element is contained in the kernel. -/
theorem normOneFrobenius_centralizer_inl_le_kernel [Fact p.Prime] (hq : 1 < q)
    {s : GaloisField p q} (hs : s ≠ 0) :
    Subgroup.centralizer
        ({(SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)} : Set (normOneFrobeniusGroup p q)) ≤
      normOneFrobeniusKernel p q := by
  exact (normOneFrobenius_isFrobeniusGroup p q hq).centralizer_kernel_le
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q)
    ⟨Multiplicative.ofAdd s, rfl⟩
    (normOneFrobenius_inl_ne_one p q hs)

/-- In the concrete Frobenius group `H = P ⋊ U`, a nonzero additive-kernel
element has centralizer exactly `P`. -/
theorem normOneFrobenius_centralizer_inl_eq_kernel [Fact p.Prime] (hq : 1 < q)
    {s : GaloisField p q} (hs : s ≠ 0) :
    Subgroup.centralizer
        ({(SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)} : Set (normOneFrobeniusGroup p q)) =
      normOneFrobeniusKernel p q := by
  exact le_antisymm
    (normOneFrobenius_centralizer_inl_le_kernel p q hq hs)
    (normOneFrobeniusKernel_le_centralizer_inl p q s)

/-- The additive kernel `P` in `H = P ⋊ U` has cardinality `p^q`. -/
theorem normOneFrobeniusKernel_card_eq [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneFrobeniusKernel p q) = p ^ q := by
  unfold normOneFrobeniusKernel
  have hrange :
      Nat.card (additiveFieldGroup p q) =
        Nat.card ((SemidirectProduct.inl :
          additiveFieldGroup p q →* normOneFrobeniusGroup p q).range) :=
    Nat.card_congr (Equiv.ofInjective
      (SemidirectProduct.inl : additiveFieldGroup p q → normOneFrobeniusGroup p q)
      SemidirectProduct.inl_injective)
  rw [← hrange]
  rw [← Nat.card_congr (Multiplicative.ofAdd : GaloisField p q ≃ additiveFieldGroup p q)]
  exact GaloisField.card p q hq

/-- For nonzero `s ∈ P`, the centralizer size needed by the q≥5 column
orthogonality estimate is `p^q`. -/
theorem normOneFrobenius_centralizer_inl_card_eq [Fact p.Prime] (hq : 1 < q)
    {s : GaloisField p q} (hs : s ≠ 0) :
    Nat.card
        (Subgroup.centralizer
          ({(SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)} : Set (normOneFrobeniusGroup p q))) =
      p ^ q := by
  rw [normOneFrobenius_centralizer_inl_eq_kernel p q hq hs]
  exact normOneFrobeniusKernel_card_eq p q (by omega)

/-- Column orthogonality specialized to a nonzero additive-kernel element
of the concrete Frobenius group `H = P ⋊ U`: the squared column norm is `p^q`. -/
theorem normOneFrobenius_column_sq_sum_inl_eq [Fact p.Prime] (hq : 1 < q)
    {s : GaloisField p q} (hs : s ≠ 0) :
    (∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)) *
          star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)))) =
      ((p ^ q : ℕ) : ℂ) := by
  rw [column_orthogonality_diagonal]
  rw [normOneFrobenius_centralizer_inl_card_eq p q hq hs]

/-- The same column-orthogonality specialization at the additive-kernel element
`2*s`, the product class representative in BG Lemma C.2. -/
theorem normOneFrobenius_column_sq_sum_two_mul_eq [Fact p.Prime] (hq : 1 < q)
    {s : GaloisField p q} (hs : s ≠ 0) (h2 : (2 : GaloisField p q) ≠ 0) :
    (∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
              normOneFrobeniusGroup p q)) *
          star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
              normOneFrobeniusGroup p q)))) =
      ((p ^ q : ℕ) : ℂ) :=
  normOneFrobenius_column_sq_sum_inl_eq p q hq (mul_ne_zero h2 hs)

open scoped Classical in
/-- The complementary column-orthogonality contribution at a nonzero
additive-kernel element, from irreducible characters not killing the additive
kernel, is `p^q - |U|`. -/
theorem normOneFrobenius_sum_nonKernelCharacter_column_inl_eq
    [Fact p.Prime] (hq : 1 < q) {s : GaloisField p q} (hs : s ≠ 0) :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        ¬ (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)),
      ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)) *
        star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q))) =
      ((p ^ q : ℕ) : ℂ) - (Nat.card (normOneUnits p q) : ℂ) := by
  let pred : IrreducibleCharacter (normOneFrobeniusGroup p q) → Prop := fun χ =>
    (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
  let term : IrreducibleCharacter (normOneFrobeniusGroup p q) → ℂ := fun χ =>
    ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd s) :
          normOneFrobeniusGroup p q)) *
      star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd s) :
          normOneFrobeniusGroup p q)))
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (IrreducibleCharacter (normOneFrobeniusGroup p q))) pred term
  have hkernel : ∑ χ ∈ Finset.univ.filter pred, term χ =
      (Nat.card (normOneUnits p q) : ℂ) := by
    simpa [pred, term] using
      normOneFrobenius_sum_kernelCharacter_column_inl_eq_normOneUnits_card p q s
  have htotal : ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q), term χ =
      ((p ^ q : ℕ) : ℂ) := by
    simpa [term] using normOneFrobenius_column_sq_sum_inl_eq p q hq hs
  have hsplit' := hsplit
  rw [hkernel, htotal] at hsplit'
  rw [add_comm] at hsplit'
  exact eq_sub_of_add_eq hsplit'

/-- The conjugacy class in `H = P ⋊ U` of the additive-kernel element attached to
`s ∈ 𝔽_{p^q}`.  BG Lemma C.2 uses the class of a nonzero `s ∈ P`. -/
noncomputable def normOneClassAt [Fact p.Prime] (s : GaloisField p q) :
    ConjClasses (normOneFrobeniusGroup p q) :=
  ConjClasses.mk
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q)

/-- Every `U`-translate `u*s` lies in the conjugacy class of `s` inside
`H = P ⋊ U`.  This is the class-language form of `u s u⁻¹ = u*s`. -/
theorem normOneClassAt_mul_eq [Fact p.Prime] (s : GaloisField p q)
    (u : normOneUnits p q) :
    ConjClasses.mk
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q) = normOneClassAt p q s := by
  unfold normOneClassAt
  apply Eq.symm
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  refine isConj_iff.mpr ⟨SemidirectProduct.inr u, ?_⟩
  simpa using normOneFrobenius_conj_inl p q u s

/-- Conjugating an additive-kernel point by an arbitrary element of
`H = P ⋊ U` only uses the `U`-coordinate.  The additive `P`-coordinate acts
trivially because `P` is abelian. -/
theorem normOneFrobenius_conj_inl_any [Fact p.Prime]
    (x : normOneFrobeniusGroup p q) (s : GaloisField p q) :
    x * SemidirectProduct.inl (Multiplicative.ofAdd s) * x⁻¹ =
      SemidirectProduct.inl
        (Multiplicative.ofAdd
          ((((x.right : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.inv_right, normOneMulAction_apply]

/-- The conjugacy class of `s ∈ P` in `H = P ⋊ U` is exactly the `U`-orbit of
`s`.  This is the inverse direction to `normOneClassAt_mul_eq`. -/
theorem exists_normOne_mul_of_mem_normOneClass [Fact p.Prime] (s : GaloisField p q)
    {x : normOneFrobeniusGroup p q} (hx : ConjClasses.mk x = normOneClassAt p q s) :
    ∃ u : normOneUnits p q,
      x =
        SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  unfold normOneClassAt at hx
  have hconj : IsConj
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) x :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hx.symm
  rcases isConj_iff.mp hconj with ⟨g, hg⟩
  refine ⟨g.right, ?_⟩
  rw [← hg, normOneFrobenius_conj_inl_any]

/-- A nonzero additive-kernel conjugacy class in `H = P ⋊ U` has exactly one
point for each norm-one unit.  The bijection is `u ↦ inl (u*s)`, and `s ≠ 0`
makes it injective. -/
theorem normOneClassAt_carrier_ncard_eq_normOneUnits_card [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) :
    (normOneClassAt p q s).carrier.ncard = Nat.card (normOneUnits p q) := by
  classical
  rw [← Set.ncard_univ (α := normOneUnits p q)]
  symm
  refine Set.ncard_congr
    (fun u _ =>
      (SemidirectProduct.inl
        (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)) ?maps_to ?inj ?surj
  · intro u _
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr (normOneClassAt_mul_eq p q s u)
  · intro u₁ u₂ _ _ h
    have hu_mul :
        (((u₁ : (GaloisField p q)ˣ) : GaloisField p q) * s) =
          (((u₂ : (GaloisField p q)ˣ) : GaloisField p q) * s) :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp h)
    exact Subtype.ext (Units.ext (mul_right_cancel₀ hs hu_mul))
  · intro x hx
    obtain ⟨u, rfl⟩ :=
      exists_normOne_mul_of_mem_normOneClass p q s
        (ConjClasses.mem_carrier_iff_mk_eq.mp hx)
    exact ⟨u, trivial, rfl⟩

/-- The product class `C_{2s}` has norm-one-unit size whenever `s ≠ 0` and
`2` is nonzero in the field.  This is the class-size factor needed after the
fixed-product fiber count. -/
theorem normOneClassAt_two_mul_carrier_ncard_eq_normOneUnits_card [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) (h2 : (2 : GaloisField p q) ≠ 0) :
    (normOneClassAt p q ((2 : GaloisField p q) * s)).carrier.ncard =
      Nat.card (normOneUnits p q) :=
  normOneClassAt_carrier_ncard_eq_normOneUnits_card p q (mul_ne_zero h2 hs)


/-- For a nonzero additive-kernel class, the centralizer of the chosen class representative
`(normOneClassAt p q s).out` has the same cardinality as the concrete centralizer of `inl s`,
namely `p^q`.  This is the denominator in the App C class-sum character formula. -/
theorem normOneClassAt_out_centralizer_card_eq [Fact p.Prime]
    (hq : 1 < q) {s : GaloisField p q} (hs : s ≠ 0) :
    Nat.card
        (Subgroup.centralizer
          ({(normOneClassAt p q s).out} : Set (normOneFrobeniusGroup p q))) =
      p ^ q := by
  classical
  let C : ConjClasses (normOneFrobeniusGroup p q) := normOneClassAt p q s
  have hmk : ConjClasses.mk C.out = C := OddOrder.RepresentationTheory.conjClass_mk_out C
  have hidx :
      (Subgroup.centralizer ({C.out} : Set (normOneFrobeniusGroup p q))).index =
        Nat.card (normOneUnits p q) := by
    rw [← OddOrder.RepresentationTheory.card_class_eq_index_centralizer C.out]
    rw [hmk]
    rw [← OddOrder.RepresentationTheory.conjClass_carrier_ncard_eq_natCard C]
    exact normOneClassAt_carrier_ncard_eq_normOneUnits_card p q hs
  have hmul :=
    (Subgroup.centralizer ({C.out} : Set (normOneFrobeniusGroup p q))).index_mul_card
  rw [hidx, normOneFrobeniusGroup_card_eq p q (by omega)] at hmul
  rw [Nat.mul_comm (Nat.card (normOneUnits p q))] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := normOneUnits p q)) hmul

/-- A class function evaluated at the chosen representative of `C_s` agrees with
its value at the concrete additive-kernel representative `inl s`. -/
theorem normOneClassAt_out_apply_eq_inl [Fact p.Prime]
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ) (s : GaloisField p q) :
    χ (normOneClassAt p q s).out =
      χ (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) := by
  have hmk_out : ConjClasses.mk (normOneClassAt p q s).out = normOneClassAt p q s :=
    OddOrder.RepresentationTheory.conjClass_mk_out (normOneClassAt p q s)
  have hmk_inl :
      ConjClasses.mk
          (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) =
        normOneClassAt p q s := rfl
  exact χ.of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp (hmk_out.trans hmk_inl.symm))

/-- Irreducible-character version for the inverse of the chosen class representative. -/
theorem normOneClassAt_out_inv_irreducibleCharacter_apply_eq_star_inl [Fact p.Prime]
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q)) (s : GaloisField p q) :
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ) (normOneClassAt p q s).out⁻¹ =
      star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q)) := by
  rw [OddOrder.RepresentationTheory.irreducibleCharacter_apply_inv]
  rw [normOneClassAt_out_apply_eq_inl p q]

/-- Fixed-product version of `IsClassPair`: the two entries lie in prescribed
classes and their product is the chosen representative `z`, not merely an
element conjugate to `z`.  This is the fiber counted by the finite-field pair
set before multiplying by the size of the product conjugacy class. -/
def IsFixedProductClassPair [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q)
    (r : normOneFrobeniusGroup p q × normOneFrobeniusGroup p q) : Prop :=
  ConjClasses.mk r.1 = Ci ∧ ConjClasses.mk r.2 = Cj ∧ r.1 * r.2 = z

/-- The set of fixed-product class pairs. -/
def fixedProductClassPairSet [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q) :
    Set (normOneFrobeniusGroup p q × normOneFrobeniusGroup p q) :=
  {r | IsFixedProductClassPair (p := p) (q := q) Ci Cj z r}

/-- Set version of the class-pair predicate, used to partition the full
class-sum pair count by exact product. -/
def classPairSet [Fact p.Prime]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    Set (normOneFrobeniusGroup p q × normOneFrobeniusGroup p q) :=
  {r | IsClassPair Ci Cj Cs r}

/-- The full class-pair set is the disjoint union of exact-product fibers over
the product conjugacy class.  This is the set-level form of the usual
`a_{ij}^s |C_s|` class-sum count. -/
theorem classPairSet_eq_iUnion_fixedProductClassPairSet [Fact p.Prime]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    classPairSet p q Ci Cj Cs =
      ⋃ z ∈ Cs.carrier, fixedProductClassPairSet (p := p) (q := q) Ci Cj z := by
  ext r
  constructor
  · intro hr
    refine Set.mem_iUnion.mpr ⟨r.1 * r.2, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · exact ConjClasses.mem_carrier_iff_mk_eq.mpr hr.2.2
    · exact ⟨hr.1, hr.2.1, rfl⟩
  · intro hr
    rcases Set.mem_iUnion.mp hr with ⟨z, hzmem⟩
    rcases Set.mem_iUnion.mp hzmem with ⟨hz, hfixed⟩
    exact ⟨hfixed.1, hfixed.2.1, by
      rw [hfixed.2.2]
      exact ConjClasses.mem_carrier_iff_mk_eq.mp hz⟩

/-- Cardinal form of `classPairSet_eq_iUnion_fixedProductClassPairSet`: the
full class-pair count is the finite sum of the fixed-product fiber sizes over
the product class. -/
theorem classPairSet_ncard_eq_finsum_fixedProductClassPairSet_ncard [Fact p.Prime]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    (classPairSet p q Ci Cj Cs).ncard =
      ∑ᶠ z ∈ Cs.carrier,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  classical
  have hdisj :
      Cs.carrier.PairwiseDisjoint
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj) := by
    intro z _ w _ hzw
    change Disjoint
      (fixedProductClassPairSet (p := p) (q := q) Ci Cj z)
      (fixedProductClassPairSet (p := p) (q := q) Ci Cj w)
    rw [Set.disjoint_left]
    intro r hz hw
    exact hzw (hz.2.2.symm.trans hw.2.2)
  rw [classPairSet_eq_iUnion_fixedProductClassPairSet]
  exact Set.Finite.ncard_biUnion (Set.toFinite _) (fun _ _ => Set.toFinite _) hdisj

/-- The set cardinality of `classPairSet` agrees with the existing class-sum
structure coefficient. -/
theorem classPairSet_ncard_eq_classSumCoeff [Fact p.Prime]
    [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    (classPairSet p q Ci Cj Cs).ncard = classSumCoeff Ci Cj Cs := by
  rw [← card_classPair (G := normOneFrobeniusGroup p q) Ci Cj Cs]
  rw [← Nat.card_coe_set_eq (classPairSet p q Ci Cj Cs)]
  rfl

/-- The class-sum structure coefficient is the sum of fixed-product fiber sizes
over the product class.  The later App C step shows these fibers have equal
cardinality in the concrete Frobenius group. -/
theorem classSumCoeff_eq_finsum_fixedProductClassPairSet_ncard [Fact p.Prime]
    [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    classSumCoeff Ci Cj Cs =
      ∑ᶠ z ∈ Cs.carrier,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  rw [← classPairSet_ncard_eq_classSumCoeff p q Ci Cj Cs]
  exact classPairSet_ncard_eq_finsum_fixedProductClassPairSet_ncard p q Ci Cj Cs

/-- Conjugation does not change the conjugacy-class label in the concrete
Frobenius group.  This local form avoids depending on private helpers from the
class-sum file. -/
theorem normOneFrobenius_mk_conj_eq [Fact p.Prime]
    (g x : normOneFrobeniusGroup p q) :
    ConjClasses.mk (g * x * g⁻¹) = ConjClasses.mk x := by
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by group⟩)

/-- Fixed-product fibers over conjugate products have the same cardinality, by
conjugating both entries of a pair. -/
theorem fixedProductClassPairSet_ncard_eq_of_isConj [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    {z w : normOneFrobeniusGroup p q} (hzw : IsConj z w) :
    (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard =
      (fixedProductClassPairSet (p := p) (q := q) Ci Cj w).ncard := by
  classical
  obtain ⟨g, hg⟩ := isConj_iff.mp hzw
  refine Set.ncard_congr
    (fun r _ => (g * r.1 * g⁻¹, g * r.2 * g⁻¹)) ?maps_to ?inj ?surj
  · intro r hr
    refine ⟨?_, ?_, ?_⟩
    · exact (normOneFrobenius_mk_conj_eq p q g r.1).trans hr.1
    · exact (normOneFrobenius_mk_conj_eq p q g r.2).trans hr.2.1
    · rw [show g * r.1 * g⁻¹ * (g * r.2 * g⁻¹) =
          g * (r.1 * r.2) * g⁻¹ by group, hr.2.2, hg]
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ _ _ hpair
    apply Prod.ext
    · have hx : g * x₁ * g⁻¹ = g * x₂ * g⁻¹ := by
        simpa using congrArg Prod.fst hpair
      have hx' : g⁻¹ * (g * x₁ * g⁻¹) * g = g⁻¹ * (g * x₂ * g⁻¹) * g := by
        rw [hx]
      simpa [mul_assoc] using hx'
    · have hy : g * y₁ * g⁻¹ = g * y₂ * g⁻¹ := by
        simpa using congrArg Prod.snd hpair
      have hy' : g⁻¹ * (g * y₁ * g⁻¹) * g = g⁻¹ * (g * y₂ * g⁻¹) * g := by
        rw [hy]
      simpa [mul_assoc] using hy'
  · intro r hr
    refine ⟨(g⁻¹ * r.1 * g, g⁻¹ * r.2 * g), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact (by
          simpa using (normOneFrobenius_mk_conj_eq p q g⁻¹ r.1).trans hr.1)
      · exact (by
          simpa using (normOneFrobenius_mk_conj_eq p q g⁻¹ r.2).trans hr.2.1)
      · have hback : g⁻¹ * w * g = z := by
          rw [← hg]
          group
        rw [show (g⁻¹ * r.1 * g) * (g⁻¹ * r.2 * g) =
            g⁻¹ * (r.1 * r.2) * g by group, hr.2.2, hback]
    · apply Prod.ext <;> group

/-- Summing fixed-product fiber sizes over one product conjugacy class multiplies
the representative fiber size by the class size. -/
theorem finsum_fixedProductClassPairSet_ncard_eq_carrier_ncard_mul [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q) :
    (∑ᶠ w ∈ (ConjClasses.mk z).carrier,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj w).ncard) =
      (ConjClasses.mk z).carrier.ncard *
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  classical
  let C := (ConjClasses.mk z).carrier
  have hCfin : C.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hCfin]
  have hconst :
      ∀ w ∈ hCfin.toFinset,
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj w).ncard =
          (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
    intro w hw
    have hwC : w ∈ C := by
      simpa [C] using hw
    have hconj : IsConj z w :=
      ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp hwC).symm
    exact (fixedProductClassPairSet_ncard_eq_of_isConj p q Ci Cj hconj).symm
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
    Set.ncard_eq_toFinset_card _ hCfin]
  simp

/-- Class-sum pair counts factor as product-class size times one fixed-product
fiber.  This is the cardinal bridge from `classSumCoeff` to the finite-field
pair count used in App C. -/
theorem classSumCoeff_eq_carrier_ncard_mul_fixedProductClassPairSet_ncard [Fact p.Prime]
    [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q) :
    classSumCoeff Ci Cj (ConjClasses.mk z) =
      (ConjClasses.mk z).carrier.ncard *
        (fixedProductClassPairSet (p := p) (q := q) Ci Cj z).ncard := by
  rw [classSumCoeff_eq_finsum_fixedProductClassPairSet_ncard]
  exact finsum_fixedProductClassPairSet_ncard_eq_carrier_ncard_mul p q Ci Cj z

/-- A pair counted by `normOnePairSetAt s` gives a fixed-product class pair with
product exactly `inl (2*s)`. -/
theorem normOnePairSetAt_isFixedProductClassPair [Fact p.Prime]
    (s : GaloisField p q) {u v : normOneUnits p q}
    (h : (u, v) ∈ normOnePairSetAt p q s) :
    IsFixedProductClassPair (p := p) (q := q)
      (normOneClassAt p q s) (normOneClassAt p q s)
      (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
        normOneFrobeniusGroup p q)
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q),
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q)) := by
  refine ⟨normOneClassAt_mul_eq p q s u, normOneClassAt_mul_eq p q s v, ?_⟩
  exact (mem_normOnePairSetAt_iff_inl_mul_inl p q s u v).mp h

/-- Conversely, a fixed-product class pair over `C_s, C_s` with product
`inl (2*s)` comes from a pair of norm-one units satisfying the BG equation
`u*s + v*s = 2*s`. -/
theorem exists_normOnePairSetAt_of_isFixedProductClassPair [Fact p.Prime]
    (s : GaloisField p q) {x y : normOneFrobeniusGroup p q}
    (h : IsFixedProductClassPair (p := p) (q := q)
      (normOneClassAt p q s) (normOneClassAt p q s)
      (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
        normOneFrobeniusGroup p q) (x, y)) :
    ∃ u v : normOneUnits p q,
      (u, v) ∈ normOnePairSetAt p q s ∧
        x = SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) ∧
        y = SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) := by
  obtain ⟨u, hx⟩ := exists_normOne_mul_of_mem_normOneClass p q s h.1
  obtain ⟨v, hy⟩ := exists_normOne_mul_of_mem_normOneClass p q s h.2.1
  refine ⟨u, v, ?_, hx, hy⟩
  have hprod := h.2.2
  rw [hx, hy] at hprod
  exact (mem_normOnePairSetAt_iff_inl_mul_inl p q s u v).mpr hprod

/-- The finite-field pair count equals the cardinality of the fixed-product
class-pair fiber over `inl (2*s)`.  The hypothesis `s ≠ 0` makes the `U`-action
on `s` free, so the parametrization by `u, v ∈ U` is injective. -/
theorem normOnePairSetAt_ncard_eq_fixedProductClassPairSet_ncard [Fact p.Prime]
    {s : GaloisField p q} (hs : s ≠ 0) :
    (normOnePairSetAt p q s).ncard =
      (fixedProductClassPairSet (p := p) (q := q)
        (normOneClassAt p q s) (normOneClassAt p q s)
        (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)).ncard := by
  classical
  refine Set.ncard_congr
    (fun uv _ =>
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd (((uv.1 : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q),
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((uv.2 : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q))) ?maps_to ?inj ?surj
  · intro uv huv
    exact normOnePairSetAt_isFixedProductClassPair p q s huv
  · rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ _ _ hpair
    have hu_pair := congrArg Prod.fst hpair
    have hv_pair := congrArg Prod.snd hpair
    have hu_mul :
        (((u₁ : (GaloisField p q)ˣ) : GaloisField p q) * s) =
          (((u₂ : (GaloisField p q)ˣ) : GaloisField p q) * s) :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp hu_pair)
    have hv_mul :
        (((v₁ : (GaloisField p q)ˣ) : GaloisField p q) * s) =
          (((v₂ : (GaloisField p q)ˣ) : GaloisField p q) * s) :=
      Multiplicative.ofAdd.injective (SemidirectProduct.inl_inj.mp hv_pair)
    have hu : u₁ = u₂ :=
      Subtype.ext (Units.ext (mul_right_cancel₀ hs hu_mul))
    have hv : v₁ = v₂ :=
      Subtype.ext (Units.ext (mul_right_cancel₀ hs hv_mul))
    exact Prod.ext hu hv
  · intro r hr
    obtain ⟨u, v, huv, hx, hy⟩ :=
      exists_normOnePairSetAt_of_isFixedProductClassPair p q s hr
    refine ⟨(u, v), huv, ?_⟩
    exact Prod.ext hx.symm hy.symm

/-- For nonzero `s`, the class-sum coefficient for `C_s * C_s` landing in
`C_{2s}` is `|U|` times the finite-field fixed-product pair count. -/
theorem classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_pairSetAt_ncard
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    {s : GaloisField p q} (hs : s ≠ 0) (h2 : (2 : GaloisField p q) ≠ 0) :
    classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
        (normOneClassAt p q ((2 : GaloisField p q) * s)) =
      Nat.card (normOneUnits p q) * (normOnePairSetAt p q s).ncard := by
  classical
  change classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
      (ConjClasses.mk
        (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)) =
    Nat.card (normOneUnits p q) * (normOnePairSetAt p q s).ncard
  rw [classSumCoeff_eq_carrier_ncard_mul_fixedProductClassPairSet_ncard]
  change (normOneClassAt p q ((2 : GaloisField p q) * s)).carrier.ncard *
      (fixedProductClassPairSet (p := p) (q := q)
        (normOneClassAt p q s) (normOneClassAt p q s)
        (SemidirectProduct.inl (Multiplicative.ofAdd ((2 : GaloisField p q) * s)) :
          normOneFrobeniusGroup p q)).ncard =
    Nat.card (normOneUnits p q) * (normOnePairSetAt p q s).ncard
  rw [normOneClassAt_two_mul_carrier_ncard_eq_normOneUnits_card p q hs h2,
    ← normOnePairSetAt_ncard_eq_fixedProductClassPairSet_ncard p q hs]

/-- Same coefficient identity with the norm set `E` from BG Appendix C. -/
theorem classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_normSetE_ncard
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hq : q ≠ 0) {s : GaloisField p q} (hs : s ≠ 0)
    (h2 : (2 : GaloisField p q) ≠ 0) :
    classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
        (normOneClassAt p q ((2 : GaloisField p q) * s)) =
      Nat.card (normOneUnits p q) * (normSetE p q).ncard := by
  rw [classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_pairSetAt_ncard
      p q hs h2, normOnePairSetAt_ncard_eq_normSetE_ncard p q hq hs]

/-- In the odd-characteristic finite fields used by Appendix C, `2` is nonzero. -/
lemma two_ne_zero_galoisField [Fact p.Prime] (hpodd : Odd p) :
    (2 : GaloisField p q) ≠ 0 := by
  haveI : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]
    exact ZMod.charP p
  intro hzero
  have hp_dvd_two : p ∣ 2 := by
    have h2cast : ((2 : ℕ) : GaloisField p q) = 0 := by simpa using hzero
    exact (CharP.cast_eq_zero_iff (GaloisField p q) p 2).mp h2cast
  rcases (Nat.dvd_prime Nat.prime_two).mp hp_dvd_two with hp_eq_one | hp_eq_two
  · exact (Fact.out : p.Prime).ne_one hp_eq_one
  · rcases hpodd with ⟨k, hk⟩
    omega

open scoped Classical in
/-- App C specialization of the class-sum coefficient character formula for
`C_1 * C_1 -> C_2` in the concrete Frobenius group `H = P ⋊ U`.  The centralizer
factor is `p^q`, and both input class sizes are `|U|`. -/
theorem normOneFrobenius_classSumCoeff_one_mul_pow_eq_character_sum
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : 1 < q) :
    (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
        ((p ^ q : ℕ) : ℂ) =
      ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
        (((Nat.card (normOneUnits p q) : ℂ) *
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (normOneClassAt p q (1 : GaloisField p q)).out *
          ((Nat.card (normOneUnits p q) : ℂ) *
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (normOneClassAt p q (1 : GaloisField p q)).out)) /
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q)) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (normOneClassAt p q (2 : GaloisField p q)).out⁻¹ := by
  classical
  letI : Fintype (ConjClasses (normOneFrobeniusGroup p q)) := Fintype.ofFinite _
  have hcard1 :
      Nat.card { x : normOneFrobeniusGroup p q //
          ConjClasses.mk x = normOneClassAt p q (1 : GaloisField p q) } =
        Nat.card (normOneUnits p q) := by
    rw [← OddOrder.RepresentationTheory.conjClass_carrier_ncard_eq_natCard]
    exact normOneClassAt_carrier_ncard_eq_normOneUnits_card p q one_ne_zero
  have hcent :
      Nat.card
          (Subgroup.centralizer
            ({(normOneClassAt p q (2 : GaloisField p q)).out} :
              Set (normOneFrobeniusGroup p q))) =
        p ^ q :=
    normOneClassAt_out_centralizer_card_eq p q hq (two_ne_zero_galoisField p q hpodd)
  have h :=
    OddOrder.RepresentationTheory.classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter
      (G := normOneFrobeniusGroup p q)
      (Ci := normOneClassAt p q (1 : GaloisField p q))
      (Cj := normOneClassAt p q (1 : GaloisField p q))
      (Cs := normOneClassAt p q (2 : GaloisField p q))
  rw [hcent, hcard1] at h
  exact h

open scoped Classical in
/-- Same App C class-sum coefficient formula, rewritten at the concrete additive-kernel
representatives `inl 1` and `inl 2` instead of the chosen `ConjClasses.out` values. -/
theorem normOneFrobenius_classSumCoeff_one_mul_pow_eq_concrete_character_sum
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : 1 < q) :
    (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
        ((p ^ q : ℕ) : ℂ) =
      ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
        (((Nat.card (normOneUnits p q) : ℂ) *
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
                normOneFrobeniusGroup p q) *
          ((Nat.card (normOneUnits p q) : ℂ) *
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
                normOneFrobeniusGroup p q))) /
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q)) *
          star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
              normOneFrobeniusGroup p q)) := by
  have h := normOneFrobenius_classSumCoeff_one_mul_pow_eq_character_sum p q hpodd hq
  refine h.trans ?_
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [normOneClassAt_out_apply_eq_inl p q,
    normOneClassAt_out_inv_irreducibleCharacter_apply_eq_star_inl p q]

open scoped Classical in
/-- In the concrete class-sum formula for `C_1 * C_1 -> C_2`, the irreducible
characters whose kernels contain the additive kernel contribute exactly `|U|^3`. -/
theorem normOneFrobenius_kernelCharacter_concrete_classSumContribution_eq
    [Fact p.Prime] :
    ∑ χ ∈ Finset.univ.filter (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)),
      (((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q) *
        ((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q))) /
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (1 : normOneFrobeniusGroup p q)) *
        star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
            normOneFrobeniusGroup p q)) =
      (Nat.card (normOneUnits p q) : ℂ) ^ 3 := by
  let pred : IrreducibleCharacter (normOneFrobeniusGroup p q) → Prop := fun χ =>
    (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
  let Uc : ℂ := (Nat.card (normOneUnits p q) : ℂ)
  have hterm : ∀ χ ∈ Finset.univ.filter pred,
      (((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q) *
        ((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q))) /
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (1 : normOneFrobeniusGroup p q)) *
        star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
            normOneFrobeniusGroup p q)) =
        Uc ^ 2 *
          ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q)) ^ 2 := by
    intro χ hχ
    have hker := (Finset.mem_filter.mp hχ).2
    rw [normOneFrobenius_apply_inl_eq_apply_one_of_kernel_subset p q hker
        (1 : GaloisField p q),
      normOneFrobenius_apply_inl_eq_apply_one_of_kernel_subset p q hker
        (2 : GaloisField p q)]
    obtain ⟨d, hdpos, hdχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
    rw [hdχ, star_natCast]
    change ((((Nat.card (normOneUnits p q) : ℂ) * (d : ℂ) *
          ((Nat.card (normOneUnits p q) : ℂ) * (d : ℂ))) / (d : ℂ)) *
        (d : ℂ) = Uc ^ 2 * (d : ℂ) ^ 2)
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hdpos)]
    ring
  have hsum := Finset.sum_congr rfl (fun χ hχ => hterm χ hχ)
  calc
    ∑ χ ∈ Finset.univ.filter pred,
      (((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q) *
        ((Nat.card (normOneUnits p q) : ℂ) *
          (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q))) /
        (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (1 : normOneFrobeniusGroup p q)) *
        star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
            normOneFrobeniusGroup p q))
        = ∑ χ ∈ Finset.univ.filter pred,
            Uc ^ 2 *
              ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
                (1 : normOneFrobeniusGroup p q)) ^ 2 := hsum
    _ = Uc ^ 2 *
          ∑ χ ∈ Finset.univ.filter pred,
            ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (1 : normOneFrobeniusGroup p q)) ^ 2 := by
          rw [Finset.mul_sum]
    _ = Uc ^ 2 * Uc := by
          rw [normOneFrobenius_sum_kernelCharacter_degree_sq_eq_normOneUnits_card]
    _ = (Nat.card (normOneUnits p q) : ℂ) ^ 3 := by
          change Uc ^ 2 * Uc = Uc ^ 3
          ring

/-- Predicate selecting irreducible characters whose kernel contains the additive
kernel of the concrete Frobenius group. -/
def normOneFrobeniusKernelCharacterPred [Fact p.Prime]
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q)) : Prop :=
  (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
    OddOrder.Peterfalvi.S03.characterKernel
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)

open scoped Classical in
/-- A non-kernel irreducible character of the concrete Frobenius group is induced
from a nontrivial irreducible character of the additive kernel, hence has degree
`|U|`. -/
theorem normOneFrobenius_nonKernelCharacter_apply_one_eq_normOneUnits_card
    [Fact p.Prime] (hq : 1 < q)
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q))
    (hχnon : ¬ normOneFrobeniusKernelCharacterPred p q χ) :
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q) =
      (Nat.card (normOneUnits p q) : ℂ) := by
  let K : Subgroup (normOneFrobeniusGroup p q) := normOneFrobeniusKernel p q
  haveI : K.Normal := normOneFrobeniusKernel_normal p q
  obtain ⟨θ, hθinner⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero
    (H := K) χ
  have hθ_ne : θ ≠ trivialIrreducibleCharacter K := by
    intro hθtriv
    apply hχnon
    intro g hg
    have hKind :
        g ∈ OddOrder.Peterfalvi.S03.characterKernel
          (ClassFunction.induce K (θ : ClassFunction K ℂ)) := by
      have hkerθ : (K.subgroupOf K : Set K) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction K ℂ) := by
        intro n _hn
        rw [hθtriv]
        simp [OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
      have hKsubset := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
        (G := normOneFrobeniusGroup p q) (A := K) (H := K) (le_refl K)
        (θ : ClassFunction K ℂ) hkerθ
      exact hKsubset hg
    exact OddOrder.Peterfalvi.S08.characterKernel_subset_of_inner_induce_ne_zero
      θ.property.isCharacter χ.property hθinner hKind
  let ψ : IrreducibleCharacter (normOneFrobeniusGroup p q) :=
    ⟨ClassFunction.induce K (θ : ClassFunction K ℂ),
      normOneFrobeniusKernel_induce_isIrreducible p q hq θ hθ_ne⟩
  have hψ_eq : ψ = χ := by
    have hinner := irreducibleCharacter_inner_eq_ite ψ χ
    by_cases hψχ : ψ = χ
    · exact hψχ
    · rw [if_neg hψχ] at hinner
      exact absurd hinner hθinner
  have hcf : ClassFunction.induce K (θ : ClassFunction K ℂ) =
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ) :=
    congrArg (fun η : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
      (η : ClassFunction (normOneFrobeniusGroup p q) ℂ)) hψ_eq
  have hval := congrArg
    (fun φ : ClassFunction (normOneFrobeniusGroup p q) ℂ =>
      φ (1 : normOneFrobeniusGroup p q)) hcf
  exact hval.symm.trans
    (normOneFrobeniusKernel_induced_irreducible_apply_one_eq_normOneUnits_card p q θ)

/-- Non-kernel irreducible characters in the App C Frobenius group have degree at
least `|U|`; in fact the previous theorem gives equality. -/
theorem normOneFrobenius_nonKernelCharacter_normOneUnits_card_le_degree
    [Fact p.Prime] (hq : 1 < q)
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q))
    (hχnon : ¬ normOneFrobeniusKernelCharacterPred p q χ) :
    (Nat.card (normOneUnits p q) : ℝ) ≤
      ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q))‖ := by
  rw [normOneFrobenius_nonKernelCharacter_apply_one_eq_normOneUnits_card p q hq χ hχnon]
  simp

/-- The concrete summand in the `C_1 * C_1 -> C_2` class-sum character formula. -/
noncomputable def normOneFrobeniusClassSumConcreteTerm [Fact p.Prime]
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q)) : ℂ :=
  (((Nat.card (normOneUnits p q) : ℂ) *
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
          normOneFrobeniusGroup p q) *
    ((Nat.card (normOneUnits p q) : ℂ) *
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
          normOneFrobeniusGroup p q))) /
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (1 : normOneFrobeniusGroup p q)) *
    star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
        normOneFrobeniusGroup p q))

open scoped Classical in
/-- The non-kernel-character error term in the concrete `C_1 * C_1 -> C_2`
class-sum formula. -/
noncomputable def normOneFrobeniusNonKernelContribution [Fact p.Prime] : ℂ :=
  ∑ χ ∈ Finset.univ.filter
      (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        ¬ normOneFrobeniusKernelCharacterPred p q χ),
    normOneFrobeniusClassSumConcreteTerm p q χ

open scoped Classical in
/-- The concrete class-sum formula split into the kernel contribution `|U|^3`
and the remaining non-kernel-character contribution. -/
theorem normOneFrobenius_classSumCoeff_one_mul_pow_eq_kernelContribution_add_nonKernelContribution
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : 1 < q) :
    (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
        ((p ^ q : ℕ) : ℂ) =
      (Nat.card (normOneUnits p q) : ℂ) ^ 3 +
        normOneFrobeniusNonKernelContribution p q := by
  let pred : IrreducibleCharacter (normOneFrobeniusGroup p q) → Prop :=
    normOneFrobeniusKernelCharacterPred p q
  let term : IrreducibleCharacter (normOneFrobeniusGroup p q) → ℂ :=
    normOneFrobeniusClassSumConcreteTerm p q
  have hformula :
      (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
            (normOneClassAt p q (1 : GaloisField p q))
            (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
          ((p ^ q : ℕ) : ℂ) =
        ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q), term χ := by
    simpa [term, normOneFrobeniusClassSumConcreteTerm] using
      normOneFrobenius_classSumCoeff_one_mul_pow_eq_concrete_character_sum p q hpodd hq
  have hkernel :
      ∑ χ ∈ Finset.univ.filter pred, term χ =
        (Nat.card (normOneUnits p q) : ℂ) ^ 3 := by
    simpa [pred, term, normOneFrobeniusKernelCharacterPred,
      normOneFrobeniusClassSumConcreteTerm] using
      normOneFrobenius_kernelCharacter_concrete_classSumContribution_eq p q
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (IrreducibleCharacter (normOneFrobeniusGroup p q))) pred term
  calc
    (classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q)) : ℂ) *
        ((p ^ q : ℕ) : ℂ)
        = ∑ χ : IrreducibleCharacter (normOneFrobeniusGroup p q), term χ := hformula
    _ = ∑ χ ∈ Finset.univ.filter pred, term χ +
          ∑ χ ∈ Finset.univ.filter (fun χ => ¬ pred χ), term χ := hsplit.symm
    _ = (Nat.card (normOneUnits p q) : ℂ) ^ 3 +
          normOneFrobeniusNonKernelContribution p q := by
        rw [hkernel]
        rfl


open scoped Classical in
/-- Real norm-square form of the non-kernel column-orthogonality contribution at
an additive-kernel element.  This is the form used for the Cauchy estimate in
BG Lemma C.2. -/
theorem normOneFrobenius_sum_nonKernelCharacter_normSq_inl_eq
    [Fact p.Prime] (hq : 1 < q) {s : GaloisField p q} (hs : s ≠ 0) :
    ∑ χ ∈ Finset.univ.filter
        (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
          ¬ normOneFrobeniusKernelCharacterPred p q χ),
      Complex.normSq
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)) =
      ((p ^ q : ℕ) : ℝ) - (Nat.card (normOneUnits p q) : ℝ) := by
  have hcomplex :
      ∑ χ ∈ Finset.univ.filter
          (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
            ¬ normOneFrobeniusKernelCharacterPred p q χ),
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)) *
          star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q))) =
        ((p ^ q : ℕ) : ℂ) - (Nat.card (normOneUnits p q) : ℂ) := by
    simpa [normOneFrobeniusKernelCharacterPred] using
      normOneFrobenius_sum_nonKernelCharacter_column_inl_eq p q hq hs
  have hcast :
      ((∑ χ ∈ Finset.univ.filter
          (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
            ¬ normOneFrobeniusKernelCharacterPred p q χ),
        Complex.normSq
          ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)) : ℝ) : ℂ) =
        ∑ χ ∈ Finset.univ.filter
          (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
            ¬ normOneFrobeniusKernelCharacterPred p q χ),
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q)) *
          star (((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd s) :
              normOneFrobeniusGroup p q))) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  apply Complex.ofReal_injective
  rw [hcast, hcomplex]
  norm_num [Complex.ofReal_sub]

open scoped Classical in
/-- The non-kernel squared column norm at a nonzero additive-kernel element is
bounded by the additive-kernel order `p^q`. -/
theorem normOneFrobenius_sum_nonKernelCharacter_normSq_inl_le
    [Fact p.Prime] (hq : 1 < q) {s : GaloisField p q} (hs : s ≠ 0) :
    ∑ χ ∈ Finset.univ.filter
        (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
          ¬ normOneFrobeniusKernelCharacterPred p q χ),
      Complex.normSq
        ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd s) :
            normOneFrobeniusGroup p q)) ≤
      ((p ^ q : ℕ) : ℝ) := by
  rw [normOneFrobenius_sum_nonKernelCharacter_normSq_inl_eq p q hq hs]
  have hU_nonneg : (0 : ℝ) ≤ (Nat.card (normOneUnits p q) : ℝ) := by positivity
  linarith

omit p q in
/-- Cauchy's inequality in the form used for the App C column estimates:
`∑ |a_i|² |b_i| ≤ (∑ |a_i|²) sqrt(∑ |b_i|²)`. -/
theorem sum_normSq_mul_norm_le_sum_normSq_mul_sqrt_sum_normSq
    {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ∑ i ∈ s, Complex.normSq (a i) * ‖b i‖ ≤
      (∑ i ∈ s, Complex.normSq (a i)) *
        √(∑ i ∈ s, Complex.normSq (b i)) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun i => Complex.normSq (a i)) (fun i => ‖b i‖)
  have hA_nonneg : 0 ≤ ∑ i ∈ s, Complex.normSq (a i) := by
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hAsq_le :
      ∑ i ∈ s, Complex.normSq (a i) ^ 2 ≤
        (∑ i ∈ s, Complex.normSq (a i)) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Complex.normSq_nonneg _
  have hsqrtA_le :
      √(∑ i ∈ s, Complex.normSq (a i) ^ 2) ≤
        ∑ i ∈ s, Complex.normSq (a i) := by
    rw [Real.sqrt_le_iff]
    exact ⟨hA_nonneg, hAsq_le⟩
  have hsqrtB_eq :
      √(∑ i ∈ s, ‖b i‖ ^ 2) =
        √(∑ i ∈ s, Complex.normSq (b i)) := by
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Complex.normSq_eq_norm_sq (b i)).symm
  calc
    ∑ i ∈ s, Complex.normSq (a i) * ‖b i‖
        ≤ √(∑ i ∈ s, Complex.normSq (a i) ^ 2) *
            √(∑ i ∈ s, ‖b i‖ ^ 2) := hcs
    _ ≤ (∑ i ∈ s, Complex.normSq (a i)) *
          √(∑ i ∈ s, ‖b i‖ ^ 2) := by
        gcongr
    _ = (∑ i ∈ s, Complex.normSq (a i)) *
          √(∑ i ∈ s, Complex.normSq (b i)) := by
        rw [hsqrtB_eq]

/-- A single non-kernel summand in the concrete class-sum formula is bounded by
`|U| * |χ(1_field)|^2 * |χ(2_field)|`, assuming the character degree is at least
`|U|`.  The remaining q≥5 work is to supply this degree lower bound for the
non-kernel characters. -/
theorem normOneFrobeniusClassSumConcreteTerm_norm_le_of_normOneUnits_card_le_degree
    [Fact p.Prime] {χ : IrreducibleCharacter (normOneFrobeniusGroup p q)}
    (hχdeg : (Nat.card (normOneUnits p q) : ℝ) ≤
      ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (1 : normOneFrobeniusGroup p q))‖) :
    ‖normOneFrobeniusClassSumConcreteTerm p q χ‖ ≤
      (Nat.card (normOneUnits p q) : ℝ) *
        Complex.normSq
          ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
              normOneFrobeniusGroup p q)) *
        ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
          (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
            normOneFrobeniusGroup p q))‖ := by
  let Uc : ℂ := (Nat.card (normOneUnits p q) : ℂ)
  let Ur : ℝ := (Nat.card (normOneUnits p q) : ℝ)
  let a : ℂ :=
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
        normOneFrobeniusGroup p q)
  let b : ℂ :=
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
        normOneFrobeniusGroup p q)
  let d : ℂ :=
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (1 : normOneFrobeniusGroup p q)
  have hd_ne : d ≠ 0 := by
    obtain ⟨n, hn, hnχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
    dsimp [d]
    rw [hnχ]
    exact Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
  have hU_norm : ‖Uc‖ = Ur := by
    simp [Uc, Ur]
  have hfrac : Ur / ‖d‖ ≤ 1 := (div_le_one hd_pos).mpr (by simpa [Ur, d] using hχdeg)
  have hU_nonneg : 0 ≤ Ur := by positivity
  have ha_nonneg : 0 ≤ ‖a‖ := norm_nonneg _
  have hb_nonneg : 0 ≤ ‖b‖ := norm_nonneg _
  calc
    ‖normOneFrobeniusClassSumConcreteTerm p q χ‖
        = ((Ur * ‖a‖) * (Ur * ‖a‖) / ‖d‖) * ‖b‖ := by
            simp [normOneFrobeniusClassSumConcreteTerm, Ur, a, b, d]
    _ = Ur * (Ur / ‖d‖) * (‖a‖ ^ 2 * ‖b‖) := by ring
    _ ≤ Ur * 1 * (‖a‖ ^ 2 * ‖b‖) := by
          gcongr
    _ = Ur * Complex.normSq a * ‖b‖ := by
          rw [Complex.normSq_eq_norm_sq]
          ring

open scoped Classical in
/-- If every non-kernel character has degree at least `|U|`, the whole
non-kernel contribution is bounded by the corresponding column-norm sum. -/
theorem normOneFrobeniusNonKernelContribution_norm_le_sum_of_degree_ge
    [Fact p.Prime]
    (hdeg : ∀ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
      ¬ normOneFrobeniusKernelCharacterPred p q χ →
        (Nat.card (normOneUnits p q) : ℝ) ≤
          ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q))‖) :
    ‖normOneFrobeniusNonKernelContribution p q‖ ≤
      ∑ χ ∈ Finset.univ.filter
          (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
            ¬ normOneFrobeniusKernelCharacterPred p q χ),
        (Nat.card (normOneUnits p q) : ℝ) *
          Complex.normSq
            ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
                normOneFrobeniusGroup p q)) *
          ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
              normOneFrobeniusGroup p q))‖ := by
  unfold normOneFrobeniusNonKernelContribution
  calc
    ‖∑ χ ∈ Finset.univ.filter
        (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
          ¬ normOneFrobeniusKernelCharacterPred p q χ),
        normOneFrobeniusClassSumConcreteTerm p q χ‖
        ≤ ∑ χ ∈ Finset.univ.filter
            (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
              ¬ normOneFrobeniusKernelCharacterPred p q χ),
            ‖normOneFrobeniusClassSumConcreteTerm p q χ‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ Finset.univ.filter
            (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
              ¬ normOneFrobeniusKernelCharacterPred p q χ),
          (Nat.card (normOneUnits p q) : ℝ) *
            Complex.normSq
              ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
                (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
                  normOneFrobeniusGroup p q)) *
            ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
              (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
                normOneFrobeniusGroup p q))‖ := by
        refine Finset.sum_le_sum ?_
        intro χ hχ
        exact normOneFrobeniusClassSumConcreteTerm_norm_le_of_normOneUnits_card_le_degree
          p q (χ := χ) (hdeg χ (Finset.mem_filter.mp hχ).2)

open scoped Classical in
/-- If every non-kernel character has degree at least `|U|`, column
orthogonality bounds the whole non-kernel error by
`|U| * p^q * sqrt(p^q)`. -/
theorem normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt_of_degree_ge
    [Fact p.Prime] (hpodd : Odd p) (hq : 1 < q)
    (hdeg : ∀ χ : IrreducibleCharacter (normOneFrobeniusGroup p q),
      ¬ normOneFrobeniusKernelCharacterPred p q χ →
        (Nat.card (normOneUnits p q) : ℝ) ≤
          ‖((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
            (1 : normOneFrobeniusGroup p q))‖) :
    ‖normOneFrobeniusNonKernelContribution p q‖ ≤
      (Nat.card (normOneUnits p q) : ℝ) *
        (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) := by
  let S : Finset (IrreducibleCharacter (normOneFrobeniusGroup p q)) :=
    Finset.univ.filter
      (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        ¬ normOneFrobeniusKernelCharacterPred p q χ)
  let a : IrreducibleCharacter (normOneFrobeniusGroup p q) → ℂ := fun χ =>
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
        normOneFrobeniusGroup p q)
  let b : IrreducibleCharacter (normOneFrobeniusGroup p q) → ℂ := fun χ =>
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
        normOneFrobeniusGroup p q)
  let U : ℝ := (Nat.card (normOneUnits p q) : ℝ)
  have hterm :=
    normOneFrobeniusNonKernelContribution_norm_le_sum_of_degree_ge p q hdeg
  have hsumCauchy :
      ∑ χ ∈ S, Complex.normSq (a χ) * ‖b χ‖ ≤
        (∑ χ ∈ S, Complex.normSq (a χ)) *
          √(∑ χ ∈ S, Complex.normSq (b χ)) :=
    sum_normSq_mul_norm_le_sum_normSq_mul_sqrt_sum_normSq S a b
  have hA_le : ∑ χ ∈ S, Complex.normSq (a χ) ≤ ((p ^ q : ℕ) : ℝ) := by
    simpa [S, a] using
      normOneFrobenius_sum_nonKernelCharacter_normSq_inl_le p q hq
        (s := (1 : GaloisField p q)) one_ne_zero
  have hB_le : ∑ χ ∈ S, Complex.normSq (b χ) ≤ ((p ^ q : ℕ) : ℝ) := by
    simpa [S, b] using
      normOneFrobenius_sum_nonKernelCharacter_normSq_inl_le p q hq
        (s := (2 : GaloisField p q)) (two_ne_zero_galoisField p q hpodd)
  have hU_nonneg : 0 ≤ U := by positivity
  calc
    ‖normOneFrobeniusNonKernelContribution p q‖
        ≤ ∑ χ ∈ S, U * Complex.normSq (a χ) * ‖b χ‖ := by
          simpa [S, a, b, U] using hterm
    _ = U * ∑ χ ∈ S, Complex.normSq (a χ) * ‖b χ‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun χ _ => ?_
          ring
    _ ≤ U * ((∑ χ ∈ S, Complex.normSq (a χ)) *
          √(∑ χ ∈ S, Complex.normSq (b χ))) := by
          gcongr
    _ ≤ U * (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) := by
          gcongr
    _ = (Nat.card (normOneUnits p q) : ℝ) *
          (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) := by
          rfl

open scoped Classical in
/-- In the concrete Appendix C Frobenius group, the non-kernel class-sum error
term is bounded by `|U| * p^q * sqrt(p^q)`.

The preceding degree-free form follows from the classification of non-kernel
irreducible characters as induced characters from the additive kernel. -/
theorem normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt
    [Fact p.Prime] (hpodd : Odd p) (hq : 1 < q) :
    ‖normOneFrobeniusNonKernelContribution p q‖ ≤
      (Nat.card (normOneUnits p q) : ℝ) *
        (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) :=
  normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt_of_degree_ge
    p q hpodd hq fun χ hχnon =>
      normOneFrobenius_nonKernelCharacter_normOneUnits_card_le_degree
        p q hq χ hχnon

open scoped Classical in
/-- If the main term `|U|^3` is separated from every possible coefficient
`c <= |U|` by more than the non-kernel error bound, then the concrete class-sum
coefficient is strictly larger than `|U|`.

This isolates the analytic/numeric part of the `q >= 5` branch from the
class-sum character calculation. -/
theorem normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card_of_error_separation
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : 1 < q)
    (hseparation : ∀ c : ℕ, c ≤ Nat.card (normOneUnits p q) →
      (Nat.card (normOneUnits p q) : ℝ) *
          (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) <
        ‖((Nat.card (normOneUnits p q) : ℂ) ^ 3 -
          (c : ℂ) * ((p ^ q : ℕ) : ℂ))‖) :
    Nat.card (normOneUnits p q) <
      classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
        (normOneClassAt p q (1 : GaloisField p q))
        (normOneClassAt p q (2 : GaloisField p q)) := by
  let c : ℕ :=
    classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
      (normOneClassAt p q (1 : GaloisField p q))
      (normOneClassAt p q (2 : GaloisField p q))
  by_contra hnot
  have hc_le : c ≤ Nat.card (normOneUnits p q) := Nat.le_of_not_gt hnot
  have hformula :
      (c : ℂ) * ((p ^ q : ℕ) : ℂ) =
        (Nat.card (normOneUnits p q) : ℂ) ^ 3 +
          normOneFrobeniusNonKernelContribution p q := by
    dsimp [c]
    simpa using
      normOneFrobenius_classSumCoeff_one_mul_pow_eq_kernelContribution_add_nonKernelContribution
        p q hpodd hq
  have herror := normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt p q hpodd hq
  have hdev :
      (Nat.card (normOneUnits p q) : ℂ) ^ 3 -
          (c : ℂ) * ((p ^ q : ℕ) : ℂ) =
        -normOneFrobeniusNonKernelContribution p q := by
    rw [hformula]
    ring
  have hdev_le :
      ‖((Nat.card (normOneUnits p q) : ℂ) ^ 3 -
          (c : ℂ) * ((p ^ q : ℕ) : ℂ))‖ ≤
        (Nat.card (normOneUnits p q) : ℝ) *
          (((p ^ q : ℕ) : ℝ) * √(((p ^ q : ℕ) : ℝ))) := by
    rw [hdev, norm_neg]
    exact herror
  exact not_lt_of_ge hdev_le (hseparation c hc_le)

open scoped Classical in
/-- For `q >= 5`, the concrete Appendix C class-sum coefficient for
`C_1 * C_1 -> C_2` is strictly larger than `|U|`. -/
theorem normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hfive : 5 ≤ q) :
    Nat.card (normOneUnits p q) <
      classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
        (normOneClassAt p q (1 : GaloisField p q))
        (normOneClassAt p q (2 : GaloisField p q)) :=
  normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card_of_error_separation
    p q hpodd (by omega) (normOneFrobenius_error_separation_of_five_le p q hfive)

/-- Once the character-theory lower bound makes the `C_s * C_s -> C_{2s}`
coefficient larger than `|U|`, the norm set has at least two elements. -/
theorem normSetE_ncard_ge_two_of_normOneCoeff_gt_normOneUnits_card
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hq : q ≠ 0) {s : GaloisField p q} (hs : s ≠ 0)
    (h2 : (2 : GaloisField p q) ≠ 0)
    (hcoeff :
      Nat.card (normOneUnits p q) <
        classSumCoeff (normOneClassAt p q s) (normOneClassAt p q s)
          (normOneClassAt p q ((2 : GaloisField p q) * s))) :
    2 ≤ (normSetE p q).ncard := by
  rw [classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_normSetE_ncard
      p q hq hs h2] at hcoeff
  by_contra hnot
  have hE_le_one : (normSetE p q).ncard ≤ 1 := by omega
  have hmul_le :
      Nat.card (normOneUnits p q) * (normSetE p q).ncard ≤
        Nat.card (normOneUnits p q) * 1 :=
    Nat.mul_le_mul_left _ hE_le_one
  rw [Nat.mul_one] at hmul_le
  exact (Nat.not_lt_of_ge hmul_le) hcoeff

/-- The `s = 1` form needed for the `q ≥ 5` branch of Lemma C.2: the only
remaining input is the character-theoretic lower bound for the `C_1*C_1`
coefficient of `C_2`. -/
theorem normSetE_ncard_ge_two_of_normOneCoeff_one_gt_normOneUnits_card
    [Fact p.Prime] [DecidableEq (ConjClasses (normOneFrobeniusGroup p q))]
    (hpodd : Odd p) (hq : q.Prime)
    (hcoeff :
      Nat.card (normOneUnits p q) <
        classSumCoeff (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (1 : GaloisField p q))
          (normOneClassAt p q (2 : GaloisField p q))) :
    2 ≤ (normSetE p q).ncard := by
  refine normSetE_ncard_ge_two_of_normOneCoeff_gt_normOneUnits_card p q hq.ne_zero
    (s := (1 : GaloisField p q)) one_ne_zero (two_ne_zero_galoisField p q hpodd) ?_
  simpa using hcoeff

/-- The `q >= 5` branch of BG Appendix C Lemma C.2, packaged at the norm-set
level after the class-sum calculation. -/
theorem normSetE_ncard_ge_two_of_five_le
    [Fact p.Prime] (hpodd : Odd p) (hq : q.Prime) (hfive : 5 ≤ q) :
    2 ≤ (normSetE p q).ncard := by
  classical
  exact normSetE_ncard_ge_two_of_normOneCoeff_one_gt_normOneUnits_card p q hpodd hq
    (normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card p q hpodd hfive)

/-- A pair counted by `normOnePairSetAt s` gives a class-pair counted by the
class-sum structure constants for the class of `s` and the class of `2*s` in
`H = P ⋊ U`.  This is the one-way bridge needed before proving that the
finite-field pair count is exactly the relevant class-sum coefficient. -/
theorem normOnePairSetAt_isClassPair [Fact p.Prime] (s : GaloisField p q)
    {u v : normOneUnits p q} (h : (u, v) ∈ normOnePairSetAt p q s) :
    IsClassPair (normOneClassAt p q s) (normOneClassAt p q s)
      (normOneClassAt p q ((2 : GaloisField p q) * s))
      ((SemidirectProduct.inl
          (Multiplicative.ofAdd (((u : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q),
        (SemidirectProduct.inl
          (Multiplicative.ofAdd (((v : (GaloisField p q)ˣ) : GaloisField p q) * s)) :
            normOneFrobeniusGroup p q)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact normOneClassAt_mul_eq p q s u
  · exact normOneClassAt_mul_eq p q s v
  · have hmul := (mem_normOnePairSetAt_iff_inl_mul_inl p q s u v).mp h
    rw [hmul]
    rfl

end OddOrder.BG.AppC.NormSet
