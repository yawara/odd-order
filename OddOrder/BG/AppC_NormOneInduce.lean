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
# BG Appendix C — the norm-one Frobenius kernel: induction layer

The `normOneFrobeniusKernel` induce/support lemmas and the irreducible-character
evaluation facts on `inl` used by the class-sum estimates of Lemmas C.2/C.3.

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/


namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory
open scoped commutatorElement

variable (p q : ℕ)

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


end OddOrder.BG.AppC.NormSet
