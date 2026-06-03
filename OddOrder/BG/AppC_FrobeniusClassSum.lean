/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Set.Card.Arithmetic
import OddOrder.BG.AppC_NormSet
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
import OddOrder.GroupTheory.RepresentationTheory.ColumnOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup
import OddOrder.Mathlib.SemidirectProduct

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
      (fun _ _ _ => zero_le _)
  have htwo : 1 < (∑ k ∈ Finset.range 2, p ^ k) := by
    simp
    omega
  exact htwo.trans_le hle

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
