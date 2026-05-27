/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.NatInt
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import OddOrder.GroupTheory.RepresentationTheory.RowOrthogonality

/-!
# Fourier coefficients of virtual characters

For a finite group `G` with `|G|` invertible in `ℂ`, the irreducible characters are
orthonormal (`characterTableRowOrthogonality`).  A virtual character `φ ∈ ZIrr G` is a
finite `ℤ`-linear combination of irreducibles, so its "Fourier coefficient" at an
irreducible `χ` is the inner product `⟨φ, χ⟩`, and this coefficient is an **integer**.

This file develops that coefficient API, the prerequisite (layer 2) for the finite
combinatorial core of Peterfalvi §3 (1.4) (`isometry_difference_pair_structure`): the images
`τ (χ_i - χ_0) ∈ ZIrr G` have integer Fourier coefficients, and the norm / mutual inner
products are sums of products of those integers (Parseval), which the combinatorial argument
then constrains.

No spanning statement (`#Irr = #conj-classes`) is needed — only that each `φ ∈ ZIrr G`
already lies in the `ℤ`-span of the orthonormal irreducibles.

Reference issue: `issues/0025-peterfalvi-isometry-difference-core.md` (layer 2).
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- Orthonormality of irreducible characters in inner-product form:
`⟨χ, ψ⟩ = δ_{χ,ψ}`.  This is `characterTableRowOrthogonality` restated through the
`ClassFunction.inner` pairing. -/
theorem irreducibleCharacter_inner_eq_ite (χ ψ : IrreducibleCharacter G) :
    ClassFunction.inner (χ : ClassFunction G ℂ) (ψ : ClassFunction G ℂ) =
      if χ = ψ then 1 else 0 := by
  by_cases h : χ = ψ
  · subst h
    rw [if_pos rfl, ← characterTableRowPairing_eq_inner]
    exact characterTableRowOrthogonality.1 χ
  · rw [if_neg h, ← characterTableRowPairing_eq_inner]
    exact characterTableRowOrthogonality.2 h

/-- The Fourier coefficient `⟨φ, χ⟩` of a virtual character `φ ∈ ZIrr G` at an irreducible
character `χ` is an integer. -/
theorem mem_ZIrr_inner_int (χ : IrreducibleCharacter G) {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) :
    ∃ m : ℤ, ClassFunction.inner φ (χ : ClassFunction G ℂ) = (m : ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      have heq := irreducibleCharacter_inner_eq_ite (⟨x, hx⟩ : IrreducibleCharacter G) χ
      rw [show ((⟨x, hx⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = x from rfl] at heq
      by_cases h : (⟨x, hx⟩ : IrreducibleCharacter G) = χ
      · refine ⟨1, ?_⟩; rw [heq, if_pos h]; norm_num
      · refine ⟨0, ?_⟩; rw [heq, if_neg h]; norm_num
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨mx, hmx⟩ := ihx
      obtain ⟨my, hmy⟩ := ihy
      refine ⟨mx + my, ?_⟩
      rw [ClassFunction.inner_add_left, hmx, hmy]
      push_cast; ring
  | smul a x _ ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨a * m, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, hm]
      push_cast; ring

omit [Finite G] in
/-- Left-linearity of `ClassFunction.inner` over a finite sum. -/
theorem inner_sum_left {ι : Type*} (s : Finset ι) (f : ι → ClassFunction G ℂ)
    (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (∑ i ∈ s, f i) ψ =
      ∑ i ∈ s, ClassFunction.inner (f i) ψ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.inner_add_left, ih]

open scoped Classical in
/-- Orthonormality at the level of irreducible class functions (not the subtype index):
for `a, b` in `irreducibleCharacters G`, `⟨a, b⟩ = δ_{a,b}`. -/
theorem irr_cf_inner {a b : ClassFunction G ℂ}
    (ha : a ∈ irreducibleCharacters G) (hb : b ∈ irreducibleCharacters G) :
    ClassFunction.inner a b = if a = b then (1 : ℂ) else 0 := by
  have key := irreducibleCharacter_inner_eq_ite
    (⟨a, ha⟩ : IrreducibleCharacter G) (⟨b, hb⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at key
  rw [key]
  by_cases h : a = b
  · rw [if_pos h, if_pos (Subtype.ext h)]
  · rw [if_neg h, if_neg fun he => h (Subtype.ext_iff.mp he)]

omit [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- A virtual character `φ ∈ ZIrr G` is a finite `ℂ`-linear combination of irreducible
characters with integer coefficients (recorded as a `Finsupp` supported on `Irr(G)`). -/
theorem mem_ZIrr_repr {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    ∃ c : ClassFunction G ℂ →₀ ℤ, (↑c.support ⊆ irreducibleCharacters G) ∧
      φ = ∑ a ∈ c.support, (c a : ℂ) • a := by
  rw [ZIrr_eq_span] at hφ
  obtain ⟨c, hsupp, hsum⟩ := Submodule.mem_span_set.mp hφ
  refine ⟨c, hsupp, ?_⟩
  rw [← hsum, Finsupp.sum]
  exact Finset.sum_congr rfl fun a _ => (Int.cast_smul_eq_zsmul ℂ (c a) a).symm

open scoped Classical in
/-- The Fourier coefficient of an integer span representation is recovered by the inner
product: `⟨∑ c_a • a, χ⟩ = c_χ`. -/
theorem inner_eq_coeff_of_repr (χ : IrreducibleCharacter G)
    {c : ClassFunction G ℂ →₀ ℤ} (hsupp : ↑c.support ⊆ irreducibleCharacters G) :
    ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a) (χ : ClassFunction G ℂ) =
      (c (χ : ClassFunction G ℂ) : ℂ) := by
  rw [inner_sum_left]
  have hχ : (χ : ClassFunction G ℂ) ∈ irreducibleCharacters G := χ.mem_irreducibleCharacters
  have step : (∑ a ∈ c.support, ClassFunction.inner ((c a : ℂ) • a) (χ : ClassFunction G ℂ))
      = ∑ a ∈ c.support, (if a = (χ : ClassFunction G ℂ) then (c a : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [ClassFunction.inner_smul_left, irr_cf_inner (hsupp (Finset.mem_coe.mpr ha)) hχ,
      mul_ite, mul_one, mul_zero]
  rw [step, Finset.sum_ite_eq' c.support (χ : ClassFunction G ℂ) (fun a => (c a : ℂ))]
  by_cases hmem : (χ : ClassFunction G ℂ) ∈ c.support
  · rw [if_pos hmem]
  · rw [if_neg hmem, Finsupp.notMem_support_iff.mp hmem, Int.cast_zero]

omit [Finite G] in
/-- Conjugate-linearity of `ClassFunction.inner` over a scalar in the right argument. -/
theorem inner_smul_right (c : ℂ) (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner φ (c • ψ) = star c * ClassFunction.inner φ ψ := by
  have h : ClassFunction.innerSum φ (c • ψ) = star c * ClassFunction.innerSum φ ψ := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ClassFunction.smul_apply, star_mul']
    ring
  rw [ClassFunction.inner, ClassFunction.inner, h]; ring

omit [Finite G] in
/-- Right-linearity of `ClassFunction.inner` over a finite sum. -/
theorem inner_sum_right {ι : Type*} (φ : ClassFunction G ℂ) (s : Finset ι)
    (f : ι → ClassFunction G ℂ) :
    ClassFunction.inner φ (∑ i ∈ s, f i) =
      ∑ i ∈ s, ClassFunction.inner φ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.inner_add_right, ih]

/-- **Parseval (norm form)** for an integer span representation: the squared norm is the
sum of squared integer coefficients. -/
theorem inner_self_eq_sum_sq_of_repr {c : ClassFunction G ℂ →₀ ℤ}
    (hsupp : ↑c.support ⊆ irreducibleCharacters G) :
    ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a)
        (∑ a ∈ c.support, (c a : ℂ) • a) =
      ∑ a ∈ c.support, (c a : ℂ) ^ 2 := by
  rw [inner_sum_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [inner_smul_right]
  have hb' : b ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr hb)
  have hcoeff : ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a) b = (c b : ℂ) := by
    have h := inner_eq_coeff_of_repr (⟨b, hb'⟩ : IrreducibleCharacter G) hsupp
    rwa [show ((⟨b, hb'⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = b from rfl] at h
  rw [hcoeff, star_intCast]; ring

/-- A virtual character `φ ∈ ZIrr G` has integer Fourier coefficients and its squared norm
is the sum of their squares. -/
theorem mem_ZIrr_inner_self_eq_sum_sq {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    ∃ c : ClassFunction G ℂ →₀ ℤ, (↑c.support ⊆ irreducibleCharacters G) ∧
      φ = ∑ a ∈ c.support, (c a : ℂ) • a ∧
      ClassFunction.inner φ φ = ∑ a ∈ c.support, (c a : ℂ) ^ 2 := by
  obtain ⟨c, hsupp, hrepr⟩ := mem_ZIrr_repr hφ
  refine ⟨c, hsupp, hrepr, ?_⟩
  rw [hrepr]
  exact inner_self_eq_sum_sq_of_repr hsupp

end OddOrder.RepresentationTheory
