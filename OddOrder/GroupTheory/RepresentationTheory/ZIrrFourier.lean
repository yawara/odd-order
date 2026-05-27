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

end OddOrder.RepresentationTheory
