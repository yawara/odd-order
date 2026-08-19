/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import OddOrder.GroupTheory.RepresentationTheory.CharacterRowOrthogonality

/-!
# Finiteness of `Irr G` and the bound `|Irr G| ≤ |ConjClasses G|`

Using the first orthogonality relation (`irreducibleCharacter_inner`), the irreducible
characters of a finite group form a linearly independent family in the space of class
functions, which is finite-dimensional of dimension `|ConjClasses G|`. Hence there are
finitely many irreducible characters, and at most as many as conjugacy classes.

This is the `≤` half of the classical `|Irr G| = |ConjClasses G|`. The reverse inequality
(completeness of the irreducible characters) is the harder Wedderburn-type statement, left
for later.

## Main results

* `OddOrder.RepresentationTheory.classFunctionEquivConjClasses` — the linear isomorphism
  `ClassFunction G ℂ ≃ₗ[ℂ] (ConjClasses G → ℂ)` (a class function is its values on classes).
* `OddOrder.RepresentationTheory.finrank_classFunction` —
  `finrank ℂ (ClassFunction G ℂ) = Nat.card (ConjClasses G)`.
* `OddOrder.RepresentationTheory.linearIndependent_irreducibleCharacter` — the irreducible
  characters are linearly independent.
* `OddOrder.RepresentationTheory.finite_irreducibleCharacter` — `Finite (IrreducibleCharacter G)`.
* `OddOrder.RepresentationTheory.card_irreducibleCharacter_le` —
  `Nat.card (IrreducibleCharacter G) ≤ Nat.card (ConjClasses G)`.
-/

namespace OddOrder.RepresentationTheory

open Module (finrank)

variable {G : Type*} [Group G]

/-- A class function is determined by, and determines, its values on conjugacy classes:
the linear isomorphism `ClassFunction G ℂ ≃ₗ[ℂ] (ConjClasses G → ℂ)`. -/
noncomputable def classFunctionEquivConjClasses :
    ClassFunction G ℂ ≃ₗ[ℂ] (ConjClasses G → ℂ) where
  toFun φ C := φ (conjugacyClassRepresentative C)
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun f := ⟨fun g => f (ConjClasses.mk g), fun g h =>
    congrArg f (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h, rfl⟩).symm)⟩
  left_inv φ := by
    apply ClassFunction.ext
    intro g
    exact φ.of_isConj
      (ConjClasses.mk_eq_mk_iff_isConj.mp (conjugacyClassRepresentative_mk_eq (ConjClasses.mk g)))
  right_inv f := by
    funext C
    exact congrArg f (conjugacyClassRepresentative_mk_eq C)

/-- The space of complex class functions on a finite group is finite-dimensional. -/
instance instFiniteDimensionalClassFunction [Finite G] :
    FiniteDimensional ℂ (ClassFunction G ℂ) := by
  have : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  exact Module.Finite.equiv classFunctionEquivConjClasses.symm

/-- The space of complex class functions on a finite group has dimension equal to the number
of conjugacy classes. -/
theorem finrank_classFunction [Finite G] :
    finrank ℂ (ClassFunction G ℂ) = Nat.card (ConjClasses G) := by
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [classFunctionEquivConjClasses.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

/-- Peterfalvi's inner product against a fixed class function `ψ`, as a linear functional. -/
noncomputable def innerDual [Fintype G] [Invertible (Nat.card G : ℂ)]
    (ψ : ClassFunction G ℂ) : Module.Dual ℂ (ClassFunction G ℂ) where
  toFun φ := ClassFunction.inner φ ψ
  map_add' φ₁ φ₂ := ClassFunction.inner_add_left φ₁ φ₂ ψ
  map_smul' c φ := by simpa using ClassFunction.inner_smul_left c φ ψ

@[simp] theorem innerDual_apply [Fintype G] [Invertible (Nat.card G : ℂ)]
    (ψ φ : ClassFunction G ℂ) : innerDual ψ φ = ClassFunction.inner φ ψ := rfl

/-- **The irreducible characters are linearly independent** (over `ℂ`), via the first
orthogonality relation and the biorthogonal system of inner-product functionals. -/
theorem linearIndependent_irreducibleCharacter [Finite G] :
    LinearIndependent ℂ (fun χ : IrreducibleCharacter G => (χ : ClassFunction G ℂ)) := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun ψ => innerDual (ψ : ClassFunction G ℂ)) (fun χ ψ hχψ => ?_) (fun χ => ?_)
  · simp only [innerDual_apply, irreducibleCharacter_inner]
    rw [if_neg (Ne.symm hχψ)]
  · simp only [innerDual_apply, irreducibleCharacter_inner, if_true]

/-- **There are finitely many irreducible characters** of a finite group. -/
theorem finite_irreducibleCharacter [Finite G] : Finite (IrreducibleCharacter G) :=
  (linearIndependent_irreducibleCharacter (G := G)).finite

/-- **`|Irr G| ≤ |ConjClasses G|`**: the number of irreducible characters is at most the number
of conjugacy classes. (The reverse inequality — completeness — is the harder direction.) -/
theorem card_irreducibleCharacter_le [Finite G] :
    Nat.card (IrreducibleCharacter G) ≤ Nat.card (ConjClasses G) := by
  have := finite_irreducibleCharacter (G := G)
  have : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← finrank_classFunction (G := G)]
  exact (linearIndependent_irreducibleCharacter (G := G)).fintype_card_le_finrank

end OddOrder.RepresentationTheory
