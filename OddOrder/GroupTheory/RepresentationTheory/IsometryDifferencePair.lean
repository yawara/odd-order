/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Complex.Basic
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing
import OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality

/-!
# Isometry on orthonormal difference pairs

A structural lemma underlying Peterfalvi §3 (1.4), §5 (3.2), §6 (4.5), §7 (5.6):

> Given `n ≥ 2` distinct irreducible complex characters `χ_0, …, χ_{n-1}` of a finite
> group `H`, all of the same degree, and a `ℤ`-linear map
> `τ : ClassFunction H ℂ → ClassFunction G ℂ` that is **isometric on the differences**
> `χ_i - χ_0`, there exist distinct irreducible characters `μ_0, …, μ_{n-1}` of `G` and
> a uniform sign `ε ∈ {±1}` such that
>
>   `τ (χ_i - χ_0) = ε • (μ_i - μ_0)`   for all `i ∈ Fin n`.

This is the key abstraction shared across Peterfalvi's Dade isometry / coherence proofs:
isometric `ℤ`-maps between virtual-character lattices send orthonormal-pair structures to
orthonormal-pair structures, up to a uniform sign.

## Status

* Statement only; proof deferred. The classical proof proceeds by induction on `n`,
  using character orthogonality (`SecondOrthogonality`) and integer norm constraints
  on `τ (χ_i - χ_0)`.
* Proof-core routing: the remaining work is split into
  `issues/0025-peterfalvi-isometry-difference-core.md`.  The theorem needs
  second orthogonality to identify the irreducible-character basis coefficients
  and a separate finite integer-vector induction proving the uniform sign shape.
  The statement also carries the degree-zero input used in Peterfalvi's
  `e₂ + e₃` exclusion: every image `τ (χ_i - χ_0)` vanishes at `1`.

## Main statement

* `OddOrder.RepresentationTheory.IsometryDifferencePairNumerics`.
* `OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily`.
* `OddOrder.RepresentationTheory.IsometryDifferenceImagesVanishAtOne`.
* `OddOrder.RepresentationTheory.isometry_difference_pair_structure`.

## References

* Peterfalvi §3 (1.4) (Tau isometry — core Dade preparation).
* Peterfalvi §5 (3.2), §6 (4.5), §7 (5.6) — re-uses the same abstraction.
* Isaacs, *Character Theory of Finite Groups*, Ch. 2 (character orthogonality).
-/

namespace OddOrder.RepresentationTheory

variable {G H : Type*} [Group G] [Group H]

theorem irreducibleCharacter_inner_eq_if
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    {n : ℕ} (χ : Fin n → IrreducibleCharacter G) (hχ : Function.Injective χ)
    (i j : Fin n) :
    ClassFunction.inner (χ i : ClassFunction G ℂ) (χ j : ClassFunction G ℂ) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [characterTableRowPairing] using
      CharacterTableRowOrthogonality.diagonal (G := G) hrow (χ i)
  · have hμ : χ i ≠ χ j := fun h => hij (hχ h)
    rw [if_neg hij]
    simpa [characterTableRowPairing] using
      CharacterTableRowOrthogonality.offDiagonal (G := G) hrow hμ

theorem irreducibleCharacter_difference_inner_self_of_ne_zero
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner
        ((χ i : ClassFunction G ℂ) - (χ 0 : ClassFunction G ℂ))
        ((χ i : ClassFunction G ℂ) - (χ 0 : ClassFunction G ℂ)) = 2 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right]
  rw [irreducibleCharacter_inner_eq_if (G := G) hrow χ hχ i i]
  rw [irreducibleCharacter_inner_eq_if (G := G) hrow χ hχ i 0]
  rw [irreducibleCharacter_inner_eq_if (G := G) hrow χ hχ 0 i]
  rw [irreducibleCharacter_inner_eq_if (G := G) hrow χ hχ 0 0]
  simp [hi, eq_comm]
  norm_num

theorem irreducibleCharacter_difference_inner_of_ne_zero_of_ne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) {i j : Fin n}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner
        ((χ i : ClassFunction G ℂ) - (χ 0 : ClassFunction G ℂ))
        ((χ j : ClassFunction G ℂ) - (χ 0 : ClassFunction G ℂ)) = 1 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right]
  rw [irreducibleCharacter_inner_eq_if (G := G) hrow χ hχ i j]
  rw [irreducibleCharacter_inner_eq_if (G := G) hrow χ hχ i 0]
  rw [irreducibleCharacter_inner_eq_if (G := G) hrow χ hχ 0 j]
  rw [irreducibleCharacter_inner_eq_if (G := G) hrow χ hχ 0 0]
  simp [hi, hj, hij, eq_comm]

/-- The source-side difference `χ_i - χ_0` used in Peterfalvi §3 (1.4). -/
abbrev irreducibleCharacterDifference {n : ℕ} [NeZero n]
    (χ : Fin n → IrreducibleCharacter G) (i : Fin n) : ClassFunction G ℂ :=
  (χ i : ClassFunction G ℂ) - (χ 0 : ClassFunction G ℂ)

@[simp] theorem irreducibleCharacterDifference_zero
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G) :
    irreducibleCharacterDifference χ 0 = 0 := by
  simp [irreducibleCharacterDifference]

theorem irreducibleCharacterDifference_ne_zero
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) {i : Fin n} (hi : i ≠ 0) :
    irreducibleCharacterDifference χ i ≠ 0 := by
  intro h
  have hclass : (χ i : ClassFunction G ℂ) = (χ 0 : ClassFunction G ℂ) :=
    sub_eq_zero.mp h
  exact hi (hχ (IrreducibleCharacter.ext hclass))

theorem irreducibleCharacterDifference_eq_zero_iff
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) (i : Fin n) :
    irreducibleCharacterDifference χ i = 0 ↔ i = 0 := by
  constructor
  · intro h
    by_contra hi
    exact irreducibleCharacterDifference_ne_zero χ hχ hi h
  · intro hi
    subst hi
    simp

@[simp] theorem irreducibleCharacterDifference_apply_one
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G) (i : Fin n) :
    irreducibleCharacterDifference χ i (1 : G) =
      ((χ i : ClassFunction G ℂ) : G → ℂ) 1 -
        ((χ 0 : ClassFunction G ℂ) : G → ℂ) 1 :=
  rfl

theorem irreducibleCharacterDifference_apply_one_of_same_degree
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (h_same_degree :
      ∀ i, ((χ i : ClassFunction G ℂ) : G → ℂ) 1 =
        ((χ 0 : ClassFunction G ℂ) : G → ℂ) 1)
    (i : Fin n) :
    irreducibleCharacterDifference χ i (1 : G) = 0 := by
  simp [h_same_degree i]

theorem irreducibleCharacterDifference_inner_self_of_ne_zero
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner (irreducibleCharacterDifference χ i)
        (irreducibleCharacterDifference χ i) = 2 := by
  exact irreducibleCharacter_difference_inner_self_of_ne_zero (G := G) hrow χ hχ hi

theorem irreducibleCharacterDifference_inner_of_ne_zero_of_ne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) {i j : Fin n}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner (irreducibleCharacterDifference χ i)
        (irreducibleCharacterDifference χ j) = 1 := by
  exact irreducibleCharacter_difference_inner_of_ne_zero_of_ne
    (G := G) hrow χ hχ hi hj hij

/-- The image under an integral isometry of a source-side difference `χ_i - χ_0`. -/
abbrev isometryDifferenceImage {G H : Type*} [Group G] [Group H]
    {n : ℕ} [NeZero n]
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (χ : Fin n → IrreducibleCharacter H) (i : Fin n) : ClassFunction G ℂ :=
  τ (irreducibleCharacterDifference χ i)

@[simp] theorem isometryDifferenceImage_zero {G H : Type*} [Group G] [Group H]
    {n : ℕ} [NeZero n]
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (χ : Fin n → IrreducibleCharacter H) :
    isometryDifferenceImage τ χ 0 = 0 := by
  simp [isometryDifferenceImage]

/-- The degree-zero hypothesis for the images in Peterfalvi §3 (1.4).

In the textbook this comes from the map landing in the reduced virtual-character
lattice on `G#`; here it is kept as an explicit class-function condition until
that lattice target is part of the theorem statement. -/
def IsometryDifferenceImagesVanishAtOne {G H : Type*} [Group G] [Group H]
    {n : ℕ} [NeZero n]
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (χ : Fin n → IrreducibleCharacter H) : Prop :=
  ∀ i, isometryDifferenceImage τ χ i (1 : G) = 0

theorem isometryDifferenceImage_inner_self_of_ne_zero
    [Fintype G] [Fintype H]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := H))
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter H)
    (hχ : Function.Injective χ)
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (h_isom : ∀ i j,
        ClassFunction.inner (isometryDifferenceImage τ χ i)
          (isometryDifferenceImage τ χ j) =
        ClassFunction.inner (irreducibleCharacterDifference χ i)
          (irreducibleCharacterDifference χ j))
    {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner (isometryDifferenceImage τ χ i)
        (isometryDifferenceImage τ χ i) = 2 := by
  rw [h_isom i i]
  exact irreducibleCharacterDifference_inner_self_of_ne_zero
    (G := H) hrow χ hχ hi

theorem isometryDifferenceImage_inner_of_ne_zero_of_ne
    [Fintype G] [Fintype H]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := H))
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter H)
    (hχ : Function.Injective χ)
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (h_isom : ∀ i j,
        ClassFunction.inner (isometryDifferenceImage τ χ i)
          (isometryDifferenceImage τ χ j) =
        ClassFunction.inner (irreducibleCharacterDifference χ i)
          (irreducibleCharacterDifference χ j))
    {i j : Fin n} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner (isometryDifferenceImage τ χ i)
        (isometryDifferenceImage τ χ j) = 1 := by
  rw [h_isom i j]
  exact irreducibleCharacterDifference_inner_of_ne_zero_of_ne
    (G := H) hrow χ hχ hi hj hij

/-- The numeric data carried by the image differences in Peterfalvi §3 (1.4).

This is the interface between character theory and the finite combinatorial
argument: the zero row, degree-zero condition, norm `2`, and mutual inner
product `1` for distinct nonzero differences. -/
structure IsometryDifferencePairNumerics {n : ℕ} [NeZero n] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (v : Fin n → ClassFunction G ℂ) : Prop where
  zero : v 0 = 0
  degree_zero : ∀ i, v i (1 : G) = 0
  inner_self_of_ne_zero :
    ∀ ⦃i : Fin n⦄, i ≠ 0 → ClassFunction.inner (v i) (v i) = 2
  inner_of_ne_zero_of_ne :
    ∀ ⦃i j : Fin n⦄, i ≠ 0 → j ≠ 0 → i ≠ j →
      ClassFunction.inner (v i) (v j) = 1

namespace IsometryDifferencePairNumerics

variable {n : ℕ} [NeZero n] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {v : Fin n → ClassFunction G ℂ}

theorem inner_self (hv : IsometryDifferencePairNumerics v)
    {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner (v i) (v i) = 2 :=
  hv.inner_self_of_ne_zero hi

theorem inner_of_ne (hv : IsometryDifferencePairNumerics v)
    {i j : Fin n} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner (v i) (v j) = 1 :=
  hv.inner_of_ne_zero_of_ne hi hj hij

end IsometryDifferencePairNumerics

/-- The image differences of an isometric family satisfy the finite numeric
conditions needed by the later combinatorial proof core. -/
theorem isometryDifferencePairNumerics_of_isometryDifferenceImage
    [Fintype G] [Fintype H]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := H))
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter H)
    (hχ : Function.Injective χ)
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (h_image_degree_zero : IsometryDifferenceImagesVanishAtOne τ χ)
    (h_isom : ∀ i j,
        ClassFunction.inner (isometryDifferenceImage τ χ i)
          (isometryDifferenceImage τ χ j) =
        ClassFunction.inner (irreducibleCharacterDifference χ i)
          (irreducibleCharacterDifference χ j)) :
    IsometryDifferencePairNumerics
      (fun i => isometryDifferenceImage τ χ i) where
  zero := by
    simp
  degree_zero := h_image_degree_zero
  inner_self_of_ne_zero := by
    intro i hi
    exact isometryDifferenceImage_inner_self_of_ne_zero
      (G := G) (H := H) hrow χ hχ τ h_isom hi
  inner_of_ne_zero_of_ne := by
    intro i j hi hj hij
    exact isometryDifferenceImage_inner_of_ne_zero_of_ne
      (G := G) (H := H) hrow χ hχ τ h_isom hi hj hij

/-- A signed `n`-tuple of irreducible characters of `G`, used as the target
shape in Peterfalvi's difference-pair lemmas.

The theorem `isometry_difference_pair_structure` says that the image of
`χ_i - χ_0` is obtained from such a family as
`ε • (μ_i - μ_0)`. -/
structure SignedIrreducibleDifferenceFamily (G : Type*) [Group G] (n : ℕ) where
  mu : Fin n → IrreducibleCharacter G
  sign : ℤ
  sign_eq : sign = 1 ∨ sign = -1
  injective : Function.Injective mu

namespace SignedIrreducibleDifferenceFamily

variable {n : ℕ}

/-- The underlying class-function family. -/
abbrev classFunction (data : SignedIrreducibleDifferenceFamily G n)
    (i : Fin n) : ClassFunction G ℂ :=
  data.mu i

@[simp] theorem classFunction_apply
    (data : SignedIrreducibleDifferenceFamily G n) (i : Fin n) :
    data.classFunction i = (data.mu i : ClassFunction G ℂ) :=
  rfl

/-- The class-function family underlying a signed irreducible-difference family
is injective. -/
theorem classFunction_injective (data : SignedIrreducibleDifferenceFamily G n) :
    Function.Injective data.classFunction := by
  intro i j hij
  exact data.injective (IrreducibleCharacter.ext (by simpa [classFunction] using hij))

/-- Distinct indices give distinct underlying class functions. -/
theorem classFunction_ne (data : SignedIrreducibleDifferenceFamily G n)
    {i j : Fin n} (hij : i ≠ j) :
    data.classFunction i ≠ data.classFunction j := by
  intro h
  exact hij (data.classFunction_injective h)

/-- Every member of a signed irreducible-difference family is irreducible. -/
@[simp] theorem classFunction_irreducible
    (data : SignedIrreducibleDifferenceFamily G n) (i : Fin n) :
    IsIrreducibleCharacter (data.classFunction i) :=
  (data.mu i).isIrreducible

/-- The difference `μ_i - μ_0` attached to a signed irreducible-difference
family. -/
abbrev difference (data : SignedIrreducibleDifferenceFamily G n)
    [NeZero n] (i : Fin n) : ClassFunction G ℂ :=
  data.classFunction i - data.classFunction 0

@[simp] theorem difference_apply
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i : Fin n) :
    data.difference i = data.classFunction i - data.classFunction 0 :=
  rfl

@[simp] theorem difference_zero
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] :
    data.difference 0 = 0 := by
  simp [difference]

theorem difference_ne_zero
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    data.difference i ≠ 0 := by
  intro h
  have hclass : data.classFunction i = data.classFunction 0 := sub_eq_zero.mp h
  exact hi (data.classFunction_injective hclass)

theorem difference_eq_zero_iff
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i : Fin n) :
    data.difference i = 0 ↔ i = 0 := by
  constructor
  · intro h
    by_contra hi
    exact data.difference_ne_zero hi h
  · intro hi
    subst hi
    simp

/-- The difference family `μ_i - μ_0` is still injective. -/
theorem difference_injective
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] :
    Function.Injective data.difference := by
  intro i j hij
  have hclass : data.classFunction i = data.classFunction j := by
    have h := congrArg (fun φ : ClassFunction G ℂ => φ + data.classFunction 0) hij
    simpa [difference, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  exact data.classFunction_injective hclass

/-- The signed target difference `ε • (μ_i - μ_0)`. -/
abbrev signedDifference (data : SignedIrreducibleDifferenceFamily G n)
    [NeZero n] (i : Fin n) : ClassFunction G ℂ :=
  data.sign • data.difference i

@[simp] theorem signedDifference_apply
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i : Fin n) :
    data.signedDifference i = data.sign • data.difference i :=
  rfl

@[simp] theorem difference_apply_one
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i : Fin n) :
    data.difference i (1 : G) =
      data.classFunction i (1 : G) - data.classFunction 0 (1 : G) :=
  rfl

theorem signedDifference_apply_one_eq_zero_iff
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i : Fin n) :
    data.signedDifference i (1 : G) = 0 ↔ data.difference i (1 : G) = 0 := by
  rcases data.sign_eq with hsign | hsign
  · simp [signedDifference, hsign]
  · constructor
    · intro h
      have hneg : (-data.difference i) (1 : G) = 0 := by
        simpa [signedDifference, hsign] using h
      change -(data.difference i (1 : G)) = 0 at hneg
      exact neg_eq_zero.mp hneg
    · intro h
      have hneg : (-data.difference i) (1 : G) = 0 := by
        change -(data.difference i (1 : G)) = 0
        rw [h, neg_zero]
      simpa [signedDifference, hsign] using hneg

theorem signedDifference_apply_one_eq_zero_of_difference
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] {i : Fin n}
    (hi : data.difference i (1 : G) = 0) :
    data.signedDifference i (1 : G) = 0 :=
  (data.signedDifference_apply_one_eq_zero_iff i).mpr hi

theorem difference_apply_one_eq_zero_of_signedDifference
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] {i : Fin n}
    (hi : data.signedDifference i (1 : G) = 0) :
    data.difference i (1 : G) = 0 :=
  (data.signedDifference_apply_one_eq_zero_iff i).mp hi

@[simp] theorem signedDifference_zero
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] :
    data.signedDifference 0 = 0 := by
  simp [signedDifference]

theorem signedDifference_ne_zero
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    data.signedDifference i ≠ 0 := by
  rcases data.sign_eq with hsign | hsign
  · simpa [signedDifference, hsign] using data.difference_ne_zero hi
  · have hdiff : data.difference i ≠ 0 := data.difference_ne_zero hi
    have hneg : -data.difference i ≠ 0 := neg_ne_zero.mpr hdiff
    simpa [signedDifference, difference, hsign, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hneg

theorem signedDifference_eq_zero_iff
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i : Fin n) :
    data.signedDifference i = 0 ↔ i = 0 := by
  constructor
  · intro h
    by_contra hi
    exact data.signedDifference_ne_zero hi h
  · intro hi
    subst hi
    simp

theorem signedDifference_injective
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] :
    Function.Injective data.signedDifference := by
  intro i j hij
  apply data.difference_injective
  rcases data.sign_eq with hsign | hsign
  · simpa [signedDifference, hsign] using hij
  · have hneg : -data.difference i = -data.difference j := by
      simpa [signedDifference, hsign] using hij
    exact neg_inj.mp hneg

theorem signedDifference_eq_signedDifference_iff
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i j : Fin n) :
    data.signedDifference i = data.signedDifference j ↔ i = j := by
  constructor
  · intro h
    exact data.signedDifference_injective h
  · intro hij
    subst hij
    rfl

theorem signedDifference_ne
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] {i j : Fin n} (hij : i ≠ j) :
    data.signedDifference i ≠ data.signedDifference j := by
  intro h
  exact hij (data.signedDifference_injective h)

theorem signedDifference_eq_difference_or_neg
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i : Fin n) :
    data.signedDifference i = data.difference i ∨
      data.signedDifference i = -data.difference i := by
  rcases data.sign_eq with hsign | hsign
  · left
    simp [signedDifference, hsign]
  · right
    simp [signedDifference, hsign]

theorem sign_smul_signedDifference
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i : Fin n) :
    data.sign • data.signedDifference i = data.difference i := by
  rcases data.sign_eq with hsign | hsign
  · simp [signedDifference, hsign]
  · simp [signedDifference, hsign]

theorem sign_ne_zero (data : SignedIrreducibleDifferenceFamily G n) :
    data.sign ≠ 0 := by
  rcases data.sign_eq with hsign | hsign <;> simp [hsign]

theorem sign_mul_self (data : SignedIrreducibleDifferenceFamily G n) :
    data.sign * data.sign = 1 := by
  rcases data.sign_eq with hsign | hsign <;> simp [hsign]

theorem classFunction_inner_eq_if
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    (data : SignedIrreducibleDifferenceFamily G n) (i j : Fin n) :
    ClassFunction.inner (data.classFunction i) (data.classFunction j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [classFunction, characterTableRowPairing] using
      CharacterTableRowOrthogonality.diagonal (G := G) hrow (data.mu i)
  · have hμ : data.mu i ≠ data.mu j := fun h => hij (data.injective h)
    rw [if_neg hij]
    simpa [classFunction, characterTableRowPairing] using
      CharacterTableRowOrthogonality.offDiagonal (G := G) hrow hμ

theorem difference_inner_self_of_ne_zero
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner (data.difference i) (data.difference i) = 2 := by
  rw [difference, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right]
  rw [classFunction_inner_eq_if (G := G) hrow data i i]
  rw [classFunction_inner_eq_if (G := G) hrow data i 0]
  rw [classFunction_inner_eq_if (G := G) hrow data 0 i]
  rw [classFunction_inner_eq_if (G := G) hrow data 0 0]
  simp [hi, eq_comm]
  norm_num

theorem difference_inner_of_ne_zero_of_ne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    {i j : Fin n} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner (data.difference i) (data.difference j) = 1 := by
  rw [difference, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right]
  rw [classFunction_inner_eq_if (G := G) hrow data i j]
  rw [classFunction_inner_eq_if (G := G) hrow data i 0]
  rw [classFunction_inner_eq_if (G := G) hrow data 0 j]
  rw [classFunction_inner_eq_if (G := G) hrow data 0 0]
  simp [hi, hj, hij, eq_comm]

theorem signedDifference_inner_signedDifference
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n] (i j : Fin n) :
    ClassFunction.inner (data.signedDifference i) (data.signedDifference j) =
      ClassFunction.inner (data.difference i) (data.difference j) := by
  rcases data.sign_eq with hsign | hsign
  · simp [signedDifference, hsign]
  · calc
      ClassFunction.inner (data.signedDifference i) (data.signedDifference j) =
          ClassFunction.inner (-data.difference i) (-data.difference j) := by
            simp [signedDifference, hsign]
      _ = ClassFunction.inner (data.difference i) (data.difference j) := by
            rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg]

theorem signedDifference_inner_self_of_ne_zero
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner (data.signedDifference i) (data.signedDifference i) = 2 := by
  rw [signedDifference_inner_signedDifference]
  exact difference_inner_self_of_ne_zero (G := G) hrow data hi

theorem signedDifference_inner_of_ne_zero_of_ne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    {i j : Fin n} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner (data.signedDifference i) (data.signedDifference j) = 1 := by
  rw [signedDifference_inner_signedDifference]
  exact difference_inner_of_ne_zero_of_ne (G := G) hrow data hi hj hij

/-- A signed irreducible-difference family satisfies the same finite numeric
conditions once the degree-zero condition is supplied separately. -/
theorem numerics_of_signedDifference_vanishAtOne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hrow : CharacterTableRowOrthogonality (G := G))
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    (hvanish : ∀ i, data.signedDifference i (1 : G) = 0) :
    IsometryDifferencePairNumerics
      (fun i => data.signedDifference i) where
  zero := by
    simp
  degree_zero := hvanish
  inner_self_of_ne_zero := by
    intro i hi
    exact signedDifference_inner_self_of_ne_zero (G := G) hrow data hi
  inner_of_ne_zero_of_ne := by
    intro i j hi hj hij
    exact signedDifference_inner_of_ne_zero_of_ne (G := G) hrow data hi hj hij

end SignedIrreducibleDifferenceFamily

theorem signedDifference_vanishAtOne_of_isometryDifferenceImage_eq
    {n : ℕ} [NeZero n]
    (χ : Fin n → IrreducibleCharacter H)
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (data : SignedIrreducibleDifferenceFamily G n)
    (h_image : ∀ i, isometryDifferenceImage τ χ i = data.signedDifference i)
    (h_image_degree_zero : IsometryDifferenceImagesVanishAtOne τ χ) :
    ∀ i, data.signedDifference i (1 : G) = 0 := by
  intro i
  rw [← h_image i]
  exact h_image_degree_zero i

theorem difference_vanishAtOne_of_isometryDifferenceImage_eq
    {n : ℕ} [NeZero n]
    (χ : Fin n → IrreducibleCharacter H)
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (data : SignedIrreducibleDifferenceFamily G n)
    (h_image : ∀ i, isometryDifferenceImage τ χ i = data.signedDifference i)
    (h_image_degree_zero : IsometryDifferenceImagesVanishAtOne τ χ) :
    ∀ i, data.difference i (1 : G) = 0 := by
  intro i
  exact data.difference_apply_one_eq_zero_of_signedDifference
    (signedDifference_vanishAtOne_of_isometryDifferenceImage_eq
      (G := G) (H := H) χ τ data h_image h_image_degree_zero i)

variable [Fintype G] [Fintype H]

/-- **Orthonormal difference-pair structure under isometry**
([Peterfalvi §3 (1.4)] abstracted, also used in §5 (3.2), §6 (4.5), §7 (5.6)).

Given `n ≥ 2` distinct irreducible characters `χ : Fin n → Irr(H)`, all of
equal degree, and a `ℤ`-linear `τ : ClassFunction H ℂ → ClassFunction G ℂ` that preserves
the normalized inner product on the differences `χ i - χ 0`, the image of these
differences is built from a new orthonormal `n`-tuple `μ : Fin n → Irr(G)`
times a uniform sign `ε = ±1`.

This conditional form takes the signed irreducible-difference family `data`
together with the witnessing equalities `h_data : ∀ i, τ (χ i - χ 0) = data.signedDifference i`
as explicit hypotheses, mirroring the forward-dep pattern used elsewhere in
the project (e.g. Ch.7 `normal_J`, `thompson_normal_p_complement`,
`burnside_p_pow_q_pow`).  The actual construction of `data` from the isometry
hypothesis requires `SecondOrthogonality` + induction on `n` (split into
`issues/0025-peterfalvi-isometry-difference-core.md`).  Downstream consumers
in §3 (1.4) / §5 (3.2) / §6 (4.5) / §7 (5.6) apply this theorem by supplying
`data` and `h_data` from their own contexts. -/
theorem isometry_difference_pair_structure
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
    {n : ℕ} [NeZero n] (_hn : 2 ≤ n)
    (χ : Fin n → IrreducibleCharacter H)
    (_h_distinct : Function.Injective χ)
    (_h_same_degree :
      ∀ i, ((χ i : ClassFunction H ℂ) : H → ℂ) 1 =
        ((χ 0 : ClassFunction H ℂ) : H → ℂ) 1)
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (h_image_degree_zero : IsometryDifferenceImagesVanishAtOne τ χ)
    (h_isom : ∀ i j,
        ClassFunction.inner (isometryDifferenceImage τ χ i)
          (isometryDifferenceImage τ χ j) =
        ClassFunction.inner (irreducibleCharacterDifference χ i)
          (irreducibleCharacterDifference χ j)) :
    ∃ data : SignedIrreducibleDifferenceFamily G n,
      ∀ i, isometryDifferenceImage τ χ i = data.signedDifference i := by
  sorry

end OddOrder.RepresentationTheory
