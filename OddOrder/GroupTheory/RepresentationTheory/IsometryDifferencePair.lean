/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Complex.Basic
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing
import OddOrder.GroupTheory.RepresentationTheory.RowOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

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
    {n : ℕ} (χ : Fin n → IrreducibleCharacter G) (hχ : Function.Injective χ)
    (i j : Fin n) :
    ClassFunction.inner (χ i : ClassFunction G ℂ) (χ j : ClassFunction G ℂ) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [characterTableRowPairing] using
      CharacterTableRowOrthogonality.diagonal (G := G) characterTableRowOrthogonality (χ i)
  · have hμ : χ i ≠ χ j := fun h => hij (hχ h)
    rw [if_neg hij]
    simpa [characterTableRowPairing] using
      CharacterTableRowOrthogonality.offDiagonal (G := G) characterTableRowOrthogonality hμ

theorem irreducibleCharacter_difference_inner_self_of_ne_zero
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner
        ((χ i : ClassFunction G ℂ) - (χ 0 : ClassFunction G ℂ))
        ((χ i : ClassFunction G ℂ) - (χ 0 : ClassFunction G ℂ)) = 2 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right]
  rw [irreducibleCharacter_inner_eq_if (G := G) χ hχ i i]
  rw [irreducibleCharacter_inner_eq_if (G := G) χ hχ i 0]
  rw [irreducibleCharacter_inner_eq_if (G := G) χ hχ 0 i]
  rw [irreducibleCharacter_inner_eq_if (G := G) χ hχ 0 0]
  simp [hi, eq_comm]
  norm_num

theorem irreducibleCharacter_difference_inner_of_ne_zero_of_ne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) {i j : Fin n}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner
        ((χ i : ClassFunction G ℂ) - (χ 0 : ClassFunction G ℂ))
        ((χ j : ClassFunction G ℂ) - (χ 0 : ClassFunction G ℂ)) = 1 := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right]
  rw [irreducibleCharacter_inner_eq_if (G := G) χ hχ i j]
  rw [irreducibleCharacter_inner_eq_if (G := G) χ hχ i 0]
  rw [irreducibleCharacter_inner_eq_if (G := G) χ hχ 0 j]
  rw [irreducibleCharacter_inner_eq_if (G := G) χ hχ 0 0]
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
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner (irreducibleCharacterDifference χ i)
        (irreducibleCharacterDifference χ i) = 2 := by
  exact irreducibleCharacter_difference_inner_self_of_ne_zero (G := G) χ hχ hi

theorem irreducibleCharacterDifference_inner_of_ne_zero_of_ne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {n : ℕ} [NeZero n] (χ : Fin n → IrreducibleCharacter G)
    (hχ : Function.Injective χ) {i j : Fin n}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner (irreducibleCharacterDifference χ i)
        (irreducibleCharacterDifference χ j) = 1 := by
  exact irreducibleCharacter_difference_inner_of_ne_zero_of_ne
    (G := G) χ hχ hi hj hij

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

/-- The virtual-character hypothesis for the images in Peterfalvi §3 (1.4).

Peterfalvi's `τ : ℤ[X, H#] → ℤ[Irr G]` carries virtual characters to virtual
characters; the integer-linear formulation `τ : ClassFunction H ℂ →ₗ[ℤ]
ClassFunction G ℂ` is broader, so the virtual-character target needs to be
recorded as a separate hypothesis on the inputs we feed into the structure
theorem. -/
def IsometryDifferenceImagesAreVirtual {G H : Type*} [Group G] [Group H]
    {n : ℕ} [NeZero n]
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (χ : Fin n → IrreducibleCharacter H) : Prop :=
  ∀ i, isometryDifferenceImage τ χ i ∈ ZIrr G

theorem isometryDifferenceImage_inner_self_of_ne_zero
    [Fintype G] [Fintype H]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
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
    (G := H) χ hχ hi

theorem isometryDifferenceImage_inner_of_ne_zero_of_ne
    [Fintype G] [Fintype H]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
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
    (G := H) χ hχ hi hj hij

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
      (G := G) (H := H) χ hχ τ h_isom hi
  inner_of_ne_zero_of_ne := by
    intro i j hi hj hij
    exact isometryDifferenceImage_inner_of_ne_zero_of_ne
      (G := G) (H := H) χ hχ τ h_isom hi hj hij

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
    (data : SignedIrreducibleDifferenceFamily G n) (i j : Fin n) :
    ClassFunction.inner (data.classFunction i) (data.classFunction j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [classFunction, characterTableRowPairing] using
      CharacterTableRowOrthogonality.diagonal (G := G) characterTableRowOrthogonality (data.mu i)
  · have hμ : data.mu i ≠ data.mu j := fun h => hij (data.injective h)
    rw [if_neg hij]
    simpa [classFunction, characterTableRowPairing] using
      CharacterTableRowOrthogonality.offDiagonal (G := G) characterTableRowOrthogonality hμ

theorem difference_inner_self_of_ne_zero
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner (data.difference i) (data.difference i) = 2 := by
  rw [difference, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right]
  rw [classFunction_inner_eq_if (G := G) data i i]
  rw [classFunction_inner_eq_if (G := G) data i 0]
  rw [classFunction_inner_eq_if (G := G) data 0 i]
  rw [classFunction_inner_eq_if (G := G) data 0 0]
  simp [hi, eq_comm]
  norm_num

theorem difference_inner_of_ne_zero_of_ne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    {i j : Fin n} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner (data.difference i) (data.difference j) = 1 := by
  rw [difference, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right]
  rw [classFunction_inner_eq_if (G := G) data i j]
  rw [classFunction_inner_eq_if (G := G) data i 0]
  rw [classFunction_inner_eq_if (G := G) data 0 j]
  rw [classFunction_inner_eq_if (G := G) data 0 0]
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
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    {i : Fin n} (hi : i ≠ 0) :
    ClassFunction.inner (data.signedDifference i) (data.signedDifference i) = 2 := by
  rw [signedDifference_inner_signedDifference]
  exact difference_inner_self_of_ne_zero (G := G) data hi

theorem signedDifference_inner_of_ne_zero_of_ne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    {i j : Fin n} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ClassFunction.inner (data.signedDifference i) (data.signedDifference j) = 1 := by
  rw [signedDifference_inner_signedDifference]
  exact difference_inner_of_ne_zero_of_ne (G := G) data hi hj hij

/-- A signed irreducible-difference family satisfies the same finite numeric
conditions once the degree-zero condition is supplied separately. -/
theorem numerics_of_signedDifference_vanishAtOne
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (data : SignedIrreducibleDifferenceFamily G n) [NeZero n]
    (hvanish : ∀ i, data.signedDifference i (1 : G) = 0) :
    IsometryDifferencePairNumerics
      (fun i => data.signedDifference i) where
  zero := by
    simp
  degree_zero := hvanish
  inner_self_of_ne_zero := by
    intro i hi
    exact signedDifference_inner_self_of_ne_zero (G := G) data hi
  inner_of_ne_zero_of_ne := by
    intro i j hi hj hij
    exact signedDifference_inner_of_ne_zero_of_ne (G := G) data hi hj hij

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

open scoped Classical in
/-- Expanding `⟨α - β, γ - δ⟩` for irreducible characters: each summand is a Kronecker
delta by `irreducibleCharacter_inner_eq_ite`. -/
theorem irreducibleCharacter_inner_sub_sub_eq_ite
    [Invertible (Nat.card G : ℂ)]
    (α β γ δ : IrreducibleCharacter G) :
    ClassFunction.inner
        ((α : ClassFunction G ℂ) - (β : ClassFunction G ℂ))
        ((γ : ClassFunction G ℂ) - (δ : ClassFunction G ℂ)) =
      (if α = γ then (1 : ℂ) else 0) - (if α = δ then (1 : ℂ) else 0)
        - (if β = γ then (1 : ℂ) else 0) + (if β = δ then (1 : ℂ) else 0) := by
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right,
      irreducibleCharacter_inner_eq_ite α γ, irreducibleCharacter_inner_eq_ite α δ,
      irreducibleCharacter_inner_eq_ite β γ, irreducibleCharacter_inner_eq_ite β δ]
  ring

/-- **Cross-pair classification (Type A / Type B).**
If `⟨α - β, γ - δ⟩ = 1` for distinct irreducible characters `α ≠ β`, `γ ≠ δ`, then
exactly one of the following holds:

* (Type A) `α = γ`, with `α ≠ δ`, `β ≠ γ`, `β ≠ δ` — the "α positions agree";
* (Type B) `β = δ`, with `α ≠ γ`, `α ≠ δ`, `β ≠ γ` — the "β positions agree".

Both branches imply `α ≠ δ ∧ β ≠ γ`.

Proof: expanding the inner product into four Kronecker deltas and ruling out the
combinations that violate `α ≠ β` or `γ ≠ δ` leaves only sum patterns whose value is
`1` exactly when one of the two cases above holds.  This is the integer-equality core
of Peterfalvi §3 (1.4) uniform-sign argument. -/
theorem irreducibleCharacter_cross_pair_classify
    [Invertible (Nat.card G : ℂ)]
    {α β γ δ : IrreducibleCharacter G}
    (hαβ : α ≠ β) (hγδ : γ ≠ δ)
    (h_inner : ClassFunction.inner
        ((α : ClassFunction G ℂ) - (β : ClassFunction G ℂ))
        ((γ : ClassFunction G ℂ) - (δ : ClassFunction G ℂ)) = 1) :
    (α = γ ∧ α ≠ δ ∧ β ≠ γ ∧ β ≠ δ) ∨
      (α ≠ γ ∧ α ≠ δ ∧ β ≠ γ ∧ β = δ) := by
  classical
  rw [irreducibleCharacter_inner_sub_sub_eq_ite] at h_inner
  by_cases hαγ : α = γ
  · have hαδ : α ≠ δ := fun h => hγδ (hαγ.symm.trans h)
    have hβγ : β ≠ γ := fun h => hαβ (hαγ.trans h.symm)
    by_cases hβδ : β = δ
    · exfalso
      rw [if_pos hαγ, if_neg hαδ, if_neg hβγ, if_pos hβδ] at h_inner
      norm_num at h_inner
    · exact Or.inl ⟨hαγ, hαδ, hβγ, hβδ⟩
  · by_cases hβδ : β = δ
    · have hαδ : α ≠ δ := fun h => hαβ (h.trans hβδ.symm)
      have hβγ : β ≠ γ := fun h => hγδ (h.symm.trans hβδ)
      exact Or.inr ⟨hαγ, hαδ, hβγ, hβδ⟩
    · exfalso
      rw [if_neg hαγ, if_neg hβδ] at h_inner
      by_cases hαδ : α = δ
      · by_cases hβγ : β = γ
        · rw [if_pos hαδ, if_pos hβγ] at h_inner; norm_num at h_inner
        · rw [if_pos hαδ, if_neg hβγ] at h_inner; norm_num at h_inner
      · by_cases hβγ : β = γ
        · rw [if_neg hαδ, if_pos hβγ] at h_inner; norm_num at h_inner
        · rw [if_neg hαδ, if_neg hβγ] at h_inner; norm_num at h_inner

/-- **Orthonormal difference-pair structure under isometry**
([Peterfalvi §3 (1.4)] abstracted, also used in §5 (3.2), §6 (4.5), §7 (5.6)).

Given `n ≥ 2` distinct irreducible characters `χ : Fin n → Irr(H)`, all of
equal degree, and a `ℤ`-linear `τ : ClassFunction H ℂ → ClassFunction G ℂ` such
that, on each difference `χ_i - χ_0`, the image lies in `ZIrr G`, vanishes at
`1 : G`, and preserves the normalized inner product, the conclusion is the
existence of a `SignedIrreducibleDifferenceFamily G n` whose signed differences
coincide with the images.  Equivalently: the image is built from a new
orthonormal `n`-tuple `μ : Fin n → Irr(G)` times a uniform sign `ε = ±1`.

The three hypotheses on `τ` correspond to Peterfalvi's textbook setup:

* `h_image_virtual` — Peterfalvi's `τ : ℤ[X, H#] → ℤ[Irr G]` is virtual-character
  preserving; required to identify the image in `ZIrr G`.
* `h_image_degree_zero` — character differences vanish at `1` on the source,
  and the isometry preserves this.
* `h_isom` — the normalized inner product is preserved on the `χ_i - χ_0`.

The proof goes through `exists_irr_sub_irr_of_inner_self_two`
(`ZIrrFourier`): each image `τ (χ_i - χ_0) ∈ ZIrr G` of squared norm `2` vanishing at
`1` is a difference `α_i - β_i` of two named irreducibles.  The uniform sign emerges
from `irreducibleCharacter_cross_pair_classify` applied to a fixed index `i = 1`:
every distinct nonzero index falls into "Type A" (sharing the `α` slot with `1`) or
"Type B" (sharing the `β` slot with `1`), and a triangle-style argument across three
indices forces a single global type.  In Type A the family is built from the shared
`α_1` with sign `-1`; in Type B from the shared `β_1` with sign `+1`.
See `issues/0025-peterfalvi-isometry-difference-core.md` for the recipe.
Downstream consumers in §3 (1.4) / §5 (3.2) / §6 (4.5) / §7 (5.6) apply this
theorem by supplying the three hypotheses from their own contexts. -/
theorem isometry_difference_pair_structure
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
    {n : ℕ} [NeZero n] (_hn : 2 ≤ n)
    (χ : Fin n → IrreducibleCharacter H)
    (_h_distinct : Function.Injective χ)
    (_h_same_degree :
      ∀ i, ((χ i : ClassFunction H ℂ) : H → ℂ) 1 =
        ((χ 0 : ClassFunction H ℂ) : H → ℂ) 1)
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (h_image_virtual : IsometryDifferenceImagesAreVirtual τ χ)
    (h_image_degree_zero : IsometryDifferenceImagesVanishAtOne τ χ)
    (h_isom : ∀ i j,
        ClassFunction.inner (isometryDifferenceImage τ χ i)
          (isometryDifferenceImage τ χ j) =
        ClassFunction.inner (irreducibleCharacterDifference χ i)
          (irreducibleCharacterDifference χ j)) :
    ∃ data : SignedIrreducibleDifferenceFamily G n,
      ∀ i, isometryDifferenceImage τ χ i = data.signedDifference i := by
  classical
  -- Numerics: norm 2, distinct mutual inner product 1, zero at index 0, vanish at `1`
  have hnum : IsometryDifferencePairNumerics
      (fun i => isometryDifferenceImage τ χ i) :=
    isometryDifferencePairNumerics_of_isometryDifferenceImage χ _h_distinct τ
      h_image_degree_zero h_isom
  -- Bridge: each image `τ (χ_i - χ_0)` (i ≠ 0) is a difference of two named irreducibles
  have key : ∀ i : Fin n, i ≠ 0 →
      ∃ α β : IrreducibleCharacter G, α ≠ β ∧
        isometryDifferenceImage τ χ i =
          (α : ClassFunction G ℂ) - (β : ClassFunction G ℂ) := fun i hi =>
    exists_irr_sub_irr_of_inner_self_two
      (h_image_virtual i) (hnum.inner_self hi) (hnum.degree_zero i)
  -- Choice functions α_i, β_i for each i (default trivial for i = 0)
  let αFun : Fin n → IrreducibleCharacter G := fun i =>
    if h : i = 0 then trivialIrreducibleCharacter G
    else (key i h).choose
  let βFun : Fin n → IrreducibleCharacter G := fun i =>
    if h : i = 0 then trivialIrreducibleCharacter G
    else (key i h).choose_spec.choose
  have hα_def : ∀ i (hi : i ≠ 0), αFun i = (key i hi).choose := fun i hi => dif_neg hi
  have hβ_def : ∀ i (hi : i ≠ 0), βFun i = (key i hi).choose_spec.choose :=
    fun i hi => dif_neg hi
  have hαβFun : ∀ i (hi : i ≠ 0), αFun i ≠ βFun i := by
    intro i hi
    rw [hα_def i hi, hβ_def i hi]
    exact (key i hi).choose_spec.choose_spec.1
  have hvFun : ∀ i (hi : i ≠ 0),
      isometryDifferenceImage τ χ i =
        (αFun i : ClassFunction G ℂ) - (βFun i : ClassFunction G ℂ) := by
    intro i hi
    rw [hα_def i hi, hβ_def i hi]
    exact (key i hi).choose_spec.choose_spec.2
  -- Reference index `one : Fin n`
  let one : Fin n := ⟨1, by omega⟩
  have hone_val : (one : Fin n).val = 1 := rfl
  have hone_ne_zero : one ≠ 0 := by
    intro h
    have h1 : (1 : ℕ) = 0 := by
      have := congrArg Fin.val h
      rw [hone_val, Fin.val_zero] at this
      exact this
    exact absurd h1 (by omega)
  -- Cross inner product = 1 for distinct nonzero indices
  have hcross : ∀ i j : Fin n, i ≠ 0 → j ≠ 0 → i ≠ j →
      ClassFunction.inner
        ((αFun i : ClassFunction G ℂ) - (βFun i : ClassFunction G ℂ))
        ((αFun j : ClassFunction G ℂ) - (βFun j : ClassFunction G ℂ)) = 1 := by
    intro i j hi hj hij
    rw [← hvFun i hi, ← hvFun j hj]
    exact hnum.inner_of_ne hi hj hij
  -- Case split on global Type A (∃ k ≠ 0, k ≠ one, αFun one = αFun k) vs Type B
  by_cases hExA : ∃ k : Fin n, k ≠ 0 ∧ k ≠ one ∧ αFun one = αFun k
  · -- Type A globally: sign = -1, μ_0 := αFun one, μ_i := βFun i (i ≠ 0)
    obtain ⟨k₀, hk₀, hk₀ne, hAk₀⟩ := hExA
    -- (one, k₀) is Type A (since αFun one = αFun k₀)
    have h_oneK₀ :
        αFun one ≠ βFun k₀ ∧ βFun one ≠ αFun k₀ ∧ βFun one ≠ βFun k₀ := by
      have hcr := hcross one k₀ hone_ne_zero hk₀ hk₀ne.symm
      rcases irreducibleCharacter_cross_pair_classify
          (hαβFun one hone_ne_zero) (hαβFun k₀ hk₀) hcr with
        ⟨_, h1, h2, h3⟩ | ⟨hne, _, _, _⟩
      · exact ⟨h1, h2, h3⟩
      · exact absurd hAk₀ hne
    obtain ⟨hαβ_one_k₀, hβα_one_k₀, hβ_ne_k₀⟩ := h_oneK₀
    -- Global Type A: for all k ≠ 0, αFun k = αFun one
    have hαAll : ∀ k : Fin n, k ≠ 0 → αFun k = αFun one := by
      intro k hk
      by_cases hkOne : k = one
      · subst hkOne; rfl
      by_cases hkk₀ : k = k₀
      · subst hkk₀; exact hAk₀.symm
      have hk₀k : k₀ ≠ k := fun h => hkk₀ h.symm
      have hcr_onek := hcross one k hone_ne_zero hk (Ne.symm hkOne)
      rcases irreducibleCharacter_cross_pair_classify
          (hαβFun one hone_ne_zero) (hαβFun k hk) hcr_onek with
        ⟨hα_eq, _, _, _⟩ | ⟨hα_ne, _, _, hβ_eq⟩
      · exact hα_eq.symm
      -- Type B at (one, k): contradiction via (k₀, k)
      exfalso
      have hcr_k₀k := hcross k₀ k hk₀ hk hk₀k
      rcases irreducibleCharacter_cross_pair_classify
          (hαβFun k₀ hk₀) (hαβFun k hk) hcr_k₀k with
        ⟨hαk₀k, _, _, _⟩ | ⟨_, _, _, hβk₀k⟩
      · exact hα_ne (hAk₀.trans hαk₀k)
      · exact hβ_ne_k₀ (hβ_eq.trans hβk₀k.symm)
    -- μFun: μ_0 := αFun one, μ_i := βFun i for i ≠ 0
    let μFun : Fin n → IrreducibleCharacter G :=
      Function.update βFun 0 (αFun one)
    have hμ0 : μFun 0 = αFun one := Function.update_self _ _ _
    have hμne : ∀ i, i ≠ 0 → μFun i = βFun i := fun i hi =>
      Function.update_of_ne hi _ _
    -- Injectivity of μFun
    have hμInj : Function.Injective μFun := by
      intro i j hij
      by_cases hi : i = 0
      · by_cases hj : j = 0
        · exact hi.trans hj.symm
        exfalso
        rw [hi, hμ0, hμne j hj] at hij
        -- hij : αFun one = βFun j; but αFun j = αFun one and αFun j ≠ βFun j
        exact hαβFun j hj ((hαAll j hj).trans hij)
      by_cases hj : j = 0
      · exfalso
        rw [hμne i hi, hj, hμ0] at hij
        -- hij : βFun i = αFun one; but αFun i = αFun one and αFun i ≠ βFun i
        exact hαβFun i hi ((hαAll i hi).trans hij.symm)
      rw [hμne i hi, hμne j hj] at hij
      by_contra hne
      have hcr_ij := hcross i j hi hj hne
      have hα_eq : αFun i = αFun j := (hαAll i hi).trans (hαAll j hj).symm
      rcases irreducibleCharacter_cross_pair_classify
          (hαβFun i hi) (hαβFun j hj) hcr_ij with
        ⟨_, _, _, hβ_ne⟩ | ⟨hα_ne, _, _, _⟩
      · exact hβ_ne hij
      · exact hα_ne hα_eq
    -- Construct data
    refine ⟨{ mu := μFun, sign := -1, sign_eq := Or.inr rfl, injective := hμInj }, ?_⟩
    intro i
    by_cases hi : i = 0
    · subst hi
      change isometryDifferenceImage τ χ 0 =
        (-1 : ℤ) • ((μFun 0 : ClassFunction G ℂ) - (μFun 0 : ClassFunction G ℂ))
      rw [isometryDifferenceImage_zero, sub_self, smul_zero]
    · rw [hvFun i hi]
      have hα_i : αFun i = αFun one := hαAll i hi
      change (αFun i : ClassFunction G ℂ) - (βFun i : ClassFunction G ℂ) =
        (-1 : ℤ) • ((μFun i : ClassFunction G ℂ) - (μFun 0 : ClassFunction G ℂ))
      rw [hμne i hi, hμ0, hα_i, neg_one_zsmul, neg_sub]
  · -- Type B globally: sign = 1, μ_0 := βFun one, μ_i := αFun i (i ≠ 0)
    push Not at hExA
    have hβAll : ∀ k : Fin n, k ≠ 0 → βFun k = βFun one := by
      intro k hk
      by_cases hkOne : k = one
      · subst hkOne; rfl
      have hcr_onek := hcross one k hone_ne_zero hk (Ne.symm hkOne)
      rcases irreducibleCharacter_cross_pair_classify
          (hαβFun one hone_ne_zero) (hαβFun k hk) hcr_onek with
        ⟨hα_eq, _, _, _⟩ | ⟨_, _, _, hβ_eq⟩
      · exact absurd hα_eq (hExA k hk hkOne)
      · exact hβ_eq.symm
    let μFun : Fin n → IrreducibleCharacter G :=
      Function.update αFun 0 (βFun one)
    have hμ0 : μFun 0 = βFun one := Function.update_self _ _ _
    have hμne : ∀ i, i ≠ 0 → μFun i = αFun i := fun i hi =>
      Function.update_of_ne hi _ _
    have hμInj : Function.Injective μFun := by
      intro i j hij
      by_cases hi : i = 0
      · by_cases hj : j = 0
        · exact hi.trans hj.symm
        exfalso
        rw [hi, hμ0, hμne j hj] at hij
        -- hij : βFun one = αFun j; but βFun j = βFun one and αFun j ≠ βFun j
        exact hαβFun j hj (hij.symm.trans (hβAll j hj).symm)
      by_cases hj : j = 0
      · exfalso
        rw [hμne i hi, hj, hμ0] at hij
        exact hαβFun i hi (hij.trans (hβAll i hi).symm)
      rw [hμne i hi, hμne j hj] at hij
      by_contra hne
      have hcr_ij := hcross i j hi hj hne
      have hβ_eq : βFun i = βFun j := (hβAll i hi).trans (hβAll j hj).symm
      rcases irreducibleCharacter_cross_pair_classify
          (hαβFun i hi) (hαβFun j hj) hcr_ij with
        ⟨_, _, _, hβ_ne⟩ | ⟨hα_ne, _, _, _⟩
      · exact hβ_ne hβ_eq
      · exact hα_ne hij
    refine ⟨{ mu := μFun, sign := 1, sign_eq := Or.inl rfl, injective := hμInj }, ?_⟩
    intro i
    by_cases hi : i = 0
    · subst hi
      change isometryDifferenceImage τ χ 0 =
        (1 : ℤ) • ((μFun 0 : ClassFunction G ℂ) - (μFun 0 : ClassFunction G ℂ))
      rw [isometryDifferenceImage_zero, sub_self, smul_zero]
    · rw [hvFun i hi]
      have hβ_i : βFun i = βFun one := hβAll i hi
      change (αFun i : ClassFunction G ℂ) - (βFun i : ClassFunction G ℂ) =
        (1 : ℤ) • ((μFun i : ClassFunction G ℂ) - (μFun 0 : ClassFunction G ℂ))
      rw [hμne i hi, hμ0, hβ_i, one_zsmul]

namespace SignedIrreducibleDifferenceFamily

/-! ### Cross-family matching

Two signed irreducible-difference families whose difference families are pairwise
orthogonal have disjoint irreducible supports.  This is the cross-column matching step of
the Coq `primeTIirr_spec` construction (`PFsection4.v:296-330`, `inj_Imu`): the per-column
families extracted by `isometry_difference_pair_structure` from the `ω`-grid columns
assemble into a jointly injective (hence jointly orthonormal) grid `μ_{ij}`. -/

/-- Orthogonality of the signed differences descends to the unsigned differences: the two
signs multiply to a unit.  (The converse holds by the same computation; this direction is
the one used when the signed differences are identified with isometric images.) -/
theorem inner_difference_eq_zero_of_signedDifference
    [Invertible (Nat.card G : ℂ)]
    {n m : ℕ} [NeZero n] [NeZero m]
    (data : SignedIrreducibleDifferenceFamily G n)
    (data' : SignedIrreducibleDifferenceFamily G m) {i : Fin n} {j : Fin m}
    (h : ClassFunction.inner (data.signedDifference i) (data'.signedDifference j) = 0) :
    ClassFunction.inner (data.difference i) (data'.difference j) = 0 := by
  rw [← data.sign_smul_signedDifference i, ← data'.sign_smul_signedDifference j,
    ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, h, mul_zero, mul_zero]

/-- **Cross-family disjointness from difference orthogonality** (Coq `PFsection4.v:296-330`,
the `inj_Imu` cross-column matching).  If the difference families of two signed
irreducible-difference families, each with at least two members, are pairwise orthogonal,
then their irreducible supports are disjoint: `μ_i ≠ μ'_j` for all `i, j`.

Expanding `⟨μ_i - μ_0, μ'_j - μ'_0⟩ = 0` into Kronecker deltas: the anchors must differ
(else the relation at a nonzero index pair reads `-δ = 1`), no `μ_i` can hit the anchor
`μ'_0` and symmetrically no `μ'_j` can hit `μ_0` (else the family repeats a member), and
with all edge deltas zero every interior delta vanishes. -/
theorem mu_ne_of_forall_inner_difference_eq_zero
    [Invertible (Nat.card G : ℂ)]
    {n m : ℕ} [NeZero n] [NeZero m] (hn : 2 ≤ n) (hm : 2 ≤ m)
    (data : SignedIrreducibleDifferenceFamily G n)
    (data' : SignedIrreducibleDifferenceFamily G m)
    (horth : ∀ i j, ClassFunction.inner (data.difference i) (data'.difference j) = 0) :
    ∀ i j, data.mu i ≠ data'.mu j := by
  classical
  -- Kronecker expansion of each orthogonality relation.
  have hE : ∀ i j,
      (if data.mu i = data'.mu j then (1 : ℂ) else 0)
        - (if data.mu i = data'.mu 0 then (1 : ℂ) else 0)
        - (if data.mu 0 = data'.mu j then (1 : ℂ) else 0)
        + (if data.mu 0 = data'.mu 0 then (1 : ℂ) else 0) = 0 := by
    intro i j
    have h := horth i j
    simp only [difference_apply, classFunction_apply] at h
    rwa [irreducibleCharacter_inner_sub_sub_eq_ite] at h
  let one : Fin n := ⟨1, by omega⟩
  let one' : Fin m := ⟨1, by omega⟩
  have hone : one ≠ 0 := by
    intro h
    have h1 : (1 : ℕ) = 0 := by
      have := congrArg Fin.val h
      rw [Fin.val_zero] at this
      exact this
    exact absurd h1 (by omega)
  have hone' : one' ≠ 0 := by
    intro h
    have h1 : (1 : ℕ) = 0 := by
      have := congrArg Fin.val h
      rw [Fin.val_zero] at this
      exact this
    exact absurd h1 (by omega)
  -- Step 1: the anchors differ.
  have h00 : data.mu 0 ≠ data'.mu 0 := by
    intro h00
    have hE11 := hE one one'
    rw [if_pos h00,
      if_neg (fun hc : data.mu one = data'.mu 0 =>
        hone (data.injective (hc.trans h00.symm))),
      if_neg (fun hc : data.mu 0 = data'.mu one' =>
        hone' (data'.injective (h00.symm.trans hc)).symm)] at hE11
    by_cases hx : data.mu one = data'.mu one'
    · rw [if_pos hx] at hE11; norm_num at hE11
    · rw [if_neg hx] at hE11; norm_num at hE11
  -- Step 2: no member of `data` hits the anchor of `data'`.
  have hi0 : ∀ i, data.mu i ≠ data'.mu 0 := by
    intro i hc
    by_cases hi : i = 0
    · exact h00 (hi ▸ hc)
    · have hEi := hE i one'
      rw [if_pos hc, if_neg h00,
        if_neg (fun ha : data.mu i = data'.mu one' =>
          hone' (data'.injective (ha.symm.trans hc)))] at hEi
      by_cases hx : data.mu 0 = data'.mu one'
      · rw [if_pos hx] at hEi; norm_num at hEi
      · rw [if_neg hx] at hEi; norm_num at hEi
  -- Step 3: no member of `data'` hits the anchor of `data`.
  have h0j : ∀ j, data.mu 0 ≠ data'.mu j := by
    intro j hc
    by_cases hj : j = 0
    · exact h00 (hj ▸ hc)
    · have hEj := hE one j
      rw [if_pos hc, if_neg h00,
        if_neg (fun ha : data.mu one = data'.mu j =>
          hone (data.injective (ha.trans hc.symm)))] at hEj
      by_cases hx : data.mu one = data'.mu 0
      · rw [if_pos hx] at hEj; norm_num at hEj
      · rw [if_neg hx] at hEj; norm_num at hEj
  -- Step 4: interior deltas vanish.
  intro i j hc
  by_cases hi : i = 0
  · exact h0j j (hi ▸ hc)
  by_cases hj : j = 0
  · exact hi0 i (hj ▸ hc)
  have hEij := hE i j
  rw [if_pos hc, if_neg (hi0 i), if_neg (h0j j), if_neg h00] at hEij
  norm_num at hEij

end SignedIrreducibleDifferenceFamily

end OddOrder.RepresentationTheory
