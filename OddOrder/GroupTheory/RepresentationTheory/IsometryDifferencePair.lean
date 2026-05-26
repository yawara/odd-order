/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Complex.Basic
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing

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

## Main statement

* `OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily`.
* `OddOrder.RepresentationTheory.isometry_difference_pair_structure`.

## References

* Peterfalvi §3 (1.4) (Tau isometry — core Dade preparation).
* Peterfalvi §5 (3.2), §6 (4.5), §7 (5.6) — re-uses the same abstraction.
* Isaacs, *Character Theory of Finite Groups*, Ch. 2 (character orthogonality).
-/

namespace OddOrder.RepresentationTheory

variable {G H : Type*} [Group G] [Group H]

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

end SignedIrreducibleDifferenceFamily

variable [Fintype G] [Fintype H]

/-- **Orthonormal difference-pair structure under isometry**
([Peterfalvi §3 (1.4)] abstracted, also used in §5 (3.2), §6 (4.5), §7 (5.6)).

Given `n ≥ 2` distinct irreducible characters `χ : Fin n → Irr(H)`, all of
equal degree, and a `ℤ`-linear `τ : ClassFunction H ℂ → ClassFunction G ℂ` that preserves
the normalized inner product on the differences `χ i - χ 0`, the image of these
differences is built from a new orthonormal `n`-tuple `μ : Fin n → Irr(G)`
times a uniform sign `ε = ±1`.

(Proof deferred: requires `SecondOrthogonality` + induction on `n`.) -/
theorem isometry_difference_pair_structure
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (χ : Fin n → IrreducibleCharacter H)
    (h_distinct : Function.Injective χ)
    (h_same_degree :
      ∀ i, ((χ i : ClassFunction H ℂ) : H → ℂ) 1 =
        ((χ 0 : ClassFunction H ℂ) : H → ℂ) 1)
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (h_isom : ∀ i j,
        ClassFunction.inner
          (τ ((χ i : ClassFunction H ℂ) - (χ 0 : ClassFunction H ℂ)))
          (τ ((χ j : ClassFunction H ℂ) - (χ 0 : ClassFunction H ℂ))) =
        ClassFunction.inner
          ((χ i : ClassFunction H ℂ) - (χ 0 : ClassFunction H ℂ))
          ((χ j : ClassFunction H ℂ) - (χ 0 : ClassFunction H ℂ))) :
    ∃ data : SignedIrreducibleDifferenceFamily G n,
      ∀ i, τ ((χ i : ClassFunction H ℂ) - (χ 0 : ClassFunction H ℂ)) =
        data.signedDifference i := by
  sorry

end OddOrder.RepresentationTheory
