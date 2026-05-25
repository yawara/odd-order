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
        data.sign • (data.classFunction i - data.classFunction 0) := by
  sorry

end OddOrder.RepresentationTheory
