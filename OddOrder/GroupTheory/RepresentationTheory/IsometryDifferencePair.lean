/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Complex.Basic
import OddOrder.GroupTheory.RepresentationTheory.ZIrr

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
  `IrreducibleCharacter` as the finite orthonormal index type, second
  orthogonality to identify the irreducible-character basis coefficients, and a
  separate finite integer-vector induction proving the uniform sign shape.

## Main statement

* `OddOrder.RepresentationTheory.isometry_difference_pair_structure`.

## References

* Peterfalvi §3 (1.4) (Tau isometry — core Dade preparation).
* Peterfalvi §5 (3.2), §6 (4.5), §7 (5.6) — re-uses the same abstraction.
* Isaacs, *Character Theory of Finite Groups*, Ch. 2 (character orthogonality).
-/

namespace OddOrder.RepresentationTheory

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]

/-- **Orthonormal difference-pair structure under isometry**
([Peterfalvi §3 (1.4)] abstracted, also used in §5 (3.2), §6 (4.5), §7 (5.6)).

Given `n ≥ 2` distinct irreducible characters `χ : Fin n → ClassFunction H ℂ`, all of
equal degree, and a `ℤ`-linear `τ : ClassFunction H ℂ → ClassFunction G ℂ` that preserves
the normalized inner product on the differences `χ i - χ 0`, the image of these
differences is built from a new orthonormal `n`-tuple `μ : Fin n → ClassFunction G ℂ`
times a uniform sign `ε = ±1`.

(Proof deferred: requires `SecondOrthogonality` + induction on `n`.) -/
theorem isometry_difference_pair_structure
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (χ : Fin n → ClassFunction H ℂ)
    (h_irr : ∀ i, IsIrreducibleCharacter (χ i))
    (h_distinct : Function.Injective χ)
    (h_same_degree : ∀ i, (χ i : H → ℂ) 1 = (χ 0 : H → ℂ) 1)
    (τ : ClassFunction H ℂ →ₗ[ℤ] ClassFunction G ℂ)
    (h_isom : ∀ i j,
        ClassFunction.inner (τ (χ i - χ 0)) (τ (χ j - χ 0)) =
        ClassFunction.inner (χ i - χ 0) (χ j - χ 0)) :
    ∃ (μ : Fin n → ClassFunction G ℂ) (ε : ℤ),
      (ε = 1 ∨ ε = -1) ∧
      Function.Injective μ ∧
      (∀ i, IsIrreducibleCharacter (μ i)) ∧
      (∀ i, τ (χ i - χ 0) = ε • (μ i - μ 0)) := by
  sorry

end OddOrder.RepresentationTheory
