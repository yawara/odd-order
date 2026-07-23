/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.Ring

/-!
# Higman Lemma 13: cancellation of commutator supports

G. Higman, *Suzuki 2-groups*, p. 93.  In the exponent-two branch,
Higman replaces generators by a nonzero linear combination that
commutes with one factor.  In the final all-isomorphic case he also
adds a third generator, choosing its coefficient so that the two
possible commutator supports are cancelled simultaneously.

This file isolates the elementary linear algebra behind those two
changes of generators.  The first lemma cancels one equation in two
coefficients.  The second cancels two equations in three coefficients
while ensuring that the first two coefficients do not both vanish.
The later group-theoretic layer supplies the commutator coordinates.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

/-- **Higman Lemma 13 (p. 93), one-support coefficient cancellation.**

For two coefficients over a field, there is a nonzero pair whose
linear combination vanishes.  This is the coefficient choice used for
`u₀ = αx₀ + βy₀` when the commutators with `W` have a single common
support. -/
theorem exists_nontrivial_pair_mul_add_mul_eq_zero
    {F : Type*} [Field F] (A B : F) :
    ∃ a b : F, (a ≠ 0 ∨ b ≠ 0) ∧ a * A + b * B = 0 := by
  by_cases hA : A = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hA]⟩
  · refine ⟨B, -A, Or.inr (neg_ne_zero.mpr hA), ?_⟩
    rw [mul_comm B A, neg_mul, add_neg_cancel]

/-- **Higman Lemma 13 (p. 93), two-support coefficient cancellation.**

Suppose two coordinate equations have coefficient columns
`(A₁, A₂)`, `(B₁, B₂)`, and `(C₁, C₂)`, and the last column is
nonzero.  Then one can choose coefficients `x`, `y`, and `z` that
cancel both equations, with `x` and `y` not both zero.  In Higman's
all-isomorphic case these are the coefficients of
`u₀ = αx₀ + βy₀ + γw₀` at the two possible commutator supports. -/
theorem exists_nontrivial_first_pair_cancel_two_linear_combinations
    {F : Type*} [Field F]
    (A₁ B₁ C₁ A₂ B₂ C₂ : F)
    (hC : C₁ ≠ 0 ∨ C₂ ≠ 0) :
    ∃ x y z : F,
      (x ≠ 0 ∨ y ≠ 0) ∧
        x * A₁ + y * B₁ + z * C₁ = 0 ∧
        x * A₂ + y * B₂ + z * C₂ = 0 := by
  obtain ⟨x, y, hxy, hrelation⟩ :=
    exists_nontrivial_pair_mul_add_mul_eq_zero
      (A₁ * C₂ - A₂ * C₁) (B₁ * C₂ - B₂ * C₁)
  rcases hC with hC₁ | hC₂
  · refine ⟨x * C₁, y * C₁, -(x * A₁ + y * B₁), ?_, ?_, ?_⟩
    · rcases hxy with hx | hy
      · exact Or.inl (mul_ne_zero hx hC₁)
      · exact Or.inr (mul_ne_zero hy hC₁)
    · ring
    · calc
        (x * C₁) * A₂ + (y * C₁) * B₂ +
            (-(x * A₁ + y * B₁)) * C₂ =
            -(x * (A₁ * C₂ - A₂ * C₁) +
              y * (B₁ * C₂ - B₂ * C₁)) := by ring
        _ = 0 := by rw [hrelation, neg_zero]
  · refine ⟨x * C₂, y * C₂, -(x * A₂ + y * B₂), ?_, ?_, ?_⟩
    · rcases hxy with hx | hy
      · exact Or.inl (mul_ne_zero hx hC₂)
      · exact Or.inr (mul_ne_zero hy hC₂)
    · calc
        (x * C₂) * A₁ + (y * C₂) * B₁ +
            (-(x * A₂ + y * B₂)) * C₁ =
            x * (A₁ * C₂ - A₂ * C₁) +
              y * (B₁ * C₂ - B₂ * C₁) := by ring
        _ = 0 := hrelation
    · ring

end OddOrder.Higman.Suzuki2Groups
