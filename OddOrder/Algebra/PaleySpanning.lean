/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Paley-type spanning set of BG Appendix C, Problem 1

For `F = 𝔽_{3^q}` with `S ⊆ Fˣ` the subgroup of squares (equivalently, of norm-one elements), the
set

`T = { s ∈ F : s ∈ S and s + 1 ∈ S }`

spans `F` over `𝔽₃`.  This is **Lemma B** of `notes/bg/appC_problem1_partial_resolution.md`
(issue 0180), the one analytic-looking input of Theorem 1 — and it turns out to need no Weil
bound at all.  The elementary route is:

* `T = { v + v⁻¹ + 1 : v ∈ S, v ≠ 1 }`, a two-to-one parametrisation (solve `s = a²`,
  `s + 1 = b²`, put `u = b - a`; in characteristic three `s = (u - u⁻¹)² = u² + u⁻² + 1`);
* the elements of a non-trivial finite subgroup of `Fˣ` sum to zero
  (`FiniteField.sum_subgroup_units_eq_zero`), whence `∑_{s ∈ T} s = -1` and therefore `1 ∈ span T`;
* `|T| = (|F| - 3)/4 > 3^{q-2}` forces `dim span T ≥ q - 1`;
* `span T` is Galois-stable, and for `q ≠ 3` the only one-dimensional simple `𝔽₃[C_q]`-summand of
  `F` is the trivial one, so a proper `span T` would have to be `ker Tr` — impossible since
  `1 ∈ span T` and `Tr 1 = q ≠ 0`.

This file carries the algebraic ingredients of the second bullet.

## Main results

* `sum_add_inv_add_one` — `∑_{v ∈ S} (v + v⁻¹ + 1) = |S|` for a non-trivial finite subgroup `S`.
-/

namespace OddOrder.Paley

open Finset

variable {F : Type*} [Field F]

/-- Summing the inverses over a finite subgroup is the same as summing the elements: inversion
permutes the subgroup. -/
theorem sum_inv_eq_sum (S : Subgroup Fˣ) [Fintype S] :
    ∑ v : S, (((v : Fˣ)⁻¹ : Fˣ) : F) = ∑ v : S, ((v : Fˣ) : F) := by
  refine Fintype.sum_equiv (Equiv.inv S) _ _ ?_
  intro v
  simp

/-- **The sum behind `1 ∈ span T`.**  For a non-trivial finite subgroup `S` of the units of a
field, `∑_{v ∈ S} (v + v⁻¹ + 1) = |S|`.

Both `∑ v` and `∑ v⁻¹` vanish (`FiniteField.sum_subgroup_units_eq_zero`), so only the constant
term survives.  Pairing `v` with `v⁻¹` — a fixed-point-free involution on `S ∖ {1}` when
`-1 ∉ S` — turns this into `2 ∑_{s ∈ T} s = |S| - 3`, which in characteristic three gives
`∑_{s ∈ T} s = -1`. -/
theorem sum_add_inv_add_one (S : Subgroup Fˣ) [Fintype S] (hS : S ≠ ⊥) :
    ∑ v : S, (((v : Fˣ) : F) + (((v : Fˣ)⁻¹ : Fˣ) : F) + 1) = (Fintype.card S : F) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_inv_eq_sum,
    FiniteField.sum_subgroup_units_eq_zero hS]
  simp

end OddOrder.Paley
