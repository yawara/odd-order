/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.Span.Basic
import OddOrder.Algebra.WordExpansion

/-!
# The commutator span of an algebra is closed under `p`-th powers

Brauer's count of the irreducible modular representations runs through the subspace

`T' = {x | ∃ m, x ^ (p ^ m) ∈ T}`,  `T = [A, A]`,

and for `T'` to be a subspace one needs `T` itself to be closed under `p`-th powers.  That
follows from the freshman's dream (`WordExpansion`) together with the fact that the `p`-th power
of a single commutator is again a commutator.

## Main results

* `OddOrder.pow_mem_commutatorSpan` — `t ∈ T ⟹ t ^ p ∈ T`
* `OddOrder.pow_pow_mem_commutatorSpan` — the same for every power `p ^ m`
-/

namespace OddOrder

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

variable (k A) in
/-- The `k`-span of the commutators of an algebra. -/
def commutatorSpan : Submodule k A :=
  Submodule.span k {z | ∃ a b : A, z = a * b - b * a}

theorem commutator_mem_commutatorSpan (a b : A) : a * b - b * a ∈ commutatorSpan k A :=
  Submodule.subset_span ⟨a, b, rfl⟩

theorem commutator_mem_toAddSubgroup (a b : A) :
    a * b - b * a ∈ (commutatorSpan k A).toAddSubgroup :=
  commutator_mem_commutatorSpan a b

/-- In characteristic `p`, `-1` is its own `p`-th power up to sign. -/
theorem neg_one_pow_prime {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0) : (-1 : A) ^ p = -1 := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have h2 : (1 : A) + 1 = 0 := by simpa [one_add_one_eq_two] using hchar
    rw [← eq_neg_of_add_eq_zero_left h2]
    simp
  · exact hodd.neg_one_pow

/-- **The commutator span is closed under `p`-th powers.** -/
theorem pow_mem_commutatorSpan {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0) {t : A}
    (ht : t ∈ commutatorSpan k A) : t ^ p ∈ commutatorSpan k A := by
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl⟩ := hz
    exact commutator_pow_mem a b hp hchar _ commutator_mem_toAddSubgroup
  | zero => rw [zero_pow hp.pos.ne']; exact Submodule.zero_mem _
  | add u v _ _ ihu ihv =>
    have hsub : (u + v) ^ p - u ^ p - v ^ p ∈ (commutatorSpan k A).toAddSubgroup :=
      add_pow_prime_sub_sub_mem u v hp hchar _ commutator_mem_toAddSubgroup
    have : (u + v) ^ p = ((u + v) ^ p - u ^ p - v ^ p) + u ^ p + v ^ p := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.add_mem _ hsub ihu) ihv
  | smul c u _ ihu =>
    have hcomm : (c • u) ^ p = c ^ p • u ^ p := by
      rw [Algebra.smul_def, Algebra.smul_def, map_pow]
      exact Commute.mul_pow (Algebra.commutes c u) p
    rw [hcomm]
    exact Submodule.smul_mem _ _ ihu

/-- **Every `p`-power of an element of the commutator span stays in it.** -/
theorem pow_pow_mem_commutatorSpan {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0) (m : ℕ) {t : A}
    (ht : t ∈ commutatorSpan k A) : t ^ p ^ m ∈ commutatorSpan k A := by
  induction m with
  | zero => simpa using ht
  | succ m ih => rw [pow_succ, pow_mul]; exact pow_mem_commutatorSpan hp hchar ih

end OddOrder
