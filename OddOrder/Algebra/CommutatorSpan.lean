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

/-- **The iterated freshman's dream**: `p`-power maps are additive modulo `T` at every level. -/
theorem add_pow_prime_pow_sub_sub_mem {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0) (m : ℕ)
    (x y : A) : (x + y) ^ p ^ m - x ^ p ^ m - y ^ p ^ m ∈ commutatorSpan k A := by
  induction m with
  | zero => simp
  | succ m ih =>
    set u := (x + y) ^ p ^ m with hu
    set v := x ^ p ^ m with hv
    set w := y ^ p ^ m with hw
    have ht : v + w + (u - v - w) = u := by abel
    have h1 : (v + w + (u - v - w)) ^ p - (v + w) ^ p - (u - v - w) ^ p
        ∈ commutatorSpan k A :=
      add_pow_prime_sub_sub_mem _ _ hp hchar _ commutator_mem_toAddSubgroup
    have h2 : (v + w) ^ p - v ^ p - w ^ p ∈ commutatorSpan k A :=
      add_pow_prime_sub_sub_mem _ _ hp hchar _ commutator_mem_toAddSubgroup
    have h3 : (u - v - w) ^ p ∈ commutatorSpan k A := pow_mem_commutatorSpan hp hchar ih
    have hsplit : u ^ p - v ^ p - w ^ p
        = ((v + w + (u - v - w)) ^ p - (v + w) ^ p - (u - v - w) ^ p)
          + ((v + w) ^ p - v ^ p - w ^ p) + (u - v - w) ^ p := by
      rw [ht]; abel
    have hgoal : (x + y) ^ p ^ (m + 1) - x ^ p ^ (m + 1) - y ^ p ^ (m + 1)
        = u ^ p - v ^ p - w ^ p := by
      rw [hu, hv, hw, pow_succ, pow_mul, pow_mul, pow_mul]
    rw [hgoal, hsplit]
    exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3

/-- **The `p`-radical of the commutator span**: the elements some `p`-power of which is a sum of
commutators.  It is a subspace precisely because of the iterated freshman's dream and the
closure of `T` under `p`-th powers. -/
def commutatorRadical {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0) : Submodule k A where
  carrier := {x : A | ∃ m, x ^ p ^ m ∈ commutatorSpan k A}
  zero_mem' := ⟨1, by simp [zero_pow hp.pos.ne']⟩
  add_mem' := by
    rintro x y ⟨a, hx⟩ ⟨b, hy⟩
    refine ⟨max a b, ?_⟩
    have hx' : x ^ p ^ max a b ∈ commutatorSpan k A := by
      rw [show p ^ max a b = p ^ a * p ^ (max a b - a) by
        rw [← pow_add]; congr 1; omega, pow_mul]
      exact pow_pow_mem_commutatorSpan hp hchar _ hx
    have hy' : y ^ p ^ max a b ∈ commutatorSpan k A := by
      rw [show p ^ max a b = p ^ b * p ^ (max a b - b) by
        rw [← pow_add]; congr 1; omega, pow_mul]
      exact pow_pow_mem_commutatorSpan hp hchar _ hy
    have hadd := add_pow_prime_pow_sub_sub_mem (k := k) hp hchar (max a b) x y
    have : (x + y) ^ p ^ max a b
        = ((x + y) ^ p ^ max a b - x ^ p ^ max a b - y ^ p ^ max a b)
          + x ^ p ^ max a b + y ^ p ^ max a b := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.add_mem _ hadd hx') hy'
  smul_mem' := by
    rintro c x ⟨m, hx⟩
    refine ⟨m, ?_⟩
    have hcomm : (c • x) ^ p ^ m = c ^ p ^ m • x ^ p ^ m := by
      rw [Algebra.smul_def, Algebra.smul_def, map_pow]
      exact Commute.mul_pow (Algebra.commutes c x) _
    rw [hcomm]
    exact Submodule.smul_mem _ _ hx

theorem mem_commutatorRadical_iff {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0) {x : A} :
    x ∈ commutatorRadical (k := k) hp hchar ↔ ∃ m, x ^ p ^ m ∈ commutatorSpan k A := Iff.rfl

theorem commutatorSpan_le_commutatorRadical {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0) :
    commutatorSpan k A ≤ commutatorRadical (k := k) hp hchar := fun _ hx =>
  ⟨0, by simpa using hx⟩

end OddOrder
