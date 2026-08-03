/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
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

/-- `(-1) ^ (p ^ m) = -1` in characteristic `p`. -/
theorem neg_one_pow_prime_pow {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0) (m : ℕ) :
    (-1 : A) ^ p ^ m = -1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_mul, ih, neg_one_pow_prime hp hchar]

/-- The subtraction form of the iterated freshman's dream. -/
theorem sub_pow_prime_pow_sub_add_mem {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0) (m : ℕ)
    (x y : A) : (x - y) ^ p ^ m - x ^ p ^ m + y ^ p ^ m ∈ commutatorSpan k A := by
  have hneg : (-y) ^ p ^ m = -(y ^ p ^ m) := by
    rw [neg_pow, neg_one_pow_prime_pow hp hchar, neg_one_mul]
  have h := add_pow_prime_pow_sub_sub_mem (k := k) hp hchar m x (-y)
  rw [hneg, ← sub_eq_add_neg, sub_neg_eq_add] at h
  exact h

/-- **If some `p`-power of `x - y` vanishes, then `x - y` lies in the `p`-radical.**  This is the
form used for group elements: `g` and its `p'`-part have equal `p`-power. -/
theorem sub_mem_commutatorRadical_of_pow_eq {p : ℕ} (hp : p.Prime) (hchar : (p : A) = 0)
    {x y : A} {m : ℕ} (h : x ^ p ^ m = y ^ p ^ m) :
    x - y ∈ commutatorRadical (k := k) hp hchar := by
  refine ⟨m, ?_⟩
  have hsub := sub_pow_prime_pow_sub_add_mem (k := k) hp hchar m x y
  rw [h] at hsub
  simpa using hsub

/-! ### The Frobenius on the quotient

The `p`-power map descends to `A ⧸ [A, A]`; it is additive (freshman's dream) and semilinear
over the Frobenius of `k`.  The `p`-radical is exactly the set of elements eventually killed by
it, so counting `dim (A ⧸ T')` becomes a Fitting-type analysis of this map.
-/

section Frobenius

variable {p : ℕ}

/-- Congruent elements have congruent `p`-th powers. -/
theorem pow_sub_pow_mem_of_sub_mem (hp : p.Prime) (hchar : (p : A) = 0) {x y : A}
    (h : x - y ∈ commutatorSpan k A) :
    x ^ p - y ^ p ∈ commutatorSpan k A := by
  have hxy : x = y + (x - y) := by abel
  have hfr : (y + (x - y)) ^ p - y ^ p - (x - y) ^ p ∈ commutatorSpan k A :=
    add_pow_prime_sub_sub_mem _ _ hp hchar _ commutator_mem_toAddSubgroup
  have hpow : (x - y) ^ p ∈ commutatorSpan k A := pow_mem_commutatorSpan hp hchar h
  have hsum : x ^ p - y ^ p
      = ((y + (x - y)) ^ p - y ^ p - (x - y) ^ p) + (x - y) ^ p := by
    rw [← hxy]; abel
  rw [hsum]
  exact Submodule.add_mem _ hfr hpow

/-- **The `p`-power map on `A ⧸ [A, A]`.** -/
noncomputable def frobQuotient (hp : p.Prime) (hchar : (p : A) = 0) :
    (A ⧸ commutatorSpan k A) → (A ⧸ commutatorSpan k A) :=
  Quotient.map' (fun x => x ^ p) fun _ _ hxy =>
    (Submodule.quotientRel_def _).mpr
      (pow_sub_pow_mem_of_sub_mem hp hchar ((Submodule.quotientRel_def _).mp hxy))

@[simp]
theorem frobQuotient_mk (hp : p.Prime) (hchar : (p : A) = 0) (x : A) :
    frobQuotient hp hchar (Submodule.Quotient.mk x : A ⧸ commutatorSpan k A)
      = Submodule.Quotient.mk (x ^ p) := rfl

/-- The Frobenius on the quotient is additive: this is the freshman's dream. -/
theorem frobQuotient_add (hp : p.Prime) (hchar : (p : A) = 0)
    (u v : A ⧸ commutatorSpan k A) :
    frobQuotient hp hchar (u + v) = frobQuotient hp hchar u + frobQuotient hp hchar v := by
  obtain ⟨x, rfl⟩ := (commutatorSpan k A).mkQ_surjective u
  obtain ⟨y, rfl⟩ := (commutatorSpan k A).mkQ_surjective v
  simp only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_add, frobQuotient_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [show (x + y) ^ p - (x ^ p + y ^ p) = (x + y) ^ p - x ^ p - y ^ p by abel]
  exact add_pow_prime_sub_sub_mem _ _ hp hchar _ commutator_mem_toAddSubgroup

/-- The Frobenius on the quotient is semilinear over the Frobenius of `k`. -/
theorem frobQuotient_smul (hp : p.Prime) (hchar : (p : A) = 0) (c : k)
    (u : A ⧸ commutatorSpan k A) :
    frobQuotient hp hchar (c • u) = c ^ p • frobQuotient hp hchar u := by
  obtain ⟨x, rfl⟩ := (commutatorSpan k A).mkQ_surjective u
  simp only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, frobQuotient_mk]
  congr 1
  rw [Algebra.smul_def, Algebra.smul_def, map_pow]
  exact Commute.mul_pow (Algebra.commutes c x) p

/-- Iterating the Frobenius raises to the corresponding `p`-power. -/
theorem iterate_frobQuotient_mk (hp : p.Prime) (hchar : (p : A) = 0) (m : ℕ) (y : A) :
    (frobQuotient hp hchar)^[m] (Submodule.Quotient.mk y : A ⧸ commutatorSpan k A)
      = Submodule.Quotient.mk (y ^ p ^ m) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, frobQuotient_mk, ih, ← pow_mul, ← pow_succ']

/-- **The `p`-radical is exactly what the Frobenius eventually kills.** -/
theorem mem_commutatorRadical_iff_frobQuotient (hp : p.Prime) (hchar : (p : A) = 0)
    {x : A} :
    x ∈ commutatorRadical (k := k) hp hchar
      ↔ ∃ m, (frobQuotient hp hchar)^[m]
          (Submodule.Quotient.mk x : A ⧸ commutatorSpan k A) = 0 := by
  have hiter := iterate_frobQuotient_mk (k := k) hp hchar
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hiter, (Submodule.Quotient.mk_eq_zero _).mpr hm]⟩
  · rintro ⟨m, hm⟩
    rw [hiter] at hm
    exact ⟨m, (Submodule.Quotient.mk_eq_zero _).mp hm⟩

theorem iterate_frobQuotient_add (hp : p.Prime) (hchar : (p : A) = 0) (m : ℕ)
    (u v : A ⧸ commutatorSpan k A) :
    (frobQuotient hp hchar)^[m] (u + v)
      = (frobQuotient hp hchar)^[m] u + (frobQuotient hp hchar)^[m] v := by
  induction m generalizing u v with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, frobQuotient_add, ih]

theorem iterate_frobQuotient_smul (hp : p.Prime) (hchar : (p : A) = 0) (m : ℕ) (c : k)
    (u : A ⧸ commutatorSpan k A) :
    (frobQuotient hp hchar)^[m] (c • u) = c ^ p ^ m • (frobQuotient hp hchar)^[m] u := by
  induction m generalizing c u with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, frobQuotient_smul, ih,
      ← pow_mul, ← pow_succ']

theorem iterate_frobQuotient_zero (hp : p.Prime) (hchar : (p : A) = 0) (m : ℕ) :
    (frobQuotient hp hchar)^[m] (0 : A ⧸ commutatorSpan k A) = 0 := by
  have h := iterate_frobQuotient_mk (k := k) hp hchar m (0 : A)
  rw [zero_pow (pow_ne_zero m hp.pos.ne')] at h
  simpa using h

end Frobenius

end OddOrder
