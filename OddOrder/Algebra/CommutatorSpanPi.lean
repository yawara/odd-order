/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Pi
import OddOrder.Algebra.CommutatorSpan

/-!
# The commutator span of a finite product of algebras

By Artin–Wedderburn the semisimple quotient of a split finite-dimensional algebra is a product
of matrix algebras, so Brauer's count needs the commutator span and its `p`-radical to be
computed factorwise.  Both are: `T` is the product of the `T`'s (the non-trivial inclusion is
that `Pi.single i` maps commutators to commutators), and `T'` inherits the collapse `T' = T` from
the factors.

## Main results

* `OddOrder.commutatorSpan_pi`
* `OddOrder.commutatorRadical_pi_eq`
-/

namespace OddOrder

variable {k ι : Type*} {A : ι → Type*} [CommRing k] [∀ i, Ring (A i)] [∀ i, Algebra k (A i)]

section Single

variable [DecidableEq ι]

/-- The `i`-th coordinate embedding is multiplicative (it is a non-unital algebra map). -/
theorem single_mul_single_pi (i : ι) (a b : A i) :
    (Pi.single i a : ∀ j, A j) * Pi.single i b = Pi.single i (a * b) := by
  funext j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- **The coordinate embedding sends commutators to commutators.** -/
theorem single_mem_commutatorSpan_pi (i : ι) {t : A i} (ht : t ∈ commutatorSpan k (A i)) :
    (Pi.single i t : ∀ j, A j) ∈ commutatorSpan k (∀ j, A j) := by
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl⟩ := hz
    have hcomm : (Pi.single i (a * b - b * a) : ∀ j, A j)
        = Pi.single i a * Pi.single i b - Pi.single i b * Pi.single i a := by
      rw [single_mul_single_pi, single_mul_single_pi, ← Pi.single_sub]
    rw [hcomm]
    exact commutator_mem_commutatorSpan _ _
  | zero => simp
  | add u v _ _ hu hv => rw [Pi.single_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [Pi.single_smul]; exact Submodule.smul_mem _ _ hu

end Single

variable [Finite ι]

/-- **The commutator span of a product is the product of the commutator spans.** -/
theorem commutatorSpan_pi :
    commutatorSpan k (∀ i, A i) = Submodule.pi Set.univ fun i => commutatorSpan k (A i) := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  refine le_antisymm ?_ fun x hx => ?_
  · rw [commutatorSpan, Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_pi]
    intro i _
    exact commutator_mem_commutatorSpan (a i) (b i)
  · rw [← Finset.univ_sum_single x]
    exact Submodule.sum_mem _ fun i _ =>
      single_mem_commutatorSpan_pi i (Submodule.mem_pi.mp hx i (Set.mem_univ i))

variable {p : ℕ}

/-- **The `p`-radical of a product collapses as soon as it collapses factorwise.**  For a split
semisimple algebra every factor is a matrix algebra, where `T' = T` because the trace of a
`p`-power is the `p`-power of the trace. -/
theorem commutatorRadical_pi_eq (hp : p.Prime) (hchar : ∀ i, (p : A i) = 0)
    (hchar' : (p : ∀ i, A i) = 0)
    (hfac : ∀ i, commutatorRadical (k := k) hp (hchar i) = commutatorSpan k (A i)) :
    commutatorRadical (k := k) hp hchar' = commutatorSpan k (∀ i, A i) := by
  classical
  refine le_antisymm (fun x hx => ?_) (commutatorSpan_le_commutatorRadical _ _)
  obtain ⟨m, hm⟩ := hx
  rw [commutatorSpan_pi] at hm ⊢
  rw [Submodule.mem_pi] at hm ⊢
  intro i _
  refine (hfac i).le ⟨m, ?_⟩
  simpa using hm i (Set.mem_univ i)

end OddOrder
