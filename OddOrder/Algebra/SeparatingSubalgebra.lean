/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Pi

/-!
# A separating subalgebra of a finite product of copies of a field is everything

The central characters embed `Z(A)` modulo its radical into `∏_{i ∈ ι} k`
(`CentralCharacter`), and the block partition is by definition the partition of `ι` that this
image cannot separate.  To turn that into a decomposition of `Z(A)` one needs the converse: the
image contains the indicator function of each block, so that the block idempotents exist.

The general fact behind this is elementary: a unital subalgebra of `ι → k` (`ι` finite, `k` a
field) that separates two coordinates contains an element which is `1` at one and `0` at the
other, and multiplying those together produces the indicators.

## Main results

* `OddOrder.exists_mem_eq_one_eq_zero`
* `OddOrder.Subalgebra.eq_top_of_separates`
-/

namespace OddOrder

open Finset

variable {k ι : Type*} [Field k]

/-- If a subalgebra separates `i` from `j`, it contains an element that is `1` at `i` and `0`
at `j`. -/
theorem exists_mem_eq_one_eq_zero {S : Subalgebra k (ι → k)} {i j : ι}
    (h : ∃ s ∈ S, s i ≠ s j) : ∃ t : ι → k, t ∈ S ∧ t i = 1 ∧ t j = 0 := by
  obtain ⟨s, hs, hij⟩ := h
  have hne : s i - s j ≠ 0 := sub_ne_zero.mpr hij
  refine ⟨(s i - s j)⁻¹ • (s - Function.const ι (s j)), ?_, ?_, ?_⟩
  · exact S.smul_mem (S.sub_mem hs (S.algebraMap_mem (s j))) _
  · simpa using inv_mul_cancel₀ hne
  · simp

variable [Finite ι]

/-- **A subalgebra of `ι → k` that separates the coordinates is the whole thing.**  The
separating elements are multiplied together into the indicator of each coordinate. -/
theorem Subalgebra.eq_top_of_separates {S : Subalgebra k (ι → k)}
    (hsep : ∀ i j : ι, i ≠ j → ∃ s ∈ S, s i ≠ s j) : S = ⊤ := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  have hsingle : ∀ i : ι, (Pi.single i 1 : ι → k) ∈ S := by
    intro i
    have hex : ∀ j : ι, ∃ t : ι → k, t ∈ S ∧ t i = 1 ∧ (j ≠ i → t j = 0) := by
      intro j
      by_cases hj : j = i
      · exact ⟨1, S.one_mem, rfl, fun h => absurd hj h⟩
      · obtain ⟨t, ht, ht1, ht0⟩ := exists_mem_eq_one_eq_zero (S := S) (hsep i j (Ne.symm hj))
        exact ⟨t, ht, ht1, fun _ => ht0⟩
    choose t ht ht1 ht0 using hex
    have hprod : (∏ j ∈ univ.erase i, t j) = (Pi.single i 1 : ι → k) := by
      funext l
      rw [Finset.prod_apply]
      by_cases hl : l = i
      · subst hl
        rw [Pi.single_eq_same]
        exact Finset.prod_eq_one fun j _ => ht1 j
      · rw [Pi.single_eq_of_ne hl]
        exact Finset.prod_eq_zero (mem_erase.mpr ⟨hl, mem_univ l⟩) (ht0 l hl)
    rw [← hprod]
    exact S.prod_mem fun j _ => ht j
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x = ∑ i : ι, x i • (Pi.single i 1 : ι → k) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact S.sum_mem fun i _ => S.smul_mem (hsingle i) _

end OddOrder
