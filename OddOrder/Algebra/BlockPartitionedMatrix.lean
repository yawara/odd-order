/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Block-partitioned square matrices have blocks of equal size

Let `M` be a square matrix with nonzero determinant, and suppose its rows and its columns are each
partitioned — by `f` and by `g` — so that `M i j = 0` whenever the row block of `i` and the column
block of `j` differ.  Then the two partitions have blocks of the same size.

This is the step in Navarro's proof of (5.12) where the block-diagonal form of the generalized
decomposition matrix is turned into the equality `k(B) = ∑_i ∑_{b^G = B} l(b)`.  Navarro phrases
it as "since `J` is regular, each `J_{B_i}` is square"; the proof here is the Leibniz formula
rather than a rank argument: a nonzero determinant forces a permutation `σ` with every
`M (σ j) j ≠ 0`, and such a `σ` matches the two partitions blockwise.

## Main results

* `OddOrder.Matrix.exists_perm_forall_ne_zero`
* `OddOrder.Matrix.card_eq_card_of_det_ne_zero`
-/

namespace OddOrder.Matrix

variable {n T R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **A nonzero determinant produces a permutation avoiding the zeros of the matrix.**  If every
permutation had a zero entry, every Leibniz term would vanish. -/
theorem exists_perm_forall_ne_zero {M : Matrix n n R} (hM : M.det ≠ 0) :
    ∃ σ : Equiv.Perm n, ∀ i, M (σ i) i ≠ 0 := by
  by_contra hcon
  refine hM ?_
  rw [_root_.Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨i, hi⟩ : ∃ i, M (σ i) i = 0 := by
    by_contra h
    exact hcon ⟨σ, fun i hz => h ⟨i, hz⟩⟩
  have hz : ∏ j, M (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [hz, smul_zero]

/-- **The blocks of a regular block-partitioned matrix have equal size.**  `f` assigns a block to
each row, `g` to each column, and `M` vanishes off the diagonal blocks. -/
theorem card_eq_card_of_det_ne_zero {M : Matrix n n R} (hM : M.det ≠ 0)
    {f g : n → T} (hblock : ∀ i j, f i ≠ g j → M i j = 0) (t : T) :
    Nat.card {i // f i = t} = Nat.card {j // g j = t} := by
  obtain ⟨σ, hσ⟩ := exists_perm_forall_ne_zero hM
  have hfg : ∀ j, f (σ j) = g j := fun j => by
    by_contra h
    exact hσ j (hblock _ _ h)
  exact (Nat.card_congr (Equiv.subtypeEquiv σ fun j => by rw [hfg j])).symm

end OddOrder.Matrix
