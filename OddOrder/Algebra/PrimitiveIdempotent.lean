/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Idempotents
import OddOrder.Algebra.PiSimpleModule
import OddOrder.Algebra.MatrixCommutator

/-!
# Lifting the matrix units

The diagonal matrix units of `∏_{i ∈ ι} M_{n_i}(k)` — one for each pair `(i, j)` with `j` a row
of the `i`-th block — form a complete orthogonal family of idempotents.  Along a surjection
`π : A ↠ ∏_i M_{n_i}(k)` with nil kernel they lift to a complete orthogonal family in `A`
(mathlib's `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`).

For `A = kG` this is the decomposition `1 = ∑ f_x` into primitive idempotents; the modules
`A f_x` are the projective indecomposables, and counting composition factors in them is the
Cartan matrix.

## Main results

* `OddOrder.completeOrthogonalIdempotents_matrixUnit`
* `OddOrder.exists_completeOrthogonalIdempotents_lift`
-/

namespace OddOrder

open Matrix

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]

omit [Fintype ι] [DecidableEq ι] in
theorem sum_single_diag_eq_one (i : ι) :
    ∑ j : nn i, Matrix.single j j (1 : k) = 1 := by
  ext a b
  rw [Matrix.sum_apply]
  by_cases h : a = b
  · subst h
    rw [Matrix.one_apply_eq, Finset.sum_eq_single a] <;> simp +contextual
  · rw [Matrix.one_apply_ne h, Finset.sum_eq_zero]
    intro j _
    simp only [Matrix.single_apply]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h rfl

omit [Fintype ι] [∀ i, DecidableEq (nn i)] in
theorem single_mul_single_of_ne_index {i i' : ι} (h : i ≠ i')
    (a : Matrix (nn i) (nn i) k) (b : Matrix (nn i') (nn i') k) :
    (Pi.single i a : ∀ j, Matrix (nn j) (nn j) k) * Pi.single i' b = 0 := by
  funext l
  by_cases hl : i = l
  · subst hl
    simp [Pi.single_eq_of_ne h]
  · simp [Pi.single_eq_of_ne (Ne.symm hl)]

/-- **The diagonal matrix units are a complete orthogonal family of idempotents.** -/
theorem completeOrthogonalIdempotents_matrixUnit :
    CompleteOrthogonalIdempotents (fun x : Σ i, nn i =>
      (Pi.single x.1 (Matrix.single x.2 x.2 1) : ∀ j, Matrix (nn j) (nn j) k)) where
  idem x := by
    change _ * _ = _
    rw [PiModule.single_mul_single, Matrix.single_mul_single_same]
    simp
  ortho := by
    rintro ⟨i, a⟩ ⟨i', a'⟩ hxy
    by_cases hi : i = i'
    · subst hi
      have haa : a ≠ a' := fun h => hxy (by subst h; rfl)
      change _ * _ = _
      rw [PiModule.single_mul_single, Matrix.single_mul_single_of_ne _ _ _ _ haa]
      simp
    · exact single_mul_single_of_ne_index hi _ _
  complete := by
    have hinner : ∀ i : ι,
        ∑ j : nn i, (Pi.single i (Matrix.single j j 1) : ∀ l, Matrix (nn l) (nn l) k)
          = Pi.single i 1 := by
      intro i
      funext l
      rw [Finset.sum_apply]
      by_cases hl : i = l
      · subst hl
        simpa using sum_single_diag_eq_one (k := k) (nn := nn) i
      · simp [Pi.single_eq_of_ne (Ne.symm hl)]
    rw [Fintype.sum_sigma]
    simp only [hinner]
    simpa using Finset.univ_sum_single (1 : ∀ l, Matrix (nn l) (nn l) k)

/-- **The matrix units lift to a complete orthogonal family of idempotents of `A`.**  For
`A = kG` this is the decomposition of `1` into primitive idempotents; the modules `A f_x` are the
projective indecomposables whose composition factors give the Cartan matrix. -/
theorem exists_completeOrthogonalIdempotents_lift {A : Type*} [Ring A]
    {π : A →+* ∀ j, Matrix (nn j) (nn j) k} (hπ : Function.Surjective π)
    (hnil : ∀ x ∈ RingHom.ker π, IsNilpotent x) :
    ∃ f : (Σ i, nn i) → A, CompleteOrthogonalIdempotents f ∧
      ∀ x : Σ i, nn i, π (f x) = Pi.single x.1 (Matrix.single x.2 x.2 1) := by
  obtain ⟨f, hf, hfe⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker π hnil
    completeOrthogonalIdempotents_matrixUnit fun x => hπ _
  exact ⟨f, hf, fun x => congrFun hfe x⟩

end OddOrder
