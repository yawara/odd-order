/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.Group

/-!
# The class-sum basis of the centre of a group algebra (general field)

For Peterfalvi (9.1)'s kernel-FPF count (†), the orbit-count form of the Brauer permutation lemma is
obtained by applying the cornerstone `finrank_invariants_eq_card_orbits` to **two** bases of
`Z(𝔽̄_p[U])`: the class-sum basis (this file) and the primitive-idempotent basis (`Z ≅ 𝔽̄_p^N`, to
follow).

The repository already has class sums over `ℂ` (`ClassSumAlgebra.lean`); this file builds the
**general-field** version needed for `𝔽̄_p`.  The class sum
`classSum C = ∑_{x ∈ C} x ∈ k[G]` is central, and the class sums form a `k`-basis of the centre
`Z(k[G]) = Subalgebra.center k (MonoidAlgebra k G)` (over any field — the centre is exactly the
functions constant on conjugacy classes, of which the class sums are the indicators).
-/

namespace OddOrder.GroupTheory.CenterClassSum

open scoped MonoidAlgebra

-- The shared `variable` block below serves lemmas with differing instance usage; suppress the
-- section-variable hygiene linters (the instances are all genuinely needed by `classSum`).
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq G]
  [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]

/-- The **class sum** `classSum C = ∑_{x ∈ C} x ∈ k[G]` of a conjugacy class `C`. -/
noncomputable def classSum (C : ConjClasses G) : MonoidAlgebra k G :=
  ∑ g : G, if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0

/-- The coefficient of `classSum C` at `x ∈ G` is `1` if `x ∈ C` and `0` otherwise. -/
theorem classSum_apply (C : ConjClasses G) (x : G) :
    classSum (k := k) C x = if ConjClasses.mk x = C then 1 else 0 := by
  have hsum : classSum (k := k) C x
      = ∑ g : G, (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0) x := by
    rw [classSum]; exact map_sum (Finsupp.applyAddHom x) _ Finset.univ
  have hzero : ∀ y : G, (0 : MonoidAlgebra k G) y = 0 := fun _ => rfl
  have hterm : ∀ g : G,
      (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0) x
      = if g = x then (if ConjClasses.mk g = C then (1 : k) else 0) else 0 := by
    intro g
    rw [apply_ite (fun f : MonoidAlgebra k G => f x), MonoidAlgebra.of_apply,
      MonoidAlgebra.single_apply, hzero x]
    by_cases hg : g = x
    · rw [if_pos hg, if_pos hg]
    · rw [if_neg hg, if_neg hg, ite_self]
  rw [hsum, Finset.sum_congr rfl (fun g _ => hterm g),
    Finset.sum_ite_eq' Finset.univ x (fun g => if ConjClasses.mk g = C then (1 : k) else 0)]
  simp

/-- Each class sum is central in `k[G]`: `classSum C` commutes with every `of k G h` (conjugation
permutes the class `C`), hence with all of `k[G]` by linearity. -/
theorem classSum_mem_center (C : ConjClasses G) :
    classSum (k := k) C ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  classical
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single h r =>
    have hof : (MonoidAlgebra.single h r : MonoidAlgebra k G) = r • MonoidAlgebra.of k G h := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hof, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [classSum, Finset.mul_sum, Finset.sum_mul]
    rw [← Equiv.sum_comp (MulAut.conj h).toEquiv
      (fun g => (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0) *
        MonoidAlgebra.of k G h)]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hconj : (MulAut.conj h).toEquiv g = h * g * h⁻¹ := by simp [MulAut.conj_apply]
    rw [hconj]
    have hclass : ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
      ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h⁻¹, by group⟩)
    rw [hclass]
    by_cases h0 : ConjClasses.mk g = C
    · simp only [h0, if_true]
      rw [← map_mul, ← map_mul]
      congr 1
      group
    · simp [h0]

/-- The class sums are `k`-linearly independent: distinct classes have disjoint supports, so the
`C.out`-coordinate of `∑_C a_C • classSum C` reads off `a_C`. -/
theorem classSum_linearIndependent :
    LinearIndependent k (classSum (k := k) (G := G)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha C
  have hmk : ConjClasses.mk (C.out) = C := by
    rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq C
  have key : ∀ C' : ConjClasses G,
      (a C' • classSum (k := k) C') C.out = if C = C' then a C' else 0 := by
    intro C'
    rw [MonoidAlgebra.smul_apply, classSum_apply, hmk, smul_eq_mul]
    split <;> simp_all
  have hx : ∑ C' : ConjClasses G, (a C' • classSum (k := k) C') C.out = 0 := by
    have h0 : (∑ C' : ConjClasses G, a C' • classSum (k := k) C') C.out = 0 := by rw [ha]; rfl
    rw [← h0]
    exact (map_sum (Finsupp.applyAddHom C.out)
      (fun C' => a C' • classSum (k := k) C') Finset.univ).symm
  rw [Finset.sum_congr rfl (fun C' _ => key C'), Finset.sum_ite_eq Finset.univ C a] at hx
  simpa using hx

-- TODO (next iteration): class sums span `Z(k[G])`, giving `Basis (ConjClasses G) k ↥(center)`
-- (an invariant element is constant on conjugacy classes ⟹ `= ∑_C (coeff) • classSum C`), then the
-- `σ_e`-permutation `σ_e (classSum C) = classSum (e · C)`; feed both into the cornerstone for (4).

end OddOrder.GroupTheory.CenterClassSum
