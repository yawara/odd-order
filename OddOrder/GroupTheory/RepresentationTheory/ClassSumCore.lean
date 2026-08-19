/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic.Group
import OddOrder.Mathlib.MonoidAlgebra

/-!
# Class sums in a monoid algebra, indexed by conjugacy classes

The **class sum** of a conjugacy class `C` of a finite group `G` is

`classSum C = ∑_{x ∈ C} x ∈ k[G]`,

together with the two facts that make it useful: its coefficient at `x ∈ G` is the indicator of
`x ∈ C`, and it is central in `k[G]`.

This core was previously duplicated verbatim in two places — `ClassSumSections.lean` (over `ℂ`,
for the class-sum congruences of Peterfalvi (6.7)) and `CenterClassSumBasis.lean` (over a field,
for the class-sum basis of `Z(k[G])`).  Both now import this file.  Extracting it also removed a
specialisation debt: neither the definition nor centrality needs `Field`, only `CommSemiring`,
so the class sums are now available over any commutative coefficient semiring.

Note the *other* class sum in the repository, `OddOrder.GroupAlgebra.classSum`
(`OddOrder/Algebra/ClassSum.lean`), which is indexed by a group *element* rather than by a
conjugacy class and is developed alongside the relative-trace machinery; the two are related by
`classSum (ConjClasses.mk g) = OddOrder.GroupAlgebra.classSum k g` but are not merged here.

## Main definitions

* `OddOrder.GroupTheory.CenterClassSum.classSum` — the class sum `∑_{x ∈ C} x ∈ k[G]`.

## Main results

* `OddOrder.GroupTheory.CenterClassSum.coeff_classSum` — its coefficients are the indicator of `C`.
* `OddOrder.GroupTheory.CenterClassSum.classSum_mem_center` — class sums are central.
-/

namespace OddOrder.GroupTheory.CenterClassSum

open scoped MonoidAlgebra

variable {k G : Type*} [CommSemiring k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]

omit [DecidableEq (ConjClasses G)] in
/-- **The indicator sum of a conjugation-invariant subset is central.**  Conjugation permutes the
subset, so multiplying by a group element on the left and on the right gives the same sum; the
general case follows by linearity.

Both `classSum_mem_center` (`S` a conjugacy class) and
`OddOrder.GroupTheory.CenterClassSum.truncClassSum_mem_center` (`S` the trace of a `G`-class on a
subgroup) are instances, as is the `C_G(P)`-truncation used in Brauer's correspondence. -/
theorem sum_ite_mem_center (S : G → Prop) [DecidablePred S]
    (hS : ∀ u x : G, S (u * x * u⁻¹) ↔ S x) :
    (∑ g : G, if S g then MonoidAlgebra.of k G g else 0)
      ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  classical
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single u r =>
    have hof : (MonoidAlgebra.single u r : MonoidAlgebra k G) = r • MonoidAlgebra.of k G u := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hof, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    rw [← Equiv.sum_comp (MulAut.conj u).toEquiv
      (fun g => (if S g then MonoidAlgebra.of k G g else 0) * MonoidAlgebra.of k G u)]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hconj : (MulAut.conj u).toEquiv g = u * g * u⁻¹ := by simp [MulAut.conj_apply]
    rw [hconj, if_congr (hS u g) rfl rfl]
    by_cases h0 : S g
    · simp only [h0, if_true]
      rw [← map_mul, ← map_mul]
      congr 1
      group
    · simp [h0]

/-- The **class sum** `classSum C = ∑_{x ∈ C} x ∈ k[G]` of a conjugacy class `C`. -/
noncomputable def classSum (C : ConjClasses G) : MonoidAlgebra k G :=
  ∑ g : G, if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0

/-- The coefficient of `classSum C` at `x ∈ G` is `1` if `x ∈ C` and `0` otherwise. -/
theorem coeff_classSum (C : ConjClasses G) (x : G) :
    (classSum (k := k) C).coeff x = if ConjClasses.mk x = C then 1 else 0 := by
  classical
  have hsum : (classSum (k := k) C).coeff x
      = ∑ g : G, (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0).coeff x := by
    rw [classSum]; exact MonoidAlgebra.coeff_finsetSum _ _ _
  have hzero : ((0 : MonoidAlgebra k G)).coeff x = 0 := rfl
  have hterm : ∀ g : G,
      (if ConjClasses.mk g = C then MonoidAlgebra.of k G g else 0).coeff x
      = if g = x then (if ConjClasses.mk g = C then (1 : k) else 0) else 0 := by
    intro g
    rw [apply_ite (fun f : MonoidAlgebra k G => f.coeff x), MonoidAlgebra.of_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, hzero]
    by_cases hg : g = x
    · rw [if_pos hg, if_pos hg]
    · rw [if_neg hg, if_neg hg, ite_self]
  rw [hsum, Finset.sum_congr rfl (fun g _ => hterm g),
    Finset.sum_ite_eq' Finset.univ x (fun g => if ConjClasses.mk g = C then (1 : k) else 0)]
  simp

open scoped Classical in
/-- **Left multiplication by a class sum sums the coefficients over the class.**
`(K̂ · w)(g) = ∑_{v ∈ K} w(v⁻¹ g)`. -/
theorem coeff_classSum_mul (C : ConjClasses G) (w : MonoidAlgebra k G) (g : G) :
    (classSum (k := k) C * w).coeff g
      = ∑ v ∈ Finset.univ.filter (fun v : G => ConjClasses.mk v = C), w.coeff (v⁻¹ * g) := by
  classical
  have hL : classSum (k := k) C * w
      = ∑ v ∈ Finset.univ.filter (fun v : G => ConjClasses.mk v = C),
        MonoidAlgebra.single v (1 : k) * w := by
    rw [classSum, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) =>
      show (if ConjClasses.mk v = C then (MonoidAlgebra.of k G) v else 0) * w
          = if ConjClasses.mk v = C then MonoidAlgebra.single v (1 : k) * w else 0 by
        by_cases h : ConjClasses.mk v = C
        · rw [if_pos h, if_pos h]; rfl
        · rw [if_neg h, if_neg h, zero_mul]]
    rw [← Finset.sum_filter]
  rw [hL, MonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff (v⁻¹ * g) (fun m' _ => ?_), one_mul]
  constructor
  · intro h; rw [← h]; group
  · rintro rfl; group

omit [Fintype G] [DecidableEq (ConjClasses G)] in
/-- Conjugacy is preserved by inversion. -/
theorem mk_inv_of_mk_eq {a b : G} (h : ConjClasses.mk a = ConjClasses.mk b) :
    ConjClasses.mk a⁻¹ = ConjClasses.mk b⁻¹ := by
  rw [ConjClasses.mk_eq_mk_iff_isConj] at h ⊢
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨c, by rw [← hc]; group⟩

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- **`(K̂' · w)(1) = ∑_{u ∈ K} w(u)`** where `K'` is the class of the inverses.  The reindexing
`v ↦ v⁻¹` matches the two classes. -/
theorem coeff_classSum_inv_mul_one (C : ConjClasses G) (w : MonoidAlgebra k G) :
    (classSum (k := k) (ConjClasses.mk C.out⁻¹) * w).coeff 1
      = ∑ u ∈ Finset.univ.filter (fun u : G => ConjClasses.mk u = C), w.coeff u := by
  classical
  rw [coeff_classSum_mul]
  have hmk : ConjClasses.mk C.out = C := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  refine Finset.sum_nbij' (fun v : G => v⁻¹) (fun u : G => u⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h := mk_inv_of_mk_eq (Finset.mem_filter.mp hv).2
    rwa [inv_inv, hmk] at h
  · intro u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h := mk_inv_of_mk_eq (((Finset.mem_filter.mp hu).2).trans hmk.symm)
    exact h
  · intro v _; simp
  · intro u _; simp
  · intro v _; rw [mul_one]

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

end OddOrder.GroupTheory.CenterClassSum
