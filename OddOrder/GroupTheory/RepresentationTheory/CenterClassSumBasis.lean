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

open Module

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

/-- A central element of `k[G]` has class-constant coefficients: `z (h * x * h⁻¹) = z x`.
Conjugation by `h` permutes the support of `z` without changing the coefficients (this is the
content of `z` commuting with `single h 1`). -/
theorem center_apply_conj {z : MonoidAlgebra k G}
    (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) (h x : G) :
    (z (h * x * h⁻¹) : k) = z x := by
  have key := (Finsupp.ext_iff.mp
    ((Subalgebra.mem_center_iff.mp hz) (MonoidAlgebra.single h 1))) (h * x)
  rw [MonoidAlgebra.single_mul_apply, MonoidAlgebra.mul_single_apply, one_mul, mul_one,
    inv_mul_cancel_left] at key
  exact key.symm

/-- A central element is constant along a conjugacy class: `mk a = mk b ⟹ z a = z b`. -/
theorem center_apply_of_mk_eq {z : MonoidAlgebra k G}
    (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) {a b : G}
    (hab : ConjClasses.mk a = ConjClasses.mk b) : (z a : k) = z b := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab)
  exact (center_apply_conj hz h a).symm

/-- **The class-sum expansion of a central element**: `z = ∑_C z(C.out) • classSum C`.
Reading off the coefficient at `y`, only the class `C = mk y` contributes, with value
`z (mk y).out = z y` (central ⟹ class-constant).  This is the spanning half of the basis. -/
theorem center_eq_sum_classSum {z : MonoidAlgebra k G}
    (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    z = ∑ C : ConjClasses G, z (C.out) • classSum (k := k) C := by
  refine Finsupp.ext fun y => ?_
  have hrhs : (∑ C : ConjClasses G, z (C.out) • classSum (k := k) C) y
      = ∑ C : ConjClasses G, (z (C.out) • classSum (k := k) C) y :=
    map_sum (Finsupp.applyAddHom y) (fun C => z (C.out) • classSum (k := k) C) Finset.univ
  rw [hrhs]
  simp only [MonoidAlgebra.smul_apply, smul_eq_mul, classSum_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (ConjClasses.mk y) (fun C => z (C.out)),
    if_pos (Finset.mem_univ _)]
  have hmk : ConjClasses.mk ((ConjClasses.mk y).out) = ConjClasses.mk y := by
    rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq _
  exact (center_apply_of_mk_eq hz hmk).symm

/-- The class sum `classSum C`, packaged as an element of the centre subalgebra. -/
noncomputable def classSumCenter (C : ConjClasses G) :
    ↥(Subalgebra.center k (MonoidAlgebra k G)) :=
  ⟨classSum C, classSum_mem_center C⟩

@[simp] theorem classSumCenter_coe (C : ConjClasses G) :
    (classSumCenter (k := k) C : MonoidAlgebra k G) = classSum C := rfl

/-- **The class-sum basis of the centre `Z(k[G])`** over an arbitrary field, indexed by conjugacy
classes.  Linear independence is inherited from the ambient `k[G]` (disjoint supports); spanning is
`center_eq_sum_classSum`.  This is one of the two bases of `Z(𝔽̄_p[U])` fed into the cornerstone
`finrank_invariants_eq_card_orbits` for Peterfalvi (9.1)'s orbit-count Brauer lemma. -/
noncomputable def centerBasis :
    Basis (ConjClasses G) k ↥(Subalgebra.center k (MonoidAlgebra k G)) :=
  Basis.mk (v := classSumCenter)
    (LinearIndependent.of_comp
      (Subalgebra.center k (MonoidAlgebra k G)).val.toLinearMap classSum_linearIndependent)
    (by
      intro z _
      have hsum : z = ∑ C : ConjClasses G,
          (z : MonoidAlgebra k G) (C.out) • classSumCenter (k := k) C := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finsetSum]
        simp only [SetLike.val_smul, classSumCenter_coe]
        exact center_eq_sum_classSum z.2
      rw [hsum]
      exact Submodule.sum_mem _ fun C _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨C, rfl⟩))

@[simp] theorem centerBasis_apply (C : ConjClasses G) :
    centerBasis (k := k) (G := G) C = classSumCenter C :=
  Basis.mk_apply _ _ C

/-- A group automorphism `α` of `G` acts on conjugacy classes compatibly with the algebra
automorphism `MonoidAlgebra.domCongr α` of `k[G]`: it **permutes the class-sum basis**,
`domCongr α (classSum C) = classSum (map α C)`.  Reading off the coefficient at `y`, both sides are
`1` exactly when `α⁻¹ y ∈ C`, equivalently `y ∈ map α C` (`α` is an isomorphism, so it carries the
conjugacy relation both ways).  This is the `σ_e`-permutation feeding the cornerstone. -/
theorem domCongr_classSum (α : G ≃* G) (C : ConjClasses G) :
    MonoidAlgebra.domCongr k k α (classSum (k := k) C)
      = classSum (k := k) (ConjClasses.map (α : G →* G) C) := by
  refine Finsupp.ext fun y => ?_
  rw [MonoidAlgebra.domCongr_apply]
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective C
  have hmap : ConjClasses.map (α : G →* G) (ConjClasses.mk c) = ConjClasses.mk (α c) := rfl
  simp only [classSum_apply, hmap]
  have hiff : (ConjClasses.mk (α.symm y) = ConjClasses.mk c)
      ↔ (ConjClasses.mk y = ConjClasses.mk (α c)) := by
    rw [ConjClasses.mk_eq_mk_iff_isConj, ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · intro h; simpa using MonoidHom.map_isConj (α : G →* G) h
    · intro h; simpa using MonoidHom.map_isConj (α.symm : G →* G) h
  exact if_congr hiff rfl rfl

end OddOrder.GroupTheory.CenterClassSum
