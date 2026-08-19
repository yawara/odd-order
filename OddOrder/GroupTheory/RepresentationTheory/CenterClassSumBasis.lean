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
import OddOrder.GroupTheory.RepresentationTheory.ClassSumCore

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

variable {k G : Type*} [CommRing k] [Group G]

/-! ### 中心元の係数は共役類上一定 (有限性・decidability 不要) -/

section CenterCoeff

/-- A central element of `k[G]` has class-constant coefficients:
`z.coeff (h * x * h⁻¹) = z.coeff x`.  Conjugation by `h` permutes the support of `z` without
changing the coefficients (this is the content of `z` commuting with `single h 1`). -/
theorem coeff_center_conj {z : MonoidAlgebra k G}
    (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) (h x : G) :
    (z.coeff (h * x * h⁻¹) : k) = z.coeff x := by
  have key := (Finsupp.ext_iff.mp (congrArg MonoidAlgebra.coeff
    ((Subalgebra.mem_center_iff.mp hz) (MonoidAlgebra.single h 1)))) (h * x)
  rw [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one,
    inv_mul_cancel_left] at key
  exact key.symm

/-- A central element is constant along a conjugacy class:
`mk a = mk b ⟹ z.coeff a = z.coeff b`. -/
theorem coeff_center_of_mk_eq {z : MonoidAlgebra k G}
    (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) {a b : G}
    (hab : ConjClasses.mk a = ConjClasses.mk b) : (z.coeff a : k) = z.coeff b := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab)
  exact (coeff_center_conj hz h a).symm

end CenterCoeff

variable [Fintype G] [DecidableEq (ConjClasses G)]

/-- The class sums are `k`-linearly independent: distinct classes have disjoint supports, so the
`C.out`-coordinate of `∑_C a_C • classSum C` reads off `a_C`. -/
theorem classSum_linearIndependent :
    LinearIndependent k (classSum (k := k) (G := G)) := by
  -- `Fintype (ConjClasses G)` は型には現れないので証明内で `Finite` から作る。
  have : Finite (ConjClasses G) := Quotient.finite _
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff]
  intro a ha C
  have hmk : ConjClasses.mk (C.out) = C := by
    rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq C
  have key : ∀ C' : ConjClasses G,
      (a C' • classSum (k := k) C').coeff C.out = if C = C' then a C' else 0 := by
    intro C'
    rw [MonoidAlgebra.coeff_smul_apply, coeff_classSum, hmk, smul_eq_mul]
    split <;> simp_all
  have hx : ∑ C' : ConjClasses G, (a C' • classSum (k := k) C').coeff C.out = 0 := by
    have h0 : (∑ C' : ConjClasses G, a C' • classSum (k := k) C').coeff C.out = 0 := by
      rw [ha]; rfl
    rw [← h0]
    exact (MonoidAlgebra.coeff_finsetSum _ _ _).symm
  rw [Finset.sum_congr rfl (fun C' _ => key C'), Finset.sum_ite_eq Finset.univ C a] at hx
  simpa using hx

/-- The class sum `classSum C`, packaged as an element of the centre subalgebra. -/
noncomputable def classSumCenter (C : ConjClasses G) :
    ↥(Subalgebra.center k (MonoidAlgebra k G)) :=
  ⟨classSum C, classSum_mem_center C⟩

@[simp] theorem classSumCenter_coe (C : ConjClasses G) :
    (classSumCenter (k := k) C : MonoidAlgebra k G) = classSum C := rfl

variable [Fintype (ConjClasses G)]

/-- **The class-sum expansion of a central element**: `z = ∑_C z(C.out) • classSum C`.
Reading off the coefficient at `y`, only the class `C = mk y` contributes, with value
`z (mk y).out = z y` (central ⟹ class-constant).  This is the spanning half of the basis. -/
theorem center_eq_sum_classSum {z : MonoidAlgebra k G}
    (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    z = ∑ C : ConjClasses G, z.coeff (C.out) • classSum (k := k) C := by
  ext y
  rw [MonoidAlgebra.coeff_finsetSum]
  simp only [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeff_classSum, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (ConjClasses.mk y) (fun C => z.coeff (C.out)),
    if_pos (Finset.mem_univ _)]
  have hmk : ConjClasses.mk ((ConjClasses.mk y).out) = ConjClasses.mk y := by
    rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq _
  exact (coeff_center_of_mk_eq hz hmk).symm

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
          (z : MonoidAlgebra k G).coeff (C.out) • classSumCenter (k := k) C := by
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

omit [Fintype (ConjClasses G)] in
/-- A group automorphism `α` of `G` acts on conjugacy classes compatibly with the algebra
automorphism `MonoidAlgebra.domCongr α` of `k[G]`: it **permutes the class-sum basis**,
`domCongr α (classSum C) = classSum (map α C)`.  Reading off the coefficient at `y`, both sides are
`1` exactly when `α⁻¹ y ∈ C`, equivalently `y ∈ map α C` (`α` is an isomorphism, so it carries the
conjugacy relation both ways).  This is the `σ_e`-permutation feeding the cornerstone. -/
theorem domCongr_classSum (α : G ≃* G) (C : ConjClasses G) :
    MonoidAlgebra.domCongr k k α (classSum (k := k) C)
      = classSum (k := k) (ConjClasses.map (α : G →* G) C) := by
  ext y
  rw [MonoidAlgebra.coeff_domCongr]
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective C
  have hmap : ConjClasses.map (α : G →* G) (ConjClasses.mk c) = ConjClasses.mk (α c) := rfl
  simp only [coeff_classSum, hmap]
  have hiff : (ConjClasses.mk (α.symm y) = ConjClasses.mk c)
      ↔ (ConjClasses.mk y = ConjClasses.mk (α c)) := by
    rw [ConjClasses.mk_eq_mk_iff_isConj, ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · intro h; simpa using MonoidHom.map_isConj (α : G →* G) h
    · intro h; simpa using MonoidHom.map_isConj (α.symm : G →* G) h
  exact if_congr hiff rfl rfl

end OddOrder.GroupTheory.CenterClassSum
