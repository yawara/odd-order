/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing

/-!
# The commutator subspace of a group algebra

Brauer's count of the irreducible modular representations — `|IBr G|` equals the number of
`p`-regular classes — runs through the subspace `T = [kG, kG]` spanned by the commutators, and
its "`p`-radical" `T' = {x : x ^ (p ^ m) ∈ T}`.  The first step, done here, is that `T` is
exactly the span of the differences of conjugate group elements, so that `kG ⧸ T` is graded by
conjugacy classes.

## Main results

* `OddOrder.RepresentationTheory.Modular.commutatorSubmodule_eq_span_conj` — `T` is spanned by
  `g - b g b⁻¹`
* `OddOrder.RepresentationTheory.Modular.classCoeffSum_eq_zero_of_mem_commutatorSubmodule` —
  summing the coefficients over a conjugacy class kills `T`; these functionals are what
  separate the classes in the quotient
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra

variable (k G : Type*) [CommRing k] [Group G]

/-- The `k`-span of the commutators `x * y - y * x` of the group algebra. -/
noncomputable def commutatorSubmodule : Submodule k (MonoidAlgebra k G) :=
  Submodule.span k {z | ∃ x y : MonoidAlgebra k G, z = x * y - y * x}

/-- The `k`-span of the differences of conjugate group elements. -/
noncomputable def conjDiffSubmodule : Submodule k (MonoidAlgebra k G) :=
  Submodule.span k {z | ∃ a b : G, z = single a (1 : k) - single (b * a * b⁻¹) 1}

variable {k G}

theorem conjDiff_mem_commutatorSubmodule (a b : G) :
    single a (1 : k) - single (b * a * b⁻¹) 1 ∈ commutatorSubmodule k G := by
  refine Submodule.subset_span ⟨single b⁻¹ (1 : k), single (b * a) 1, ?_⟩
  rw [single_mul_single, single_mul_single, one_mul]
  congr 2
  group

theorem conjDiffSubmodule_le_commutatorSubmodule :
    conjDiffSubmodule k G ≤ commutatorSubmodule k G := by
  rw [conjDiffSubmodule, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  exact conjDiff_mem_commutatorSubmodule a b

/-- The commutator of two group elements, as a scalar multiple of a difference of conjugates. -/
theorem single_mul_sub_mul_mem (a b : G) (c d : k) :
    single a c * single b d - single b d * single a c ∈ conjDiffSubmodule k G := by
  rw [single_mul_single, single_mul_single, mul_comm d c]
  have hconj : b * a = b * (a * b) * b⁻¹ := by group
  have hsmul : single (a * b) (c * d) - single (b * a) (c * d)
      = (c * d) • (single (a * b) (1 : k) - single (b * (a * b) * b⁻¹) 1) := by
    rw [← hconj, smul_sub]
    simp
  rw [hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a * b, b, rfl⟩)

/-- Every commutator lies in the span of differences of conjugates: reduce bilinearly to
group elements. -/
theorem mul_sub_mul_mem (x y : MonoidAlgebra k G) :
    x * y - y * x ∈ conjDiffSubmodule k G := by
  induction x using MonoidAlgebra.induction_on with
  | of a =>
    induction y using MonoidAlgebra.induction_on with
    | of b =>
      simpa only [MonoidAlgebra.of_apply] using single_mul_sub_mul_mem (k := k) a b 1 1
    | add y₁ y₂ h₁ h₂ =>
      have hexp : (of k G) a * (y₁ + y₂) - (y₁ + y₂) * (of k G) a
          = ((of k G) a * y₁ - y₁ * (of k G) a) + ((of k G) a * y₂ - y₂ * (of k G) a) := by
        noncomm_ring
      rw [hexp]
      exact Submodule.add_mem _ h₁ h₂
    | smul c y h =>
      have hexp : (of k G) a * (c • y) - (c • y) * (of k G) a
          = c • ((of k G) a * y - y * (of k G) a) := by
        rw [smul_sub, mul_smul_comm, smul_mul_assoc]
      rw [hexp]
      exact Submodule.smul_mem _ _ h
  | add x₁ x₂ h₁ h₂ =>
    have hexp : (x₁ + x₂) * y - y * (x₁ + x₂) = (x₁ * y - y * x₁) + (x₂ * y - y * x₂) := by
      noncomm_ring
    rw [hexp]
    exact Submodule.add_mem _ h₁ h₂
  | smul c x h =>
    have hexp : (c • x) * y - y * (c • x) = c • (x * y - y * x) := by
      rw [smul_sub, smul_mul_assoc, mul_smul_comm]
    rw [hexp]
    exact Submodule.smul_mem _ _ h

/-- **The commutator subspace is spanned by the differences of conjugate group elements.** -/
theorem commutatorSubmodule_eq_span_conj :
    commutatorSubmodule k G = conjDiffSubmodule k G := by
  refine le_antisymm ?_ conjDiffSubmodule_le_commutatorSubmodule
  rw [commutatorSubmodule, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  exact mul_sub_mul_mem x y

/-! ### The class-coefficient functionals -/

section ClassSum

variable [Fintype G] [DecidableEq (ConjClasses G)]

/-- Summing the coefficients of an element of `kG` over a conjugacy class. -/
noncomputable def classCoeffSum (C : ConjClasses G) : MonoidAlgebra k G →ₗ[k] k where
  toFun x := ∑ g ∈ Finset.univ.filter (fun g : G => ConjClasses.mk g = C), x.coeff g
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem classCoeffSum_apply (C : ConjClasses G) (x : MonoidAlgebra k G) :
    classCoeffSum C x
      = ∑ g ∈ Finset.univ.filter (fun g : G => ConjClasses.mk g = C), x.coeff g := rfl

@[simp]
theorem classCoeffSum_single (C : ConjClasses G) (a : G) (c : k) :
    classCoeffSum C (single a c) = if ConjClasses.mk a = C then c else 0 := by
  classical
  rw [classCoeffSum_apply]
  by_cases h : ConjClasses.mk a = C
  · rw [if_pos h]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩) hmem
  · rw [if_neg h, Finset.sum_eq_zero]
    intro b hb
    have hbC : ConjClasses.mk b = C := (Finset.mem_filter.mp hb).2
    have hab : a ≠ b := fun hEq => h (hEq ▸ hbC)
    simp [hab]

/-- **The class-coefficient functionals kill the commutator subspace**: conjugate elements lie
in the same class, so their difference contributes `0`. -/
theorem classCoeffSum_eq_zero_of_mem_commutatorSubmodule (C : ConjClasses G)
    {x : MonoidAlgebra k G} (hx : x ∈ commutatorSubmodule k G) : classCoeffSum C x = 0 := by
  rw [commutatorSubmodule_eq_span_conj, conjDiffSubmodule] at hx
  refine Submodule.span_induction ?_ (map_zero _) (fun _ _ _ _ h₁ h₂ => by simp [h₁, h₂])
    (fun c _ _ h => by simp [h]) hx
  rintro _ ⟨a, b, rfl⟩
  have hconj : ConjClasses.mk (b * a * b⁻¹) = ConjClasses.mk a :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨b⁻¹, by group⟩)
  simp [hconj]

end ClassSum

end OddOrder.RepresentationTheory.Modular
