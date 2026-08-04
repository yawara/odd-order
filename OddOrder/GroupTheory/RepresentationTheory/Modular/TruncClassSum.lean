/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.SubgroupTruncation
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis

/-!
# The trace of a `G`-class on a subgroup

**Navarro, before (4.13).**  The Brauer correspondence induces a block `b` of `H ≤ G` up to `G`
by extending the central character `λ_b : Z(kH) → k` to `Z(kG)` through

`λ_b^G(K̂) = λ_b( ∑_{x ∈ K ∩ H} x )`,

where `K` runs over the conjugacy classes of `G`.  The element `∑_{x ∈ K ∩ H} x ∈ kH` is what this
file supplies: `K ∩ H` is stable under `H`-conjugation (conjugating inside `H` is conjugating
inside `G`), so the sum is central in `kH` and `λ_b` can be applied to it.

The class sums of `G` are a basis of `Z(kG)` (`CenterClassSum.centerBasis`), so
`K̂ ↦ ∑_{x ∈ K ∩ H} x` determines a `k`-linear map `centerTrunc : Z(kG) → Z(kH)`; composing a
central character of `H` with it gives Navarro's `λ_b^G`.

## Main results

* `OddOrder.GroupTheory.CenterClassSum.truncClassSum` — `∑_{x ∈ K ∩ H} x`, as an element of `kH`
* `OddOrder.GroupTheory.CenterClassSum.coeff_truncClassSum`
* `OddOrder.GroupTheory.CenterClassSum.truncClassSum_mem_center`
* `OddOrder.GroupTheory.CenterClassSum.centerTrunc` — the induced linear map `Z(kG) → Z(kH)`
* `OddOrder.GroupTheory.CenterClassSum.inducedCentralCharacter` — `λ_b^G`
-/

namespace OddOrder.GroupTheory.CenterClassSum

open scoped MonoidAlgebra

variable {k G : Type*} [CommRing k] [Group G] [DecidableEq (ConjClasses G)]
variable (H : Subgroup G) [Fintype H]

/-- **The trace of a `G`-class on a subgroup**: `∑_{x ∈ K ∩ H} x ∈ k[H]`. -/
noncomputable def truncClassSum (C : ConjClasses G) : MonoidAlgebra k H :=
  ∑ h : H, if ConjClasses.mk (h : G) = C then MonoidAlgebra.of k H h else 0

/-- The coefficient of `truncClassSum H C` at `h ∈ H` is `1` if `h ∈ K` and `0` otherwise. -/
theorem coeff_truncClassSum (C : ConjClasses G) (x : H) :
    (truncClassSum (k := k) H C).coeff x = if ConjClasses.mk (x : G) = C then 1 else 0 := by
  classical
  have hsum : (truncClassSum (k := k) H C).coeff x
      = ∑ h : H, (if ConjClasses.mk (h : G) = C then MonoidAlgebra.of k H h else 0).coeff x := by
    rw [truncClassSum]; exact MonoidAlgebra.coeff_finsetSum _ _ _
  have hzero : ((0 : MonoidAlgebra k H)).coeff x = 0 := rfl
  have hterm : ∀ h : H,
      (if ConjClasses.mk (h : G) = C then MonoidAlgebra.of k H h else 0).coeff x
      = if h = x then (if ConjClasses.mk (h : G) = C then (1 : k) else 0) else 0 := by
    intro h
    rw [apply_ite (fun f : MonoidAlgebra k H => f.coeff x), MonoidAlgebra.of_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, hzero]
    by_cases hh : h = x
    · rw [if_pos hh, if_pos hh]
    · rw [if_neg hh, if_neg hh, ite_self]
  rw [hsum, Finset.sum_congr rfl (fun h _ => hterm h),
    Finset.sum_ite_eq' Finset.univ x
      (fun h : H => if ConjClasses.mk (h : G) = C then (1 : k) else 0)]
  simp

/-- **`∑_{x ∈ K ∩ H} x` is central in `k[H]`.**  Conjugating inside `H` is conjugating inside `G`,
so `K ∩ H` is a union of `H`-classes. -/
theorem truncClassSum_mem_center (C : ConjClasses G) :
    truncClassSum (k := k) H C ∈ Subalgebra.center k (MonoidAlgebra k H) := by
  classical
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single u r =>
    have hof : (MonoidAlgebra.single u r : MonoidAlgebra k H) = r • MonoidAlgebra.of k H u := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hof, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [truncClassSum, Finset.mul_sum, Finset.sum_mul]
    rw [← Equiv.sum_comp (MulAut.conj u).toEquiv
      (fun h : H => (if ConjClasses.mk (h : G) = C then MonoidAlgebra.of k H h else 0) *
        MonoidAlgebra.of k H u)]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hconj : (MulAut.conj u).toEquiv h = u * h * u⁻¹ := by simp [MulAut.conj_apply]
    rw [hconj]
    have hcoe : ((u * h * u⁻¹ : H) : G) = (u : G) * (h : G) * (u : G)⁻¹ := by push_cast; rfl
    have hclass : ConjClasses.mk ((u * h * u⁻¹ : H) : G) = ConjClasses.mk (h : G) := by
      rw [hcoe]
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨(u : G)⁻¹, by group⟩)
    rw [hclass]
    by_cases h0 : ConjClasses.mk (h : G) = C
    · simp only [h0, if_true]
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, MonoidAlgebra.of_apply,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, one_mul]
      congr 1
      group
    · simp [h0]

/-- The central element `∑_{x ∈ K ∩ H} x` of `k[H]`, bundled into the centre. -/
noncomputable def truncClassSumCenter (C : ConjClasses G) :
    ↥(Subalgebra.center k (MonoidAlgebra k H)) :=
  ⟨truncClassSum H C, truncClassSum_mem_center H C⟩

section Basis

variable [Fintype G] [Fintype (ConjClasses G)]

/-- **The truncation map `Z(kG) → Z(kH)`**, `K̂ ↦ ∑_{x ∈ K ∩ H} x`, defined on the class-sum
basis of the centre.  It is only `k`-linear — multiplicativity is exactly the condition under
which the induced block `b^G` is defined, and it does not always hold. -/
noncomputable def centerTrunc : ↥(Subalgebra.center k (MonoidAlgebra k G)) →ₗ[k]
    ↥(Subalgebra.center k (MonoidAlgebra k H)) :=
  (centerBasis (k := k) (G := G)).constr k (truncClassSumCenter (k := k) H)

@[simp]
theorem centerTrunc_classSumCenter (C : ConjClasses G) :
    centerTrunc (k := k) H (classSumCenter C) = truncClassSumCenter (k := k) H C := by
  rw [centerTrunc, ← centerBasis_apply (k := k) (G := G) C, Module.Basis.constr_basis]

/-- **Navarro's induced central character** `λ_b^G = λ_b ∘ centerTrunc`.  When this linear map
happens to be an algebra homomorphism it is the central character of a unique block `b^G` of `G`,
the *induced block*. -/
noncomputable def inducedCentralCharacter
    (lam : ↥(Subalgebra.center k (MonoidAlgebra k H)) →ₗ[k] k) :
    ↥(Subalgebra.center k (MonoidAlgebra k G)) →ₗ[k] k :=
  lam.comp (centerTrunc H)

@[simp]
theorem inducedCentralCharacter_classSumCenter
    (lam : ↥(Subalgebra.center k (MonoidAlgebra k H)) →ₗ[k] k) (C : ConjClasses G) :
    inducedCentralCharacter H lam (classSumCenter C) = lam (truncClassSumCenter (k := k) H C) := by
  rw [inducedCentralCharacter, LinearMap.comp_apply, centerTrunc_classSumCenter]

/-! ### `centerTrunc` is coefficient truncation

`centerTrunc` is defined on the class-sum basis, which is what makes `λ_b^G` easy to write down,
but the proof of Navarro (5.6) needs to know that it is nothing but "forget the coefficients
outside `H`".  Both descriptions are `k`-linear, so it is enough to compare them on class sums. -/

omit [Fintype (ConjClasses G)] in
theorem subgroupTrunc_classSum (C : ConjClasses G) :
    OddOrder.GroupAlgebra.subgroupTrunc H (classSum (k := k) C) = truncClassSum H C :=
  MonoidAlgebra.ext (Finsupp.ext fun x => by
    rw [OddOrder.GroupAlgebra.coeff_subgroupTrunc, coeff_classSum, coeff_truncClassSum])

/-- **`centerTrunc` truncates coefficients.**  This is the description used in Navarro (5.6),
where the block idempotent `f_B` is split into its `H`-part and its `G ∖ H`-part. -/
theorem coe_centerTrunc (z : ↥(Subalgebra.center k (MonoidAlgebra k G))) :
    ((centerTrunc (k := k) H z : ↥(Subalgebra.center k (MonoidAlgebra k ↥H))) :
        MonoidAlgebra k ↥H)
      = OddOrder.GroupAlgebra.subgroupTrunc H (z : MonoidAlgebra k G) := by
  have hext : (Subalgebra.center k (MonoidAlgebra k ↥H)).val.toLinearMap.comp
        (centerTrunc (k := k) H)
      = (OddOrder.GroupAlgebra.subgroupTruncₗ (R := k) H).comp
        (Subalgebra.center k (MonoidAlgebra k G)).val.toLinearMap := by
    refine (centerBasis (k := k) (G := G)).ext fun C => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, centerBasis_apply, centerTrunc_classSumCenter]
    exact (subgroupTrunc_classSum H C).symm
  exact congrFun (congrArg (fun f : ↥(Subalgebra.center k (MonoidAlgebra k G)) →ₗ[k]
    MonoidAlgebra k ↥H => f.toFun) hext) z

end Basis

end OddOrder.GroupTheory.CenterClassSum
