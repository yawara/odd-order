/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG.TGapCross
import OddOrder.Peterfalvi.S16_NonExistenceG.CoherentProjectionRigidity

/-!
# Peterfalvi (11.9)/(14.9): T-side eta-grid projection data

The integer orthogonal projection of the T-side bridge onto the shared eta-grid.
This is the linear-algebraic first half of Coq `FTtype34_structure`'s `bridgeS1`
calculation, before the orbit and non-orthogonality arguments force its off-axis
coefficients to vanish.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory
open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), integral eta-grid projection with norm bound.**
A virtual character `b` of norm `p+1` has integer Fourier coefficients `mᵢⱼ`
against the orthonormal eta-grid. Pythagoras writes its norm as the sum of
coefficient squares plus the perpendicular residual norm, hence
`sum mᵢⱼ² ≤ p+1`.

For the T-side bridge, `b = τ_T(ν₀-ζ)` and the norm premise is supplied by
`exists_typeIII_induced_primeTIDifference_with_norm`. -/
theorem exists_etaGrid_intProjection_of_inner_self_eq [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    {b : ClassFunction G ℂ} (hbZ : b ∈ ZIrr G)
    (hbnorm : ClassFunction.inner b b = (((base.p : ℤ) + 1) : ℂ)) :
    ∃ m : Fin base.q → Fin base.p → ℤ,
      (∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ)) ∧
      ClassFunction.inner b b =
        ((∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) : ℂ) +
          ClassFunction.inner (b - etaGridProjection base m)
            (b - etaGridProjection base m) ∧
      (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤
        (base.p : ℤ) + 1 := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  let witness : ∀ i : Fin base.q, ∀ j : Fin base.p,
      ∃ z : ℤ, ClassFunction.inner b (base.eta i j) = (z : ℂ) :=
    fun i j => ClassFunction.inner_mem_ZIrr_int hbZ (eta_mem_ZIrr base i j)
  let m : Fin base.q → Fin base.p → ℤ := fun i j => (witness i j).choose
  have hcoeff : ∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ) :=
    fun i j => (witness i j).choose_spec
  have hpyth := etaGrid_projection_pythagorean base b m hcoeff
  have hbound : (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤
      (base.p : ℤ) + 1 := by
    have hnn : (0 : ℝ) ≤
        (ClassFunction.inner (b - etaGridProjection base m)
          (b - etaGridProjection base m)).re :=
      inner_self_re_nonneg _
    have hre := congrArg Complex.re hpyth
    rw [Complex.add_re, Complex.intCast_re] at hre
    have hbRe : (ClassFunction.inner b b).re = (base.p : ℝ) + 1 := by
      rw [hbnorm]
      norm_num
    rw [hbRe] at hre
    have hle :
        ((∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) : ℝ) ≤
          (base.p : ℝ) + 1 := by linarith
    exact_mod_cast hle
  exact ⟨m, hcoeff, hpyth, hbound⟩

/-- An integer linear combination of the `eta`-grid is a virtual character. -/
theorem etaGridProjection_mem_ZIrr [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin base.q → Fin base.p → ℤ) :
    etaGridProjection base m ∈ ZIrr G := by
  classical
  rw [etaGridProjection]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  rw [Int.cast_smul_eq_zsmul]
  exact (ZIrr G).smul_mem (m i j) (eta_mem_ZIrr base i j)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- A test character orthogonal to the eta-grid but not to `b` witnesses that the perpendicular
eta-grid residual of `b` is nonzero. -/
theorem etaGrid_projection_residual_ne_zero_of_inner [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    (b psi : ClassFunction G ℂ) (m : Fin base.q → Fin base.p → ℤ)
    (hbpsi : ClassFunction.inner b psi ≠ 0)
    (hetapsi : ∀ i j, ClassFunction.inner (base.eta i j) psi = 0) :
    b - etaGridProjection base m ≠ 0 := by
  intro hzero
  have hbproj : b = etaGridProjection base m := sub_eq_zero.mp hzero
  apply hbpsi
  rw [hbproj, etaGridProjection, inner_sum_left]
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_sum_left]
  apply Finset.sum_eq_zero
  intro j _
  rw [ClassFunction.inner_smul_left, hetapsi i j, mul_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), strict residual sharpens the projection bound.**
If the perpendicular residual of a norm-`p+1` virtual character is nonzero, it is itself a
nonzero virtual character and therefore has integral squared norm at least `1`.  Pythagoras then
sharpens the eta-grid coefficient bound from `sum mᵢⱼ² ≤ p+1` to `sum mᵢⱼ² ≤ p`. -/
theorem etaGrid_projection_sum_sq_le_of_residual_ne_zero [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    {b : ClassFunction G ℂ} (hbZ : b ∈ ZIrr G)
    (hbnorm : ClassFunction.inner b b = (((base.p : ℤ) + 1) : ℂ))
    (m : Fin base.q → Fin base.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ))
    (hresidual : b - etaGridProjection base m ≠ 0) :
    (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤ (base.p : ℤ) := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hresZ : b - etaGridProjection base m ∈ ZIrr G :=
    (ZIrr G).sub_mem hbZ (etaGridProjection_mem_ZIrr base m)
  obtain ⟨c, hsupp, hrepr, hnorm⟩ := mem_ZIrr_inner_self_eq_sum_sq hresZ
  have hsupport : c.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hresidual
    rw [hrepr, h]
    simp
  obtain ⟨a, ha⟩ := hsupport
  have hca : c a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hresNormLower : (1 : ℤ) ≤ ∑ x ∈ c.support, (c x) ^ 2 := by
    calc
      (1 : ℤ) ≤ (c a) ^ 2 := by
        nlinarith [Int.one_le_abs hca, sq_abs (c a)]
      _ ≤ ∑ x ∈ c.support, (c x) ^ 2 := by
        exact Finset.single_le_sum (fun x _ => sq_nonneg (c x)) ha
  have hnormCast :
      ClassFunction.inner (b - etaGridProjection base m)
          (b - etaGridProjection base m) =
        ((∑ x ∈ c.support, (c x) ^ 2 : ℤ) : ℂ) := by
    rw [hnorm]
    push_cast
    rfl
  have hpyth := etaGrid_projection_pythagorean base b m hcoeff
  rw [hbnorm, hnormCast] at hpyth
  have hpythZ : (base.p : ℤ) + 1 =
      (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) +
        ∑ x ∈ c.support, (c x) ^ 2 := by
    exact_mod_cast hpyth
  omega

end OddOrder.Peterfalvi.S16
