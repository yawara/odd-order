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

end OddOrder.Peterfalvi.S16
