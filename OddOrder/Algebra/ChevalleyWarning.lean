/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# A quadratic-map consequence of Chevalley--Warning

This file derives a coordinate-free consequence of the Chevalley--Warning
theorem. Over a finite field of characteristic two, a twisted quadratic map
`x ↦ B x (T x)` from `V` to `W` has a nonzero zero whenever
`2 * finrank W < finrank V`.

The proof writes the coordinates of the map as quadratic multivariate
polynomials and applies Chevalley--Warning to their common zero set.
-/

noncomputable section

open scoped BigOperators
open MvPolynomial
open Module

namespace OddOrder.Algebra

private noncomputable def quadraticPolynomial
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {n m : ℕ} (bV : Basis (Fin n) F V) (bW : Basis (Fin m) F W)
    (B : V →ₗ[F] V →ₗ[F] W) (T : V ≃ₗ[F] V) (j : Fin m) :
    MvPolynomial (Fin n) F :=
  ∑ i, ∑ k, C (bW.equivFun (B (bV i) (T (bV k))) j) * X i * X k

private lemma eval_quadraticPolynomial
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {n m : ℕ} (bV : Basis (Fin n) F V) (bW : Basis (Fin m) F W)
    (B : V →ₗ[F] V →ₗ[F] W) (T : V ≃ₗ[F] V) (j : Fin m)
    (c : Fin n → F) :
    eval c (quadraticPolynomial bV bW B T j) =
      bW.equivFun (B (bV.equivFun.symm c) (T (bV.equivFun.symm c))) j := by
  simp only [quadraticPolynomial, Basis.equivFun_symm_apply, map_sum, eval_mul, eval_C,
    eval_X, LinearMap.sum_apply]
  simp only [map_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

private lemma totalDegree_quadraticPolynomial_le
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {n m : ℕ} (bV : Basis (Fin n) F V) (bW : Basis (Fin m) F W)
    (B : V →ₗ[F] V →ₗ[F] W) (T : V ≃ₗ[F] V) (j : Fin m) :
    (quadraticPolynomial bV bW B T j).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i hi
  apply totalDegree_finsetSum_le
  intro k hk
  calc
    (C (bW.equivFun (B (bV i) (T (bV k))) j) * X i * X k).totalDegree
        ≤ (C (bW.equivFun (B (bV i) (T (bV k))) j) * X i).totalDegree +
            (X k).totalDegree := totalDegree_mul _ _
    _ ≤ ((C (bW.equivFun (B (bV i) (T (bV k))) j)).totalDegree +
            (X i).totalDegree) + (X k).totalDegree := by
          gcongr
          exact totalDegree_mul _ _
    _ ≤ 2 := by simp

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
private theorem exists_ne_zero_solution_of_sum_lt
    {F σ ι : Type*} [Fintype F] [DecidableEq F] [Field F] [CharP F 2]
    [Fintype σ] [DecidableEq σ] [Fintype ι] (f : ι → MvPolynomial σ F)
    (hzero : ∀ i, eval 0 (f i) = 0)
    (hdegree : (∑ i, (f i).totalDegree) < Fintype.card σ) :
    ∃ c : σ → F, c ≠ 0 ∧ ∀ i, eval c (f i) = 0 := by
  set N := Fintype.card {c : σ → F // ∀ i, eval c (f i) = 0}
  let zeroSol : {c : σ → F // ∀ i, eval c (f i) = 0} := ⟨0, hzero⟩
  have hpos : 0 < N := @Fintype.card_pos _ _ ⟨zeroSol⟩
  have hdiv : 2 ∣ N :=
    char_dvd_card_solutions_of_fintype_sum_lt 2 hdegree
  have hone : 1 < N :=
    (by decide : 1 < 2).trans_le (Nat.le_of_dvd hpos hdiv)
  obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card hone zeroSol
  refine ⟨c.1, ?_, c.2⟩
  intro hc0
  apply hc
  apply Subtype.ext
  exact hc0

/-- Over a finite field of characteristic two, a twisted quadratic map
`x ↦ B x (T x)` has a nonzero zero when the source dimension is more than
twice the target dimension. This is a coordinate-free consequence of the
Chevalley--Warning theorem. -/
theorem exists_ne_zero_bilinear_twist_zero
    {F V W : Type*} [Finite F] [Field F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (B : V →ₗ[F] V →ₗ[F] W) (T : V ≃ₗ[F] V)
    (hdim : 2 * Module.finrank F W < Module.finrank F V) :
    ∃ x : V, x ≠ 0 ∧ B x (T x) = 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let bV : Basis (Fin (Module.finrank F V)) F V := Module.finBasis F V
  let bW : Basis (Fin (Module.finrank F W)) F W := Module.finBasis F W
  let f : Fin (Module.finrank F W) → MvPolynomial (Fin (Module.finrank F V)) F :=
    fun j ↦ quadraticPolynomial bV bW B T j
  have hdeg (j : Fin (Module.finrank F W)) : (f j).totalDegree ≤ 2 := by
    exact totalDegree_quadraticPolynomial_le bV bW B T j
  have hsum : (∑ j, (f j).totalDegree) < Fintype.card (Fin (Module.finrank F V)) := by
    rw [Fintype.card_fin]
    calc
      (∑ j, (f j).totalDegree) ≤ ∑ _j : Fin (Module.finrank F W), 2 :=
        Finset.sum_le_sum fun j _ ↦ hdeg j
      _ = 2 * Module.finrank F W := by simp [Nat.mul_comm]
      _ < Module.finrank F V := hdim
  obtain ⟨c, hc, hcf⟩ := exists_ne_zero_solution_of_sum_lt f (by
    intro j
    simp [f, quadraticPolynomial]) hsum
  let x : V := bV.equivFun.symm c
  have hx : x ≠ 0 := by
    intro hx0
    apply hc
    apply bV.equivFun.symm.injective
    simpa [x] using hx0
  refine ⟨x, hx, ?_⟩
  apply bW.equivFun.injective
  funext j
  rw [map_zero, Pi.zero_apply]
  rw [← eval_quadraticPolynomial bV bW B T j c]
  exact hcf j

end OddOrder.Algebra
