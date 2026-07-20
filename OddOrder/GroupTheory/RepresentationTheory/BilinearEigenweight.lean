/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Weights of an equivariant bilinear map

`OddOrder.GroupTheory.RepresentationTheory` shared module.

An operator that is diagonal in a basis has its eigenvalue on any eigenvector
readable from any nonzero coordinate of that eigenvector.  For a bilinear map
intertwining three operators this forces a *weight equation*: a nonzero
product of two eigenvectors is itself an eigenvector for the product weight,
so that weight occurs in the spectrum of the target.

The source arguments are only required to be *families* of eigenvectors whose
span contains the vectors of interest, not bases.  That is the shape actually
needed when the two families come from two proper subspaces of a common
ambient module.

This is the linear-algebra core of the step in Higman, *Suzuki 2-groups*,
Illinois J. Math. **7** (1963), p. 90: if `x₀ ξ = λ x₀` and `y₀ ξ = μ y₀`, then
`[xᵢ, yⱼ]` can be nonzero only if `λ^(2^i) μ^(2^j)` is an eigenvalue of `ξ` on
`Φ(G)`.  Nothing here refers to the group-theoretic origin of the modules.
-/

open Module

namespace OddOrder.RepresentationTheory

universe uF uV uW uX uI uJ uL

section Eigenweight

variable {F : Type uF} [Field F]

/-- The eigenvalue of an eigenvector equals the weight of any basis vector at
which the eigenvector has a nonzero coordinate. -/
theorem eigenvalue_eq_of_basis_repr_ne_zero
    {W : Type uW} {L : Type uL} [AddCommGroup W] [Module F W] [Finite L]
    (T : Module.End F W) (b : Basis L F W) (weight : L → F)
    (hb : ∀ k, T (b k) = weight k • b k)
    {x : W} {a : F} (hx : T x = a • x)
    (k : L) (hk : b.repr x k ≠ 0) :
    a = weight k := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  have hcoord : b.repr (T x) k = weight k * b.repr x k := by
    rw [← b.sum_repr x, map_sum]
    simp [hb, smul_smul, mul_comm]
    simp only [Finsupp.single_apply]
    simp
  have hcoord' := congrArg (fun y : W => b.repr y k) hx
  rw [hcoord] at hcoord'
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord'
  exact (mul_right_cancel₀ hk hcoord').symm

/-- A vector that a basis represents by the zero coordinate function is zero. -/
theorem eq_zero_of_forall_basis_repr_eq_zero
    {W : Type uW} {L : Type uL} [AddCommGroup W] [Module F W]
    (b : Basis L F W) {x : W} (hx : ∀ k, b.repr x k = 0) :
    x = 0 := by
  have hrepr : b.repr x = 0 := by
    ext k
    simpa using hx k
  simpa using congrArg b.repr.symm hrepr

variable {V₁ : Type uV} {V₂ : Type uX} {W : Type uW}
variable [AddCommGroup V₁] [Module F V₁]
variable [AddCommGroup V₂] [Module F V₂]
variable [AddCommGroup W] [Module F W]

/-- If a bilinear map has a nonzero value on a pair drawn from the spans of two
families, then it is already nonzero on a pair of family members. -/
theorem exists_pair_ne_zero_of_mem_span
    {I : Type uI} {J : Type uJ}
    (beta : V₁ →ₗ[F] V₂ →ₗ[F] W)
    (xs : I → V₁) (ys : J → V₂)
    {x : V₁} {y : V₂}
    (hx : x ∈ Submodule.span F (Set.range xs))
    (hy : y ∈ Submodule.span F (Set.range ys))
    (hxy : beta x y ≠ 0) :
    ∃ (i : I) (j : J), beta (xs i) (ys j) ≠ 0 := by
  by_contra hall
  push Not at hall
  -- Fixing a family member on the left, the map vanishes on the right span.
  have hright : ∀ i : I, ∀ v : V₂,
      v ∈ Submodule.span F (Set.range ys) → beta (xs i) v = 0 := by
    intro i v hv
    have hsub : Submodule.span F (Set.range ys) ≤
        LinearMap.ker (beta (xs i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hall i j
    exact hsub hv
  -- Hence the linear map `z ↦ beta z y` vanishes on the left span.
  have hleft : ∀ z : V₁,
      z ∈ Submodule.span F (Set.range xs) → beta z y = 0 := by
    intro z hz
    have hsub : Submodule.span F (Set.range xs) ≤
        LinearMap.ker ((LinearMap.flip beta) y) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa using hright i y hy
    simpa using hsub hz
  exact hxy (hleft x hx)

/-- **Weight equation for one nonzero product.**

If an equivariant bilinear map is nonzero on a pair of eigenvectors, then the
product of their eigenvalues occurs among the weights of the target eigenbasis.

This is Higman's “`[xᵢ, yⱼ]` can be nonzero only if `λ^(2^i) μ^(2^j)` is an
eigenvalue on the centre”. -/
theorem exists_weight_eq_of_bilinear_ne_zero
    {L : Type uL} [Finite L]
    (T₁ : Module.End F V₁) (T₂ : Module.End F V₂) (T₃ : Module.End F W)
    (beta : V₁ →ₗ[F] V₂ →ₗ[F] W)
    (b₃ : Basis L F W) (w₃ : L → F)
    (hb₃ : ∀ k, T₃ (b₃ k) = w₃ k • b₃ k)
    (hcov : ∀ u v, T₃ (beta u v) = beta (T₁ u) (T₂ v))
    {u : V₁} {v : V₂} {a c : F}
    (hu : T₁ u = a • u) (hv : T₂ v = c • v)
    (hne : beta u v ≠ 0) :
    ∃ k : L, a * c = w₃ k := by
  classical
  -- The nonzero product is an eigenvector for the product weight.
  have heigen : T₃ (beta u v) = (a * c) • beta u v := by
    rw [hcov, hu, hv, LinearMap.map_smul₂, map_smul, smul_smul]
  -- A nonzero vector has a nonzero coordinate.
  obtain ⟨k, hk⟩ : ∃ k, b₃.repr (beta u v) k ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact hne (eq_zero_of_forall_basis_repr_eq_zero b₃ hzero)
  exact ⟨k, eigenvalue_eq_of_basis_repr_ne_zero T₃ b₃ w₃ hb₃ heigen k hk⟩

/-- **Weight equation for an equivariant bilinear map.**

Let `beta` intertwine `T₁, T₂` with `T₃`, let `xs` and `ys` be families of
eigenvectors for `T₁` and `T₂`, and let `b₃` be an eigenbasis for `T₃`.  If
`beta` is nonzero on some pair drawn from the two spans, then some pair of
family members already has a nonzero product, and its product weight is one of
the target weights.

This is Higman's `λ^(2^i) μ^(2^j) = ν^(2^k)` in coordinate-free form. -/
theorem exists_pair_ne_zero_and_weight_eq
    {I : Type uI} {J : Type uJ} {L : Type uL} [Finite L]
    (T₁ : Module.End F V₁) (T₂ : Module.End F V₂) (T₃ : Module.End F W)
    (beta : V₁ →ₗ[F] V₂ →ₗ[F] W)
    (xs : I → V₁) (ys : J → V₂) (b₃ : Basis L F W)
    (w₁ : I → F) (w₂ : J → F) (w₃ : L → F)
    (hxs : ∀ i, T₁ (xs i) = w₁ i • xs i)
    (hys : ∀ j, T₂ (ys j) = w₂ j • ys j)
    (hb₃ : ∀ k, T₃ (b₃ k) = w₃ k • b₃ k)
    (hcov : ∀ u v, T₃ (beta u v) = beta (T₁ u) (T₂ v))
    {x : V₁} {y : V₂}
    (hx : x ∈ Submodule.span F (Set.range xs))
    (hy : y ∈ Submodule.span F (Set.range ys))
    (hxy : beta x y ≠ 0) :
    ∃ (i : I) (j : J) (k : L),
      beta (xs i) (ys j) ≠ 0 ∧ w₁ i * w₂ j = w₃ k := by
  obtain ⟨i, j, hij⟩ :=
    exists_pair_ne_zero_of_mem_span beta xs ys hx hy hxy
  obtain ⟨k, hk⟩ :=
    exists_weight_eq_of_bilinear_ne_zero T₁ T₂ T₃ beta b₃ w₃ hb₃ hcov
      (hxs i) (hys j) hij
  exact ⟨i, j, k, hij, hk⟩

end Eigenweight

end OddOrder.RepresentationTheory
