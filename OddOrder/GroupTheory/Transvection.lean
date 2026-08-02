/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Transvections, coordinate-free

A **transvection** with centre `v` is the linear automorphism `x ↦ x + f x • v` attached to
a linear functional `f` killing `v`.  Fixing `v` and letting `f` range over the annihilator
of `v` gives a subgroup `transvectionSubgroup v` of the automorphism group, abelian and
isomorphic to that annihilator.

Mathlib's `Matrix.transvection i j c` is the same notion written in coordinates, with
`v = eᵢ` and `f = c • eⱼ*`.  The coordinate-free form is what an *Iwasawa structure*
(`MulAction.IwasawaStructure`) needs, because Iwasawa's criterion indexes its abelian
subgroups by the points of the action — here the non-zero vectors — and requires
`T (g • v) = MulAut.conj g • T v`, which is exactly `transvectionSubgroup_map_conj` below.

## Main definitions and results

* `LinearMap.transvection v f hf` — the automorphism `x ↦ x + f x • v`, for `f v = 0`.
* `LinearMap.transvectionSubgroup v` — all transvections with centre `v`, a subgroup of
  `V ≃ₗ[R] V`.
* `LinearMap.transvectionSubgroup_isMulCommutative` — it is abelian:
  `t_{v,f} * t_{v,g} = t_{v,f+g}`.
* `LinearMap.transvectionSubgroup_map_conj` — `T (g v) = g (T v) g⁻¹`.
* `LinearMap.toMatrix_transvection` — the matrix of `transvection (B i) (c • B.coord j)` in
  the basis `B` is mathlib's `Matrix.transvection i j c`.
* `LinearMap.commutator_transvection` — `⁅t_{v,f}, t_{w,g}⁆ = t_{w, -(g v) • f}` when `f`
  kills both centres and `g` kills its own; the route to perfectness of the linear group.
* `LinearMap.iSup_transvectionSubgroup_eq_top` — **over `𝔽₂` the transvections generate**,
  Iwasawa's `is_generator`.  Mathlib's Gaussian elimination
  (`Matrix.diagonal_transvection_induction_of_det_ne_zero`) writes any invertible matrix in
  terms of transvections and a diagonal, and over `𝔽₂` an invertible diagonal is the
  identity.

## References

Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen* (1941).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

namespace LinearMap

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **The transvection `x ↦ x + f x • v`**, for a functional `f` killing its centre `v`.

`f v = 0` is what makes it an involution up to sign: the inverse is `x ↦ x − f x • v`. -/
def transvection (v : V) (f : V →ₗ[R] R) (hf : f v = 0) : V ≃ₗ[R] V where
  toFun x := x + f x • v
  map_add' x y := by
    simp only [map_add, add_smul]
    abel
  map_smul' c x := by
    simp only [map_smul, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]
  invFun x := x - f x • v
  left_inv x := by
    simp only [map_add, map_smul, hf, smul_eq_mul, mul_zero, add_zero]
    abel
  right_inv x := by
    simp only [map_sub, map_smul, hf, smul_eq_mul, mul_zero, sub_zero]
    abel

@[simp]
theorem transvection_apply (v : V) (f : V →ₗ[R] R) (hf : f v = 0) (x : V) :
    transvection v f hf x = x + f x • v := rfl

@[simp]
theorem transvection_zero (v : V) (hf : (0 : V →ₗ[R] R) v = 0) :
    transvection v (0 : V →ₗ[R] R) hf = 1 := by
  ext x
  simp [transvection]

/-- Composing two transvections with the same centre adds the functionals. -/
theorem transvection_mul (v : V) (f g : V →ₗ[R] R) (hf : f v = 0) (hg : g v = 0) :
    transvection v f hf * transvection v g hg
      = transvection v (f + g) (by simp [hf, hg]) := by
  ext x
  have : f (g x • v) = 0 := by rw [map_smul, hf, smul_eq_mul, mul_zero]
  change (x + g x • v) + f (x + g x • v) • v = x + (f x + g x) • v
  rw [map_add, this, add_zero, add_smul]
  abel

/-- **All transvections with a given centre**, as a subgroup of the automorphism group. -/
def transvectionSubgroup (v : V) : Subgroup (V ≃ₗ[R] V) where
  carrier := {t | ∃ (f : V →ₗ[R] R) (hf : f v = 0), t = transvection v f hf}
  one_mem' := ⟨0, by simp, (transvection_zero v (by simp)).symm⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, by simp [hf, hg], transvection_mul v f g hf hg⟩
  inv_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨-f, by simp [hf], ?_⟩
    rw [inv_eq_iff_mul_eq_one, transvection_mul]
    simp

theorem mem_transvectionSubgroup {v : V} {t : V ≃ₗ[R] V} :
    t ∈ transvectionSubgroup v ↔ ∃ (f : V →ₗ[R] R) (hf : f v = 0), t = transvection v f hf :=
  Iff.rfl

theorem transvection_mem (v : V) (f : V →ₗ[R] R) (hf : f v = 0) :
    transvection v f hf ∈ transvectionSubgroup v := ⟨f, hf, rfl⟩

/-- **Transvections with a fixed centre commute** — Iwasawa's `is_comm`. -/
theorem transvectionSubgroup_isMulCommutative (v : V) :
    IsMulCommutative (transvectionSubgroup (R := R) v) := by
  refine ⟨⟨?_⟩⟩
  rintro ⟨_, f, hf, rfl⟩ ⟨_, g, hg, rfl⟩
  refine Subtype.ext ?_
  change transvection v f hf * transvection v g hg = transvection v g hg * transvection v f hf
  rw [transvection_mul, transvection_mul]
  congr 1
  exact add_comm f g

/-- **Conjugating a transvection moves its centre** — Iwasawa's `is_conj`.

`g t_{v,f} g⁻¹ = t_{g v, f ∘ g⁻¹}`, read off by evaluating both sides at `x`. -/
theorem conj_transvection (g : V ≃ₗ[R] V) (v : V) (f : V →ₗ[R] R) (hf : f v = 0) :
    g * transvection v f hf * g⁻¹
      = transvection (g v) (f ∘ₗ (g.symm : V →ₗ[R] V))
        (by simp [LinearEquiv.symm_apply_apply, hf]) := by
  ext x
  change g (transvection v f hf (g.symm x)) = x + f (g.symm x) • g v
  rw [transvection_apply, map_add, map_smul, LinearEquiv.apply_symm_apply]

/-- **The Iwasawa conjugation law**: `T (g v) = g (T v) g⁻¹`. -/
theorem transvectionSubgroup_map_conj (g : V ≃ₗ[R] V) (v : V) :
    transvectionSubgroup (R := R) (g v)
      = (transvectionSubgroup (R := R) v).map (MulAut.conj g).toMonoidHom := by
  ext t
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨transvection v (f ∘ₗ (g : V →ₗ[R] V)) (by simp [hf]),
      transvection_mem _ _ _, ?_⟩
    change g * transvection v (f ∘ₗ (g : V →ₗ[R] V)) (by simp [hf]) * g⁻¹ = _
    rw [conj_transvection]
    congr 1
    ext x
    simp
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    change g * transvection v f hf * g⁻¹ ∈ _
    rw [conj_transvection]
    exact transvection_mem _ _ _

/-- **The commutator of two transvections is a transvection** (Iwasawa's route to
perfectness).

If `f` kills both centres and `g` kills its own centre `w`, then

  `⁅t_{v,f}, t_{w,g}⁆ = t_{w, -(g v) • f}`.

Evaluating at `x`, the four factors telescope: `b⁻¹` subtracts `g x • w`, `a⁻¹` then
subtracts `f x • v` (the `g x • w` term dies because `f w = 0`), `b` adds back
`(g x − f x · g v) • w` (using `g w = 0`), and `a` adds back `f x • v` (using `f v = 0`
and `f w = 0`).  What survives is `−f x · g v` in the direction `w`.

Taking `g v = 1` — possible as soon as `v` and `w` are independent — exhibits *every*
transvection with centre `w` as a commutator, which is what makes the linear group
perfect once the dimension is at least `3` (one needs `v ∈ ker f`, `v ≠ 0`, `v ≠ w`). -/
theorem commutator_transvection {v w : V} {f g : V →ₗ[R] R}
    (hfv : f v = 0) (hfw : f w = 0) (hgw : g w = 0) :
    (transvection v f hfv) * (transvection w g hgw) * (transvection v f hfv)⁻¹ *
        (transvection w g hgw)⁻¹
      = transvection w (-(g v) • f) (by simp [hfw]) := by
  ext x
  have hinvf : ∀ y : V, (transvection v f hfv)⁻¹ y = y - f y • v := fun _ => rfl
  have hinvg : ∀ y : V, (transvection w g hgw)⁻¹ y = y - g y • w := fun _ => rfl
  change (transvection v f hfv)
      ((transvection w g hgw)
        ((transvection v f hfv)⁻¹ ((transvection w g hgw)⁻¹ x))) = x + (-(g v) * f x) • w
  rw [hinvg, hinvf]
  simp only [transvection_apply, map_add, map_sub, map_smul, smul_eq_mul, hfv, hfw, hgw,
    mul_zero, add_zero, sub_zero, zero_smul]
  module

section Coordinates

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Mathlib's matrix transvection is the coordinate-free one at a basis vector.**

`Matrix.transvection i j c = 1 + single i j c` adds `c` times the `j`-th coordinate to the
`i`-th, which is `x ↦ x + (c · xⱼ) • Bᵢ`: centre `B i`, functional `c • B.coord j`.  This
is the bridge that lets mathlib's Gaussian elimination
(`Matrix.diagonal_transvection_induction_of_det_ne_zero`) be read as a statement about
`transvectionSubgroup`. -/
theorem toMatrix_transvection (B : Module.Basis ι R V) {i j : ι} (hij : i ≠ j) (c : R)
    (hf : (c • B.coord j) (B i) = 0) :
    LinearMap.toMatrix B B
        ((transvection (B i) (c • B.coord j) hf : V ≃ₗ[R] V) : V →ₗ[R] V)
      = Matrix.transvection i j c := by
  ext k l
  rw [LinearMap.toMatrix_apply]
  have hval : ((transvection (B i) (c • B.coord j) hf : V ≃ₗ[R] V) : V →ₗ[R] V) (B l)
      = B l + (c * (B.repr (B l)) j) • B i := rfl
  rw [hval, map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply, B.repr_self,
    B.repr_self, smul_eq_mul]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single,
    Matrix.of_apply, Finsupp.single_apply]
  by_cases hlj : l = j
  · subst hlj
    by_cases hki : k = i
    · subst hki
      simp [hij, Ne.symm hij]
    · simp [Ne.symm hki, eq_comm]
  · simp [hlj, Ne.symm hlj, eq_comm]

end Coordinates

section Generation

open Matrix

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- Over a two-element field the only invertible diagonal matrix is the identity. -/
theorem diagonal_eq_one_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hK : ∀ x : K, x = 0 ∨ x = 1) (D : ι → K) (hD : (Matrix.diagonal D).det ≠ 0) :
    Matrix.diagonal D = 1 := by
  have hone : D = fun _ => (1 : K) := by
    funext i
    rcases hK (D i) with h | h
    · exact absurd (by rw [Matrix.det_diagonal]; exact Finset.prod_eq_zero (Finset.mem_univ i) h)
        hD
    · exact h
  rw [hone]
  exact Matrix.diagonal_one

/-- `g ↦ toMatrix B B g` is injective on linear automorphisms. -/
theorem toMatrix_injective {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Module.Basis ι K W)
    {g h : W ≃ₗ[K] W}
    (hgh : LinearMap.toMatrix B B (g : W →ₗ[K] W) = LinearMap.toMatrix B B (h : W →ₗ[K] W)) :
    g = h := by
  have := (LinearMap.toMatrix B B).injective hgh
  exact LinearEquiv.toLinearMap_injective this

/-- Matrices of a product of automorphisms multiply. -/
theorem toMatrix_mul_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Module.Basis ι K W)
    (g h : W ≃ₗ[K] W) :
    LinearMap.toMatrix B B ((g * h : W ≃ₗ[K] W) : W →ₗ[K] W)
      = LinearMap.toMatrix B B (g : W →ₗ[K] W) * LinearMap.toMatrix B B (h : W →ₗ[K] W) := by
  rw [← LinearMap.toMatrix_comp B B B]
  rfl

/-- The matrix of an automorphism is invertible. -/
theorem det_toMatrix_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Module.Basis ι K W)
    (g : W ≃ₗ[K] W) : (LinearMap.toMatrix B B (g : W →ₗ[K] W)).det ≠ 0 := by
  intro h0
  have hone : LinearMap.toMatrix B B ((g.symm * g : W ≃ₗ[K] W) : W →ₗ[K] W) = 1 := by
    rw [show (g.symm * g : W ≃ₗ[K] W) = 1 from by ext x; simp]
    exact LinearMap.toMatrix_id B
  rw [toMatrix_mul_equiv] at hone
  have := congrArg Matrix.det hone
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

/-- **Transvections generate the linear group over `𝔽₂`** — Iwasawa's `is_generator`. -/
theorem iSup_transvectionSubgroup_eq_top [FiniteDimensional K W]
    (hK : ∀ x : K, x = 0 ∨ x = 1) :
    ⨆ v : {v : W // v ≠ 0}, transvectionSubgroup (R := K) (v : W) = ⊤ := by
  classical
  set B := Module.finBasis K W with hBdef
  set S : Subgroup (W ≃ₗ[K] W) :=
    ⨆ v : {v : W // v ≠ 0}, transvectionSubgroup (R := K) (v : W) with hSdef
  have hmem : ∀ (v : W) (hv : v ≠ 0), transvectionSubgroup (R := K) v ≤ S := fun v hv =>
    le_iSup (fun w : {v : W // v ≠ 0} => transvectionSubgroup (R := K) (w : W)) ⟨v, hv⟩
  rw [eq_top_iff]
  rintro g -
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun N => ∀ g' : W ≃ₗ[K] W, LinearMap.toMatrix B B (g' : W →ₗ[K] W) = N → g' ∈ S)
    (LinearMap.toMatrix B B (g : W →ₗ[K] W)) (det_toMatrix_ne_zero B g) ?_ ?_ ?_ g rfl
  · -- diagonal: over `𝔽₂` it is the identity
    intro D hD g' hg'
    rw [diagonal_eq_one_of_det_ne_zero hK D hD, ← LinearMap.toMatrix_id B] at hg'
    have : g' = 1 := toMatrix_injective B (by rw [hg']; rfl)
    rw [this]
    exact S.one_mem
  · -- transvection: the coordinate-free one with centre `B t.i`
    intro t g' hg'
    have hne : (t.j : _) ≠ t.i := Ne.symm t.hij
    have hf : ((t.c • B.coord t.j) (B t.i) : K) = 0 := by
      simp [Module.Basis.coord_apply, B.repr_self, hne]
    have hmat := toMatrix_transvection B t.hij t.c hf
    have heq : g' = (transvection (B t.i) (t.c • B.coord t.j) hf : W ≃ₗ[K] W) :=
      toMatrix_injective B (by rw [hg', hmat]; rfl)
    rw [heq]
    exact hmem (B t.i) (B.ne_zero t.i) (transvection_mem _ _ _)
  · -- product
    intro A A' hA hA' PA PA' g' hg'
    set gA' : W ≃ₗ[K] W := Matrix.toLinearEquiv B A' (isUnit_iff_ne_zero.mpr hA') with hgA'
    have hgA'mat : LinearMap.toMatrix B B (gA' : W →ₗ[K] W) = A' := by
      rw [hgA', show ((Matrix.toLinearEquiv B A' (isUnit_iff_ne_zero.mpr hA') : W ≃ₗ[K] W) :
        W →ₗ[K] W) = Matrix.toLin B B A' from rfl, LinearMap.toMatrix_toLin]
    have hsplit : g' = (g' * gA'⁻¹) * gA' := by group
    rw [hsplit]
    refine S.mul_mem (PA _ ?_) (PA' _ hgA'mat)
    rw [toMatrix_mul_equiv, hg']
    have hinv : LinearMap.toMatrix B B ((gA'⁻¹ : W ≃ₗ[K] W) : W →ₗ[K] W) * A' = 1 := by
      rw [← hgA'mat, ← toMatrix_mul_equiv, show (gA'⁻¹ * gA' : W ≃ₗ[K] W) = 1 from by
        ext x; simp]
      exact LinearMap.toMatrix_id B
    calc A * A' * LinearMap.toMatrix B B ((gA'⁻¹ : W ≃ₗ[K] W) : W →ₗ[K] W)
        = A * (A' * LinearMap.toMatrix B B ((gA'⁻¹ : W ≃ₗ[K] W) : W →ₗ[K] W)) := by
          rw [Matrix.mul_assoc]
      _ = A := by
          rw [show A' * LinearMap.toMatrix B B ((gA'⁻¹ : W ≃ₗ[K] W) : W →ₗ[K] W) = 1 from ?_,
            Matrix.mul_one]
          exact mul_eq_one_comm.mp hinv

end Generation

end LinearMap

end OddOrder.GroupTheory
