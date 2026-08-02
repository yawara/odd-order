/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Group.Subgroup.Basic

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

end LinearMap

end OddOrder.GroupTheory
