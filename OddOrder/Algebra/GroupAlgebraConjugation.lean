/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Ring.Action.End
import OddOrder.Algebra.RelativeTrace

/-!
# The group algebra as a `G`-algebra under conjugation

The group algebra `R[G]` carries the action of `G` by *conjugation*, `g • x = g x g⁻¹`.  This is
the `G`-algebra to which the relative trace machinery of `OddOrder.Algebra.RelativeTrace` is
applied in block theory: its `G`-fixed points are the centre `Z(R[G])`, its `H`-fixed points are
the `R`-span of the `H`-conjugacy class sums, and the images of the relative traces `Tr^G_D`
define the defect groups of a block.

The action is *not* declared as a global instance — `R[G]` already carries several `G`-flavoured
structures in mathlib and conjugation is not the expected default.  It lives in the
`OddOrder.Conjugation` scope; open it with `open scoped OddOrder.Conjugation`.

## Main definitions

* `OddOrder.GroupAlgebra.conjRingAut` — conjugation as a map `G →* RingAut R[G]`.
* `OddOrder.GroupAlgebra.conjMulSemiringAction` — the scoped `MulSemiringAction G R[G]`.

## Main results

* `OddOrder.GroupAlgebra.conj_smul_single`, `OddOrder.GroupAlgebra.coeff_conj_smul` — the action
  on a monomial and on coefficients.
* `OddOrder.GroupAlgebra.smul_eq_conj` — the action really is conjugation *inside* `R[G]`.
* `OddOrder.GroupAlgebra.forall_smul_eq_iff_mem_center` — over a commutative base the `G`-fixed
  points are exactly the centre.
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra

variable (R : Type*) [Semiring R] (G : Type*) [Group G]

/-- Conjugation, as a homomorphism from `G` to the ring automorphisms of `R[G]`. -/
noncomputable def conjRingAut : G →* RingAut (MonoidAlgebra R G) where
  toFun g := mapDomainRingEquiv R (MulAut.conj g)
  map_one' := by
    refine RingEquiv.ext fun x => ?_
    ext n
    change (mapDomainRingEquiv R (MulAut.conj 1) x).coeff n = x.coeff n
    rw [coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
    -- `MulEquiv.coe_toEquiv_symm` は `rfl` なので `Equiv` 側の `symm` を `MulEquiv` 側に読み替える
    change x.coeff ((MulAut.conj (1 : G)).symm n) = x.coeff n
    rw [MulAut.conj_symm_apply]
    simp
  map_mul' g h := by
    refine RingEquiv.ext fun x => ?_
    ext n
    change (mapDomainRingEquiv R (MulAut.conj (g * h)) x).coeff n
        = (mapDomainRingEquiv R (MulAut.conj g)
            (mapDomainRingEquiv R (MulAut.conj h) x)).coeff n
    rw [coeff_mapDomainRingEquiv, coeff_mapDomainRingEquiv, coeff_mapDomainRingEquiv]
    simp only [Finsupp.equivMapDomain_apply]
    congr 1
    change (g * h)⁻¹ * n * (g * h) = h⁻¹ * (g⁻¹ * n * g) * h
    group

/-- The **conjugation action** of `G` on its group algebra, `g • x = g x g⁻¹`.

Scoped: `R[G]` carries other `G`-flavoured structures, so this must be opted into with
`open scoped OddOrder.Conjugation`. -/
@[reducible] noncomputable def conjMulSemiringAction : MulSemiringAction G (MonoidAlgebra R G) :=
  MulSemiringAction.compHom _ (conjRingAut R G)

scoped[OddOrder.Conjugation] attribute [instance] OddOrder.GroupAlgebra.conjMulSemiringAction

open scoped OddOrder.Conjugation

variable {R G}

@[simp]
theorem coeff_conj_smul (g : G) (x : MonoidAlgebra R G) (n : G) :
    (g • x).coeff n = x.coeff (g⁻¹ * n * g) := by
  change (mapDomainRingEquiv R (MulAut.conj g) x).coeff n = _
  simp

@[simp]
theorem conj_smul_single (g h : G) (r : R) :
    g • (single h r : MonoidAlgebra R G) = single (g * h * g⁻¹) r := by
  change mapDomainRingEquiv R (MulAut.conj g) (single h r) = _
  simp

/-- Conjugation is `R`-linear. -/
theorem conj_smul_smul (g : G) (r : R) (x : MonoidAlgebra R G) : g • (r • x) = r • (g • x) := by
  ext n
  rw [coeff_conj_smul, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_smul_apply,
    coeff_conj_smul]

/-- The conjugation action is conjugation *inside* the algebra, by the unit `single g 1`. -/
theorem smul_eq_conj (g : G) (x : MonoidAlgebra R G) :
    g • x = single g 1 * x * single g⁻¹ 1 := by
  ext n
  rw [coeff_conj_smul, MonoidAlgebra.coeff_mul_single_apply,
    MonoidAlgebra.coeff_single_mul_apply]
  simp [mul_assoc]

/-- Conjugation by `g` fixes `x` exactly when the coefficient function of `x` is invariant. -/
theorem smul_eq_self_iff_coeff (g : G) (x : MonoidAlgebra R G) :
    g • x = x ↔ ∀ n : G, x.coeff (g⁻¹ * n * g) = x.coeff n := by
  constructor
  · intro h n
    rw [← coeff_conj_smul g x n, h]
  · intro h
    exact MonoidAlgebra.ext <| Finsupp.ext fun n => by rw [coeff_conj_smul, h]

/-- `x` is fixed by all of `H` exactly when its coefficient function is constant on
`H`-conjugacy classes.  This is the working description of `(R[G])^H`. -/
theorem forall_mem_smul_eq_iff_coeff (H : Subgroup G) (x : MonoidAlgebra R G) :
    (∀ g ∈ H, g • x = x) ↔ ∀ g ∈ H, ∀ n : G, x.coeff (g * n * g⁻¹) = x.coeff n := by
  constructor
  · intro h g hg n
    have := (smul_eq_self_iff_coeff g⁻¹ x).mp (h g⁻¹ (H.inv_mem hg)) n
    simpa using this
  · intro h g hg
    refine (smul_eq_self_iff_coeff g x).mpr fun n => ?_
    have := h g⁻¹ (H.inv_mem hg) n
    simpa using this

/-- Conjugation by `g` fixes `x` exactly when `x` commutes with the monomial `single g 1`. -/
theorem smul_eq_self_iff_commute (g : G) (x : MonoidAlgebra R G) :
    g • x = x ↔ single g 1 * x = x * single g 1 := by
  rw [smul_eq_conj]
  have hgg : (single g 1 : MonoidAlgebra R G) * single g⁻¹ 1 = 1 := by
    rw [single_mul_single, mul_inv_cancel, mul_one, ← MonoidAlgebra.one_def]
  have hg'g : (single g⁻¹ 1 : MonoidAlgebra R G) * single g 1 = 1 := by
    rw [single_mul_single, inv_mul_cancel, mul_one, ← MonoidAlgebra.one_def]
  constructor
  · intro h
    have hstep : single g 1 * x * single g⁻¹ 1 * single g 1 = x * single g 1 := by rw [h]
    rwa [mul_assoc (single g 1 * x), hg'g, mul_one] at hstep
  · intro h
    rw [h, mul_assoc, hgg, mul_one]

section CommSemiring

variable {R : Type*} [CommSemiring R] {G : Type*} [Group G]

/-- **The `G`-fixed points of `R[G]` under conjugation are exactly the centre.**

This is what identifies `(R[G])^G` with `Z(R[G])`, the ring in which block idempotents live. -/
theorem forall_smul_eq_iff_mem_center {x : MonoidAlgebra R G} :
    (∀ g : G, g • x = x) ↔ ∀ y : MonoidAlgebra R G, x * y = y * x := by
  constructor
  · intro h y
    induction y using MonoidAlgebra.induction_on with
    | hM m => exact ((smul_eq_self_iff_commute m x).mp (h m)).symm
    | hadd y z hy hz => rw [mul_add, add_mul, hy, hz]
    | hsmul r y hy => rw [mul_smul_comm, smul_mul_assoc, hy]
  · intro h g
    exact (smul_eq_self_iff_commute g x).mpr (h _).symm

end CommSemiring

end OddOrder.GroupAlgebra
