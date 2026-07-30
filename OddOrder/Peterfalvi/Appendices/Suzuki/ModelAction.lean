/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.ModelIsomorphism

/-!
# Step (4) of the Ch. III §3 Proposition: the `K₁W₁`-action on the model

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §3, p. 120–121, step (4) of the Proposition:

> Let `A` be the image of `K W` in `Aut(S₁)` (`K W` acts on `S ≅ S₁` by
> conjugation).  One checks that the formula of the statement defines an action of
> `K₁ W₁` on `S₁`, and lets `B` be the image of `K₁ W₁` in `Aut(S₁)`.

This file builds that action.  The formula is `(x, y)^a = (a x, a^{1+σ} y)`, and it
is a group automorphism of the twisted product `S₁ = E ×_φ F` precisely because the
cocycle obeys the **diagonal** scaling `φ (a x) (a y) = a^{1+σ} φ (x, y)` — which,
unlike the `F`-semilinearity of step (3), holds for every scalar admitting a scaling
relation on `χ`, so in particular on all of `K₁ W₁` (note `W₁ ⊄ F`).

The central-coordinate scalar is the scaling constant of `χ`, namely `μ(k,1)^d`; by
`centreQuadraticMap_smul_KW` it does not involve the `W`-component, so the constants
form a homomorphism on `K × W` outright.

## Main results

* `Hypothesis.modelScalarAut` — a single scalar acting on the model.
* `Hypothesis.modelScalarHom` — the action as a group homomorphism; its image is
  the book's subgroup `B`.
* `Hypothesis.exists_modelScalarHom` — the instance for `K W` itself.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

variable {m : ℕ} (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)

/-! ## The scalar action on the model `S₁` -/

/-- **A scalar acting on the model `S₁`** (Peterfalvi Part II, Ch. III §3, p. 120):
`(x, y)^a = (a x, ν y)`, where `ν` is the scaling constant of the cocycle.

Well defined as a group automorphism exactly because of the diagonal scaling
`φ (a x) (a y) = ν · φ (x, y)` — which, unlike the `F`-semilinearity, holds for
every `a` admitting a scaling relation on `χ`, in particular for the whole of
`K₁W₁` (`W₁` is not contained in `F`). -/
noncomputable def modelScalarAut
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {a : M.E} (ha : a ≠ 0)
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)} (hν : ν ≠ 0)
    (h : ∀ x y : M.E, φ (a * x) (a * y) = ν * φ x y) :
    MulAut (Suzuki2Groups.BilinearTwistedProduct φ) :=
  Suzuki2Groups.BilinearTwistedProduct.congrEquiv
    (AddEquiv.mk' (Equiv.mulLeft₀ a ha) (mul_add a))
    (AddEquiv.mk' (Equiv.mulLeft₀ ν hν) (mul_add ν)) h

@[simp] theorem modelScalarAut_quotient
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {a : M.E} (ha : a ≠ 0)
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)} (hν : ν ≠ 0)
    (h : ∀ x y : M.E, φ (a * x) (a * y) = ν * φ x y)
    (p : Suzuki2Groups.BilinearTwistedProduct φ) :
    (hyp.modelScalarAut M φ ha hν h p).quotient = a * p.quotient :=
  rfl

@[simp] theorem modelScalarAut_central
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {a : M.E} (ha : a ≠ 0)
    {ν : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)} (hν : ν ≠ 0)
    (h : ∀ x y : M.E, φ (a * x) (a * y) = ν * φ x y)
    (p : Suzuki2Groups.BilinearTwistedProduct φ) :
    (hyp.modelScalarAut M φ ha hν h p).central = ν * p.central :=
  rfl

/-- **The scalar action of a group on the model `S₁`, as a homomorphism.**

Given compatible homomorphisms `A` into the scalars acting on the quotient
coordinate and `N` into those acting on the central coordinate,
`g ↦ ((x, y) ↦ (A g · x, N g · y))` is a homomorphism into `Aut S₁`.

Its image is the subgroup `B` of Peterfalvi Part II, Ch. III §3, p. 121, step (4),
once `A` is taken to be the scalar realization `μ` of `K W` and `N` the
corresponding family of scaling constants of `χ`. -/
noncomputable def modelScalarHom {Γ : Type*} [Group Γ]
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (A : Γ →* M.Eˣ)
    (N : Γ →* (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ)
    (h : ∀ (g : Γ) (x y : M.E),
      φ (((A g : M.Eˣ) : M.E) * x) (((A g : M.Eˣ) : M.E) * y)
        = ((N g : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * φ x y) :
    Γ →* MulAut (Suzuki2Groups.BilinearTwistedProduct φ) where
  toFun g := Suzuki2Groups.BilinearTwistedProduct.congrEquiv
    (AddEquiv.mk' (Equiv.mulLeft₀ ((A g : M.Eˣ) : M.E) (A g).ne_zero) (mul_add _))
    (AddEquiv.mk' (Equiv.mulLeft₀
      ((N g : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (N g).ne_zero) (mul_add _))
    (h g)
  map_one' := by
    refine MulEquiv.ext fun p => ?_
    refine Suzuki2Groups.BilinearTwistedProduct.ext ?_ ?_
    · change ((A 1 : M.Eˣ) : M.E) * p.quotient = p.quotient
      rw [map_one, Units.val_one, one_mul]
    · change ((N 1 : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * p.central = p.central
      rw [map_one, Units.val_one, one_mul]
  map_mul' g g' := by
    refine MulEquiv.ext fun p => ?_
    refine Suzuki2Groups.BilinearTwistedProduct.ext ?_ ?_
    · change ((A (g * g') : M.Eˣ) : M.E) * p.quotient
        = ((A g : M.Eˣ) : M.E) * (((A g' : M.Eˣ) : M.E) * p.quotient)
      rw [map_mul, Units.val_mul, mul_assoc]
    · change ((N (g * g') : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * p.central
        = ((N g : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) *
          (((N g' : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * p.central)
      rw [map_mul, Units.val_mul, mul_assoc]

@[simp] theorem modelScalarHom_quotient {Γ : Type*} [Group Γ]
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (A : Γ →* M.Eˣ)
    (N : Γ →* (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ)
    (h : ∀ (g : Γ) (x y : M.E),
      φ (((A g : M.Eˣ) : M.E) * x) (((A g : M.Eˣ) : M.E) * y)
        = ((N g : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * φ x y)
    (g : Γ) (p : Suzuki2Groups.BilinearTwistedProduct φ) :
    (hyp.modelScalarHom M φ A N h g p).quotient = ((A g : M.Eˣ) : M.E) * p.quotient :=
  rfl

@[simp] theorem modelScalarHom_central {Γ : Type*} [Group Γ]
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (A : Γ →* M.Eˣ)
    (N : Γ →* (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ)
    (h : ∀ (g : Γ) (x y : M.E),
      φ (((A g : M.Eˣ) : M.E) * x) (((A g : M.Eˣ) : M.E) * y)
        = ((N g : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * φ x y)
    (g : Γ) (p : Suzuki2Groups.BilinearTwistedProduct φ) :
    (hyp.modelScalarHom M φ A N h g p).central =
      ((N g : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * p.central :=
  rfl

/-! ## The `K W`-action on the model -/

/-- The scalar `μ(k, 1)`, as a unit of the subfield `F` (it lies there by
`QuotientFieldModel.mu_K_frobFixed`). -/
noncomputable def muKUnit (k : ↥hyp.actualKActor) :
    (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ :=
  Units.mk0 ⟨((M.mu (k, 1) : M.Eˣ) : M.E),
      OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed k)⟩
    (fun h => (M.mu (k, 1) : M.Eˣ).ne_zero
      (congrArg (Subtype.val (p := fun x =>
        x ∈ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) h))

/-- `μ(·, 1)` as a homomorphism into the units of `F`. -/
noncomputable def muKUnitHom :
    ↥hyp.actualKActor →* (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ where
  toFun := hyp.muKUnit M
  map_one' := by
    refine Units.ext (Subtype.ext ?_)
    change ((M.mu (1, 1) : M.Eˣ) : M.E) = 1
    rw [show ((1, 1) : ↥hyp.actualKActor × ↥hyp.W) = 1 from rfl, map_one, Units.val_one]
  map_mul' k k' := by
    refine Units.ext (Subtype.ext ?_)
    change ((M.mu (k * k', 1) : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) *
      ((M.mu (k', 1) : M.Eˣ) : M.E)
    rw [← Units.val_mul, ← map_mul]
    congr 2
    exact Prod.ext rfl (one_mul _).symm

/-- The inclusion of `F` into `E` on units. -/
noncomputable def frobFixedUnitsHom :
    (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ →* M.Eˣ :=
  Units.map ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m).subtype :
    ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) →+* M.E).toMonoidHom

/-- Powers of `μ(k, 1)` computed in `F` agree with those computed in `E`. -/
theorem muKUnitHom_zpow_val (k : ↥hyp.actualKActor) (d : ℤ) :
    (((hyp.muKUnitHom M k ^ d :
        (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) := by
  have hbase : hyp.frobFixedUnitsHom M (hyp.muKUnitHom M k) = M.mu (k, 1) :=
    Units.ext rfl
  have := congrArg (fun u : M.Eˣ => (u : M.E))
    ((map_zpow (hyp.frobFixedUnitsHom M) (hyp.muKUnitHom M k) d).trans (by rw [hbase]))
  exact this

include s in
/-- **The `K W`-action on the model `S₁`** (Peterfalvi Part II, Ch. III §3, p. 121,
step (4)): `(x, y)^{(k,v)} = (μ(k,v)·x, μ(k,1)^d·y)` is a homomorphism into
`Aut S₁`, whose image is the book's subgroup `B`.

The central-coordinate scalar is `μ(k,1)^d` — the scaling constant of `χ`, which by
`centreQuadraticMap_smul_KW` does not involve the `W`-component.  In the book's
notation it is `a^{1+σ}` for `a = μ(k,v)`; well-definedness rests on the diagonal
scaling of the cocycle, not on its `F`-semilinearity, since `W₁ ⊄ F`. -/
theorem exists_modelScalarHom
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (hdiagscale : ∀ a b : M.E,
      (∀ x : M.E, ((hyp.centreQuadraticMap s M ι (a * x) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = b * ((hyp.centreQuadraticMap s M ι x :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) →
      ∀ x y : M.E, ((φ (a * x) (a * y) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = b * ((φ x y :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)) :
    ∃ Θ : ↥hyp.actualKActor × ↥hyp.W →*
        MulAut (Suzuki2Groups.BilinearTwistedProduct φ),
      (∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
        (p : Suzuki2Groups.BilinearTwistedProduct φ),
          (Θ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient) ∧
      ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
        (p : Suzuki2Groups.BilinearTwistedProduct φ),
          (((Θ kv p).central :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
            = ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E) *
              ((p.central :
                ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) := by
  refine ⟨hyp.modelScalarHom M φ M.mu
    ((zpowGroupHom d).comp ((hyp.muKUnitHom M).comp (MonoidHom.fst _ _)))
    (fun kv x y => ?_), fun kv p => rfl, fun kv p => ?_⟩
  · -- compatibility: the diagonal scaling with constant `μ(kv.1, 1)^d`
    refine Subtype.ext ?_
    rw [show (((((zpowGroupHom d).comp ((hyp.muKUnitHom M).comp
          (MonoidHom.fst ↥hyp.actualKActor ↥hyp.W))) kv :
        (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * φ x y :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)).val
      = ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E) * ((φ x y :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) by
      rw [Submonoid.coe_mul]
      exact congrArg (· * _) (hyp.muKUnitHom_zpow_val M kv.1 d)]
    exact hdiagscale _ _ (hyp.centreQuadraticMap_smul_KW s M ι d hequiv kv) x y
  · -- the central coordinate
    change ((((((zpowGroupHom d).comp ((hyp.muKUnitHom M).comp
        (MonoidHom.fst ↥hyp.actualKActor ↥hyp.W))) kv :
      (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * p.central :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) = _
    rw [Submonoid.coe_mul]
    exact congrArg (· * _) (hyp.muKUnitHom_zpow_val M kv.1 d)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
