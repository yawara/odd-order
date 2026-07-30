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

/-! ## The conjugation action `A`, transported to the model -/

/-- **The transported conjugation action on the quotient coordinate**: `K W` acting
on `S ≅ S₁` by conjugation multiplies the quotient coordinate by `μ(k,v)`, exactly
as the model action does.

Chain: the isomorphism reads the quotient coordinate as `M.coord` of the class
(`hquot`), conjugation on `Q` induces the `K × W`-action on `Q ⧸ Z(Q)`
(`quotientKWHom_mk`), and that action is multiplication by `μ` (`coord_act`). -/
theorem congr_conjQHom_quotient
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hquot : ∀ e : ↥hyp.Q, (Φ e).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e)))
    (kv : ↥hyp.actualKActor × ↥hyp.W)
    (p : Suzuki2Groups.BilinearTwistedProduct φ) :
    ((MulAut.congr Φ) (hyp.conjQHom kv) p).quotient
      = ((M.mu kv : M.Eˣ) : M.E) * p.quotient := by
  have hp : (MulAut.congr Φ) (hyp.conjQHom kv) p = Φ (hyp.conjQHom kv (Φ.symm p)) := rfl
  rw [hp, hquot]
  have hmk : (QuotientGroup.mk' (Subgroup.center hyp.Q) (hyp.conjQHom kv (Φ.symm p)))
      = hyp.quotientKWHom kv
        (QuotientGroup.mk' (Subgroup.center hyp.Q) (Φ.symm p)) := rfl
  rw [hmk, M.coord_act, ← hquot, Φ.apply_symm_apply]

include s in
/-- **The transported conjugation action on the kernel coordinate**: on the centre
of `Q` the `W`-part acts trivially (`conjQByW_fixes_center`), so conjugation
restricts to `centerKHom`, whose effect in the coordinate `ι` is multiplication by
`μ(k,1)^d` — again exactly the model action. -/
theorem congr_conjQHom_central
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
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    (kv : ↥hyp.actualKActor × ↥hyp.W)
    (w : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) :
    ((((MulAut.congr Φ) (hyp.conjQHom kv) ⟨0, w⟩).central :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
      = ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E) * (w : M.E) := by
  -- the preimage of `⟨0, w⟩` is the central element with coordinate `w`
  set z : ↥(Subgroup.center hyp.Q) := Additive.toMul (ι.symm w) with hz
  have hzw : ι (Additive.ofMul z) = w := by
    rw [hz]
    exact ι.apply_symm_apply w
  have hpre : Φ.symm (⟨0, w⟩ : Suzuki2Groups.BilinearTwistedProduct φ) = (z : ↥hyp.Q) := by
    refine Φ.injective ?_
    rw [Φ.apply_symm_apply, hker z, hzw]
  -- conjugation fixes the `W`-part on the centre and is `centerKHom` on the `K`-part
  have hconj : hyp.conjQHom kv (z : ↥hyp.Q) = ((hyp.centerKHom kv.1 z : _) : ↥hyp.Q) := by
    have hW : hyp.conjQByW kv.2 (z : ↥hyp.Q) = (z : ↥hyp.Q) :=
      hyp.conjQByW_fixes_center s.centerEqQ0 kv.2 (z : ↥hyp.Q) z.2
    have : hyp.conjQHom kv (z : ↥hyp.Q)
        = hyp.actualKActor.subtype kv.1 (hyp.conjQByW kv.2 (z : ↥hyp.Q)) := rfl
    rw [this, hW, hyp.centerKHom_apply_val]
  have hp : (MulAut.congr Φ) (hyp.conjQHom kv) (⟨0, w⟩ : Suzuki2Groups.BilinearTwistedProduct φ)
      = Φ (hyp.conjQHom kv (Φ.symm ⟨0, w⟩)) := rfl
  rw [hp, hpre, hconj, hker, hequiv kv.1 z, hzw]

include s in
/-- **`A` and `B` differ by `U`, elementwise** (Peterfalvi Part II, Ch. III §3,
p. 121, step (4): "by (1), `B ⊆ U A`").

For each `(k,v)`, the conjugation action transported to the model and the model's
own scalar action induce the *same* maps on both ends of the extension — both
multiply the quotient coordinate by `μ(k,v)` and the kernel coordinate by
`μ(k,1)^d` — so their ratio lies in `U`.

This is stronger than the book's inclusion `B ⊆ U A`: it gives the two subgroups
the same product with `U`, i.e. `U A = U B`, which is what the complement form of
the Zassenhaus argument needs. -/
theorem congr_conjQHom_mul_inv_mem_inducingIdAuts
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
    (Φ : ↥hyp.Q ≃* Suzuki2Groups.BilinearTwistedProduct φ)
    (hker : ∀ z : ↥(Subgroup.center hyp.Q),
      Φ (z : ↥hyp.Q) = ⟨0, ι (Additive.ofMul z)⟩)
    (hquot : ∀ e : ↥hyp.Q, (Φ e).quotient =
      M.coord (Additive.ofMul (QuotientGroup.mk' (Subgroup.center hyp.Q) e)))
    (Θ : ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (hΘq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (Θ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient)
    (hΘc : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (((Θ kv p).central :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
          = ((M.mu (kv.1, 1) ^ d : M.Eˣ) : M.E) *
            ((p.central :
              ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    (kv : ↥hyp.actualKActor × ↥hyp.W) :
    (Θ kv)⁻¹ * (MulAut.congr Φ) (hyp.conjQHom kv) ∈
      (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inducingIdAuts := by
  -- the inverse of `Θ kv` is `Θ` at the inverse, so its formulas come for free
  have hinvΘ : (Θ kv)⁻¹ = Θ kv⁻¹ := (map_inv Θ kv).symm
  have hmuinv : ((M.mu kv⁻¹ : M.Eˣ) : M.E) = (((M.mu kv)⁻¹ : M.Eˣ) : M.E) := by
    rw [map_inv]
  have hnuinv : ((M.mu (kv⁻¹.1, 1) ^ d : M.Eˣ) : M.E)
      = (((M.mu (kv.1, 1) ^ d)⁻¹ : M.Eˣ) : M.E) := by
    rw [← inv_zpow, ← map_inv]
    congr 3
    exact Prod.ext rfl (inv_one (G := ↥hyp.W)).symm
  refine ⟨fun w => ?_, fun e => ?_⟩
  · -- the kernel is fixed
    have hinl : (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inl w
        = (⟨0, w.toAdd⟩ : Suzuki2Groups.BilinearTwistedProduct φ) := rfl
    rw [hinl]
    refine Suzuki2Groups.BilinearTwistedProduct.ext ?_ ?_
    · -- quotient coordinate stays `0`
      change ((Θ kv)⁻¹ ((MulAut.congr Φ) (hyp.conjQHom kv) _)).quotient = _
      rw [hinvΘ, hΘq, hyp.congr_conjQHom_quotient M φ Φ hquot]
      change _ * (((M.mu kv : M.Eˣ) : M.E) * (0 : M.E)) = (0 : M.E)
      rw [mul_zero, mul_zero]
    · -- kernel coordinate is restored
      refine Subtype.ext ?_
      change (((Θ kv)⁻¹ ((MulAut.congr Φ) (hyp.conjQHom kv) _)).central : M.E) = _
      rw [hinvΘ, hΘc, hyp.congr_conjQHom_central s M ι d hequiv φ Φ hker,
        hnuinv, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  · -- the quotient is fixed
    change Multiplicative.ofAdd
      ((Θ kv)⁻¹ ((MulAut.congr Φ) (hyp.conjQHom kv) e)).quotient = _
    rw [hinvΘ, hΘq, hyp.congr_conjQHom_quotient M φ Φ hquot, hmuinv, ← mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rfl

/-! ## The complement conditions for the Zassenhaus argument -/

/-- **An automorphism of the model that lies in `U` cannot scale the quotient
coordinate.**  Evaluating the `InducesId` condition at `⟨1, 0⟩` reads the scalar
off directly.

This is what makes both `A` and `B` meet `U` trivially, once `μ` is known to be
faithful (`mu_injective`). -/
theorem eq_one_of_mem_inducingIdAuts_of_quotient_smul
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (Ψ : MulAut (Suzuki2Groups.BilinearTwistedProduct φ)) (u : M.Eˣ)
    (hΨ : ∀ p : Suzuki2Groups.BilinearTwistedProduct φ,
      (Ψ p).quotient = ((u : M.Eˣ) : M.E) * p.quotient)
    (hmem : Ψ ∈ (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inducingIdAuts) :
    u = 1 := by
  have h := hmem.2 (⟨1, 0⟩ : Suzuki2Groups.BilinearTwistedProduct φ)
  have hq : (Ψ (⟨1, 0⟩ : Suzuki2Groups.BilinearTwistedProduct φ)).quotient
      = (⟨1, 0⟩ : Suzuki2Groups.BilinearTwistedProduct φ).quotient :=
    congrArg (fun z : Multiplicative M.E => z.toAdd) h
  rw [hΨ] at hq
  refine Units.ext ?_
  rw [Units.val_one]
  change ((u : M.Eˣ) : M.E) * (1 : M.E) = (1 : M.E) at hq
  rwa [mul_one] at hq

include s in
/-- **The model action is injective**: it determines the scalar `μ(k,v)`, and `μ`
is faithful. -/
theorem modelScalarHom_injective_of_quotient
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card hyp.Q0 ^ 3)
    (inductionHypothesis : TheoremAInductionBelow G Ω)
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (Θ : ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (hΘq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (Θ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient) :
    Function.Injective Θ := by
  have hker : ∀ kv, Θ kv = 1 → kv = 1 := by
    intro kv hkv
    refine hyp.mu_injective hst hm hQ0card hcardQ inductionHypothesis s M ?_
    rw [map_one]
    refine hyp.eq_one_of_mem_inducingIdAuts_of_quotient_smul M φ (Θ kv) (M.mu kv)
      (hΘq kv) ?_
    rw [hkv]
    exact Subgroup.one_mem _
  intro a b hab
  have hmul : Θ (a⁻¹ * b) = 1 := by
    rw [map_mul, ← hab, ← map_mul, inv_mul_cancel, map_one]
  have := hker _ hmul
  rwa [inv_mul_eq_one] at this

include s in
/-- **`U` meets the image of a scalar action trivially.**

Stated for any homomorphism into `Aut S₁` whose quotient-coordinate effect is
multiplication by `μ` — which covers both the model action `B` and the transported
conjugation action `A` (`congr_conjQHom_quotient`).  This is the complement
condition `U ∩ A = U ∩ B = 1` of the Zassenhaus step. -/
theorem inducingIdAuts_inf_range_eq_bot
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card hyp.Q0 ^ 3)
    (inductionHypothesis : TheoremAInductionBelow G Ω)
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (Ξ : ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (Suzuki2Groups.BilinearTwistedProduct φ))
    (hΞq : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
      (p : Suzuki2Groups.BilinearTwistedProduct φ),
        (Ξ kv p).quotient = ((M.mu kv : M.Eˣ) : M.E) * p.quotient) :
    (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inducingIdAuts ⊓ Ξ.range
      = ⊥ := by
  rw [eq_bot_iff]
  rintro Ψ ⟨hU, kv, rfl⟩
  have hu : M.mu kv = 1 :=
    hyp.eq_one_of_mem_inducingIdAuts_of_quotient_smul M φ (Ξ kv) (M.mu kv) (hΞq kv) hU
  have hkv : kv = 1 :=
    hyp.mu_injective hst hm hQ0card hcardQ inductionHypothesis s M
      (by rw [hu, map_one])
  rw [hkv, map_one]
  exact Subgroup.mem_bot.mpr rfl

/-- **A scalar automorphism of the model normalizes `U`.**

Both the model action `B` and the transported conjugation action `A` scale the two
coordinates by units, hence map the kernel onto itself; `inducingIdAuts_conj_mem`
then applies.  This is `U ⊴ U A` of Peterfalvi Part II, Ch. III §3, p. 121,
step (4). -/
theorem inducingIdAuts_conj_mem_of_scalar
    (φ : LinearMap.BilinMap (ZMod 2) M.E
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    (Ψ : MulAut (Suzuki2Groups.BilinearTwistedProduct φ)) (u : M.Eˣ)
    (ν : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ)
    (hq : ∀ p : Suzuki2Groups.BilinearTwistedProduct φ,
      (Ψ p).quotient = ((u : M.Eˣ) : M.E) * p.quotient)
    (hc : ∀ w : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m),
      (Ψ (⟨0, w⟩ : Suzuki2Groups.BilinearTwistedProduct φ)).central
        = ((ν : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * w)
    {x : MulAut (Suzuki2Groups.BilinearTwistedProduct φ)}
    (hx : x ∈ (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inducingIdAuts) :
    Ψ * x * Ψ⁻¹ ∈
      (Suzuki2Groups.BilinearTwistedProduct.groupExtension φ).inducingIdAuts := by
  refine GroupExtension.inducingIdAuts_conj_mem _ Ψ
    (fun w => Multiplicative.ofAdd
      (((ν : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * w.toAdd))
    (fun y => Multiplicative.ofAdd (((u : M.Eˣ) : M.E) * y.toAdd))
    (fun w => ⟨Multiplicative.ofAdd
      (((ν⁻¹ : (↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))ˣ) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) * w.toAdd), by
      simp only [toAdd_ofAdd, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul, ofAdd_toAdd]⟩)
    (fun w => ?_) (fun e => ?_) hx
  · refine Suzuki2Groups.BilinearTwistedProduct.ext ?_ ?_
    · change (Ψ (⟨0, w.toAdd⟩ : Suzuki2Groups.BilinearTwistedProduct φ)).quotient = 0
      rw [hq]
      change ((u : M.Eˣ) : M.E) * (0 : M.E) = (0 : M.E)
      rw [mul_zero]
    · exact hc w.toAdd
  · exact congrArg Multiplicative.ofAdd (hq e)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
