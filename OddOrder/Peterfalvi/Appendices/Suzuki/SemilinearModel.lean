/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Ring.Action.End
import Mathlib.Algebra.Ring.AddAut
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Peterfalvi Part II, Chapter I §2 — the semilinear affine group

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Chapter I §2, p. 104.

Immediately before Proposition 3, Peterfalvi defines
`𝓛(F, A) = (F_add ⋊ Fˣ) ⋊ A`, where nonzero scalars act on the additive
group of `F` and `A ≤ Aut(F)` acts naturally on both coordinates.  This file
constructs that group honestly as `semilinearGroup F A`, including the full
action API.  It also proves that `Aut(F)` and all its subgroups are cyclic
when `F` is finite, the final clause used by Proposition 3.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

section FieldAffineGroup

variable (F : Type*) [Field F]

/-- The multiplicative group of nonzero scalars acts on the additive group of a field. -/
def fieldScalarAction : Fˣ →* MulAut (Multiplicative F) :=
  (MulAutMultiplicative F).symm.toMonoidHom.comp (AddAut.mulLeft (R := F))

@[simp]
theorem fieldScalarAction_apply (u : Fˣ) (x : Multiplicative F) :
    Multiplicative.toAdd (fieldScalarAction F u x) =
      (u : F) * Multiplicative.toAdd x := rfl

/-- The affine group `F_add ⋊ Fˣ`. -/
abbrev fieldAffineGroup := Multiplicative F ⋊[fieldScalarAction F] Fˣ

/-- Ring automorphisms act on the additive group of a field. -/
def fieldRingAutOnAdditive : RingAut F →* MulAut (Multiplicative F) :=
  (MulAutMultiplicative F).symm.toMonoidHom.comp (RingAut.toAddAut F)

@[simp]
theorem fieldRingAutOnAdditive_apply (σ : RingAut F) (x : Multiplicative F) :
    Multiplicative.toAdd (fieldRingAutOnAdditive F σ x) =
      σ (Multiplicative.toAdd x) := rfl

/-- Ring automorphisms act on the units of a field. -/
def fieldRingAutOnUnits : RingAut F →* MulAut Fˣ where
  toFun σ := Units.mapEquiv σ.toMulEquiv
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem fieldRingAutOnUnits_apply_val (σ : RingAut F) (u : Fˣ) :
    ((fieldRingAutOnUnits F σ u : Fˣ) : F) = σ (u : F) := rfl

/-- The natural action of ring automorphisms on the affine group. -/
def fieldRingAutOnAffine : RingAut F →* MulAut (fieldAffineGroup F) where
  toFun σ :=
    SemidirectProduct.congr (fieldRingAutOnAdditive F σ) (fieldRingAutOnUnits F σ)
      (fun u => by
        ext x
        change σ ((u : F) * Multiplicative.toAdd x) =
          σ (u : F) * σ (Multiplicative.toAdd x)
        exact map_mul σ _ _)
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

@[simp]
theorem fieldRingAutOnAffine_apply_left (σ : RingAut F) (x : fieldAffineGroup F) :
    Multiplicative.toAdd (fieldRingAutOnAffine F σ x).left =
      σ (Multiplicative.toAdd x.left) := rfl

@[simp]
theorem fieldRingAutOnAffine_apply_right_val (σ : RingAut F) (x : fieldAffineGroup F) :
    ((fieldRingAutOnAffine F σ x).right : F) = σ (x.right : F) := rfl

/-- The semilinear affine group `(F_add ⋊ Fˣ) ⋊ A`. -/
abbrev semilinearGroup (A : Subgroup (RingAut F)) :=
  fieldAffineGroup F ⋊[(fieldRingAutOnAffine F).comp A.subtype] A

@[simp]
theorem semilinearGroup_action_apply_left (A : Subgroup (RingAut F)) (a : A)
    (x : fieldAffineGroup F) :
    Multiplicative.toAdd (((fieldRingAutOnAffine F).comp A.subtype) a x).left =
      (a : RingAut F) (Multiplicative.toAdd x.left) := rfl

@[simp]
theorem semilinearGroup_action_apply_right_val (A : Subgroup (RingAut F)) (a : A)
    (x : fieldAffineGroup F) :
    ((((fieldRingAutOnAffine F).comp A.subtype) a x).right : F) =
      (a : RingAut F) (x.right : F) := rfl

end FieldAffineGroup

section FiniteFieldAutomorphisms

variable (F : Type*) [Field F] [Finite F]

/-- The ring automorphism group of a finite field is cyclic. -/
theorem ringAut_isCyclic_of_finite : IsCyclic (RingAut F) := by
  letI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.prime_ringChar F⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  let toAlgAut : RingAut F →* (F ≃ₐ[ZMod (ringChar F)] F) :=
    { toFun := fun f => AlgEquiv.ofRingEquiv (f := f) (fun x => by
        obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
        simp)
      map_one' := by ext; rfl
      map_mul' := by intro f g; ext; rfl }
  exact isCyclic_of_injective toAlgAut (by
    intro f g h
    ext x
    exact DFunLike.congr_fun h x)

noncomputable instance instIsCyclicRingAutOfFinite : IsCyclic (RingAut F) :=
  ringAut_isCyclic_of_finite F

/-- Every subgroup of the automorphism group of a finite field is cyclic. -/
theorem ringAutSubgroup_isCyclic_of_finite (A : Subgroup (RingAut F)) : IsCyclic A :=
  inferInstance

end FiniteFieldAutomorphisms

end OddOrder.Peterfalvi.Appendices.Suzuki
