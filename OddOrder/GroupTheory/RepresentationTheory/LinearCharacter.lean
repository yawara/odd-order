/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SchurCenterBound
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing

/-!
# Linear characters from group homomorphisms to `ℂˣ`

A group homomorphism `χ : H →* ℂˣ` defines a one-dimensional representation `h ↦ χ h • id`
of `H` on `ℂ`, irreducible by `isIrreducible_complex_rep`.  Its character is the class
function `h ↦ (χ h : ℂ)`.  This packages such **linear characters** (degree-one irreducible
characters) as `IrreducibleCharacter H` and records the basic API used by the Peterfalvi
(6.8) `Y = S(H')` family construction, whose members are induced from the nontrivial linear
characters of `H` (`= Irr(H/H') ∖ {1}`).

Main definitions / results:
* `linearClassFunction χ`, `linearIrreducibleCharacter χ` for `χ : H →* ℂˣ`.
* `linearIrreducibleCharacter_apply`, `..._apply_one` (degree one).
* `linearIrreducibleCharacter_injective`, `linearIrreducibleCharacter_eq_trivial_iff`.
-/

namespace OddOrder.RepresentationTheory

variable {H : Type*} [Group H]

/-- The class function `h ↦ (χ h : ℂ)` attached to a homomorphism `χ : H →* ℂˣ`.  It is a
class function because the target `ℂˣ` is commutative. -/
def linearClassFunction (χ : H →* ℂˣ) : ClassFunction H ℂ :=
  ⟨fun h => (χ h : ℂ), fun g h =>
    congrArg (fun u : ℂˣ => (u : ℂ)) (by
      rw [map_mul, map_mul, map_inv, mul_comm (χ h) (χ g)]; group)⟩

@[simp] theorem linearClassFunction_apply (χ : H →* ℂˣ) (h : H) :
    (linearClassFunction χ) h = (χ h : ℂ) := rfl

/-- A homomorphism `χ : H →* ℂˣ` as a (linear, degree-one) irreducible character. -/
noncomputable def linearIrreducibleCharacter (χ : H →* ℂˣ) : IrreducibleCharacter H :=
  ⟨linearClassFunction χ, ℂ, inferInstance, inferInstance, inferInstance,
    { toFun := fun h => (χ h : ℂ) • (LinearMap.id : Module.End ℂ ℂ)
      map_one' := by
        rw [map_one, Units.val_one]; ext; simp [Module.End.one_apply]
      map_mul' := fun h₁ h₂ => by
        rw [map_mul, Units.val_mul]; ext
        simp [Module.End.mul_apply, smul_smul, mul_comm] },
    isIrreducible_complex_rep _, by
      funext h
      change (χ h : ℂ) = LinearMap.trace ℂ ℂ ((χ h : ℂ) • LinearMap.id)
      rw [map_smul, LinearMap.trace_id]; simp⟩

@[simp] theorem linearIrreducibleCharacter_coe (χ : H →* ℂˣ) :
    (linearIrreducibleCharacter χ : ClassFunction H ℂ) = linearClassFunction χ := rfl

@[simp] theorem linearIrreducibleCharacter_apply (χ : H →* ℂˣ) (h : H) :
    ((linearIrreducibleCharacter χ : ClassFunction H ℂ)) h = (χ h : ℂ) := rfl

@[simp] theorem linearIrreducibleCharacter_apply_one (χ : H →* ℂˣ) :
    ((linearIrreducibleCharacter χ : ClassFunction H ℂ)) (1 : H) = 1 := by
  rw [linearIrreducibleCharacter_apply, map_one, Units.val_one]

theorem linearIrreducibleCharacter_injective :
    Function.Injective (linearIrreducibleCharacter (H := H)) := by
  intro χ₁ χ₂ h
  refine MonoidHom.ext fun g => Units.val_injective ?_
  have hg : ((linearIrreducibleCharacter χ₁ : ClassFunction H ℂ)) g =
      ((linearIrreducibleCharacter χ₂ : ClassFunction H ℂ)) g :=
    congrArg (fun c : ClassFunction H ℂ => c g) (Subtype.ext_iff.mp h)
  simpa only [linearIrreducibleCharacter_apply] using hg

@[simp] theorem linearIrreducibleCharacter_eq_trivial_iff {χ : H →* ℂˣ} :
    linearIrreducibleCharacter χ = trivialIrreducibleCharacter H ↔ χ = 1 := by
  rw [Subtype.ext_iff]
  constructor
  · intro h
    refine MonoidHom.ext fun g => ?_
    have hg : ((χ g : ℂ)) = 1 := by
      have := congrArg (fun c : ClassFunction H ℂ => c g) h
      simpa [linearClassFunction_apply, trivialClassFunction_apply] using this
    simpa using Units.val_eq_one.mp hg
  · intro h
    subst h
    ext g
    simp [linearClassFunction_apply, trivialClassFunction_apply]

end OddOrder.RepresentationTheory
