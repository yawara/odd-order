/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Conjugate of a character: `χ(g⁻¹) = conj (χ(g))`

For a finite-dimensional complex representation `ρ` of a finite group `G`, the value of the
character at `g⁻¹` is the complex conjugate of its value at `g`:

  `ρ.character g⁻¹ = star (ρ.character g)`.

The proof avoids eigenvalues: fixing a basis, write `Mₕ` for the matrix of `ρ h` and form the
group-averaged Gram matrix `S = ∑ₕ Mₕᴴ Mₕ`, which is positive definite (hence invertible).
The homomorphism property of `ρ` together with reindexing the sum by `h ↦ h·g` gives the
invariance `Mᴴ S M = S` for `M = M_g`, whence `M⁻¹ = S⁻¹ Mᴴ S` and, using that trace is
cyclic and `trace Aᴴ = star (trace A)`,

  `trace (ρ g⁻¹) = trace M⁻¹ = trace (S⁻¹ Mᴴ S) = trace Mᴴ = star (trace M) = star (trace (ρ g))`.

mathlib provides `Representation.char_orthonormal` only in the `g⁻¹` form, while Peterfalvi's
class-function inner product `(α, β)_G = |G|⁻¹ ∑ α(g) · conj(β(g))` uses complex conjugation;
this lemma bridges the two and is the foundation for discharging
`CharacterTableRowOrthogonality`.
-/

namespace OddOrder.RepresentationTheory

open Matrix
open scoped ComplexOrder

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- For a finite-dimensional complex representation of a finite group,
`χ(g⁻¹) = conj (χ(g))`. -/
theorem character_inv (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = star (ρ.character g) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let b := Module.Free.chooseBasis ℂ V
  let Mat : G → Matrix (Module.Free.ChooseBasisIndex ℂ V) (Module.Free.ChooseBasisIndex ℂ V) ℂ :=
    fun h => LinearMap.toMatrix b b (ρ h)
  have hmul : ∀ h₁ h₂ : G, Mat (h₁ * h₂) = Mat h₁ * Mat h₂ := by
    intro h₁ h₂
    change LinearMap.toMatrix b b (ρ (h₁ * h₂)) = _
    rw [map_mul, LinearMap.toMatrix_mul]
  have hone : Mat 1 = 1 := by
    change LinearMap.toMatrix b b (ρ 1) = 1
    rw [map_one, LinearMap.toMatrix_one]
  have hchar : ∀ h : G, ρ.character h = (Mat h).trace := by
    intro h
    change LinearMap.trace ℂ V (ρ h) = _
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
  -- every `Mat h` is invertible
  have hMatUnit : ∀ h : G, IsUnit (Mat h) := fun h =>
    IsUnit.of_mul_eq_one (b := Mat h⁻¹) (by rw [← hmul h h⁻¹, mul_inv_cancel, hone])
  set M := Mat g with hMdef
  -- `Mat g⁻¹` is the two-sided inverse of `M`.
  have hLinv : Mat g⁻¹ * M = 1 := by rw [hMdef, ← hmul g⁻¹ g, inv_mul_cancel, hone]
  have hRinv : M * Mat g⁻¹ = 1 := by rw [hMdef, ← hmul g g⁻¹, mul_inv_cancel, hone]
  have hMdet : IsUnit M.det :=
    IsUnit.of_mul_eq_one (b := (Mat g⁻¹).det)
      (by rw [← Matrix.det_mul, hRinv, Matrix.det_one])
  have hMinv : M⁻¹ = Mat g⁻¹ := Matrix.inv_eq_left_inv hLinv
  -- the group-averaged Gram matrix is positive definite, hence invertible
  set S : Matrix (Module.Free.ChooseBasisIndex ℂ V) (Module.Free.ChooseBasisIndex ℂ V) ℂ :=
    ∑ h : G, (Mat h)ᴴ * Mat h with hSdef
  have hSpd : S.PosDef := by
    rw [hSdef]
    refine Matrix.posDef_sum Finset.univ_nonempty (fun h _ => ?_)
    exact Matrix.PosDef.conjTranspose_mul_self (Mat h)
      (Matrix.mulVec_injective_of_isUnit (hMatUnit h))
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSpd.isUnit
  -- invariance `Mᴴ S M = S` from reindexing the sum by `h ↦ h · g`
  have hterm : ∀ h : G, Mᴴ * ((Mat h)ᴴ * Mat h) * M = (Mat (h * g))ᴴ * Mat (h * g) := by
    intro h
    rw [hmul h g, Matrix.conjTranspose_mul, hMdef]
    simp only [Matrix.mul_assoc]
  have hSinv : Mᴴ * S * M = S := by
    rw [hSdef, Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun h _ => hterm h)]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => by rw [Equiv.coe_mulRight])
  -- `M⁻¹ = S⁻¹ Mᴴ S`.
  have hMinv2 : M⁻¹ = S⁻¹ * Mᴴ * S := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc (S⁻¹ * Mᴴ) S M, Matrix.mul_assoc S⁻¹ Mᴴ (S * M),
      ← Matrix.mul_assoc Mᴴ S M, hSinv, Matrix.nonsing_inv_mul S hSdet]
  -- conclude
  rw [hchar g⁻¹, hchar g, ← hMinv, hMinv2, Matrix.trace_mul_cycle,
    Matrix.mul_nonsing_inv S hSdet, Matrix.one_mul, Matrix.trace_conjTranspose]

end OddOrder.RepresentationTheory
