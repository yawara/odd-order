/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CliffordMultiplicityOne
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Conjugate characters of the constituents of a restriction (toward BG Prop 2.2(a)'s `hconj`)

`OddOrder.GroupTheory.RepresentationTheory` shared module.  For `ρ : Representation k G V`, a normal
subgroup `H ⊴ G`, and a `k[H]`-submodule `W` of the restriction, conjugation by `g` (realised by the
`k`-linear automorphism `ρ g`) carries the subrepresentation on `W` to the subrepresentation on the
conjugate `(ρ g)(W)`, twisting the `H`-action by `h ↦ g⁻¹ h g`.  At the level of characters this is

  `χ_{(ρ g)(W)}(h) = χ_W(g⁻¹ h g)`     (`character_subRep_conj`).

This is the bridge that turns the **Bender–Glauberman Proposition 2.2(a)** hypothesis `M ≅ M^g` into
a *character* identity: combined with the vanishing of the character of a faithful irreducible
extraspecial constituent off its centre (`ExtraspecialFaithful.character_eq_zero_of_notMem_center`,
Gorenstein 5.5.5) and the centralising of `Z(P)` by `x`, it forces `χ_{W^g} = χ_W`, whence Schur
orthogonality (`Representation.char_orthonormal`, valid over any algebraically closed field of
characteristic prime to `|H|`) gives `W ≅ W^g` — the input to `restriction_isIrreducible`.  This
replaces a from-scratch formalisation of Gorenstein 5.5.4.

## Main statements

* `repEquiv` — `ρ g` packaged as a `k`-linear automorphism of `V`.
* `character_subRep_conj` — the conjugate character identity `χ_{(ρ g)(W)}(h) = χ_W(g⁻¹ h g)`.
-/

namespace OddOrder.RepresentationTheory

open Representation
open scoped MonoidAlgebra

variable {G : Type*} [Group G]
variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- `ρ g` as a `k`-linear automorphism of `V`. -/
noncomputable def repEquiv (g : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinear (ρ g) (ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id])

@[simp] theorem repEquiv_apply (g : G) (v : V) : repEquiv ρ g v = ρ g v := rfl

/-- Global conjugation identity: `ρ h ∘ ρ g = ρ g ∘ ρ (g⁻¹ h g)`. -/
theorem repEquiv_conj (g : G) (h : G) :
    (ρ h) ∘ₗ (repEquiv ρ g).toLinearMap
      = (repEquiv ρ g).toLinearMap ∘ₗ (ρ (g⁻¹ * h * g)) := by
  ext v
  simp only [LinearMap.comp_apply, repEquiv_apply, LinearEquiv.coe_coe]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

section ConjChar

variable {H : Subgroup G} [hH : H.Normal]
variable (W : Submodule k[↥H] (resRep ρ H).asModule)

/-- The underlying `k`-submodule of the conjugate `(ρ g)(W)` equals the `repEquiv ρ g`-image of the
underlying `k`-submodule of `W`. -/
theorem ofSubmodule'_map_toSubmodule (g : G) :
    (Subrepresentation.ofSubmodule' (W.map (conjSemilinearEnd (H := H) ρ g))).toSubmodule
      = (Subrepresentation.ofSubmodule' W).toSubmodule.map (repEquiv ρ g).toLinearMap := by
  apply Submodule.ext
  intro v
  simp only [Submodule.mem_map, repEquiv_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩

/-- The restricted `k`-linear equivalence between the constituent on `W` and the constituent on the
conjugate `(ρ g)(W)`, induced by `repEquiv ρ g`. -/
noncomputable def conjSubEquiv (g : G) :
    (Subrepresentation.ofSubmodule' W).toSubmodule ≃ₗ[k]
      (Subrepresentation.ofSubmodule' (W.map (conjSemilinearEnd (H := H) ρ g))).toSubmodule :=
  (Submodule.equivMapOfInjective (repEquiv ρ g).toLinearMap (repEquiv ρ g).injective _).trans
    (LinearEquiv.ofEq _ _ (ofSubmodule'_map_toSubmodule ρ W g).symm)

@[simp] theorem conjSubEquiv_coe (g : G)
    (w : (Subrepresentation.ofSubmodule' W).toSubmodule) :
    (conjSubEquiv ρ W g w : V) = ρ g (w : V) := by
  simp only [conjSubEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Submodule.coe_equivMapOfInjective_apply, LinearEquiv.coe_coe, repEquiv_apply]

omit hH in
/-- Coe of the subrepresentation action: `(σ.toRepresentation h) w = ρ h w` in `V`. -/
theorem coe_toRepresentation_apply (σ : Subrepresentation (resRep ρ H)) (h : ↥H)
    (w : σ.toSubmodule) :
    ((σ.toRepresentation h) w : V) = ρ (h : G) (w : V) := rfl

/-- **Conjugate character** (the bridge for BG Prop 2.2(a)'s `hconj`).  The character of the
conjugate constituent `(ρ g)(W)` at `h` equals the character of `W` at `g⁻¹ h g`.  Proof: `repEquiv`
realises an isomorphism of representations between `(ρ g)(W)` and `W` precomposed with the
conjugation automorphism `h ↦ g⁻¹ h g`, so `Representation.char_iso` equates their characters. -/
theorem character_subRep_conj [FiniteDimensional k V] (g : G) (h : ↥H) :
    ((Subrepresentation.ofSubmodule'
        (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character h
      = ((Subrepresentation.ofSubmodule' W).toRepresentation).character
          (conjNormalMulAut H g⁻¹ h) := by
  have hequiv : Representation.Equiv
      (((Subrepresentation.ofSubmodule' W).toRepresentation).comp
        (conjNormalMulAut H g⁻¹).toMonoidHom)
      ((Subrepresentation.ofSubmodule'
        (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation) :=
    Representation.Equiv.mk (conjSubEquiv ρ W g) (by
      intro h'
      ext w
      have hconj := LinearMap.congr_fun (repEquiv_conj ρ g (h' : G)) (w : V)
      simp only [LinearMap.comp_apply, repEquiv_apply, LinearEquiv.coe_coe] at hconj
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, conjSubEquiv_coe,
        MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_toRepresentation_apply,
        conjNormalMulAut_apply_coe, inv_inv]
      exact hconj.symm)
  exact (congrFun (Representation.char_iso hequiv) h).symm

end ConjChar

end OddOrder.RepresentationTheory
