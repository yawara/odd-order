/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CliffordMultiplicityOne
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialFaithful
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

/-- A group automorphism preserves the centre: `e h` is central iff `h` is. -/
theorem mulEquiv_mem_center_iff {Γ : Type*} [Group Γ] (e : Γ ≃* Γ) (h : Γ) :
    e h ∈ Subgroup.center Γ ↔ h ∈ Subgroup.center Γ := by
  simp only [Subgroup.mem_center_iff]
  refine ⟨fun H z => e.injective ?_, fun H y => ?_⟩
  · rw [map_mul, map_mul, H (e z)]
  · rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, H (e.symm y)]

section SubrepAsModule

/-! General-field analogues of the `ℂ`-pinned `ofSubmodulePrime*` lemmas in `CharacterCompleteness`,
needed over the algebraically closed base field of BG Theorem 2.5.  (The `ℂ` versions should be
unified with these once the character-completeness file is de-`ℂ`-pinned.) -/

variable {J : Type*} [Monoid J] {M : Type*} [AddCommGroup M] [Module k M]
variable (σ : Representation k J M)

set_option backward.isDefEq.respectTransparency false in
/-- The `k[J]`-action on the `asModule` of a subrepresentation `ofSubmodule' N` is the ambient
action restricted. -/
theorem subRep_coe_smul (N : Submodule k[J] σ.asModule) (c : k[J])
    (v : (Subrepresentation.ofSubmodule' N).toRepresentation.asModule) :
    ((c • v).1 : σ.asModule) = c • (show σ.asModule from v.1) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_smul, add_smul, AddSubmonoid.coe_add, hx, hy]
  | single g a => rw [Representation.single_smul, Representation.single_smul]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- A `k[J]`-submodule `N` of `σ.asModule`, viewed as `ofSubmodule' N`, has its `asModule`
`k[J]`-linearly isomorphic to `N` (identity on the shared carrier). -/
noncomputable def subRepAsModuleEquiv (N : Submodule k[J] σ.asModule) :
    (↥N) ≃ₗ[k[J]] (Subrepresentation.ofSubmodule' N).toRepresentation.asModule where
  toFun v := v
  invFun w := w
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c v := by
    apply Subtype.ext
    rw [RingHom.id_apply, Submodule.coe_smul]
    exact (subRep_coe_smul σ N c v).symm

set_option backward.isDefEq.respectTransparency false in
/-- For a simple `k[J]`-submodule `N`, the subrepresentation `ofSubmodule' N` is irreducible. -/
theorem subRep_isIrreducible (N : Submodule k[J] σ.asModule) [IsSimpleModule k[J] (↥N)] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' N).toRepresentation := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (subRepAsModuleEquiv σ N).isSimpleModule_iff.mp inferInstance

/-- An isomorphism of representations is a `k[J]`-linear isomorphism of the `asModule`s. -/
noncomputable def equivAsModule {N : Type*} [AddCommGroup N] [Module k N]
    {ρ₁ : Representation k J M} {ρ₂ : Representation k J N} (φ : ρ₁.Equiv ρ₂) :
    ρ₁.asModule ≃ₗ[k[J]] ρ₂.asModule :=
  LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ₁ ρ₂ φ.toIntertwiningMap)
    φ.toLinearEquiv.bijective

end SubrepAsModule

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

/-- **The conjugate constituent has the same character** when `W` is a faithful irreducible
constituent (nilpotency class `≤ 2`) and `g` centralises `Z(H)`.  Combines the conjugate-character
identity with the vanishing of the character off the centre (`character_eq_zero_of_notMem_center`,
Gor 5.5.5): on the centre the conjugation `h ↦ g⁻¹ h g` is the identity, and off the centre both
characters vanish (the centre is automorphism-invariant). -/
theorem character_subRep_conj_eq [IsAlgClosed k] [FiniteDimensional k V] [IsSimpleModule k[↥H] ↥W]
    (hf : Function.Injective ((Subrepresentation.ofSubmodule' W).toRepresentation))
    (hcl : commutator ↥H ≤ Subgroup.center ↥H) (g : G)
    (hgc : ∀ z : ↥H, z ∈ Subgroup.center ↥H → conjNormalMulAut H g⁻¹ z = z) :
    ((Subrepresentation.ofSubmodule'
        (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character
      = ((Subrepresentation.ofSubmodule' W).toRepresentation).character := by
  haveI := subRep_isIrreducible (resRep ρ H) W
  haveI : FiniteDimensional k ↥((Subrepresentation.ofSubmodule' W).toSubmodule) := inferInstance
  funext h
  rw [character_subRep_conj]
  by_cases hmem : h ∈ Subgroup.center ↥H
  · rw [hgc h hmem]
  · rw [character_eq_zero_of_notMem_center _ hf hcl
        (fun hc => hmem ((mulEquiv_mem_center_iff (conjNormalMulAut H g⁻¹) h).mp hc)),
      character_eq_zero_of_notMem_center _ hf hcl hmem]

/-- **From equal characters to an isomorphism of constituents.**  If the simple constituent `W` and
its conjugate `(ρ g)(W)` have the same character (as `H`-representations), then they are isomorphic
as `k[H]`-modules.  Over an algebraically closed field with `char k ∤ |H|`, this is Schur
orthogonality (`Representation.char_orthonormal`): equal characters force the inner product
`⟨χ_W, χ_W⟩ = 1` to coincide with `⟦W ≅ (ρ g)(W)⟧`, so the latter is nonzero, i.e.
`W ≅ (ρ g)(W)`. -/
theorem submodule_iso_of_character_eq [IsAlgClosed k] [FiniteDimensional k V] [Finite ↥H]
    [Invertible (Nat.card ↥H : k)] [IsSimpleModule k[↥H] ↥W] (g : G)
    (hchar : ((Subrepresentation.ofSubmodule'
          (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character
        = ((Subrepresentation.ofSubmodule' W).toRepresentation).character) :
    Nonempty (↥W ≃ₗ[k[↥H]] ↥(W.map (conjSemilinearEnd (H := H) ρ g))) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : IsSimpleModule k[↥H] ↥(W.map (conjSemilinearEnd (H := H) ρ g)) :=
    isSimpleModule_map_conjSemilinearEnd ρ g W
  haveI := subRep_isIrreducible (resRep ρ H) W
  haveI := subRep_isIrreducible (resRep ρ H) (W.map (conjSemilinearEnd (H := H) ρ g))
  have h2 : (Nat.card ↥H : k)⁻¹ * ∑ h : ↥H,
      ((Subrepresentation.ofSubmodule' W).toRepresentation).character h
        * ((Subrepresentation.ofSubmodule' W).toRepresentation).character h⁻¹ = 1 := by
    rw [Representation.char_orthonormal, if_pos ⟨Representation.Equiv.refl _⟩]
  have key := Representation.char_orthonormal
    ((Subrepresentation.ofSubmodule' (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation)
    ((Subrepresentation.ofSubmodule' W).toRepresentation)
  rw [hchar, h2] at key
  have hne : Nonempty (((Subrepresentation.ofSubmodule' W).toRepresentation).Equiv
      ((Subrepresentation.ofSubmodule'
        (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation)) := by
    by_contra hc
    rw [if_neg hc] at key
    exact one_ne_zero key
  obtain ⟨φ⟩ := hne
  exact ⟨(subRepAsModuleEquiv (resRep ρ H) W).trans ((equivAsModule φ).trans
    (subRepAsModuleEquiv (resRep ρ H) (W.map (conjSemilinearEnd (H := H) ρ g))).symm)⟩

/-- **The conjugate `M ≅ M^g` for a faithful irreducible constituent** (BG Prop 2.2(a)'s `hconj`,
the char_orthonormal route).  If `W` is a faithful simple constituent of nilpotency class `≤ 2` over
an algebraically closed field with `char k ∤ |H|`, and `g` centralises `Z(H)`, then `W` is
isomorphic to its conjugate `(ρ g)(W)`.  This is exactly the per-`g` input
(`conjSemilinearEnd`-conjugate form) consumed by `restriction_isIrreducible` /
`isIsotypicOfType_of_conjugates`, obtained from Gorenstein 5.5.5 (character vanishing) plus Schur
orthogonality rather than a from-scratch Gorenstein 5.5.4. -/
theorem conjugate_submodule_iso [IsAlgClosed k] [FiniteDimensional k V] [Finite ↥H]
    [Invertible (Nat.card ↥H : k)] [IsSimpleModule k[↥H] ↥W]
    (hf : Function.Injective ((Subrepresentation.ofSubmodule' W).toRepresentation))
    (hcl : commutator ↥H ≤ Subgroup.center ↥H) (g : G)
    (hgc : ∀ z : ↥H, z ∈ Subgroup.center ↥H → conjNormalMulAut H g⁻¹ z = z) :
    Nonempty (↥W ≃ₗ[k[↥H]] ↥(W.map (conjSemilinearEnd (H := H) ρ g))) :=
  submodule_iso_of_character_eq ρ W g (character_subRep_conj_eq ρ W hf hcl g hgc)

end ConjChar

end OddOrder.RepresentationTheory
