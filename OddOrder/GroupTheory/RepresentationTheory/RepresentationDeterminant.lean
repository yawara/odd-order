/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RepresentationTheory.Basic
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter

/-!
# The determinant character of a representation

For a `ℂ`-representation `ρ : Representation ℂ G V`, the map `g ↦ det (ρ g)` is a homomorphism
`G →* ℂˣ` — the **determinant character** `det ρ`.  It is well-defined into `ℂˣ` because each `ρ g`
is invertible (`Representation.asGroupHom`), and it is multiplicative because it is a composite of
monoid homomorphisms (`Units.map`, `LinearMap.detMonoidHom`).

The associated *linear* class function `linearClassFunction (det ρ)` is the classical determinantal
character; its order (as an element of `Hom(G, ℂˣ)`) is the load-bearing invariant of the **coprime
extension theorem** (Isaacs, *Character Theory*, 6.28/8.16): a `G`-invariant `θ ∈ Irr(H)` with
`gcd([G:H], |H|) = 1` extends to `χ ∈ Irr(G)`, the extension pinned down by its determinantal order.
This feeds the multiplicity-one conclusion of the constructive Clifford decomposition
(Peterfalvi (1.7), the general type-I `typeI_induced_char_constituents`).
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The **determinant character** `det ρ : G →* ℂˣ` of a representation, `g ↦ det (ρ g)`.  A
homomorphism because it factors as `Units.map LinearMap.det ∘ ρ.asGroupHom` (`LinearMap.det` is a
monoid homomorphism `Module.End ℂ V →* ℂ`). -/
noncomputable def representationDeterminant (ρ : Representation ℂ G V) : G →* ℂˣ :=
  (Units.map (LinearMap.det : (V →ₗ[ℂ] V) →* ℂ)).comp ρ.asGroupHom

@[simp] theorem representationDeterminant_apply (ρ : Representation ℂ G V) (g : G) :
    (representationDeterminant ρ g : ℂ) = LinearMap.det (ρ g) := by
  rw [representationDeterminant, MonoidHom.comp_apply, Units.coe_map, ρ.asGroupHom_apply]

/-- The determinant character commutes with pullback along a homomorphism:
`det (ρ ∘ f) = (det ρ) ∘ f`.  With `f = H.subtype` this is `det (Res_H χ) = Res_H (det χ)` — the
determinantal character of an extension `χ ∈ Irr(I)` of `θ ∈ Irr(H)` restricts to `det θ`, the
compatibility that pins the coprime extension. -/
theorem representationDeterminant_comp {H : Type*} [Group H] (ρ : Representation ℂ G V)
    (f : H →* G) :
    representationDeterminant (ρ.comp f) = (representationDeterminant ρ).comp f := by
  ext h
  simp only [representationDeterminant_apply, MonoidHom.comp_apply]

/-- **The determinant character has values that are `|G|`-th roots of unity.**  For a finite group,
`(det ρ g)^{|G|} = det ρ (g^{|G|}) = det ρ 1 = 1` (`pow_card_eq_one'`).  Hence the order of `det ρ`
in `Hom(G, ℂˣ)` divides `|G|` — the arithmetic that, against `gcd([K:H], |H|) = 1`, drives the
uniqueness of the coprime extension (Isaacs *CT* 8.16). -/
theorem representationDeterminant_pow_card [Finite G] (ρ : Representation ℂ G V) (g : G) :
    representationDeterminant ρ g ^ Nat.card G = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

end OddOrder.RepresentationTheory
