/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The induced representation, as `H`-equivariant functions

Toward **Navarro (8.2)** (Brauer–Nesbitt): if `W` is an `FH`-module affording the Brauer
character `α`, then the induced module `W^G` affords `α^G`.  That is a statement about
eigenvalues of the induced action, so we need a model of `W^G` concrete enough to compute
with — concretely enough that `Module.finrank` of an eigenspace is accessible.

## Why not mathlib's `Representation.ind`

Mathlib has `Representation.ind φ ρ`, defined as the coinvariants `(k[H] ⊗[k] A)_G`, together
with `Rep.indCoindIso` identifying it with the coinduced representation for a finite-index
subgroup.  That packaging is aimed at Shapiro's lemma and the adjunction with restriction; the
underlying module is a quotient of a tensor product, which is awkward for the eigenvalue
bookkeeping a Brauer character needs.

We therefore use the *coinduced* description directly, which for finite index is isomorphic to
the induced one and is a concrete submodule of `G → W`:

`Ind(ρ) = { f : G → W | f (h * x) = ρ h (f x) for all h ∈ H, x ∈ G }`,   `(g · f)(x) = f (x * g)`.

Choosing a transversal identifies this `k`-linearly with `(G ⧸ H) → W`, which is where the
eigenvalue computation will happen; but the action above involves **no choice**, which keeps
the `Representation` structure clean.

## Main definitions

* `OddOrder.RepresentationTheory.indSubmodule` — the submodule of `H`-equivariant functions
* `OddOrder.RepresentationTheory.indRep` — the induced representation of `G`
* `OddOrder.RepresentationTheory.coordShift` — the `H`-part of `x` against the chosen
  representative of the right coset `H x`
* `OddOrder.RepresentationTheory.indCoordEquiv` — coordinates on the induced space

## Main results

* `indRep_apply` — the action is right translation
* `mem_indSubmodule_iff` — membership unfolds to the equivariance identity
* `coordShift_mul_out` — `x = coordShift x * out ⟦x⟧`
* `indCoordEquiv` — `indSubmodule H ρ ≃ₗ[k] (H \ G) → W`, so the induced space has
  `[G : H]` coordinates each a copy of `W`; this is what makes `Module.finrank` (and hence
  the Brauer character) of the induced module accessible
-/

namespace OddOrder.RepresentationTheory

variable {k G W : Type*} [CommRing k] [Group G] [AddCommGroup W] [Module k W]

/-- The `k`-submodule of `H`-equivariant functions `G → W`, the underlying space of the
induced representation. -/
def indSubmodule (H : Subgroup G) (ρ : Representation k ↥H W) : Submodule k (G → W) where
  carrier := { f | ∀ (h : ↥H) (x : G), f ((h : G) * x) = ρ h (f x) }
  add_mem' {f₁ f₂} hf₁ hf₂ h x := by
    simp only [Pi.add_apply, hf₁ h x, hf₂ h x, map_add]
  zero_mem' h x := by simp only [Pi.zero_apply, map_zero]
  smul_mem' c f hf h x := by
    simp only [Pi.smul_apply, hf h x, map_smul]

variable {H : Subgroup G} {ρ : Representation k ↥H W}

@[simp] theorem mem_indSubmodule_iff (f : G → W) :
    f ∈ indSubmodule H ρ ↔ ∀ (h : ↥H) (x : G), f ((h : G) * x) = ρ h (f x) :=
  Iff.rfl

theorem indSubmodule_apply_mul (f : ↥(indSubmodule H ρ)) (h : ↥H) (x : G) :
    (f : G → W) ((h : G) * x) = ρ h ((f : G → W) x) :=
  f.2 h x

variable (H ρ)

/-- Right translation by `g`, as a `k`-linear endomorphism of the induced space.

Equivariance is preserved because left multiplication by `h ∈ H` and right multiplication by
`g` commute: `(g · f)(h x) = f (h x g) = ρ h (f (x g)) = ρ h ((g · f)(x))`. -/
def indRepAux (g : G) : ↥(indSubmodule H ρ) →ₗ[k] ↥(indSubmodule H ρ) where
  toFun f := ⟨fun x => (f : G → W) (x * g), by
    intro h x
    have := indSubmodule_apply_mul f h (x * g)
    simpa [mul_assoc] using this⟩
  map_add' f₁ f₂ := rfl
  map_smul' c f := rfl

@[simp] theorem indRepAux_apply (g : G) (f : ↥(indSubmodule H ρ)) (x : G) :
    ((indRepAux H ρ g f : G → W)) x = (f : G → W) (x * g) :=
  rfl

/-- **The induced representation** `Ind_H^G ρ`, on the space of `H`-equivariant functions
`G → W`, with `G` acting by right translation. -/
def indRep : Representation k G ↥(indSubmodule H ρ) where
  toFun := indRepAux H ρ
  map_one' := by
    ext f x
    simp
  map_mul' g₁ g₂ := by
    ext f x
    simp [mul_assoc]

@[simp] theorem indRep_apply (g : G) (f : ↥(indSubmodule H ρ)) (x : G) :
    ((indRep H ρ g f : G → W)) x = (f : G → W) (x * g) :=
  rfl

/-! ## Coordinates: an equivariant function is its values on a right transversal

An `f ∈ indSubmodule H ρ` satisfies `f (h * x) = ρ h (f x)`, so it is determined by its values
on the right cosets `H x`.  Reading off those values against `Quotient.out` gives a `k`-linear
isomorphism with `(H \ G) → W`, which is what makes `Module.finrank` — and hence the Brauer
character — computable. -/

section Coordinates

variable {H}

/-- For `x : G`, the element of `H` carrying the chosen representative of the right coset `H x`
to `x`.  By construction `x = coordShift x * Quotient.out ⟦x⟧`. -/
noncomputable def coordShift (H : Subgroup G) (x : G) : ↥H :=
  ⟨x * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) x))⁻¹, by
    have hout : Quotient.mk (QuotientGroup.rightRel H)
        (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) x))
        = Quotient.mk (QuotientGroup.rightRel H) x := Quotient.out_eq _
    exact QuotientGroup.rightRel_apply.mp (Quotient.exact hout)⟩

theorem coordShift_mul_out (x : G) :
    ((coordShift H x : G)) * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) x)) = x := by
  change (x * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) x))⁻¹) * _ = x
  group

/-- Reading an equivariant function off the chosen right-coset representatives. -/
noncomputable def indCoord (ρ : Representation k ↥H W) :
    ↥(indSubmodule H ρ) →ₗ[k] (Quotient (QuotientGroup.rightRel H) → W) where
  toFun f := fun c => (f : G → W) (Quotient.out c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem indCoord_apply (ρ : Representation k ↥H W) (f : ↥(indSubmodule H ρ))
    (c : Quotient (QuotientGroup.rightRel H)) :
    indCoord ρ f c = (f : G → W) (Quotient.out c) :=
  rfl

/-- Rebuilding an equivariant function from its values on the chosen representatives. -/
noncomputable def indOfCoord (ρ : Representation k ↥H W) :
    (Quotient (QuotientGroup.rightRel H) → W) →ₗ[k] ↥(indSubmodule H ρ) where
  toFun v := ⟨fun x => ρ (coordShift H x) (v (Quotient.mk (QuotientGroup.rightRel H) x)), by
    intro h x
    have hmk : Quotient.mk (QuotientGroup.rightRel H) ((h : G) * x)
        = Quotient.mk (QuotientGroup.rightRel H) x := by
      refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
      have hrw : x * ((h : G) * x)⁻¹ = (h : G)⁻¹ := by group
      rw [hrw]; exact H.inv_mem h.2
    have hshift : coordShift H ((h : G) * x) = h * coordShift H x := by
      apply Subtype.ext
      change (h : G) * x * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) ((h : G) * x)))⁻¹
        = (h : G) * (x * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) x))⁻¹)
      rw [hmk]; group
    change (ρ (coordShift H ((h : G) * x)))
        (v (Quotient.mk (QuotientGroup.rightRel H) ((h : G) * x)))
      = (ρ h) ((ρ (coordShift H x)) (v (Quotient.mk (QuotientGroup.rightRel H) x)))
    rw [hmk, hshift, map_mul]
    rfl⟩
  map_add' u v := by ext x; simp [map_add]
  map_smul' c v := by ext x; simp [map_smul]

@[simp] theorem indOfCoord_apply (ρ : Representation k ↥H W)
    (v : Quotient (QuotientGroup.rightRel H) → W) (x : G) :
    ((indOfCoord ρ v : G → W)) x
      = ρ (coordShift H x) (v (Quotient.mk (QuotientGroup.rightRel H) x)) :=
  rfl

/-- **Coordinates on the induced space.**  An `H`-equivariant function `G → W` is exactly a
family of elements of `W` indexed by the right cosets `H \ G`. -/
noncomputable def indCoordEquiv (ρ : Representation k ↥H W) :
    ↥(indSubmodule H ρ) ≃ₗ[k] (Quotient (QuotientGroup.rightRel H) → W) :=
  { indCoord ρ with
    invFun := indOfCoord ρ
    left_inv := by
      intro f
      apply Subtype.ext
      funext x
      change ρ (coordShift H x) ((f : G → W)
        (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) x))) = (f : G → W) x
      rw [← indSubmodule_apply_mul f (coordShift H x), coordShift_mul_out]
    right_inv := by
      intro v
      funext c
      change ρ (coordShift H (Quotient.out c)) (v (Quotient.mk (QuotientGroup.rightRel H)
        (Quotient.out c))) = v c
      have hout : Quotient.mk (QuotientGroup.rightRel H) (Quotient.out c) = c := Quotient.out_eq _
      have hshift : coordShift H (Quotient.out c) = 1 := by
        apply Subtype.ext
        change Quotient.out c * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H)
          (Quotient.out c)))⁻¹ = (1 : G)
        rw [hout]; group
      rw [hout, hshift, map_one]
      rfl }

/-! ### The degree of an induced representation -/

/-- The right cosets `H \\ G` are in bijection with the left cosets `G ⧸ H`, so there are
`H.index` of them. -/
theorem card_quotient_rightRel (H : Subgroup G) :
    Nat.card (Quotient (QuotientGroup.rightRel H)) = H.index :=
  Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)

/-- **The degree of an induced representation** is `[G : H]` times the degree of the original:
the induced space has one coordinate copy of `W` for each right coset (`indCoordEquiv`).

This is the module-level source of the character identity `θ^G(1) = [G : H] · θ(1)`, and in
particular of `induceCoset`'s value at `1`. -/
theorem finrank_indSubmodule [StrongRankCondition k] [Finite G]
    [Module.Free k W] [Module.Finite k W] (ρ : Representation k ↥H W) :
    Module.finrank k ↥(indSubmodule H ρ) = H.index * Module.finrank k W := by
  classical
  have : Fintype (Quotient (QuotientGroup.rightRel H)) := Fintype.ofFinite _
  rw [(indCoordEquiv ρ).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, card_quotient_rightRel]

end Coordinates

end OddOrder.RepresentationTheory
