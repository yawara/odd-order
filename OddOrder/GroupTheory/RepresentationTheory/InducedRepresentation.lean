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

/-! ## Right translation on cosets, and support submodules

Toward the Brauer character of `Ind_H^G W` at an element `g`: restricted to `⟨g⟩`, the induced
module splits along the orbits of `g` on the right cosets `H \\ G`.  A `g`-stable set of cosets
cuts out a `⟨g⟩`-submodule, namely the functions supported there.  Summing the Brauer character
over the orbits then reduces (8.2) to two cases — a fixed coset, which contributes
`α (x g x⁻¹)`, and an orbit of length `> 1`, which contributes `0`. -/

section Support

/-- Right translation of right cosets: `H x ↦ H x g`.  Well defined because right
multiplication commutes with the left `H`-action defining the cosets. -/
def cosetRightMul (H : Subgroup G) (g : G) :
    Quotient (QuotientGroup.rightRel H) → Quotient (QuotientGroup.rightRel H) :=
  fun c => Quotient.liftOn' c (fun x => Quotient.mk (QuotientGroup.rightRel H) (x * g)) <| by
    rintro a b hab
    refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
    have hmem : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hab
    have hrw : (b * g) * (a * g)⁻¹ = b * a⁻¹ := by group
    rw [hrw]; exact hmem

@[simp] theorem cosetRightMul_mk (H : Subgroup G) (g x : G) :
    cosetRightMul H g (Quotient.mk (QuotientGroup.rightRel H) x)
      = Quotient.mk (QuotientGroup.rightRel H) (x * g) :=
  rfl

variable {H} (ρ : Representation k ↥H W)

/-- The functions in the induced space supported on a given set `S` of right cosets. -/
def indSupport (S : Set (Quotient (QuotientGroup.rightRel H))) :
    Submodule k ↥(indSubmodule H ρ) where
  carrier := { f | ∀ x : G, Quotient.mk (QuotientGroup.rightRel H) x ∉ S → (f : G → W) x = 0 }
  add_mem' {f₁ f₂} hf₁ hf₂ x hx := by
    change (f₁ : G → W) x + (f₂ : G → W) x = 0
    rw [hf₁ x hx, hf₂ x hx, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c f hf x hx := by
    change c • (f : G → W) x = 0
    rw [hf x hx, smul_zero]

@[simp] theorem mem_indSupport_iff (S : Set (Quotient (QuotientGroup.rightRel H)))
    (f : ↥(indSubmodule H ρ)) :
    f ∈ indSupport ρ S ↔
      ∀ x : G, Quotient.mk (QuotientGroup.rightRel H) x ∉ S → (f : G → W) x = 0 :=
  Iff.rfl

/-- **A `g`-stable set of cosets cuts out a `⟨g⟩`-submodule.**  This is the decomposition step
of the Brauer–Nesbitt computation: the induced module restricted to `⟨g⟩` is the direct sum of
the pieces supported on the `⟨g⟩`-orbits of cosets. -/
theorem indSupport_invariant {S : Set (Quotient (QuotientGroup.rightRel H))} {g : G}
    (hS : ∀ c, c ∈ S ↔ cosetRightMul H g c ∈ S) (f : ↥(indSubmodule H ρ))
    (hf : f ∈ indSupport ρ S) :
    indRep H ρ g f ∈ indSupport ρ S := by
  intro x hx
  have hxg : Quotient.mk (QuotientGroup.rightRel H) (x * g) ∉ S := by
    intro hcon
    exact hx ((hS (Quotient.mk (QuotientGroup.rightRel H) x)).mpr (by
      rw [cosetRightMul_mk]; exact hcon))
  exact hf (x * g) hxg

/-- A right coset is fixed by right translation by `g` exactly when `g` conjugates into `H`.
This is the membership condition `x g x⁻¹ ∈ H` cutting out the terms of `induceCoset`. -/
theorem cosetRightMul_mk_eq_iff (H : Subgroup G) (g x : G) :
    cosetRightMul H g (Quotient.mk (QuotientGroup.rightRel H) x)
        = Quotient.mk (QuotientGroup.rightRel H) x
      ↔ x * g * x⁻¹ ∈ H := by
  rw [cosetRightMul_mk]
  constructor
  · intro hq
    have hrel : x * (x * g)⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    have hrw : (x * (x * g)⁻¹)⁻¹ = x * g * x⁻¹ := by group
    rw [← hrw]; exact H.inv_mem hrel
  · intro hmem
    refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
    have hrw : x * (x * g)⁻¹ = (x * g * x⁻¹)⁻¹ := by group
    rw [hrw]; exact H.inv_mem hmem

/-- **The fixed-coset contribution.**  If right translation by `g` fixes the coset `H x` — that
is, `x g x⁻¹ ∈ H` — then on the value at `x` the induced action is exactly `ρ (x g x⁻¹)`.

Summing this over the fixed cosets is precisely the sum defining `induceCoset`, and it is why
the Brauer–Nesbitt formula picks out the terms with `x g x⁻¹ ∈ H`. -/
theorem indRep_apply_of_conj_mem {g x : G} (hx : x * g * x⁻¹ ∈ H)
    (f : ↥(indSubmodule H ρ)) :
    ((indRep H ρ g f : G → W)) x = ρ ⟨x * g * x⁻¹, hx⟩ ((f : G → W) x) := by
  have key := indSubmodule_apply_mul f ⟨x * g * x⁻¹, hx⟩ x
  have hxg : ((⟨x * g * x⁻¹, hx⟩ : ↥H) : G) * x = x * g := by
    change (x * g * x⁻¹) * x = x * g
    group
  rw [hxg] at key
  exact key

end Support

end OddOrder.RepresentationTheory
