/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

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

## Main results

* `indRep_apply` — the action is right translation
* `mem_indSubmodule_iff` — membership unfolds to the equivariance identity
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

end OddOrder.RepresentationTheory
