/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RepresentationTheory.Character

/-!
# Virtual characters over an arbitrary field

Gorenstein's `ch(G)` — the ring of *generalized* (= virtual) characters — for a group `G` and a
field `K`.  This is the ambient object of **Brauer's characterization of characters**
(Gorenstein 1968, §4.7, book pp. 160–170), which Navarro (2.15) cites and which is therefore the
last genuine prerequisite of the modular development of `issues/9506`.

The definition here is deliberately **splitting-free**: `θ` is a virtual character when it is a
`ℤ`-combination of characters of finite-dimensional `K`-representations.  Brauer's theorem
quantifies over *all* elementary subgroups `E ≤ G`, and equipping each of them with a Wedderburn
splitting of `K[E]` would be both painful and unnecessary — the only place a splitting is needed
is for `G` itself, when one converts "all inner products with `Irr(G)` are integers" into
membership.  Everything else (restriction, products, the Frobenius pairing) works over any field.

To keep the definition universe-monomorphic, the generating set is taken to consist of the
characters of representations on the *standard* space `Fin n → K`; `isRepCharacter_of_finite`
shows that this loses nothing.

## Main definitions

* `OddOrder.RepresentationTheory.transportRepresentation` — a representation transported along a
  linear equivalence
* `OddOrder.RepresentationTheory.IsRepCharacter` — `θ` is the character of a finite-dimensional
  representation
* `OddOrder.RepresentationTheory.virtualCharacters` — Gorenstein's `ch(G)`, as an `AddSubgroup`

## Main results

* `OddOrder.RepresentationTheory.isRepCharacter_of_finite` — any finite-dimensional
  representation, on any carrier, has `IsRepCharacter` character
* `OddOrder.RepresentationTheory.IsRepCharacter.mul` — closure under tensor product
* `OddOrder.RepresentationTheory.mul_mem_virtualCharacters` — `ch(G)` is closed under products
* `OddOrder.RepresentationTheory.comp_mem_virtualCharacters` — pulling back along a group
  homomorphism; in particular `Res_H` maps `ch(G)` into `ch(H)`

## References

* D. Gorenstein, *Finite Groups*, §4.7 (`references/gorenstein/pages/gorenstein-p16*.png`).
* G. Navarro, *Characters and Blocks of Finite Groups*, (2.15) (p. 28).
-/

namespace OddOrder.RepresentationTheory

open Module

/-! ### Transporting a representation along a linear equivalence -/

section Transport

variable {K H V W : Type*} [Field K] [Monoid H]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- **A representation transported along a linear equivalence** `e : V ≃ₗ[K] W`, acting by
`e ∘ ρ g ∘ e⁻¹`.  Used to move an arbitrary finite-dimensional representation onto the standard
space `Fin n → K`. -/
noncomputable def transportRepresentation (ρ : Representation K H V) (e : V ≃ₗ[K] W) :
    Representation K H W :=
  ((e.conjRingEquiv : Module.End K V ≃+* Module.End K W) : Module.End K V →+* Module.End K W
    ).toMonoidHom.comp ρ

@[simp]
theorem transportRepresentation_apply (ρ : Representation K H V) (e : V ≃ₗ[K] W) (h : H) :
    transportRepresentation ρ e h = e.conj (ρ h) := rfl

/-- Transporting does not change the character. -/
theorem character_transportRepresentation [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K H V) (e : V ≃ₗ[K] W) :
    (transportRepresentation ρ e).character = ρ.character := by
  funext h
  rw [Representation.character, transportRepresentation_apply, LinearMap.trace_conj']
  rfl

end Transport

/-! ### Characters of finite-dimensional representations -/

variable {K H : Type*} [Field K] [Monoid H]

/-- **`θ` is the character of a finite-dimensional `K`-representation of `H`.**  The carrier is
fixed to the standard space `Fin n → K` so that the predicate lives in a single universe;
`isRepCharacter_of_finite` shows this is no restriction. -/
def IsRepCharacter (K : Type*) [Field K] {H : Type*} [Monoid H] (θ : H → K) : Prop :=
  ∃ (n : ℕ) (ρ : Representation K H (Fin n → K)), θ = ρ.character

/-- The character of **any** finite-dimensional representation is an `IsRepCharacter`: pick a
basis and transport. -/
theorem isRepCharacter_of_finite {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K H V) : IsRepCharacter K ρ.character := by
  classical
  refine ⟨finrank K V, transportRepresentation ρ (finBasis K V).equivFun, ?_⟩
  rw [character_transportRepresentation]

/-- The trivial (one-dimensional) representation has character `1`. -/
theorem isRepCharacter_one : IsRepCharacter K (1 : H → K) := by
  refine ⟨1, 1, ?_⟩
  funext h
  change (1 : K) = LinearMap.trace K (Fin 1 → K) 1
  rw [LinearMap.trace_one]
  simp

/-- **Products**: the tensor product of two representations has the product character. -/
theorem IsRepCharacter.mul {θ ψ : H → K} (hθ : IsRepCharacter K θ) (hψ : IsRepCharacter K ψ) :
    IsRepCharacter K (θ * ψ) := by
  obtain ⟨n, ρ, rfl⟩ := hθ
  obtain ⟨m, σ, rfl⟩ := hψ
  exact (Representation.char_tensor ρ σ) ▸ isRepCharacter_of_finite (Representation.tprod ρ σ)

/-- **Pullback along a monoid homomorphism** — restriction to a subgroup is the case of an
inclusion. -/
theorem IsRepCharacter.comp {H' : Type*} [Monoid H'] {θ : H → K} (hθ : IsRepCharacter K θ)
    (f : H' →* H) : IsRepCharacter K (θ ∘ f) := by
  obtain ⟨n, ρ, rfl⟩ := hθ
  exact ⟨n, ρ.comp f, rfl⟩

/-! ### The group of virtual characters -/

variable (K H) in
/-- **Gorenstein's `ch(H)`**: the additive group of virtual (generalized) characters of `H` over
`K`, i.e. the `ℤ`-span of the characters of the finite-dimensional `K`-representations. -/
def virtualCharacters : AddSubgroup (H → K) :=
  AddSubgroup.closure { θ : H → K | IsRepCharacter K θ }

theorem IsRepCharacter.mem_virtualCharacters {θ : H → K} (hθ : IsRepCharacter K θ) :
    θ ∈ virtualCharacters K H :=
  AddSubgroup.subset_closure hθ

theorem one_mem_virtualCharacters : (1 : H → K) ∈ virtualCharacters K H :=
  isRepCharacter_one.mem_virtualCharacters

/-- `ch(H)` is closed under multiplication: it is in fact a subring of `H → K`. -/
theorem mul_mem_virtualCharacters {θ ψ : H → K} (hθ : θ ∈ virtualCharacters K H)
    (hψ : ψ ∈ virtualCharacters K H) : θ * ψ ∈ virtualCharacters K H := by
  induction hθ using AddSubgroup.closure_induction with
  | mem θ hθ =>
      induction hψ using AddSubgroup.closure_induction with
      | mem ψ hψ => exact (hθ.mul hψ).mem_virtualCharacters
      | zero => simpa only [mul_zero] using (virtualCharacters K H).zero_mem
      | add a b _ _ ha hb => simpa only [mul_add] using (virtualCharacters K H).add_mem ha hb
      | neg a _ ha => simpa only [mul_neg] using (virtualCharacters K H).neg_mem ha
  | zero => simpa only [zero_mul] using (virtualCharacters K H).zero_mem
  | add a b _ _ ha hb => simpa only [add_mul] using (virtualCharacters K H).add_mem ha hb
  | neg a _ ha => simpa only [neg_mul] using (virtualCharacters K H).neg_mem ha

/-- **`ch` is contravariant in the group**: pulling back along `f : H' →* H` maps `ch(H)` into
`ch(H')`.  With `f` the inclusion of a subgroup this is `Res_{H'} (ch(H)) ⊆ ch(H')`, the trivial
half of Brauer's characterization. -/
theorem comp_mem_virtualCharacters {H' : Type*} [Monoid H'] (f : H' →* H) {θ : H → K}
    (hθ : θ ∈ virtualCharacters K H) : θ ∘ f ∈ virtualCharacters K H' := by
  induction hθ using AddSubgroup.closure_induction with
  | mem θ hθ => exact (hθ.comp f).mem_virtualCharacters
  | zero =>
      have : ((0 : H → K) ∘ f) = (0 : H' → K) := rfl
      rw [this]
      exact (virtualCharacters K H').zero_mem
  | add a b _ _ ha hb => exact (virtualCharacters K H').add_mem ha hb
  | neg a _ ha => exact (virtualCharacters K H').neg_mem ha

end OddOrder.RepresentationTheory
