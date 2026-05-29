/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import OddOrder.GroupTheory.RepresentationTheory.CharacterConjugate
import OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality

/-!
# Row orthogonality of irreducible characters (first orthogonality), discharged

This module discharges `CharacterTableRowOrthogonality (G := G)` for a finite group `G`,
turning the row-orthogonality *hypothesis* used throughout the second-orthogonality /
character-table matrix development (`SecondOrthogonality.lean`) into an unconditional
*theorem*.

The mathematical content is mathlib's `Representation.char_orthonormal` (orthogonality of
characters of irreducible complex representations of a finite group), bridged to Peterfalvi's
class-function inner product `(α, β)_G = |G|⁻¹ ∑ α(g) · conj(β(g))` via the conjugate-character
identity `χ(g⁻¹) = star (χ(g))` (`character_inv`, proved in `CharacterConjugate.lean`).

## Main results

* `OddOrder.RepresentationTheory.irreducibleCharacter_inner` — for `χ ψ : IrreducibleCharacter G`,
  `(χ, ψ)_G = if χ = ψ then 1 else 0`.
* `OddOrder.RepresentationTheory.characterTableRowOrthogonality_holds` —
  `CharacterTableRowOrthogonality (G := G)` holds unconditionally (for `[Fintype G]` with
  `|G|` invertible in `ℂ`).

The off-diagonal case uses that isomorphic representations have equal characters
(`Representation.char_iso`): distinct irreducible characters cannot come from isomorphic
representations, so `char_orthonormal`'s `if Nonempty (Equiv ..)` branch is the `0` branch.
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open Classical in
/-- **First orthogonality relation.** Irreducible characters are orthonormal under Peterfalvi's
class-function inner product: `(χ, ψ)_G = if χ = ψ then 1 else 0`.

Bridges mathlib's `Representation.char_orthonormal` (stated with the `g⁻¹` summand) to the
conjugate-summand inner product via `character_inv`. -/
theorem irreducibleCharacter_inner [Fintype G] [Invertible (Nat.card G : ℂ)]
    (χ ψ : IrreducibleCharacter G) :
    ClassFunction.inner (χ : ClassFunction G ℂ) (ψ : ClassFunction G ℂ) =
      if χ = ψ then 1 else 0 := by
  by_cases hχψ : χ = ψ
  · -- Diagonal: extract one irreducible representation and apply `char_orthonormal ρ ρ`.
    subst hχψ
    obtain ⟨V, _, _, _, ρ, hρ, hcoe⟩ := χ.isIrreducible
    haveI : Representation.IsIrreducible ρ := hρ
    rw [if_pos rfl, ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum,
      invOf_eq_inv]
    have hsum : ∀ g : G,
        (χ : ClassFunction G ℂ) g * star ((χ : ClassFunction G ℂ) g) =
          ρ.character g * ρ.character g⁻¹ := by
      intro g
      rw [congrFun hcoe g, ← character_inv ρ g]
    rw [Finset.sum_congr rfl (fun g _ => hsum g), ρ.char_orthonormal,
      if_pos ⟨Representation.Equiv.refl ρ⟩]
  · -- Off-diagonal: distinct characters ⇒ non-isomorphic representations ⇒ the `0` branch.
    obtain ⟨Vχ, _, _, _, ρχ, hρχ, hcoeχ⟩ := χ.isIrreducible
    obtain ⟨Vψ, _, _, _, ρψ, hρψ, hcoeψ⟩ := ψ.isIrreducible
    haveI : Representation.IsIrreducible ρχ := hρχ
    haveI : Representation.IsIrreducible ρψ := hρψ
    rw [if_neg hχψ, ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum,
      invOf_eq_inv]
    have hsum : ∀ g : G,
        (χ : ClassFunction G ℂ) g * star ((ψ : ClassFunction G ℂ) g) =
          ρχ.character g * ρψ.character g⁻¹ := by
      intro g
      rw [congrFun hcoeχ g, congrFun hcoeψ g, ← character_inv ρψ g]
    rw [Finset.sum_congr rfl (fun g _ => hsum g), ρχ.char_orthonormal]
    rw [if_neg]
    rintro ⟨e⟩
    -- An equivalence `ρψ ≃ ρχ` forces equal characters, hence `ψ = χ`.
    apply hχψ
    apply IrreducibleCharacter.ext
    apply ClassFunction.ext
    intro g
    rw [congrFun hcoeχ g, congrFun hcoeψ g, ← congrFun (Representation.char_iso e) g]

/-- **`CharacterTableRowOrthogonality` holds unconditionally.** Discharges the row-orthogonality
input assumed throughout `SecondOrthogonality.lean`, via `irreducibleCharacter_inner`. -/
theorem characterTableRowOrthogonality_holds [Fintype G] [Invertible (Nat.card G : ℂ)] :
    CharacterTableRowOrthogonality (G := G) := by
  refine ⟨fun χ => ?_, fun χ ψ hχψ => ?_⟩
  · rw [characterTableRowPairing_eq_inner, irreducibleCharacter_inner, if_pos rfl]
  · rw [characterTableRowPairing_eq_inner, irreducibleCharacter_inner, if_neg hχψ]

end OddOrder.RepresentationTheory
