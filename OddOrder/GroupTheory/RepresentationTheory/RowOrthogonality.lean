/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import OddOrder.GroupTheory.RepresentationTheory.CharacterConjugate
import OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality

/-!
# Row orthogonality of irreducible characters, as a theorem

`SecondOrthogonality.lean` states the first (row) orthogonality relation
`CharacterTableRowOrthogonality` as a `Prop` and then *consumes* it as a
hypothesis (`hrow`) in the column-orthogonality matrix argument.  This file
discharges that hypothesis: `characterTableRowOrthogonality` proves it outright.

The bridge is mathlib's `Representation.char_orthonormal`, which gives

  `|G|⁻¹ · ∑_g ρ.char g · σ.char g⁻¹ = if Nonempty (σ.Equiv ρ) then 1 else 0`,

phrased with the *inverse argument* `σ.char g⁻¹`.  Peterfalvi's class-function
inner product `(α, β)_G = |G|⁻¹ ∑_g α(g) · conj(β(g))` — which is how
`characterTableRowPairing` is defined — instead uses complex conjugation, so
`character_inv` (`χ(g⁻¹) = conj χ(g)`, the layer-1a lemma in
`CharacterConjugate.lean`) turns one into the other.

* The diagonal value `1` comes from the identity equivalence
  `Representation.Equiv.refl`.
* The off-diagonal value `0` comes from the fact that an `Equiv` between the two
  irreducible representations would force their characters — hence the two
  irreducible-character indices — to coincide (`Representation.char_iso`).

Reference issue: `issues/0025-peterfalvi-isometry-difference-core.md` (layer 1b).
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **First (row) orthogonality** of irreducible complex characters, proved as a
theorem rather than assumed.  This discharges the `CharacterTableRowOrthogonality`
hypothesis used by the column-orthogonality matrix argument and, downstream, by
the Peterfalvi §3 (1.4) isometry difference-pair core. -/
theorem characterTableRowOrthogonality :
    CharacterTableRowOrthogonality (G := G) := by
  classical
  refine ⟨fun χ => ?_, fun χ ψ hχψ => ?_⟩
  · -- Diagonal entry `(χ, χ)` equals `1`.
    obtain ⟨V, _, _, _, ρ, hρ, hχ⟩ := χ.isIrreducible
    haveI : Representation.IsIrreducible ρ := hρ
    have hsum : ∑ g : G, (χ : ClassFunction G ℂ) g * star ((χ : ClassFunction G ℂ) g)
        = ∑ g : G, ρ.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => by rw [congrFun hχ g, ← character_inv ρ g]
    rw [characterTableRowPairing_eq_inv_card_sum, hsum, invOf_eq_inv,
      Representation.char_orthonormal ρ ρ, if_pos ⟨Representation.Equiv.refl ρ⟩]
  · -- Off-diagonal entry `(χ, ψ)` with `χ ≠ ψ` equals `0`.
    obtain ⟨Vχ, _, _, _, ρ, hρ, hχ⟩ := χ.isIrreducible
    obtain ⟨Vψ, _, _, _, σ, hσ, hψ⟩ := ψ.isIrreducible
    haveI : Representation.IsIrreducible ρ := hρ
    haveI : Representation.IsIrreducible σ := hσ
    have hsum : ∑ g : G, (χ : ClassFunction G ℂ) g * star ((ψ : ClassFunction G ℂ) g)
        = ∑ g : G, ρ.character g * σ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => by
        rw [congrFun hχ g, congrFun hψ g, ← character_inv σ g]
    -- An equivalence `σ ≃ ρ` would make the two irreducible characters equal.
    have hnc : ¬ Nonempty (σ.Equiv ρ) := by
      rintro ⟨φ⟩
      apply hχψ
      apply IrreducibleCharacter.ext
      apply ClassFunction.ext
      intro g
      rw [congrFun hχ g, congrFun hψ g]
      exact (congrFun (Representation.char_iso φ) g).symm
    rw [characterTableRowPairing_eq_inv_card_sum, hsum, invOf_eq_inv,
      Representation.char_orthonormal ρ σ, if_neg hnc]

end OddOrder.RepresentationTheory
