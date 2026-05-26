/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing

/-!
# Second orthogonality (column orthogonality) of irreducible characters

For a finite group `G`, the irreducible characters and the conjugacy classes form a square
character table whose rows and columns are mutually orthogonal. mathlib's
`FDRep.char_orthonormal` covers the **first (row)** orthogonality

  `⅟|G| · ∑_{g ∈ G} χ(g) · ψ(g⁻¹) = ⟨χ, ψ⟩ = δ_{χ, ψ}`     (for `χ, ψ ∈ Irr G`).

The **second (column)** orthogonality, stated here, is the dual statement summing over
`Irr(G)`:

  `∑_{χ ∈ Irr G} χ(g) · χ̄(h) = |C_G(g)|`  if `g ~ h`,
  `= 0`                                       if `g ≁ h`.

This is [Is] Thm 2.18 / Thm 6.10 (column version).

## Status

* The **statements** are given here (modulo a `Fintype` indexing the irreducible characters).
* The **proof core** is `column_orthogonality_cases`.  It is deferred and routed to
  `issues/0027-peterfalvi-column-orthogonality-core.md`: the classical route uses
  invertibility of the character table (matrix algebra). The derived public lemmas
  below are kept `sorry`-free.

## Main statements

* `OddOrder.RepresentationTheory.characterTableRowPairing` — the normalized row pairing
  of two irreducible-character rows.
* `OddOrder.RepresentationTheory.CharacterTableRowOrthogonality` — the first
  orthogonality statement in a form usable by the later matrix proof.
* `OddOrder.RepresentationTheory.characterTableColumnPairing` — the column pairing
  `∑_χ χ(g) · star (χ(h))`.
* `OddOrder.RepresentationTheory.column_orthogonality_diag` — diagonal case
  `∑_{χ ∈ Irr G} χ(g) · star (χ(g)) = |C_G(g)|`.
* `OddOrder.RepresentationTheory.column_orthogonality_conj` — for conjugate `g, h`,
  the sum equals `|C_G(g)|`.
* `OddOrder.RepresentationTheory.column_orthogonality_not_conj` — for non-conjugate
  `g, h`: the sum vanishes.

## References

* Isaacs, *Character Theory of Finite Groups*, Thm 2.18 / Thm 6.10.
* Peterfalvi §3 (1.2) (vanishing criterion for normal closures).
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G]

/-- The normalized character-table row pairing of two irreducible complex
characters.  This is the row side of the Schur orthogonality matrix argument. -/
noncomputable def characterTableRowPairing
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (χ ψ : IrreducibleCharacter G) : ℂ :=
  ClassFunction.inner (χ : ClassFunction G ℂ) (ψ : ClassFunction G ℂ)

@[simp] theorem characterTableRowPairing_eq_inner
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (χ ψ : IrreducibleCharacter G) :
    characterTableRowPairing χ ψ =
      ClassFunction.inner (χ : ClassFunction G ℂ) (ψ : ClassFunction G ℂ) :=
  rfl

theorem characterTableRowPairing_eq_inv_card_sum
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (χ ψ : IrreducibleCharacter G) :
    characterTableRowPairing χ ψ =
      ⅟(Nat.card G : ℂ) *
        ∑ g : G, ((χ : ClassFunction G ℂ) g) *
          star ((ψ : ClassFunction G ℂ) g) :=
  rfl

/-- The first, row-side character orthogonality statement, separated from the
column theorem so the later character-table invertibility proof can take it as
the input row relation. -/
def CharacterTableRowOrthogonality
    [Fintype G] [Invertible (Nat.card G : ℂ)] : Prop :=
  (∀ χ : IrreducibleCharacter G, characterTableRowPairing χ χ = 1) ∧
    ∀ ⦃χ ψ : IrreducibleCharacter G⦄,
      χ ≠ ψ → characterTableRowPairing χ ψ = 0

namespace CharacterTableRowOrthogonality

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

theorem diagonal (hrow : CharacterTableRowOrthogonality (G := G))
    (χ : IrreducibleCharacter G) :
    characterTableRowPairing χ χ = 1 :=
  hrow.1 χ

theorem offDiagonal (hrow : CharacterTableRowOrthogonality (G := G))
    {χ ψ : IrreducibleCharacter G} (hχψ : χ ≠ ψ) :
    characterTableRowPairing χ ψ = 0 :=
  hrow.2 hχψ

end CharacterTableRowOrthogonality

/-- The character-table column pairing
`∑_χ χ(g) · star (χ(h))`, summing over irreducible complex characters. -/
noncomputable def characterTableColumnPairing
    [Fintype (IrreducibleCharacter G)] (g h : G) : ℂ :=
  ∑ χ : IrreducibleCharacter G,
    ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h)

@[simp] theorem characterTableColumnPairing_eq_sum
    [Fintype (IrreducibleCharacter G)] (g h : G) :
    characterTableColumnPairing g h =
      ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) :=
  rfl

theorem characterTableColumnPairing_of_isConj_left
    [Fintype (IrreducibleCharacter G)]
    {g₁ g₂ h : G} (hg : IsConj g₁ g₂) :
    characterTableColumnPairing g₁ h =
      characterTableColumnPairing g₂ h := by
  simp only [characterTableColumnPairing]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [((χ : ClassFunction G ℂ).of_isConj hg)]

theorem characterTableColumnPairing_of_isConj_right
    [Fintype (IrreducibleCharacter G)]
    {g h₁ h₂ : G} (hh : IsConj h₁ h₂) :
    characterTableColumnPairing g h₁ =
      characterTableColumnPairing g h₂ := by
  simp only [characterTableColumnPairing]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [((χ : ClassFunction G ℂ).of_isConj hh)]

theorem characterTableColumnPairing_conj_left
    [Fintype (IrreducibleCharacter G)] (x g h : G) :
    characterTableColumnPairing (x * g * x⁻¹) h =
      characterTableColumnPairing g h :=
  characterTableColumnPairing_of_isConj_left
    (isConj_iff.mpr ⟨x⁻¹, by simp [mul_assoc]⟩)

theorem characterTableColumnPairing_conj_right
    [Fintype (IrreducibleCharacter G)] (x g h : G) :
    characterTableColumnPairing g (x * h * x⁻¹) =
      characterTableColumnPairing g h :=
  characterTableColumnPairing_of_isConj_right
    (isConj_iff.mpr ⟨x⁻¹, by simp [mul_assoc]⟩)

/-- Primitive cases form of the second (column) orthogonality theorem.

The two projections are the conjugate and non-conjugate columns of the character-table
orthogonality relation.  Public named corollaries below are derived from this single
deferred proof core. -/
theorem column_orthogonality_cases
    [Fintype (IrreducibleCharacter G)]
    (g h : G) :
    (IsConj g h →
      characterTableColumnPairing g h =
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ)) ∧
    (¬ IsConj g h →
      characterTableColumnPairing g h = 0) := by
  sorry

/-- Named-column form of the diagonal second orthogonality relation. -/
theorem characterTableColumnPairing_diag
    [Fintype (IrreducibleCharacter G)]
    (g : G) :
    characterTableColumnPairing g g =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  exact (column_orthogonality_cases g g).1 (IsConj.refl g)

/-- Named-column form of the conjugate second orthogonality relation. -/
theorem characterTableColumnPairing_conj
    [Fintype (IrreducibleCharacter G)]
    {g h : G} (hgh : IsConj g h) :
    characterTableColumnPairing g h =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  exact (column_orthogonality_cases g h).1 hgh

/-- Named-column form of the non-conjugate second orthogonality relation. -/
theorem characterTableColumnPairing_not_conj
    [Fintype (IrreducibleCharacter G)]
    {g h : G} (hgh : ¬ IsConj g h) :
    characterTableColumnPairing g h = 0 := by
  exact (column_orthogonality_cases g h).2 hgh

/-- Diagonal second (column) orthogonality:
`∑_{χ ∈ Irr G} χ(g) · star (χ(g)) = |C_G(g)|`.

This is the `g = h` specialization of `column_orthogonality_cases`. -/
theorem column_orthogonality_diag
    [Fintype (IrreducibleCharacter G)]
    (g : G) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) g) =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  simpa using characterTableColumnPairing_diag (G := G) g

/-- **Second (column) orthogonality**, conjugate case ([Is] Thm 2.18 / 6.10).

For `g, h ∈ G` with `g ~ h`, `∑_{χ ∈ Irr G} χ(g) · χ̄(h) = |C_G(g)|` in `ℂ`.

The sum runs over `IrreducibleCharacter G`, the named subtype of `ClassFunction G ℂ`
carved out by `IsIrreducibleCharacter`. Such a `Fintype` is well-defined for finite
`G`; supplying it as an explicit instance keeps this statement uncoupled from the
eventual existence proof for the indexing type.

This is the conjugate projection of `column_orthogonality_cases`. -/
theorem column_orthogonality_conj
    [Fintype (IrreducibleCharacter G)]
    {g h : G} (hgh : IsConj g h) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  simpa using characterTableColumnPairing_conj (G := G) hgh

/-- **Second (column) orthogonality**, non-conjugate case ([Is] Thm 2.18 / 6.10).

For `g, h ∈ G` with `g ≁ h`, `∑_{χ ∈ Irr G} χ(g) · χ̄(h) = 0` in `ℂ`. -/
theorem column_orthogonality_not_conj
    [Fintype (IrreducibleCharacter G)]
    {g h : G} (hgh : ¬ IsConj g h) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) = 0 := by
  simpa using characterTableColumnPairing_not_conj (G := G) hgh

end OddOrder.RepresentationTheory
