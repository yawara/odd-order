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
* The **proof** is deferred: the classical route uses invertibility of the character table
  (matrix algebra). The lemma is needed by `BrauerPermutation` and by Peterfalvi §3 (1.2).

## Main statements

* `OddOrder.RepresentationTheory.column_orthogonality_diag` — diagonal case
  `∑_{χ ∈ Irr G} χ(g) · star (χ(g)) = |C_G(g)|`.
* `OddOrder.RepresentationTheory.column_orthogonality_conj` — for conjugate `g, h`,
  derived from the diagonal case by class-function invariance.
* `OddOrder.RepresentationTheory.column_orthogonality_not_conj` — for non-conjugate
  `g, h`: the sum vanishes.

## References

* Isaacs, *Character Theory of Finite Groups*, Thm 2.18 / Thm 6.10.
* Peterfalvi §3 (1.2) (vanishing criterion for normal closures).
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G]

/-- Diagonal second (column) orthogonality:
`∑_{χ ∈ Irr G} χ(g) · star (χ(g)) = |C_G(g)|`.

This is the primitive deferred statement for the conjugate column case; the
off-diagonal non-conjugate case is still a separate character-table theorem. -/
theorem column_orthogonality_diag
    [Fintype (IrreducibleCharacter G)]
    (g : G) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) g) =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  sorry

/-- **Second (column) orthogonality**, conjugate case ([Is] Thm 2.18 / 6.10).

For `g, h ∈ G` with `g ~ h`, `∑_{χ ∈ Irr G} χ(g) · χ̄(h) = |C_G(g)|` in `ℂ`.

The sum runs over `IrreducibleCharacter G`, the named subtype of `ClassFunction G ℂ`
carved out by `IsIrreducibleCharacter`. Such a `Fintype` is well-defined for finite
`G`; supplying it as an explicit instance keeps this statement uncoupled from the
eventual existence proof for the indexing type.

This is a direct consequence of the diagonal case because every class function is
constant on conjugacy classes. -/
theorem column_orthogonality_conj
    [Fintype (IrreducibleCharacter G)]
    {g h : G} (hgh : IsConj g h) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  calc
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h)
        = ∑ χ : IrreducibleCharacter G,
            ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) g) := by
          refine Finset.sum_congr rfl ?_
          intro χ _
          have hχ : (χ : ClassFunction G ℂ) g = (χ : ClassFunction G ℂ) h :=
            ClassFunction.of_isConj (χ : ClassFunction G ℂ) hgh
          rw [← hχ]
    _ = (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) :=
        column_orthogonality_diag g

/-- **Second (column) orthogonality**, non-conjugate case ([Is] Thm 2.18 / 6.10).

For `g, h ∈ G` with `g ≁ h`, `∑_{χ ∈ Irr G} χ(g) · χ̄(h) = 0` in `ℂ`. -/
theorem column_orthogonality_not_conj
    [Fintype (IrreducibleCharacter G)]
    {g h : G} (hgh : ¬ IsConj g h) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) = 0 := by
  sorry

end OddOrder.RepresentationTheory
