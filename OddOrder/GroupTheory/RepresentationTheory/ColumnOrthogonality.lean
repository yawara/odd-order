/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CharacterCompleteness
import OddOrder.GroupTheory.RepresentationTheory.CharacterRowOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

/-!
# Second (column) orthogonality of irreducible characters, unconditional form

This module supplies the **hypothesis-free** public form of the second (column)
orthogonality relation ([Isaacs] Thm 2.18 / Thm 6.10) for a finite group `G`.

The matrix proof core (`SecondOrthogonality.lean`) states the column relations
`column_orthogonality_diag` / `column_orthogonality_conj` / `column_orthogonality_not_conj`
relative to two inputs that, at that point in the development, are still hypotheses:

* a square indexing package `idx : CharacterTableIndexing G` (rows `IrreducibleCharacter G`,
  columns `ConjClasses G`, with `|Irr G| = |ConjClasses G|`), and
* `CharacterTableWeightedRowOrthogonality idx` (first orthogonality in class-weighted Gram form).

Both inputs are now discharged unconditionally for `[Finite G]`:

* the indexing comes from `card_irreducibleCharacter_eq` (`CharacterCompleteness.lean`), packaged
  as the instance `instCharacterTableIndexingOfFinite`;
* the weighted row orthogonality comes from `characterTableRowOrthogonality_holds`
  (`CharacterRowOrthogonality.lean`), converted by
  `CharacterTableWeightedRowOrthogonality.ofRowOrthogonality`.

Feeding these in yields the three public theorems below with `[Finite G]` as their only
typeclass assumption.

## Main results

* `OddOrder.RepresentationTheory.column_orthogonality_diagonal` —
  `∑_{χ ∈ Irr G} χ(g) · star (χ(g)) = |C_G(g)|`.
* `OddOrder.RepresentationTheory.column_orthogonality_conjugate` —
  for `g ~ h`, `∑_{χ ∈ Irr G} χ(g) · star (χ(h)) = |C_G(g)|`.
* `OddOrder.RepresentationTheory.column_orthogonality_not_conjugate` —
  for `g ≁ h`, `∑_{χ ∈ Irr G} χ(g) · star (χ(h)) = 0`.

The diagonal case at `g = 1` is the **Burnside degree-sum identity**
(Peterfalvi (1.5.d)), recorded here as:

* `OddOrder.RepresentationTheory.sumIrreducibleDegreeSq` —
  `∑_{χ ∈ Irr G} χ(1)² = |G|`;
* `OddOrder.RepresentationTheory.sumNontrivialIrreducibleDegreeSq` —
  `∑_{χ ∈ Irr G, χ ≠ 1} χ(1)² = |G| - 1`.

Reference issues: `issues/0027-peterfalvi-column-orthogonality-core.md`,
`issues/0044-peterfalvi-s09-card-g0-lower-bound.md`.
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Finite G]

/-- The canonical `Fintype` on `IrreducibleCharacter G` for a finite group, used as the
summation index of the public column-orthogonality theorems below. -/
noncomputable instance : Fintype (IrreducibleCharacter G) :=
  letI := finite_irreducibleCharacter (G := G)
  Fintype.ofFinite _

/-- The class-weighted first orthogonality input for the matrix proof core, discharged
unconditionally for a finite group from `characterTableRowOrthogonality_holds`. -/
private theorem weightedRowOrthogonality_ofFinite :
    CharacterTableWeightedRowOrthogonality (instCharacterTableIndexingOfFinite (G := G)) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact CharacterTableWeightedRowOrthogonality.ofRowOrthogonality
    (instCharacterTableIndexingOfFinite (G := G)) (characterTableRowOrthogonality_holds (G := G))

/-- Bridge between the ambient `Fintype (IrreducibleCharacter G)` summation index and the one
carried by `instCharacterTableIndexingOfFinite`: `Fintype` is a subsingleton, so the two index
finsets coincide and any sum over `IrreducibleCharacter G` is unchanged. -/
private theorem sum_irreducibleCharacter_idx_eq {M : Type*} [AddCommMonoid M]
    (f : IrreducibleCharacter G → M) :
    (letI := (instCharacterTableIndexingOfFinite (G := G)).irrFintype
      ∑ χ : IrreducibleCharacter G, f χ) = ∑ χ : IrreducibleCharacter G, f χ :=
  congrArg (∑ χ ∈ ·, f χ)
    (congrArg (@Finset.univ (IrreducibleCharacter G))
      (Subsingleton.elim (instCharacterTableIndexingOfFinite (G := G)).irrFintype _))

/-- **Second (column) orthogonality**, diagonal case ([Isaacs] Thm 2.18 / Thm 6.10).

For a finite group `G` and `g : G`, the squared column norm equals the centralizer order:
`∑_{χ ∈ Irr G} χ(g) · star (χ(g)) = |C_G(g)|` in `ℂ`. -/
theorem column_orthogonality_diagonal (g : G) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) g) =
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  rw [← sum_irreducibleCharacter_idx_eq]
  exact column_orthogonality_diag (instCharacterTableIndexingOfFinite (G := G))
    weightedRowOrthogonality_ofFinite g

/-- **Second (column) orthogonality**, conjugate case ([Isaacs] Thm 2.18 / Thm 6.10).

For a finite group `G` and conjugate elements `g ~ h`,
`∑_{χ ∈ Irr G} χ(g) · star (χ(h)) = |C_G(g)|` in `ℂ`. -/
theorem column_orthogonality_conjugate {g h : G} (hgh : IsConj g h) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) =
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  rw [← sum_irreducibleCharacter_idx_eq]
  exact column_orthogonality_conj (instCharacterTableIndexingOfFinite (G := G))
    weightedRowOrthogonality_ofFinite hgh

/-- **Second (column) orthogonality**, non-conjugate case ([Isaacs] Thm 2.18 / Thm 6.10).

For a finite group `G` and non-conjugate elements `g ≁ h`,
`∑_{χ ∈ Irr G} χ(g) · star (χ(h)) = 0` in `ℂ`. -/
theorem column_orthogonality_not_conjugate {g h : G} (hgh : ¬ IsConj g h) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) = 0 := by
  rw [← sum_irreducibleCharacter_idx_eq]
  exact column_orthogonality_not_conj (instCharacterTableIndexingOfFinite (G := G))
    weightedRowOrthogonality_ofFinite hgh

omit [Finite G] in
/-- The summand `χ(g) · star (χ(g))` of the diagonal column relation equals `χ(g)²`
whenever `χ(g)` is a real natural number cast, in particular at `g = 1` where
`χ(1)` is the (positive integer) degree of `χ`. -/
private theorem char_one_mul_star_eq_sq (χ : IrreducibleCharacter G) :
    ((χ : ClassFunction G ℂ) 1) * star ((χ : ClassFunction G ℂ) 1) =
      ((χ : ClassFunction G ℂ) 1) ^ 2 := by
  obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  rw [hd, star_natCast, sq]

/-- **Burnside degree-sum identity** (Peterfalvi (1.5.d); the diagonal column relation
[Isaacs] Thm 2.18 at `g = 1`).

The sum of the squares of the degrees of all irreducible characters of a finite group `G`
equals the group order: `∑_{χ ∈ Irr G} χ(1)² = |G|` in `ℂ`. -/
theorem sumIrreducibleDegreeSq :
    ∑ χ : IrreducibleCharacter G, ((χ : ClassFunction G ℂ) 1) ^ 2 = (Nat.card G : ℂ) := by
  have hcentralizer : (Subgroup.centralizer ({(1 : G)} : Set G)) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr
      (Set.singleton_subset_iff.mpr (Subgroup.one_mem _))
  have h := column_orthogonality_diagonal (1 : G)
  rw [Finset.sum_congr rfl (fun χ _ => char_one_mul_star_eq_sq χ)] at h
  rw [h, hcentralizer, Subgroup.card_top]

open scoped Classical in
/-- **Burnside degree-sum identity, nontrivial part** (Peterfalvi (1.5.d)).

Summing the squared degrees over the *nontrivial* irreducible characters (i.e. all `χ`
except the trivial character, whose degree is `1`) gives `|G| - 1`:
`∑_{χ ∈ Irr G, χ ≠ 1} χ(1)² = |G| - 1` in `ℂ`. -/
theorem sumNontrivialIrreducibleDegreeSq :
    ∑ χ ∈ Finset.univ.erase (trivialIrreducibleCharacter G),
        ((χ : ClassFunction G ℂ) 1) ^ 2 = (Nat.card G : ℂ) - 1 := by
  have htriv : ((trivialIrreducibleCharacter G : ClassFunction G ℂ) 1) ^ 2 = 1 := by
    simp
  have hsplit :=
    Finset.add_sum_erase (Finset.univ : Finset (IrreducibleCharacter G))
      (fun χ => ((χ : ClassFunction G ℂ) 1) ^ 2)
      (a := trivialIrreducibleCharacter G) (Finset.mem_univ _)
  rw [htriv] at hsplit
  rw [eq_sub_iff_add_eq, add_comm, hsplit, sumIrreducibleDegreeSq]

end OddOrder.RepresentationTheory
