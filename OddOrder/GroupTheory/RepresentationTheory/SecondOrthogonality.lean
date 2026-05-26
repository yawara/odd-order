/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
* The **column-side proof core** `column_orthogonality_cases` and its named corollaries are
  conditional on weighted row orthogonality `CharacterTableWeightedRowOrthogonality idx`.
  The conditional proof itself is closed via the matrix algebra in this file. Bridging
  this hypothesis to mathlib's `Representation.char_orthonormal` (which provides row
  orthogonality directly) is the remaining gap; see
  `issues/0027-peterfalvi-column-orthogonality-core.md`.

## Main statements

* `OddOrder.RepresentationTheory.characterTableRowPairing` — the normalized row pairing
  of two irreducible-character rows.
* `OddOrder.RepresentationTheory.CharacterTableRowOrthogonality` — the first
  orthogonality statement in a form usable by the later matrix proof.
* `OddOrder.RepresentationTheory.CharacterTableIndexing` — finite square indexing data
  for rows `IrreducibleCharacter G` and columns `ConjClasses G`.
* `OddOrder.RepresentationTheory.characterTableEntry` — a character-table entry indexed
  by an irreducible character and a conjugacy class.
* `OddOrder.RepresentationTheory.conjugacyClassSize_mk_mul_card_centralizer` — the
  class-size/centralizer cardinality bridge for later column diagonal entries.
* `OddOrder.RepresentationTheory.characterTableMatrix` — the rectangular character table.
* `OddOrder.RepresentationTheory.characterTableSquareMatrix` — the same table reindexed
  to a square matrix via `CharacterTableIndexing.rowColumnEquiv`.
* `OddOrder.RepresentationTheory.characterTableDeterminant` — determinant of the square
  character table for the matrix-invertibility proof.
* `OddOrder.RepresentationTheory.characterTableWeightedRowPairing` — the class-weighted
  row pairing used by the character-table matrix argument.
* `OddOrder.RepresentationTheory.characterTableWeightedRowGramMatrix` — the weighted
  row Gram matrix `A * W * Aᴴ` for the square reindexed character table.
* `OddOrder.RepresentationTheory.characterTableDeterminant_ne_zero_of_weightedRowOrthogonality`
  — determinant nonvanishing from weighted row orthogonality.
* `OddOrder.RepresentationTheory.characterTableSquareMatrixInvertibleOfDet` — the
  `[Invertible]` instance bridge extracted from determinant nonvanishing.
* `OddOrder.RepresentationTheory.characterTableColumnPairing` — the column pairing
  `∑_χ χ(g) · star (χ(h))`.
* `OddOrder.RepresentationTheory.characterTableSquareColumnPairing` — the same column
  pairing after reindexing columns by irreducible characters.
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

/-- The conjugacy-class side of the character table has a finite indexing for a finite
group.  Keeping this as a named non-instance avoids changing instance search in later
matrix proofs. -/
@[reducible]
noncomputable def conjClassesFintypeOfFinite (G : Type*) [Group G] [Finite G] :
    Fintype (ConjClasses G) :=
  Fintype.ofFinite (ConjClasses G)

/-- Finite square indexing data for the character table: rows are irreducible complex
characters and columns are conjugacy classes, with the two finite cardinalities aligned.

The eventual proof of second orthogonality supplies this data from the standard theorem
that the number of irreducible characters equals the number of conjugacy classes. -/
structure CharacterTableIndexing (G : Type*) [Group G] where
  irrFintype : Fintype (IrreducibleCharacter G)
  classFintype : Fintype (ConjClasses G)
  card_eq :
    @Fintype.card (IrreducibleCharacter G) irrFintype =
      @Fintype.card (ConjClasses G) classFintype

namespace CharacterTableIndexing

/-- Number of character-table rows under a chosen indexing package. -/
def rowCount (idx : CharacterTableIndexing G) : ℕ :=
  @Fintype.card (IrreducibleCharacter G) idx.irrFintype

/-- Number of character-table columns under a chosen indexing package. -/
def columnCount (idx : CharacterTableIndexing G) : ℕ :=
  @Fintype.card (ConjClasses G) idx.classFintype

theorem rowCount_eq_columnCount (idx : CharacterTableIndexing G) :
    idx.rowCount = idx.columnCount :=
  idx.card_eq

/-- A noncomputable equivalence between row and column index types, extracted from the
cardinality equality in a character-table indexing package. -/
noncomputable def rowColumnEquiv (idx : CharacterTableIndexing G) :
    IrreducibleCharacter G ≃ ConjClasses G := by
  letI := idx.irrFintype
  letI := idx.classFintype
  exact Fintype.equivOfCardEq idx.card_eq

/-- Build character-table indexing data from a finite group, a finite irreducible-character
indexing, and the cardinal equality theorem. -/
noncomputable def ofFinite [Finite G] [Fintype (IrreducibleCharacter G)]
    (hcard :
      @Fintype.card (IrreducibleCharacter G) inferInstance =
        @Fintype.card (ConjClasses G) (conjClassesFintypeOfFinite G)) :
    CharacterTableIndexing G where
  irrFintype := inferInstance
  classFintype := conjClassesFintypeOfFinite G
  card_eq := hcard

end CharacterTableIndexing

/-- A fixed representative of a conjugacy class, used only to define class-indexed
character-table entries. -/
noncomputable def conjugacyClassRepresentative (C : ConjClasses G) : G :=
  Classical.choose (ConjClasses.exists_rep C)

theorem conjugacyClassRepresentative_mk_eq (C : ConjClasses G) :
    ConjClasses.mk (conjugacyClassRepresentative C) = C :=
  Classical.choose_spec (ConjClasses.exists_rep C)

/-- The size of a conjugacy class, as a natural number. -/
noncomputable def conjugacyClassSize (C : ConjClasses G) : ℕ :=
  Nat.card C.carrier

/-- A conjugacy class has size `|G| / |C_G(g)|`, equivalently
`|class(g)| * |C_G(g)| = |G|`.  This form avoids committing later matrix arguments to
natural-number division. -/
theorem conjugacyClassSize_mk_mul_card_centralizer [Finite G] (g : G) :
    conjugacyClassSize (ConjClasses.mk g) *
      Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses.mk g).carrier := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit (ConjAct G) g) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer (ConjAct G) g) := Fintype.ofFinite _
  rw [conjugacyClassSize, Nat.card_eq_fintype_card, ConjClasses.card_carrier]
  have hstabNat :
      Nat.card (Subgroup.centralizer ({g} : Set G)) =
        Nat.card (MulAction.stabilizer (ConjAct G) g) := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    rfl
  have hstab :
      Nat.card (Subgroup.centralizer ({g} : Set G)) =
        Fintype.card (MulAction.stabilizer (ConjAct G) g) := by
    rw [hstabNat, Nat.card_eq_fintype_card]
  rw [hstab, Nat.card_eq_fintype_card]
  exact Nat.div_mul_cancel
    ⟨Fintype.card (MulAction.orbit (ConjAct G) g), by
      rw [mul_comm]
      exact (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g).symm⟩

theorem conjugacyClassSize_mk_mul_card_centralizer_cast [Finite G] (g : G) :
    (conjugacyClassSize (ConjClasses.mk g) : ℂ) *
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) =
        (Nat.card G : ℂ) := by
  exact_mod_cast conjugacyClassSize_mk_mul_card_centralizer (G := G) g

theorem card_centralizer_eq_card_div_conjugacyClassSize_cast [Finite G] (g : G) :
    (Nat.card G : ℂ) / (conjugacyClassSize (ConjClasses.mk g) : ℂ) =
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  have hmul := conjugacyClassSize_mk_mul_card_centralizer_cast (G := G) g
  have hclass_pos : 0 < conjugacyClassSize (ConjClasses.mk g) := by
    rw [conjugacyClassSize]
    exact Nat.card_pos_iff.mpr ⟨⟨g, ConjClasses.mem_carrier_mk⟩, inferInstance⟩
  have hclass_ne : (conjugacyClassSize (ConjClasses.mk g) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hclass_pos.ne'
  rw [div_eq_iff hclass_ne]
  simpa [mul_comm] using hmul.symm

/-- The character-table entry indexed by an irreducible character and a conjugacy class. -/
noncomputable def characterTableEntry
    (χ : IrreducibleCharacter G) (C : ConjClasses G) : ℂ :=
  (χ : ClassFunction G ℂ) (conjugacyClassRepresentative C)

@[simp] theorem characterTableEntry_mk (χ : IrreducibleCharacter G) (g : G) :
    characterTableEntry χ (ConjClasses.mk g) =
      (χ : ClassFunction G ℂ) g := by
  simpa [characterTableEntry] using
    ((χ : ClassFunction G ℂ).of_isConj
      (ConjClasses.mk_eq_mk_iff_isConj.mp
        (conjugacyClassRepresentative_mk_eq (C := ConjClasses.mk g))))

/-- The character table as a rectangular matrix whose columns are conjugacy classes. -/
noncomputable def characterTableMatrix (G : Type*) [Group G] :
    Matrix (IrreducibleCharacter G) (ConjClasses G) ℂ :=
  Matrix.of fun χ C => characterTableEntry χ C

@[simp] theorem characterTableMatrix_apply
    (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    characterTableMatrix G χ C = characterTableEntry χ C :=
  rfl

/-- The character table reindexed as a square matrix on irreducible characters.

The column equivalence is arbitrary but fixed by `idx`; determinant/invertibility arguments
can use this square form and transport conclusions back to `ConjClasses G`. -/
noncomputable def characterTableSquareMatrix (idx : CharacterTableIndexing G) :
    Matrix (IrreducibleCharacter G) (IrreducibleCharacter G) ℂ :=
  (Matrix.reindex (Equiv.refl (IrreducibleCharacter G)) idx.rowColumnEquiv.symm)
    (characterTableMatrix G)

@[simp] theorem characterTableSquareMatrix_apply
    (idx : CharacterTableIndexing G) (χ ψ : IrreducibleCharacter G) :
    characterTableSquareMatrix idx χ ψ =
      characterTableEntry χ (idx.rowColumnEquiv ψ) := by
  simp [characterTableSquareMatrix]

/-- Determinant of a square reindexing of the character table.  The value depends on the
chosen row-column equivalence only up to sign, so nonvanishing is the intended invariant. -/
noncomputable def characterTableDeterminant (idx : CharacterTableIndexing G) : ℂ :=
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  Matrix.det (characterTableSquareMatrix idx)

/-- Matrix-invertibility input needed for the classical proof of column orthogonality. -/
noncomputable def CharacterTableMatrixInvertible (idx : CharacterTableIndexing G) : Prop :=
  characterTableDeterminant idx ≠ 0

theorem characterTableMatrixInvertible_iff_det_ne_zero
    (idx : CharacterTableIndexing G) :
    CharacterTableMatrixInvertible idx ↔ characterTableDeterminant idx ≠ 0 :=
  Iff.rfl

/-- Turn determinant nonvanishing of the square character table into the matrix
`[Invertible]` instance used by the later inverse-matrix argument. -/
@[implicit_reducible]
noncomputable def characterTableSquareMatrixInvertibleOfDet
    (idx : CharacterTableIndexing G) (hinv : CharacterTableMatrixInvertible idx) :
    letI := idx.irrFintype
    letI := Classical.decEq (IrreducibleCharacter G)
    Invertible (characterTableSquareMatrix idx) := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  have hdet : Matrix.det (characterTableSquareMatrix idx) ≠ 0 := by
    simpa [CharacterTableMatrixInvertible, characterTableDeterminant] using hinv
  letI : Invertible (Matrix.det (characterTableSquareMatrix idx)) :=
    invertibleOfNonzero hdet
  exact Matrix.invertibleOfDetInvertible (characterTableSquareMatrix idx)

/-- The class-weighted row pairing of two character-table rows.  This is the matrix form
of summing over group elements after collecting terms by conjugacy class. -/
noncomputable def characterTableWeightedRowPairing
    (idx : CharacterTableIndexing G) (χ ψ : IrreducibleCharacter G) : ℂ :=
  letI := idx.classFintype
  ∑ C : ConjClasses G,
    (conjugacyClassSize C : ℂ) * characterTableEntry χ C * star (characterTableEntry ψ C)

@[simp] theorem characterTableWeightedRowPairing_eq_sum
    (idx : CharacterTableIndexing G) (χ ψ : IrreducibleCharacter G) :
    characterTableWeightedRowPairing idx χ ψ =
      letI := idx.classFintype
      ∑ C : ConjClasses G,
        (conjugacyClassSize C : ℂ) * characterTableEntry χ C *
          star (characterTableEntry ψ C) :=
  rfl

/-- Row orthogonality in the class-weighted matrix form.  This is the exact input used
to prove nonvanishing of the character-table determinant. -/
def CharacterTableWeightedRowOrthogonality (idx : CharacterTableIndexing G) : Prop :=
  (∀ χ : IrreducibleCharacter G,
    characterTableWeightedRowPairing idx χ χ = (Nat.card G : ℂ)) ∧
    ∀ ⦃χ ψ : IrreducibleCharacter G⦄,
      χ ≠ ψ → characterTableWeightedRowPairing idx χ ψ = 0

namespace CharacterTableWeightedRowOrthogonality

theorem diagonal {idx : CharacterTableIndexing G}
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (χ : IrreducibleCharacter G) :
    characterTableWeightedRowPairing idx χ χ = (Nat.card G : ℂ) :=
  hrow.1 χ

theorem offDiagonal {idx : CharacterTableIndexing G}
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    {χ ψ : IrreducibleCharacter G} (hχψ : χ ≠ ψ) :
    characterTableWeightedRowPairing idx χ ψ = 0 :=
  hrow.2 hχψ

end CharacterTableWeightedRowOrthogonality

/-- The diagonal matrix of conjugacy-class sizes, pulled back along the square
row-column indexing of the character table. -/
noncomputable def characterTableClassSizeSquareMatrix
    (idx : CharacterTableIndexing G) :
    Matrix (IrreducibleCharacter G) (IrreducibleCharacter G) ℂ :=
  letI := Classical.decEq (IrreducibleCharacter G)
  Matrix.diagonal fun ψ => (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ)

@[simp] theorem characterTableClassSizeSquareMatrix_apply_same
    (idx : CharacterTableIndexing G) (ψ : IrreducibleCharacter G) :
    characterTableClassSizeSquareMatrix idx ψ ψ =
      (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ) := by
  letI := Classical.decEq (IrreducibleCharacter G)
  simp [characterTableClassSizeSquareMatrix]

theorem characterTableClassSizeSquareMatrix_apply_ne
    (idx : CharacterTableIndexing G) {ψ η : IrreducibleCharacter G}
    (hψη : ψ ≠ η) :
    characterTableClassSizeSquareMatrix idx ψ η = 0 := by
  letI := Classical.decEq (IrreducibleCharacter G)
  simp [characterTableClassSizeSquareMatrix, Matrix.diagonal_apply_ne _ hψη]

/-- The class-weighted row pairing, written over the square matrix's column index. -/
noncomputable def characterTableSquareWeightedRowPairing
    (idx : CharacterTableIndexing G) (χ ψ : IrreducibleCharacter G) : ℂ :=
  letI := idx.irrFintype
  ∑ η : IrreducibleCharacter G,
    characterTableSquareMatrix idx χ η *
      ((conjugacyClassSize (idx.rowColumnEquiv η) : ℂ) *
        star (characterTableSquareMatrix idx ψ η))

@[simp] theorem characterTableSquareWeightedRowPairing_eq_weightedRowPairing
    (idx : CharacterTableIndexing G) (χ ψ : IrreducibleCharacter G) :
    characterTableSquareWeightedRowPairing idx χ ψ =
      characterTableWeightedRowPairing idx χ ψ := by
  letI := idx.irrFintype
  letI := idx.classFintype
  rw [characterTableSquareWeightedRowPairing, characterTableWeightedRowPairing]
  simpa [characterTableSquareMatrix_apply, mul_assoc, mul_left_comm, mul_comm] using
    (Equiv.sum_comp idx.rowColumnEquiv
      (fun C : ConjClasses G =>
        characterTableEntry χ C *
          ((conjugacyClassSize C : ℂ) * star (characterTableEntry ψ C))))

/-- The weighted row Gram matrix `A * W * Aᴴ` of the square reindexed character table. -/
noncomputable def characterTableWeightedRowGramMatrix
    (idx : CharacterTableIndexing G) :
    Matrix (IrreducibleCharacter G) (IrreducibleCharacter G) ℂ :=
  letI := idx.irrFintype
  characterTableSquareMatrix idx *
    (characterTableClassSizeSquareMatrix idx *
      Matrix.conjTranspose (characterTableSquareMatrix idx))

theorem characterTableClassSizeSquareMatrix_mul_conjTranspose_apply
    [Fintype (IrreducibleCharacter G)]
    (idx : CharacterTableIndexing G) (η ψ : IrreducibleCharacter G) :
    (characterTableClassSizeSquareMatrix idx *
      Matrix.conjTranspose (characterTableSquareMatrix idx)) η ψ =
      (conjugacyClassSize (idx.rowColumnEquiv η) : ℂ) *
        star (characterTableSquareMatrix idx ψ η) := by
  letI := Classical.decEq (IrreducibleCharacter G)
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single η]
  · simp [characterTableClassSizeSquareMatrix, Matrix.conjTranspose_apply]
  · intro η' _ hη'
    simp [characterTableClassSizeSquareMatrix,
      Matrix.diagonal_apply_ne _ (Ne.symm hη')]
  · intro hη
    simp at hη

@[simp] theorem characterTableWeightedRowGramMatrix_apply
    (idx : CharacterTableIndexing G) (χ ψ : IrreducibleCharacter G) :
    characterTableWeightedRowGramMatrix idx χ ψ =
      characterTableSquareWeightedRowPairing idx χ ψ := by
  letI := idx.irrFintype
  rw [characterTableWeightedRowGramMatrix, characterTableSquareWeightedRowPairing]
  rw [Matrix.mul_apply]
  simp [characterTableClassSizeSquareMatrix_mul_conjTranspose_apply]

/-- Weighted row orthogonality says the weighted Gram matrix is the scalar diagonal
matrix with diagonal entries `|G|`. -/
theorem characterTableWeightedRowGramMatrix_eq_diagonal
    (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx) :
    characterTableWeightedRowGramMatrix idx =
      letI := Classical.decEq (IrreducibleCharacter G)
      Matrix.diagonal fun _ : IrreducibleCharacter G => (Nat.card G : ℂ) := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  ext χ ψ
  by_cases hχψ : χ = ψ
  · subst ψ
    simpa [characterTableWeightedRowPairing] using
      CharacterTableWeightedRowOrthogonality.diagonal hrow χ
  · simpa [characterTableWeightedRowPairing, Matrix.diagonal_apply_ne _ hχψ] using
      CharacterTableWeightedRowOrthogonality.offDiagonal hrow hχψ

/-- The weighted row Gram matrix has nonzero determinant once weighted row
orthogonality is known. -/
theorem characterTableWeightedRowGramMatrix_det_ne_zero
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx) :
    letI := idx.irrFintype
    letI := Classical.decEq (IrreducibleCharacter G)
    Matrix.det (characterTableWeightedRowGramMatrix idx) ≠ 0 := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  rw [characterTableWeightedRowGramMatrix_eq_diagonal idx hrow, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun _ _ =>
    Nat.cast_ne_zero.mpr
      (Nat.card_pos_iff.mpr ⟨⟨(1 : G)⟩, inferInstance⟩).ne'

/-- Weighted row orthogonality gives the determinant nonvanishing needed by the
character-table matrix proof of second orthogonality. -/
theorem characterTableDeterminant_ne_zero_of_weightedRowOrthogonality
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx) :
    CharacterTableMatrixInvertible idx := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  have hgram :
      Matrix.det (characterTableWeightedRowGramMatrix idx) ≠ 0 :=
    characterTableWeightedRowGramMatrix_det_ne_zero (G := G) idx hrow
  intro hdet
  have hdetA : Matrix.det (characterTableSquareMatrix idx) = 0 := by
    simpa [characterTableDeterminant] using hdet
  have hzero : Matrix.det (characterTableWeightedRowGramMatrix idx) = 0 := by
    rw [characterTableWeightedRowGramMatrix, Matrix.det_mul, Matrix.det_mul, hdetA]
    simp
  exact hgram hzero

/-- The square character table is `[Invertible]` once weighted row orthogonality is
available. -/
@[implicit_reducible]
noncomputable def characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx) :
    letI := idx.irrFintype
    letI := Classical.decEq (IrreducibleCharacter G)
    Invertible (characterTableSquareMatrix idx) :=
  characterTableSquareMatrixInvertibleOfDet idx
    (characterTableDeterminant_ne_zero_of_weightedRowOrthogonality (G := G) idx hrow)

/-- Cancel the left character-table factor in the weighted row Gram identity.  This is
the matrix-algebra bridge from row orthogonality toward column orthogonality. -/
theorem characterTableClassSizeSquareMatrix_mul_conjTranspose_eq_inv_mul_cardDiagonal
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx) :
    letI := idx.irrFintype
    letI := Classical.decEq (IrreducibleCharacter G)
    letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
    characterTableClassSizeSquareMatrix idx *
        Matrix.conjTranspose (characterTableSquareMatrix idx) =
      (characterTableSquareMatrix idx)⁻¹ *
        Matrix.diagonal (fun _ : IrreducibleCharacter G => (Nat.card G : ℂ)) := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
  have hgram := characterTableWeightedRowGramMatrix_eq_diagonal idx hrow
  have hleft :=
    congrArg (fun M =>
      (characterTableSquareMatrix idx)⁻¹ * M) hgram
  simpa [characterTableWeightedRowGramMatrix, Matrix.mul_assoc] using hleft

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

/-- The column pairing indexed by conjugacy classes instead of chosen representatives. -/
noncomputable def characterTableClassColumnPairing
    [Fintype (IrreducibleCharacter G)] (C D : ConjClasses G) : ℂ :=
  ∑ χ : IrreducibleCharacter G,
    characterTableEntry χ C * star (characterTableEntry χ D)

@[simp] theorem characterTableClassColumnPairing_mk
    [Fintype (IrreducibleCharacter G)] (g h : G) :
    characterTableClassColumnPairing (ConjClasses.mk g) (ConjClasses.mk h) =
      characterTableColumnPairing g h := by
  simp [characterTableClassColumnPairing, characterTableColumnPairing]

theorem characterTableClassColumnPairing_eq_columnPairing_representatives
    [Fintype (IrreducibleCharacter G)] (C D : ConjClasses G) :
    characterTableClassColumnPairing C D =
      characterTableColumnPairing
        (conjugacyClassRepresentative C) (conjugacyClassRepresentative D) := by
  rfl

/-- The class-column pairing using the irreducible-character indexing bundled in
`CharacterTableIndexing`. -/
noncomputable def characterTableClassColumnPairingOfIndexing
    (idx : CharacterTableIndexing G) (C D : ConjClasses G) : ℂ :=
  letI := idx.irrFintype
  characterTableClassColumnPairing C D

@[simp] theorem characterTableClassColumnPairingOfIndexing_eq_sum
    (idx : CharacterTableIndexing G) (C D : ConjClasses G) :
    characterTableClassColumnPairingOfIndexing idx C D =
      letI := idx.irrFintype
      ∑ χ : IrreducibleCharacter G,
        characterTableEntry χ C * star (characterTableEntry χ D) :=
  rfl

@[simp] theorem characterTableClassColumnPairingOfIndexing_mk
    (idx : CharacterTableIndexing G) (g h : G) :
    characterTableClassColumnPairingOfIndexing idx (ConjClasses.mk g) (ConjClasses.mk h) =
      @characterTableColumnPairing G _ idx.irrFintype g h := by
  simp [characterTableClassColumnPairingOfIndexing]

theorem characterTableClassColumnPairingOfIndexing_eq_columnPairing_representatives
    (idx : CharacterTableIndexing G) (C D : ConjClasses G) :
    characterTableClassColumnPairingOfIndexing idx C D =
      @characterTableColumnPairing G _ idx.irrFintype
        (conjugacyClassRepresentative C) (conjugacyClassRepresentative D) :=
  rfl

/-- The column pairing of the square reindexed character table. -/
noncomputable def characterTableSquareColumnPairing
    (idx : CharacterTableIndexing G) (ψ η : IrreducibleCharacter G) : ℂ :=
  letI := idx.irrFintype
  ∑ χ : IrreducibleCharacter G,
    characterTableSquareMatrix idx χ ψ * star (characterTableSquareMatrix idx χ η)

@[simp] theorem characterTableSquareColumnPairing_eq_classColumnPairing
    (idx : CharacterTableIndexing G) (ψ η : IrreducibleCharacter G) :
    characterTableSquareColumnPairing idx ψ η =
      characterTableClassColumnPairingOfIndexing idx
        (idx.rowColumnEquiv ψ) (idx.rowColumnEquiv η) := by
  simp [characterTableSquareColumnPairing, characterTableClassColumnPairingOfIndexing,
    characterTableClassColumnPairing]

theorem characterTableClassColumnPairingOfIndexing_eq_squareColumnPairing
    (idx : CharacterTableIndexing G) (C D : ConjClasses G) :
    characterTableClassColumnPairingOfIndexing idx C D =
      characterTableSquareColumnPairing idx
        (idx.rowColumnEquiv.symm C) (idx.rowColumnEquiv.symm D) := by
  simp [characterTableSquareColumnPairing, characterTableClassColumnPairingOfIndexing,
    characterTableClassColumnPairing]

theorem characterTableSquareColumnPairing_eq_columnPairing_representatives
    (idx : CharacterTableIndexing G) (ψ η : IrreducibleCharacter G) :
    characterTableSquareColumnPairing idx ψ η =
      @characterTableColumnPairing G _ idx.irrFintype
        (conjugacyClassRepresentative (idx.rowColumnEquiv ψ))
        (conjugacyClassRepresentative (idx.rowColumnEquiv η)) := by
  rw [characterTableSquareColumnPairing_eq_classColumnPairing]
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

/-- Primitive cases form of the second (column) orthogonality theorem
([Is] Thm 2.18 / 6.10).

Both projections (conjugate and non-conjugate columns) are derived from the matrix
identity `D · Aᴴ · A = (Nat.card G : ℂ) • 1`, where `A` is the (square) reindexed
character table and `D` is the diagonal of conjugacy-class sizes. The matrix
identity is `characterTableClassSizeSquareMatrix_mul_conjTranspose_eq_inv_mul_cardDiagonal`
multiplied on the right by `A`.

Takes a `CharacterTableIndexing` together with weighted row orthogonality
`CharacterTableWeightedRowOrthogonality idx` as explicit hypotheses; supplying these
keeps the statement uncoupled from the existence/finiteness proof for the indexing
type and from the row orthogonality proof. -/
theorem column_orthogonality_cases
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (g h : G) :
    letI := idx.irrFintype
    (IsConj g h →
      characterTableColumnPairing g h =
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ)) ∧
    (¬ IsConj g h →
      characterTableColumnPairing g h = 0) := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
  -- Existing matrix bridge: D · Aᴴ = A⁻¹ · cardDiag.
  have hbridge :
      characterTableClassSizeSquareMatrix idx *
          Matrix.conjTranspose (characterTableSquareMatrix idx) =
        (characterTableSquareMatrix idx)⁻¹ *
          Matrix.diagonal (fun _ : IrreducibleCharacter G => (Nat.card G : ℂ)) :=
    characterTableClassSizeSquareMatrix_mul_conjTranspose_eq_inv_mul_cardDiagonal idx hrow
  -- cardDiag is `(Nat.card G : ℂ) • 1`, so it commutes with A.
  have hcardDiag_scalar :
      (Matrix.diagonal (fun _ : IrreducibleCharacter G => (Nat.card G : ℂ))) =
        (Nat.card G : ℂ) •
          (1 : Matrix (IrreducibleCharacter G) (IrreducibleCharacter G) ℂ) := by
    ext χ ψ
    by_cases hχψ : χ = ψ
    · subst hχψ; simp
    · simp [Matrix.diagonal_apply_ne _ hχψ, Matrix.one_apply_ne hχψ]
  -- Multiply on the right by A: D · Aᴴ · A = A⁻¹ · cardDiag · A = cardDiag.
  have hkey :
      characterTableClassSizeSquareMatrix idx *
          (Matrix.conjTranspose (characterTableSquareMatrix idx) *
            characterTableSquareMatrix idx) =
        Matrix.diagonal (fun _ : IrreducibleCharacter G => (Nat.card G : ℂ)) := by
    rw [← Matrix.mul_assoc, hbridge, hcardDiag_scalar]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.inv_mul_of_invertible]
  -- Extract entry at (ψh, ηg).
  set Ch : ConjClasses G := ConjClasses.mk h with hCh_def
  set Cg : ConjClasses G := ConjClasses.mk g with hCg_def
  set ψh : IrreducibleCharacter G := idx.rowColumnEquiv.symm Ch with hψh_def
  set ηg : IrreducibleCharacter G := idx.rowColumnEquiv.symm Cg with hηg_def
  have hψh_eq : idx.rowColumnEquiv ψh = Ch := by simp [hψh_def]
  have hηg_eq : idx.rowColumnEquiv ηg = Cg := by simp [hηg_def]
  -- LHS entry: (D · (Aᴴ · A)) ψh ηg = (|Ch| : ℂ) · column_pairing g h.
  have hAtA_entry :
      (Matrix.conjTranspose (characterTableSquareMatrix idx) *
        characterTableSquareMatrix idx) ψh ηg =
      characterTableColumnPairing g h := by
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, characterTableSquareMatrix_apply,
      hψh_eq, hηg_eq, hCh_def, hCg_def, characterTableEntry_mk]
    rw [characterTableColumnPairing_eq_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [mul_comm]
  have hLHS :
      (characterTableClassSizeSquareMatrix idx *
        (Matrix.conjTranspose (characterTableSquareMatrix idx) *
          characterTableSquareMatrix idx)) ψh ηg =
      (conjugacyClassSize Ch : ℂ) * characterTableColumnPairing g h := by
    -- characterTableClassSizeSquareMatrix idx is defeq to a Matrix.diagonal.
    change (Matrix.diagonal
        (fun ψ => (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ)) *
        (Matrix.conjTranspose (characterTableSquareMatrix idx) *
          characterTableSquareMatrix idx)) ψh ηg = _
    rw [Matrix.diagonal_mul, hψh_eq, hAtA_entry]
  -- RHS entry: cardDiag ψh ηg = if ψh = ηg then |G| else 0.
  have hRHS :
      (Matrix.diagonal (fun _ : IrreducibleCharacter G => (Nat.card G : ℂ))) ψh ηg =
        if ψh = ηg then (Nat.card G : ℂ) else 0 := by
    rw [Matrix.diagonal_apply]
  -- Apply both to the matrix entry equation.
  have hentry : (characterTableClassSizeSquareMatrix idx *
        (Matrix.conjTranspose (characterTableSquareMatrix idx) *
          characterTableSquareMatrix idx)) ψh ηg =
      (Matrix.diagonal (fun _ : IrreducibleCharacter G => (Nat.card G : ℂ))) ψh ηg := by
    rw [hkey]
  rw [hLHS, hRHS] at hentry
  -- Nonzero class sizes.
  have hsize_h_pos : 0 < conjugacyClassSize Ch := by
    rw [conjugacyClassSize]
    exact Nat.card_pos_iff.mpr ⟨⟨h, ConjClasses.mem_carrier_mk⟩, inferInstance⟩
  have hsize_h_ne : (conjugacyClassSize Ch : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hsize_h_pos.ne'
  refine ⟨?_, ?_⟩
  · -- Conjugate case.
    intro hgh
    have hCheq : Ch = Cg := by
      change ConjClasses.mk h = ConjClasses.mk g
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr (IsConj.symm hgh)
    have hpsi : ψh = ηg := by
      change idx.rowColumnEquiv.symm Ch = idx.rowColumnEquiv.symm Cg
      rw [hCheq]
    rw [if_pos hpsi] at hentry
    -- hentry: (|Ch| : ℂ) * pairing = |G|. Use |Ch| = |Cg|.
    have hSize_eq : (conjugacyClassSize Ch : ℂ) = (conjugacyClassSize Cg : ℂ) := by
      rw [hCheq]
    rw [hSize_eq] at hentry
    have hsize_g_pos : 0 < conjugacyClassSize Cg := by
      change 0 < conjugacyClassSize (ConjClasses.mk g)
      rw [conjugacyClassSize]
      exact Nat.card_pos_iff.mpr ⟨⟨g, ConjClasses.mem_carrier_mk⟩, inferInstance⟩
    have hsize_g_ne : (conjugacyClassSize Cg : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hsize_g_pos.ne'
    have hcent : (Nat.card G : ℂ) / (conjugacyClassSize Cg : ℂ) =
        (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
      change (Nat.card G : ℂ) / (conjugacyClassSize (ConjClasses.mk g) : ℂ) = _
      exact card_centralizer_eq_card_div_conjugacyClassSize_cast (G := G) g
    -- Solve for pairing using hentry and hcent.
    rw [← hcent, eq_div_iff hsize_g_ne, mul_comm]
    exact hentry
  · -- Non-conjugate case.
    intro hgh
    have hCne : Ch ≠ Cg := by
      intro he
      apply hgh
      have : IsConj h g := ConjClasses.mk_eq_mk_iff_isConj.mp he
      exact this.symm
    have hpsi_ne : ψh ≠ ηg := by
      change idx.rowColumnEquiv.symm Ch ≠ idx.rowColumnEquiv.symm Cg
      intro he
      exact hCne (idx.rowColumnEquiv.symm.injective he)
    rw [if_neg hpsi_ne] at hentry
    exact (mul_eq_zero.mp hentry).resolve_left hsize_h_ne

/-- Named-column form of the diagonal second orthogonality relation. -/
theorem characterTableColumnPairing_diag
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (g : G) :
    letI := idx.irrFintype
    characterTableColumnPairing g g =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  letI := idx.irrFintype
  exact (column_orthogonality_cases idx hrow g g).1 (IsConj.refl g)

/-- Named-column form of the conjugate second orthogonality relation. -/
theorem characterTableColumnPairing_conj
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    {g h : G} (hgh : IsConj g h) :
    letI := idx.irrFintype
    characterTableColumnPairing g h =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  letI := idx.irrFintype
  exact (column_orthogonality_cases idx hrow g h).1 hgh

/-- Named-column form of the non-conjugate second orthogonality relation. -/
theorem characterTableColumnPairing_not_conj
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    {g h : G} (hgh : ¬ IsConj g h) :
    letI := idx.irrFintype
    characterTableColumnPairing g h = 0 := by
  letI := idx.irrFintype
  exact (column_orthogonality_cases idx hrow g h).2 hgh

/-- Diagonal second (column) orthogonality:
`∑_{χ ∈ Irr G} χ(g) · star (χ(g)) = |C_G(g)|`.

This is the `g = h` specialization of `column_orthogonality_cases`. -/
theorem column_orthogonality_diag
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (g : G) :
    letI := idx.irrFintype
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) g) =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  letI := idx.irrFintype
  simpa using characterTableColumnPairing_diag (G := G) idx hrow g

/-- **Second (column) orthogonality**, conjugate case ([Is] Thm 2.18 / 6.10).

For `g, h ∈ G` with `g ~ h`, `∑_{χ ∈ Irr G} χ(g) · χ̄(h) = |C_G(g)|` in `ℂ`.

The sum runs over `IrreducibleCharacter G`, the named subtype of `ClassFunction G ℂ`
carved out by `IsIrreducibleCharacter`.

This is the conjugate projection of `column_orthogonality_cases`. -/
theorem column_orthogonality_conj
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    {g h : G} (hgh : IsConj g h) :
    letI := idx.irrFintype
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) =
    (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  letI := idx.irrFintype
  simpa using characterTableColumnPairing_conj (G := G) idx hrow hgh

/-- **Second (column) orthogonality**, non-conjugate case ([Is] Thm 2.18 / 6.10).

For `g, h ∈ G` with `g ≁ h`, `∑_{χ ∈ Irr G} χ(g) · χ̄(h) = 0` in `ℂ`. -/
theorem column_orthogonality_not_conj
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    {g h : G} (hgh : ¬ IsConj g h) :
    letI := idx.irrFintype
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) = 0 := by
  letI := idx.irrFintype
  simpa using characterTableColumnPairing_not_conj (G := G) idx hrow hgh

end OddOrder.RepresentationTheory
