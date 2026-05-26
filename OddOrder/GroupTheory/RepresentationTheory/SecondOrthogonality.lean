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
* The **proof core** is `column_orthogonality_cases`.  It is deferred and routed to
  `issues/0027-peterfalvi-column-orthogonality-core.md`: the classical route uses
  invertibility of the character table (matrix algebra). The derived public lemmas
  below are kept `sorry`-free.

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
* `OddOrder.RepresentationTheory.characterTableSquareColumnPairing_diag_of_weightedRowOrthogonality`
  and `characterTableSquareColumnPairing_eq_zero_of_ne_of_weightedRowOrthogonality` —
  the conditional column relations extracted from the matrix proof core.
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

/-- A conjugacy class of a finite group is nonempty, hence has positive size. -/
theorem conjugacyClassSize_pos [Finite G] (C : ConjClasses G) :
    0 < conjugacyClassSize C := by
  rw [conjugacyClassSize]
  rcases ConjClasses.exists_rep C with ⟨g, hg⟩
  exact Nat.card_pos_iff.mpr
    ⟨⟨g, by
      rw [← hg]
      exact ConjClasses.mem_carrier_mk⟩, inferInstance⟩

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
  have hclass_pos : 0 < conjugacyClassSize (ConjClasses.mk g) :=
    conjugacyClassSize_pos (G := G) (ConjClasses.mk g)
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

/-- Multiplying the column Gram matrix by the class-size diagonal gives the scalar
diagonal matrix `|G| I`.

This is the next matrix-algebra step after canceling the left character-table factor in the
weighted row Gram identity.  Entrywise, it says
`|C| * (Aᴴ A)_{C,D} = |G| δ_{C,D}` after square reindexing. -/
theorem characterTableClassSizeSquareMatrix_mul_columnGram_eq_cardDiagonal
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx) :
    letI := idx.irrFintype
    letI := Classical.decEq (IrreducibleCharacter G)
    letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
    characterTableClassSizeSquareMatrix idx *
        (Matrix.conjTranspose (characterTableSquareMatrix idx) *
          characterTableSquareMatrix idx) =
      Matrix.diagonal (fun _ : IrreducibleCharacter G => (Nat.card G : ℂ)) := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
  have hbridge :=
    characterTableClassSizeSquareMatrix_mul_conjTranspose_eq_inv_mul_cardDiagonal
      (G := G) idx hrow
  have hmul := congrArg (fun M =>
    M * characterTableSquareMatrix idx) hbridge
  have hdiag :
      Matrix.diagonal (fun _ : IrreducibleCharacter G => (Nat.card G : ℂ)) =
        (Nat.card G : ℂ) • (1 : Matrix (IrreducibleCharacter G)
          (IrreducibleCharacter G) ℂ) :=
    (Matrix.smul_one_eq_diagonal (m := IrreducibleCharacter G) (Nat.card G : ℂ)).symm
  rw [hdiag] at hmul ⊢
  simpa [Matrix.mul_assoc, Matrix.smul_mul] using hmul

/-- Entrywise form of
`characterTableClassSizeSquareMatrix_mul_columnGram_eq_cardDiagonal`. -/
theorem conjugacyClassSize_mul_characterTableColumnGram_apply
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (ψ η : IrreducibleCharacter G) :
    letI := idx.irrFintype
    letI := Classical.decEq (IrreducibleCharacter G)
    letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
    (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ) *
        ((Matrix.conjTranspose (characterTableSquareMatrix idx) *
          characterTableSquareMatrix idx) ψ η) =
      if ψ = η then (Nat.card G : ℂ) else 0 := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
  have hmatrix :=
    characterTableClassSizeSquareMatrix_mul_columnGram_eq_cardDiagonal (G := G) idx hrow
  have hentry := congrFun (congrFun hmatrix ψ) η
  by_cases hψη : ψ = η
  · subst η
    simpa only [characterTableClassSizeSquareMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_apply_eq, if_true] using hentry
  · rw [if_neg hψη]
    simpa only [characterTableClassSizeSquareMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_apply_ne _ hψη] using hentry

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

/-- The usual matrix column Gram entry is the complex conjugate of the
`characterTableSquareColumnPairing` convention used in this file. -/
theorem characterTableConjTranspose_mul_squareMatrix_apply_eq_star_squareColumnPairing
    (idx : CharacterTableIndexing G) (ψ η : IrreducibleCharacter G) :
    letI := idx.irrFintype
    ((Matrix.conjTranspose (characterTableSquareMatrix idx) *
          characterTableSquareMatrix idx) ψ η) =
      star (characterTableSquareColumnPairing idx ψ η) := by
  letI := idx.irrFintype
  simp [Matrix.mul_apply, characterTableSquareColumnPairing, Matrix.conjTranspose_apply,
    star_sum, star_mul, mul_comm]

/-- Conditional off-diagonal column orthogonality in the square indexed table,
assuming the weighted row orthogonality input. -/
theorem characterTableSquareColumnPairing_eq_zero_of_ne_of_weightedRowOrthogonality
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    {ψ η : IrreducibleCharacter G} (hψη : ψ ≠ η) :
    letI := idx.irrFintype
    letI := Classical.decEq (IrreducibleCharacter G)
    letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
    characterTableSquareColumnPairing idx ψ η = 0 := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
  have hmul :=
    conjugacyClassSize_mul_characterTableColumnGram_apply (G := G) idx hrow ψ η
  rw [if_neg hψη] at hmul
  have hclass_ne : (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (conjugacyClassSize_pos (G := G) (idx.rowColumnEquiv ψ)).ne'
  have hgram :
      ((Matrix.conjTranspose (characterTableSquareMatrix idx) *
          characterTableSquareMatrix idx) ψ η) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hclass_ne
  have hstar : star (characterTableSquareColumnPairing idx ψ η) = 0 := by
    simpa [characterTableConjTranspose_mul_squareMatrix_apply_eq_star_squareColumnPairing]
      using hgram
  exact star_eq_zero.mp hstar

/-- Conditional diagonal column orthogonality in the square indexed table,
assuming the weighted row orthogonality input. -/
theorem characterTableSquareColumnPairing_diag_of_weightedRowOrthogonality
    [Finite G] (idx : CharacterTableIndexing G)
    (hrow : CharacterTableWeightedRowOrthogonality idx)
    (ψ : IrreducibleCharacter G) :
    letI := idx.irrFintype
    letI := Classical.decEq (IrreducibleCharacter G)
    letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
    characterTableSquareColumnPairing idx ψ ψ =
      (Nat.card G : ℂ) / (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ) := by
  letI := idx.irrFintype
  letI := Classical.decEq (IrreducibleCharacter G)
  letI := characterTableSquareMatrixInvertibleOfWeightedRowOrthogonality (G := G) idx hrow
  have hmul :=
    conjugacyClassSize_mul_characterTableColumnGram_apply (G := G) idx hrow ψ ψ
  rw [if_pos rfl] at hmul
  have hclass_ne : (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (conjugacyClassSize_pos (G := G) (idx.rowColumnEquiv ψ)).ne'
  have hgram :
      ((Matrix.conjTranspose (characterTableSquareMatrix idx) *
          characterTableSquareMatrix idx) ψ ψ) =
        (Nat.card G : ℂ) / (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ) := by
    rw [eq_div_iff hclass_ne]
    simpa [mul_comm] using hmul
  have hstar :
      star (characterTableSquareColumnPairing idx ψ ψ) =
        (Nat.card G : ℂ) / (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ) := by
    simpa [characterTableConjTranspose_mul_squareMatrix_apply_eq_star_squareColumnPairing]
      using hgram
  have hstar_rhs :
      star ((Nat.card G : ℂ) / (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ)) =
        (Nat.card G : ℂ) / (conjugacyClassSize (idx.rowColumnEquiv ψ) : ℂ) := by
    simp
  rw [← hstar_rhs, ← hstar]
  simp

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
