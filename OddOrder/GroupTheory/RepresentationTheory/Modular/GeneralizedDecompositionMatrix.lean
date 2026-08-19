/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryColumnOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.Modular.PSectionClassCount

/-!
# The generalized decomposition matrix

Navarro's proof of (5.12) forms the square matrix

`J = (d^{x_i}_{χμ})`,   rows `χ ∈ Irr(G)`,   columns `(x_i, μ)` with `μ ∈ IBr(C_G(x_i))`,

`x_1, …, x_k` representing the `G`-classes of `p`-elements, and shows it is regular.  Navarro
gets regularity from `J̄ᵗ J = diag(C^{(x_1)}, …, C^{(x_k)})`, i.e. from (5.13); the route taken
here is shorter and needs neither (5.13) nor the numbers at `x_i⁻¹`:

`E = J · diag(B^{(x_1)}, …, B^{(x_k)})`,

where `B^{(x_i)}` is the Brauer character table of `C_G(x_i)` and `E` is the **ordinary character
table of `G`**, read on the class representatives `x_i z` supplied by the `p`-section
parametrisation (`PSectionClassCount`).  The factorisation is nothing but the defining property
(5.1) of the generalized decomposition numbers, `χ(x_i z) = ∑_μ d^{x_i}_{χμ} μ(z)`.  Both `E` and
each `B^{(x_i)}` are regular, so `J` is.

The `p`-element classes index everything directly — no representatives of them are chosen beyond
`Quotient.out`, which is what `PSectionClassCount` already uses.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.pElementRep` — `x_D`, a representative of the class `D`
* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionMatrix` — `J`
* `OddOrder.RepresentationTheory.Modular.sectionCharacterMatrix` — `E`

## Main results

* `OddOrder.RepresentationTheory.Modular.sectionCharacterMatrix_eq_mul_blockDiagonal` —
  `E = J · diag(B)`
* `OddOrder.RepresentationTheory.Modular.isUnit_det_blockDiagonal_brauerCharacterMatrix`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Finite G]

/-! ### The index set of the `p`-sections -/

/-- The `G`-classes of `p`-elements: the index set of the `p`-sections, and of the column blocks
of the generalized decomposition matrix. -/
abbrev PElementClass (p : ℕ) (G : Type*) [Group G] : Type _ :=
  {D : ConjClasses G // IsPElementClass p D}

/-- A representative of a `p`-element class. -/
noncomputable def pElementRep (D : PElementClass p G) : G := Quotient.out (D : ConjClasses G)

omit [Finite G] in
theorem isPElement_pElementRep (D : PElementClass p G) : IsPElement p (pElementRep D) :=
  isPElementClass_mk.mp (by rw [pElementRep, conjClasses_mk_out]; exact D.2)

/-! ### The two matrices -/

variable {ι : PElementClass p G → Type*} [∀ D, Fintype (ι D)] [∀ D, DecidableEq (ι D)]
  {nn : ∀ D : PElementClass p G, ι D → Type*}
  [∀ D i, Fintype (nn D i)] [∀ D i, DecidableEq (nn D i)] [∀ D i, Nonempty (nn D i)]
variable (hp : p.Prime)
  {ω' : PElementClass p G → ResidueField 𝒪}
  (hω' : ∀ D : PElementClass p G,
    IsPrimitiveRoot (ω' D) (pRegularExponent p ↥(centralizerOf (pElementRep D))))
  {π : ∀ D : PElementClass p G,
    MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pElementRep D)) →+*
      ∀ i, Matrix (nn D i) (nn D i) (ResidueField 𝒪)}
  (hπ : ∀ D, Function.Surjective (π D))
  (hlin : ∀ (D : PElementClass p G) (c : ResidueField 𝒪)
    (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pElementRep D))),
    π D (c • a) = c • π D a)
  (hkerJ : ∀ D : PElementClass p G, RingHom.ker (π D)
    = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pElementRep D))))
variable {ι' : Type*} [Fintype ι'] {mG : ι' → Type*} [∀ i, Fintype (mG i)]
  [∀ i, DecidableEq (mG i)] [∀ i, Nonempty (mG i)]
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (mG i) (mG i) K)

/-- The chosen `p`-regular representative of the class of `C_G(x_D)` indexed by `n`. -/
noncomputable def sectionRep (D : PElementClass p G) (n : ι D) : G :=
  ((pRegularRep hp (hπ D) (hlin D) (hkerJ D) n : ↥(centralizerOf (pElementRep D))) : G)

omit [IsDomain 𝒪] [ValuationRing 𝒪] [∀ D, DecidableEq (ι D)] in
include hp hπ hlin hkerJ in
theorem isPRegular_sectionRep (D : PElementClass p G) (n : ι D) :
    IsPRegular p (sectionRep hp hπ hlin hkerJ D n) :=
  isPRegular_coe (isPRegular_pRegularRep hp (hπ D) (hlin D) (hkerJ D) n)

/-- **The generalized decomposition matrix** `J = (d^{x_D}_{χ n})`: rows the ordinary
irreducibles of `G`, columns the pairs `(D, n)` with `n ∈ IBr(C_G(x_D))`. -/
noncomputable def generalizedDecompositionMatrix :
    Matrix ι' (Σ D : PElementClass p G, ι D) K := fun i c =>
  generalizedDecompositionNumber (pElementRep c.1) hp (hω' c.1) (hπ c.1) (hlin c.1) (hkerJ c.1)
    ((wedderburnRepresentation eG i).character) (fun _ _ h => character_eq_of_isConj _ h) c.2

/-- **The ordinary character table of `G`, read on the `p`-section parametrisation**:
`E_{χ, (D, n)} = χ(x_D z_{D,n})`.  By `PSectionClassCount` the elements `x_D z_{D,n}` represent
the conjugacy classes of `G` exactly once, so this is the character table with its columns
reindexed. -/
noncomputable def sectionCharacterMatrix :
    Matrix ι' (Σ D : PElementClass p G, ι D) K := fun i c =>
  (wedderburnRepresentation eG i).character
    (pElementRep c.1 * sectionRep hp hπ hlin hkerJ c.1 c.2)

/-! ### The factorisation `E = J · diag(B)` -/

omit [∀ D, DecidableEq (ι D)] [Fintype ι'] [∀ i, Nonempty (mG i)] in
include hp hω' hπ hlin hkerJ in
/-- **`E = J · diag(B)`** — Navarro (5.1) written as a matrix identity.  The `(D, n)` column of
`E` is `χ(x_D z_{D,n}) = ∑_μ d^{x_D}_{χμ} μ(z_{D,n})`, and the Brauer character table of
`C_G(x_D)` supplies the second factor. -/
theorem sectionCharacterMatrix_eq_mul_blockDiagonal
    [Fintype (PElementClass p G)] [DecidableEq (PElementClass p G)] :
    sectionCharacterMatrix hp hπ hlin hkerJ eG
      = generalizedDecompositionMatrix hp hω' hπ hlin hkerJ eG *
        Matrix.blockDiagonal'
          (fun D : PElementClass p G =>
            brauerCharacterMatrix (K := K) hp (hπ D) (hlin D) (hkerJ D)) := by
  ext i c
  obtain ⟨D, n⟩ := c
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  have hoff : ∀ D' : PElementClass p G, D' ≠ D → ∀ μ : ι D',
      generalizedDecompositionMatrix hp hω' hπ hlin hkerJ eG i ⟨D', μ⟩ *
        Matrix.blockDiagonal'
          (fun D : PElementClass p G =>
            brauerCharacterMatrix (K := K) hp (hπ D) (hlin D) (hkerJ D)) ⟨D', μ⟩ ⟨D, n⟩ = 0 :=
    fun D' hD' μ => by rw [Matrix.blockDiagonal'_apply_ne _ _ _ hD', mul_zero]
  rw [Finset.sum_eq_single D (fun D' _ hD' => Finset.sum_eq_zero fun μ _ => hoff D' hD' μ)
    (fun h => absurd (Finset.mem_univ D) h)]
  have hdiag : ∀ μ : ι D,
      Matrix.blockDiagonal'
          (fun D : PElementClass p G =>
            brauerCharacterMatrix (K := K) hp (hπ D) (hlin D) (hkerJ D)) ⟨D, μ⟩ ⟨D, n⟩
        = brauerCharacterMatrix (K := K) hp (hπ D) (hlin D) (hkerJ D) μ n :=
    fun μ => Matrix.blockDiagonal'_apply_eq _ _ _ _
  rw [Finset.sum_congr rfl fun μ _ => by rw [hdiag μ]]
  exact (sum_generalizedDecompositionNumber (pElementRep D) hp (hω' D) (hπ D) (hlin D) (hkerJ D)
    _ _ (isPRegular_pRegularRep hp (hπ D) (hlin D) (hkerJ D) n)).symm

include hp hω' hπ hlin hkerJ in
/-- **The block-diagonal Brauer character table is regular**: each block is
(`isUnit_det_brauerCharacterMatrix`), and the blockwise inverse is a two-sided inverse.

`Matrix.det_blockDiagonal'` is not available for blocks of varying size, so the inverse is
exhibited instead. -/
theorem isUnit_det_blockDiagonal_brauerCharacterMatrix
    [Fintype (PElementClass p G)] [DecidableEq (PElementClass p G)] :
    IsUnit (Matrix.blockDiagonal'
      (fun D : PElementClass p G =>
        brauerCharacterMatrix (K := K) hp (hπ D) (hlin D) (hkerJ D))).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := Matrix.blockDiagonal'
    (fun D : PElementClass p G =>
      (brauerCharacterMatrix (K := K) hp (hπ D) (hlin D) (hkerJ D))⁻¹)) ?_
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
  exact congrArg Matrix.blockDiagonal' (funext fun D => Matrix.mul_nonsing_inv _
    (isUnit_det_brauerCharacterMatrix hp (hω' D) (hπ D) (hlin D) (hkerJ D)))

/-! ### `E` is the character table, so `J` is regular -/

include hp hπ hlin hkerJ in
/-- **The columns of `J` are the conjugacy classes of `G`**: the pair `(D, n)` corresponds to the
class of `x_D z_{D,n}`.  This is `PSectionClassCount` transported along the indexing of
`IBr(C_G(x_D))` by the `p`-regular classes. -/
noncomputable def sectionClassIndexEquiv : (Σ D : PElementClass p G, ι D) ≃ ConjClasses G :=
  (Equiv.sigmaCongrRight fun D : PElementClass p G =>
      (equivPRegularClass hp (hπ D) (hlin D) (hkerJ D)).trans
        ((pSectionClassEquiv hp (isPElement_pElementRep D)).trans
          (Equiv.subtypeEquivRight fun _ => by rw [pElementRep, conjClasses_mk_out]))).trans
    (Equiv.sigmaSubtypeFiberEquiv (pPartClass p) (IsPElementClass p)
      (isPElementClass_pPartClass hp))

omit [IsDomain 𝒪] [ValuationRing 𝒪] [∀ D, DecidableEq (ι D)] in
include hp hπ hlin hkerJ in
theorem sectionClassIndexEquiv_apply (D : PElementClass p G) (n : ι D) :
    sectionClassIndexEquiv hp hπ hlin hkerJ ⟨D, n⟩
      = ConjClasses.mk (pElementRep D * sectionRep hp hπ hlin hkerJ D n) := rfl

variable [Fintype G] [Fintype (ConjClasses G)] [DecidableEq ι'] [Invertible (Nat.card G : K)]
  [Fintype (PElementClass p G)] [DecidableEq (PElementClass p G)]

include hp hπ hlin hkerJ in
/-- The columns of `J`, reindexed by the ordinary irreducibles through the character table. -/
noncomputable def sectionColumnEquiv : (Σ D : PElementClass p G, ι D) ≃ ι' :=
  (sectionClassIndexEquiv hp hπ hlin hkerJ).trans (equivConjClasses eG).symm

omit [IsDomain 𝒪] [ValuationRing 𝒪] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
  [∀ D, DecidableEq (ι D)] [DecidableEq ι'] [Invertible (Nat.card G : K)]
  [Fintype (PElementClass p G)] [DecidableEq (PElementClass p G)] in
include hp hπ hlin hkerJ in
/-- **`E` is the character table.**  Its `(D, n)` column sits at the class of `x_D z_{D,n}`, and
characters are class functions. -/
theorem sectionCharacterMatrix_submatrix :
    (sectionCharacterMatrix hp hπ hlin hkerJ eG).submatrix id
        (sectionColumnEquiv hp hπ hlin hkerJ eG).symm
      = characterMatrix eG := by
  ext i j
  refine character_eq_of_isConj _ (ConjClasses.mk_eq_mk_iff_isConj.mp ?_)
  rw [show ConjClasses.mk (pElementRep ((sectionColumnEquiv hp hπ hlin hkerJ eG).symm j).1 *
      sectionRep hp hπ hlin hkerJ ((sectionColumnEquiv hp hπ hlin hkerJ eG).symm j).1
        ((sectionColumnEquiv hp hπ hlin hkerJ eG).symm j).2)
      = sectionClassIndexEquiv hp hπ hlin hkerJ
          ((sectionColumnEquiv hp hπ hlin hkerJ eG).symm j) from rfl,
    classRep, conjugacyClassRepresentative_mk_eq, sectionColumnEquiv]
  simp

omit [∀ D, DecidableEq (ι D)] [Fintype G] [Fintype (PElementClass p G)]
  [DecidableEq (PElementClass p G)] in
include hp hω' hπ hlin hkerJ in
/-- **The generalized decomposition matrix is regular** — Navarro's "in particular, notice that
the matrix `J` is regular", obtained from `E = J · diag(B)` with both `E` (the character table)
and `diag(B)` regular. -/
theorem isUnit_det_generalizedDecompositionMatrix :
    IsUnit ((generalizedDecompositionMatrix hp hω' hπ hlin hkerJ eG).submatrix id
      (sectionColumnEquiv hp hπ hlin hkerJ eG).symm).det := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (PElementClass p G) := Fintype.ofFinite _
  have hE : IsUnit (characterMatrix eG).det :=
    Matrix.isUnit_det_of_right_inverse (characterMatrix_mul_characterMatrixInv eG)
  rw [← sectionCharacterMatrix_submatrix hp hπ hlin hkerJ eG,
    sectionCharacterMatrix_eq_mul_blockDiagonal hp hω' hπ hlin hkerJ eG,
    ← Matrix.submatrix_mul_equiv _ _ id (sectionColumnEquiv hp hπ hlin hkerJ eG).symm
      (⇑(sectionColumnEquiv hp hπ hlin hkerJ eG).symm),
    Matrix.det_mul, Matrix.det_submatrix_equiv_self] at hE
  exact isUnit_of_mul_isUnit_left hE

end OddOrder.RepresentationTheory.Modular
