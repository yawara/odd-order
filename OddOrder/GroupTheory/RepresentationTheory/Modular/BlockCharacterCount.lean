/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BlockPartitionedMatrix
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecompositionMatrix
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainBlockOfIrr

/-!
# Navarro (5.12): `k(B) = ∑_i ∑_{b^G = B} l(b)`

For a block `B` of `G`, the number of ordinary irreducible characters in `B` equals the total
number of irreducible Brauer characters lying in the blocks of the centralizers `C_G(x_i)` that
induce `B`, the sum running over the `G`-classes of `p`-elements.

The proof is Navarro's, with two simplifications:

* the generalized decomposition matrix `J` is regular because `E = J · diag(B)` with `E` the
  ordinary character table (`GeneralizedDecompositionMatrix`) — Navarro instead uses
  `J̄ᵗ J = diag(Cartan)`, i.e. (5.13);
* "since `J` is regular, each `J_{B_i}` is square" is the Leibniz-formula lemma
  `OddOrder.Matrix.card_eq_card_of_det_ne_zero`, not a rank argument.

The block-diagonal shape of `J` is the second main theorem in the form
`generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne`.

## Main results

* `OddOrder.RepresentationTheory.Modular.card_blockOfIrr_eq_card_inducedBlockOfCentralizer`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule
open OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)]
-- the modular data of the centralizers, indexed by the `G`-classes of `p`-elements
variable [∀ D : PElementClass p G, Fintype ↥(centralizerOf (pElementRep D))]
variable {ι : PElementClass p G → Type*} [∀ D, Fintype (ι D)] [∀ D, DecidableEq (ι D)]
  {nn : ∀ D : PElementClass p G, ι D → Type*}
  [∀ D i, Fintype (nn D i)] [∀ D i, DecidableEq (nn D i)] [∀ D i, Nonempty (nn D i)]
variable {ι' : PElementClass p G → Type*} [∀ D, Finite (ι' D)]
  {m : ∀ D : PElementClass p G, ι' D → Type*}
  [∀ D i, Fintype (m D i)] [∀ D i, DecidableEq (m D i)] [∀ D i, Nonempty (m D i)]
-- the modular data of `G`
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]
variable {κ : Type*} [Finite κ] {mG : κ → Type*} [∀ i, Fintype (mG i)]
  [∀ i, DecidableEq (mG i)] [∀ i, Nonempty (mG i)]
variable (hp : p.Prime)
  {ω : PElementClass p G → 𝒪}
  (hω : ∀ D : PElementClass p G,
    IsPrimitiveRoot (ω D) (pRegularExponent p ↥(centralizerOf (pElementRep D))))
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
  (hnilH : ∀ (D : PElementClass p G) (z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf (pElementRep D)))),
    blockCharacterPi (π D) (hπ D) (hlin D) z = 0 → IsNilpotent z)
  (e : ∀ D : PElementClass p G,
    MonoidAlgebra K ↥(centralizerOf (pElementRep D)) ≃ₐ[K] ∀ i, Matrix (m D i) (m D i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (mG i) (mG i) K)
  {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)

/-- The block of `G` induced by the block of the `μ`-th irreducible Brauer character of
`C_G(x_D)`. -/
noncomputable def inducedBlockOfColumn (c : Σ D : PElementClass p G, ι D) : Block πG hπG hlinG :=
  inducedBlockOfCentralizer (pElementRep c.1) (π c.1) (hπ c.1) (hlin c.1) πG hπG hlinG hnilG hp
    (isPElement_pElementRep c.1) (Quotient.mk (blockSetoid (π c.1) (hπ c.1) (hlin c.1)) c.2)

omit [∀ D, DecidableEq (ι D)] in
include hp hω hω' hπ hlin hkerJ hnilH e hπG hlinG hnilG hζ hζk hζK in
/-- **Navarro (5.12).**  `k(B) = ∑_i ∑_{b ∈ Bl(C_G(x_i)), b^G = B} l(b)`: the ordinary
irreducibles in `B` are as many as the irreducible Brauer characters of the centralizers of the
`p`-element class representatives whose blocks induce `B`.

The generalized decomposition matrix is regular
(`isUnit_det_generalizedDecompositionMatrix`) and, by the second main theorem
(`generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne`), block-diagonal for the two block
partitions; `OddOrder.Matrix.card_eq_card_of_det_ne_zero` then matches the block sizes. -/
theorem card_blockOfIrr_eq_card_inducedBlockOfCentralizer (B : Block πG hπG hlinG) :
    Nat.card {i : κ // blockOfIrr eG hπG hlinG hnilG i = B}
      = Nat.card {c : (Σ D : PElementClass p G, ι D) //
          inducedBlockOfColumn hp hπ hlin hπG hlinG hnilG c = B} := by
  classical
  haveI : Fintype κ := Fintype.ofFinite κ
  haveI : Fintype (PElementClass p G) := Fintype.ofFinite _
  have hdet : ((generalizedDecompositionMatrix hp hω' hπ hlin hkerJ eG).submatrix id
      (sectionColumnEquiv hp hπ hlin hkerJ eG).symm).det ≠ 0 :=
    (isUnit_det_generalizedDecompositionMatrix hp hω' hπ hlin hkerJ eG).ne_zero
  have hblock : ∀ i j : κ,
      blockOfIrr eG hπG hlinG hnilG i
          ≠ inducedBlockOfColumn hp hπ hlin hπG hlinG hnilG
              ((sectionColumnEquiv hp hπ hlin hkerJ eG).symm j) →
        (generalizedDecompositionMatrix hp hω' hπ hlin hkerJ eG).submatrix id
          (sectionColumnEquiv hp hπ hlin hkerJ eG).symm i j = 0 := by
    intro i j h
    exact generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne hp
      (isPElement_pElementRep _) (e _) eG hπG hlinG (hπ _) (hlin _) (hkerJ _) (hnilH _) hnilG
      (hω _) (hω' _) hζ hζk hζK (Ne.symm h)
  refine (OddOrder.Matrix.card_eq_card_of_det_ne_zero hdet hblock B).trans
    (Nat.card_congr (Equiv.subtypeEquiv (sectionColumnEquiv hp hπ hlin hkerJ eG).symm
      fun _ => Iff.rfl))

end OddOrder.RepresentationTheory.Modular
