/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockOfIrreducible
import OddOrder.GroupTheory.RepresentationTheory.Modular.SecondMainBlockForm

/-!
# Navarro (5.8) for the ordinary irreducibles

`generalizedDecompositionNumber_eq_zero_of_inducedBlockOfCentralizer_ne` states the second main
theorem for an arbitrary representation together with an invariant lattice.  The ordinary
irreducibles of `G` come with a canonical such lattice (`wedderburnLattice`), and the block they
determine is `blockOfIrr`, so the statement specialises with nothing to supply:

`d^x_{χ_i μ} = 0`   unless the block of `μ` induces the block of `χ_i`.

This is the vanishing that makes the generalized decomposition matrix block-diagonal.

## Main results

* `OddOrder.RepresentationTheory.Modular.generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Finite ιG] [∀ i, Nonempty (nnG i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Finite ι'] [∀ i, Nonempty (m i)]
variable {κ : Type*} {mG : κ → Type*} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
  [Finite κ] [∀ i, Nonempty (mG i)]

set_option maxHeartbeats 1000000 in
-- Same cost as the general form it specialises: unifying the two splittings, the two block index
-- sets and the three incarnations of `f_b`.
omit [Finite κ] in
/-- **Navarro (5.8) for `χ_i ∈ Irr(G)`.**  The generalized decomposition numbers of the `i`-th
ordinary irreducible vanish outside the blocks of `C_G(x)` inducing `blockOfIrr eG i`. -/
theorem generalizedDecompositionNumber_eq_zero_of_blockOfIrr_ne (hp : p.Prime)
    {x : G} (hx : IsPElement p x) [Fintype ↥(centralizerOf x)]
    (e : MonoidAlgebra K ↥(centralizerOf x) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
    (eG : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (mG i) (mG i) K)
    {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
    (hπG : Function.Surjective πG)
    (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
    {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
    (hnilH : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
    (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
      blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
    {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf x)))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf x)))
    {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
    {i : κ} {j : ι}
    (hj : inducedBlockOfCentralizer x π hπ hlin πG hπG hlinG hnilG hp hx
          (Quotient.mk (blockSetoid π hπ hlin) j)
        ≠ blockOfIrr eG hπG hlinG hnilG i) :
    generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x hp hω' hπ hlin hkerJ
        ((wedderburnRepresentation eG i).character)
        (fun _ _ hgh => character_eq_of_isConj _ hgh) j = 0 :=
  generalizedDecompositionNumber_eq_zero_of_inducedBlockOfCentralizer_ne hp hx e hπG hlinG hπ hlin
    hkerJ hnilH hnilG hω hω' hζ hζk hζK (wedderburnRepresentation eG i)
    (invariant_wedderburnLattice eG i) (exists_smul_id_of_commute_wedderburnLattice eG i) hj

end OddOrder.RepresentationTheory.Modular
