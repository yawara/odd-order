/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockOfIrreducible
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanBlockDiagonal

/-!
# The decomposition matrix is block diagonal

`CartanBlockDiagonal` shows that two irreducible Brauer characters occurring in the *same*
ordinary character have the same central character.  What the block theory actually wants is the
sharper statement relating the two block partitions:

`d_{χφ} ≠ 0 → φ ∈ B(χ)`,

i.e. an irreducible Brauer character occurring in `χ` lies in the block `blockOfIrr` of `χ`.

Both sides are named by a central character, so the proof is a computation of one scalar.  The
centre acts on the reduction of the lattice of `χ` by `λ_χ(z) = ω_χ(z)*`
(`asAlgebraHom_reduction_center_eq`, the explicit-witness form of
`exists_smul_id_asAlgebraHom_reduction`), and by
`centralCharacterAlg_eq_of_decompositionNumber_ne_zero` that same scalar is the central character
of any Brauer character occurring in `χ`.  So `λ_φ = λ_χ`, and
`MatrixModule.eq_blockOfCentralCharacter` turns the equality of central characters into an
equality of blocks.

## Main results

* `OddOrder.RepresentationTheory.Modular.asAlgebraHom_reduction_center_eq` — the centre acts on
  the reduction of an absolutely irreducible lattice by `λ_χ`
* `OddOrder.RepresentationTheory.Modular.blockOfIrr_eq_of_decompositionMatrix_ne_zero`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.GroupTheory.CenterClassSum
open OddOrder.MatrixModule

open scoped TensorProduct

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Module.Finite 𝒪 L]
  [Nontrivial L]

/-! ### The scalar by which the centre acts on the reduction -/

set_option maxHeartbeats 1000000 in
-- The reduced central character carries the whole `𝒪 → k` lift chain; comparing it to the scalar
-- produced by absolute irreducibility is what costs the heartbeats.
omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] [Module.Finite 𝒪 L] in
/-- **The centre acts on the reduction of an absolutely irreducible lattice by `λ_χ`.**  This is
`exists_smul_id_asAlgebraHom_reduction` with the scalar named: it is the reduction of `ω_χ`
evaluated on any lift of `z`, which is exactly the reduced central character of `χ`. -/
theorem asAlgebraHom_reduction_center_eq (ρ : Representation 𝒪 G L)
    (hEnd : ∀ E : Module.End K (K ⊗[𝒪] L),
      (∀ a : MonoidAlgebra 𝒪 G,
        E * LinearMap.baseChange K (ρ.asAlgebraHom a)
          = LinearMap.baseChange K (ρ.asAlgebraHom a) * E) →
      ∃ c : K, E = c • LinearMap.id)
    (z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)) :
    (reduction ρ).asAlgebraHom (z : MonoidAlgebra (ResidueField 𝒪) G)
      = reducedCentralCharacterAlg (residue_surjective (R := 𝒪))
          (centralCharacter K ρ.asAlgebraHom hEnd) z • LinearMap.id := by
  classical
  set c : 𝒪 := centralScalar K ρ.asAlgebraHom hEnd
    (centerLift (residue_surjective (R := 𝒪)) z) with hc
  have hbase : (reduction ρ).asAlgebraHom (z : MonoidAlgebra (ResidueField 𝒪) G)
      = LinearMap.baseChange (ResidueField 𝒪) (ρ.asAlgebraHom
          ((centerLift (residue_surjective (R := 𝒪)) z :
            Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) : MonoidAlgebra 𝒪 G)) := by
    rw [← mapRingHom_centerLift (residue_surjective (R := 𝒪)) z,
      asAlgebraHom_reduction_mapRingHom]
  have hlam : reducedCentralCharacterAlg (residue_surjective (R := 𝒪))
      (centralCharacter K ρ.asAlgebraHom hEnd) z = residue 𝒪 c := rfl
  have halg : residue 𝒪 c = algebraMap 𝒪 (ResidueField 𝒪) c := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
  rw [hbase, apply_center_eq_centralScalar_smul K ρ.asAlgebraHom hEnd, ← hc,
    LinearMap.baseChange_smul, LinearMap.baseChange_id, hlam, halg]
  exact (algebraMap_smul (ResidueField 𝒪) c LinearMap.id).symm

/-! ### Block diagonality of `D` -/

variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

set_option maxHeartbeats 1000000 in
-- Unifying the two namings of a block (through `Quotient.mk` and through `blockOfLattice`) has
-- to unfold both central-character constructions.
set_option linter.unusedFintypeInType false in
omit [Fintype ι'] in
include hp hω hω' hkerJ in
/-- **The decomposition matrix is block diagonal.**  If the irreducible Brauer character `φ`
occurs in the ordinary irreducible `χ_i`, then `φ` lies in the block of `χ_i`.

Both blocks are the one named by a central character: the block of `φ` by `λ_φ`, the block of
`χ_i` by `λ_{χ_i}`.  The centre acts on the reduction of `χ_i`'s lattice by `λ_{χ_i}`, and
`centralCharacterAlg_eq_of_decompositionNumber_ne_zero` says that scalar is `λ_φ`. -/
theorem blockOfIrr_eq_of_decompositionMatrix_ne_zero (i : ι') {φ : ι}
    (hφ : decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ ≠ 0) :
    Quotient.mk (blockSetoid π hπ hlin) φ = blockOfIrr e hπ hlin hnil i := by
  classical
  have h1 : blockCharacter π hπ hlin (blockOfIrr e hπ hlin hnil i)
      = centralCharacterAlg π φ hπ hlin := by
    have h2 : blockCharacter π hπ hlin (blockOfIrr e hπ hlin hnil i)
        = reducedCentralCharacterAlg (residue_surjective (R := 𝒪))
            (centralCharacter K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
              (exists_smul_id_of_commute_wedderburnLattice e i)) :=
      blockCharacter_blockOfLattice K _ _ _ π hπ hlin hnil
    rw [h2]
    refine AlgHom.ext fun z => ?_
    exact centralCharacterAlg_eq_of_decompositionNumber_ne_zero (nn := nn) hp hω hω' hπ hlin hkerJ
      _ hφ (asAlgebraHom_reduction_center_eq
        (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i)
        (exists_smul_id_of_commute_wedderburnLattice (𝒪 := 𝒪) e i) z)
  rw [eq_blockOfCentralCharacter π hπ hlin hnil (blockCharacter_mk π hπ hlin φ),
    eq_blockOfCentralCharacter π hπ hlin hnil h1]

set_option maxHeartbeats 1000000 in
-- Same block-naming unfolding as the theorem it contraposes.
set_option linter.unusedFintypeInType false in
omit [Fintype ι'] in
include hp hω hω' hkerJ in
/-- **The contrapositive**: the decomposition numbers of `χ_i` vanish outside its own block. -/
theorem decompositionMatrix_eq_zero_of_blockOfIrr_ne (i : ι') {φ : ι}
    (hφ : Quotient.mk (blockSetoid π hπ hlin) φ ≠ blockOfIrr e hπ hlin hnil i) :
    decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ = 0 := by
  by_contra hne
  exact hφ (blockOfIrr_eq_of_decompositionMatrix_ne_zero hp hω hω' hπ hlin hkerJ hnil e i hne)

end OddOrder.RepresentationTheory.Modular
