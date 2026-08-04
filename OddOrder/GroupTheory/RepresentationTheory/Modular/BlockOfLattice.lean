/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CentralCharacterBlock
import OddOrder.GroupTheory.RepresentationTheory.Modular.CenterReduction
import OddOrder.GroupTheory.RepresentationTheory.Modular.LatticeBlockIdempotent

/-!
# The block of an ordinary character

Navarro's Chapter 3 attaches a `p`-block to each `χ ∈ Irr(G)`: the one whose central character is
`λ_χ = ω_χ mod 𝔪`.  Here `ω_χ : Z(𝒪G) →ₐ[𝒪] 𝒪` is the central character of an absolutely
irreducible `𝒪`-lattice affording `χ` (`LatticeCentralCharacter.centralCharacter`, integral by
construction), and `λ_χ` is its reduction, packaged as an algebra homomorphism
`Z(FG) →ₐ[F] F` by `CenterReduction.reducedCentralCharacterAlg`.  Navarro (3.11)
(`MatrixModule.blockOfCentralCharacter`) then names the unique block with that central character.

That makes "`χ ∈ B`" a genuine equation `blockOfLattice = B`, and combining it with (3.13.a)
(`LatticeBlockIdempotent`) turns it into the statement (5.7) actually consumes:

* `χ ∉ B` ⟹ `f_B` annihilates the lattice;
* `χ ∈ B` ⟹ `f_B` acts as the identity.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.blockOfLattice` — the block of `χ`

## Main results

* `OddOrder.RepresentationTheory.Modular.blockCharacter_blockOfLattice`
* `OddOrder.RepresentationTheory.Modular.apply_eq_zero_of_blockOfLattice_ne` — (3.13.a), `χ ∉ B`
* `OddOrder.RepresentationTheory.Modular.apply_eq_id_of_blockOfLattice_eq` — (3.13.a), `χ ∈ B`
-/

namespace OddOrder.RepresentationTheory.Modular

open TensorProduct MonoidAlgebra
open OddOrder.GroupTheory.CenterClassSum

variable {𝒪 K F G : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing K] [Algebra 𝒪 K]
  [FaithfulSMul 𝒪 K] [Field F] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)]
variable {L : Type*} [AddCommGroup L] [Module 𝒪 L] [Module.Free 𝒪 L] [Nontrivial L]
variable (K)
variable (ψ : MonoidAlgebra 𝒪 G →ₐ[𝒪] Module.End 𝒪 L)
  (hEnd : ∀ E : Module.End K (K ⊗[𝒪] L),
    (∀ a : MonoidAlgebra 𝒪 G,
      E * LinearMap.baseChange K (ψ a) = LinearMap.baseChange K (ψ a) * E) →
    ∃ c : K, E = c • LinearMap.id)
variable {f : 𝒪 →+* F} (hf : Function.Surjective f)
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)]
  [∀ i, DecidableEq (nn i)] [∀ i, Nonempty (nn i)]
variable (π : MonoidAlgebra F G →+* ∀ j, Matrix (nn j) (nn j) F) (hπ : Function.Surjective π)
  (hlin : ∀ (c : F) (a : MonoidAlgebra F G), π (c • a) = c • π a)
  [Fintype (MatrixModule.Block π hπ hlin)]
  (hnil : ∀ z : Subalgebra.center F (MonoidAlgebra F G),
    MatrixModule.blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)

/-- **The block of an ordinary character.**  The unique block of `FG` whose central character is
`λ_χ = ω_χ mod 𝔪`. -/
noncomputable def blockOfLattice : MatrixModule.Block π hπ hlin :=
  MatrixModule.blockOfCentralCharacter π hπ hlin hnil
    (reducedCentralCharacterAlg hf (centralCharacter K ψ hEnd))

set_option maxHeartbeats 1000000 in
-- The central characters carry long instance chains; comparing them as algebra maps is what
-- costs the heartbeats.
set_option linter.unusedFintypeInType false in
omit [IsLocalRing 𝒪] [Fintype (MatrixModule.Block π hπ hlin)] in
theorem blockCharacter_blockOfLattice :
    MatrixModule.blockCharacter π hπ hlin (blockOfLattice K ψ hEnd hf π hπ hlin hnil)
      = reducedCentralCharacterAlg hf (centralCharacter K ψ hEnd) :=
  MatrixModule.blockCharacter_blockOfCentralCharacter π hπ hlin hnil _

set_option maxHeartbeats 1000000 in
-- Same instance chains as above.
set_option linter.unusedFintypeInType false in
omit [IsLocalRing 𝒪] [Fintype (MatrixModule.Block π hπ hlin)] in
/-- **The block character of `χ`'s block, evaluated on the reduction of a central element**, is
the reduction of `ω_χ` there.  This is the bridge that turns block membership into a statement
about `ω_χ`. -/
theorem blockCharacter_blockOfLattice_mapRingHom
    (z : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))
    {z' : Subalgebra.center F (MonoidAlgebra F G)}
    (hz : MonoidAlgebra.mapRingHom G f (z : MonoidAlgebra 𝒪 G) = (z' : MonoidAlgebra F G)) :
    MatrixModule.blockCharacter π hπ hlin (blockOfLattice K ψ hEnd hf π hπ hlin hnil) z'
      = f (centralScalar K ψ hEnd z) := by
  rw [blockCharacter_blockOfLattice, reducedCentralCharacterAlg_apply,
    reducedCentralCharacter_eq hf _ hz]
  rfl

variable [DecidableEq (MatrixModule.Block π hπ hlin)]
  {B : MatrixModule.Block π hπ hlin}
  {fB : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
  {fB' : Subalgebra.center F (MonoidAlgebra F G)}

set_option maxHeartbeats 1000000 in
-- Same instance chains as above.
set_option linter.unusedFintypeInType false in
omit [IsLocalRing 𝒪] [Fintype (MatrixModule.Block π hπ hlin)] in
/-- The value of `ω_χ` on a block idempotent, read off from block membership. -/
theorem reduce_centralScalar_blockIdempotent
    (hfB : MonoidAlgebra.mapRingHom G f (fB : MonoidAlgebra 𝒪 G) = (fB' : MonoidAlgebra F G))
    (hB : MatrixModule.blockCharacterPi π hπ hlin fB' = Pi.single B 1) :
    f (centralScalar K ψ hEnd fB)
      = if blockOfLattice K ψ hEnd hf π hπ hlin hnil = B then 1 else 0 := by
  rw [← blockCharacter_blockOfLattice_mapRingHom K ψ hEnd hf π hπ hlin hnil fB hfB,
    ← MatrixModule.blockCharacterPi_apply, hB, Pi.single_apply]

set_option maxHeartbeats 1000000 in
-- Same instance chains as above.
set_option linter.unusedFintypeInType false in
omit [Fintype (MatrixModule.Block π hπ hlin)] in
/-- **Navarro (3.13.a), the `χ ∉ B` half, in terms of block membership.** -/
theorem apply_eq_zero_of_blockOfLattice_ne
    (hker : RingHom.ker f = IsLocalRing.maximalIdeal 𝒪)
    (hidem : IsIdempotentElem fB)
    (hfB : MonoidAlgebra.mapRingHom G f (fB : MonoidAlgebra 𝒪 G) = (fB' : MonoidAlgebra F G))
    (hB : MatrixModule.blockCharacterPi π hπ hlin fB' = Pi.single B 1)
    (hne : blockOfLattice K ψ hEnd hf π hπ hlin hnil ≠ B) :
    ψ (fB : MonoidAlgebra 𝒪 G) = 0 :=
  apply_eq_zero_of_reduce_centralScalar_eq_zero K ψ hEnd f hker hidem
    (by rw [reduce_centralScalar_blockIdempotent K ψ hEnd hf π hπ hlin hnil hfB hB, if_neg hne])

set_option maxHeartbeats 1000000 in
-- Same instance chains as above.
set_option linter.unusedFintypeInType false in
omit [Fintype (MatrixModule.Block π hπ hlin)] in
/-- **Navarro (3.13.a), the `χ ∈ B` half, in terms of block membership.** -/
theorem apply_eq_id_of_blockOfLattice_eq
    (hker : RingHom.ker f = IsLocalRing.maximalIdeal 𝒪)
    (hidem : IsIdempotentElem fB)
    (hfB : MonoidAlgebra.mapRingHom G f (fB : MonoidAlgebra 𝒪 G) = (fB' : MonoidAlgebra F G))
    (hB : MatrixModule.blockCharacterPi π hπ hlin fB' = Pi.single B 1)
    (heq : blockOfLattice K ψ hEnd hf π hπ hlin hnil = B) :
    ψ (fB : MonoidAlgebra 𝒪 G) = LinearMap.id :=
  apply_eq_id_of_reduce_centralScalar_ne_zero K ψ hEnd f hker hidem
    (by rw [reduce_centralScalar_blockIdempotent K ψ hEnd hf π hπ hlin hnil hfB hB, if_pos heq]
        exact one_ne_zero)

end OddOrder.RepresentationTheory.Modular
