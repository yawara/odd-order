/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockIdempotentLift
import OddOrder.GroupTheory.RepresentationTheory.Modular.CentralScalarBridge
import OddOrder.GroupTheory.RepresentationTheory.Modular.DecompositionBlockDiagonal
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularSumBlock
import OddOrder.GroupTheory.RepresentationTheory.Modular.PairingZeroBlock

/-!
# `ω_χ(Ĝ⁰) = 0` outside the principal block

Navarro's Lemma (3.32) says `Ĝ⁰ f_{B_0} = Ĝ⁰`, hence `λ_B(Ĝ⁰) = 0` for `B ≠ B_0`.  Written on the
ordinary side this is

`ω_χ(Ĝ⁰) · χ(1) = ∑_{g ∈ G⁰} χ(g) = 0`  for `χ ∉ Irr(B_0)`,

the first equality being `centralScalar_pRegularSum_mul_character_one` and the second Navarro
(3.20) (`sum_pRegular_trace_eq_zero_of_centralCharacterAlg_ne`) paired against the trivial
character.  Since `χ(1)` is a positive integer and `K` has characteristic zero, `ω_χ(Ĝ⁰) = 0`.

## Main results

* `OddOrder.RepresentationTheory.Modular.centralScalar_pRegularSum_eq_zero`
* `OddOrder.RepresentationTheory.Modular.blockCharacter_blockOfIrr_pRegularSum_eq_zero` —
  `λ_B(Ĝ⁰) = 0` for `B ≠ B_0`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [DecidableEq ι]
  [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  [Invertible (Nat.card G : K)]
variable {L' : Type*} [AddCommGroup L'] [Module 𝒪 L'] [Module.Free 𝒪 L'] [Module.Finite 𝒪 L']
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

set_option maxHeartbeats 800000 in
-- The character sum, its descent and the cancellation run under the same instance chains.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
include hp hω hω' hπ hlin hkerJ in
open scoped Classical in
/-- **`ω_χ(Ĝ⁰) = 0` for `χ` outside the block of the trivial character.**  This is Navarro (3.32)
on the ordinary side; reducing it gives `λ_B(Ĝ⁰) = 0` for `B ≠ B_0`. -/
theorem centralScalar_pRegularSum_eq_zero (i : ι') (σ : Representation 𝒪 G L')
    (hσ : ∀ g : G, LinearMap.trace 𝒪 L' (σ g) = 1)
    (hne : ∀ φ μ : ι,
      decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ ≠ 0 →
      decompositionNumber (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ σ μ ≠ 0 →
      MatrixModule.centralCharacterAlg π φ hπ hlin
        ≠ MatrixModule.centralCharacterAlg π μ hπ hlin) :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i (pRegularSum p K) = 0 := by
  classical
  -- the character sum over `G⁰` vanishes, first over `𝒪` and then over `K`
  have hzero := sum_pRegular_trace_eq_zero_of_centralCharacterAlg_ne hp hω hω' hπ hlin hkerJ e
    (K := K) (wedderburnLatticeRepresentation (𝒪 := 𝒪) e i) σ hσ hne
  have hsum : ∑ g ∈ Finset.univ.filter (fun g : G => IsPRegular p g),
      (wedderburnRepresentation e i).character g = 0 := by
    have := congrArg (algebraMap 𝒪 K) hzero
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun g _ => (algebraMap_ordinaryCharacter (𝒪 := 𝒪) e i g).symm
  -- `χ(1) ≠ 0`
  have hone : (wedderburnRepresentation e i).character 1 = (Fintype.card (m i) : K) := by
    rw [Representation.char_one, Module.finrank_fintype_fun_eq_card]
  have hone0 : (wedderburnRepresentation e i).character 1 ≠ 0 := by
    rw [hone]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine (mul_eq_zero.mp ?_).resolve_right hone0
  rw [centralScalar_pRegularSum_mul_character_one e i p, hsum]

set_option maxHeartbeats 1200000 in
-- The descent of `ω_χ(Ĝ⁰)` and the block character are elaborated under the same chains.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
include hp hω hω' hπ hlin hkerJ in
open scoped Classical in
/-- **Navarro (3.32): `λ_B(Ĝ⁰) = 0` for `B ≠ B_0`.**  The lattice central character of `Ĝ⁰`
vanishes for `χ` outside the trivial character's block, hence so does its reduction, which is the
block character. -/
theorem blockCharacter_blockOfIrr_pRegularSum_eq_zero (i : ι') (σ : Representation 𝒪 G L')
    (hσ : ∀ g : G, LinearMap.trace 𝒪 L' (σ g) = 1)
    (hne : ∀ φ μ : ι,
      decompositionMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e i φ ≠ 0 →
      decompositionNumber (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ σ μ ≠ 0 →
      MatrixModule.centralCharacterAlg π φ hπ hlin
        ≠ MatrixModule.centralCharacterAlg π μ hπ hlin) :
    MatrixModule.blockCharacter π hπ hlin (blockOfIrr e hπ hlin hnil i)
      ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩ = 0 := by
  classical
  -- the lattice central character of `Ĝ⁰` is zero, because its image in `K` is
  have hlat : centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
      (exists_smul_id_of_commute_wedderburnLattice e i)
      ⟨pRegularSum p 𝒪, pRegularSum_mem_center⟩ = 0 := by
    refine FaithfulSMul.algebraMap_injective 𝒪 K ?_
    rw [map_zero, algebraMap_centralScalar_eq e i ⟨pRegularSum p 𝒪, pRegularSum_mem_center⟩,
      mapRingHom_pRegularSum]
    exact centralScalar_pRegularSum_eq_zero hp hω hω' hπ hlin hkerJ e i σ hσ hne
  rw [blockOfIrr, blockCharacter_blockOfLattice_mapRingHom K _
    (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective π hπ hlin hnil
    ⟨pRegularSum p 𝒪, pRegularSum_mem_center⟩
    (z' := ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩)
    (mapRingHom_pRegularSum (residue 𝒪)), hlat, map_zero]

/-! ### `λ_B(Ĝ⁰) = 0` for an arbitrary block `B ≠ B_0`

`blockCharacter_blockOfIrr_pRegularSum_eq_zero` is stated for a block of the form `blockOfIrr e i`
and carries a separation hypothesis `hne`.  Both are now removable: `blockOfIrr` is surjective
(`exists_blockOfIrr_eq`), and `hne` *is* `B ≠ B_0`, because the group algebra acts on the trivial
representation through the augmentation (`asAlgebraHom_trivial`), so every Brauer constituent of
its reduction has central character `aug` and hence lies in `B_0`. -/

set_option maxHeartbeats 800000 in
-- The trivial lattice and its reduction are compared under the full modular-datum chain.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] [DecidableEq ι] in
include hp hω hω' hkerJ in
/-- **Every irreducible Brauer constituent of the trivial representation lies in `B_0`.** -/
theorem mk_eq_principalBlock_of_decompositionNumber_trivial {μ : ι}
    (hμ : decompositionNumber (nn := nn) hp hω hω' hπ hlin hkerJ
      (Representation.trivial 𝒪 G 𝒪) μ ≠ 0) :
    Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ = principalBlock π hπ hlin hnil := by
  refine mk_eq_principalBlock_of_centralCharacterAlg_eq π hπ hlin hnil μ (AlgHom.ext fun z => ?_)
  refine (centralCharacterAlg_eq_of_decompositionNumber_ne_zero hp hω hω' hπ hlin hkerJ
    (ρ := Representation.trivial 𝒪 G 𝒪) hμ
    (c := OddOrder.GroupTheory.CenterSimplesOrbit.aug z) ?_).symm
  have hred : reduction (Representation.trivial 𝒪 G 𝒪)
      = Representation.trivial (ResidueField 𝒪) G (TensorProduct 𝒪 (ResidueField 𝒪) 𝒪) := by
    refine MonoidHom.ext fun g => ?_
    rw [reduction_apply]
    exact LinearMap.baseChange_id
  rw [hred, asAlgebraHom_trivial]
  rfl

set_option maxHeartbeats 1600000 in
-- The block idempotent, the surjectivity of `blockOfIrr` and the vanishing lemma are all
-- elaborated under the full modular-datum chain.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
include hp hω hω' hkerJ e in
/-- **Navarro (3.32) for an arbitrary block**: `λ_B(Ĝ⁰) = 0` for every `B ≠ B_0`.

`blockOfIrr` is surjective (`exists_blockOfIrr_eq`, applied to the block idempotent of `B`), and
the separation hypothesis of `blockCharacter_blockOfIrr_pRegularSum_eq_zero` is exactly `B ≠ B_0`:
the Brauer constituents of the trivial representation all lie in `B_0`
(`mk_eq_principalBlock_of_decompositionNumber_trivial`). -/
theorem blockCharacter_pRegularSum_eq_zero_of_ne_principalBlock
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (B : MatrixModule.Block π hπ hlin) (hB : B ≠ principalBlock π hπ hlin hnil) :
    MatrixModule.blockCharacter π hπ hlin B
      ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩ = 0 := by
  classical
  obtain ⟨F, F', hidem, hf, hFB⟩ := exists_blockIdempotentFamily π hπ hlin hnil
  obtain ⟨i, hi⟩ := exists_blockOfIrr_eq e hπ hlin hnil B (hidem B) (hf B) (hFB B)
  rw [← hi]
  refine blockCharacter_blockOfIrr_pRegularSum_eq_zero hp hω hω' hπ hlin hkerJ hnil e i
    (Representation.trivial 𝒪 G 𝒪) (fun g => by rw [show Representation.trivial 𝒪 G 𝒪 g
        = LinearMap.id from rfl, LinearMap.trace_id, Module.finrank_self, Nat.cast_one])
    ?_
  intro φ μ hφ hμ heq
  refine hB ?_
  calc B = blockOfIrr e hπ hlin hnil i := hi.symm
    _ = Quotient.mk (MatrixModule.blockSetoid π hπ hlin) φ :=
        (blockOfIrr_eq_of_decompositionMatrix_ne_zero hp hω hω' hπ hlin hkerJ hnil e i hφ).symm
    _ = Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ := Quotient.sound heq
    _ = principalBlock π hπ hlin hnil :=
        mk_eq_principalBlock_of_decompositionNumber_trivial hp hω hω' hπ hlin hkerJ hnil hμ

end OddOrder.RepresentationTheory.Modular
