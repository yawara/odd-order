/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CentralScalarBridge
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryIdempotent

/-!
# A block idempotent is the sum of the ordinary idempotents in its block

If `f ∈ Z(𝒪G)` is an idempotent lifting the block idempotent `e_B ∈ Z(kG)`
(`BlockIdempotentLift.exists_isIdempotentElem_blockCharacterPi_eq_single`), then its image in
`K[G]` is

`∑_{χ ∈ Irr(B)} e_χ`.

The argument is three lines once the machinery is in place:

* `ω^K_i(f)` is an idempotent of the field `K`, so it is `0` or `1`;
* it equals `algebraMap 𝒪 K (ω^L_i(f))` (`algebraMap_centralScalar_eq`), and the reduction of
  `ω^L_i(f)` is the block character of `B` at `e_B`, i.e. `1` exactly when `χ_i ∈ Irr(B)`
  (`blockCharacter_blockOfLattice_mapRingHom`);
* the spectral decomposition of `Z(K[G])` then assembles `f` from the surviving `e_χ`.

This identifies the class-sum coefficients `a_B(K̂)` that Navarro (4.19) regroups block by block:
they are the reductions of `∑_{χ ∈ Irr(B)} (χ(1)/|G|) χ(x_K⁻¹)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.mapRingHom_blockIdempotent_eq_sum`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra MatrixModule

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

set_option maxHeartbeats 1200000 in
-- The two central characters and the block machinery are all in play.
open scoped Classical in
/-- **A lift of the block idempotent `e_B` maps to `∑_{χ ∈ Irr(B)} e_χ` in `K[G]`.** -/
theorem mapRingHom_blockIdempotent_eq_sum [DecidableEq (Block πG hπG hlinG)]
    {B : Block πG hπG hlinG} {f : Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    (hidem : IsIdempotentElem f)
    {f' : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hf : MonoidAlgebra.mapRingHom G (residue 𝒪) (f : MonoidAlgebra 𝒪 G)
      = (f' : MonoidAlgebra (ResidueField 𝒪) G))
    (hB : blockCharacterPi πG hπG hlinG f' = Pi.single B 1) :
    MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (f : MonoidAlgebra 𝒪 G)
      = ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        ordinaryIdempotent e i := by
  classical
  set fK : MonoidAlgebra K G :=
    MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (f : MonoidAlgebra 𝒪 G) with hfK
  have hfKcentral : fK ∈ Subalgebra.center K (MonoidAlgebra K G) :=
    OddOrder.mapRingHom_mem_center (algebraMap 𝒪 K) f.2
  -- `ω^K_i(f)` is `0` or `1`
  have hsq : ∀ i : ι', MatrixModule.centralScalar e.toAlgHom.toRingHom i fK
      * MatrixModule.centralScalar e.toAlgHom.toRingHom i fK
      = MatrixModule.centralScalar e.toAlgHom.toRingHom i fK := by
    intro i
    rw [← centralScalar_mul e i hfKcentral hfKcentral]
    congr 1
    rw [hfK, ← map_mul]
    exact congrArg _ (congrArg Subtype.val hidem)
  -- and it is `1` exactly on `Irr(B)`
  have hval : ∀ i : ι', MatrixModule.centralScalar e.toAlgHom.toRingHom i fK
      = if blockOfIrr e hπG hlinG hnilG i = B then 1 else 0 := by
    intro i
    have hbridge : MatrixModule.centralScalar e.toAlgHom.toRingHom i fK
        = algebraMap 𝒪 K (centralScalar K
          ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
          (exists_smul_id_of_commute_wedderburnLattice e i) f) :=
      (algebraMap_centralScalar_eq e i f).symm
    have hres : residue 𝒪 (centralScalar K
        ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e i) f)
        = if blockOfIrr e hπG hlinG hnilG i = B then 1 else 0 := by
      rw [← blockCharacter_blockOfLattice_mapRingHom K _
        (exists_smul_id_of_commute_wedderburnLattice e i) residue_surjective πG hπG hlinG hnilG
        f hf, ← MatrixModule.blockCharacterPi_apply, hB, Pi.single_apply]
      rfl
    have hzero_or : MatrixModule.centralScalar e.toAlgHom.toRingHom i fK = 0
        ∨ MatrixModule.centralScalar e.toAlgHom.toRingHom i fK = 1 := by
      have hz : MatrixModule.centralScalar e.toAlgHom.toRingHom i fK
          * (MatrixModule.centralScalar e.toAlgHom.toRingHom i fK - 1) = 0 := by
        linear_combination hsq i
      rcases mul_eq_zero.mp hz with h | h
      · exact Or.inl h
      · exact Or.inr (by linear_combination h)
    by_cases hiB : blockOfIrr e hπG hlinG hnilG i = B
    · rw [if_pos hiB]
      rw [if_pos hiB] at hres
      rcases hzero_or with h0 | h1
      · exfalso
        have hz0 : centralScalar K
            ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
            (exists_smul_id_of_commute_wedderburnLattice e i) f = 0 :=
          FaithfulSMul.algebraMap_injective 𝒪 K (by rw [map_zero, ← hbridge, h0])
        rw [hz0, map_zero] at hres
        exact one_ne_zero hres.symm
      · exact h1
    · rw [if_neg hiB]
      rw [if_neg hiB] at hres
      rcases hzero_or with h0 | h1
      · exact h0
      · exfalso
        have hone : centralScalar K ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e i).asAlgebraHom)
            (exists_smul_id_of_commute_wedderburnLattice e i) f = 1 :=
          (FaithfulSMul.algebraMap_injective 𝒪 K) (by rw [map_one, ← hbridge, h1])
        rw [hone, map_one] at hres
        exact one_ne_zero hres
  -- assemble by the spectral decomposition
  rw [eq_sum_centralScalar_smul_ordinaryIdempotent e fK hfKcentral]
  have hsplit : ∀ i : ι',
      MatrixModule.centralScalar e.toAlgHom.toRingHom i fK • ordinaryIdempotent e i
        = if blockOfIrr e hπG hlinG hnilG i = B then ordinaryIdempotent e i else 0 := by
    intro i
    rw [hval i]
    by_cases hiB : blockOfIrr e hπG hlinG hnilG i = B
    · rw [if_pos hiB, if_pos hiB, one_smul]
    · rw [if_neg hiB, if_neg hiB, zero_smul]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hsplit i]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

end OddOrder.RepresentationTheory.Modular
