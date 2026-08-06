/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockIdempotentOrdinary
import OddOrder.GroupTheory.RepresentationTheory.Modular.OsimaLinkedIntegral

/-!
# Navarro (3.9): `Irr(B)` is a single connected component of the Brauer graph

`blockOfIrr i` is by definition the block whose central character is the reduction of `ω_{χ_i}` —
Navarro's `λ_χ`.  So the assertion "`Irr(B)` is a *single* connected component" is:

> a set `A ⊆ Irr(G)` closed under linking is a union of fibres of `blockOfIrr`.

The proof is Navarro's.  Osima's (3.8) (`exists_center_mapRingHom_eq_sum_ordinaryIdempotent`)
puts `f_A = ∑_{χ ∈ A} e_χ` inside `Z(𝒪G)`; its `K`-central character at `χ_k` is `1` for `k ∈ A`
and `0` otherwise (first orthogonality), hence so is its `𝒪`-central character, and reducing gives
`λ_{χ_k}(f_A) = 1` exactly for `k ∈ A`.  Two characters in the same block have the same `λ`, so
they are both in `A` or both out — otherwise `1 = 0` in the residue field.

Together with the easy direction (`centralCharacterAlg_eq_of_decompositionMatrix_ne_zero`: linked
characters lie in the same block) this is Navarro (3.9), and its corollary (3.10) is Problem (3.4):
the decomposition matrix of a block is not `(* 0; 0 *)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.mem_of_blockOfIrr_eq_of_linkedClosed`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (3.8), (3.9), (3.10).
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)] [Invertible (Nat.card G : K)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)

set_option maxHeartbeats 800000 in
-- The (3.8) idempotent and the two central-character bridges are elaborated together.
set_option linter.unusedFintypeInType false in
open scoped Classical in
include hp hω hω' hkerJ in
/-- **Navarro (3.9)**: a linking-closed set of ordinary characters is a union of blocks.

If `χ_i ∈ A` and `χ_j` lies in the same block as `χ_i`, then `χ_j ∈ A`: the reduced central
character of Osima's idempotent `f_A` is `1` at `χ_i` and would be `0` at `χ_j`, but it only
depends on the block. -/
theorem mem_of_blockOfIrr_eq_of_linkedClosed [Fact p.Prime] {Q : ι' → Prop}
    (hQ : ∀ (a b : ι') (ψ : ι), Q a →
      decompositionMatrix hp hω hω' hπ hlin hkerJ e a ψ ≠ 0 →
      decompositionMatrix hp hω hω' hπ hlin hkerJ e b ψ ≠ 0 → Q b)
    {i j : ι'} (hi : Q i)
    (hij : blockOfIrr e hπ hlin hnil i = blockOfIrr e hπ hlin hnil j) : Q j := by
  classical
  by_contra hj
  obtain ⟨f, hf⟩ :=
    exists_center_mapRingHom_eq_sum_ordinaryIdempotent hp hω hω' hπ hlin hkerJ e hQ
  -- the `K`-central character of `f_A` at `χ_k` is `1` exactly on `A`
  have hK : ∀ k : ι', MatrixModule.centralScalar e.toAlgHom.toRingHom k
        (MonoidAlgebra.mapRingHom G (algebraMap 𝒪 K) (f : MonoidAlgebra 𝒪 G))
      = if Q k then 1 else 0 := by
    intro k
    rw [hf, MatrixModule.centralScalar_finsetSum,
      Finset.sum_congr rfl fun l _ => centralScalar_ordinaryIdempotent e l k,
      Finset.sum_ite_eq' (Finset.univ.filter Q) k (fun _ => (1 : K))]
    by_cases hk : Q k
    · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩), if_pos hk]
    · rw [if_neg fun hc => hk (Finset.mem_filter.mp hc).2, if_neg hk]
  -- hence so is the `𝒪`-central character
  have h𝒪 : ∀ k : ι', centralScalar K
        ((wedderburnLatticeRepresentation (𝒪 := 𝒪) e k).asAlgebraHom)
        (exists_smul_id_of_commute_wedderburnLattice e k) f = if Q k then 1 else 0 := by
    intro k
    refine FaithfulSMul.algebraMap_injective 𝒪 K ?_
    rw [algebraMap_centralScalar_eq e k f, hK k]
    by_cases hk : Q k
    · rw [if_pos hk, if_pos hk, map_one]
    · rw [if_neg hk, if_neg hk, map_zero]
  -- and its reduction is the block character, which only depends on the block
  have hres : ∀ k : ι', MatrixModule.blockCharacter π hπ hlin (blockOfIrr e hπ hlin hnil k)
        ⟨MonoidAlgebra.mapRingHom G (residue 𝒪) (f : MonoidAlgebra 𝒪 G),
          OddOrder.mapRingHom_mem_center (residue 𝒪) f.2⟩
      = residue 𝒪 (if Q k then 1 else 0) := by
    intro k
    rw [← h𝒪 k]
    exact blockCharacter_blockOfLattice_mapRingHom K _
      (exists_smul_id_of_commute_wedderburnLattice e k) residue_surjective π hπ hlin hnil f rfl
  have hcontra : residue 𝒪 (if Q i then (1 : 𝒪) else 0)
      = residue 𝒪 (if Q j then (1 : 𝒪) else 0) := by
    rw [← hres i, ← hres j, hij]
  rw [if_pos hi, if_neg hj, map_one, map_zero] at hcontra
  exact one_ne_zero hcontra

end OddOrder.RepresentationTheory.Modular
