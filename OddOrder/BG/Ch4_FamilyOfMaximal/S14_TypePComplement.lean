/-
Copyright (c) 2026 OddOrder contributors. All rights reserved.
-/
import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting
import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF
import OddOrder.GroupTheory.AInvariantComplement

/-!
# Peterfalvi (13.1.b): the κ-Hall-invariant complement `U` to `M_F` in `M'`

For a type-`P` maximal subgroup `M` with cyclic κ-Hall `K`, the derived subgroup `M' = [M,M]`
factors as `M' = M_F U` with a complement `U` *that `K` normalizes* — Peterfalvi's "`W₁`
normalizes `U`, which is possible by the remark following Definition (8.4)".  This is exactly the
invariant Schur–Zassenhaus complement
(`OddOrder.GroupTheory.exists_aInvariant_complement_within_normal`):
`K` acts coprimely on the solvable `M'` (it complements `M'` in `M`, so `|K|` is coprime to
`|M'| = [M : K]`), and `M_F` is a `K`-invariant normal Hall subgroup of `M'`.

This discharges the U-side of the `Section16TypePStructure` producer (issue 7005 piece 2).
-/

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch4.S15

variable {G : Type*} [Group G] [Finite G]

/-- **Peterfalvi (13.1.b), the semidirect factor `U` with `K ≤ N_G(U)`.**  The derived subgroup of a
type-`P` maximal subgroup `M` is `M' = M_F U` for a complement `U` normalised by the (cyclic) κ-Hall
`K`. -/
theorem exists_kappaHall_invariant_complement_to_MF (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    ∃ U : Subgroup G, derivedInG M = maxNilpotentNormalHall M ⊔ U ∧
      K ≤ Subgroup.normalizer (U : Set G) ∧ maxNilpotentNormalHall M ⊓ U = ⊥ := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  -- `M' ≤ M` is solvable.
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  haveI : IsSolvable ↥(derivedInG M) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hM'le)
  -- `M_F ≤ M' ≤ M`.
  have hMFle' : maxNilpotentNormalHall M ≤ derivedInG M := maxNilpotentNormalHall_le_derived hG hM
  have hMFleM : maxNilpotentNormalHall M ≤ M := maxNilpotentNormalHall_le M
  -- `M` normalises both `M_F` and `M'`.
  have hM_norm_MF : M ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (maxNilpotentNormalHall_subgroupOf_normal M)
  have hM'_subgroupOf_normal : ((derivedInG M).subgroupOf M).Normal := by
    rw [show (derivedInG M).subgroupOf M = commutator ↥M by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
    infer_instance
  have hM_norm_M' : M ≤ Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM'le).mp hM'_subgroupOf_normal
  -- Inputs to the ambient invariant complement.
  have hM'_norm_MF : derivedInG M ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    hM'le.trans hM_norm_MF
  have hK_norm_M' : K ≤ Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) :=
    hKM.trans hM_norm_M'
  have hK_norm_MF : K ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    hKM.trans hM_norm_MF
  -- `M_F` is a Hall subgroup of `M'` (restrict from Hall in `M`: the relative index divides
  -- `[M:M_F]`).
  have hMF_hallM := maxNilpotentNormalHall_isHall M
  have hMF_hall' : Ch03.IsHallSubgroup (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors
      ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)) := by
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMFle').toEquiv] at hr
    · refine hMF_hallM.2 r ?_
      rw [Nat.mem_primeFactors] at hr ⊢
      refine ⟨hr.1, hr.2.1.trans ?_, Subgroup.index_ne_zero_of_finite⟩
      exact ⟨(derivedInG M).relIndex M,
        (Subgroup.relIndex_mul_relIndex (maxNilpotentNormalHall M) (derivedInG M) M
          hMFle' hM'le).symm⟩
  -- `|K|` is coprime to `|M'|`: `K` complements `M'` in `M`, so `[M : K] = |M'|`.
  have hcompl := typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  have hidx : (K.subgroupOf M).index = Nat.card ↥(derivedInG M) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have hco := hK.coprime_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hidx] at hco
  -- Invariant Schur–Zassenhaus.
  obtain ⟨U, -, hUsup, hUnorm, hUinf⟩ :=
    OddOrder.GroupTheory.exists_aInvariant_complement_within_normal hMFle' hM'_norm_MF
      hK_norm_M' hK_norm_MF hMF_hall' hCop
  exact ⟨U, hUsup.symm, hUnorm, hUinf⟩

end OddOrder.BG.Ch4.S14
