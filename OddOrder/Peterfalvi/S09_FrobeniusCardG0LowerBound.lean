/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusSelectedEstimate

/-!
# Frobenius-family lower bound (Peterfalvi 7.10)

This file assembles the concrete estimates proved for a Frobenius family into
`FrobeniusFamily.CharacterEstimateData`.  The Frobenius kernels are supplied as
nilpotent groups, exactly as required by the Sibley coherence theorem used in
Peterfalvi's proof.

Textbook: Peterfalvi, Section 7, pp. 42–43, equations (7.10)–(7.11).
Coq comparison: `PFsection7.v`, `CoherentFrobeniusPartition`.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

open scoped Classical in
/-- The character-estimate package in Peterfalvi (7.10), assembled from the
canonical coherent image at a member of minimal kernel order. -/
noncomputable def characterEstimateData_of_isNilpotent
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hnilp : ∀ j : Fin k,
      Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j))) :
    F.CharacterEstimateData := by
  let C : ∀ j : Fin k, Subgroup ↥(F.L j) :=
    fun j => Classical.choose (F.isFrobenius j)
  have hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j) :=
    fun j => Classical.choose_spec (F.isFrobenius j)
  let hminExists := F.exists_min_h_index
  let i : Fin k := Classical.choose hminExists
  have hmin : ∀ j : Fin k, F.h i ≤ F.h j :=
    Classical.choose_spec hminExists
  letI : Fintype ↥(F.L i) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L i) : ℂ) :=
    (F.familyHypothesis71).invertibleL i
  letI : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : ((F.H i).subgroupOf (F.L i)).Normal := (hFrob i).isNormal
  let H78 := F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)
  let chi := F.distinguishedNuAt hodd hnilp C hFrob i
  let B := F.reverseCoefficientZeroIndices hodd hnilp C hFrob i
  let hsig :=
    H78.exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet i hodd (hnilp i) (C i) (hFrob i))
      (F.hypothesis78_nu_eq i hodd (hnilp i) (C i) (hFrob i))
      (F.hypothesis78_zeta_irreducible i hodd (hnilp i) (C i) (hFrob i))
  let eps : ℤ := Classical.choose hsig
  let hsigXi := Classical.choose_spec hsig
  let xi : IrreducibleCharacter G := Classical.choose hsigXi
  have hsigned := Classical.choose_spec hsigXi
  have heps : eps = 1 ∨ eps = -1 := hsigned.1
  have hsigned := hsigned.2
  have hzetaDistinct : H78.zetaDistinct = 0 := rfl
  have hsignedZero :
      H78.nu (H78.hyp76.zeta 0) = eps • (xi : ClassFunction G ℂ) := by
    simpa only [hzetaDistinct, eps, xi] using hsigned
  have hchi_signed : chi = eps • (xi : ClassFunction G ℂ) := by
    change H78.nu (H78.hyp76.zeta 0) = eps • (xi : ClassFunction G ℂ)
    exact hsignedZero
  have hzero_ne : (0 : Fin (H78.hyp76.n + 1)) ≠ H78.ind1H := by
    rw [← hzetaDistinct]
    exact H78.zetaDistinct_ne_ind1H
  have hchi_norm : ClassFunction.inner chi chi = 1 := by
    change ClassFunction.inner (H78.nu (H78.hyp76.zeta 0))
      (H78.nu (H78.hyp76.zeta 0)) = 1
    exact F.hypothesis78_nu_zeta_norm_one_at
      i hodd (hnilp i) (C i) (hFrob i) hzero_ne
  have hL : ∀ j : Fin k, (F.familyHypothesis71).L j = F.L j :=
    fun _ => rfl
  have hA : ∀ j : Fin k,
      (F.familyHypothesis71).A j = ((F.H j : Set G) \ ({1} : Set G)) :=
    fun _ => rfl
  have hG0 : (F.familyHypothesis71).G0 = F.G0 := by
    ext g
    change (∀ j, g ∉ (F.hypothesis71 j).hyp.dadeSupport) ↔
      ∀ j, g ∉ F.kernelSpread j
    constructor
    · intro hg j hj
      exact hg j ((F.dadeSupport_hypothesis71_eq_kernelSpread j).symm ▸ hj)
    · intro hg j hj
      exact hg j (F.dadeSupport_hypothesis71_eq_kernelSpread j ▸ hj)
  exact F.characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible
    F.familyHypothesis71 chi hchi_norm hmin B eps xi heps hchi_signed hL hA hG0
    (F.reverseCoefficientZeroIndices_avoids hodd hnilp C hFrob i)
    (F.reverseCoefficientZeroIndices_Bsum_le hodd hnilp C hFrob i)
    (F.distinguishedNuAt_chiRhoNormSq_ge hodd hnilp C hFrob i)
    (F.reverseCoefficientZeroIndices_good_bound hodd hnilp C hFrob i)

end FrobeniusFamily

variable {G : Type*} [Group G]

/-- **Peterfalvi (7.10).** Under `FrobeniusFamily` with `G` of odd order and
nilpotent Frobenius kernels, there is an index `i` for which, writing
`e = e_i` and `h = h_i`,

`(|G₀| - 1)/|G| ≥ (e - 1) · ((h - 2e - 1)/(e·h) + 2/(h·(h+2)))`.

The explicit nilpotence input is the Sibley-coherence prerequisite.  In the FT
consumer it is constructed from `maxNilpotentNormalHall_isNilpotent`. -/
theorem card_G0_lower_bound [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hnilp : ∀ j : Fin k,
      Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j))) :
    ∃ i : Fin k,
      ((Nat.card F.G0 : ℚ) - 1) / (Nat.card G : ℚ) ≥
        ((F.e i : ℚ) - 1) *
          (((F.h i : ℚ) - 2 * (F.e i : ℚ) - 1) /
              ((F.e i : ℚ) * (F.h i : ℚ)) +
            2 / ((F.h i : ℚ) * ((F.h i : ℚ) + 2))) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact F.lowerBoundTerm_of_characterEstimateData hodd
    (F.characterEstimateData_of_isNilpotent hodd hnilp)

/-- **Peterfalvi (7.11).** No odd-order Frobenius family with nilpotent kernels
can have its conjugate kernel spreads cover every nonidentity element. -/
theorem not_trivial_G0 [Finite G] {k : ℕ}
    (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
    (hnilp : ∀ j : Fin k,
      Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
    (hG0 : F.G0 = {(1 : G)}) : False := by
  exact not_trivial_G0_of_lowerBoundTerm F hodd
    (card_G0_lower_bound F hodd hnilp) hG0

end OddOrder.Peterfalvi.S09
