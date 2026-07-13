/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusBsumEstimate

/-!
# Frobenius-family good-index estimate (Peterfalvi 7.8.c, 7.10)

For a selected family member `i`, Peterfalvi divides the other indices into
those for which the reverse coefficient

`inner beta_j (nu_i zeta_i)`

vanishes and its complement.  On the complement, (7.8.c) and integrality of
the coefficient give the local lower bound

`(h_j - 1) / (e_j * h_j) <= normSq ((nu_i zeta_i) ^ rho_j)`.

The coherent image is only canonically a signed irreducible character.  The
proof therefore extracts its sign, applies the already proved irreducible
(7.8.c) estimate, and transports the rho norm back across the sign.

Textbook: Peterfalvi, Section 7, pp. 40-43, equations (7.8.c) and (7.10).
Coq comparison: `PFsection7.v`, proof of `CoherentFrobeniusPartition`.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

private theorem chiRhoCF_neg [Fintype G] {A : Set G} {L : Subgroup G}
    (H71 : Hypothesis71 G A L) (chi : ClassFunction G ℂ) :
    H71.chiRhoCF (-chi) = -H71.chiRhoCF chi := by
  classical
  ext a
  change H71.chiRho (-chi) a = -H71.chiRho chi a
  by_cases ha : (a : G) ∈ A
  · rw [H71.chiRho_of_mem _ ha, H71.chiRho_of_mem _ ha]
    simp only [ClassFunction.neg_apply, Finset.sum_neg_distrib]
    ring
  · rw [H71.chiRho_of_not_mem _ ha, H71.chiRho_of_not_mem _ ha, neg_zero]

section GoodIndex

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))
variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- **Peterfalvi (7.8.c), concrete good-index bound.**  If the reverse
coefficient of the `j`-th beta against the selected coherent image at `i` is
nonzero, then the `j`-th rho norm of that selected image is at least the local
sharp-kernel ratio. -/
theorem distinguishedNuAt_chiRhoNormSq_ge_of_reverseCoefficient_ne
    (i j : Fin k) (hij : i ≠ j)
    (hcoeff : ClassFunction.inner
      (F.betaAt hodd hnilp C hFrob j)
      (F.distinguishedNuAt hodd hnilp C hFrob i) ≠ 0) :
    ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) j := by
  classical
  letI : Fintype ↥(F.L i) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L i) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L i)).ne')
  letI : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : ((F.H i).subgroupOf (F.L i)).Normal := (hFrob i).isNormal
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
  let H78i := F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)
  let H78j := F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)
  obtain ⟨eps, xi, heps, hsigned⟩ :=
    H78i.exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet i hodd (hnilp i) (C i) (hFrob i))
      (F.hypothesis78_nu_eq i hodd (hnilp i) (C i) (hFrob i))
      (F.hypothesis78_zeta_irreducible i hodd (hnilp i) (C i) (hFrob i))
  have hzetaDistinct_i : H78i.zetaDistinct = 0 := rfl
  rw [hzetaDistinct_i] at hsigned
  have hsignedAt : F.distinguishedNuAt hodd hnilp C hFrob i =
      eps • (xi : ClassFunction G ℂ) := by
    simpa [distinguishedNuAt, H78i] using hsigned
  have hzero_ne_i : (0 : Fin (H78i.hyp76.n + 1)) ≠ H78i.ind1H := by
    rw [← hzetaDistinct_i]
    exact H78i.zetaDistinct_ne_ind1H
  have hcross : ∀ r : Fin (H78j.hyp76.n + 1), r ≠ H78j.ind1H →
      ClassFunction.inner
        (F.distinguishedNuAt hodd hnilp C hFrob i)
        (H78j.nu (H78j.hyp76.zeta r)) = 0 := by
    intro r hr
    simpa [distinguishedNuAt, H78i, H78j] using
      (F.hypothesis79_zeta_cross_eq_zero_at
        hodd (hnilp i) (C i) (hFrob i) (hnilp j) (C j) (hFrob j)
        hij hzero_ne_i hr)
  have hdiffZ :
      H78j.hyp76.zeta H78j.ind1H - H78j.hyp76.zeta H78j.zetaDistinct ∈
        ZIrr ↥(F.L j) :=
    H78j.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (F.hypothesis78_ind1H_mem_ZIrr j hodd (hnilp j) (C j) (hFrob j))
      (F.hypothesis78_zeta_irreducible j hodd (hnilp j) (C j) (hFrob j))
  have hcoeff' : ClassFunction.inner H78j.beta
      (F.distinguishedNuAt hodd hnilp C hFrob i) ≠ 0 := by
    simpa [betaAt, H78j] using hcoeff
  have hratio :
      (Nat.card (OddOrder.Peterfalvi.S08.sharpImage
          ((F.H j).subgroupOf (F.L j))) : ℝ) /
          (Nat.card ↥(F.L j) : ℝ) =
        ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) := by
    rw [F.sharpImage_subgroupOf_eq j]
    exact F.card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h_real j
  rcases heps with rfl | rfl
  · have hsignedOne : F.distinguishedNuAt hodd hnilp C hFrob i =
        (xi : ClassFunction G ℂ) := by simpa using hsignedAt
    have horthXi : ∀ r : Fin (H78j.hyp76.n + 1), r ≠ H78j.ind1H →
        ClassFunction.inner (xi : ClassFunction G ℂ)
          (H78j.nu (H78j.hyp76.zeta r)) = 0 := by
      intro r hr
      simpa [hsignedOne] using hcross r hr
    have hcoeffXi : ClassFunction.inner H78j.beta
        (xi : ClassFunction G ℂ) ≠ 0 := by
      simpa [hsignedOne] using hcoeff'
    have hbound := chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero
      H78j (xi : ClassFunction G ℂ) xi.property horthXi hdiffZ hcoeffXi
    change (Nat.card (OddOrder.Peterfalvi.S08.sharpImage
        ((F.H j).subgroupOf (F.L j))) : ℝ) / (Nat.card ↥(F.L j) : ℝ) ≤
      (ClassFunction.inner
        ((F.sibleyToHypothesis71 j hodd (hnilp j) (C j) (hFrob j)).chiRhoCF
          (xi : ClassFunction G ℂ))
        ((F.sibleyToHypothesis71 j hodd (hnilp j) (C j) (hFrob j)).chiRhoCF
          (xi : ClassFunction G ℂ))).re at hbound
    rw [F.sibleyToHypothesis71_chiRhoCF_eq] at hbound
    change ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
      (ClassFunction.inner
        ((F.hypothesis71 j).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i))
        ((F.hypothesis71 j).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i))).re
    rw [hsignedOne]
    rw [← hratio]
    exact hbound
  · have hsignedNeg : F.distinguishedNuAt hodd hnilp C hFrob i =
        -(xi : ClassFunction G ℂ) := by simpa using hsignedAt
    have horthXi : ∀ r : Fin (H78j.hyp76.n + 1), r ≠ H78j.ind1H →
        ClassFunction.inner (xi : ClassFunction G ℂ)
          (H78j.nu (H78j.hyp76.zeta r)) = 0 := by
      intro r hr
      have hz := hcross r hr
      rw [hsignedNeg, ClassFunction.inner_neg_left, neg_eq_zero] at hz
      exact hz
    have hcoeffXi : ClassFunction.inner H78j.beta
        (xi : ClassFunction G ℂ) ≠ 0 := by
      intro hz
      apply hcoeff'
      rw [hsignedNeg, ClassFunction.inner_neg_right, hz, neg_zero]
    have hbound := chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero
      H78j (xi : ClassFunction G ℂ) xi.property horthXi hdiffZ hcoeffXi
    change (Nat.card (OddOrder.Peterfalvi.S08.sharpImage
        ((F.H j).subgroupOf (F.L j))) : ℝ) / (Nat.card ↥(F.L j) : ℝ) ≤
      (ClassFunction.inner
        ((F.sibleyToHypothesis71 j hodd (hnilp j) (C j) (hFrob j)).chiRhoCF
          (xi : ClassFunction G ℂ))
        ((F.sibleyToHypothesis71 j hodd (hnilp j) (C j) (hFrob j)).chiRhoCF
          (xi : ClassFunction G ℂ))).re at hbound
    rw [F.sibleyToHypothesis71_chiRhoCF_eq] at hbound
    change ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
      (ClassFunction.inner
        ((F.hypothesis71 j).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i))
        ((F.hypothesis71 j).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i))).re
    rw [hsignedNeg, chiRhoCF_neg, ClassFunction.inner_neg_left,
      ClassFunction.inner_neg_right, neg_neg]
    rw [← hratio]
    exact hbound

/-- Consumer form for Peterfalvi's complement of `B`: an index distinct from
the selected member and not in the vanishing-coefficient set satisfies the
(7.8.c) good-index lower bound. -/
theorem reverseCoefficientZeroIndices_good_bound (i j : Fin k)
    (hij : i ≠ j)
    (hjB : j ∉ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i) :
    ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) j := by
  apply F.distinguishedNuAt_chiRhoNormSq_ge_of_reverseCoefficient_ne
    hodd hnilp C hFrob i j hij
  intro hzero
  apply hjB
  exact (F.mem_reverseCoefficientZeroIndices_iff
    hodd hnilp C hFrob i j).2 ⟨hij, hzero⟩

end GoodIndex

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
