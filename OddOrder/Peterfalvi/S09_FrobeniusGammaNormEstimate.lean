/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusGammaDecomposition

/-!
# Frobenius-family Gamma norm estimate (Peterfalvi 7.8.b)

This file evaluates the norm of the concrete residual `Gamma` attached to a
Frobenius-family member.  The source norm of `Ind 1_H - zeta` gives
`‖beta‖² = e + 1`; the already evaluated weighted coherent sum then gives the
orthogonal expansion of `‖beta‖²`.  Peterfalvi's quadratic argument finally
yields `‖Gamma‖² ≤ e - 1`.

Textbook: Peterfalvi, Section 7, pp. 40-42, equation (7.8.b).
Coq comparison: `PFsection7.v`, `coherent_norm_1` and the proof of
`CoherentFrobeniusPartition`.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalGammaNorm

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
variable [((F.H i).subgroupOf (F.L i)).Normal]
variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
variable (C : Subgroup ↥(F.L i))
variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

private noncomputable abbrev localH78 :=
  F.hypothesis78 i hodd hnilp C hFrob

private noncomputable abbrev localBD :=
  F.hypothesis78_betaDecomp i hodd hnilp C hFrob

/-- The induced principal member has norm square equal to the Frobenius
complement index.  This is the first source inner product in (7.8.b). -/
theorem hypothesis78_ind1H_inner_self_eq_complementIndex :
    ClassFunction.inner
      ((localH78 F i hodd hnilp C hFrob).hyp76.zeta
        (localH78 F i hodd hnilp C hFrob).ind1H)
      ((localH78 F i hodd hnilp C hFrob).hyp76.zeta
        (localH78 F i hodd hnilp C hFrob).ind1H) =
      ((localH78 F i hodd hnilp C hFrob).complementIndex : ℂ) := by
  classical
  let H78 := localH78 F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hz_ind : H78.hyp76.zeta H78.ind1H =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (trivialIrreducibleCharacter
          ↥((F.H i).subgroupOf (F.L i)) : ClassFunction _ ℂ) := by
    rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) H78.ind1H,
      show H78.ind1H = pf.ind1H from rfl, pf.triv]
  rw [Cert.complementIndex_eq_subgroupOf_index H78]
  change ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
      (H78.hyp76.zeta H78.ind1H) =
    (((F.H i).subgroupOf (F.L i)).index : ℂ)
  rw [hz_ind]
  exact Cert.induce_trivialChar_normSq_eq_index
    ((F.H i).subgroupOf (F.L i))

/-- The distinguished non-principal induced character is orthogonal to the
induced principal member.  This is the cross term in the source norm of
`Ind 1_H - zeta`. -/
theorem hypothesis78_zetaDistinct_inner_ind1H_eq_zero :
    ClassFunction.inner
      ((localH78 F i hodd hnilp C hFrob).hyp76.zeta
        (localH78 F i hodd hnilp C hFrob).zetaDistinct)
      ((localH78 F i hodd hnilp C hFrob).hyp76.zeta
        (localH78 F i hodd hnilp C hFrob).ind1H) = 0 := by
  classical
  let H78 := localH78 F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  rw [show H78.zetaDistinct = 0 from rfl,
    congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0,
    congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) H78.ind1H,
    show H78.ind1H = pf.ind1H from rfl]
  exact Cert.induce_family_orthogonal_of_injective
    ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj 0 pf.ind1H
      (Ne.symm pf.ind1H_ne_zero)

/-- The source norm computation in (7.8.b), transported through the Dade
isometry: the concrete `beta` has norm square `e + 1`. -/
theorem hypothesis78_betaNormSq_eq_complementIndex_add_one :
    (localH78 F i hodd hnilp C hFrob).betaNormSq =
      ((localH78 F i hodd hnilp C hFrob).complementIndex : ℝ) + 1 := by
  let H78 := localH78 F i hodd hnilp C hFrob
  exact H78.betaNormSq_eq_complementIndex_add_one_of_zeta_ind_orthogonal_of_zeta_irreducible
    (F.hypothesis78_ind1H_inner_self_eq_complementIndex i hodd hnilp C hFrob)
    (F.hypothesis78_zetaDistinct_inner_ind1H_eq_zero i hodd hnilp C hFrob)
    (F.hypothesis78_zeta_irreducible i hodd hnilp C hFrob)

/-- The concrete beta decomposition has Peterfalvi's orthogonal norm
expansion.  The weighted-sum norm was evaluated by the induced-family degree
sum in `hypothesis78_weightedNuSum_inner_self_eq`. -/
theorem hypothesis78_betaNormSq_eq_orthogonal_expand :
    (localH78 F i hodd hnilp C hFrob).betaNormSq =
      2 +
        ((((localH78 F i hodd hnilp C hFrob).kernelOrder : ℝ) - 1) /
          ((localH78 F i hodd hnilp C hFrob).complementIndex : ℝ)) *
          ((localBD F i hodd hnilp C hFrob).a : ℝ) ^ 2 -
        2 * ((localBD F i hodd hnilp C hFrob).a : ℝ) +
          (localH78 F i hodd hnilp C hFrob).gammaNormSq
            (localBD F i hodd hnilp C hFrob) := by
  let H78 := localH78 F i hodd hnilp C hFrob
  let hBD := localBD F i hodd hnilp C hFrob
  letI : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  have hzeta_norm :
      ClassFunction.inner
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
    F.hypothesis78_nu_zeta_norm_one_at i hodd hnilp C hFrob
      H78.zetaDistinct_ne_ind1H
  have hweighted_zeta :
      ClassFunction.inner H78.weightedNuSum
        (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 := by
    have h := F.hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
      i hodd hnilp C hFrob (r := H78.zetaDistinct)
        H78.zetaDistinct_ne_ind1H
    rw [show H78.zetaDistinct = 0 from rfl,
      F.hypothesis78_d_zero_eq_one i hodd hnilp C hFrob] at h
    exact h
  have hweighted_norm :
      ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
        ((((H78.kernelOrder : ℝ) - 1) /
          (H78.complementIndex : ℝ)) : ℂ) := by
    have h := F.hypothesis78_weightedNuSum_inner_self_eq
      i hodd hnilp C hFrob
    have hh : H78.kernelOrder = F.h i := rfl
    have he : H78.complementIndex = F.e i := rfl
    rw [hh, he]
    convert h using 1
    all_goals norm_num
  exact H78.betaNormSq_eq_of_weightedNuSum_norm hBD
    hzeta_norm hweighted_zeta hweighted_norm

/-- Exact residual norm formula underlying the upper bound in (7.8.b). -/
theorem hypothesis78_gammaNormSq_eq :
    (localH78 F i hodd hnilp C hFrob).gammaNormSq
        (localBD F i hodd hnilp C hFrob) =
      ((localH78 F i hodd hnilp C hFrob).complementIndex : ℝ) - 1 -
        ((localH78 F i hodd hnilp C hFrob).kernelOrder : ℝ) *
          (localH78 F i hodd hnilp C hFrob).normQuadraticCorrection
            (localBD F i hodd hnilp C hFrob) := by
  let H78 := localH78 F i hodd hnilp C hFrob
  let hBD := localBD F i hodd hnilp C hFrob
  exact H78.gammaNormSq_eq_of_betaNormSq_expand hBD
    (F.hypothesis78_betaNormSq_eq_complementIndex_add_one
      i hodd hnilp C hFrob)
    (F.hypothesis78_betaNormSq_eq_orthogonal_expand
      i hodd hnilp C hFrob)

omit [((F.H i).subgroupOf (F.L i)).Normal] in
/-- Odd-order Frobenius cardinalities give the small-index inequality
`2e + 1 ≤ h` used in (7.8.b). -/
theorem hypothesis78_smallIndex_at :
    (localH78 F i hodd hnilp C hFrob).smallIndex := by
  let H78 := localH78 F i hodd hnilp C hFrob
  have hoddL : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  have hKodd : Odd (Nat.card ↥((F.H i).subgroupOf (F.L i))) :=
    hoddL.of_dvd_nat
      (Subgroup.card_subgroup_dvd_card ((F.H i).subgroupOf (F.L i)))
  have hCodd : Odd (Nat.card ↥C) :=
    hoddL.of_dvd_nat (Subgroup.card_subgroup_dvd_card C)
  have hcompl :
      Nat.card ↥((F.H i).subgroupOf (F.L i)) * Nat.card ↥C =
        Nat.card ↥(F.L i) :=
    hFrob.isComplement.card_mul_card
  have hKcard : Nat.card ↥((F.H i).subgroupOf (F.L i)) =
      Nat.card ↥(F.H i) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv
  have hfrob := hFrob.two_mul_card_complement_add_one_le_card_kernel
    hKodd hCodd hFrob.ne_bot_kernel
  change 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
  have hke : H78.kernelOrder =
      Nat.card ↥((F.H i).subgroupOf (F.L i)) := by
    change Nat.card ↥(F.H i) =
      Nat.card ↥((F.H i).subgroupOf (F.L i))
    exact hKcard.symm
  have hce : H78.complementIndex = Nat.card ↥C := by
    change Nat.card ↥(F.L i) / Nat.card ↥(F.H i) = Nat.card ↥C
    rw [← hKcard, ← hcompl, Nat.mul_div_cancel_left _ Nat.card_pos]
  rw [hke, hce]
  exact hfrob

/-- **Peterfalvi (7.8.b), concrete residual bound.**  The Gamma term in the
canonical beta decomposition of the `i`-th Frobenius member satisfies
`‖Gamma_i‖² ≤ e_i - 1`. -/
theorem hypothesis78_gamma_inner_self_re_le :
    (ClassFunction.inner
      (localBD F i hodd hnilp C hFrob).Gamma
      (localBD F i hodd hnilp C hFrob).Gamma).re ≤
        (F.e i : ℝ) - 1 := by
  let H78 := localH78 F i hodd hnilp C hFrob
  let hBD := localBD F i hodd hnilp C hFrob
  have hlocal := H78.gammaNormSq_le_of_normQuadraticCorrection_eq hBD
    (F.hypothesis78_gammaNormSq_eq i hodd hnilp C hFrob)
    (F.hypothesis78_smallIndex_at i hodd hnilp C hFrob)
  have he : H78.complementIndex = F.e i := rfl
  change H78.gammaNormSq hBD ≤ (F.e i : ℝ) - 1
  simpa [he] using hlocal

end LocalGammaNorm

section FamilyGammaNorm

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))
variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- Family-wide form of the concrete (7.8.b) residual bound. -/
theorem gammaAt_inner_self_re_le (i : Fin k) :
    (ClassFunction.inner
      (F.gammaAt hodd hnilp C hFrob i)
      (F.gammaAt hodd hnilp C hFrob i)).re ≤
        (F.e i : ℝ) - 1 := by
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
  simpa only [gammaAt] using
    (F.hypothesis78_gamma_inner_self_re_le
      i hodd (hnilp i) (C i) (hFrob i))

end FamilyGammaNorm

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
