/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusGoodIndexEstimate

/-!
# Frobenius-family selected-character estimate (Peterfalvi 7.8.b)

This file proves the lower norm estimate for the canonical distinguished
coherent image of every member of a Frobenius family.  Unlike the earlier
existential form, the character here is exactly `distinguishedNuAt`; this is
the character whose reverse coefficients define the set `B` in (7.10).

The proof applies the abstract (7.8.b) identity to the canonical induced
family, using the proved beta decomposition, induced-family orthogonality,
coherence coefficient formulas, the degree sum (1.5.d), and the odd-order
Frobenius small-index inequality.

Textbook: Peterfalvi, Section 7, pp. 40-43, equations (7.8.b) and (7.10).
Coq comparison: `PFsection7.v`, proof of `CoherentFrobeniusPartition`.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalSelectedEstimate

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

/-- **Peterfalvi (7.8.b), canonical local form.**  The distinguished coherent
image in the canonical `Hypothesis78` attached to a Frobenius-family member
satisfies `1 - e/h <= normSq (zeta_0^(nu rho))`. -/
theorem hypothesis78_zetaNuRhoNormSq_ge_at :
    1 - ((localH78 F i hodd hnilp C hFrob).complementIndex : ℝ) /
        ((localH78 F i hodd hnilp C hFrob).kernelOrder : ℝ) ≤
      (localH78 F i hodd hnilp C hFrob).zetaNuRhoNormSq := by
  classical
  let H78 := localH78 F i hodd hnilp C hFrob
  let hBD := localBD F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hzeta : ∀ r, H78.hyp76.zeta r =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ r : ClassFunction _ ℂ) :=
    fun r => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) r
  have hz0 : H78.hyp76.zeta 0 (1 : ↥(F.L i)) ≠ 0 := by
    rw [hzeta 0]
    exact Cert.induce_apply_one_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  have hz0_induced : ClassFunction.induce ((F.H i).subgroupOf (F.L i))
      (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) ≠ 0 :=
    Cert.induce_apply_one_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  have horth : ∀ r s, r ≠ s →
      ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta s) = 0 := by
    intro r s hrs
    rw [hzeta r, hzeta s]
    exact Cert.induce_family_orthogonal_of_injective
      ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj r s hrs
  have hzero_ne : (0 : Fin (H78.hyp76.n + 1)) ≠ H78.ind1H := by
    exact Ne.symm pf.ind1H_ne_zero
  have hζ0norm : ClassFunction.inner (H78.hyp76.zeta 0)
      (H78.hyp76.zeta 0) = 1 := by
    exact IsIrreducibleCharacter.inner_self_eq_one
      (F.hypothesis78_zeta_irreducible i hodd hnilp C hFrob)
  have hzetaImageNorm : ClassFunction.inner
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 :=
    F.hypothesis78_nu_zeta_norm_one_at i hodd hnilp C hFrob
      H78.zetaDistinct_ne_ind1H
  have hweighted : ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1 := by
    have h := F.hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
      i hodd hnilp C hFrob (r := H78.zetaDistinct)
        H78.zetaDistinct_ne_ind1H
    rw [show H78.zetaDistinct = 0 from rfl,
      F.hypothesis78_d_zero_eq_one i hodd hnilp C hFrob] at h
    exact h
  have hbeta : ClassFunction.inner H78.beta
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = (hBD.a : ℂ) - 1 :=
    H78.beta_inner_zetaImage_eq_int_sub_one_of_weighted hBD
      hzetaImageNorm hweighted
  have hz_ind : H78.hyp76.zeta H78.ind1H =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (trivialIrreducibleCharacter
          ↥((F.H i).subgroupOf (F.L i)) : ClassFunction _ ℂ) := by
    rw [hzeta, show H78.ind1H = pf.ind1H from rfl, pf.triv]
  have hd1 : H78.hyp76.d H78.ind1H = 1 := by
    change ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (pf.θ pf.ind1H : ClassFunction _ ℂ) (1 : ↥(F.L i)) /
        ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) = 1
    have hdeg_match := H78.zeta_one_eq_ind1H_one
    change ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ pf.ind1H : ClassFunction _ ℂ) (1 : ↥(F.L i)) at hdeg_match
    rw [← hdeg_match, div_self hz0_induced]
  have hP_ind1H : H78.hyp76.zeta H78.ind1H (1 : ↥(F.L i)) =
      (H78.complementIndex : ℂ) := by
    rw [Cert.complementIndex_eq_subgroupOf_index H78, hz_ind]
    exact Cert.induce_trivialChar_apply_eq_index
      ((F.H i).subgroupOf (F.L i)) (Subgroup.one_mem _)
  have hN_ind1H : H78.hyp76.zetaNormSq H78.ind1H =
      (H78.complementIndex : ℂ) := by
    exact F.hypothesis78_ind1H_inner_self_eq_complementIndex
      i hodd hnilp C hFrob
  have hz0_compl : H78.hyp76.zeta 0 (1 : ↥(F.L i)) =
      (H78.complementIndex : ℂ) := by
    change H78.hyp76.zeta H78.zetaDistinct (1 : ↥(F.L i)) =
      (H78.complementIndex : ℂ)
    rw [H78.zeta_one_eq_ind1H_one, hP_ind1H]
  have hz0_deg : ClassFunction.induce ((F.H i).subgroupOf (F.L i))
      (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) =
        (((F.H i).subgroupOf (F.L i)).index : ℂ) := by
    calc
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) =
          Classical.choose
            (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)
              (1 : ↥(F.L i)) := congrArg
                (fun χ : ClassFunction ↥(F.L i) ℂ => χ 1) pf.induce_zero_eq
      _ = (((F.H i).subgroupOf (F.L i)).index : ℂ) :=
        (Classical.choose_spec
          (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).2
  have hGsum : ∑ r ∈ (Finset.Ioi (0 : Fin (H78.hyp76.n + 1))).erase H78.ind1H,
        H78.hyp76.zeta r 1 ^ 2 / H78.hyp76.zetaNormSq r =
      (H78.complementIndex : ℂ) * ((H78.kernelOrder : ℂ) - 1) -
        (H78.complementIndex : ℂ) ^ 2 := by
    rw [Cert.complementIndex_eq_subgroupOf_index H78,
      show (H78.kernelOrder : ℂ) =
          (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) from by
        rw [show H78.kernelOrder =
            Nat.card ↥((F.H i).subgroupOf (F.L i)) from
          (Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv).symm]]
    exact Cert.family_degree_sum_Ioi
      ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj pf.cover pf.ind1H
        pf.ind1H_ne_zero pf.triv hz0_deg hζ0norm
  exact Cert.zetaNuRhoNormSq_ge_of_facts H78 hBD rfl horth
    (by
      rw [Cert.cCoeff_nu_zeta_zero_ind1H_eq H78 H78.nu rfl hd1]
      simpa only [show H78.zetaDistinct = 0 from rfl] using hbeta)
    (fun r hr0 hrind =>
      Cert.cCoeff_nu_zeta_zero_eq_neg_d H78.hyp76 H78.nu
        (fun s _ hsind =>
          F.hypothesis78_coherence_agreement_at
            i hodd hnilp C hFrob hsind)
        H78.nu_isometry hzero_ne (fun s hs => horth s 0 hs)
        hζ0norm r hr0 hrind)
    (F.hypothesis78_star_d_at i hodd hnilp C hFrob)
    (fun r => by
      rw [hzeta r]
      exact Cert.induce_apply_one_star
        ((F.H i).subgroupOf (F.L i)) (pf.θ r))
    (fun r => by
      change H78.hyp76.zeta r (1 : ↥(F.L i)) /
          H78.hyp76.zeta 0 (1 : ↥(F.L i)) =
        H78.hyp76.zeta r (1 : ↥(F.L i)) /
          (H78.complementIndex : ℂ)
      rw [hz0_compl])
    hN_ind1H hP_ind1H hGsum
    (F.hypothesis78_smallIndex_at i hodd hnilp C hFrob)

end LocalSelectedEstimate

section FamilySelectedEstimate

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))
variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- **Peterfalvi (7.8.b), family consumer form.**  The canonical character
used to define the reverse-coefficient set in (7.10) satisfies the selected
member's rho-norm lower bound. -/
theorem distinguishedNuAt_chiRhoNormSq_ge (i : Fin k) :
    (1 : ℝ) - (F.e i : ℝ) / (F.h i : ℝ) ≤
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) i := by
  classical
  letI : Fintype ↥(F.L i) := (F.familyHypothesis71).fintypeL i
  letI : Invertible (Nat.card ↥(F.L i) : ℂ) :=
    (F.familyHypothesis71).invertibleL i
  letI : Fintype ↥((F.H i).subgroupOf (F.L i)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : ((F.H i).subgroupOf (F.L i)).Normal := (hFrob i).isNormal
  let H78 := F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)
  have hbound := F.hypothesis78_zetaNuRhoNormSq_ge_at
    i hodd (hnilp i) (C i) (hFrob i)
  have he : H78.complementIndex = F.e i := rfl
  have hh : H78.kernelOrder = F.h i := rfl
  have hnorm : H78.zetaNuRhoNormSq =
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) i := by
    change (ClassFunction.inner H78.zetaNuRho H78.zetaNuRho).re = _
    have hcf : H78.zetaNuRho =
        (F.hypothesis71 i).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i) := by
      change (F.sibleyToHypothesis71 i hodd (hnilp i) (C i) (hFrob i)).chiRhoCF
          (H78.nu (H78.hyp76.zeta 0)) =
        (F.hypothesis71 i).chiRhoCF
          (F.distinguishedNuAt hodd hnilp C hFrob i)
      rw [F.sibleyToHypothesis71_chiRhoCF_eq]
      rfl
    rw [hcf]
    rfl
  rw [he, hh, hnorm] at hbound
  exact hbound

end FamilySelectedEstimate

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
