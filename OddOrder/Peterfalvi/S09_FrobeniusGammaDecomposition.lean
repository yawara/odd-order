/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusFamilyOrthogonality
import OddOrder.Peterfalvi.S09_FrobeniusParity

/-!
# Frobenius-family Gamma decomposition (Peterfalvi 7.10)

This file constructs the coefficient relation used in Peterfalvi 7.10 to project
the residual Gamma of a selected Frobenius-family member onto the weighted coherent
sums of the other members.

Textbook: Peterfalvi, Section 7, pp. 41-43.
Coq comparison: PFsection7.v, CoherentFrobeniusPartition.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalCoefficient

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
variable [Fintype ↥((F.H i).subgroupOf (F.L i))]
variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
variable [((F.H i).subgroupOf (F.L i)).Normal]
variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
variable (C : Subgroup ↥(F.L i))
variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

private noncomputable abbrev localH78 :=
  F.hypothesis78 i hodd hnilp C hFrob

/-- The zeroth degree ratio in the concrete Frobenius family is one. -/
theorem hypothesis78_d_zero_eq_one :
    (localH78 F i hodd hnilp C hFrob).hyp76.d 0 = 1 := by
  let H78 := localH78 F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hz0 : H78.hyp76.zeta 0 (1 : ↥(F.L i)) ≠ 0 := by
    rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0]
    exact Cert.induce_apply_one_ne_zero ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  exact (mul_right_cancel₀ hz0 (by
    rw [one_mul]
    exact H78.hyp76.zeta_one_eq_d_mul 0)).symm

/-- Every concrete Frobenius-family degree ratio is fixed by complex conjugation. -/
theorem hypothesis78_star_d_at
    (r : Fin ((localH78 F i hodd hnilp C hFrob).hyp76.n + 1)) :
    star ((localH78 F i hodd hnilp C hFrob).hyp76.d r) =
      (localH78 F i hodd hnilp C hFrob).hyp76.d r := by
  let H78 := localH78 F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hzeta : ∀ s, H78.hyp76.zeta s =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ s : ClassFunction _ ℂ) :=
    fun s => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) s
  have hz0 : H78.hyp76.zeta 0 (1 : ↥(F.L i)) ≠ 0 := by
    rw [hzeta 0]
    exact Cert.induce_apply_one_ne_zero ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  have hreal : ∀ s, star (H78.hyp76.zeta s (1 : ↥(F.L i))) =
      H78.hyp76.zeta s (1 : ↥(F.L i)) := by
    intro s
    rw [hzeta s]
    exact Cert.induce_apply_one_star ((F.H i).subgroupOf (F.L i)) (pf.θ s)
  have hd : H78.hyp76.d r =
      H78.hyp76.zeta r (1 : ↥(F.L i)) /
        H78.hyp76.zeta 0 (1 : ↥(F.L i)) := by
    rw [eq_div_iff hz0]
    exact (H78.hyp76.zeta_one_eq_d_mul r).symm
  rw [hd, star_div₀, hreal r, hreal 0]

/-- On every nonzero, non-principal member, the concrete coherent extension
agrees with the Dade map on the degree-zero source difference. -/
theorem hypothesis78_coherence_agreement_at
    {r : Fin ((localH78 F i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (localH78 F i hodd hnilp C hFrob).ind1H) :
    (localH78 F i hodd hnilp C hFrob).hyp76.hyp71.τ
        ⟨(localH78 F i hodd hnilp C hFrob).hyp76.zeta r -
            (localH78 F i hodd hnilp C hFrob).hyp76.d r •
              (localH78 F i hodd hnilp C hFrob).hyp76.zeta 0,
          (localH78 F i hodd hnilp C hFrob).hyp76.psi_support r⟩ =
      (localH78 F i hodd hnilp C hFrob).nu
          ((localH78 F i hodd hnilp C hFrob).hyp76.zeta r) -
        (localH78 F i hodd hnilp C hFrob).hyp76.d r •
          (localH78 F i hodd hnilp C hFrob).nu
            ((localH78 F i hodd hnilp C hFrob).hyp76.zeta 0) := by
  classical
  let H78 := localH78 F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hzeta : ∀ s, H78.hyp76.zeta s =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ s : ClassFunction _ ℂ) :=
    fun s => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) s
  have hθ_ne : ∀ s, s ≠ pf.ind1H →
      pf.θ s ≠ trivialIrreducibleCharacter _ := by
    intro s hs h
    exact hs (pf.inj (by simp only [h, pf.triv]))
  have hr_mem : H78.hyp76.zeta r ∈
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S :=
    ⟨pf.θ r, hθ_ne r hr, hzeta r⟩
  have h0_mem : H78.hyp76.zeta 0 ∈
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S :=
    ⟨pf.θ 0, hθ_ne 0 (Ne.symm pf.ind1H_ne_zero), hzeta 0⟩
  obtain ⟨deg_r, -, hdeg_r⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (pf.θ r)
  obtain ⟨deg_0, hdeg_0_pos, hdeg_0⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (pf.θ
      (0 : Fin (H78.hyp76.n + 1)))
  have hdeg_0_ne : (deg_0 : ℂ) ≠ 0 := by
    exact_mod_cast hdeg_0_pos.ne'
  have hidx_ne : (((F.H i).subgroupOf (F.L i)).index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  have hzr :
      H78.hyp76.zeta r (1 : ↥(F.L i)) =
        (((F.H i).subgroupOf (F.L i)).index : ℂ) * (deg_r : ℂ) := by
    rw [hzeta r, ClassFunction.induce_apply_one, hdeg_r]
  have hz0 :
      H78.hyp76.zeta 0 (1 : ↥(F.L i)) =
        (((F.H i).subgroupOf (F.L i)).index : ℂ) * (deg_0 : ℂ) := by
    rw [hzeta 0, ClassFunction.induce_apply_one]
    exact congrArg (((((F.H i).subgroupOf (F.L i)).index : ℂ)) * ·) hdeg_0
  have hd : H78.hyp76.d r = (deg_r : ℂ) / (deg_0 : ℂ) := by
    have h := H78.hyp76.zeta_one_eq_d_mul r
    rw [hzr, hz0] at h
    rw [eq_div_iff hdeg_0_ne]
    apply mul_left_cancel₀ hidx_ne
    linear_combination -h
  have hagree := Cert.coherence_hagree_dadeMap
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).hconj
    (F.coherence i hodd hnilp C hFrob) hr_mem h0_mem
    (m0 := deg_0) (mi := deg_r) hdeg_0_ne hd
    (H78.hyp76.psi_support r)
  rw [F.hypothesis78_nu_eq i hodd hnilp C hFrob]
  exact hagree

/-- The coherent degree-zero difference is supported on the local Dade support. -/
theorem hypothesis78_nu_zeta_sub_d_smul_support_at
    {r : Fin ((localH78 F i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (localH78 F i hodd hnilp C hFrob).ind1H) :
    ((localH78 F i hodd hnilp C hFrob).nu
          ((localH78 F i hodd hnilp C hFrob).hyp76.zeta r) -
        (localH78 F i hodd hnilp C hFrob).hyp76.d r •
          (localH78 F i hodd hnilp C hFrob).nu
            ((localH78 F i hodd hnilp C hFrob).hyp76.zeta 0)).support
      ⊆ (localH78 F i hodd hnilp C hFrob).hyp76.hyp71.hyp.dadeSupport := by
  let H78 := localH78 F i hodd hnilp C hFrob
  rw [← F.hypothesis78_coherence_agreement_at i hodd hnilp C hFrob hr]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  exact hg (H78.hyp76.hyp71.isDadeMap.map_eq_zero_of_not_mem_dadeSupport
    (H78.hyp76.psiSupp r) g hgnot)

end LocalCoefficient

section CrossProjection

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) {i j : Fin k}
variable (hodd : Odd (Nat.card G))
variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
variable [Fintype ↥((F.H i).subgroupOf (F.L i))]
variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
variable [((F.H i).subgroupOf (F.L i)).Normal]
variable (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
variable (C_i : Subgroup ↥(F.L i))
variable (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)
variable [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]
variable [Fintype ↥((F.H j).subgroupOf (F.L j))]
variable [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]
variable [((F.H j).subgroupOf (F.L j)).Normal]
variable (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
variable (C_j : Subgroup ↥(F.L j))
variable (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j)

/-- The weighted coherent sum of one family is orthogonal to every
non-principal coherent source image of a distinct family. -/
theorem hypothesis79_weightedNuSum_cross_zeta_eq_zero_at
    (hij : i ≠ j)
    {r : Fin ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H) :
    ClassFunction.inner
      (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).weightedNuSum
      ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta r)) = 0 := by
  classical
  rw [Hypothesis78.weightedNuSum,
    OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [ClassFunction.inner_smul_left,
    F.hypothesis79_zeta_cross_eq_zero_at
      hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j hij
      (Finset.ne_of_mem_erase hs) hr,
    mul_zero]

/-- Expanding the selected beta decomposition against a coherent source image
of a distinct family leaves only the Gamma term. -/
theorem hypothesis79_beta_inner_nu_zeta_eq_gamma
    (hBD_i : (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).BetaDecomp)
    (hBD_j : (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).BetaDecomp)
    (hij : i ≠ j)
    {r : Fin ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H) :
    ClassFunction.inner
        (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta r)) =
      ClassFunction.inner hBD_i.Gamma
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta r)) := by
  let H78i := F.hypothesis78 i hodd hnilp_i C_i hFrob_i
  let H78j := F.hypothesis78 j hodd hnilp_j C_j hFrob_j
  have hone : ClassFunction.inner (Hypothesis71.constOne G)
      (H78j.nu (H78j.hyp76.zeta r)) = 0 := by
    rw [Hypothesis71.ClassFunction.inner_symm, hBD_j.orth_one r hr, star_zero]
  have hzeta : ClassFunction.inner
      (H78i.nu (H78i.hyp76.zeta H78i.zetaDistinct))
      (H78j.nu (H78j.hyp76.zeta r)) = 0 :=
    F.hypothesis79_zeta_cross_eq_zero_at
      hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j hij
      H78i.zetaDistinct_ne_ind1H hr
  have hweighted : ClassFunction.inner H78i.weightedNuSum
      (H78j.nu (H78j.hyp76.zeta r)) = 0 :=
    F.hypothesis79_weightedNuSum_cross_zeta_eq_zero_at
      hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j hij hr
  rw [hBD_i.beta_eq, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
    ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    hone, hzeta, hweighted, mul_zero]
  ring

/-- The coefficient of Gamma on any source image in a distinct Frobenius
family is its local degree ratio times the distinguished beta coefficient. -/
theorem hypothesis79_gamma_inner_nu_zeta_eq_d_mul
    (hBD_i : (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).BetaDecomp)
    (hBD_j : (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).BetaDecomp)
    (hij : i ≠ j)
    {r : Fin ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H) :
    ClassFunction.inner hBD_i.Gamma
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta r)) =
      (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.d r *
        ClassFunction.inner
          (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
            ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta 0)) := by
  let H78i := F.hypothesis78 i hodd hnilp_i C_i hFrob_i
  let H78j := F.hypothesis78 j hodd hnilp_j C_j hFrob_j
  let H79 :=
    F.hypothesis79 i j hij hodd
      hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j
  have hsupp :
      (H78j.nu (H78j.hyp76.zeta r) -
        H78j.hyp76.d r • H78j.nu (H78j.hyp76.zeta 0)).support
        ⊆ H78j.hyp76.hyp71.hyp.dadeSupport :=
    F.hypothesis78_nu_zeta_sub_d_smul_support_at
      j hodd hnilp_j C_j hFrob_j hr
  have hzero : ClassFunction.inner H78i.beta
      (H78j.nu (H78j.hyp76.zeta r) -
        H78j.hyp76.d r • H78j.nu (H78j.hyp76.zeta 0)) = 0 := by
    apply ClassFunction.inner_eq_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro g hg_beta hg_diff
    exact Set.disjoint_left.mp H79.dadeSupport_disjoint
      (H78i.beta_support_subset_dadeSupport hg_beta)
      (hsupp hg_diff)
  have hbeta_gamma := F.hypothesis79_beta_inner_nu_zeta_eq_gamma
    hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j
    hBD_i hBD_j hij hr
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_smul_right,
    F.hypothesis78_star_d_at j hodd hnilp_j C_j hFrob_j r,
    hbeta_gamma] at hzero
  linear_combination hzero

/-- The distinguished beta coefficient against another family is an integer,
because both class functions are virtual characters. -/
theorem hypothesis79_exists_integral_beta_zeta_coefficient :
    ∃ x : ℤ,
      ClassFunction.inner
          (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
            ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta 0)) =
        (x : ℂ) := by
  classical
  let H78i := F.hypothesis78 i hodd hnilp_i C_i hFrob_i
  let H78j := F.hypothesis78 j hodd hnilp_j C_j hFrob_j
  have h0 : (0 : Fin (H78j.hyp76.n + 1)) ≠ H78j.ind1H := by
    intro h
    apply H78j.zetaDistinct_ne_ind1H
    exact (show H78j.zetaDistinct = 0 from rfl).trans h
  have hbetaZ : H78i.beta ∈ ZIrr G :=
    H78i.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (F.hypothesis78_ind1H_mem_ZIrr i hodd hnilp_i C_i hFrob_i)
      (F.hypothesis78_zeta_irreducible i hodd hnilp_i C_i hFrob_i)
  have hnuZ : H78j.nu (H78j.hyp76.zeta 0) ∈ ZIrr G :=
    H78j.nu_zeta_mem_ZIrr_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet j hodd hnilp_j C_j hFrob_j)
      (F.hypothesis78_nu_eq j hodd hnilp_j C_j hFrob_j) h0
  exact ClassFunction.inner_mem_ZIrr_int hbetaZ hnuZ
end CrossProjection

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
