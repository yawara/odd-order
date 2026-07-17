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
/-- The weighted coherent sum projects onto each non-principal source image
with coefficient equal to the corresponding local degree ratio. -/
theorem hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
    {r : Fin ((localH78 F i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (localH78 F i hodd hnilp C hFrob).ind1H) :
    ClassFunction.inner
        (localH78 F i hodd hnilp C hFrob).weightedNuSum
        ((localH78 F i hodd hnilp C hFrob).nu
          ((localH78 F i hodd hnilp C hFrob).hyp76.zeta r)) =
      (localH78 F i hodd hnilp C hFrob).hyp76.d r := by
  let H78 := localH78 F i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hzeta : ∀ s, H78.hyp76.zeta s =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ s : ClassFunction _ ℂ) :=
    fun s => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) s
  have horth : ∀ s t, s ≠ t →
      ClassFunction.inner (H78.hyp76.zeta s) (H78.hyp76.zeta t) = 0 := by
    intro s t hst
    rw [hzeta s, hzeta t]
    exact Cert.induce_family_orthogonal_of_injective
      ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj s t hst
  have hnorm : ∀ s,
      ClassFunction.inner (H78.hyp76.zeta s) (H78.hyp76.zeta s) ≠ 0 := by
    intro s
    rw [hzeta s]
    exact Cert.induce_norm_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ s)
  have hz0 : H78.hyp76.zeta 0 (1 : ↥(F.L i)) ≠ 0 := by
    rw [hzeta 0]
    exact Cert.induce_apply_one_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  have hprojection := Cert.inner_weightedNuSum_nu_gen
    H78.hyp76.zeta horth hnorm hz0 H78.nu H78.nu_isometry hr
  change ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta r)) = H78.hyp76.d r
  rw [Hypothesis78.weightedNuSum,
    show H78.zetaDistinct = 0 from rfl, hprojection, div_eq_iff hz0]
  exact H78.hyp76.zeta_one_eq_d_mul r


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

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
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

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in
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
/-- The cross-family integer coefficient is exactly the orthogonal projection
coefficient of Gamma onto the other family's weighted coherent sum. -/
theorem hypothesis79_gamma_inner_weightedNuSum_eq_mul_self
    (hBD_i : (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).BetaDecomp)
    (hBD_j : (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).BetaDecomp)
    (hij : i ≠ j) (x : ℤ)
    (hx : ClassFunction.inner
        (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta 0)) =
      (x : ℂ)) :
    ClassFunction.inner hBD_i.Gamma
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum =
      (x : ℂ) * ClassFunction.inner
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum := by
  classical
  let H78j := F.hypothesis78 j hodd hnilp_j C_j hFrob_j
  let coeff : Fin (H78j.hyp76.n + 1) → ℂ := fun r =>
    H78j.hyp76.zeta r (1 : ↥(F.L j)) /
      (H78j.hyp76.zeta H78j.zetaDistinct (1 : ↥(F.L j)) *
        ClassFunction.inner (H78j.hyp76.zeta r) (H78j.hyp76.zeta r))
  have hpoint : ∀ r ∈ Finset.univ.erase H78j.ind1H,
      ClassFunction.inner hBD_i.Gamma
          (H78j.nu (H78j.hyp76.zeta r)) =
        (x : ℂ) * ClassFunction.inner H78j.weightedNuSum
          (H78j.nu (H78j.hyp76.zeta r)) := by
    intro r hr
    have hr' : r ≠ H78j.ind1H := Finset.ne_of_mem_erase hr
    calc
      ClassFunction.inner hBD_i.Gamma
          (H78j.nu (H78j.hyp76.zeta r)) =
        H78j.hyp76.d r *
          ClassFunction.inner
            (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
            (H78j.nu (H78j.hyp76.zeta 0)) :=
        F.hypothesis79_gamma_inner_nu_zeta_eq_d_mul
          hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j
          hBD_i hBD_j hij hr'
      _ = H78j.hyp76.d r * (x : ℂ) := by rw [hx]
      _ = (x : ℂ) * ClassFunction.inner H78j.weightedNuSum
          (H78j.nu (H78j.hyp76.zeta r)) := by
        rw [F.hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
          j hodd hnilp_j C_j hFrob_j hr']
        ring
  have hW : H78j.weightedNuSum =
      ∑ r ∈ Finset.univ.erase H78j.ind1H,
        coeff r • H78j.nu (H78j.hyp76.zeta r) := by
    rfl
  have hGammaExpand :
      ClassFunction.inner hBD_i.Gamma H78j.weightedNuSum =
        ∑ r ∈ Finset.univ.erase H78j.ind1H,
          star (coeff r) *
            ClassFunction.inner hBD_i.Gamma
              (H78j.nu (H78j.hyp76.zeta r)) := by
    calc
      ClassFunction.inner hBD_i.Gamma H78j.weightedNuSum =
          ClassFunction.inner hBD_i.Gamma
            (∑ r ∈ Finset.univ.erase H78j.ind1H,
              coeff r • H78j.nu (H78j.hyp76.zeta r)) :=
        congrArg (ClassFunction.inner hBD_i.Gamma) hW
      _ = ∑ r ∈ Finset.univ.erase H78j.ind1H,
          star (coeff r) *
            ClassFunction.inner hBD_i.Gamma
              (H78j.nu (H78j.hyp76.zeta r)) := by
        rw [OddOrder.RepresentationTheory.inner_sum_right]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [ClassFunction.inner_smul_right]
  have hWExpand :
      ClassFunction.inner H78j.weightedNuSum H78j.weightedNuSum =
        ∑ r ∈ Finset.univ.erase H78j.ind1H,
          star (coeff r) *
            ClassFunction.inner H78j.weightedNuSum
              (H78j.nu (H78j.hyp76.zeta r)) := by
    calc
      ClassFunction.inner H78j.weightedNuSum H78j.weightedNuSum =
          ClassFunction.inner H78j.weightedNuSum
            (∑ r ∈ Finset.univ.erase H78j.ind1H,
              coeff r • H78j.nu (H78j.hyp76.zeta r)) :=
        congrArg (ClassFunction.inner H78j.weightedNuSum) hW
      _ = ∑ r ∈ Finset.univ.erase H78j.ind1H,
          star (coeff r) *
            ClassFunction.inner H78j.weightedNuSum
              (H78j.nu (H78j.hyp76.zeta r)) := by
        rw [OddOrder.RepresentationTheory.inner_sum_right]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [ClassFunction.inner_smul_right]
  rw [hGammaExpand, hWExpand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hpoint r hr]
  ring

/-- Rational-weight form of the Gamma projection identity used in Peterfalvi
(7.10). -/
theorem hypothesis79_gamma_inner_weightedNuSum_eq_mul_BsumWeight
    (hBD_i : (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).BetaDecomp)
    (hBD_j : (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).BetaDecomp)
    (hij : i ≠ j) (x : ℤ)
    (hx : ClassFunction.inner
        (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).beta
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
          ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta 0)) =
      (x : ℂ)) :
    ClassFunction.inner hBD_i.Gamma
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum =
      (x : ℂ) * (F.BsumWeight j : ℂ) := by
  calc
    ClassFunction.inner hBD_i.Gamma
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum =
      (x : ℂ) * ClassFunction.inner
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum :=
      F.hypothesis79_gamma_inner_weightedNuSum_eq_mul_self
        hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j
        hBD_i hBD_j hij x hx
    _ = (x : ℂ) * (F.BsumWeight j : ℂ) := by
      rw [F.hypothesis78_weightedNuSum_inner_self_eq_BsumWeight
        j hodd hnilp_j C_j hFrob_j]

end CrossProjection

end FrobeniusFamily
namespace Cert

section ProjectionResidual

variable {G ι : Type*} [Group G]
variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- **Peterfalvi (7.10), orthogonal projection residual.**  If a finite family
is orthogonal with diagonal weights m_j and Gamma has integer projection
coefficient x_j on every selected member, then subtracting those projections
constructs a residual orthogonal to the entire selected family. -/
theorem exists_orthogonal_projection_residual
    (B : Finset ι) (v : ι → ClassFunction G ℂ)
    (x : ι → ℤ) (m : ι → ℂ) (Γ : ClassFunction G ℂ)
    (horth : ∀ i ∈ B, ∀ j ∈ B,
      ClassFunction.inner (v i) (v j) = if i = j then m i else 0)
    (hproj : ∀ j ∈ B,
      ClassFunction.inner Γ (v j) = (((x j : ℝ) : ℂ)) * m j) :
    ∃ Γ₁ : ClassFunction G ℂ,
      Γ = (∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)) + Γ₁ ∧
      ∀ j ∈ B, ClassFunction.inner Γ₁ (v j) = 0 := by
  classical
  let projection : ClassFunction G ℂ :=
    ∑ j ∈ B, (((x j : ℝ) : ℂ) • v j)
  refine ⟨Γ - projection, ?_, ?_⟩
  · dsimp [projection]
    abel
  · intro j hj
    have hsum :
        ClassFunction.inner projection (v j) =
          (((x j : ℝ) : ℂ)) * m j := by
      change ClassFunction.inner
        (∑ l ∈ B, (((x l : ℝ) : ℂ) • v l)) (v j) =
          (((x j : ℝ) : ℂ)) * m j
      rw [OddOrder.RepresentationTheory.inner_sum_left,
        Finset.sum_eq_single_of_mem j hj (fun l hl hlj => by
          rw [ClassFunction.inner_smul_left, horth l hl j hj,
            if_neg hlj, mul_zero]),
        ClassFunction.inner_smul_left, horth j hj j hj, if_pos rfl]
    rw [ClassFunction.inner_sub_left, hsum, hproj j hj, sub_self]

end ProjectionResidual

end Cert
namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section FamilyRealization

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))
variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))
variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- The concrete (7.8) datum of every member of a Frobenius family, with the
finite-cardinality instances generated canonically from the finite ambient
group.  Nilpotence remains an explicit proved input. -/
noncomputable def hypothesis78At (j : Fin k) :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)

/-- The proved beta decomposition attached to the canonical (7.8) datum of a
family member. -/
noncomputable def betaDecompAt (j : Fin k) :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
  F.hypothesis78_betaDecomp j hodd (hnilp j) (C j) (hFrob j)

/-- The weighted coherent sum belonging to the canonical (7.8) datum of a
family member. -/
noncomputable def weightedNuSumAt (j : Fin k) : ClassFunction G ℂ :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  (F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).weightedNuSum

/-- The beta class function of the canonical (7.8) datum at a family index. -/
noncomputable def betaAt (j : Fin k) : ClassFunction G ℂ :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  (F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).beta

/-- The distinguished coherent image used to define the integer cross-family
coefficient. -/
noncomputable def distinguishedNuAt (j : Fin k) : ClassFunction G ℂ :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let H78 := F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)
  H78.nu (H78.hyp76.zeta 0)

/-- The Gamma residual of the proved beta decomposition at a family index. -/
noncomputable def gammaAt (j : Fin k) : ClassFunction G ℂ :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
  (F.hypothesis78_betaDecomp j hodd (hnilp j) (C j) (hFrob j)).Gamma
/-- **Peterfalvi (7.10), family-wide weighted Gamma decomposition.**  For a
selected member i and a finite set B of distinct other members, choose the
integral cross-family coefficients x_j.  The Gamma residual at i is the sum of
the corresponding orthogonal weighted coherent projections plus a residual
Gamma₁ orthogonal to every selected weighted sum. -/
theorem exists_weightedGammaDecomposition
    (i : Fin k) (B : Finset (Fin k))
    (hB : ∀ j ∈ B, i ≠ j) :
    ∃ x : Fin k → ℤ, ∃ Γ₁ : ClassFunction G ℂ,
      (∀ j, ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob i)
        (F.distinguishedNuAt hodd hnilp C hFrob j) = (x j : ℂ)) ∧
      (∀ j ∈ B, ∀ l ∈ B,
        ClassFunction.inner
          (F.weightedNuSumAt hodd hnilp C hFrob j)
          (F.weightedNuSumAt hodd hnilp C hFrob l) =
            if j = l then (F.BsumWeight j : ℂ) else 0) ∧
      F.gammaAt hodd hnilp C hFrob i =
        (∑ j ∈ B,
          (((x j : ℝ) : ℂ) • F.weightedNuSumAt hodd hnilp C hFrob j)) + Γ₁ ∧
      ∀ j ∈ B, ClassFunction.inner Γ₁
        (F.weightedNuSumAt hodd hnilp C hFrob j) = 0 := by
  classical
  have hex : ∀ j : Fin k, ∃ x : ℤ,
      ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob i)
        (F.distinguishedNuAt hodd hnilp C hFrob j) = (x : ℂ) := by
    intro j
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
    simpa [betaAt, distinguishedNuAt] using
      (F.hypothesis79_exists_integral_beta_zeta_coefficient
        (i := i) (j := j) hodd
        (hnilp i) (C i) (hFrob i) (hnilp j) (C j) (hFrob j))
  choose x hx using hex
  have horth : ∀ j ∈ B, ∀ l ∈ B,
      ClassFunction.inner
        (F.weightedNuSumAt hodd hnilp C hFrob j)
        (F.weightedNuSumAt hodd hnilp C hFrob l) =
          if j = l then (F.BsumWeight j : ℂ) else 0 := by
    intro j _hj l _hl
    by_cases hjl : j = l
    · subst l
      rw [if_pos rfl]
      letI : Fintype ↥(F.L j) := Fintype.ofFinite _
      letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
        invertibleOfNonzero
          (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
      letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
      letI : Invertible
          (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      letI : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
      simpa [weightedNuSumAt] using
        (F.hypothesis78_weightedNuSum_inner_self_eq_BsumWeight
          j hodd (hnilp j) (C j) (hFrob j))
    · rw [if_neg hjl]
      letI : Fintype ↥(F.L j) := Fintype.ofFinite _
      letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
        invertibleOfNonzero
          (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
      letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
      letI : Invertible
          (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      letI : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
      letI : Fintype ↥(F.L l) := Fintype.ofFinite _
      letI : Invertible (Nat.card ↥(F.L l) : ℂ) :=
        invertibleOfNonzero
          (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L l)).ne')
      letI : Fintype ↥((F.H l).subgroupOf (F.L l)) := Fintype.ofFinite _
      letI : Invertible
          (Nat.card ↥((F.H l).subgroupOf (F.L l)) : ℂ) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      letI : ((F.H l).subgroupOf (F.L l)).Normal := (hFrob l).isNormal
      simpa [weightedNuSumAt] using
        (F.hypothesis79_weightedNuSum_cross_eq_zero
          (i := j) (j := l) hodd
          (hnilp j) (C j) (hFrob j) (hnilp l) (C l) (hFrob l) hjl)
  have hproj : ∀ j ∈ B,
      ClassFunction.inner
        (F.gammaAt hodd hnilp C hFrob i)
        (F.weightedNuSumAt hodd hnilp C hFrob j) =
          (((x j : ℝ) : ℂ)) * (F.BsumWeight j : ℂ) := by
    intro j hj
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
    have hxj :
        ClassFunction.inner
          (F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).beta
          ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).nu
            ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).hyp76.zeta 0)) =
            (x j : ℂ) := by
      simpa [betaAt, distinguishedNuAt] using hx j
    have hp :=
      F.hypothesis79_gamma_inner_weightedNuSum_eq_mul_BsumWeight
        (i := i) (j := j) hodd
        (hnilp i) (C i) (hFrob i) (hnilp j) (C j) (hFrob j)
        (F.hypothesis78_betaDecomp i hodd (hnilp i) (C i) (hFrob i))
        (F.hypothesis78_betaDecomp j hodd (hnilp j) (C j) (hFrob j))
        (hB j hj) (x j) hxj
    have hcast : (((x j : ℝ) : ℂ)) = (x j : ℂ) := by
      norm_num
    rw [hcast]
    simpa [gammaAt, weightedNuSumAt] using hp
  obtain ⟨Γ₁, hdecomp, hΓ₁⟩ :=
    Cert.exists_orthogonal_projection_residual B
      (F.weightedNuSumAt hodd hnilp C hFrob) x
      (fun j => (F.BsumWeight j : ℂ))
      (F.gammaAt hodd hnilp C hFrob i)
      (fun j hj l hl => by
        rw [horth j hj l hl]
        by_cases hjl : j = l <;> simp [hjl])
      hproj
  exact ⟨x, Γ₁, hx, horth, hdecomp, hΓ₁⟩
/-- The (7.9) parity alternative makes every selected projection coefficient
nonzero whenever the reverse cross coefficient vanishes. -/
theorem exists_weightedGammaDecomposition_of_reverse_eq_zero
    (i : Fin k) (B : Finset (Fin k))
    (hB : ∀ j ∈ B, i ≠ j)
    (hreverse : ∀ j ∈ B,
      ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob j)
        (F.distinguishedNuAt hodd hnilp C hFrob i) = 0) :
    ∃ x : Fin k → ℤ, ∃ Γ₁ : ClassFunction G ℂ,
      (∀ j, ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob i)
        (F.distinguishedNuAt hodd hnilp C hFrob j) = (x j : ℂ)) ∧
      (∀ j ∈ B, ∀ l ∈ B,
        ClassFunction.inner
          (F.weightedNuSumAt hodd hnilp C hFrob j)
          (F.weightedNuSumAt hodd hnilp C hFrob l) =
            if j = l then (F.BsumWeight j : ℂ) else 0) ∧
      F.gammaAt hodd hnilp C hFrob i =
        (∑ j ∈ B,
          (((x j : ℝ) : ℂ) • F.weightedNuSumAt hodd hnilp C hFrob j)) + Γ₁ ∧
      (∀ j ∈ B, ClassFunction.inner Γ₁
        (F.weightedNuSumAt hodd hnilp C hFrob j) = 0) ∧
      ∀ j ∈ B, x j ≠ 0 := by
  classical
  obtain ⟨x, Γ₁, hx, horth, hdecomp, hΓ₁⟩ :=
    F.exists_weightedGammaDecomposition hodd hnilp C hFrob i B hB
  refine ⟨x, Γ₁, hx, horth, hdecomp, hΓ₁, ?_⟩
  intro j hj
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
  have hc :=
    F.hypothesis79_conclusion i j (hB j hj) hodd
      (hnilp i) (C i) (hFrob i) (hnilp j) (C j) (hFrob j)
  change
    ClassFunction.inner
        (F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).beta
        ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).nu
          ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).hyp76.zeta 0)) ≠ 0 ∨
      ClassFunction.inner
        (F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).beta
        ((F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).nu
          ((F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).hyp76.zeta 0)) ≠ 0
    at hc
  have hreverse' :
      ClassFunction.inner
        (F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).beta
        ((F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).nu
          ((F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).hyp76.zeta 0)) = 0 := by
    simpa [betaAt, distinguishedNuAt] using hreverse j hj
  have hforward :
      ClassFunction.inner
        (F.hypothesis78 i hodd (hnilp i) (C i) (hFrob i)).beta
        ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).nu
          ((F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).hyp76.zeta 0)) ≠ 0 := by
    rcases hc with h | h
    · exact h
    · exact False.elim (h hreverse')
  have hforwardAt :
      ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob i)
        (F.distinguishedNuAt hodd hnilp C hFrob j) ≠ 0 := by
    simpa [betaAt, distinguishedNuAt] using hforward
  intro hx0
  apply hforwardAt
  simpa [hx0] using hx j
/-- Peterfalvi's set B for the selected index i: the other family members whose
reverse cross coefficient with the distinguished image at i vanishes. -/
noncomputable def reverseCoefficientZeroIndices (i : Fin k) :
    Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun j =>
    i ≠ j ∧ ClassFunction.inner
      (F.betaAt hodd hnilp C hFrob j)
      (F.distinguishedNuAt hodd hnilp C hFrob i) = 0

theorem mem_reverseCoefficientZeroIndices_iff (i j : Fin k) :
    j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i ↔
      i ≠ j ∧ ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob j)
        (F.distinguishedNuAt hodd hnilp C hFrob i) = 0 := by
  classical
  simp [reverseCoefficientZeroIndices]

/-- Consumer-ready form of the (7.10) Gamma decomposition on Peterfalvi's
concrete set B.  It exposes exactly the orthogonality, decomposition, residual
orthogonality, and nonzero coefficients required by the B-sum norm bridge. -/
theorem exists_weightedGammaDecomposition_on_reverseCoefficientZeroIndices
    (i : Fin k) :
    ∃ x : Fin k → ℤ, ∃ Γ₁ : ClassFunction G ℂ,
      (∀ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
        ∀ l ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
          ClassFunction.inner
            (F.weightedNuSumAt hodd hnilp C hFrob j)
            (F.weightedNuSumAt hodd hnilp C hFrob l) =
              if j = l then (F.BsumWeight j : ℂ) else 0) ∧
      F.gammaAt hodd hnilp C hFrob i =
        (∑ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
          (((x j : ℝ) : ℂ) • F.weightedNuSumAt hodd hnilp C hFrob j)) + Γ₁ ∧
      (∀ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
        ClassFunction.inner Γ₁
          (F.weightedNuSumAt hodd hnilp C hFrob j) = 0) ∧
      ∀ j ∈ F.reverseCoefficientZeroIndices hodd hnilp C hFrob i,
        x j ≠ 0 := by
  classical
  let B := F.reverseCoefficientZeroIndices hodd hnilp C hFrob i
  have hB : ∀ j ∈ B, i ≠ j := by
    intro j hj
    exact (F.mem_reverseCoefficientZeroIndices_iff
      hodd hnilp C hFrob i j).mp hj |>.1
  have hreverse : ∀ j ∈ B,
      ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob j)
        (F.distinguishedNuAt hodd hnilp C hFrob i) = 0 := by
    intro j hj
    exact (F.mem_reverseCoefficientZeroIndices_iff
      hodd hnilp C hFrob i j).mp hj |>.2
  obtain ⟨x, Γ₁, _hx, horth, hdecomp, hΓ₁, hx_nonzero⟩ :=
    F.exists_weightedGammaDecomposition_of_reverse_eq_zero
      hodd hnilp C hFrob i B hB hreverse
  exact ⟨x, Γ₁, horth, hdecomp, hΓ₁, hx_nonzero⟩
end FamilyRealization

end FrobeniusFamily


end OddOrder.Peterfalvi.S09
