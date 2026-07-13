/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusConjIndex

/-!
# Family-wide orthogonality for Frobenius coherence (Peterfalvi 7.10)

This file supplies the general-index conjugate mechanism used in Peterfalvi 7.10.
For every non-principal member of a Frobenius induced family, its complex conjugate
is another non-principal member.  These data are the upstream input for proving
that coherent images from distinct Frobenius-family members are pairwise orthogonal.

Textbook: Peterfalvi, Section 7, pp. 40-42.
Coq comparison: PFsection7.v, CoherentFrobeniusPartition.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section GeneralIndex

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
variable [((F.H i).subgroupOf (F.L i)).Normal]
variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
variable (C : Subgroup ↥(F.L i))
variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

/-- Every non-principal member of the Sibley induced family is irreducible. -/
theorem hypothesis78_zeta_irreducible_at
    {r : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H) :
    IsIrreducibleCharacter
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r) := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) r]
  have hr_pf : r ≠ pf.ind1H := by
    intro h
    apply hr
    exact h.trans (show pf.ind1H =
      (F.hypothesis78 i hodd hnilp C hFrob).ind1H from rfl)
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hFrob (pf.θ r) (by
    intro htriv
    exact hr_pf (pf.inj (by simp only [htriv, pf.triv])))

/-- The conjugate of any non-principal induced-family member is represented by
another non-principal family index. -/
theorem exists_conjIndex_hypothesis78_at
    {r : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H) :
    ∃ r', r' ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H ∧
      (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r' =
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r).conj := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hzeta : ∀ j, (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j =
      ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (pf.θ j : ClassFunction _ ℂ) :=
    fun j => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) j
  have hzeta_inj :
      Function.Injective (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta := by
    rw [F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob]
    exact pf.inj
  have hconj_eq :
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r).conj =
        ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          ((IrreducibleCharacter.conjPerm _ (pf.θ r)) : ClassFunction _ ℂ) := by
    rw [hzeta r, conj_induce]
    exact congrArg _
      (IrreducibleCharacter.conjPerm_apply_coe (pf.θ r)).symm
  obtain ⟨r', hr'_range⟩ :=
    pf.cover (IrreducibleCharacter.conjPerm _ (pf.θ r))
  have hr'_conj :
      (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r' =
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r).conj := by
    rw [hzeta r', hconj_eq]
    exact hr'_range
  refine ⟨r', ?_, hr'_conj⟩
  intro hr'1
  apply hr
  apply hzeta_inj
  have hind_real :
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).ind1H).conj =
        (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).ind1H := by
    rw [hzeta, show (F.hypothesis78 i hodd hnilp C hFrob).ind1H =
      pf.ind1H from rfl, pf.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  have h1 :
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r).conj =
        (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).ind1H := by
    rw [← hr'_conj, hr'1]
  calc
    (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r =
        (((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r).conj).conj :=
      (ClassFunction.conj_conj _).symm
    _ = (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).ind1H := by
      rw [h1, hind_real]

/-- No non-principal induced-family member is real in odd order. -/
theorem hypothesis78_zeta_ne_conj_at
    {r : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H) :
    (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r ≠
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r).conj := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hirr := F.hypothesis78_zeta_irreducible_at i hodd hnilp C hFrob hr
  have hodd_L : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hK_ne_top : (F.H i).subgroupOf (F.L i) ≠ ⊤ := by
    intro hKtop
    refine hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := hFrob.isComplement.disjoint
    rw [hKtop] at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < ((F.H i).subgroupOf (F.L i)).index :=
    Subgroup.one_lt_index_of_ne_top hK_ne_top
  obtain ⟨d, hd_pos, hd⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (pf.θ r)
  have hdeg :
      (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r (1 : ↥(F.L i)) =
        (((F.H i).subgroupOf (F.L i)).index : ℂ) * (d : ℂ) := by
    rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) r]
    change ClassFunction.induce ((F.H i).subgroupOf (F.L i))
      (pf.θ r : ClassFunction _ ℂ) (1 : ↥(F.L i)) = _
    rw [ClassFunction.induce_apply_one, hd]
  have hne_triv :
      (⟨(F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r, hirr⟩ :
        IrreducibleCharacter ↥(F.L i)) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf :
        (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r =
          trivialClassFunction ↥(F.L i) := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : (((F.H i).subgroupOf (F.L i)).index : ℂ) * (d : ℂ) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    have hmul : ((F.H i).subgroupOf (F.L i)).index * d = 1 := by
      exact_mod_cast hone
    have hindex_one : ((F.H i).subgroupOf (F.L i)).index = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_right hmul with h
      omega
    omega
  intro hreal
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv hreal.symm

/-- The difference between a family member and its conjugate is supported on
the sharp Frobenius kernel. -/
theorem hypothesis78_zeta_sub_conj_support_at
    {r r' : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr' : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r' =
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r).conj) :
    ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r -
      (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r').support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S08.sharpImage
          ((F.H i).subgroupOf (F.L i))) (F.L i) := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hr',
    ClassFunction.conj_apply] at hx
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup,
    F.sharpImage_subgroupOf_eq i, OddOrder.Peterfalvi.S04.mem_sharp]
  refine ⟨?_, ?_⟩
  · by_contra hxH
    apply hx
    rw [(F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta_eq_zero_of_not_mem_H
      _ x hxH, star_zero, sub_zero]
  · intro hx1
    apply hx
    rw [OneMemClass.coe_eq_one.mp hx1]
    have hreal :
        star ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          r (1 : ↥(F.L i))) =
          (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            r (1 : ↥(F.L i)) := by
      rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) r]
      exact Cert.induce_apply_one_star ((F.H i).subgroupOf (F.L i)) (pf.θ r)
    rw [hreal, sub_self]

/-- The coherent-image difference of a conjugate pair is supported in
the Dade support. -/
theorem hypothesis78_nu_zeta_sub_conj_support_at
    {r r' : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H)
    (hr'_ne : r' ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H)
    (hr' : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r' =
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r).conj) :
    ((F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r) -
      (F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r')).support
      ⊆ (F.hypothesis78 i hodd hnilp C hFrob).hyp76.hyp71.hyp.dadeSupport := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hθ_ne : ∀ j, j ≠ pf.ind1H →
      pf.θ j ≠ trivialIrreducibleCharacter _ := by
    intro j hj h
    exact hj (pf.inj (by simp only [h, pf.triv]))
  have hr_mem :
      (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r ∈
        (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
    rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) r]
    exact ⟨pf.θ r, hθ_ne r hr, rfl⟩
  have hr'_mem :
      (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r' ∈
        (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
    rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) r']
    exact ⟨pf.θ r', hθ_ne r' hr'_ne, rfl⟩
  have hsupp' :
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r -
        (1 : ℂ) •
          (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r').support
        ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage
            ((F.H i).subgroupOf (F.L i))) (F.L i) := by
    rw [one_smul]
    exact F.hypothesis78_zeta_sub_conj_support_at
      i hodd hnilp C hFrob hr'
  have hagree := Cert.coherence_hagree_dadeMap
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).hconj
    (F.coherence i hodd hnilp C hFrob) hr_mem hr'_mem
    (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  have heq :
      (F.hypothesis78 i hodd hnilp C hFrob).nu
          ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r) -
        (F.hypothesis78 i hodd hnilp C hFrob).nu
          ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r') =
        ((F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade.fullDadeIsometryData
            (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).hconj).toDadeMap
            ⟨_, (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [F.hypothesis78_nu_eq i hodd hnilp C hFrob,
      ← one_smul ℂ ((F.coherence i hodd hnilp C hFrob).extension
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r'))]
    exact hagree.symm
  rw [heq]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_contra hgnot
  have hdade :=
    ((F.sibleyDadeHypothesis_of_frobenius
        i hodd hnilp C hFrob).dade.fullDadeIsometryData
      (F.sibleyDadeHypothesis_of_frobenius
        i hodd hnilp C hFrob).hconj).toDadeIsometryData.isDadeMap
  exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)

/-- Every non-principal coherent image has norm one. -/
theorem hypothesis78_nu_zeta_norm_one_at
    {r : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H) :
    ClassFunction.inner
      ((F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r))
      ((F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r)) = 1 := by
  rw [(F.hypothesis78 i hodd hnilp C hFrob).nu_isometry r r hr hr]
  exact IsIrreducibleCharacter.inner_self_eq_one
    (F.hypothesis78_zeta_irreducible_at i hodd hnilp C hFrob hr)

/-- Coherent images of a non-principal member and its conjugate are orthogonal. -/
theorem hypothesis78_nu_zeta_inner_conj_eq_zero_at
    {r r' : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H)
    (hr'_ne : r' ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H)
    (hr' : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r' =
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r).conj) :
    ClassFunction.inner
      ((F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r))
      ((F.hypothesis78 i hodd hnilp C hFrob).nu
        ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r')) = 0 := by
  rw [(F.hypothesis78 i hodd hnilp C hFrob).nu_isometry
    r r' hr hr'_ne]
  have hirr_r :=
    F.hypothesis78_zeta_irreducible_at i hodd hnilp C hFrob hr
  have hirr_r' :=
    F.hypothesis78_zeta_irreducible_at i hodd hnilp C hFrob hr'_ne
  have hne :
      (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r ≠
        (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta r' := by
    rw [hr']
    exact F.hypothesis78_zeta_ne_conj_at i hodd hnilp C hFrob hr
  have h := irreducibleCharacter_inner_eq_ite
    (⟨_, hirr_r⟩ : IrreducibleCharacter ↥(F.L i)) ⟨_, hirr_r'⟩
  rwa [if_neg (fun heq => hne (congrArg Subtype.val heq))] at h

end GeneralIndex

section CrossFamily

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) {i j : Fin k}
variable (hodd : Odd (Nat.card G))
variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
variable [((F.H i).subgroupOf (F.L i)).Normal]
variable (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
variable (C_i : Subgroup ↥(F.L i))
variable (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)
variable [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]
variable [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]
variable [((F.H j).subgroupOf (F.L j)).Normal]
variable (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))
variable (C_j : Subgroup ↥(F.L j))
variable (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j)

/-- Coherent images of arbitrary non-principal members of distinct Frobenius
families are orthogonal. -/
theorem hypothesis79_zeta_cross_eq_zero_at (hij : i ≠ j)
    {r : Fin ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).ind1H)
    {s : Fin ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.n + 1)}
    (hs : s ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H) :
    ClassFunction.inner
      ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).nu
        ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).hyp76.zeta r))
      ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta s)) = 0 := by
  classical
  obtain ⟨r', hr'_ne, hr'⟩ :=
    F.exists_conjIndex_hypothesis78_at i hodd hnilp_i C_i hFrob_i hr
  obtain ⟨s', hs'_ne, hs'⟩ :=
    F.exists_conjIndex_hypothesis78_at j hodd hnilp_j C_j hFrob_j hs
  refine orthonormal_vchar_diff_ortho
    ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).nu_zeta_mem_ZIrr_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet i hodd hnilp_i C_i hFrob_i)
      (F.hypothesis78_nu_eq i hodd hnilp_i C_i hFrob_i) hr)
    ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).nu_zeta_mem_ZIrr_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet i hodd hnilp_i C_i hFrob_i)
      (F.hypothesis78_nu_eq i hodd hnilp_i C_i hFrob_i) hr'_ne)
    ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu_zeta_mem_ZIrr_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet j hodd hnilp_j C_j hFrob_j)
      (F.hypothesis78_nu_eq j hodd hnilp_j C_j hFrob_j) hs)
    ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu_zeta_mem_ZIrr_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet j hodd hnilp_j C_j hFrob_j)
      (F.hypothesis78_nu_eq j hodd hnilp_j C_j hFrob_j) hs'_ne)
    (F.hypothesis78_nu_zeta_norm_one_at
      i hodd hnilp_i C_i hFrob_i hr)
    (F.hypothesis78_nu_zeta_norm_one_at
      i hodd hnilp_i C_i hFrob_i hr'_ne)
    (F.hypothesis78_nu_zeta_norm_one_at
      j hodd hnilp_j C_j hFrob_j hs)
    (F.hypothesis78_nu_zeta_norm_one_at
      j hodd hnilp_j C_j hFrob_j hs'_ne)
    (F.hypothesis78_nu_zeta_inner_conj_eq_zero_at
      i hodd hnilp_i C_i hFrob_i hr hr'_ne hr')
    (F.hypothesis78_nu_zeta_inner_conj_eq_zero_at
      j hodd hnilp_j C_j hFrob_j hs hs'_ne hs')
    ?_ ?_ ?_
  · apply ClassFunction.inner_eq_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro g hgi hgj
    exact Set.disjoint_left.mp
      (F.hypothesis79 i j hij hodd
        hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j).dadeSupport_disjoint
      (F.hypothesis78_nu_zeta_sub_conj_support_at
        i hodd hnilp_i C_i hFrob_i hr hr'_ne hr' hgi)
      (F.hypothesis78_nu_zeta_sub_conj_support_at
        j hodd hnilp_j C_j hFrob_j hs hs'_ne hs' hgj)
  · have hz :
        ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).nu
            ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).hyp76.zeta r) -
          (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).nu
            ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).hyp76.zeta r'))
            (1 : G) = 0 := by
      by_contra h
      exact
        (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).hyp76.hyp71.hyp.one_notMem_dadeSupport
          (F.hypothesis78_nu_zeta_sub_conj_support_at
            i hodd hnilp_i C_i hFrob_i hr hr'_ne hr'
            (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz
  · have hz :
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
            ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta s) -
          (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
            ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta s'))
            (1 : G) = 0 := by
      by_contra h
      exact
        (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.hyp71.hyp.one_notMem_dadeSupport
          (F.hypothesis78_nu_zeta_sub_conj_support_at
            j hodd hnilp_j C_j hFrob_j hs hs'_ne hs'
            (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz

/-- Weighted coherent sums from distinct Frobenius-family members are
orthogonal. -/
theorem hypothesis79_weightedNuSum_cross_eq_zero (hij : i ≠ j) :
    ClassFunction.inner
      (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).weightedNuSum
      (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).weightedNuSum = 0 := by
  classical
  rw [Hypothesis78.weightedNuSum, Hypothesis78.weightedNuSum,
    OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun r hr_mem => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero fun s hs_mem => ?_
  have hr :
      r ≠ (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).ind1H :=
    (Finset.mem_erase.mp hr_mem).1
  have hs :
      s ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H :=
    (Finset.mem_erase.mp hs_mem).1
  rw [ClassFunction.inner_smul_left,
    OddOrder.RepresentationTheory.inner_smul_right,
    F.hypothesis79_zeta_cross_eq_zero_at
      hodd hnilp_i C_i hFrob_i hnilp_j C_j hFrob_j hij hr hs,
    mul_zero, mul_zero]

end CrossFamily

section WeightedNorm

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
variable [((F.H i).subgroupOf (F.L i)).Normal]
variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
variable (C : Subgroup ↥(F.L i))
variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

/-- The squared norm of the weighted coherent sum is the local ratio
(h_i - 1) / e_i. -/
theorem hypothesis78_weightedNuSum_inner_self_eq :
    ClassFunction.inner
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum =
        (((((F.h i : ℝ) - 1) / (F.e i : ℝ)) : ℝ) : ℂ) := by
  classical
  let H78 := F.hypothesis78 i hodd hnilp C hFrob
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  change ClassFunction.inner H78.weightedNuSum H78.weightedNuSum =
    (((((F.h i : ℝ) - 1) / (F.e i : ℝ)) : ℝ) : ℂ)
  have hzeta :
      H78.hyp76.zeta =
        fun r => ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (pf.θ r : ClassFunction _ ℂ) :=
    F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob
  have horth_if : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ∀ s ∈ (Finset.univ.erase H78.ind1H),
        ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta s) =
          if r = s then
            ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)
          else 0 := by
    intro r _ s _
    by_cases hrs : r = s
    · rw [if_pos hrs, hrs]
    · rw [if_neg hrs, congrFun hzeta r, congrFun hzeta s]
      exact Cert.induce_family_orthogonal_of_injective
        ((F.H i).subgroupOf (F.L i)) pf.θ pf.inj r s hrs
  have hnorm_ne : ∀ r ∈ (Finset.univ.erase H78.ind1H),
      ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r) ≠ 0 := by
    intro r _
    rw [congrFun hzeta r]
    exact Cert.induce_norm_ne_zero
      ((F.H i).subgroupOf (F.L i)) (pf.θ r)
  have hzeta_degree :
      H78.hyp76.zeta H78.zetaDistinct (1 : ↥(F.L i)) =
        (H78.complementIndex : ℂ) := by
    rw [show H78.zetaDistinct = 0 from rfl, congrFun hzeta 0,
      Cert.complementIndex_eq_subgroupOf_index H78]
    change ClassFunction.induce ((F.H i).subgroupOf (F.L i))
      (pf.θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) =
        (((F.H i).subgroupOf (F.L i)).index : ℂ)
    rw [pf.induce_zero_eq]
    exact
      (Classical.choose_spec
        (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).2
  have hdegree_sum :
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
        H78.hyp76.zeta r (1 : ↥(F.L i)) *
            star (H78.hyp76.zeta r (1 : ↥(F.L i))) /
          ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ) := by
    have hstar : ∀ r : Fin (H78.hyp76.n + 1),
        star (H78.hyp76.zeta r (1 : ↥(F.L i))) =
          H78.hyp76.zeta r (1 : ↥(F.L i)) := by
      intro r
      rw [congrFun hzeta r]
      exact Cert.induce_apply_one_star
        ((F.H i).subgroupOf (F.L i)) (pf.θ r)
    have hsq : ∀ r : Fin (H78.hyp76.n + 1),
        H78.hyp76.zeta r (1 : ↥(F.L i)) *
            star (H78.hyp76.zeta r (1 : ↥(F.L i))) =
          H78.hyp76.zeta r (1 : ↥(F.L i)) ^ 2 := by
      intro r
      rw [hstar r, sq]
    have hind : H78.ind1H = pf.ind1H := rfl
    calc
      (∑ r ∈ (Finset.univ.erase H78.ind1H),
          H78.hyp76.zeta r (1 : ↥(F.L i)) *
              star (H78.hyp76.zeta r (1 : ↥(F.L i))) /
            ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r)) =
        ∑ r ∈ (Finset.univ.erase H78.ind1H),
          H78.hyp76.zeta r (1 : ↥(F.L i)) ^ 2 /
            ClassFunction.inner (H78.hyp76.zeta r) (H78.hyp76.zeta r) :=
        Finset.sum_congr rfl fun r _ => by rw [hsq r]
      _ = (((F.H i).subgroupOf (F.L i)).index : ℂ) *
          ((Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) - 1) := by
        change
          (∑ r ∈ (Finset.univ.erase pf.ind1H),
            ClassFunction.induce ((F.H i).subgroupOf (F.L i))
                (pf.θ r : ClassFunction _ ℂ) (1 : ↥(F.L i)) ^ 2 /
              ClassFunction.inner
                (ClassFunction.induce ((F.H i).subgroupOf (F.L i))
                  (pf.θ r : ClassFunction _ ℂ))
                (ClassFunction.induce ((F.H i).subgroupOf (F.L i))
                  (pf.θ r : ClassFunction _ ℂ))) =
            (((F.H i).subgroupOf (F.L i)).index : ℂ) *
              ((Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) - 1)
        exact Cert.family_degree_sum ((F.H i).subgroupOf (F.L i))
          pf.θ pf.inj pf.cover pf.ind1H pf.triv
      _ = ((H78.kernelOrder : ℂ) - 1) * (H78.complementIndex : ℂ) := by
        have hke :
            (H78.kernelOrder : ℂ) =
              (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ) := by
          exact_mod_cast
            (Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (F.kernel_le i)).toEquiv).symm
        have hce :
            (H78.complementIndex : ℂ) =
              (((F.H i).subgroupOf (F.L i)).index : ℂ) := by
          exact_mod_cast Cert.complementIndex_eq_subgroupOf_index H78
        rw [hke, hce]
        ring
  have hnorm :=
    H78.weightedNuSum_inner_self_eq_of_source_orthogonal
      horth_if hnorm_ne hzeta_degree hdegree_sum
  have hh : H78.kernelOrder = F.h i := rfl
  have he : H78.complementIndex = F.e i := rfl
  rw [hh, he] at hnorm
  convert hnorm using 1
  all_goals norm_num

/-- Rational-cast form of the weighted norm used by the (7.10)
orthogonal-decomposition estimate. -/
theorem hypothesis78_weightedNuSum_inner_self_eq_BsumWeight :
    ClassFunction.inner
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum =
        (F.BsumWeight i : ℂ) := by
  rw [F.hypothesis78_weightedNuSum_inner_self_eq i hodd hnilp C hFrob]
  simp only [BsumWeight]
  norm_num

end WeightedNorm

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
