/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S09_FrobeniusCrossOrtho
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutationUnconditional
import OddOrder.GroupTheory.RepresentationTheory.CliffordDecomposition

/-!
# The conjugate family index for a Frobenius member (Peterfalvi (7.9))

Discharges the residual conjugate-index inputs of `zetaImage_cross_eq_zero_of_conjIndex`
(`S09_FrobeniusCrossOrtho`) at the Frobenius level, now that `hypothesis78`'s induced family is
exposed via `sibleyPlacedFamily` (`hypothesis78_hyp76_zeta_eq`).

The distinguished `ζ = ζ_0 = Ind_K^L (θ_0)`; its complex conjugate `ζ̄ = Ind_K^L (θ_0)^*`
(`conj_induce`) is again an induced character, so by the family's `cover` it equals `ζ_{j₁}` for
some index `j₁`.  That `j₁ ≠ ind1H` because `ζ̄ ≠ Ind 1_K` (else `θ_0` would be trivial,
contradicting `ind1H ≠ 0` via `inj`).
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The distinguished character's conjugate is a family member of distinct index.**  For the
`i`-th Frobenius `Hypothesis78`, there is a family index `j₁ ≠ ind1H` whose induced character is the
complex conjugate of the distinguished `ζ` (= `ζ_{zetaDistinct}`).  This supplies `j₁`, `hj₁ne_ind`,
`hj₁` to `zetaImage_cross_eq_zero_of_conjIndex`. -/
theorem exists_conjIndex_hypothesis78 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    ∃ j₁, j₁ ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H ∧
      (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁
        = ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  -- `ζ_j = Ind_K (θ_j)`, `zetaDistinct = 0`, `ind1H = pf.ind1H` (all definitional).
  have hzeta : ∀ j, (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j
      = ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (pf.θ j : ClassFunction _ ℂ) :=
    fun j => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) j
  have hzd : (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 := rfl
  have hind : (F.hypothesis78 i hodd hnilp C hFrob).ind1H = pf.ind1H := rfl
  -- `ζ̄_0 = Ind_K ((θ_0)^*)`, a family member by `cover`.
  have hconj_eq : ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
      (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj
      = ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          ((IrreducibleCharacter.conjPerm _ (pf.θ 0)) : ClassFunction _ ℂ) := by
    rw [hzd, hzeta 0, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (pf.θ 0)).symm
  -- `ζ` is injective on the index (via the projection and `pf.inj`).
  have hzeta_inj : Function.Injective (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta := by
    have hfun : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        = fun j => ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (pf.θ j : ClassFunction _ ℂ) :=
      F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob
    rw [hfun]; exact pf.inj
  obtain ⟨j₁, hj₁_range⟩ := pf.cover (IrreducibleCharacter.conjPerm _ (pf.θ 0))
  -- `ζ_{j₁} = ζ̄` (second property), used also for `j₁ ≠ ind1H`.
  have hj₁_conj : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁
      = ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj := by
    rw [hzeta j₁, hconj_eq]; exact hj₁_range
  refine ⟨(j₁ : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)), ?_, hj₁_conj⟩
  -- `j₁ ≠ ind1H`: else `ζ_{zetaDistinct} = ζ_{ind1H}` (via `ζ̄` and `ζ_{ind1H}` real), contra.
  intro hj1
  apply (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct_ne_ind1H
  apply hzeta_inj
  -- `ζ_{ind1H}` is real (`Ind 1_K`), and `ζ_{ind1H} = ζ_{j₁} = ζ̄_{zetaDistinct}`.
  have e1 : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).ind1H
      = ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj := by
    rw [← hj1]; exact hj₁_conj
  have e2 : ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).ind1H).conj
      = (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).ind1H := by
    rw [hzeta, hind, pf.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  calc (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
      = ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).ind1H).conj := by rw [e1, ClassFunction.conj_conj]
    _ = (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).ind1H := e2

/-- **The distinguished `ζ` is irreducible** (Frobenius-kernel induction).  `ζ_0 = Ind_K(θ_0)` with
`θ_0 ≠ 1_K`, so it is irreducible by `isIrreducibleCharacter_induce_of_frobeniusGroup`. -/
theorem hypothesis78_zeta_irreducible [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    IsIrreducibleCharacter ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
      (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct) := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hθ0_ne : pf.θ 0 ≠ trivialIrreducibleCharacter _ := by
    intro h
    refine pf.ind1H_ne_zero (pf.inj ?_).symm
    simp only [h, pf.triv]
  have hzd : (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 := rfl
  rw [hzd, congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hFrob (pf.θ 0) hθ0_ne

/-- **The distinguished `ζ` is not real** (odd order): `ζ ≠ ζ̄`.  It is a nontrivial irreducible
character (degree `[L:K] > 1`) of the odd-order group `L`, so by (1.1) it is not real.  Supplies
`hζ₁ne_conj`/`hζ₂ne_conj` to `zetaImage_cross_eq_zero_of_conjIndex`. -/
theorem hypothesis78_zeta_ne_conj [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
      ≠ ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hirr := F.hypothesis78_zeta_irreducible i hodd hnilp C hFrob
  -- `L` has odd order (subgroup of the odd `G`).
  have hodd_L : Odd (Nat.card ↥(F.L i)) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  -- The kernel is proper (complement nontrivial), so `[L:K] > 1`.
  have hK_ne_top : (F.H i).subgroupOf (F.L i) ≠ ⊤ := by
    intro hKtop
    refine hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := hFrob.isComplement.disjoint
    rw [hKtop] at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < ((F.H i).subgroupOf (F.L i)).index :=
    Subgroup.one_lt_index_of_ne_top hK_ne_top
  -- `ζ_0 (1) = [L:K] ≠ 1`, so `ζ_0 ≠ 1_L`.
  have hdeg : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct (1 : ↥(F.L i))
      = (((F.H i).subgroupOf (F.L i)).index : ℂ) := by
    have hzd : (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 := rfl
    have hz0χ : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta 0
        = Classical.choose (F.exists_sibley_distinguished_char i hodd hnilp C hFrob) := by
      rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0]
      exact (F.sibleyPlacedFamily i hodd hnilp C hFrob).induce_zero_eq
    rw [hzd, hz0χ]
    exact (Classical.choose_spec (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).2
  have hne_triv : (⟨(F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct, hirr⟩ : IrreducibleCharacter ↥(F.L i))
      ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = trivialClassFunction ↥(F.L i) := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : (((F.H i).subgroupOf (F.L i)).index : ℂ) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    exact absurd (by exact_mod_cast hone : ((F.H i).subgroupOf (F.L i)).index = 1) (by omega)
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

/-- **`ζ − ζ̄` is supported on `A = H^#`** (equal degree).  Both `ζ = ζ_0` and `ζ̄ = ζ_{j₁}` are
induced from `K`, so vanish off `H`, and their common degree `ζ(1) = [L:K]` (real) makes the
difference vanish at `1`.  The `A`-support input to `coherence_hagree_dadeMap` for `hab_supp`. -/
theorem hypothesis78_zeta_sub_conj_support [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    {j₁ : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)}
    (hj₁ : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁
      = ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj) :
    ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
        - (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) := by
  classical
  -- `ζ(1) = [L:K]` (as in `hypothesis78_zeta_ne_conj`).
  have hdeg : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct (1 : ↥(F.L i))
      = (((F.H i).subgroupOf (F.L i)).index : ℂ) := by
    have hzd : (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 := rfl
    have hz0χ : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta 0
        = Classical.choose (F.exists_sibley_distinguished_char i hodd hnilp C hFrob) := by
      rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0]
      exact (F.sibleyPlacedFamily i hodd hnilp C hFrob).induce_zero_eq
    rw [hzd, hz0χ]
    exact (Classical.choose_spec (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).2
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hj₁, ClassFunction.conj_apply] at hx
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, F.sharpImage_subgroupOf_eq i,
    OddOrder.Peterfalvi.S04.mem_sharp]
  refine ⟨?_, ?_⟩
  · -- `(x:G) ∈ H_i`: else `ζ x = 0`, so the difference vanishes.
    by_contra hxH
    apply hx
    rw [(F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH,
      star_zero, sub_zero]
  · -- `(x:G) ≠ 1`: at `1`, `ζ(1) = [L:K]` is real, so `ζ(1) − star ζ(1) = 0`.
    intro hx1
    apply hx
    rw [OneMemClass.coe_eq_one.mp hx1, hdeg]
    simp

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
