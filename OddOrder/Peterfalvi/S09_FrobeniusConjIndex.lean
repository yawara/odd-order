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

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
