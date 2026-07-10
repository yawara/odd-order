import OddOrder.Peterfalvi.S16_NonExistenceG.TSideTypeP
import OddOrder.Peterfalvi.S13_PrimeTIResidueBridge

/-!
# Peterfalvi (14.9): the T-side prime-TI anchor

Construction of the reducible prime-TI character `ν₀ = primeTIred 0` used in
`βT0 = ν₀ - ζ`.  This is the `primeTIred ptiWT 0` of Coq `PFsection14.v`, not the
two-dimensional §13 `nu` grid.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.9), T-side prime-TI anchor.**  If `T` is type III, its certain-type
prime-TI residue datum constructs `ν₀ = primeTIred 0`.  It is a real virtual character,
is induced from `T'` and hence supported there, and has degree
`[T:T'] = |W₁(T)| = p`.

These are precisely the source-side inputs for the supported Dade difference
`βT0 = ν₀ - ζ`; no S-side gap or cross-maximal relation is used. -/
theorem exists_typeIII_primeTIredZero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ∃ ν0 : ClassFunction ↥hyp.base.T ℂ,
      ν0 ∈ ZIrr ↥hyp.base.T ∧
        ClassFunction.IsReal ν0 ∧
        ν0.support ⊆
          ((derivedInG hyp.base.T).subgroupOf hyp.base.T :
            Set ↥hyp.base.T) ∧
        ν0 1 = (hyp.base.p : ℂ) := by
  classical
  let td : OddOrder.GroupTheory.TypeIIIData hyp.base.T := hIII.some
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeIII hG hyp.base.T_maximal hIII
  let s06 : OddOrder.Peterfalvi.S06.Hypothesis ↥hyp.base.T :=
    OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis td.typeP hG.odd
      (OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime
        hG hyp.base.T_maximal hP td.typeP)
  letI : NeZero (Nat.card ↥s06.W1) := ⟨Nat.card_pos.ne'⟩
  letI : NeZero (Nat.card ↥s06.W2) := ⟨Nat.card_pos.ne'⟩
  let residue : PrimeTIResidueData ↥hyp.base.T s06.K
      (Nat.card ↥s06.W1) (Nat.card ↥s06.W2) :=
    PrimeTIResidueData.ofS06Hypothesis s06 ⊤ le_top
  refine ⟨residue.primeTIred 0, residue.prTIred_mem_ZIrr 0, ?_, ?_, ?_⟩
  · change (residue.primeTIred 0).conj = residue.primeTIred 0
    rw [← residue.cfInd_prTIres 0, residue.prTIres0,
      ClassFunction.induce_conj, trivialClassFunction_isReal]
  · haveI : s06.K.Normal := s06.K_normal
    change (residue.primeTIred 0).support ⊆ (s06.K : Set ↥hyp.base.T)
    rw [← residue.cfInd_prTIres 0, residue.prTIres0]
    exact ClassFunction.support_induce_subset_of_normal s06.K
      (trivialClassFunction ↥s06.K)
  · calc
      residue.primeTIred 0 1 =
          (Nat.card ↥s06.W1 : ℂ) := by
        rw [← residue.cfInd_prTIres 0, residue.prTIres0,
          ClassFunction.induce_apply_one, s06.index_K_eq,
          trivialClassFunction_apply, mul_one]
      _ = (Nat.card ↥td.typeP.W1 : ℂ) := by
        congr 1
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe td.typeP.W1_le).toEquiv
      _ = (hyp.base.p : ℂ) := by
        rw [T_typeIII_card_W1 hyp td]

end OddOrder.Peterfalvi.S16
