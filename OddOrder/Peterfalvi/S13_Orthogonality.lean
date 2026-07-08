/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_CoreStructure
import OddOrder.Peterfalvi.S11_NineElevenCaseA

/-!
# Peterfalvi Section 13: the (11.8.6) orthogonality endpoint — unconditional `𝒮(H₀C)` coherence

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §11, pp. 64-68.

This leaf sits **downstream of both Clifford branches** of the (9.11) `Ptype_core_coherence`
induction — caseA (`S11_NineElevenCaseA`) and caseB (`S13_CoreStructure`, issue 9075) are sibling
leaves, so the case *dispatch* needs this common downstream file.  It assembles the **unconditional**
`𝒮(H₀C)`-coherence (`coherent_sOf_H0C`) — the `hY` input of the honest (11.8.6) world-bridge union
glue `coherent_SOf_H0C_of_glued` — which replaces the deprecated wide-`Sset \ SHCSet` uniform-degree
route (false for non-Galois type III/IV, issue 1019).

The sole sorried-cite is the caseA **refuter** (the (9.11.2) pair-adjoining non-coherence, lane-b's
active `S11_NineElevenCoherence` work); everything else — the caseB coherence, the (11.7) `H₀C′ ≤ H₀C`
transfer, the Clifford dispatch, and the reducible-μ-column witness — is landed.
-/

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), unconditional: `𝒮(H₀C)` is coherent on `A₀(M)`** — the Clifford dichotomy
`clifford_dichotomy` dispatches to caseB (landed `caseB_coherent_sOf_H0C`, issue 9075 via the (11.7)
transfer) and caseA (`caseA_coherent_sOf_H0Cprime_of_refuter` + the same transfer).  The caseA
**refuter** — the (9.11.2) pair-adjoining non-coherence supplied by lane-b's `S11_NineElevenCoherence`
induction — is the sole sorried-cite.  The `𝒮(H₀C)`-restriction witness (shared by the transfer) is
the conjugate difference `μ̄ − μ` of a reducible μ-column (`columnSum_muColumnChar_mem_sOf_H0C`,
`w₂ ≥ 2`), `A₀`-supported and nonzero (odd-order no-real-characters).

This is the unconditional `hY` (𝒮(H₀C)-coherence) input of the honest (11.8.6) world-bridge union
glue `coherent_SOf_H0C_of_glued`; contradicting (11.3) `S_H0C_not_coherent` closes (11.8) without the
false wide uniform-degree route (issue 1019). -/
theorem coherent_sOf_H0C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)] :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0) := by
  haveI := hyp.base.finiteG
  classical
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) with hA | hB
  · -- **caseA**: (9.11) case-a coherence via the refuter (lane-b (9.11.2) active work, sorried-cite),
    -- then the (11.7) `H₀C′ ≤ H₀C` transfer with the reducible-μ-column witness.
    have caseA := hA.some
    have hw2 : 1 < hyp.base.w2 := hyp.params.w2_prime.one_lt
    have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
      intro heq; have := congrArg Fin.val heq; simp at this
    set μ : ClassFunction ↥M ℂ := OddOrder.Peterfalvi.S06.columnSum
      (hyp.base.toHypothesis46 hG hG.odd) (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩) with hμdef
    have hμmem : μ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
      columnSum_muColumnChar_mem_sOf_H0C hG hyp ⟨1, hw2⟩ hk1
    have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
        x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
        x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
          ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
        (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
    have hμc : μ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
      Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hμmem
    refine ⟨coherent_sOf_H0C_of_coherent_sOf_H0Cprime hyp
      (OddOrder.Peterfalvi.S13.caseA_coherent_sOf_H0Cprime_of_refuter hG hyp caseA
        (by sorry)).some ⟨μ.conj - μ, ⟨?_, ?_⟩, ?_⟩⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span hμc) (Submodule.subset_span hμmem)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.base.mderivSharp_subset_A0 (hIKF hμmem)
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ (hIKF hμmem) (sub_eq_zero.mp h)
  · -- **caseB**: the landed norm-general coherence (issue 9075) transferred to `𝒮(H₀C)`.
    exact ⟨caseB_coherent_sOf_H0C hG hyp hB.some⟩

end OddOrder.Peterfalvi.S13
