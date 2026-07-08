/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_MaximalIII_IV
import OddOrder.Peterfalvi.S07_Subcoherent
import OddOrder.Peterfalvi.S11_NineElevenCoherence

/-!
# Peterfalvi (9.11), case (9.7.a): the maximality-induction entry point

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§9, pp. 55–57 (mmd `04.11`, (9.11.1)); Coq mirror `Ptype_core_coherence`
(`PFsection9.v:1484-2227`), the Clifford Galois/non-Galois split (9.7).

## What this file provides

The **case-(a) entry point** of the (9.11) `Ptype_core_coherence` induction: the
outer reduction of the coherence of the whole §9 family `𝒮(H₀C′)` to the maximality
"refuter" clause.  In Clifford case (9.7.a) one shows `𝒮(H₀C′)` is coherent by a
maximality induction — the degree-`qa` irreducible subfamily `𝒮₁` is coherent
(base case), a maximal coherent conjugation-closed `𝒮₂ ⊇ 𝒮₁` exists, and if
`𝒮₃ = 𝒮(H₀C′) ∖ 𝒮₂ ≠ ∅` then the (9.11.1)–(9.11.8) squeeze refutes the possibility
that no conjugate pair from `𝒮₃` can be coherently adjoined.

`caseA_coherent_sOf_H0Cprime_of_refuter` wires together:

* the **base case** `𝒮₁` coherent — lane-a's `sOf_degreeSubfamily_isCoherent`
  (S13) seeded by the degree-`qa` witness derived from the (9.8.d) count
  `S11.caseA_character_count_exact` (positive because `p − 1 ≥ 1` and
  `[U : U′] ≥ u ≥ 1`), transported from `𝒮(H₀U′)` down to `𝒮(H₀C′)` along
  `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′`) via `S11.sOf_antitone`;
* the lane-b **maximality skeleton**
  `S07.coherent_of_maximal_coherent_pair_refuted` (S07_Subcoherent).

The deep **refuter** clause — the (9.11.1)–(9.11.8) contradiction that no
conjugate pair from `𝒮₃` can be adjoined to a maximal `𝒮₂ ⊊ 𝒮(H₀C′)` — is taken
here as a genuine hypothesis `hrefute`; it is discharged separately.  This file is
*only* the honest reduction: no `sorry`, no new axiom.

Reference note: `issues/1017-pf-s5-uniform-degree-coherence.md` (update #27).
-/

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S11
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-- **Peterfalvi (9.11), case (9.7.a): reduction to the maximality refuter.**

In Clifford case (a), the coherence of the whole §9 family `𝒮(H₀C′)` follows from
the maximality "refuter" clause `hrefute`: given the degree-`qa` irreducible base
subfamily `𝒮₁` (coherent by `sOf_degreeSubfamily_isCoherent`), a maximal coherent
conjugation-closed `𝒮₂ ⊇ 𝒮₁` cannot have `𝒮(H₀C′) ∖ 𝒮₂ ≠ ∅` with *no* adjoinable
conjugate pair — that impossibility is `hrefute`, the (9.11.1)–(9.11.8) squeeze.

The base case's degree-`qa` witness is extracted from the positive (9.8.d) count
`S11.caseA_character_count_exact` (lower bound `(p−1)·[U:U′] > 0`), then moved from
`𝒮(H₀U′)` down to `𝒮(H₀C′)` via `S11.sOf_antitone` along `H₀C′ ≤ H₀U′`. -/
theorem caseA_coherent_sOf_H0Cprime_of_refuter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (hrefute : ∀ S₂ : Set (ClassFunction ↥M ℂ),
      {φ : ClassFunction ↥M ℂ |
          φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
          IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
        S₂ ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
        OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
        Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau S₂ hyp.base.A0) →
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂).Nonempty →
        (∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
          ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
            (S₂ ∪ {χ, χ.conj}) hyp.base.A0)) → False) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0) := by
  haveI := hyp.base.finiteG
  classical
  -- positivity of the (9.8.d) count lower bound `(p−1)·[U:U′]`
  have hp1 : 0 < hyp.chief.p - 1 := Nat.sub_pos_of_lt hyp.chief.p_prime.one_lt
  have hrel : 0 < (OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U :=
    lt_of_lt_of_le
      (OddOrder.Peterfalvi.S11.u_odd hG
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)).pos
      (OddOrder.Peterfalvi.S11.u_le_relIndex_uprimeSub_U
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
  have hNpos := lt_of_lt_of_le (mul_pos hp1 hrel)
    (OddOrder.Peterfalvi.S11.caseA_character_count_exact hG caseA)
  -- the (9.8.d) count set is nonempty: a degree-`qa` irreducible in `𝒮(H₀U′)`
  have hne : {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter χ ∧ χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    intro h0
    rw [h0, Nat.zero_mul] at hNpos
    exact absurd hNpos (lt_irrefl 0)
  -- `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′` by derived-subgroup monotonicity)
  have hCU : hyp.C ≤ hyp.s11Setup.U := by
    show hyp.C ≤ hyp.s11Setup.typeP.U
    rw [hyp.setup_typeP_eq]; exact hyp.C_le_U
  have hle : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := by
    show hyp.chief.H0 ⊔ derivedInG hyp.C
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
    refine sup_le_sup_left ?_ hyp.chief.H0
    show derivedInG hyp.C ≤ derivedInG hyp.s11Setup.U
    rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.C,
      OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.s11Setup.U]
    exact Subgroup.commutator_mono hCU hCU
  -- the base-case degree-`qa` witness `hex`, transported to `𝒮(H₀C′)`
  obtain ⟨χ, hχS, hχirr, hχdeg⟩ := hne
  have hex : ∃ ζ : ClassFunction ↥M ℂ,
      ζ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
      IsIrreducibleCharacter ζ ∧
      ((ζ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)) :=
    ⟨χ, OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hle hχS, hχirr, hχdeg⟩
  -- the whole family `𝒮(H₀C′)` is finite (world-bridge to the §10 kernel family)
  have hSfin : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime).Finite :=
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite
        (K := (derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M)).subset
      (fun x hx => by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  -- assemble the reduction via the lane-b maximality skeleton
  exact OddOrder.Peterfalvi.S07.coherent_of_maximal_coherent_pair_refuted
    (S₁ := {φ : ClassFunction ↥M ℂ |
      φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
      IsIrreducibleCharacter φ ∧
      ((φ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ))})
    hSfin
    (Hypothesis.sOf_closedUnderConjugate hyp.s11Setup hyp.H0Cprime)
    (fun _ hφ => hφ.1)
    (fun _ hχ => irrCut_conjClosed hyp hyp.H0Cprime (hyp.s11Setup.q * caseA.a) hχ)
    ⟨sOf_degreeSubfamily_isCoherent hG hyp hyp.H0Cprime (hyp.s11Setup.q * caseA.a) hex⟩
    hrefute

end OddOrder.Peterfalvi.S13
