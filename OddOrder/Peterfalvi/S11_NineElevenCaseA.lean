/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S13_MaximalIII_IV
import OddOrder.Peterfalvi.S07_Subcoherent
import OddOrder.Peterfalvi.S11_NineElevenCoherence
import OddOrder.Peterfalvi.S11_NineElevenTwoSummand
import OddOrder.Peterfalvi.S11_NineElevenMackeyNorm
import OddOrder.Peterfalvi.S13_CoreStructure
import OddOrder.Peterfalvi.S13_SixTwoBridge

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

/-! ### The (9.11.1) squeeze wiring: refuter ⟶ equality configuration (issue 9083, Phase A)

Book (9.11.1) opens the refutation of `𝒮₃ ≠ ∅`: *"By Theorem (5.6) and by (9.8.a, d),
`(p−1)|U:U′|q² ≤ ∑_{ψ∈𝒮₁∩𝒮(H₀U′)∩Irr M} ψ(1)²/‖ψ‖² ≤ ∑_{ψ∈𝒮₂} ψ(1)²/‖ψ‖² ≤ 2q²aχ(1) ≤ 2q²au`.
Thus … `C = U′` and `a = (p−1)/2`.  Furthermore, the inequalities above are equalities."*  The
squeeze arithmetic is landed (`nineElevenOne_squeeze_arithmetic`/`nineElevenOne_configuration`);
the two remaining honest inputs are isolated here as named `Prop` shapes, and
`caseA_refuter_of_equality_refutation` wires them through the squeeze to discharge the refuter
clause of `caseA_coherent_sOf_H0Cprime_of_refuter`. -/

/-- **Peterfalvi (9.11.1), the (5.6) pair-bound bundle** (hypothesis shape, issue 9083 Phase A).

The world-side output of Theorem (5.6) at a pair-refuted (9.11) configuration: for a coherent
conjugation-closed `𝒮₁ ⊆ 𝒮₂ ⊆ 𝒮(H₀C′)` and a `χ ∈ 𝒮₃ = 𝒮(H₀C′) ∖ 𝒮₂` whose conjugate pair
`{χ, χ̄}` cannot be coherently adjoined, the member `χ = Ind_{HU}^M ζ` has degree `χ(1) = q·d`
with source degree `d = ζ(1) ≤ u` (Coq `lb01`'s degree dictionary: `ζ|_{HC}` contains a linear
constituent because `(HC)′ ≤ H₀C′`, so `ζ(1) ≤ [HU:HC] = u`), and every finite subfamily
`F ⊆ 𝒮₂` obeys the norm-weighted degree-square bound `sumnS F ≤ 2·(qa)·(q·d) = 2q²a·d` — the raw
form of the (5.6) contrapositive `coherentDegreeSqNormBound_of_not_coherentW`'s
`∑ deg²/mc ≤ 2·(d/a)`, rescaled by the anchor degree `qa` (`sumnS_image_eq_anchorSq_mul`).  This
is the right endpoint `sumnS 𝒮₂ ≤ 2q²aχ₀(1)` of the (9.11.1) squeeze circle (Coq
`PFsection9.v:1560-1611`), quantified over finite subfamilies so the squeeze can instantiate it
at `𝒮₁′` (here) and later phases at `𝒮₂` itself (the `𝒮₂ = 𝒮₁` extraction).  Discharged by the
(9.11) refuter assembly threading the §9 member Dade decompositions through the weighted (5.6)
engine (issue 9083 Phase E). -/
def NineElevenPairBound [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
    {φ : ClassFunction ↥M ℂ |
        φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
        IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
      S₂ ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau S₂ hyp.base.A0) →
      ∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
          (S₂ ∪ {χ, χ.conj}) hyp.base.A0) →
        ∃ d : ℕ,
          ((χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * d : ℕ) : ℂ)) ∧
          d ≤ (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u ∧
          ∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
            OddOrder.Peterfalvi.S07.sumnS F
              ≤ 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ)

/-- **Peterfalvi (9.11.2)–(9.11.8), the equality-configuration refutation** (hypothesis shape,
issue 9083 Phase A).

The (9.11.1) squeeze forces the *equality configuration* at any pair-refuted maximal `𝒮₂`:
`2a = p−1` (so `p = 2a+1`), `C = U′`, every `𝒮₃`-member of degree `qu`, the count equality
`|𝒮₁′|·a² = (p−1)·[U:U′]`, and the saturated subfamily bound `sumnS F ≤ 2q²au` (`F ⊆ 𝒮₂` finite;
at the full `F = 𝒮₂` this is the squeeze equality forcing the book's `𝒮₂ = 𝒮₁`, since any extra
member adds positive `Snorm`).  This `Prop` is that configuration's refutation — the remaining
honest (9.11) content: **(9.11.2)** the two-summand inertia identity `U₁ ∩ U₁ʷ = C` giving
`u ≤ a²` (issue 9083 Phase B), **(9.11.3)** the `HŪ/(H₀C)` class equation and `W₁`-orbit split
(Phase C), **(9.11.4)** the Mackey norm `‖α‖²·u = (a+1)u + (q−1)a²` (Phase D), and the
(9.11.5)–(9.11.8) `|𝒮₄| ≤ ‖α‖²` bound from the pair clause plus the coherent-pair construction
(Phase E); the arithmetic chain is landed as `nineElevenCaseA_equality_refutation`
(`S11_NineElevenCoherence`). -/
def NineElevenEqualityRefutation [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
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
          (S₂ ∪ {χ, χ.conj}) hyp.base.A0)) →
      2 * caseA.a = hyp.chief.p - 1 →
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C
        = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Uprime →
      (∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
        (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q *
          (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ)) →
      {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
          (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
          IsIrreducibleCharacter χ ∧
          χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
        = (hyp.chief.p - 1)
          * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U) →
      (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ)
          * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℝ)) →
      False

/-- **Peterfalvi (9.11.1): the caseA maximality refuter, reduced to the equality-configuration
refutation** (issue 9083 Phase A).

The refuter clause of `caseA_coherent_sOf_H0Cprime_of_refuter` follows from the two remaining
honest inputs: the (5.6) pair-bound bundle `hbound` (`NineElevenPairBound`) and the
(9.11.2)–(9.11.8) equality-configuration refutation `hrefuteEq` (`NineElevenEqualityRefutation`).

The wiring is the (9.11.1) squeeze: for each non-adjoinable `χ ∈ 𝒮₃`, `hbound` gives the source
degree `d ≤ u` and the upper bound `sumnS 𝒮₁′ ≤ 2q²a·d` at the uniform degree-`qa` subfamily
`𝒮₁′ ⊆ 𝒮₁ ⊆ 𝒮₂` (transported from `𝒮(H₀U′)` along `H₀C′ ≤ H₀U′`, as in the base case); the
matching lower bound `|𝒮₁′|·(qa)² = sumnS 𝒮₁′` is `sumnS_irreducible_constant_degree` (norm-one
irreducibles of uniform degree `qa`).  Feeding both into `nineElevenOne_configuration` closes the
squeeze circle and yields the equality configuration — `2a = p−1`, `C = U′`, `d = u` (so *every*
`𝒮₃`-member has degree `qu`: the book's "we may assume" is made uniform by running the squeeze
per member), and the count equality — which `hrefuteEq` refutes. -/
theorem caseA_refuter_of_equality_refutation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (hbound : NineElevenPairBound hyp caseA)
    (hrefuteEq : NineElevenEqualityRefutation hyp caseA) :
    ∀ S₂ : Set (ClassFunction ↥M ℂ),
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
            (S₂ ∪ {χ, χ.conj}) hyp.base.A0)) → False := by
  haveI := hyp.base.finiteG
  classical
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs
  -- numeric positivity inputs of the squeeze
  have hq : 0 < hyp.s11Setup.q := hyp.s11Setup.nontrivial.2.1.pos
  have hu : 0 < (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u :=
    (OddOrder.Peterfalvi.S11.u_odd hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)).pos
  have hp1 : 0 < hyp.chief.p - 1 := Nat.sub_pos_of_lt hyp.chief.p_prime.one_lt
  -- `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′`), as in `caseA_coherent_sOf_H0Cprime_of_refuter`
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
  -- the uniform degree-`qa` subfamily `𝒮₁′ ⊆ 𝒮(H₀U′)` is finite and contained in `𝒮₂`
  have hSfin : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime).Finite :=
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite
        (K := (derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M)).subset
      (fun x hx => by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hS1'sub : {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter χ ∧
      χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)} ⊆ S₂ := fun χ hχ =>
    hS₁sub ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hle hχ.1, hχ.2.1, hχ.2.2⟩
  have hS1'fin : ({χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter χ ∧
      χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}).Finite :=
    hSfin.subset fun χ hχ => hS₂sub (hS1'sub hχ)
  -- (9.11.5) left endpoint: `sumnS 𝒮₁′ = |𝒮₁′|·(qa)²` (norm-one uniform degree-`qa` members)
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ) * ((hyp.s11Setup.q * caseA.a : ℕ) : ℝ) ^ 2 :=
    OddOrder.Peterfalvi.S11.sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  have hs1' : (({χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
        (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
        IsIrreducibleCharacter χ ∧
        χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard : ℝ))
      * ((hyp.s11Setup.q * caseA.a : ℕ) : ℝ) ^ 2
      ≤ OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset :=
    le_of_eq (by rw [Set.ncard_eq_toFinset_card _ hS1'fin, hsum1'])
  -- per-`χ` (9.11.1) squeeze: every non-adjoinable `𝒮₃`-member forces the equality configuration
  have hconfig : ∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      ∃ d : ℕ, ((χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * d : ℕ) : ℂ)) ∧
        (2 * caseA.a = hyp.chief.p - 1 ∧
          (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C
            = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Uprime ∧
          d = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u ∧
          {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
              (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
              IsIrreducibleCharacter χ ∧
              χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
            = (hyp.chief.p - 1)
              * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex
                hyp.s11Setup.U)) ∧
        (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
          OddOrder.Peterfalvi.S07.sumnS F
            ≤ 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ)) := by
    intro χ hχ
    obtain ⟨d, hχdeg, hdu, hFbound⟩ :=
      hbound S₂ hS₁sub hS₂sub hS₂conj hS₂coh χ hχ (hpairs χ hχ)
    have hpair : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
        ≤ 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) :=
      hFbound hS1'fin.toFinset (by rw [Set.Finite.coe_toFinset]; exact hS1'sub)
    exact ⟨d, hχdeg,
      OddOrder.Peterfalvi.S11.nineElevenOne_configuration hG caseA hq hu hp1 hdu hs1' hpair,
      hFbound⟩
  -- extract the global configuration facts from the `𝒮₃`-witness …
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  obtain ⟨d₀, -, ⟨h2a, hCUprime, hd₀u, hcount⟩, hFbound₀⟩ := hconfig χ₀ hχ₀
  -- … the uniform degree `qu` on `𝒮₃` (the squeeze run per member) …
  have hS3deg : ∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q *
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ) := by
    intro χ hχ
    obtain ⟨d, hχdeg, ⟨-, -, hdu, -⟩, -⟩ := hconfig χ hχ
    rwa [hdu] at hχdeg
  -- … and the saturated subfamily bound `sumnS F ≤ 2q²au`
  have hFboundU : ∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ)
        * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℝ) := by
    intro F hF
    have h := hFbound₀ F hF
    rwa [hd₀u] at h
  -- hand the configuration to the (9.11.2)–(9.11.8) refutation
  exact hrefuteEq S₂ hS₁sub hS₂sub hS₂conj hS₂coh ⟨χ₀, hχ₀⟩ hpairs
    h2a hCUprime hS3deg hcount hFboundU

/-! ### The (5.6) pair-bound bundle discharged (issue 9083, Phase E-PairBound)

Book (9.11.1) right endpoint: *"… `≤ ∑_{ψ∈𝒮₂} ψ(1)²/‖ψ‖² ≤ 2q²aχ(1)`"* — Theorem (5.6) applied
at the maximal coherent `𝒮₂` with the degree-`qa` anchor `χ₁ ∈ 𝒮₁ ⊆ 𝒮₂` and the pair-refuted
break `χ ∈ 𝒮₃` (Coq `PFsection9.v:1608-1618`, the `extend_coherent` branch read contrapositively).
The norm-weighted engine is `S08.coherentDegreeSqNormBound_of_not_coherentW_k`; its member
ratios `deg(ψ) = ψ(1)/χ₁(1) = (source degree)/a ∈ ℕ` are supplied by the case-(a) divisibility
(9.8.a) `a ∣ (source degree)` (`caseA_source_degree_dvd_a`, Coq `a_dv_XH0` — exactly the
divisibility Coq feeds `extend_coherent`'s `xi1 1%g %| chi 1%g` side condition), and the
per-member Dade decompositions come from the §11 grid supply `S12.sixTwoDecompositionData`
((5.2.d) + (5.2.e), issue 2022). -/

/-- **Peterfalvi (9.8.a), member-degree dictionary for `𝒮(H₀ ⊔ Y)`** (Coq `a_dv_XH0` in member
form): in Clifford case (a), every member `Ind_{HU}^M ξ` of a §9 family whose source kernel
contains `H₀` has degree `q·a·e` for some `e : ℕ` — the source degree `ξ(1)` is divisible by the
Clifford integer `a` (`caseA_source_degree_dvd_a`).  This is the per-member degree-ratio supply
of the (5.6) pair-bound assembly `nineElevenPairBound`: ratios are taken against the degree-`qa`
anchor, so each member's ratio is the natural `e = ξ(1)/a`. -/
theorem caseA_sOf_source_degree_ratio [Finite G] {M : Subgroup G}
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    {chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData chars)
    {Y : Subgroup G} {ψ : ClassFunction ↥M ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S11.sOf data (chief.H0 ⊔ Y)) :
    ∃ e : ℕ, (ψ : ↥M → ℂ) 1 = ((data.q * caseA.a * e : ℕ) : ℂ) := by
  classical
  obtain ⟨ξ, hξ, rfl⟩ := hψ
  obtain ⟨dξ, -, hdξ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξ
  have hker : ((chief.H0.subgroupOf M).subgroupOf (OddOrder.Peterfalvi.S11.huSub data) :
      Set ↥(OddOrder.Peterfalvi.S11.huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ) :=
    subset_trans (SetLike.coe_subset_coe.mpr (Subgroup.subgroupOf_mono _
      (Subgroup.subgroupOf_mono _ le_sup_left))) hξ.2
  obtain ⟨e, he⟩ := OddOrder.Peterfalvi.S11.caseA_source_degree_dvd_a caseA hξ.1 hker hdξ
  refine ⟨e, ?_⟩
  rw [OddOrder.Peterfalvi.S11.induceHU_apply_one_eq_q_mul, hdξ, he]
  push_cast
  ring

set_option maxHeartbeats 3200000 in
-- the (5.6) engine and the grid decomposition supply thread the
-- `hyp.base.tau = dadeIntegralCharacterMap` / `hyp.base.A0 = supportInSubgroup` defeqs,
-- which is feasible but expensive (same as `caseB_coherent_sOf_H0Cprime`)
/-- **Peterfalvi (9.11.1), the (5.6) pair-bound bundle, discharged** (issue 9083 Phase
E-PairBound).

For a pair-refuted `χ ∈ 𝒮₃ = 𝒮(H₀C′) ∖ 𝒮₂`: the member dictionary gives `χ = Ind_{HU}^M ζ` with
`χ(1) = q·d`, `d = ζ(1)`; the source-degree bound `d ≤ u` is `xiOf_H0Cprime_source_apply_one_le_u`
(the (9.11.1) preamble: `ζ` lies over a linear character of `HC` since `⁅HC,HC⁆ ≤ H₀C′ ⊆ Ker ζ`);
and every finite `F ⊆ 𝒮₂` obeys `sumnS F ≤ 2q²a·d` — Theorem (5.6) at the degree-`qa` anchor
`χ₁ ∈ 𝒮₁ ⊆ 𝒮₂` (from the positive (9.8.d) count, as in the base case), read contrapositively
through the norm-weighted engine `coherentDegreeSqNormBound_of_not_coherentW_k`:

* member ratios `deg(ψ) = ψ(1)/χ₁(1) = (source degree)/a ∈ ℕ` by the (9.8.a) divisibility
  `a ∣ (source degree)` (`caseA_sOf_source_degree_ratio`, Coq `a_dv_XH0`), anchor ratio `1`,
  break ratio `χ(1)/χ₁(1) = d/a`;
* Gram data (orthogonality, positive squared norms), scaled-difference supports, `ZIrr`
  integrality, and the two generation clauses from the general kernel-family layer
  (`S08_SixTwoGeneral`, as in `inducedKernelFamily_degreeSqNormReBound_of_break_k`);
* the break decomposition `Da` and the per-member (5.2.d)/(5.2.e) R-data from the §11 grid
  supply `S12.sixTwoDecompositionData` (issue 2022);

then `sumnS F ≤ sumnS 𝒮₂ = (qa)²·∑ deg²/‖·‖² ≤ (qa)²·2·(d/a) = 2q²a·d`
(`sumnS_le_of_subset` + the raw↔normalized rescaling). -/
theorem nineElevenPairBound [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)) :
    NineElevenPairBound hyp caseA := by
  haveI := hyp.base.finiteG
  classical
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh χ hχ hnc
  obtain ⟨hχS, hχnotS₂⟩ := hχ
  obtain ⟨cohS₂⟩ := hS₂coh
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hq : 0 < hyp.s11Setup.q := hyp.s11Setup.nontrivial.2.1.pos
  -- ── the break dictionary: `χ = Ind_{HU}^M ζ`, `χ(1) = q·d`, `a ∣ d`, `d ≤ u`
  obtain ⟨ζ, hζ, rfl⟩ := hχS
  obtain ⟨d, -, hdζ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ζ
  have hχdeg : (OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) : ↥M → ℂ) 1
      = ((hyp.s11Setup.q * d : ℕ) : ℂ) := by
    rw [OddOrder.Peterfalvi.S11.induceHU_apply_one_eq_q_mul, hdζ]
    push_cast
    ring
  -- `a ∣ d` ((9.8.a), Coq `a_dv_XH0`)
  have hkerζ : ((hyp.chief.H0.subgroupOf M).subgroupOf
      (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) :
      Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) :=
    subset_trans (SetLike.coe_subset_coe.mpr (Subgroup.subgroupOf_mono _
      (Subgroup.subgroupOf_mono _ le_sup_left))) hζ.2
  obtain ⟨e, he⟩ := OddOrder.Peterfalvi.S11.caseA_source_degree_dvd_a caseA hζ.1 hkerζ hdζ
  -- `d ≤ u` (the (9.11.1) preamble source-degree bound)
  have hCp : OddOrder.Peterfalvi.S11.cprimeSub hyp.s11Setup hyp.chief = derivedInG hyp.C := by
    change derivedInG (OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief) = derivedInG hyp.C
    rw [C_eq_cSub hG hyp]
  have hζ' : ζ ∈ OddOrder.Peterfalvi.S11.xiOf hyp.s11Setup
      (hyp.chief.H0 ⊔ (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Cprime) := by
    show ζ ∈ OddOrder.Peterfalvi.S11.xiOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cprimeSub hyp.s11Setup hyp.chief)
    rw [hCp]
    exact hζ
  have hduC := OddOrder.Peterfalvi.S11.xiOf_H0Cprime_source_apply_one_le_u
    (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) hζ'
  rw [hdζ] at hduC
  have hdu : d ≤ (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u := by
    have h := (Complex.le_def.mp hduC).1
    rw [Complex.natCast_re, Complex.natCast_re] at h
    exact_mod_cast h
  refine ⟨d, hχdeg, hdu, ?_⟩
  -- ── the anchor: a degree-`qa` irreducible of `𝒮(H₀U′)`, transported into `S₂` via `hS₁sub`
  have hp1 : 0 < hyp.chief.p - 1 := Nat.sub_pos_of_lt hyp.chief.p_prime.one_lt
  have hrel : 0 < (OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U :=
    lt_of_lt_of_le
      (OddOrder.Peterfalvi.S11.u_odd hG
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)).pos
      (OddOrder.Peterfalvi.S11.u_le_relIndex_uprimeSub_U
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
  have hNpos := lt_of_lt_of_le (mul_pos hp1 hrel)
    (OddOrder.Peterfalvi.S11.caseA_character_count_exact hG caseA)
  have hne : {φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter φ ∧ φ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    intro h0
    rw [h0, Nat.zero_mul] at hNpos
    exact absurd hNpos (lt_irrefl 0)
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
  obtain ⟨χ₁, hχ₁sOfU', hχ₁irr, hχ₁deg⟩ := hne
  have hχ₁S₂ : χ₁ ∈ S₂ :=
    hS₁sub ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hle hχ₁sOfU', hχ₁irr, hχ₁deg⟩
  -- ── `S₂` is finite; enumerate it and locate the anchor index
  have hSfin : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime).Finite :=
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite
        (K := (derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M)).subset
      (fun x hx => by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hS₂fin : S₂.Finite := hSfin.subset hS₂sub
  obtain ⟨k, χmem, hinj, hrange⟩ := OddOrder.Peterfalvi.S08.exists_finEnum_general hS₂fin
  have hmemS1set : ∀ j, χmem j ∈ S₂ := fun j => hrange ▸ Set.mem_range_self j
  have hχ₁mem : χ₁ ∈ Set.range χmem := hrange ▸ hχ₁S₂
  obtain ⟨i₁, hi₁eq⟩ := hχ₁mem
  subst hi₁eq
  -- ── the world-bridge `S₂ ⊆ 𝒮(H₀C′) ⊆ S(H₀C′) ⊆ S(⊥)` and the break memberships
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hS₂bot : S₂ ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx => hIKF (hS₂sub hx)
  have hmemfam : ∀ j, χmem j ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun j => hS₂bot (hmemS1set j)
  have hχsOf : OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)
      ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime := ⟨ζ, hζ, rfl⟩
  have hψB : OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := by
    rw [← hyp.SOf_eq]
    exact hyp.sOf_subset_SOf hyp.H0Cprime hχsOf
  have hχcnotS₂ : (OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)).conj ∉ S₂ := by
    intro hc
    apply hχnotS₂
    have h := hS₂conj hc
    rwa [ClassFunction.conj_conj] at h
  -- ── member degree ratios against the degree-`qa` anchor ((9.8.a))
  choose deg hdeg using fun j : Fin k =>
    caseA_sOf_source_degree_ratio caseA
      (show χmem j ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
          (hyp.chief.H0 ⊔ derivedInG hyp.C) from hS₂sub (hmemS1set j))
  have hdeg_anchor : ∀ j, (χmem j : ↥M → ℂ) 1 = (deg j : ℂ) * (χmem i₁ : ↥M → ℂ) 1 := by
    intro j
    rw [hdeg j, hχ₁deg]
    push_cast
    ring
  have ha1 : deg i₁ = 1 := by
    have h : hyp.s11Setup.q * caseA.a * 1 = hyp.s11Setup.q * caseA.a * deg i₁ := by
      rw [mul_one]
      exact Nat.cast_inj.mp (hχ₁deg.symm.trans (hdeg i₁))
    exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hq caseA.a_pos) h).symm
  -- ── the break ratio `e = d/a` against the anchor
  have hψdeg : (OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) : ↥M → ℂ) 1
      = (e : ℂ) * (χmem i₁ : ↥M → ℂ) 1 := by
    rw [hχdeg, hχ₁deg, he]
    push_cast
    ring
  -- ── the §11 grid decomposition supply ((5.2.d)/(5.2.e), issue 2022)
  have hnt : OddOrder.GroupTheory.TypePNontrivialCore M hyp.base.typeP :=
    OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV hyp.type_alt hyp.base.typeP
  have hsub : S₂ ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) ∪
      OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := fun x hx =>
    Or.inl (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime (hS₂sub hx))
  obtain ⟨Da, hDatau1, hdatum⟩ := hyp.base.sixTwoDecompositionData hG
    (hyp.params_mu_eq hG hG.odd) hyp.params_delta_pm
    (fun j hj => hyp.params_delta_sign hG hG.odd j hj)
    hyp.params_zeta_mem hyp.params_zeta_degree hyp.type_alt hnt
    ((OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
      (hyp.base.toTypesIIIIIIVSetup hyp.type_alt hnt)).choose)
    (hyp.H0Cprime.subgroupOf M) (hyp.H0Cprime.subgroupOf M)
    S₂ hS₂conj hsub cohS₂
    (OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ))
    hψB hχnotS₂ hχcnotS₂ (χmem i₁) (hmemS1set i₁) e hψdeg hnc
  choose Dfun hDorth hDtau using hdatum
  -- ── break-character fields, supports, integrality, generation (general kernel layer)
  obtain ⟨-, hψψne, hψbψbne, hψbψ, hψψb, hdiffsuppψ, hψ_S1, hψbar_S1⟩ :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_breakChar_fields hModd
      hyp.base.mderivSharp_subset_A0 hS₂bot hψB hχnotS₂ hχcnotS₂
  have hmemdegdiffsupp : ∀ i : Fin k, i ∈ (Finset.univ : Finset (Fin k)) →
      ((χmem i - deg i • χmem i₁).support ⊆ hyp.base.A0) := fun i _ =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
      hyp.base.mderivSharp_subset_A0 (hmemfam i) (hmemfam i₁) (hdeg_anchor i)
  have hdiffasuppψ : ((OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ))
        - e • χmem i₁).support ⊆ hyp.base.A0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
      hyp.base.mderivSharp_subset_A0 hψB (hmemfam i₁) hψdeg
  have htau1ψ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
      (hyp.base.dadeData.dade.fullDadeIsometryData hyp.base.hconj)
      ((OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
        (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ))
          - e • χmem i₁) ∈ ZIrr G := by
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.base.dadeData.dade hyp.base.hconj hdiffasuppψ ?_
    refine Submodule.sub_mem _
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hψB) ?_
    exact nsmul_mem (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hmemfam i₁)) e
  have hcover : ∀ x ∈ S₂, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧ χmem j = x := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen :=
    OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
      (s := (Finset.univ : Finset (Fin k))) (χmem := χmem) (deg := deg) (i₁ := i₁)
      hcover (Finset.mem_univ i₁) (fun j _ => hmemS1set j) hmemdegdiffsupp
  have hbar1 : ((OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)).conj : ↥M → ℂ) 1
      = (OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
        (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) : ↥M → ℂ) 1 := by
    rw [ClassFunction.conj_apply, hχdeg]
    exact star_natCast _
  have hχ₁ne : (χmem i₁ : ↥M → ℂ) 1 ≠ 0 := by
    rw [hχ₁deg]
    exact Nat.cast_ne_zero.mpr (Nat.mul_pos hq caseA.a_pos).ne'
  have hgen :=
    OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
      (χ := OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
        (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ))
      (chibar := (OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
        (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)).conj)
      (chi1 := χmem i₁) (a := e)
      hSgen hψdeg hbar1 hχ₁ne hyp.base.one_notMem_A0
  -- ── Gram data: positive real squared norms, weighted orthogonality, anchor norm `1`
  have hmcpos : ∀ j, 0 < (ClassFunction.inner (χmem j) (χmem j)).re := fun j =>
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hmemfam j)).2
  have hmemortho : ∀ i j, ClassFunction.inner (χmem i) (χmem j)
      = @ite ℂ (i = j) (Classical.propDecidable (i = j))
          (((ClassFunction.inner (χmem i) (χmem i)).re : ℝ) : ℂ) 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hmemfam i)).1
    · rw [if_neg hij]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hmemfam i) (hmemfam j) (fun h => hij (hinj h))
  have hanchorNorm : (ClassFunction.inner (χmem i₁) (χmem i₁)).re = 1 := by
    have hval : ClassFunction.inner (χmem i₁) (χmem i₁) = 1 := by
      have h := irreducibleCharacter_inner_eq_ite
        (⟨χmem i₁, hχ₁irr⟩ : IrreducibleCharacter ↥M) ⟨χmem i₁, hχ₁irr⟩
      rwa [if_pos rfl] at h
    rw [hval, Complex.one_re]
  -- ── fire the norm-weighted (5.6) engine (contrapositive of `xAdjoinStepW_k`)
  have hbound := OddOrder.Peterfalvi.S08.coherentDegreeSqNormBound_of_not_coherentW_k
    hyp.base.dadeData.dade hyp.base.hconj cohS₂
    (OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ))
    hdiffsuppψ hψψne hψbψbne hψψb hψbψ hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    hmemdegdiffsupp (fun j _ => hmemS1set j)
    (fun j => (ClassFunction.inner (χmem j) (χmem j)).re) (fun j _ => hmcpos j)
    (fun i _ j _ => hmemortho i j) hanchorNorm
    (fun i _ => Dfun (χmem i) (hmemS1set i))
    Da hDatau1
    (fun i _ => hDorth (χmem i) (hmemS1set i))
    (fun i _ => hDtau (χmem i) (hmemS1set i))
    hdiffasuppψ htau1ψ ha1 hSgen hgen hnc
  -- ── rescale: `sumnS F ≤ sumnS S₂ = (qa)²·∑ deg²/‖·‖² ≤ (qa)²·2·e = 2q²a·d`
  intro F hF
  have hFsub : F ⊆ hS₂fin.toFinset := fun ψ hψ => hS₂fin.mem_toFinset.mpr (hF hψ)
  have henum : OddOrder.Peterfalvi.S07.sumnS hS₂fin.toFinset
      = ∑ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j) := by
    rw [OddOrder.Peterfalvi.S07.sumnS,
      show hS₂fin.toFinset = (Set.range χmem).toFinset by
        ext ψ; rw [Set.Finite.mem_toFinset, Set.mem_toFinset, hrange],
      OddOrder.Peterfalvi.S08.sum_toFinset_range_eq hinj]
  have hsnorm : ∀ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j)
      = ((deg j : ℝ) * ((hyp.s11Setup.q * caseA.a : ℕ) : ℝ)) ^ 2
        / (ClassFunction.inner (χmem j) (χmem j)).re := by
    intro j
    unfold OddOrder.Peterfalvi.S07.Snorm
    congr 1
    rw [hdeg j, Complex.natCast_re]
    push_cast
    ring
  calc OddOrder.Peterfalvi.S07.sumnS F
      ≤ OddOrder.Peterfalvi.S07.sumnS hS₂fin.toFinset :=
        OddOrder.Peterfalvi.S07.sumnS_le_of_subset hFsub
    _ = ∑ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j) := henum
    _ = ∑ j : Fin k, ((deg j : ℝ) * ((hyp.s11Setup.q * caseA.a : ℕ) : ℝ)) ^ 2
          / (ClassFunction.inner (χmem j) (χmem j)).re :=
        Finset.sum_congr rfl (fun j _ => hsnorm j)
    _ = ((hyp.s11Setup.q * caseA.a : ℕ) : ℝ) ^ 2
          * ∑ j : Fin k, (deg j : ℝ) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ((hyp.s11Setup.q * caseA.a : ℕ) : ℝ) ^ 2 * (2 * (e : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) := by
        rw [he]
        push_cast
        ring

/-! ### The (9.11.2) two-summand inertia inputs at the `Hypothesis` level (issue 9083, Phase B)

Book (9.11.2): *"if `w ∈ W₁^#` then `U₁ ∩ U₁^w = C`; moreover `u ≤ a²`."*  The S11-level identity
is landed as `S11.nineElevenTwo_two_summand_inertia` (`S11_NineElevenTwoSummand`); this section
instantiates it in the `NineElevenEqualityRefutation` hypothesis budget, discharging its
degree-dichotomy input from the two configuration degree facts: the landed squeeze output
`hS3deg` (every `𝒮₃`-member has degree `qu`) and the Phase-E `𝒮₂ = 𝒮₁` extraction `hS2deg`
(every `𝒮₂`-member has degree `qa`, recoverable from the saturated bound since any
non-degree-`qa` member adds `Snorm` beyond the equality).  The outputs are **exactly** the
`hK₁`/`hK₂`/`hCinf` inputs of `S11.nineElevenCaseA_equality_refutation`; the remaining distance
to `NineElevenEqualityRefutation` is Phases C ((9.11.3) `hclass`/`hn`), D ((9.11.4) `hnorm`),
and E ((9.11.5-8) `hle` + the `𝒮₂ = 𝒮₁` extraction consumed here). -/

/-- **Peterfalvi (9.11.2) at the `Hypothesis` level: the two-summand inertia inputs** (issue 9083
Phase B).  In the equality configuration — given the landed `𝒮₃`-degree fact `hS3deg` and the
Phase-E `𝒮₂`-degree extraction `hS2deg` — there are `K₁, K₂` (the single-factor centralizers
`C_U(H_i)`, `C_U(H_j)` of two Clifford summands, or their common value) with
`[U:K₁] = [U:K₂] = a` and `C = K₁ ⊓ K₂`, exactly the (9.11.2) inputs consumed by
`S11.nineElevenCaseA_equality_refutation` (through `S11.nineElevenTwo_u_le_a_sq`, giving
`u ≤ a²`).

The degree dichotomy for `S11.nineElevenTwo_two_summand_inertia` is assembled by locating each
`𝒮(H₀C)`-member inside `𝒮(H₀C′)` (`S11.sOf_antitone` along `H₀C′ ≤ H₀C`, i.e. `C′ ≤ C` via the
§11/§9 kernel identification `C_eq_cSub`) and splitting on `𝒮₂`-membership. -/
theorem caseA_two_summand_inertia_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS3deg : ∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q *
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ))
    (hS2deg : ∀ χ ∈ S₂,
      (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)) :
    ∃ K₁ K₂ : Subgroup G,
      K₁.relIndex hyp.s11Setup.U = caseA.a ∧ K₂.relIndex hyp.s11Setup.U = caseA.a ∧
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C = K₁ ⊓ K₂ := by
  haveI := hyp.base.finiteG
  refine OddOrder.Peterfalvi.S11.nineElevenTwo_two_summand_inertia caseA ?_
  intro φ hφ
  -- `𝒮(H₀C) ⊆ 𝒮(H₀C′)` along `H₀C′ ≤ H₀C` (`C′ = [C,C] ≤ C`, `C = cSub` by `C_eq_cSub`)
  have hle : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
    show hyp.chief.H0 ⊔ derivedInG hyp.C ≤ _
    refine sup_le_sup_left ?_ hyp.chief.H0
    rw [C_eq_cSub hG hyp]
    exact OddOrder.Peterfalvi.S11.cprimeSub_le_C hyp.s11Setup hyp.chief
  have hφ' : φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime :=
    OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hle hφ
  by_cases hφS₂ : φ ∈ S₂
  · exact Or.inr (hS2deg φ hφS₂)
  · exact Or.inl (hS3deg φ ⟨hφ', hφS₂⟩)

/-! ### The (9.11.3) count inputs at the `Hypothesis` level (issue 9083, Phase C)

Book (9.11.3): *"`|𝒮₄| = (1/q)·(((p^q−1)−(p−1)q)/u − (p−1))`"*.  The S11-level orbit split is
landed as `S11.nineElevenThree_orbit_split` (`S11_NineElevenCoherence`); this section instantiates
it in the `NineElevenEqualityRefutation` hypothesis budget, producing **exactly** the
`hclass`/`hn` inputs of `S11.nineElevenCaseA_equality_refutation` at `n = |𝒮₄|·q + (p−1)` (so
`hn` is `rfl`), with `𝒮₄` pinned to the concrete member family `nineElevenSFour`.  Together with
the Phase-B inertia inputs (`caseA_two_summand_inertia_inputs`) this closes the assembler chain:
`nineElevenEqualityRefutation_of_sTwoExtraction_normBound` reduces the remaining distance to
`NineElevenEqualityRefutation` to the two named Phase-D/E `Prop`s `NineElevenSTwoExtraction`
((9.11.1) equality forcing `𝒮₂ = 𝒮₁`) and `NineElevenNormBound` ((9.11.4) Mackey norm +
(9.11.5)–(9.11.8) `|𝒮₄| ≤ ‖α‖²`). -/

/-- **Peterfalvi (9.11.3)'s family `𝒮₄`**: the irreducible members of `𝒮₃ ∩ 𝒮(H₀C)`, i.e. the
irreducible members of `𝒮(H₀C)` outside the maximal coherent `𝒮₂` (since `𝒮(H₀C) ⊆ 𝒮(H₀C′)`,
"`∈ 𝒮₃`" is "`∉ 𝒮₂`" there).  Its cardinality is the `S4` of the (9.11.3) count
(`caseA_nineElevenThree_count_inputs`) and of the (9.11.5)–(9.11.8) bound `|𝒮₄| ≤ ‖α‖²`
(`NineElevenNormBound`). -/
noncomputable def nineElevenSFour [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (S₂ : Set (ClassFunction ↥M ℂ)) : Set (ClassFunction ↥M ℂ) :=
  {φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief) |
    IsIrreducibleCharacter φ ∧ φ ∉ S₂}

/-- **Peterfalvi (9.11.3) at the `Hypothesis` level: the count inputs** (issue 9083 Phase C).

In the equality configuration — the degree-`qa` base subfamily inside `𝒮₂` (`hS₁sub`), the landed
`𝒮₃`-degree fact `hS3deg`, the Phase-E `𝒮₂`-degree extraction `hS2deg`, `C = U′` (`hCUprime`),
and the (9.8.d) count equality (`hcount`) — the `𝒳(H₀C)` class equation holds with the
degree-`u` character count already split into `W₁`-orbits:

`u + (|𝒮₄|·q + (p−1))·u² + q·(p−1)·u = p^q·u`.

This is `S11.nineElevenCaseA_equality_refutation`'s `hclass` at `n = |𝒮₄|·q + (p−1)`, making its
`hn` input definitional (`rfl`); `S4 = (nineElevenSFour hyp S₂).ncard` is the same cardinality
that the (9.11.5)–(9.11.8) bound `hle : S4 ≤ N` (`NineElevenNormBound`) must control.  The
`𝒮(H₀C′)`-level hypotheses are moved to the §9 families via `S11.sOf_antitone` along
`H₀C′ ≤ H₀U′` (derived-subgroup monotonicity) and `H₀C′ ≤ H₀C` (`C_eq_cSub`). -/
theorem caseA_nineElevenThree_count_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS₁sub : {φ : ClassFunction ↥M ℂ |
        φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
        IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ))} ⊆ S₂)
    (hS3deg : ∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q *
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ))
    (hS2deg : ∀ χ ∈ S₂,
      (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ))
    (hCUprime : (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C
      = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Uprime)
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
        (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
        IsIrreducibleCharacter χ ∧
        χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
      = (hyp.chief.p - 1)
        * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U)) :
    (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
      + ((nineElevenSFour hyp S₂).ncard * hyp.s11Setup.q + (hyp.chief.p - 1))
        * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u ^ 2
      + hyp.s11Setup.q * (hyp.chief.p - 1)
        * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
      = hyp.chief.p ^ hyp.s11Setup.q
        * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u := by
  haveI := hyp.base.finiteG
  classical
  -- `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′`), as in `caseA_refuter_of_equality_refutation`
  have hCUle : hyp.C ≤ hyp.s11Setup.U := by
    show hyp.C ≤ hyp.s11Setup.typeP.U
    rw [hyp.setup_typeP_eq]; exact hyp.C_le_U
  have hleU' : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := by
    show hyp.chief.H0 ⊔ derivedInG hyp.C
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
    refine sup_le_sup_left ?_ hyp.chief.H0
    show derivedInG hyp.C ≤ derivedInG hyp.s11Setup.U
    rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.C,
      OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.s11Setup.U]
    exact Subgroup.commutator_mono hCUle hCUle
  -- `H₀C′ ≤ H₀C` (`C′ ≤ C`, `C = cSub` by `C_eq_cSub`), as in the Phase-B corollary
  have hleC : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
    show hyp.chief.H0 ⊔ derivedInG hyp.C ≤ _
    refine sup_le_sup_left ?_ hyp.chief.H0
    rw [C_eq_cSub hG hyp]
    exact OddOrder.Peterfalvi.S11.cprimeSub_le_C hyp.s11Setup hyp.chief
  -- the S11-level hypothesis shapes
  have hS₁'sub : {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter χ ∧
      χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)} ⊆ S₂ := fun χ hχ =>
    hS₁sub ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hleU' hχ.1, hχ.2.1, hχ.2.2⟩
  have hS3deg' : ∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief), χ ∉ S₂ →
      χ 1 = ((hyp.s11Setup.q *
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ) :=
    fun χ hχ hnot =>
      hS3deg χ ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hleC hχ, hnot⟩
  exact OddOrder.Peterfalvi.S11.nineElevenThree_orbit_split hG caseA
    hS₁'sub hS3deg' hS2deg hCUprime hcount

/-- **Peterfalvi (9.11.1), the `𝒮₂ = 𝒮₁` extraction** (hypothesis shape, issue 9083 Phase E
remainder).  Book (9.11.1): *"Furthermore, the inequalities above are equalities.  Then
`𝒮₂ = 𝒮₁ ∩ 𝒮(H₀U′) ∩ Irr(M)`.  Therefore … `𝒮₂ = 𝒮₁`"* — at the saturated bound
`sumnS 𝒮₂ ≤ 2q²au` every `𝒮₂`-member must have degree `qa`, since the degree-`qa` subfamily
`𝒮₁′` alone already meets the bound (`(p−1)·[U:U′]·q² = 2q²au` at the equality configuration)
and any additional member contributes positive `Snorm`.  This is the degree fact consumed by the
(9.11.2) inertia inputs (`caseA_two_summand_inertia_inputs`) and the (9.11.3) count
(`caseA_nineElevenThree_count_inputs`). -/
def NineElevenSTwoExtraction [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
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
          (S₂ ∪ {χ, χ.conj}) hyp.base.A0)) →
      2 * caseA.a = hyp.chief.p - 1 →
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C
        = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Uprime →
      (∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
        (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q *
          (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ)) →
      {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
          (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
          IsIrreducibleCharacter χ ∧
          χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
        = (hyp.chief.p - 1)
          * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U) →
      (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ)
          * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℝ)) →
      ∀ χ ∈ S₂, (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)

/-- **Peterfalvi (9.11.4)–(9.11.8), the norm bound** (hypothesis shape, issue 9083 Phases D/E).
Book: **(9.11.4)** `α = Ind_{HU₁}^M 1 − ψ₁` has `Supp(α) ⊆ A(M)` and
`‖α‖² = a + 1 + (q−1)a²/u` — in cleared form `N·u = (a+1)·u + (q−1)·a²` with `N = ‖α‖² ∈ ℕ`
(the `‖α‖² = ‖γ‖² + 1` reduction is landed as `cfnorm_sub_irreducible_orthogonal`, the `‖γ‖²`
Mackey double-coset count runs through the (9.11.2) identity `U₁ ∩ U₁ʷ = C`); **(9.11.5)–(9.11.8)**
every `ξ ∈ 𝒮₄` with `⟨α^τ, ξ^τ⟩ ≠ 0` would let the pair `{ξ, ξ̄}` be coherently adjoined
(the (9.11.6)–(9.11.8) construction), contradicting the pair clause — so distinct `𝒮₄`-members
consume orthogonal unit slices of `α^τ` and `|𝒮₄| ≤ ‖α^τ‖² = ‖α‖² = N`. -/
def NineElevenNormBound [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
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
          (S₂ ∪ {χ, χ.conj}) hyp.base.A0)) →
      2 * caseA.a = hyp.chief.p - 1 →
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C
        = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Uprime →
      (∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
        (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q *
          (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ)) →
      {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
          (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
          IsIrreducibleCharacter χ ∧
          χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
        = (hyp.chief.p - 1)
          * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U) →
      (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ)
          * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℝ)) →
      (∀ χ ∈ S₂, (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)) →
      ∃ N : ℕ,
        N * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
          = (caseA.a + 1) * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
            + (hyp.s11Setup.q - 1) * caseA.a ^ 2 ∧
        (nineElevenSFour hyp S₂).ncard ≤ N

/-- **Peterfalvi (9.11.2)–(9.11.5): the equality refutation, reduced to the Phase-D/E remainders**
(issue 9083 Phase C assembler).  With Phases B ((9.11.2) `caseA_two_summand_inertia_inputs`) and
C ((9.11.3) `caseA_nineElevenThree_count_inputs`) landed, `NineElevenEqualityRefutation` follows
from the two remaining named inputs: the `𝒮₂ = 𝒮₁` degree extraction (`NineElevenSTwoExtraction`,
Phase E) and the `|𝒮₄| ≤ ‖α‖²` norm bound (`NineElevenNormBound`, Phases D + E).  The spine is
`S11.nineElevenCaseA_equality_refutation`, whose `hn` is definitional here (`n = |𝒮₄|·q + (p−1)`
by construction), with `3 ≤ q` (odd prime), `1 ≤ u` (`u_odd`), and `p = 2a+1` (from the squeeze
output `2a = p−1`) supplied on the spot. -/
theorem nineElevenEqualityRefutation_of_sTwoExtraction_normBound [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (hext : NineElevenSTwoExtraction hyp caseA)
    (hnb : NineElevenNormBound hyp caseA) :
    NineElevenEqualityRefutation hyp caseA := by
  haveI := hyp.base.finiteG
  classical
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg hcount hFbound
  -- Phase-E remainders
  have hS2deg := hext S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg
    hcount hFbound
  obtain ⟨N, hnorm, hleN⟩ := hnb S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime
    hS3deg hcount hFbound hS2deg
  -- Phase B: the (9.11.2) inertia inputs
  obtain ⟨K₁, K₂, hK₁, hK₂, hCinf⟩ :=
    caseA_two_summand_inertia_inputs hG hyp caseA hS3deg hS2deg
  -- Phase C: the (9.11.3) count inputs
  have hclass := caseA_nineElevenThree_count_inputs hG hyp caseA hS₁sub hS3deg hS2deg
    hCUprime hcount
  -- numeric side conditions: `q` odd prime `≥ 3`, `u ≥ 1`, `p = 2a + 1`
  have hqp : (hyp.s11Setup.q).Prime := hyp.s11Setup.nontrivial.2.1
  have hqodd : Odd hyp.s11Setup.q :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.s11Setup.typeP.W1)
  have hq3 : 3 ≤ hyp.s11Setup.q := by
    obtain ⟨k, hk⟩ := hqodd
    have h2 := hqp.two_le
    omega
  have hu : 1 ≤ (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u :=
    (OddOrder.Peterfalvi.S11.u_odd hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)).pos
  have hp1 : 1 < hyp.chief.p := hyp.chief.p_prime.one_lt
  have hpeq : hyp.chief.p = 2 * caseA.a + 1 := by omega
  exact OddOrder.Peterfalvi.S11.nineElevenCaseA_equality_refutation caseA hq3 hu hpeq
    hK₁ hK₂ hCinf hclass rfl hnorm hleN

/-! ### The (9.11.4) norm inputs at the `Hypothesis` level (issue 9083, Phase D)

Book (9.11.4): *"Let `ψ₁ ∈ 𝒮₁`, let `γ = Ind_{HU₁}^M 1` and let `α = γ − ψ₁`.  Then
`Supp(α) ⊆ A(M)` and `‖α‖² = a + 1 + (q−1)a²/u`"*.  The S11-level content is landed in
`S11_NineElevenMackeyNorm` (`nineElevenGamma_*`: support, degree, orthogonality, and the
Mackey conjugation count under the (9.11.2) TI-witness); this section instantiates it in
the equality configuration, choosing `ψ₁` from the (9.8.d)-positive degree-`qa` family and
producing the **cleared norm identity with its integrality**:

`∃ N, N·u = (a+1)·u + (q−1)·a²` realized by a genuine `A₀`-supported virtual character `α`
with `‖α‖² = N`.  This is the (9.11.4) half of `NineElevenNormBound`; the remaining
(9.11.5)–(9.11.8) half is the bound `|𝒮₄| ≤ N = ‖α‖²` (Phase E), which consumes the same
`α` through the Dade isometry (`α ∈ ℤ[Irr M]`, `Supp(α) ⊆ A₀`, so `α^τ` is defined and
`‖α^τ‖² = N`). -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.4) at the `Hypothesis` level** (issue 9083 Phase D): in the equality
configuration (`C = U′`, the (9.8.d) count equality) and given the (9.11.2) TI-witness
(`NineElevenTwoTIWitness`), there is `N : ℕ` with

`N·u = (a+1)·u + (q−1)·a²`

realized as `N = ‖α‖²` for a virtual character `α = γ − ψ₁ ∈ ℤ[Irr M]` supported in
`A₀(M)` — the book's `α` for `ψ₁ ∈ 𝒮₁` and `γ = Ind_{HU₁}^M 1`.  Support: both `γ` and
`ψ₁` are supported in `HU = M′` (`nineElevenGamma_support`,
`support_induce_subset_of_normal`), the value at `1` cancels (`γ(1) = qa = ψ₁(1)`), and
`(M′)^# ⊆ A₀(M)` (`mderivSharp_subset_A0` — in this formalization `A(M) = (M′)^#` is a
theorem, so the Coq gap-patch `PFsection9.v:1476-1483` is not needed).  Norm:
`‖α‖² = ‖γ‖² + 1` (`cfnorm_sub_irreducible_orthogonal`, orthogonality from the
averaging-projector engine at the source `H ⊄ Ker ζ`), and `‖γ‖²·u = a·u + (q−1)·a²`
(`nineElevenGamma_inner_self_mul_u`, the Mackey count).  Integrality: `α ∈ ℤ[Irr M]` has
`‖α‖²` a sum of squares of integers (`mem_ZIrr_inner_self_eq_sum_sq`). -/
theorem caseA_nineElevenFour_norm_inputs [Finite G]
    {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    (htw : OddOrder.Peterfalvi.S11.NineElevenTwoTIWitness caseA)
    (hCUprime : (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C
      = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Uprime)
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
        (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
        IsIrreducibleCharacter χ ∧
        χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
      = (hyp.chief.p - 1)
        * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U)) :
    ∃ N : ℕ,
      N * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
        = (caseA.a + 1) * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
          + (hyp.s11Setup.q - 1) * caseA.a ^ 2 ∧
      ∃ α : ClassFunction ↥M ℂ,
        α ∈ OddOrder.RepresentationTheory.ZIrr ↥M ∧
        α.support ⊆ hyp.base.A0 ∧
        ClassFunction.inner α α = (N : ℂ) := by
  haveI := hyp.base.finiteG
  classical
  obtain ⟨U₁, hCU₁, hU₁U, hU₁a, hTI⟩ := htw
  -- `U′ ≤ U₁` from the equality configuration `C = U′` (`chars.C = cSub`, `chars.Uprime =
  -- uprimeSub` definitionally)
  have hUpC : OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
      = OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
    have h : OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief
        = OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := hCUprime
    exact h.symm
  have hUpU₁ : OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup ≤ U₁ := by
    rw [hUpC]; exact hCU₁
  -- `ψ₁ ∈ 𝒮₁`: the degree-`qa` irreducible family is nonempty by the (9.8.d) count
  have hrelne : (OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U
      ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hcne : {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter χ ∧
      χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have hp1 : 1 < hyp.chief.p := hyp.chief.p_prime.one_lt
    have := Nat.pos_of_ne_zero hrelne
    have : 0 < (hyp.chief.p - 1)
        * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U) :=
      Nat.mul_pos (by omega) this
    omega
  obtain ⟨ψ₁, hψ₁sOf, hψ₁irr, hψ₁deg⟩ := Set.nonempty_of_ncard_ne_zero hcne
  obtain ⟨ζ, hζmem, hψ₁eq⟩ := hψ₁sOf
  have hζxi : ζ ∈ OddOrder.Peterfalvi.S11.xiSet hyp.s11Setup :=
    OddOrder.Peterfalvi.S11.xiOf_subset_xiSet hyp.s11Setup _ hζmem
  -- `γ = Ind_{HU₁}^M 1` and its landed (9.11.4) facts
  set K : Subgroup ↥M := hyp.s11Setup.H.subgroupOf M ⊔ U₁.subgroupOf M with hKdef
  set γ : ClassFunction ↥M ℂ :=
    ClassFunction.induce K (trivialClassFunction ↥K) with hγdef
  have hγsupp : γ.support ⊆ (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup : Set ↥M) :=
    OddOrder.Peterfalvi.S11.nineElevenGamma_support hyp.s11Setup hU₁U
  have hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥M :=
    OddOrder.Peterfalvi.S11.nineElevenGamma_mem_ZIrr hyp.s11Setup U₁
  have hγ1 : γ (1 : ↥M) = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ) :=
    OddOrder.Peterfalvi.S11.nineElevenGamma_apply_one hyp.s11Setup hU₁U hU₁a
  have hγγu : ClassFunction.inner γ γ
        * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℂ)
      = ((caseA.a * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
          + (hyp.s11Setup.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) :=
    OddOrder.Peterfalvi.S11.nineElevenGamma_inner_self_mul_u
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) hU₁U hUpU₁ hU₁a hTI
  -- `induceHU` agrees with the scoped-instance induction term
  have hindEq : OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
        (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)
      = ClassFunction.induce (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)
        (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) := rfl
  -- orthogonality `⟨γ, ψ₁⟩ = 0` and the norm split `‖α‖² = ‖γ‖² + 1`
  have hγψ : ClassFunction.inner γ ψ₁ = 0 := by
    rw [hψ₁eq, hindEq]
    exact OddOrder.Peterfalvi.S11.nineElevenGamma_inner_induceHU hyp.s11Setup hU₁U hζxi
  have hαα : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) = ClassFunction.inner γ γ + 1 :=
    OddOrder.Peterfalvi.S11.cfnorm_sub_irreducible_orthogonal hψ₁irr hγψ
  -- `α ∈ ℤ[Irr M]` and the integrality of `‖α‖²`
  have hαZIrr : γ - ψ₁ ∈ OddOrder.RepresentationTheory.ZIrr ↥M := by
    refine Submodule.sub_mem _ hγZIrr ?_
    rw [hψ₁eq]
    exact OddOrder.Peterfalvi.S11.induceHU_mem_ZIrr hyp.s11Setup ζ
  obtain ⟨c, -, -, hcsum⟩ :=
    OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq hαZIrr
  have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmval : ClassFunction.inner (γ - ψ₁) (γ - ψ₁)
      = ((∑ x ∈ c.support, (c x) ^ 2 : ℤ) : ℂ) := by
    rw [hcsum]
    push_cast
    rfl
  set N : ℕ := (∑ x ∈ c.support, (c x) ^ 2).toNat with hNdef
  have hNval : ((N : ℕ) : ℂ) = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) := by
    rw [hmval, hNdef]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)
  refine ⟨N, ?_, γ - ψ₁, hαZIrr, ?_, hNval.symm⟩
  · -- the cleared norm identity `N·u = (a+1)·u + (q−1)·a²`, by `ℕ`-cast injectivity
    have h2 : ClassFunction.inner (γ - ψ₁) (γ - ψ₁)
          * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℂ)
        = ((caseA.a * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
            + (hyp.s11Setup.q - 1) * caseA.a ^ 2 : ℕ) : ℂ)
          + ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℂ) := by
      rw [hαα, add_mul, one_mul, hγγu]
    have h3 : ((N * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ)
        = (((caseA.a + 1)
              * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u
            + (hyp.s11Setup.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) := by
      push_cast at h2 ⊢
      rw [hNval]
      linear_combination h2
    exact Nat.cast_injective h3
  · -- `Supp(α) ⊆ A₀(M)`: both parts supported in `HU = M′`, value at `1` cancels
    intro x hx
    have hxmem : x ∈ γ.support ∪ ψ₁.support :=
      ClassFunction.support_sub_subset γ ψ₁ hx
    have hxHU : x ∈ OddOrder.Peterfalvi.S11.huSub hyp.s11Setup := by
      rcases hxmem with h | h
      · exact hγsupp h
      · have hψsupp : ψ₁.support
            ⊆ (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup : Set ↥M) := by
          rw [hψ₁eq, hindEq]
          exact ClassFunction.support_induce_subset_of_normal _ _
        exact hψsupp h
    have hx1 : x ≠ 1 := by
      intro h1
      rw [ClassFunction.mem_support, h1] at hx
      apply hx
      rw [ClassFunction.sub_apply, hγ1, hψ₁deg, sub_self]
    have hxM' : x ∈ (derivedInG M).subgroupOf M := by
      rwa [← OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf]
    exact hyp.base.mderivSharp_subset_A0 x hxM' hx1

end OddOrder.Peterfalvi.S13
