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

end OddOrder.Peterfalvi.S13
