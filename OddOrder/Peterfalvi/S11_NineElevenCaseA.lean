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
import OddOrder.Peterfalvi.S11_NineElevenTIWitness
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
    change hyp.C ≤ hyp.s11Setup.typeP.U
    rw [hyp.setup_typeP_eq]; exact hyp.C_le_U
  have hle : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
    refine sup_le_sup_left ?_ hyp.chief.H0
    change derivedInG hyp.C ≤ derivedInG hyp.s11Setup.U
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
  `a ∣ (source degree)` (`S11.caseA_sOf_source_degree_ratio`, Coq `a_dv_XH0`), anchor ratio `1`,
  break ratio `χ(1)/χ₁(1) = d/a`;
* Gram data (orthogonality, positive squared norms), scaled-difference supports, `ZIrr`
  integrality, and the two generation clauses from the general kernel-family layer
  (`S08_SixTwoGeneral`, as in `inducedKernelFamily_degreeSqNormReBound_of_break_k`);
* the break decomposition `Da` and the per-member (5.2.d)/(5.2.e) R-data from the §11 grid
  supply `S12.sixTwoDecompositionData` (issue 2022);

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
      (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ))
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    ∃ K₁ K₂ : Subgroup G,
      K₁.relIndex hyp.s11Setup.U = caseA.a ∧ K₂.relIndex hyp.s11Setup.U = caseA.a ∧
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C = K₁ ⊓ K₂ := by
  haveI := hyp.base.finiteG
  refine OddOrder.Peterfalvi.S11.nineElevenTwo_two_summand_inertia caseA ?_
  intro φ hφ
  -- `𝒮(H₀C) ⊆ 𝒮(H₀C′)` along `H₀C′ ≤ H₀C` (`C′ = [C,C] ≤ C`, `C = cSub` by `C_eq_cSub`)
  have hle : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C ≤ _
    refine sup_le_sup_left ?_ hyp.chief.H0
    rw [C_eq_cSub_of_noncoherent hG hyp hncH0C htype]
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
        * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U))
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
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
    change hyp.C ≤ hyp.s11Setup.typeP.U
    rw [hyp.setup_typeP_eq]; exact hyp.C_le_U
  have hleU' : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
    refine sup_le_sup_left ?_ hyp.chief.H0
    change derivedInG hyp.C ≤ derivedInG hyp.s11Setup.U
    rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.C,
      OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.s11Setup.U]
    exact Subgroup.commutator_mono hCUle hCUle
  -- `H₀C′ ≤ H₀C` (`C′ ≤ C`, `C = cSub` by `C_eq_cSub`), as in the Phase-B corollary
  have hleC : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C ≤ _
    refine sup_le_sup_left ?_ hyp.chief.H0
    rw [C_eq_cSub_of_noncoherent hG hyp hncH0C htype]
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

/-- **Every `𝒮`-member has positive `Snorm` weight**: `Snorm χ = (χ(1).re)²/⟨χ,χ⟩.re` with
`χ(1) = q·d` a positive natural degree (member dictionary) and `⟨χ,χ⟩.re > 0`
(`inducedKernelFamily_inner_self_real_pos`). -/
theorem sOf_mem_Snorm_pos [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {Y : Subgroup G} {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup Y) :
    0 < OddOrder.Peterfalvi.S07.Snorm χ := by
  haveI := hyp.base.finiteG
  classical
  have hIKF : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (Y.subgroupOf M) := by
    rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf Y hχ
  have hpos := OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hIKF
  obtain ⟨ζ, hζ, rfl⟩ := hχ
  obtain ⟨dζ, hdpos, hdζ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ζ
  have hq : 0 < hyp.s11Setup.q := hyp.s11Setup.nontrivial.2.1.pos
  have hdeg : (OddOrder.Peterfalvi.S11.induceHU hyp.s11Setup
      (ζ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) : ↥M → ℂ) 1
      = ((hyp.s11Setup.q * dζ : ℕ) : ℂ) := by
    rw [OddOrder.Peterfalvi.S11.induceHU_apply_one_eq_q_mul, hdζ]
    push_cast
    ring
  unfold OddOrder.Peterfalvi.S07.Snorm
  apply div_pos
  · rw [hdeg, Complex.natCast_re]
    exact pow_pos (Nat.cast_pos.mpr (Nat.mul_pos hq hdpos)) 2
  · exact hpos.2

/-- **Peterfalvi (9.11.1), `𝒮₂ = 𝒮₁` — the saturated-bound subset form** (issue 9083 Phase E,
Coq `eqS12`): at the equality configuration the maximal coherent `𝒮₂` is *contained in* the
degree-`qa` irreducible cut `𝒮₁′` of `𝒮(H₀U′)`.  `𝒮₁′ ⊆ 𝒮₂` (`hS₁sub` + `sOf_antitone`)
already saturates the bound `2q²au` exactly (`sumnS_irreducible_constant_degree` + the
(9.8.d) count equality at `C = U′`, `2a = p−1`), so a member outside `𝒮₁′` would add its
positive `Snorm` (`sOf_mem_Snorm_pos`) beyond `hFbound`. -/
theorem caseA_sTwo_subset_degreeQaCut [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS₁sub : {φ : ClassFunction ↥M ℂ |
        φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
        IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ))} ⊆ S₂)
    (hS₂sub : S₂ ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (h2a : 2 * caseA.a = hyp.chief.p - 1)
    (hCUprime : (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).C
      = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Uprime)
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
        (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
        IsIrreducibleCharacter χ ∧
        χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
      = (hyp.chief.p - 1)
        * ((OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U))
    (hFbound : ∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ)
        * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℝ)) :
    S₂ ⊆ {χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
        (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter χ ∧ χ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)} := by
  haveI := hyp.base.finiteG
  classical
  intro χ hχS₂
  by_contra hnot
  -- make the cut `𝒮₁′` an atom so cast rewrites cannot enter its set-builder
  set S1' : Set (ClassFunction ↥M ℂ) := {φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup
      (hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup) |
      IsIrreducibleCharacter φ ∧
      φ 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ)} with hS1'def
  -- `H₀C′ ≤ H₀U′` and `𝒮₁′ ⊆ 𝒮₂` (as in `caseA_refuter_of_equality_refutation`)
  have hCU : hyp.C ≤ hyp.s11Setup.U := by
    change hyp.C ≤ hyp.s11Setup.typeP.U
    rw [hyp.setup_typeP_eq]; exact hyp.C_le_U
  have hle : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup
    refine sup_le_sup_left ?_ hyp.chief.H0
    change derivedInG hyp.C ≤ derivedInG hyp.s11Setup.U
    rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.C,
      OddOrder.Peterfalvi.S11.derivedInG_eq_commutator hyp.s11Setup.U]
    exact Subgroup.commutator_mono hCU hCU
  have hS1'sub : S1' ⊆ S₂ := fun φ hφ =>
    hS₁sub ⟨OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hle hφ.1, hφ.2.1, hφ.2.2⟩
  have hSfin : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime).Finite :=
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite
        (K := (derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M)).subset
      (fun x hx => by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hS1'fin : S1'.Finite := hSfin.subset fun φ hφ => hS₂sub (hS1'sub hφ)
  -- `sumnS 𝒮₁′ = |𝒮₁′|·(qa)²` (norm-one irreducibles of uniform degree `qa`)
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ) * ((hyp.s11Setup.q * caseA.a : ℕ) : ℝ) ^ 2 :=
    OddOrder.Peterfalvi.S11.sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  -- the count at `C = U′`: `|𝒮₁′|·a² = 2a·u` in `ℕ`
  have hrelu : (OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup).relIndex hyp.s11Setup.U
      = (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u := by
    have hUpC : OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief
        = OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := hCUprime
    rw [← hUpC]
    exact OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u _
  have hcount' : S1'.ncard * (caseA.a * caseA.a)
      = 2 * caseA.a
        * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u := by
    rw [hcount, hrelu, ← h2a]
  -- `𝒮₁′` alone saturates the bound: `sumnS 𝒮₁′ = 2q²au` in `ℝ`
  have hsatur : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = 2 * (hyp.s11Setup.q : ℝ) ^ 2 * (caseA.a : ℝ)
        * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℝ) := by
    have hcast : ((S1'.ncard : ℝ)) * ((caseA.a : ℝ) * (caseA.a : ℝ))
        = 2 * (caseA.a : ℝ)
          * ((hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcount'
    rw [hsum1', ← Set.ncard_eq_toFinset_card _ hS1'fin, Nat.cast_mul]
    linear_combination ((hyp.s11Setup.q : ℝ) ^ 2) * hcast
  -- the offending member: `χ ∈ 𝒮₂ ∖ 𝒮₁′` adds positive `Snorm` beyond the saturated bound
  have hχnot : χ ∉ hS1'fin.toFinset := fun hmem => hnot (hS1'fin.mem_toFinset.mp hmem)
  have hFsub : ↑(insert χ hS1'fin.toFinset) ⊆ S₂ := by
    rw [Finset.coe_insert]
    exact Set.insert_subset hχS₂
      (by rw [Set.Finite.coe_toFinset]; exact hS1'sub)
  have hbound := hFbound _ hFsub
  have hsplit : OddOrder.Peterfalvi.S07.sumnS (insert χ hS1'fin.toFinset)
      = OddOrder.Peterfalvi.S07.Snorm χ
        + OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset := by
    unfold OddOrder.Peterfalvi.S07.sumnS
    exact Finset.sum_insert hχnot
  rw [hsplit, hsatur] at hbound
  linarith [sOf_mem_Snorm_pos hyp (hS₂sub hχS₂)]

/-- **Peterfalvi (9.11.2) at the `Hypothesis` level: the TI-witness** (issue 9083 Phase E).
In the equality configuration — the landed `𝒮₃`-degree fact `hS3deg` and the `𝒮₂ = 𝒮₁`
extraction `hS2deg` — the (9.11.2) TI-witness holds: `∃ U₁`, `C ≤ U₁ ≤ U`, `[U:U₁] = a`,
and `U₁ ∩ U₁^w = C` for every `w ∈ W₁^#`.  This is the `htw` input of the Phase-D norm
bundle `caseA_nineElevenFour_norm_inputs`. -/
theorem caseA_nineElevenTwo_tiWitness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS3deg : ∀ χ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime \ S₂,
      (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q *
        (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℂ))
    (hS2deg : ∀ χ ∈ S₂,
      (χ : ↥M → ℂ) 1 = ((hyp.s11Setup.q * caseA.a : ℕ) : ℂ))
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    OddOrder.Peterfalvi.S11.NineElevenTwoTIWitness caseA := by
  haveI := hyp.base.finiteG
  refine OddOrder.Peterfalvi.S11.nineElevenTwoTIWitness_of_degree_dichotomy caseA ?_
  intro φ hφ
  -- `𝒮(H₀C) ⊆ 𝒮(H₀C′)` along `H₀C′ ≤ H₀C` (`C′ = [C,C] ≤ C`, `C = cSub` by `C_eq_cSub`)
  have hle : hyp.H0Cprime
      ≤ hyp.chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C ≤ _
    refine sup_le_sup_left ?_ hyp.chief.H0
    rw [C_eq_cSub_of_noncoherent hG hyp hncH0C htype]
    exact OddOrder.Peterfalvi.S11.cprimeSub_le_C hyp.s11Setup hyp.chief
  have hφ' : φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime :=
    OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup hle hφ
  by_cases hφS₂ : φ ∈ S₂
  · exact Or.inr (hS2deg φ hφS₂)
  · exact Or.inl (hS3deg φ ⟨hφ', hφS₂⟩)

end OddOrder.Peterfalvi.S13
