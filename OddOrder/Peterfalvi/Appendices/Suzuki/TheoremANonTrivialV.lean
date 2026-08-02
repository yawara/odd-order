/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3TheoremADichotomy
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.TheoremB

/-!
# Peterfalvi Part II, Ch. III §1: hypothesis (C1), and Theorem A for `V ≠ 1`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. III §1, p. 115.

> Suppose that `V = 1`. … Thus `G` is a Zassenhaus group.  By [HB], Chapter XI,
> Theorem 11.16, `G` is isomorphic to `PSL(2, q)` or to `Sz(q)`, and the conclusion of
> Theorem A is valid.  **Taking Theorem B into account**, we will then assume from this
> point on that
>
> **(C1)** The subgroup `V` is non-trivial; `C_G(P)` has 2-rank `≥ 2` for every subgroup
> `P` of `V` which is of prime order.

So (C1) is what remains after two cases have been disposed of, and the second of them is
Chapter II: if some prime-order `P ≤ V` has `C_G(P)` of 2-rank `≤ 1`, that is *verbatim*
the standing hypothesis of the First Case (`FirstCaseHypothesis.twoRank_centralizer_le_one`)
and Theorem B already gives the conclusion.  This file performs that case split, so that
`V ≠ 1` alone suffices.

## Main results

* `Hypothesis.twoRank_centralizer_le_one_of_not_exists` — the bridge between the two
  spellings of the 2-rank condition (`Subgroup ↥C_G(P)` in Ch. III, `Subgroup G` with
  `≤ C_G(P)` in Ch. II).
* `Hypothesis.nonempty_theoremAConclusion_of_V_ne_bot` — **🎯 Theorem A for `V ≠ 1`**:
  Chapter II on one side of (C1), Chapters III–IV on the other.

What is left of Theorem A is the case `V = 1`, which the book settles by citing the
classification of Zassenhaus groups ([HB], Ch. XI, Thm 11.16) rather than proving it.

## ⚠ Axiom status

`nonempty_theoremAConclusion_of_V_ne_bot` is **not** axiom-clean: it inherits `sorryAx`
from Chapter II, whose `FirstCaseHypothesis.theoremB` goes through
`NearFields.rankOne_affine_nearField` → `RankOneHypothesis.brauerSuzuki` →
`brauerSuzuki_quaternionSylow_q8`, the `Q₈` case of Brauer–Suzuki (issue 0147, a tracked
long-term project needing modular character theory).  The Chapter III–IV half
(`SecondCaseHypothesis.nonempty_theoremAConclusion`) *is* axiom-clean, and so is the
bridge below; the only `sorry` reachable from here is that one.  It is therefore absent
from `AxiomsCheck`, deliberately.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **The two spellings of "2-rank `≤ 1`" agree.**

Chapter III states the 2-rank condition of (C1) as a subgroup *of* `C_G(P)`
(`SecondCaseHypothesis.twoRank_centralizer_ge_two`), Chapter II as a subgroup of `G`
lying inside `C_G(P)` (`FirstCaseHypothesis.twoRank_centralizer_le_one`).  Failure of the
first gives the second: an elementary abelian `E ≤ C_G(P)` of order `> 2` has order `2ⁿ`
with `n ≥ 2`, so it contains a subgroup of order `4` (Sylow), and that subgroup, read
inside `C_G(P)`, is the witness Chapter III asks for. -/
theorem twoRank_centralizer_le_one_of_not_exists {P : Subgroup G}
    (h : ¬ ∃ E : Subgroup ↥(Subgroup.centralizer (P : Set G)),
      Nat.card ↥E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1) :
    ∀ E : Subgroup G, E ≤ Subgroup.centralizer (P : Set G) → (∀ x ∈ E, x ^ 2 = 1) →
      Nat.card ↥E ≤ 2 := by
  classical
  intro E hEC hEexp
  by_contra hlt
  refine h ?_
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  -- `E` is elementary abelian, so `|E| = 2ⁿ` with `n ≥ 2`
  have hE2 : IsPGroup 2 ↥E := fun x => ⟨1, by simpa using Subtype.ext (hEexp (x : G) x.2)⟩
  obtain ⟨n, hn⟩ := hE2.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hcon
    have hle : (2 : ℕ) ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := ↥E) 2 (n := 2)
      (hn ▸ pow_dvd_pow 2 hn2)
  -- transport `K` into `C_G(P)` along `E ≤ C_G(P)`
  refine ⟨K.map (Subgroup.inclusion hEC), ?_, ?_⟩
  · have hmap : Nat.card ↥(K.map (Subgroup.inclusion hEC)) = Nat.card ↥K :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective K (Subgroup.inclusion hEC)
          (Subgroup.inclusion_injective hEC)).toEquiv).symm
    rw [hmap, hK]
    norm_num
  · rintro _ ⟨z, -, rfl⟩
    refine Subtype.ext ?_
    have hz : ((z : ↥E) : G) ^ 2 = 1 := hEexp _ (z : ↥E).2
    simpa using hz

/-- **🎯 Peterfalvi Part II, Suzuki's Theorem A for `V ≠ 1`** (pp. 108–134): if the
subgroup `V` of the standing hypothesis is non-trivial, then `O^{2′}(G)` is normal of odd
index in `G` and carries one of the three standard models.

This is the case split of (C1) at the head of Ch. III §1 (p. 115):

* if some prime-order `P ≤ V` has `C_G(P)` of 2-rank `≤ 1`, the data is a
  `FirstCaseHypothesis` and Chapter II's Theorem B applies;
* otherwise (C1) holds in full, the data is a `SecondCaseHypothesis`, and Chapters III–IV
  apply (`SecondCaseHypothesis.nonempty_theoremAConclusion`).

The book's remaining case, `V = 1`, is settled there by citing the classification of
Zassenhaus groups ([HB], Ch. XI, Thm 11.16).

⚠ Depends on `sorryAx` through Chapter II only — see the module docstring. -/
theorem nonempty_theoremAConclusion_of_V_ne_bot (hV : hyp.V ≠ ⊥)
    (ih : TheoremAInductionBelow G Ω) :
    Nonempty (TheoremAConclusion G Ω) := by
  classical
  by_cases hbad : ∃ (P : Subgroup G) (p : ℕ), P ≤ hyp.V ∧ p.Prime ∧ Nat.card ↥P = p ∧
      ¬ ∃ E : Subgroup ↥(Subgroup.centralizer (P : Set G)),
        Nat.card ↥E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1
  · -- the First Case: Chapter II
    obtain ⟨P, p, hPV, hp, hcard, hno⟩ := hbad
    exact FirstCaseHypothesis.theoremB
      { toHypothesis := hyp
        P := P
        p := p
        p_prime := hp
        P_le_V := hPV
        card_P := hcard
        twoRank_centralizer_le_one := twoRank_centralizer_le_one_of_not_exists hno } ih
  · -- (C1) holds: Chapters III–IV
    refine SecondCaseHypothesis.nonempty_theoremAConclusion
      { toHypothesis := hyp
        V_ne_bot := hV
        twoRank_centralizer_ge_two := fun P hPV p hp hcard => ?_ } ih
    by_contra hno
    exact hbad ⟨P, p, hPV, hp, hcard, hno⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
