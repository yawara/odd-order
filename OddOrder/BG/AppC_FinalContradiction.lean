/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_LemmaC3_FixedPointFree
import OddOrder.BG.AppC_LemmaC2
import OddOrder.Peterfalvi.S16_NonExistenceG

/-!
# BG Appendix C: The Final Contradiction

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, pp. 145--152.

Appendix C records the Carlip--Wheeler presentation of Peterfalvi's finite-field
argument for the final contradiction.  In Peterfalvi Section 16 the same endpoint
appears as Theorem (14.2): a field-normalizer configuration is constructed with
primes `q < p`.  BG Appendix C proves that any such configuration forces
`p <= q`.

This file assembles Theorem C from Lemmas C.1--C.3, all three of which are `p, q`-level
statements about the norm set `E ⊆ 𝔽_{p^q}`: C.1 and C.2 live in `OddOrder.BG.AppC.NormSet`,
and C.3 in the `OddOrder.BG.AppC_LemmaC3_*` development.

`theoremC_of_hypothesisBAbstract` is the book's statement verbatim -- primes `p, q` with
condition (A), a group `G` satisfying hypothesis (B), conclusion `p ≤ q` -- with no reference to
the Peterfalvi Section 16 configuration anywhere.  Section 16 supplies one instance of (B)
(`theoremC`, the Feit--Thompson bridge, and `final_contradiction`); the book's Remark (II)
example `p = 2`, `G = SL(2, 2^q)` supplies another (`hypothesisBAbstract_sl2`).

The hypotheses (A) and (B) themselves live upstream in `OddOrder.BG.AppC_HypothesisB`
(`conditionA`, `primeLine`, `HypothesisBAbstract`).
-/

namespace OddOrder.BG.AppC
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.Peterfalvi
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Lemmas C.1--C.3

All three step lemmas are `p, q`-level statements about the norm set `E ⊆ 𝔽_{p^q}`:

* **C.1** `NormSet.lemmaC1` — an inverse-closed `E` with `|E| ≥ 2` forces `p ≤ q`, by a root
  count for a polynomial of degree `< q`;
* **C.2** `NormSet.lemmaC2` — condition (A) alone gives `|E| ≥ 2`;
* **C.3** `FieldNormalizerData.normSetGeneratorRelation_of_hypothesisB` — hypothesis (B) gives
  the norm relation `N(2a − 1) = 1` on `E`, hence (`NormSet.normSetE_eq_inv_of_...`) that `E`
  is inverse-closed.

Theorem C is their composition, below. -/

/-- **BG Appendix C, Remark (V)**: "by (A) one may assume `p` and `q` are odd".

Precisely: for primes `p, q` satisfying condition (A), the conclusion `p ≤ q` of Theorem C already
holds whenever one of them is even, so the theorem's content is entirely in the odd case.

* `p = 2` gives `p ≤ q` outright, since every prime is at least `2`;
* `q = 2` cannot happen for odd `p`: condition (A) reads `gcd((p² - 1)/(p - 1), p - 1) = 1`, and
  `(p² - 1)/(p - 1) = p + 1`, so it says `gcd(p + 1, p - 1) = 1` — impossible for odd `p ≥ 3`,
  where `p + 1` and `p - 1` are both even.

Stated in the `p, q`-abstract setting of `theoremC_abstract`; the FT spine never needs it (oddness
of `p, q` is ambient in the Peterfalvi Section 16 configuration), so this closes the remark purely
for book completeness. -/
theorem le_of_conditionA_of_not_odd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hA : conditionA p q) (hno : ¬ (Odd p ∧ Odd q)) : p ≤ q := by
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · exact hq.two_le
  · exfalso
    have hq2 : q = 2 := by
      by_contra h
      exact hno ⟨hpodd, hq.odd_of_ne_two h⟩
    subst hq2
    have hp3 : 3 ≤ p := by
      rcases hpodd with ⟨k, hk⟩
      have := hp.two_le
      omega
    have hfact : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      cases p with
      | zero => omega
      | succ n => simp [pow_two]; ring_nf; omega
    have hdiv : (p ^ 2 - 1) / (p - 1) = p + 1 := by
      rw [hfact, Nat.mul_div_cancel_left _ (by omega : 0 < p - 1)]
    rw [conditionA, hdiv] at hA
    have h2a : 2 ∣ p + 1 := by rcases hpodd with ⟨k, hk⟩; omega
    have h2b : 2 ∣ p - 1 := by rcases hpodd with ⟨k, hk⟩; omega
    have hgcd : (2 : ℕ) ∣ Nat.gcd (p + 1) (p - 1) := Nat.dvd_gcd h2a h2b
    rw [hA] at hgcd
    omega

/-- **BG Theorem C, `p`/`q`-abstract form.**  For odd primes `p, q` and the norm-set relation that
Hypothesis (B) produces — `N(2a - 1) = 1` for every `a` in the norm set `E` — one has `p ≤ q`.

⚠ **Condition (A) is not needed here** (2026-08-08, issue 0179).  The book states Theorem C under
(A), and this abstract form used to carry `hA : conditionA p q` as an argument, but none of the
three step lemmas uses it: `lemmaC1` only needs `E = E⁻¹` and `|E| ≥ 2`, and `lemmaC2` only needs
`p`, `q` odd (its own `(A)` argument was likewise unused and has been dropped).  (A) does real work
downstream, in producing `hrel` from Hypothesis (B); it does no work in this composition.

This is the book's Theorem C with the Peterfalvi Section 16 configuration removed from the
*statement*: no `S16.Hypothesis`, no `FieldNormalizerData`, no ambient `q < p`.  The three step
lemmas were already abstract in `p, q` (`NormSet.lemmaC1`, `NormSet.lemmaC2`,
`NormSet.normSetE_eq_inv_of_forall_normN_two_mul_sub_one`); only the wrappers above were tied to
`S16`, so this is their `p, q`-level composition.

What Hypothesis (B) contributes is exactly `hrel`: the group-theoretic embedding of `H = PU` with
its two normalizer conditions is what forces the norm set to satisfy `N(2a - 1) = 1`, and any other
configuration supplying `hrel` — e.g. the `SL(2, 2^q)` example of the book's Remark (II) — feeds
this form directly.  The FT spine continues to use `theoremC` below, which discharges `hrel` from
the constructed `FieldNormalizerData`. -/
theorem theoremC_abstract {p q : ℕ} [Fact p.Prime] (hp_odd : Odd p) (hq : q.Prime) (hq_odd : Odd q)
    (hrel : ∀ a : GaloisField p q, a ∈ NormSet.normSetE p q →
      NormSet.normN p q ((2 : GaloisField p q) * a - 1) = 1) :
    p ≤ q :=
  NormSet.lemmaC1 (p := p) (q := q) hq
    (NormSet.normSetE_eq_inv_of_forall_normN_two_mul_sub_one (p := p) (q := q) hq.pos hrel)
    (NormSet.lemmaC2 (p := p) (q := q) hp_odd hq hq_odd)

/-! ## Theorem C -/

/-- **BG Theorem C** from field-normalizer data, i.e. from hypotheses (A) and (B) with the three
images `σ(P)`, `σ(U)`, `σ(P₀)` named: `p ≤ q`.

Lemma C.3 (`normSetGeneratorRelation_of_hypothesisB`) supplies the norm relation, and Remark (V)
disposes of the case where `q` is even. -/
theorem theoremC_of_hypothesisB {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (data : FieldNormalizerData p q G) : p ≤ q := by
  by_cases hqodd : Odd q
  · exact theoremC_abstract data.p_odd data.q_prime hqodd
      data.normSetGeneratorRelation_of_hypothesisB
  · exact le_of_conditionA_of_not_odd Fact.out data.q_prime data.cyclotomic_coprime
      fun h => hqodd h.2

/-- **BG Theorem C** (p. 145), verbatim: *let `p` and `q` be two primes satisfying condition (A),
and suppose there is a group `G` such that hypothesis (B) holds.  Then `p ≤ q`.*

Nothing in the statement mentions the Peterfalvi Section 16 configuration; the Feit--Thompson
spine merely supplies one instance of (B) (`theoremC` below).  Another instance is the book's
Remark (II) example `p = 2`, `G = SL(2, 2^q)` (`hypothesisBAbstract_sl2`).

Oddness of `p` is not assumed: by Remark (V) the even case is immediate
(`le_of_conditionA_of_not_odd`).  Neither is finiteness of `G`: hypothesis (B) only asks that
`Q` be finite, and `|σ(P₀)| = p` is a consequence of the setup, so those two are all the
finiteness the proof uses (`FieldNormalizerData.finite_Q`, `.finite_W2`). -/
theorem theoremC_of_hypothesisBAbstract {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (hb : HypothesisBAbstract p q G) (hq : q.Prime) (hA : conditionA p q) : p ≤ q := by
  by_cases hpodd : Odd p
  · exact theoremC_of_hypothesisB (hb.toFieldNormalizerData hq hpodd hA)
  · exact le_of_conditionA_of_not_odd Fact.out hq hA fun h => hpodd h.1

/-! ## The Peterfalvi bridge -/

/-- **BG Theorem C**: the field-normalizer configuration constructed in
Peterfalvi (14.2) forces `p <= q`.  This is `theoremC_of_hypothesisB` at the Section 16
instance of (B). -/
theorem theoremC [Finite G] (hyp : S16.Hypothesis (G := G)) :
    S16.FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q := by
  intro data
  haveI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  exact theoremC_of_hypothesisB data.toFieldNormalizerData

/-- **BG Appendix C + Peterfalvi Section 16**: once Peterfalvi constructs the
field-normalizer data, BG Theorem C contradicts the standing hypothesis `q < p`. -/
theorem final_contradiction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : S16.Hypothesis (G := G)) :
    False :=
  S16.nonexistence_of_G hG hnoV hncH0C hyp (theoremC hyp)

end OddOrder.BG.AppC
