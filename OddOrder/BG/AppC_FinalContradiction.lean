/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_HypothesisB
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

This file is the BG-side scaffold for that last interface.  Lemmas C.1 and C.2
are wired to the concrete finite-field norm-set development in
`OddOrder.BG.AppC.NormSet`; Lemma C.3 consumes the concrete generator relation
constructed in Peterfalvi's field-normalizer data.  The final bridge to
Peterfalvi Section 16 is connected and axiom-clean.

The hypotheses (A) and (B) of Theorem C themselves live upstream, in
`OddOrder.BG.AppC_HypothesisB` (`conditionA`, `primeLine`, `HypothesisBAbstract`); the concrete
Section 16 instance of (B) is `OddOrder.Peterfalvi.S16.FieldNormalizerData`, whose
`sigma`/`sigma_injective`/`Q`/`y`/normalizer fields are exactly (B)'s clauses transported to the
field-normalizer configuration.
-/

namespace OddOrder.BG.AppC
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

open OddOrder.GroupTheory
open OddOrder.Peterfalvi
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Theorem C setup -/

/-- The concrete norm set cardinality conclusion attached to a Peterfalvi
Section 16 hypothesis.

This adapter keeps the `Fact hyp.base.p.Prime` instance local, because the
concrete type `GaloisField hyp.base.p hyp.base.q` needs that instance even to be
formed. -/
def normSetCardGeTwo (hyp : S16.Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  2 ≤ (NormSet.normSetE hyp.base.p hyp.base.q).ncard

/-- The concrete norm set inversion-closure conclusion attached to a Peterfalvi
Section 16 hypothesis. -/
def normSetInverseClosed (hyp : S16.Hypothesis (G := G)) : Prop :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  NormSet.normSetE hyp.base.p hyp.base.q =
    (NormSet.normSetE hyp.base.p hyp.base.q)⁻¹

/-- The norm-set outputs needed to assemble BG Theorem C from Lemmas C.1--C.3. -/
structure NormSetData (hyp : S16.Hypothesis (G := G)) where
  conditionA_holds : conditionA hyp.base.p hyp.base.q
  E_card_ge_two : normSetCardGeTwo hyp
  E_inverse_closed : normSetInverseClosed hyp

/-! ## Lemmas C.1--C.3 -/

/-- **BG Lemma C.1**: if the norm set is inverse-closed and has at least two
elements, the polynomial root count gives `p <= q`. -/
theorem lemmaC1_root_count [Finite G]
    (hyp : S16.Hypothesis (G := G)) (norms : NormSetData hyp) :
    hyp.base.p ≤ hyp.base.q := by
  haveI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hEinv :
      NormSet.normSetE hyp.base.p hyp.base.q =
        (NormSet.normSetE hyp.base.p hyp.base.q)⁻¹ := by
    simpa [normSetInverseClosed] using norms.E_inverse_closed
  have hcard : 2 ≤ (NormSet.normSetE hyp.base.p hyp.base.q).ncard := by
    simpa [normSetCardGeTwo] using norms.E_card_ge_two
  exact NormSet.lemmaC1 (p := hyp.base.p) (q := hyp.base.q)
    hyp.base.q_prime hEinv hcard

/-- **BG Lemma C.2**: condition (A) alone gives that the norm set has at
least two elements. -/
theorem lemmaC2_card_ge_two_of_conditionA [Finite G]
    (hyp : S16.Hypothesis (G := G)) (hA : conditionA hyp.base.p hyp.base.q) :
    normSetCardGeTwo hyp := by
  haveI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  have hcard := NormSet.lemmaC2 (p := hyp.base.p) (q := hyp.base.q)
    hyp.base.p_odd hyp.base.q_prime hyp.base.q_odd hA
  simpa [normSetCardGeTwo] using hcard

/-- **BG Lemma C.2**: the field-normalizer data supplies condition (A), hence
the norm set has at least two elements. -/
theorem lemmaC2_card_ge_two [Finite G]
    (hyp : S16.Hypothesis (G := G)) (data : S16.FieldNormalizerData hyp) :
    normSetCardGeTwo hyp :=
  lemmaC2_card_ge_two_of_conditionA hyp data.cyclotomic_coprime

/-- **BG Lemma C.3**: the norm set is closed under inversion. -/
theorem lemmaC3_inverse_closed [Finite G]
    (hyp : S16.Hypothesis (G := G)) (data : S16.FieldNormalizerData hyp) :
    normSetInverseClosed hyp := by
  haveI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  simpa [normSetInverseClosed]
    using NormSet.normSetE_eq_inv_of_forall_normN_two_mul_sub_one
      (p := hyp.base.p) (q := hyp.base.q) hyp.base.q_prime.pos
      data.appC_normSet_generator_relation

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

/-- **BG Theorem C, `p`/`q`-abstract form.**  For odd primes `p, q` satisfying condition (A) and
the norm-set relation that Hypothesis (B) produces — `N(2a - 1) = 1` for every `a` in the norm set
`E` — one has `p ≤ q`.

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
    (hA : conditionA p q)
    (hrel : ∀ a : GaloisField p q, a ∈ NormSet.normSetE p q →
      NormSet.normN p q ((2 : GaloisField p q) * a - 1) = 1) :
    p ≤ q :=
  NormSet.lemmaC1 (p := p) (q := q) hq
    (NormSet.normSetE_eq_inv_of_forall_normN_two_mul_sub_one (p := p) (q := q) hq.pos hrel)
    (NormSet.lemmaC2 (p := p) (q := q) hp_odd hq hq_odd hA)

/-! ## Theorem C and the Peterfalvi bridge -/

/-- **BG Theorem C**: the field-normalizer configuration constructed in
Peterfalvi (14.2) forces `p <= q`. -/
theorem theoremC [Finite G] (hyp : S16.Hypothesis (G := G)) :
    S16.FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q := by
  intro data
  exact lemmaC1_root_count hyp
    { conditionA_holds := data.cyclotomic_coprime
      E_card_ge_two := lemmaC2_card_ge_two hyp data
      E_inverse_closed := lemmaC3_inverse_closed hyp data }

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
