/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3PropositionModel
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourEndgame
import OddOrder.Peterfalvi.Appendices.Suzuki.WCyclicDivides

/-!
# Peterfalvi Part II, Ch. IV §4 → §3 Corollary 1: `O^{2′}(G) ≅ PSU(3, q)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV, pp. 129–134.

§4 ends (`SectionFourSetup.exists_mem_W`) with

> an `x ∈ Q − Q₀` and a `ζ ∈ W^#` such that `f(x) = (x⁻¹)^ζ` and `h(x) ∈ W`,

which is *verbatim* the hypothesis of the Proposition of §3 — the point of the section
being that it reaches it without `V = W`.  Corollary 1 of that Proposition then identifies
`O^{2′}(G)` with `PSU(3, q)`, and `nonempty_theoremAConclusion_of_isStandardModel` runs
that identification off the model of Ch. III §3.  This file joins the two, which closes
Ch. IV.

Every remaining input is section data:

* the model of Ch. III §3 is `exists_standardModel` (its `x₀ ≠ 1` is
  `exists_center_Q_ne_one`);
* `|W|` divides `q + 1` by Ch. I §3 Lemma 5 (`isCyclic_W_and_card_dvd_of_orderThree`),
  and `|W| > 1` because §4 hands back a nontrivial `ζ`;
* `|K| = q − 1` is `card_actualKActor_eq`;
* `q > 8` is `SectionFourSetup.eight_lt_natCard_Q0`, which supplies both `1 < m` (the
  standard model is `PSU(3, 2^m)` with `m ≥ 2`) and `|F| ≥ 3`.

## Main results

* `Hypothesis.SectionFourSetup.nonempty_theoremAConclusion` — **Ch. IV's conclusion**:
  under §4's standing data, `Theorem A`'s conclusion holds for `G` acting on `Ω`, with
  `L = O^{2′}(G)` carrying the standard `PSU(3, q)` model.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.RankOneBNPair
open OddOrder.GroupTheory.Suzuki2Group

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

include hyp in
/-- **🎯🎯🎯🎯🎯 Peterfalvi Part II, Ch. IV** (pp. 122–134): under the standing data of §4,

  `O^{2′}(G) ≅ PSU(3, q)`, acting on `Ω` as on the Hermitian unital,

which is Theorem A's conclusion (Corollary 1 of §3, p. 132).

§4 (`SectionFourSetup.exists_mem_W`) produces the Proposition's hypothesis —
`x ∈ Q − Q₀`, `ζ ∈ W^#`, `f(x) = (x⁻¹)^ζ`, `h(x) ∈ W` — in the case `V ≠ W`, where the
`V = W` route of Corollary 2 is unavailable; `nonempty_theoremAConclusion_of_isStandardModel`
turns it into Corollary 1.  Neither half uses `V = W`.

The mappings are the ones `exists_fgh_mapsTo` builds, so that `f` maps `Q` into `Q`
(§3 evaluates `f` at elements of `Q` without knowing them non-trivial); `IsFGH` does not
see the change, since it constrains `f` only on `Q^#`. -/
theorem SectionFourSetup.nonempty_theoremAConclusion (s4 : hyp.SectionFourSetup)
    {m : ℕ} (M : hyp.QuotientFieldModel m) (sfive : hyp.LemmaFiveSetup m)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card hyp.Q0 ^ 3)
    (hmu : Function.Injective M.mu) (hQ2 : IsPGroup 2 ↥hyp.Q)
    (hQsuz : IsSuzuki2Group ↥hyp.Q)
    (hCop : Nat.Coprime (Nat.card ↥(s4.P.subgroupOf hyp.D)) (Nat.card ↥hyp.Q))
    (hSolv : Group.IsSolvable ↥hyp.Q) (hP : s4.P ≠ ⊥)
    (hA3 : ∃ E : Subgroup ↥(Subgroup.centralizer ((s4.P : Set G))),
      Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hord : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer ((s4.P : Set G)))))
    (ih : TheoremAInductionBelow G Ω)
    (hl : 2 < Nat.card ↥(hyp.Q0 ⊓ Subgroup.centralizer ((s4.P : Set G)))) :
    Nonempty (TheoremAConclusion G Ω) := by
  classical
  -- `q = 2^m > 8`, so `m ≥ 2` and `|F| = q ≥ 3`
  have hq8 : 8 < 2 ^ m := hQ0card ▸ SectionFourSetup.eight_lt_natCard_Q0 hyp s4 hl
  have hn : 1 < m := by
    by_contra hc
    exact absurd (Nat.pow_le_pow_right (by norm_num) (by omega) :
      (2 : ℕ) ^ m ≤ 2 ^ 1) (by omega)
  have hm : m ≠ 0 := (Nat.zero_lt_one.trans hn).ne'
  have hcard : 3 ≤ Nat.card ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m) := by
    rw [OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm]
    omega
  have hC2 := hyp.braid_of_orderThree hord
  -- §4's output: the hypothesis of the Proposition of §3
  obtain ⟨f₁, g₁, h₁, H₁, hfQ⟩ := hyp.exists_fgh_mapsTo
  obtain ⟨ω, hωQ, hωQ0, ζ, hζ, hζ1, hf, hhW⟩ :=
    SectionFourSetup.exists_mem_W hyp s4 H₁ hC2 M sfive sfive.centerEqQ0 hm hQ0card hmu
      hQ2 hQsuz hCop hSolv hP hA3 hord hCQ ih hl
  -- the model of Ch. III §3, and the numerology of `K` and `W`
  obtain ⟨x₀, hx₀⟩ := hyp.exists_center_Q_ne_one
  obtain ⟨-, hWdvd⟩ :=
    hyp.isCyclic_W_and_card_dvd_of_orderThree hord hQsuz hm hQ0card hcardQ ih
  exact hyp.nonempty_theoremAConclusion_of_isStandardModel H₁ hC2 hn sfive M
    sfive.centerEqQ0 hmu hQ0card hcard (hyp.card_actualKActor_eq sfive M hm hQ0card)
    hWdvd (hyp.one_lt_natCard_W ⟨ζ, hζ, hζ1⟩) hfQ x₀
    (hyp.exists_standardModel sfive M hord hm hQ0card hcardQ ih x₀ hx₀)
    hζ (fun hc => hζ1 (congrArg Subtype.val hc)) hωQ hωQ0 hf hhW hQ2

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
