/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionThree

/-!
# Peterfalvi Part II, Ch. IV §4: the linear equation (4)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, p. 133.

Step (3) of §4 gives `f(ω) = ω^{-ζ}` and `h(ω) ∈ ζ³P`, i.e. `h(ω) = ζ³η` with `η ∈ P`.
`stepOne_chain_of_h_eq_mul` runs the chain of §3's stage (1) with that conjugator and
lands the book's displayed identity

  `f(ω^{ζ⁻¹} s^a)^{a²} s^a = f(ω^ζ s^a)^{ζ⁻³η} ω^{ζ⁻¹}`.

This file reads it in the coordinate `Q ⧸ Z(Q) ≅ E`, which is the book's

  **(4)**  `a² f(ω s^a)‾ = ζ⁻¹ f(ω s^a)‾^η + ω̄`.

Unlike §3's `stepTwo_linear` there is *no* hypothesis `V = W` here — §4 is precisely the
case `V ≠ W`, and the identification `Q ⋊ KW ≅ S₁ ⋊ K₁W₁` used in the book is the one
for the *ambient* `Q`, `K`, `W`, which `QuotientFieldModel` already carries.

What replaces `V = W` is that `η ∉ KW`: the book therefore reads `X̄ ↦ X̄^η` as a
*semilinear* map of `E` (Appendix I, Proposition 2), and equation (4) keeps `f(ω s^a)‾^η`
as an unevaluated term.  Here that term is literally the coordinate of the conjugate
`η · f(ω s^a) · η⁻¹`, so (4) is stated without any semilinearity input; the field
automorphism `μ` of the book enters only from (5) onwards.

The one property of `η` that (4) does use is that it commutes with `ζ` — in the book
because `ζ ∈ C_W(P)` and `η ∈ P`.  That collapses the two `ζ`-conjugations flanking the
`η`-conjugation on the right-hand side into a single `ζ²`.

## Main results

* `Hypothesis.sectionFour_conj_eta_of_commute` — the right-hand side of the chain, with
  `η` moved past `ζ`: `(ζ³η) · (X^{ζ⁻¹}) · (ζ³η)⁻¹ = ζ² · (X^η) · ζ⁻²`.
* `Hypothesis.sectionFour_four_linear` — **the book's (4)**.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

omit [Finite G] in
/-- **The right-hand conjugator of §4's chain, with `η` moved past `ζ`** (Peterfalvi
Part II, Ch. IV §4, p. 133).

In §3 the conjugator of stage (1) is `ζ³` and the argument is `X^ζ`, so the two
conjugations combine into `ζ²`.  In §4 the conjugator is `ζ³η`; since `η` commutes with
`ζ` (the book takes `ζ ∈ C_W(P)` and `η ∈ P`), the `ζ`-parts still combine into `ζ²`
and only the `η`-conjugation is left over.  It is that leftover which the book reads as
a semilinear map of `E`. -/
theorem sectionFour_conj_eta_of_commute {ζ η x : G} (hηζ : η * ζ = ζ * η) :
    (ζ ^ 3 * η) * (ζ⁻¹ * x * ζ) * (ζ ^ 3 * η)⁻¹
      = ζ ^ 2 * (η * x * η⁻¹) * (ζ ^ 2)⁻¹ := by
  have hcomm : Commute η ζ := hηζ
  have h1 : η * ζ⁻¹ = ζ⁻¹ * η := hcomm.inv_right.eq
  have h2 : ζ * η⁻¹ = η⁻¹ * ζ := hcomm.inv_left.eq.symm
  calc (ζ ^ 3 * η) * (ζ⁻¹ * x * ζ) * (ζ ^ 3 * η)⁻¹
      = ζ ^ 3 * (η * ζ⁻¹) * x * (ζ * η⁻¹) * (ζ ^ 3)⁻¹ := by group
    _ = ζ ^ 3 * (ζ⁻¹ * η) * x * (η⁻¹ * ζ) * (ζ ^ 3)⁻¹ := by rw [h1, h2]
    _ = ζ ^ 2 * (η * x * η⁻¹) * (ζ ^ 2)⁻¹ := by group

include hyp in
/-- **🎯 Peterfalvi Part II, Ch. IV §4, equation (4)** (p. 133):

  `a² f(ω s^a)‾ = ζ⁻¹ f(ω s^a)‾^η + ω̄`.

The group identity behind it is `stepOne_chain_of_h_eq_mul`, i.e. the chain of §3's
stage (1) run with the conjugator `h(ω) = ζ³η` that §4's step (3) supplies.  Both
`f`-values in that chain are `ζ^{±1}`-conjugates of the single unknown
`X = f(ω s^a)` (`f_conj_zeta_of_mem_Q0`), so reading the chain in `Q ⧸ Z(Q) ≅ E` gives a
relation between `X̄`, its `η`-conjugate's coordinate, and `ω̄`:

* `s^a ∈ Q₀ = Z(Q)` disappears (`coord_mk_eq_zero_of_mem_Q0`);
* each `K W`-conjugation becomes multiplication by a scalar (`coord_conj_eq`);
* `η` commutes with `ζ`, so on the right the conjugations by `ζ³` and `ζ` collapse to
  `ζ²` around the `η`-conjugate (`sectionFour_conj_eta_of_commute`).

Cancelling the common factor `μ(1, ζ)` — a unit — is what turns

  `μ(a²) μ(ζ) X̄ = μ(ζ)² X̄^η + μ(ζ) ω̄`

into the book's shape.  As in §3 the scalars are the *inverses* of the book's, its `x^d`
being conjugation by `d⁻¹`: the book's `ζ⁻¹` is `μ(1, ζ)` here.

⚠ No hypothesis `V = W` and no injectivity of `μ` is needed: the model is only used
through the scalar action of `K W`, which `QuotientFieldModel` provides outright. -/
theorem sectionFour_four_linear (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ζ ω a η : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (haK : a ∈ hyp.KSet) (ha2 : a ^ 2 ∈ hyp.K) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hηζ : η * ζ = ζ * η) (hhω : h ω = ζ ^ 3 * η) (htη : hyp.t * η * hyp.t = η)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q)
    (hEQ : η * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * η⁻¹ ∈ hyp.Q) :
    ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
        * M.coord (Additive.ofMul (QuotientGroup.mk
            (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))
      = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
          * M.coord (Additive.ofMul (QuotientGroup.mk
              (⟨η * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * η⁻¹, hEQ⟩ : ↥hyp.Q)))
        + M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
  classical
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hconjQ : ∀ {c x : G}, c ∈ hyp.D → x ∈ hyp.Q → c * x * c⁻¹ ∈ hyp.Q := by
    intro c x hc hx
    have hm := hyp.rankOneSetup.DQ c⁻¹ (hyp.D.inv_mem hc) x hx
    rwa [inv_inv] at hm
  have hzQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D haK.1 hyp.distinguishedInvolution_mem_Q0
  have hzQ : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q := hyp.Q0_le_Q hzQ0
  -- the chain of stage (1), with both `f`-values expressed through `X = f(ω s^a)`
  obtain ⟨hcL, hcR⟩ := hyp.f_conj_zeta_of_mem_Q0 H hζ hzQ0 hωQ hωQ0
  have hchain := hyp.stepOne_chain_of_h_eq_mul H hC2 hζ hωQ hωQ0 haK hf hhω htη
  rw [hcL, hcR, sectionFour_conj_eta_of_commute (G := G) hηζ] at hchain
  -- memberships
  have ha2D : a ^ 2 ∈ hyp.D := hyp.K_le_D ha2
  have hζ2D : ζ ^ 2 ∈ hyp.D := pow_mem hζD 2
  have hYQ : ζ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ⁻¹ ∈ hyp.Q :=
    hconjQ hζD hXQ
  have hAQ : a ^ 2 * (ζ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ⁻¹)
      * (a⁻¹) ^ 2 ∈ hyp.Q := by
    have hm := hconjQ ha2D hYQ
    rwa [show (a ^ 2)⁻¹ = (a⁻¹) ^ 2 from by group] at hm
  have hLQ : a ^ 2 * (ζ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ⁻¹)
      * (a⁻¹) ^ 2 * (a * hyp.distinguishedInvolution * a⁻¹) ∈ hyp.Q :=
    hyp.Q.mul_mem hAQ hzQ
  have hBQ : ζ ^ 2 * (η * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * η⁻¹)
      * (ζ ^ 2)⁻¹ ∈ hyp.Q := hconjQ hζ2D hEQ
  have hωconjQ : ζ * ω * ζ⁻¹ ∈ hyp.Q := hconjQ hζD hωQ
  have hRQ : ζ ^ 2 * (η * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * η⁻¹)
      * (ζ ^ 2)⁻¹ * (ζ * ω * ζ⁻¹) ∈ hyp.Q := hyp.Q.mul_mem hBQ hωconjQ
  -- the two sides of the chain are the same element of `Q`
  have hcoordeq : M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hLQ⟩ : ↥hyp.Q)))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hRQ⟩ : ↥hyp.Q))) :=
    congrArg (fun q : ↥hyp.Q => M.coord (Additive.ofMul (QuotientGroup.mk q)))
      (Subtype.ext hchain)
  have honeK : (hyp.kActor (hyp.K.one_mem)) = 1 := hyp.kActor_one hyp.K.one_mem
  have hL : M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hLQ⟩ : ↥hyp.Q)))
      = ((M.mu (hyp.kActor ha2, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) *
        M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hXQ⟩ : ↥hyp.Q))) := by
    rw [hyp.coord_mk_mul M hAQ hzQ hLQ,
      hyp.coord_mk_eq_zero_of_mem_Q0 M hZ hzQ0 hzQ, add_zero,
      hyp.coord_conj_eq M ha2 hζ hXQ hAQ (by group)]
  have hR : M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hRQ⟩ : ↥hyp.Q)))
      = ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W) ^ 2) : M.Eˣ) : M.E) *
          M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hEQ⟩ : ↥hyp.Q)))
        + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) *
          M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
    rw [hyp.coord_mk_mul M hBQ hωconjQ hRQ,
      hyp.coord_conj_eq M hyp.K.one_mem (hyp.W.pow_mem hζ 2) hEQ hBQ (by group),
      hyp.coord_conj_eq M hyp.K.one_mem hζ hωQ hωconjQ (by group)]
    rw [honeK]
    rfl
  -- the two scalars of the left-hand side split, and `μ(1, ζ²) = μ(1, ζ)²`
  have hmuprod : ((M.mu (hyp.kActor ha2, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
      = ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
        * ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) := by
    have hp : ((hyp.kActor ha2, 1) : ↥hyp.actualKActor × ↥hyp.W) * (1, ⟨ζ, hζ⟩)
        = (hyp.kActor ha2, ⟨ζ, hζ⟩) := by
      rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [← hp, map_mul, Units.val_mul]
  have hmusq : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W) ^ 2) : M.Eˣ) : M.E)
      = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) ^ 2 := by
    have hp : (((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) : ↥hyp.actualKActor × ↥hyp.W)
        ^ 2 = ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W) ^ 2) := by
      rw [Prod.pow_mk, one_pow]
    rw [← hp, map_pow, Units.val_pow_eq_pow_val]
  rw [hL, hR, hmuprod, hmusq] at hcoordeq
  refine mul_left_cancel₀ (Units.ne_zero (M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)))) ?_
  linear_combination hcoordeq

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
