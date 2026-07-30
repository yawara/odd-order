/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.RankOneSetup
import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution
import OddOrder.Peterfalvi.Appendices.Suzuki.InvolutionClass

/-!
# Peterfalvi Part II, Ch. IV §2: preliminary calculation

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, p. 123.

Chapter IV determines the mappings `f, g, h` of §1 for the case `L = G`, `M = H`,
resuming the hypotheses (C1) and (C2) of Chapter III.  The part of (C2) used here is
that `st` has order `3`, equivalently — since `s` and `t` are involutions —

  `t s t = s t s`,

which is the structure equation `t s t = r⁻¹ t r` of Ch. I Prop 4 (b) in the special
case `r = s`.

The first step is the book's

> **(1)** for `a ∈ K`, `f(s^a) = g(s^a) = s^{a⁻¹}` and `h(s^a) = a²`.

It comes out of `t s t = s t s` being *already* a canonical factorization
`p · d · t · q` with `p = q = s ∈ Q` and `d = 1 ∈ D`, which reads off
`f(s) = g(s) = s` and `h(s) = 1`; (H3) then transports these along `a ∈ D`, and for
`a ∈ K` the twist `a^t` is `a⁻¹`, turning `s^{a^t}` into `s^{a⁻¹}` and
`(a^t)⁻¹ h(s) a` into `a²`.

## Main results

* `Hypothesis.fgh_at_distinguishedInvolution` — `f(s) = g(s) = s`, `h(s) = 1`.
* `Hypothesis.fgh_at_conj_distinguishedInvolution` — step (1).
* `Hypothesis.f_mul_conj_distinguishedInvolution` — step (2).
* `Hypothesis.f_conj_distinguishedInvolution_mul` — step (3).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- The distinguished involution lies in `Q` (Ch. I Prop 4 (b) plus
`Hypothesis.mem_Q_of_sq_eq_one_of_mem_H`). -/
theorem distinguishedInvolution_mem_Q : hyp.distinguishedInvolution ∈ hyp.Q :=
  hyp.mem_Q_of_sq_eq_one_of_mem_H hyp.distinguishedInvolution_mem_H
    hyp.distinguishedInvolution_sq

/-- **Peterfalvi Part II, Ch. IV §2** (p. 123), the base case of step (1):
under `(C2)` — in the form `t s t = s t s` — the mappings of §1 take the values
`f(s) = g(s) = s` and `h(s) = 1` at the distinguished involution.

The point is that `s t s` is *already* in the canonical form `p · d · t · q` of §1,
with `p = q = s ∈ Q` and `d = 1 ∈ D`. -/
theorem fgh_at_distinguishedInvolution (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution) :
    f hyp.distinguishedInvolution = hyp.distinguishedInvolution ∧
      g hyp.distinguishedInvolution = hyp.distinguishedInvolution ∧
      h hyp.distinguishedInvolution = 1 :=
  fgh_eq_of_canonical hyp.rankOneSetup H hyp.distinguishedInvolution_mem_Q
    hyp.distinguishedInvolution_ne_one hyp.distinguishedInvolution_mem_Q
    (Subgroup.one_mem _) hyp.distinguishedInvolution_mem_Q (by rw [hC2]; group)

/-- **Peterfalvi Part II, Ch. IV §2, step (1)** (p. 123): for `a ∈ K`,

  `f(s^a) = g(s^a) = s^{a⁻¹}`  and  `h(s^a) = a²`.

By (H3) the three values at `s^a` are `f(s)^{a^t}`, `g(s)^{a^t}` and
`(a^t)⁻¹ h(s) a`; the base case gives `f(s) = g(s) = s` and `h(s) = 1`, and `a ∈ K`
means precisely `a^t = a⁻¹`.  (Exponents are Peterfalvi's: `x^a = a⁻¹ x a`.) -/
theorem fgh_at_conj_distinguishedInvolution (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {a : G} (haK : a ∈ hyp.KSet) :
    f (a⁻¹ * hyp.distinguishedInvolution * a)
        = a * hyp.distinguishedInvolution * a⁻¹ ∧
      g (a⁻¹ * hyp.distinguishedInvolution * a)
        = a * hyp.distinguishedInvolution * a⁻¹ ∧
      h (a⁻¹ * hyp.distinguishedInvolution * a) = a ^ 2 := by
  obtain ⟨haD, hat⟩ := haK
  obtain ⟨hf, hg, hh⟩ := hyp.fgh_at_distinguishedInvolution H hC2
  obtain ⟨e₁, e₂, e₃⟩ := hThree hyp.rankOneSetup H hyp.distinguishedInvolution_mem_Q
    hyp.distinguishedInvolution_ne_one haD
  refine ⟨?_, ?_, ?_⟩
  · rw [e₁, hat, hf, inv_inv]
  · rw [e₂, hat, hg, inv_inv]
  · rw [e₃, hat, hh, inv_inv, mul_one, sq]

/-- `s^a ≠ 1` for any `a`. -/
theorem conj_distinguishedInvolution_ne_one (a : G) :
    a⁻¹ * hyp.distinguishedInvolution * a ≠ 1 := by
  intro hc
  refine hyp.distinguishedInvolution_ne_one ?_
  have e : hyp.distinguishedInvolution
      = a * (a⁻¹ * hyp.distinguishedInvolution * a) * a⁻¹ := by group
  rw [hc] at e
  simpa using e

/-- `t a² t = (a⁻¹)²` for `a ∈ K`, since `a^t = a⁻¹`. -/
theorem t_conj_sq_of_mem_KSet {a : G} (haK : a ∈ hyp.KSet) :
    hyp.t * a ^ 2 * hyp.t = (a⁻¹) ^ 2 := by
  have hinvol : hyp.t * hyp.t = 1 := hyp.rankOneSetup.invol
  have e : hyp.t * a ^ 2 * hyp.t = (hyp.t * a * hyp.t) * (hyp.t * a * hyp.t) := by
    have e' : (hyp.t * a * hyp.t) * (hyp.t * a * hyp.t)
        = hyp.t * a * (hyp.t * hyp.t) * a * hyp.t := by group
    rw [e', hinvol]
    rw [sq]
    group
  rw [e, haK.2, sq]

/-- **Peterfalvi Part II, Ch. IV §2, step (2)** (p. 123): for `a ∈ K` and `ω ∈ Q^#`
with `ω s^a ≠ 1`,

  `f(ω s^a) = f(f(ω) s^{a⁻¹})^{a⁻²} s^{a⁻¹}`.

This is (H6) at `x = ω`, `y = s^a`, with step (1) supplying
`g(s^a) = f(s^a) = s^{a⁻¹}` and `h(s^a) = a²`, whose `t`-twist is `a⁻²`.

The book states it for `ω ∈ Q − Q₀`, which is what makes `ω s^a ≠ 1`; that
non-degeneracy is taken as a hypothesis here. -/
theorem f_mul_conj_distinguishedInvolution (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {a ω : G} (haK : a ∈ hyp.KSet) (hωQ : ω ∈ hyp.Q) (hω1 : ω ≠ 1)
    (hne : ω * (a⁻¹ * hyp.distinguishedInvolution * a) ≠ 1) :
    f (ω * (a⁻¹ * hyp.distinguishedInvolution * a))
      = a ^ 2 * f (f ω * (a * hyp.distinguishedInvolution * a⁻¹)) * (a⁻¹) ^ 2 *
        (a * hyp.distinguishedInvolution * a⁻¹) := by
  obtain ⟨hf1, hg1, hh1⟩ := hyp.fgh_at_conj_distinguishedInvolution H hC2 haK
  have hsaQ : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q :=
    hyp.rankOneSetup.DQ a haK.1 _ hyp.distinguishedInvolution_mem_Q
  obtain ⟨-, e₂, -, -⟩ :=
    hSix hyp.rankOneSetup H hωQ hω1 hsaQ (hyp.conj_distinguishedInvolution_ne_one a) hne
  rw [e₂, hg1, hf1, hh1, hyp.t_conj_sq_of_mem_KSet haK, inv_pow, inv_inv]

/-- **Peterfalvi Part II, Ch. IV §2, step (3)** (p. 123): for `a ∈ K` and `ω ∈ Q^#`
with `s^a ω ≠ 1`,

  `f(s^a ω) = f(s^{a⁻¹} g(ω))^{h(ω)^t} f(ω)`.

This is (H6) at `x = s^a`, `y = ω`, using only `f(s^a) = s^{a⁻¹}` from step (1).

⚠ The book prints this as `f(ω s^a) = f(g(ω) s^{a⁻¹})^{h(ω)^t} f(ω)`, i.e. with both
products written in the opposite order.  The two agree because `s^a` and `s^{a⁻¹}` are
involutions of `Q`, hence lie in `Q₀ = Z(Q)`, and so commute with everything in `Q`;
the statement here is the one (H6) yields directly, without that input. -/
theorem f_conj_distinguishedInvolution_mul (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {a ω : G} (haK : a ∈ hyp.KSet) (hωQ : ω ∈ hyp.Q) (hω1 : ω ≠ 1)
    (hne : (a⁻¹ * hyp.distinguishedInvolution * a) * ω ≠ 1) :
    f ((a⁻¹ * hyp.distinguishedInvolution * a) * ω)
      = (hyp.t * h ω * hyp.t)⁻¹ *
        f ((a * hyp.distinguishedInvolution * a⁻¹) * g ω) *
        (hyp.t * h ω * hyp.t) * f ω := by
  obtain ⟨hf1, -, -⟩ := hyp.fgh_at_conj_distinguishedInvolution H hC2 haK
  have hsaQ : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q :=
    hyp.rankOneSetup.DQ a haK.1 _ hyp.distinguishedInvolution_mem_Q
  obtain ⟨-, e₂, -, -⟩ :=
    hSix hyp.rankOneSetup H hsaQ (hyp.conj_distinguishedInvolution_ne_one a) hωQ hω1 hne
  rw [e₂, hf1]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
