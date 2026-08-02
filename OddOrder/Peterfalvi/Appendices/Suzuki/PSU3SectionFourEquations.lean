/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourSemilinear

/-!
# Peterfalvi Part II, Ch. IV §4: the equations (5) and (6)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, p. 133.  Writing `X = f(ω s^b)‾` and `Y = X^η`:

* **(5)** `ζ X = a^{-2μ} Y + ω̄`,
* **(6)** `b² X = ζ⁻¹ Y + ω̄`.

(6) is (4) read at `b` instead of `a`.  (5) is (4) at `a` with `f(ω s^a)‾` replaced by the
right-hand side of (3) — and that substitution is where the semilinearity is used for the
first time: `(ζ a⁻² X)^η = (ζ a⁻²)^μ X^η = ζ a^{-2μ} X^η`, the last step because `μ` fixes
`ζ` (the book takes `ζ ∈ C_W(P)` and `η ∈ P`, so `η` centralizes `ζ`).

The scalars here are the *inverses* of the book's throughout, as everywhere in Ch. IV: its
`x^d` is conjugation by `d⁻¹`, whereas `coord_act` is stated for conjugation by `d`.  So
the book's `ζ` is `μ(1, ζ)⁻¹` and its `a²` is `μ(a², 1)`.  Written out, the two equations
below are `sectionFour_seven_book`'s `h5`, `h6` at

  `X := f(ω s^b)‾`,  `Y := (f(ω s^b)‾)^η`,  `w := ω̄`,
  `A := μ(a², 1)^μ`,  `B := μ(b², 1)`,  `c := μ(1, ζ)⁻¹`.

## Main results

* `Hypothesis.sectionFour_four_coordConjD` — (4) with its `η`-conjugate written through
  `coordConjD`, which is the form (5) and (6) compose with.
* `Hypothesis.sectionFour_six_linear` — **(6)**.
* `Hypothesis.sectionFour_five_linear` — **(5)**, from (4) and (3).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp in
/-- **(4) with the `η`-conjugate read through `coordConjD`** (Peterfalvi Part II,
Ch. IV §4, p. 133).

`sectionFour_four_linear` states the book's `f(ω s^a)‾^η` as the coordinate of the group
element `η · f(ω s^a) · η⁻¹`; this is the same equation with that coordinate presented as
the image of `f(ω s^a)‾` under the additive map `coordConjD`, which is what the
semilinearity `(c x)^η = c^μ x^η` applies to. -/
theorem sectionFour_four_coordConjD (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ζ ω a η : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (haK : a ∈ hyp.KSet) (ha2 : a ^ 2 ∈ hyp.K) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hηζ : η * ζ = ζ * η) (hhω : h ω = ζ ^ 3 * η) (htη : hyp.t * η * hyp.t = η)
    (hηD : η ∈ hyp.D)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q) :
    ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
        * M.coord (Additive.ofMul (QuotientGroup.mk
            (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))
      = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
          * hyp.coordConjD M ⟨η, hηD⟩
            (M.coord (Additive.ofMul (QuotientGroup.mk
              (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q))))
        + M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
  have hEQ : η * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * η⁻¹ ∈ hyp.Q :=
    hyp.conj_mem_Q_of_mem_D hηD hXQ
  rw [hyp.coordConjD_coord_val M hηD hXQ hEQ rfl]
  exact hyp.sectionFour_four_linear H hC2 M hZ hζ hωQ hωQ0 haK ha2 hf hηζ hhω htη hXQ hEQ

include hyp in
/-- **🎯 Peterfalvi Part II, Ch. IV §4, equation (6)** (p. 133):

  `b² f(ω s^b)‾ = ζ⁻¹ f(ω s^b)‾^η + ω̄`.

"Equation (4) holds with `b` in the place of `a`" — literally `sectionFour_four_coordConjD`
at `b`.  It is recorded separately only so that the `A`, `B`, `c` of the arithmetic of
(7)–(9) can be read off both equations side by side. -/
theorem sectionFour_six_linear (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ζ ω b η : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hbK : b ∈ hyp.KSet) (hb2 : b ^ 2 ∈ hyp.K) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hηζ : η * ζ = ζ * η) (hhω : h ω = ζ ^ 3 * η) (htη : hyp.t * η * hyp.t = η)
    (hηD : η ∈ hyp.D)
    (hYQ : f (ω * (b * hyp.distinguishedInvolution * b⁻¹)) ∈ hyp.Q) :
    ((M.mu (hyp.kActor hb2, 1) : M.Eˣ) : M.E)
        * M.coord (Additive.ofMul (QuotientGroup.mk
            (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q)))
      = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
          * hyp.coordConjD M ⟨η, hηD⟩
            (M.coord (Additive.ofMul (QuotientGroup.mk
              (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q))))
        + M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) :=
  hyp.sectionFour_four_coordConjD H hC2 M hZ hζ hωQ hωQ0 hbK hb2 hf hηζ hhω htη hηD hYQ

include hyp in
/-- **🎯 Peterfalvi Part II, Ch. IV §4, equation (3)** (p. 133):

  `f(ω s^a)‾ = f(ω^{-ζ} s^{a⁻¹})^{a⁻²}‾ = ζ a⁻² f(ω s^b)‾`.

"by (2) of §2" — which is exactly what `stepTen_quotient_coord` formalizes, and that lemma
is already stated for an arbitrary `ω`, `ζ`, `y` with `f(ω) = (ω y)^ζ`.  Only two things
are §4-specific:

* the exponent-`4` bridge.  §4's hypothesis is `f(ω) = (ω⁻¹)^ζ` while stage (10) wants
  `f(ω) = (ω y)^ζ`; with `y = ω²` the two agree because `ω⁴ = 1` — `y` lies in
  `Q₀`, whose elements are involutions.  This is the "`C_Q(P)` has exponent `4`" of
  step (1), read on the element `ω`.
* `b` is presented through the book's `s^b = y · s^{a⁻¹}` (the group form of
  `b^{1+θ} = α + a^{-(1+θ)}`), so that the right-hand side is a `b`-instance of the same
  unknown. -/
theorem sectionFour_three_coord (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ζ ω y a b : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsq : ω * ω = y) (haK : a ∈ hyp.K)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hb : b * hyp.distinguishedInvolution * b⁻¹
      = y * (a⁻¹ * hyp.distinguishedInvolution * a))
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q)
    (hYQ : f (ω * (b * hyp.distinguishedInvolution * b⁻¹)) ∈ hyp.Q) :
    M.coord (Additive.ofMul (QuotientGroup.mk
        (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))
      = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹
        * ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)⁻¹
        * M.coord (Additive.ofMul (QuotientGroup.mk
            (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q))) := by
  -- `ω⁴ = 1`, so `ω y = ω³ = ω⁻¹`
  have hy2 : y * y = 1 := by
    have := hyp.sq_eq_one_of_mem_Q0 hyQ0
    rwa [sq] at this
  have hω4 : ω * y = ω⁻¹ := by
    have h4 : ω * ω * (ω * ω) = 1 := by rw [hsq]; exact hy2
    calc ω * y = ω * (ω * ω) := by rw [hsq]
      _ = (ω * ω * (ω * ω)) * ω⁻¹ := by group
      _ = ω⁻¹ := by rw [h4, one_mul]
  have hfω : f ω = ζ⁻¹ * (ω * y) * ζ := by rw [hω4]; exact hf
  rw [hyp.stepTen_quotient_coord H hC2 M hZ hζ hωQ hωQ0 hyQ0 haK hfω hb.symm hXQ hYQ,
    mul_inv]
  ring

include hyp in
/-- **🎯 Peterfalvi Part II, Ch. IV §4, equation (5)** (p. 133):

  `ζ f(ω s^b)‾ = a^{-2μ} f(ω s^b)‾^η + ω̄`.

> Assume again that `a ≠ α^{-τ}` and, in (4), replace `f(ω s^a)‾` by the right-hand side
> of (3) to see that (5).

`h3` is that right-hand side, in the inverted scalars of the repository: the book's
`f(ω s^a)‾ = ζ a⁻² f(ω s^b)‾`.  Substituting it into (4) leaves `a²·ζ a⁻² = ζ` on the
left; on the right the semilinearity
(`coordConjD_mul_eq_coordFieldAut_mul`) turns `(ζ a⁻² X)^η` into `(ζ a⁻²)^μ X^η`, and
`μ` fixes `ζ` (`coordFieldAut_muW_eq_self`, available because `η` centralizes `ζ`), so
`ζ⁻¹·ζ` cancels and only `a^{-2μ}` survives. -/
theorem sectionFour_five_linear (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m) (s : hyp.LemmaFiveSetup m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {ζ ω a b η : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (haK : a ∈ hyp.KSet) (ha2 : a ^ 2 ∈ hyp.K) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hηζ : η * ζ = ζ * η) (hhω : h ω = ζ ^ 3 * η) (htη : hyp.t * η * hyp.t = η)
    (hηD : η ∈ hyp.D)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q)
    (hYQ : f (ω * (b * hyp.distinguishedInvolution * b⁻¹)) ∈ hyp.Q)
    (h3 : M.coord (Additive.ofMul (QuotientGroup.mk
          (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))
        = ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹
          * ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)⁻¹
          * M.coord (Additive.ofMul (QuotientGroup.mk
              (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q)))) :
    ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹
        * M.coord (Additive.ofMul (QuotientGroup.mk
            (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q)))
      = (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
            ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E))⁻¹
          * hyp.coordConjD M ⟨η, hηD⟩
            (M.coord (Additive.ofMul (QuotientGroup.mk
              (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q))))
        + M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
  set A := ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E) with hAdef
  set C := ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) with hCdef
  set σ := hyp.coordFieldAut s M hm hQ0card hηD hζ hznot with hσdef
  set Ψ := hyp.coordConjD M ⟨η, hηD⟩ with hΨdef
  set Xb := M.coord (Additive.ofMul (QuotientGroup.mk
    (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q))) with hXbdef
  have hA : A ≠ 0 := Units.ne_zero _
  have hC : C ≠ 0 := Units.ne_zero _
  -- (4) at `a`
  have h4 := hyp.sectionFour_four_coordConjD H hC2 M hZ hζ hωQ hωQ0 haK ha2 hf hηζ hhω
    htη hηD hXQ
  -- `μ` fixes `ζ`, because `η` centralizes it
  have hfixζ : η * ζ * η⁻¹ = ζ := by
    rw [hηζ, mul_assoc, mul_inv_cancel, mul_one]
  have hσC : σ C = C :=
    hyp.coordFieldAut_muW_eq_self s M hm hQ0card hηD hζ hznot hζ hfixζ
  have hσprod : σ (C⁻¹ * A⁻¹) = C⁻¹ * (σ A)⁻¹ := by
    rw [map_mul, map_inv₀, map_inv₀, hσC]
  -- the semilinear image of (3)
  have hΨa : Ψ (C⁻¹ * A⁻¹ * Xb) = C⁻¹ * (σ A)⁻¹ * Ψ Xb := by
    rw [hΨdef, hσdef,
      hyp.coordConjD_mul_eq_coordFieldAut_mul s M hm hQ0card hηD hζ hznot _ Xb, hσprod]
  rw [h3, hΨa] at h4
  -- clear the two cancelling scalars
  have e1 : A * (C⁻¹ * A⁻¹ * Xb) = C⁻¹ * Xb := by
    rw [show A * (C⁻¹ * A⁻¹ * Xb) = (A * A⁻¹) * (C⁻¹ * Xb) from by ring,
      mul_inv_cancel₀ hA, one_mul]
  have e2 : C * (C⁻¹ * (σ A)⁻¹ * Ψ Xb) = (σ A)⁻¹ * Ψ Xb := by
    rw [show C * (C⁻¹ * (σ A)⁻¹ * Ψ Xb) = (C * C⁻¹) * ((σ A)⁻¹ * Ψ Xb) from by ring,
      mul_inv_cancel₀ hC, one_mul]
  rw [e1, e2] at h4
  exact h4

include hyp in
/-- **🎯 (5), with (3) discharged** (Peterfalvi Part II, Ch. IV §4, p. 133).

The composite of `sectionFour_three_coord` and `sectionFour_five_linear`: the book's
sentence "replace `f(ω s^a)‾` by the right-hand side of (3)" in one step, so that a caller
supplies only the group-level data (`ω² = y`, `s^b = y · s^{a⁻¹}`, `f(ω) = (ω⁻¹)^ζ`,
`h(ω) = ζ³η`). -/
theorem sectionFour_five_of_three (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m) (s : hyp.LemmaFiveSetup m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    {ζ ω y a b η : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsq : ω * ω = y) (haK : a ∈ hyp.K)
    (haKset : a ∈ hyp.KSet) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hηζ : η * ζ = ζ * η) (hhω : h ω = ζ ^ 3 * η) (htη : hyp.t * η * hyp.t = η)
    (hηD : η ∈ hyp.D)
    (hznot : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E)
      ∉ OddOrder.FiniteField.frobFixedSubfield M.E 2 m)
    (hb : b * hyp.distinguishedInvolution * b⁻¹
      = y * (a⁻¹ * hyp.distinguishedInvolution * a))
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q)
    (hYQ : f (ω * (b * hyp.distinguishedInvolution * b⁻¹)) ∈ hyp.Q) :
    ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹
        * M.coord (Additive.ofMul (QuotientGroup.mk
            (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q)))
      = (hyp.coordFieldAut s M hm hQ0card hηD hζ hznot
            ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E))⁻¹
          * hyp.coordConjD M ⟨η, hηD⟩
            (M.coord (Additive.ofMul (QuotientGroup.mk
              (⟨f (ω * (b * hyp.distinguishedInvolution * b⁻¹)), hYQ⟩ : ↥hyp.Q))))
        + M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) :=
  hyp.sectionFour_five_linear H hC2 M s hZ hm hQ0card hζ hωQ hωQ0 haKset (pow_mem haK 2)
    hf hηζ hhω htη hηD hznot hXQ hYQ
    (hyp.sectionFour_three_coord H hC2 M hZ hζ hωQ hωQ0 hyQ0 hsq haK hf hb hXQ hYQ)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
