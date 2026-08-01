/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3StepTwenty

/-!
# Peterfalvi Part II, Ch. IV §3: determination of `f`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3, pp. 129–134.

> **Proposition.** Suppose that there are elements `ω ∈ Q − Q₀` and `ζ ∈ W^#` such that
> `f(ω) = (ω⁻¹)^ζ` and `h(ω) ∈ W`.  Then `θ = 1` and `f(ρ) = (ρ̄/y, 1/y)` for all
> `ρ = (ρ̄, y) ∈ Q − Q₀`.

Both hypotheses are supplied by §2: `f_eq_conj_inv_of_stepTwenty_chain` and `h_mem_W`.

This file starts the proof.  Its first stage (the book's (1), p. 130) opens with the
computation `(f ∘ j)³(ω⁻¹) = ω^{-ζ³}`, which is three applications of (H3) to the
hypothesis, and then reads off `h(ω⁻¹) = ζ⁻³` from (H5) — a step the book justifies by
`h(ω⁻¹) = h(ω)^{-t} ∈ W`, and which here is again the freeness of the `D`-action.

## Main results

* `Hypothesis.fj_cube_of_f_eq_conj_inv` — `(f ∘ j)³(ω⁻¹) = ω^{-ζ³}`.
* `Hypothesis.f_inv_eq`, `Hypothesis.g_inv_eq` — `f(ω⁻¹) = ω^{ζ⁻¹}` and
  `g(ω⁻¹) = ω^ζ`.
* `Hypothesis.h_inv_eq` — `h(ω⁻¹) = ζ⁻³`.
* `Hypothesis.h_eq_zpow_three` — `h(ω) = ζ³`, given `h(ω) ∈ W`.
* `Hypothesis.stepOne_chain` — §3's stage (1).
* `Hypothesis.f_conj_zeta_of_mem_Q0` — the two `f`-values of stage (1) as `ζ^{±1}`-conjugates
  of `f(ω s^a)`.
* `Hypothesis.stepTwo_linear` — §3's stage (2), the linear equation
  `(a² + ζ⁻¹) · f(ω s^a)‾ = ω̄` in `E`.
* `Hypothesis.stepTen_quotient_coord` — §2's stage (10) read in `E`.
* `Hypothesis.stepThree_sq_eq` — the group-to-field bridge of §3 (3):
  `b² = ζ + ζ⁻¹ + a⁻²`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- `t` centralizes every power of an element of `W`. -/
theorem conj_t_pow_eq {ζ : G} (hζ : ζ ∈ hyp.W) (n : ℕ) :
    hyp.t * ζ ^ n * hyp.t = ζ ^ n := by
  have hc : Commute ζ hyp.t := hyp.commute_t_of_mem_V (hyp.W_le_V hζ)
  rw [← (hc.pow_left n).eq, mul_assoc, hyp.rankOneSetup.invol, mul_one]

/-- **`(f ∘ j)³(ω⁻¹) = ω^{-ζ³}`** (Peterfalvi Part II, p. 130, opening of §3's stage (1)).

Each of the three steps is (H3) applied to `f(ω) = (ω⁻¹)^ζ`, the twist `a ↦ a^t` being
trivial on `W`. -/
theorem fj_cube_of_f_eq_conj_inv (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    f ((f ((f ω)⁻¹))⁻¹) = (ζ ^ 3)⁻¹ * ω⁻¹ * ζ ^ 3 := by
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hωQ hω1 hζD
  have htζt : hyp.t * ζ * hyp.t = ζ := by
    have hp := hyp.conj_t_pow_eq hζ 1
    rwa [pow_one] at hp
  rw [htζt] at h3
  -- second step
  have e2 : f ((f ω)⁻¹) = (ζ ^ 2)⁻¹ * ω⁻¹ * ζ ^ 2 := by
    have hinv1 : (f ω)⁻¹ = ζ⁻¹ * ω * ζ := by rw [hf]; group
    rw [hinv1, h3, hf, pow_two]
    group
  -- third step, by (H3) at `ζ²`
  have hζ2D : ζ ^ 2 ∈ hyp.D := pow_mem hζD 2
  obtain ⟨h3'', -, -⟩ := hThree hyp.rankOneSetup H hωQ hω1 hζ2D
  rw [hyp.conj_t_pow_eq hζ 2] at h3''
  have hinv2 : (f ((f ω)⁻¹))⁻¹ = (ζ ^ 2)⁻¹ * ω * ζ ^ 2 := by rw [e2]; group
  rw [hinv2, h3'', hf, pow_two, pow_three']
  group

/-- **`f(ω⁻¹) = ω^{ζ⁻¹}`** (Peterfalvi Part II, p. 130): applying `f` to the hypothesis
`f(ω) = (ω⁻¹)^ζ` and moving the conjugation across by (H3). -/
theorem f_inv_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    f ω⁻¹ = ζ * ω * ζ⁻¹ := by
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  have hωinvQ : ω⁻¹ ∈ hyp.Q := hyp.Q.inv_mem hωQ
  have hωinv1 : ω⁻¹ ≠ 1 := fun hc => hω1 (inv_eq_one.mp hc)
  have htζt : hyp.t * ζ * hyp.t = ζ := by
    have hp := hyp.conj_t_pow_eq hζ 1
    rwa [pow_one] at hp
  obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hωinvQ hωinv1 hζD
  rw [htζt] at h3
  have h2 : f (f ω) = ω := (hTwo hyp.rankOneSetup H hωQ hω1).1
  rw [hf, h3] at h2
  calc f ω⁻¹ = ζ * (ζ⁻¹ * f ω⁻¹ * ζ) * ζ⁻¹ := by group
    _ = ζ * ω * ζ⁻¹ := by rw [h2]

/-- **`g(ω⁻¹) = ω^ζ`** (Peterfalvi Part II, p. 130): (H1) says `g(x⁻¹) = f(x)⁻¹`. -/
theorem g_inv_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    g ω⁻¹ = ζ⁻¹ * ω * ζ := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨-, o2, -⟩ := hOne hyp.rankOneSetup H hωQ hω1
  rw [o2, hf]
  group

/-- **`h(ω⁻¹) = ζ⁻³`** (Peterfalvi Part II, p. 130).

(H5) says `(f ∘ j)³(ω⁻¹) = (ω⁻¹)^{h(ω⁻¹)⁻¹}`, and the left side is `ω^{-ζ³}`; so
`ζ³ h(ω⁻¹) ∈ D` fixes `ω⁻¹`, hence is trivial by `eq_one_of_conj_eq_mul_Q0_of_mem_D`.

The book instead argues that `h(ω⁻¹) = h(ω)^{-t}` lies in `W` and reads the exponent off
there; the freeness makes the detour unnecessary. -/
theorem h_inv_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    h ω⁻¹ = (ζ ^ 3)⁻¹ := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  have hωinvQ : ω⁻¹ ∈ hyp.Q := hyp.Q.inv_mem hωQ
  have hωinvQ0 : ω⁻¹ ∉ hyp.Q0 := fun hc => hωQ0 (by simpa using hyp.Q0.inv_mem hc)
  have hωinv1 : ω⁻¹ ≠ 1 := fun hc => hω1 (inv_eq_one.mp hc)
  -- (H5) at `ω⁻¹`, whose `j` is `ω`
  have h5 := hFive hyp.rankOneSetup H hωinvQ hωinv1
  rw [inv_inv, hyp.fj_cube_of_f_eq_conj_inv H hζ hωQ hωQ0 hf] at h5
  -- `ζ³ · h(ω⁻¹)` fixes `ω⁻¹`
  have hζ3D : ζ ^ 3 ∈ hyp.D := pow_mem (hyp.V_le_D (hyp.W_le_V hζ)) 3
  have hhD : h ω⁻¹ ∈ hyp.D := H.h_mem hωinvQ hωinv1
  have hcD : ζ ^ 3 * h ω⁻¹ ∈ hyp.D := hyp.D.mul_mem hζ3D hhD
  have hconj : (ζ ^ 3 * h ω⁻¹)⁻¹ * ω⁻¹ * (ζ ^ 3 * h ω⁻¹) = ω⁻¹ * 1 := by
    rw [mul_one]
    calc (ζ ^ 3 * h ω⁻¹)⁻¹ * ω⁻¹ * (ζ ^ 3 * h ω⁻¹)
        = (h ω⁻¹)⁻¹ * ((ζ ^ 3)⁻¹ * ω⁻¹ * ζ ^ 3) * h ω⁻¹ := by group
      _ = (h ω⁻¹)⁻¹ * (h ω⁻¹ * ω⁻¹ * (h ω⁻¹)⁻¹) * h ω⁻¹ := by rw [← h5]
      _ = ω⁻¹ := by group
  have hone := hyp.eq_one_of_conj_eq_mul_Q0_of_mem_D M hZ hmu hVW hωinvQ hωinvQ0 hcD
    hyp.Q0.one_mem hconj
  calc h ω⁻¹ = (ζ ^ 3)⁻¹ * (ζ ^ 3 * h ω⁻¹) := by group
    _ = (ζ ^ 3)⁻¹ := by rw [hone, mul_one]

/-- **`h(ω) = ζ³`** (Peterfalvi Part II, p. 130): with `h(ω) ∈ W`, the twist `a ↦ a^t` of
(H1) is trivial, so `h(ω⁻¹) = h(ω)⁻¹`. -/
theorem h_eq_zpow_three (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) (hhW : h ω ∈ hyp.W) :
    h ω = ζ ^ 3 := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨-, -, o3⟩ := hOne hyp.rankOneSetup H hωQ hω1
  have hth : hyp.t * h ω * hyp.t = h ω := by
    have hc : Commute (h ω) hyp.t := hyp.commute_t_of_mem_V (hyp.W_le_V hhW)
    rw [← hc.eq, mul_assoc, hyp.rankOneSetup.invol, mul_one]
  rw [hth] at o3
  have hkey := hyp.h_inv_eq H M hZ hmu hVW hζ hωQ hωQ0 hf
  rw [o3] at hkey
  exact inv_injective hkey

/-- **§3, stage (1)** (Peterfalvi Part II, p. 130):

  `f(ω^{ζ⁻¹} s^{a⁻¹})^{a²} s^a = f(ω^ζ s^a)^{ζ⁻³} ω^{ζ⁻¹}`   for `a ∈ K`.

Both sides are the same element `f(ω⁻¹ s^a)`, read through the two halves of (H6) that
§2 packaged as its steps (2) and (3) — the left through
`f_mul_conj_distinguishedInvolution`, the right through
`f_conj_distinguishedInvolution_mul`.  What makes them meet is that the conjugates of
`s` lie in `Q₀ = Z(Q)`, so the two orders of the product agree; the substitutions are
`f(ω⁻¹) = ω^{ζ⁻¹}`, `g(ω⁻¹) = ω^ζ` and `h(ω⁻¹) = ζ⁻³`, whose `t`-twist is again `ζ⁻³`
because `ζ ∈ W`. -/
theorem stepOne_chain (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω a : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (haK : a ∈ hyp.KSet) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ) :
    a ^ 2 * f ((ζ * ω * ζ⁻¹) * (a * hyp.distinguishedInvolution * a⁻¹)) * (a⁻¹) ^ 2
        * (a * hyp.distinguishedInvolution * a⁻¹)
      = (ζ ^ 3) * f ((a * hyp.distinguishedInvolution * a⁻¹) * (ζ⁻¹ * ω * ζ))
        * (ζ ^ 3)⁻¹ * (ζ * ω * ζ⁻¹) := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  have hωinvQ : ω⁻¹ ∈ hyp.Q := hyp.Q.inv_mem hωQ
  have hωinvQ0 : ω⁻¹ ∉ hyp.Q0 := fun hc => hωQ0 (by simpa using hyp.Q0.inv_mem hc)
  have hωinv1 : ω⁻¹ ≠ 1 := fun hc => hω1 (inv_eq_one.mp hc)
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 := hyp.distinguishedInvolution_mem_Q0
  have hsaQ0 : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q0 := by
    have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem haK.1) hsQ0
    rwa [inv_inv] at hmem
  obtain ⟨-, hprodQ0⟩ := hyp.mul_mem_sdiff_Q0 hωinvQ hωinvQ0 hsaQ0
  have hne1 : ω⁻¹ * (a⁻¹ * hyp.distinguishedInvolution * a) ≠ 1 :=
    fun hc => hprodQ0 (hc ▸ hyp.Q0.one_mem)
  -- the two orders of the product agree, `s^a` being central in `Q`
  have hcomm : ω⁻¹ * (a⁻¹ * hyp.distinguishedInvolution * a)
      = (a⁻¹ * hyp.distinguishedInvolution * a) * ω⁻¹ :=
    Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hsaQ0) ω⁻¹ hωinvQ
  have hne2 : (a⁻¹ * hyp.distinguishedInvolution * a) * ω⁻¹ ≠ 1 := by
    rw [← hcomm]; exact hne1
  -- the two readings of `f(ω⁻¹ s^a)`
  have hA := hyp.f_mul_conj_distinguishedInvolution H hC2 haK hωinvQ hωinv1 hne1
  have hB := hyp.f_conj_distinguishedInvolution_mul H hC2 haK hωinvQ hωinv1 hne2
  rw [← hcomm] at hB
  rw [hyp.f_inv_eq H hζ hωQ hωQ0 hf] at hA
  rw [hyp.g_inv_eq H hωQ hωQ0 hf, hyp.f_inv_eq H hζ hωQ hωQ0 hf,
    hyp.h_inv_eq H M hZ hmu hVW hζ hωQ hωQ0 hf] at hB
  -- the `t`-twist of `ζ⁻³` is `ζ⁻³`
  have htinv : hyp.t⁻¹ = hyp.t := inv_eq_of_mul_eq_one_right hyp.rankOneSetup.invol
  have htw : hyp.t * (ζ ^ 3)⁻¹ * hyp.t = (ζ ^ 3)⁻¹ := by
    have hp := hyp.conj_t_pow_eq hζ 3
    calc hyp.t * (ζ ^ 3)⁻¹ * hyp.t = (hyp.t⁻¹ * ζ ^ 3 * hyp.t⁻¹)⁻¹ := by group
      _ = (hyp.t * ζ ^ 3 * hyp.t)⁻¹ := by rw [htinv]
      _ = (ζ ^ 3)⁻¹ := by rw [hp]
  rw [htw, inv_inv] at hB
  exact hA.symm.trans hB

/-- **The two `f`-values of stage (1) are conjugates of a single one** (Peterfalvi
Part II, p. 130, entering stage (2)).

Writing `X = f(ω s^a)`, the arguments occurring in `stepOne_chain` are `ω s^a` conjugated
by `ζ^{±1}`: the conjugation does not move `s^a`, which lies in `Q₀ = Z(Q)`, and (H3)
moves `f` across it without a twist because `t` centralizes `W`.

This is what turns stage (1) into a *linear* equation for the single unknown `X̄` in `E`.
-/
theorem f_conj_zeta_of_mem_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω z : G} (hζ : ζ ∈ hyp.W) (hzQ0 : z ∈ hyp.Q0)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    f ((ζ * ω * ζ⁻¹) * z) = ζ * f (ω * z) * ζ⁻¹ ∧
      f (z * (ζ⁻¹ * ω * ζ)) = ζ⁻¹ * f (ω * z) * ζ := by
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have htζt : hyp.t * ζ * hyp.t = ζ := by
    have hp := hyp.conj_t_pow_eq hζ 1
    rwa [pow_one] at hp
  have htinv : hyp.t⁻¹ = hyp.t := inv_eq_of_mul_eq_one_right hyp.rankOneSetup.invol
  have htζit : hyp.t * ζ⁻¹ * hyp.t = ζ⁻¹ := by
    calc hyp.t * ζ⁻¹ * hyp.t = (hyp.t⁻¹ * ζ * hyp.t⁻¹)⁻¹ := by group
      _ = (hyp.t * ζ * hyp.t)⁻¹ := by rw [htinv]
      _ = ζ⁻¹ := by rw [htζt]
  obtain ⟨hωzQ, hωzQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hzQ0
  have hωz1 : ω * z ≠ 1 := fun hc => hωzQ0 (hc ▸ hyp.Q0.one_mem)
  have hcz : ζ * z = z * ζ := hyp.W_centralizes_Q0 hζ hzQ0
  constructor
  · -- `(ζ ω ζ⁻¹) z = ζ (ω z) ζ⁻¹`, then (H3) at `ζ⁻¹`
    obtain ⟨h3, -, -⟩ :=
      hThree hyp.rankOneSetup H hωzQ hωz1 (hyp.D.inv_mem hζD)
    rw [htζit, inv_inv] at h3
    have harg : (ζ * ω * ζ⁻¹) * z = ζ * (ω * z) * ζ⁻¹ := by
      calc (ζ * ω * ζ⁻¹) * z = ζ * ω * (ζ⁻¹ * z * ζ) * ζ⁻¹ := by group
        _ = ζ * ω * z * ζ⁻¹ := by
            rw [show ζ⁻¹ * z * ζ = z from by
              calc ζ⁻¹ * z * ζ = ζ⁻¹ * (z * ζ) := by group
                _ = ζ⁻¹ * (ζ * z) := by rw [← hcz]
                _ = z := by group]
        _ = ζ * (ω * z) * ζ⁻¹ := by group
    rw [harg, h3]
  · -- `z (ζ⁻¹ ω ζ) = ζ⁻¹ (ω z) ζ`, then (H3) at `ζ`
    obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hωzQ hωz1 hζD
    rw [htζt] at h3
    have harg : z * (ζ⁻¹ * ω * ζ) = ζ⁻¹ * (ω * z) * ζ := by
      calc z * (ζ⁻¹ * ω * ζ) = ζ⁻¹ * (ζ * z * ζ⁻¹) * ω * ζ := by group
        _ = ζ⁻¹ * z * ω * ζ := by
            rw [show ζ * z * ζ⁻¹ = z from by
              calc ζ * z * ζ⁻¹ = (z * ζ) * ζ⁻¹ := by rw [hcz]
                _ = z := by group]
        _ = ζ⁻¹ * (ω * z) * ζ := by
            have hzω : z * ω = ω * z :=
              (Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hzQ0) ω hωQ).symm
            calc ζ⁻¹ * z * ω * ζ = ζ⁻¹ * (z * ω) * ζ := by group
              _ = ζ⁻¹ * (ω * z) * ζ := by rw [hzω]
    rw [harg, h3]

/-- **§3, stage (2)** (Peterfalvi Part II, p. 130): stage (1), read in the coordinates of
`Q ⧸ Z(Q) ≅ E`, is the linear equation

  `(a² + ζ⁻¹) · f(ω s^a)‾ = ω̄`.

The conjugate `s^a` lies in `Q₀ = Z(Q)` and so disappears in the quotient
(`coord_mk_eq_zero_of_mem_Q0`); each conjugation becomes multiplication by a scalar
(`coord_conj_eq`), and the products split by additivity (`coord_mk_mul`).

The book's `ζ⁻¹` is `μ(1, ζ)` here — its `x^d` is conjugation by `d⁻¹`, whereas `coord_act`
is stated for conjugation by `d`. -/
theorem stepTwo_linear (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω a : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (haK : a ∈ hyp.KSet) (ha2 : a ^ 2 ∈ hyp.K) (hf : f ω = ζ⁻¹ * ω⁻¹ * ζ)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q) :
    (((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E)
        + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E))
      * M.coord (Additive.ofMul (QuotientGroup.mk
          (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
  classical
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hconjQ : ∀ {c x : G}, c ∈ hyp.D → x ∈ hyp.Q → c * x * c⁻¹ ∈ hyp.Q := by
    intro c x hc hx
    have hm := hyp.rankOneSetup.DQ c⁻¹ (hyp.D.inv_mem hc) x hx
    rwa [inv_inv] at hm
  have hzQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D haK.1 hyp.distinguishedInvolution_mem_Q0
  have hzQ : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q := hyp.Q0_le_Q hzQ0
  -- the chain of stage (1), with both `f`-values expressed through `X`
  obtain ⟨hcL, hcR⟩ := hyp.f_conj_zeta_of_mem_Q0 H hζ hzQ0 hωQ hωQ0
  have hchain := hyp.stepOne_chain H hC2 M hZ hmu hVW hζ hωQ hωQ0 haK hf
  rw [hcL, hcR] at hchain
  -- memberships
  have ha2D : a ^ 2 ∈ hyp.D := hyp.K_le_D ha2
  have hζ3D : ζ ^ 3 ∈ hyp.D := pow_mem hζD 3
  have hYQ : ζ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ⁻¹ ∈ hyp.Q :=
    hconjQ hζD hXQ
  have hZ'Q : ζ⁻¹ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ ∈ hyp.Q := by
    have hm := hconjQ (hyp.D.inv_mem hζD) hXQ
    rwa [inv_inv] at hm
  have hAQ : a ^ 2 * (ζ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ⁻¹)
      * (a⁻¹) ^ 2 ∈ hyp.Q := by
    have hm := hconjQ ha2D hYQ
    rwa [show (a ^ 2)⁻¹ = (a⁻¹) ^ 2 from by group] at hm
  have hBQ : ζ ^ 3 * (ζ⁻¹ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ)
      * (ζ ^ 3)⁻¹ ∈ hyp.Q := hconjQ hζ3D hZ'Q
  have hCQ : ζ * ω * ζ⁻¹ ∈ hyp.Q := hconjQ hζD hωQ
  have hLQ : a ^ 2 * (ζ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ⁻¹)
      * (a⁻¹) ^ 2 * (a * hyp.distinguishedInvolution * a⁻¹) ∈ hyp.Q :=
    hyp.Q.mul_mem hAQ hzQ
  have hRQ : ζ ^ 3 * (ζ⁻¹ * f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) * ζ)
      * (ζ ^ 3)⁻¹ * (ζ * ω * ζ⁻¹) ∈ hyp.Q := hyp.Q.mul_mem hBQ hCQ
  -- one coordinate of each side
  have hone : (⟨(1 : G), hyp.W.one_mem⟩ : ↥hyp.W) = 1 := rfl
  have honeK : (hyp.kActor (hyp.K.one_mem)) = 1 := hyp.kActor_one hyp.K.one_mem
  have hL : M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hLQ⟩ : ↥hyp.Q)))
      = ((M.mu (hyp.kActor ha2, 1) : M.Eˣ) : M.E) *
        (((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) *
          M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hXQ⟩ : ↥hyp.Q)))) := by
    rw [hyp.coord_mk_mul M hAQ hzQ hLQ,
      hyp.coord_mk_eq_zero_of_mem_Q0 M hZ hzQ0 hzQ, add_zero,
      hyp.coord_conj_eq M ha2 hyp.W.one_mem hYQ hAQ (by group),
      hyp.coord_conj_eq M hyp.K.one_mem hζ hXQ hYQ (by group)]
    rw [hone, honeK]
  have hR : M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hRQ⟩ : ↥hyp.Q)))
      = ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3) : M.Eˣ) : M.E) *
          (((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹) : M.Eˣ) : M.E) *
            M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hXQ⟩ : ↥hyp.Q))))
        + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E) *
          M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := by
    rw [hyp.coord_mk_mul M hBQ hCQ hRQ,
      hyp.coord_conj_eq M hyp.K.one_mem (hyp.W.pow_mem hζ 3) hZ'Q hBQ (by group),
      hyp.coord_conj_eq M hyp.K.one_mem (hyp.W.inv_mem hζ) hXQ hZ'Q (by group),
      hyp.coord_conj_eq M hyp.K.one_mem hζ hωQ hCQ (by group)]
    rw [honeK]
    rfl
  -- the two sides of stage (1) are the same element, so their coordinates agree
  have hcoordeq : M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hLQ⟩ : ↥hyp.Q)))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨_, hRQ⟩ : ↥hyp.Q))) :=
    congrArg (fun q : ↥hyp.Q => M.coord (Additive.ofMul (QuotientGroup.mk q)))
      (Subtype.ext hchain)
  have hprod : ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3) *
      ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹)
      = ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) ^ 2 := by
    have e1 : ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3) *
        ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹)
        = ((1 : ↥hyp.actualKActor) * 1,
            (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3 * (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹) := rfl
    have e2 : ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)) ^ 2
        = ((1 : ↥hyp.actualKActor) ^ 2, (⟨ζ, hζ⟩ : ↥hyp.W) ^ 2) := rfl
    rw [e1, e2, one_mul, one_pow]
    congr 1
    group
  have hVpow : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W) ^ 3) : M.Eˣ) : M.E)
      * ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹) : M.Eˣ) : M.E)
      = ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2 := by
    rw [← Units.val_mul, ← map_mul, hprod, map_pow, Units.val_pow_eq_pow_val]
  rw [hL, hR] at hcoordeq
  refine mul_left_cancel₀ (Units.ne_zero (M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)))) ?_
  linear_combination hcoordeq
    + (M.coord (Additive.ofMul (QuotientGroup.mk
        (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))) * hVpow
    + (((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ^ 2 *
      M.coord (Additive.ofMul (QuotientGroup.mk
        (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))) * h2E

/-- **§2's stage (10), read in `Q ⧸ Z(Q) ≅ E`** (Peterfalvi Part II, p. 130, first display
of §3 (3)).

Stage (10) says `f(ω s^a) = (f(ω z) · s^a)^{ζ a⁻²}` with `z = y · s^{a⁻¹}`; in the
quotient the factor `s^a ∈ Q₀ = Z(Q)` disappears and the conjugation becomes a scalar, so

  `f(ω s^a)‾ = (μ(a²) μ(ζ))⁻¹ · f(ω z)‾`.

This is the book's `f(ωs^a)‾ = ζ a⁻² · f(ω(0, α + a^{-(1+θ)}))‾`.  The scalars are the
*inverses* of the book's throughout: its `x^d` is conjugation by `d⁻¹`, whereas `coord_act`
is stated for conjugation by `d`.  Both stages invert in the same way, so the eventual
field identity has the book's shape (`stepThree_sq_eq`).

The conjugate of `s` is written `a s a⁻¹` — the convention of `stepTwo_linear`, which is
`s^{a⁻¹}` in the book's; stage (10) is therefore applied at `a⁻¹`. -/
theorem stepTen_quotient_coord (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ζ ω y a z : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (haK : a ∈ hyp.K) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hz : y * (a⁻¹ * hyp.distinguishedInvolution * a) = z)
    (hXQ : f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) ∈ hyp.Q)
    (hWQ : f (ω * z) ∈ hyp.Q) :
    M.coord (Additive.ofMul (QuotientGroup.mk
        (⟨f (ω * (a * hyp.distinguishedInvolution * a⁻¹)), hXQ⟩ : ↥hyp.Q)))
      = (((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)
            * ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E))⁻¹
        * M.coord (Additive.ofMul (QuotientGroup.mk (⟨f (ω * z), hWQ⟩ : ↥hyp.Q))) := by
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 := hyp.distinguishedInvolution_mem_Q0
  have haD : a ∈ hyp.D := hyp.K_le_D haK
  -- stage (10) at `a⁻¹`, with the double inverses removed
  have hstep := hyp.stepTen H hC2 hζ hωQ hωQ0 hyQ0 (hyp.K.inv_mem haK) hfω
    (show y * (a⁻¹ * hyp.distinguishedInvolution * a⁻¹⁻¹) = z by rwa [inv_inv])
  rw [inv_inv] at hstep
  -- the `Q₀`-factor and the memberships
  have hsaQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D haD hsQ0
  have hsaQ : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q := hyp.Q0_le_Q hsaQ0
  have hUQ : f (ω * z) * (a * hyp.distinguishedInvolution * a⁻¹) ∈ hyp.Q :=
    hyp.Q.mul_mem hWQ hsaQ
  have hκ : (a ^ 2)⁻¹ ∈ hyp.K := hyp.K.inv_mem (pow_mem haK 2)
  have hv : ζ⁻¹ ∈ hyp.W := hyp.W.inv_mem hζ
  -- the conjugating element is `(a²)⁻¹ ζ⁻¹`
  have hval : ((a ^ 2)⁻¹ * ζ⁻¹) * (f (ω * z) * (a * hyp.distinguishedInvolution * a⁻¹))
      * ((a ^ 2)⁻¹ * ζ⁻¹)⁻¹ = f (ω * (a * hyp.distinguishedInvolution * a⁻¹)) := by
    rw [hstep]; group
  rw [hyp.coord_conj_eq M hκ hv hUQ hXQ hval, hyp.coord_mk_mul M hWQ hsaQ hUQ,
    hyp.coord_mk_eq_zero_of_mem_Q0 M hZ hsaQ0 hsaQ, add_zero]
  -- identify the scalar as the inverse of `μ(a²) μ(ζ)`
  congr 1
  have hpair : (hyp.kActor hκ, (⟨ζ⁻¹, hv⟩ : ↥hyp.W))
      = ((hyp.kActor (pow_mem haK 2), (1 : ↥hyp.W)) *
          ((1 : ↥hyp.actualKActor), (⟨ζ, hζ⟩ : ↥hyp.W)))⁻¹ := by
    have hfst : hyp.kActor hκ = (hyp.kActor (pow_mem haK 2))⁻¹ :=
      hyp.kActor_eq_inv (pow_mem haK 2) hκ rfl
    have hsnd : (⟨ζ⁻¹, hv⟩ : ↥hyp.W) = (⟨ζ, hζ⟩ : ↥hyp.W)⁻¹ := Subtype.ext rfl
    rw [Prod.mk_mul_mk, one_mul, mul_one, Prod.inv_mk, hfst, hsnd]
  rw [hpair, map_inv, Units.val_inv_eq_inv_val, map_mul, Units.val_mul]

/-- **`b² = ζ + ζ⁻¹ + a⁻²`** (Peterfalvi Part II, p. 130, inside §3 (3)) — the bridge from
the group to the field.

The book gets there by dividing the two instances of stage (2),

  `1/(a² + ζ⁻¹) = ζ a⁻² / (b² + ζ⁻¹)`,

but the division is avoidable: stage (2) at `a` and at `b` both evaluate `ω̄`, and stage
(10) relates the two unknowns, so cancelling the (nonzero) unknown at `b` already gives the
identity — no side condition `a² + ζ⁻¹ ≠ 0` is needed.

Written with `A = μ(a²)` and `Z = μ(ζ)`, the three inputs are
`(A + Z) X_a = ω̄`, `(B + Z) X_b = ω̄` and `X_a = (A Z)⁻¹ X_b`, whence
`(A + Z)(A Z)⁻¹ = B + Z`, i.e. `B = A⁻¹ + Z + Z⁻¹`.  The scalars being the inverses of the
book's (see `stepTen_quotient_coord`), this is its `b² = ζ + ζ⁻¹ + a⁻²`.

The element `b` is the one produced by `stepTen_exists`; its defining relation
`s^b = y · s^{a⁻¹}` is the book's `b^{1+θ} = α + a^{-(1+θ)}` (`stepTen_coord`). -/
theorem stepThree_sq_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω y a b : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hsq : ω * ω = y) (haK : a ∈ hyp.K) (hbK : b ∈ hyp.K)
    (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hb : b * hyp.distinguishedInvolution * b⁻¹
      = y * (a⁻¹ * hyp.distinguishedInvolution * a)) :
    ((M.mu (hyp.kActor (pow_mem hbK 2), 1) : M.Eˣ) : M.E)
      = ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E)⁻¹
        + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)
        + ((M.mu (1, ⟨ζ, hζ⟩) : M.Eˣ) : M.E)⁻¹ := by
  have h2E : (2 : M.E) = 0 := by
    have := M.charTwo
    simpa using (CharP.cast_eq_zero M.E 2)
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 := hyp.distinguishedInvolution_mem_Q0
  -- the §3 hypothesis in the form stage (1) needs
  have hf : f ω = ζ⁻¹ * ω⁻¹ * ζ := hyp.f_eq_conj_inv_of_sq_eq hyQ0 hfω hsq
  -- the two arguments of `f`, and their images
  have hsaQ0 : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D haK) hsQ0
  have hsbQ0 : b * hyp.distinguishedInvolution * b⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D hbK) hsQ0
  obtain ⟨hωaQ, hωaQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hsaQ0
  obtain ⟨hωbQ, hωbQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hsbQ0
  obtain ⟨hXaQ, -⟩ := hyp.f_mem_sdiff_Q0 H hC2 hωaQ hωaQ0
  obtain ⟨hXbQ, hXbQ0⟩ := hyp.f_mem_sdiff_Q0 H hC2 hωbQ hωbQ0
  -- the three equations
  have hA := hyp.stepTwo_linear H hC2 M hZ hmu hVW hζ hωQ hωQ0
    (by rw [← hyp.coe_K] at *; exact haK) (pow_mem haK 2) hf hXaQ
  have hB := hyp.stepTwo_linear H hC2 M hZ hmu hVW hζ hωQ hωQ0
    (by rw [← hyp.coe_K] at *; exact hbK) (pow_mem hbK 2) hf hXbQ
  have hT := hyp.stepTen_quotient_coord H hC2 M hZ hζ hωQ hωQ0 hyQ0 haK hfω hb.symm
    hXaQ hXbQ
  -- the unknown at `b` is nonzero, so it cancels
  have hXb0 := hyp.coord_ne_zero_of_not_mem_Q0 M hZ hXbQ hXbQ0
  have hAne : ((M.mu (hyp.kActor (pow_mem haK 2), 1) : M.Eˣ) : M.E) ≠ 0 := Units.ne_zero _
  have hZne : ((M.mu (1, (⟨ζ, hζ⟩ : ↥hyp.W)) : M.Eˣ) : M.E) ≠ 0 := Units.ne_zero _
  rw [hT] at hA
  exact eq_add_inv_add_inv_of_mul_inv_eq h2E hAne hZne
    (mul_right_cancel₀ hXb0 (by rw [← mul_assoc] at hA; exact hA.trans hB.symm))

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
