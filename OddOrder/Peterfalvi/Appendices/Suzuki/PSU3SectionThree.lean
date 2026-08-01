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
* `Hypothesis.h_inv_eq` — `h(ω⁻¹) = ζ⁻³`.
* `Hypothesis.h_eq_zpow_three` — `h(ω) = ζ³`, given `h(ω) ∈ W`.
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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
