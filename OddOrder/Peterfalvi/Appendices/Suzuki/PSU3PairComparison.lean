/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3Preliminary

/-!
# Peterfalvi Part II, Ch. IV §2, steps (19)–(20): comparing two representatives

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, pp. 127–128.

Steps (19) and (20) assume `n ≥ 2`, so that there are at least two representatives
`ω₁, ω₂` of the `KW`-orbits on `(Q/Q₀)^#`, and compare the two sequences `(u_i)` and
`(u'_i)` that (11) attaches to them.  The input is the relation supplied by (7) and (8),

  `f(ω₁(0,x₁)) = (ω₂(0,x₂))^k`   for some `x₁, x₂ ∈ F` and `k ∈ K`,

and the output of (20) is that the two sequences coincide, `α₁ = α₂ = x₁ + x₂`.

The chain of equalities the book writes out for (19) never touches the model: it is
step (2), (H2) and (H3) applied to elements of `Q₀`.  So `stepNineteen` below is stated
group-theoretically, exactly as `stepTen` is, and the book's coordinate form is what one
reads off afterwards.  Concretely, with `a ∈ K` chosen so that `x₁ + a^{-(1+θ)} = u_i`
(that is `a^{1+θ} = 1/(x₁ + u_i)`, `exists_inv_frobNorm_eq_of_ne`),

* `s^{a k⁻¹} = (0, a^{1+θ} k^{-(1+θ)}) = (0, 1/(k^{1+θ}(x₁ + u_i)))`,
* `s^{a d_i⁻¹} = (0, a^{1+θ} d_i^{-(1+σ)}) = (0, 1/(d_i^{1+σ}(x₁ + u_i)))`,
* `a⁻² = (x₁ + u_i)^{2τ}`, so the conjugating element `d_i a⁻² k` is the book's
  `e_i = k d_i (x₁ + u_i)^{2τ}` (the two orders agree because `KW` is abelian).

## Main results

* `Hypothesis.f_swap_of_pair` — `f(ω₁ z₁) = (ω₂ z₂)^k` implies `f(ω₂ z₂) = (ω₁ z₁)^k`,
  which is what lets (19)(b) be (19)(a) with the roles of `ω₁` and `ω₂` interchanged.
* `Hypothesis.stepNineteen` — step (19)(a).
* `Hypothesis.stepNineteen_swap` — step (19)(b).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **Interchanging the two representatives** (Peterfalvi Part II, p. 128): if
`f(x) = y^k` with `k ∈ K`, then `f(y) = x^k`, with the *same* `k`.

Applying `f` to `f(x) = y^k` gives `x = f(y^k) = f(y)^{k^t} = f(y)^{k⁻¹}` by (H2) and
(H3), the twist `k^t` being `k⁻¹` because `k ∈ K` is inverted by `t`.

This is the one line the book spends on step (19)(b): "`f(ω₂(0,x₂))^{k⁻¹} = ω₁(0,x₁)`,
so that `f(ω₂(0,x₂)) = (ω₁(0,x₁))^k`, and so we get (b) on interchanging the roles of
`ω₁` and `ω₂`". -/
theorem f_swap_of_pair (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {x y k : G} (hxQ : x ∈ hyp.Q) (hx1 : x ≠ 1) (hyQ : y ∈ hyp.Q) (hy1 : y ≠ 1)
    (hkK : k ∈ hyp.KSet) (hpair : f x = k⁻¹ * y * k) :
    f y = k⁻¹ * x * k := by
  obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hyQ hy1 hkK.1
  rw [hkK.2, inv_inv] at h3
  have h2 : f (f x) = x := (hTwo hyp.rankOneSetup H hxQ hx1).1
  rw [hpair, h3] at h2
  rw [← h2]
  group

/-- **Peterfalvi Part II, Ch. IV §2, step (19)(a)** (p. 127).

Given the relation `f(ω₁ z₁) = (ω₂ z₂)^k` of (7)–(8), an `a ∈ K` with
`z₁ · s^{a⁻¹} = u`, and the invariant `f(ω₁ u) = (ω₁ v)^d` carried by the sequences of
(11),

  `f(ω₂ z₂ · s^{a k⁻¹}) = (ω₁ v · s^{a d⁻¹})^{d a⁻² k}`.

The book's chain, unfolded: (H3) at `k` moves `f` across the conjugation, turning the
left side into `f(f(ω₁ z₁) · s^a)^{k⁻¹}`; step (2) — read backwards, at the exponent
`a⁻¹` — rewrites that as `f(ω₁ z₁ · s^{a⁻¹})^{a⁻²} s^{a⁻¹}`, which is
`f(ω₁ u)^{a⁻²} s^{a⁻¹}`; the invariant replaces `f(ω₁ u)` by `(ω₁ v)^d`; and finally
`(s^{a d⁻¹})^{d a⁻²} = s^{a⁻¹}` collects the trailing `s^{a⁻¹}` inside the conjugate.

Nothing is assumed about `u`, `v` and `d` beyond the two displayed equations — in
particular `d` need not lie in `KW`.  In the book's coordinates `z_j = (0,x_j)`,
`u = (0,u_i)`, `v = (0,v_i)`, `d = d_i`, and the two conjugates of `s` are the two
displayed fractions; see the module docstring. -/
theorem stepNineteen (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω₁ ω₂ z₁ z₂ u v k a d : G}
    (hω₁Q : ω₁ ∈ hyp.Q) (hω₁Q0 : ω₁ ∉ hyp.Q0)
    (hω₂Q : ω₂ ∈ hyp.Q) (hω₂Q0 : ω₂ ∉ hyp.Q0)
    (hz₁ : z₁ ∈ hyp.Q0) (hz₂ : z₂ ∈ hyp.Q0)
    (hkK : k ∈ hyp.KSet) (haK : a ∈ hyp.KSet)
    (hpair : f (ω₁ * z₁) = k⁻¹ * (ω₂ * z₂) * k)
    (hu : z₁ * (a * hyp.distinguishedInvolution * a⁻¹) = u)
    (hinv : f (ω₁ * u) = d⁻¹ * (ω₁ * v) * d) :
    f (ω₂ * (z₂ * (k * (a⁻¹ * hyp.distinguishedInvolution * a) * k⁻¹)))
      = (d * (a⁻¹) ^ 2 * k)⁻¹ *
          (ω₁ * (v * (d * (a⁻¹ * hyp.distinguishedInvolution * a) * d⁻¹))) *
          (d * (a⁻¹) ^ 2 * k) := by
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 :=
    ⟨hyp.distinguishedInvolution_sq, hyp.distinguishedInvolution_mem_H⟩
  have hsa : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q0 := by
    have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem haK.1) hsQ0
    rwa [inv_inv] at hmem
  have hsainv : a * hyp.distinguishedInvolution * a⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D haK.1 hsQ0
  have hksa : k * (a⁻¹ * hyp.distinguishedInvolution * a) * k⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D hkK.1 hsa
  have hsa2 : (a⁻¹ * hyp.distinguishedInvolution * a) *
      (a⁻¹ * hyp.distinguishedInvolution * a) = 1 := by
    have hsq := hsa.1
    rwa [sq] at hsq
  -- `a⁻¹ ∈ K`, so step (2) can be applied at the inverse exponent
  have haKinv : a⁻¹ ∈ hyp.KSet := by
    have hx : a ∈ hyp.K := by
      have hx' : a ∈ (hyp.K : Set G) := by rw [hyp.coe_K]; exact haK
      exact hx'
    have hy : a⁻¹ ∈ (hyp.K : Set G) := hyp.K.inv_mem hx
    rwa [hyp.coe_K] at hy
  -- the element whose `f`-value is being computed lies in `Q − Q₀`
  obtain ⟨hXQ, hXQ0⟩ := hyp.mul_mem_sdiff_Q0 hω₂Q hω₂Q0 (hyp.Q0.mul_mem hz₂ hksa)
  have hX1 : ω₂ * (z₂ * (k * (a⁻¹ * hyp.distinguishedInvolution * a) * k⁻¹)) ≠ 1 :=
    fun hc => hXQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨hω₁z₁Q, hω₁z₁Q0⟩ := hyp.mul_mem_sdiff_Q0 hω₁Q hω₁Q0 hz₁
  have hω₁z₁1 : ω₁ * z₁ ≠ 1 := fun hc => hω₁z₁Q0 (hc ▸ hyp.Q0.one_mem)
  have huQ0 : u ∈ hyp.Q0 := by
    rw [← hu]
    exact hyp.Q0.mul_mem hz₁ hsainv
  obtain ⟨-, hω₁uQ0⟩ := hyp.mul_mem_sdiff_Q0 hω₁Q hω₁Q0 huQ0
  have hω₁u1 : ω₁ * u ≠ 1 := fun hc => hω₁uQ0 (hc ▸ hyp.Q0.one_mem)
  -- (H3) at `k ∈ K`, where the twist `k^t` is `k⁻¹`
  obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hXQ hX1 hkK.1
  rw [hkK.2, inv_inv] at h3
  have hconj : k⁻¹ *
      (ω₂ * (z₂ * (k * (a⁻¹ * hyp.distinguishedInvolution * a) * k⁻¹))) * k
      = f (ω₁ * z₁) * (a⁻¹ * hyp.distinguishedInvolution * a) := by
    rw [hpair]
    group
  rw [hconj] at h3
  -- step (2) at the exponent `a⁻¹`
  have hne2 : (ω₁ * z₁) * ((a⁻¹)⁻¹ * hyp.distinguishedInvolution * a⁻¹) ≠ 1 := by
    have e : (ω₁ * z₁) * ((a⁻¹)⁻¹ * hyp.distinguishedInvolution * a⁻¹) = ω₁ * u := by
      rw [← hu]; group
    rw [e]
    exact hω₁u1
  have h2 :=
    hyp.f_mul_conj_distinguishedInvolution H hC2 haKinv hω₁z₁Q hω₁z₁1 hne2
  simp only [inv_inv] at h2
  rw [show (ω₁ * z₁) * (a * hyp.distinguishedInvolution * a⁻¹) = ω₁ * u from by
      rw [← hu]; group, hinv, h3] at h2
  -- what remains is the cancellation `s^a · s^a = 1`
  have hcollapse : ∀ F : G,
      k⁻¹ * a ^ 2 * ((a⁻¹) ^ 2 * (k * F * k⁻¹) * a ^ 2 *
          (a⁻¹ * hyp.distinguishedInvolution * a)) *
          (a⁻¹ * hyp.distinguishedInvolution * a) * (a⁻¹) ^ 2 * k = F := by
    intro F
    calc k⁻¹ * a ^ 2 * ((a⁻¹) ^ 2 * (k * F * k⁻¹) * a ^ 2 *
            (a⁻¹ * hyp.distinguishedInvolution * a)) *
            (a⁻¹ * hyp.distinguishedInvolution * a) * (a⁻¹) ^ 2 * k
        = k⁻¹ * a ^ 2 * (a⁻¹) ^ 2 * (k * F * k⁻¹) * a ^ 2 *
            ((a⁻¹ * hyp.distinguishedInvolution * a) *
              (a⁻¹ * hyp.distinguishedInvolution * a)) * (a⁻¹) ^ 2 * k := by group
      _ = F := by rw [hsa2]; group
  have hgoal : (d * (a⁻¹) ^ 2 * k)⁻¹ *
        (ω₁ * (v * (d * (a⁻¹ * hyp.distinguishedInvolution * a) * d⁻¹))) *
        (d * (a⁻¹) ^ 2 * k)
      = k⁻¹ * a ^ 2 * (d⁻¹ * (ω₁ * v) * d) *
          (a⁻¹ * hyp.distinguishedInvolution * a) * (a⁻¹) ^ 2 * k := by group
  rw [hgoal, h2, hcollapse]

/-- **Peterfalvi Part II, Ch. IV §2, step (19)(b)** (p. 127): step (19)(a) with the roles
of `ω₁` and `ω₂` interchanged.

The same `k` serves both, by `f_swap_of_pair`; the sequence data `u'`, `v'`, `d'` is the
one attached to `ω₂`. -/
theorem stepNineteen_swap (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω₁ ω₂ z₁ z₂ u' v' k a d' : G}
    (hω₁Q : ω₁ ∈ hyp.Q) (hω₁Q0 : ω₁ ∉ hyp.Q0)
    (hω₂Q : ω₂ ∈ hyp.Q) (hω₂Q0 : ω₂ ∉ hyp.Q0)
    (hz₁ : z₁ ∈ hyp.Q0) (hz₂ : z₂ ∈ hyp.Q0)
    (hkK : k ∈ hyp.KSet) (haK : a ∈ hyp.KSet)
    (hpair : f (ω₁ * z₁) = k⁻¹ * (ω₂ * z₂) * k)
    (hu : z₂ * (a * hyp.distinguishedInvolution * a⁻¹) = u')
    (hinv : f (ω₂ * u') = d'⁻¹ * (ω₂ * v') * d') :
    f (ω₁ * (z₁ * (k * (a⁻¹ * hyp.distinguishedInvolution * a) * k⁻¹)))
      = (d' * (a⁻¹) ^ 2 * k)⁻¹ *
          (ω₂ * (v' * (d' * (a⁻¹ * hyp.distinguishedInvolution * a) * d'⁻¹))) *
          (d' * (a⁻¹) ^ 2 * k) := by
  obtain ⟨hω₁z₁Q, hω₁z₁Q0⟩ := hyp.mul_mem_sdiff_Q0 hω₁Q hω₁Q0 hz₁
  obtain ⟨hω₂z₂Q, hω₂z₂Q0⟩ := hyp.mul_mem_sdiff_Q0 hω₂Q hω₂Q0 hz₂
  refine hyp.stepNineteen H hC2 hω₂Q hω₂Q0 hω₁Q hω₁Q0 hz₂ hz₁ hkK haK ?_ hu hinv
  exact hyp.f_swap_of_pair H hω₁z₁Q (fun hc => hω₁z₁Q0 (hc ▸ hyp.Q0.one_mem)) hω₂z₂Q
    (fun hc => hω₂z₂Q0 (hc ▸ hyp.Q0.one_mem)) hkK hpair

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
