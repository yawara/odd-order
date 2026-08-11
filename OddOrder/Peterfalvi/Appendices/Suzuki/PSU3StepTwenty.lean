/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3StepFifteen

/-!
# Peterfalvi Part II, Ch. IV §2, step (20): `α₁ = α₂`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, p. 128.

> **(20)** We have `α₁ = α₂`; also, with `α = α₁`,
> `f(ω₁(0,x)) = (ω₂(0, x + α))^{d(x)}`, with `d(x) ∈ KW`, for all `x` such that
> `f(ω₁(0,x))‾` is in the orbit of `ω̄₂` under `KW`.

The book runs the two sequences of (11) — one for `α₁`, one for `α₂` — feeds (19)(a) at
index `i` and (19)(b) at index `m − i` into step (7), and reads the resulting (∗∗∗) at
`i = 1` and at `i = m − 1`.

Only those two indices are used, and at them the sequence data degenerates:

* at `i = 1`, `(u₁, v₁, d₁) = (0, α, ζ)`, so (19)'s hypothesis is the normalization
  `f(ω) = (ω y)^ζ` itself;
* at `i = m − 1`, `(u_{m-1}, v_{m-1}, d_{m-1}) = (α, 0, ζ⁻¹)` — by steps (15) and (17) —
  so (19)'s hypothesis is the *inverted* normalization `f(ω y) = ω^{ζ⁻¹}`, which is
  `f_mul_eq_conj_of_normalized`.

So the whole of (20) can be run off the two normalizations, with no sequence at all.  The
book's `e_i^{-t} ∈ e'_{m-i}K` is likewise free of the field: the twist reverses the
`W`-part and fixes the `K`-part (`inv_conj_t_of_mem_W_mul_KSet`), and here both `W`-parts
are `ζ^{±1}`, so the two conjugators sit in the same coset of `K` outright.

## Main results

* `Hypothesis.stepTwenty_fst_eq` — the core: `z₁ = z₂ y₂`, the book's `x₁ = x₂ + α₂`.
* `Hypothesis.stepTwenty_snd` — **step (20)**'s second assertion: the image is always
  `ω₂ (z y)`.
* `Hypothesis.stepTwenty` — **step (20)**'s first assertion `α₁ = α₂`, i.e. `y₁ = y₂`.
* `Hypothesis.dOrbitRel_of_stepTwenty_chain` — the (H5) chain of §2's closing
  Proposition.
* `Hypothesis.f_eq_conj_inv_of_stepTwenty_chain` — §2's closing Proposition, second half:
  `ω² = (0,α)` and `f(ω) = (ω⁻¹)^ζ`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- Membership in `K` and in `KSet` are the same. -/
theorem mem_KSet_iff_mem_K {x : G} : x ∈ hyp.KSet ↔ x ∈ hyp.K := by
  constructor
  · intro hx
    have hx' : x ∈ (hyp.K : Set G) := by rw [hyp.coe_K]; exact hx
    exact hx'
  · intro hx
    have hx' : x ∈ (hyp.K : Set G) := hx
    rwa [hyp.coe_K] at hx'

/-- **The comparison of step (20), at the pair of indices `(1, m − 1)`**
(Peterfalvi Part II, p. 128).

With `f(ω₁ z₁) = (ω₂ z₂)^k` the relation of (7)–(8), step (19)(a) at the *first* index of
`ω₁`'s sequence and step (19)(b) at the *last* index of `ω₂`'s sequence produce two
presentations of the same shape `f(ω₁ ·) = (ω₂ ·)^·` whose conjugators differ by an
element of `K`.  Step (7) then forces the conjugators to be equal, and unwinding gives

  `z₁ = z₂ y₂`,

the book's `x₁ = x₂ + α₂`.

The two side conditions are the book's standing assumption that `ω₁` and `ω₂` lie in
different `KW`-orbits: `z₁ = 1` would put `f(ω₁)` in `ω₁`'s own orbit, and `z₂ = y₂`
would identify `f(ω₂ y₂) = ω₂^{ζ⁻¹}` with `(ω₁ z₁)^{k⁻¹}`. -/
theorem stepTwenty_fst_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω₁ ω₂ y₁ y₂ z₁ z₂ k : G} (hζ : ζ ∈ hyp.W)
    (hω₁Q : ω₁ ∈ hyp.Q) (hω₁Q0 : ω₁ ∉ hyp.Q0)
    (hω₂Q : ω₂ ∈ hyp.Q) (hω₂Q0 : ω₂ ∉ hyp.Q0)
    (hy₁Q0 : y₁ ∈ hyp.Q0) (hy₂Q0 : y₂ ∈ hyp.Q0)
    (hz₁Q0 : z₁ ∈ hyp.Q0) (hz₂Q0 : z₂ ∈ hyp.Q0)
    (hf₁ : f ω₁ = ζ⁻¹ * (ω₁ * y₁) * ζ) (hf₂ : f ω₂ = ζ⁻¹ * (ω₂ * y₂) * ζ)
    (hkK : k ∈ hyp.KSet) (hpair : f (ω₁ * z₁) = k⁻¹ * (ω₂ * z₂) * k)
    (hz₁1 : z₁ ≠ 1) (hz₂y₂ : z₂ * y₂ ≠ 1) :
    z₁ = z₂ * y₂ := by
  classical
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hsQ0 : hyp.distinguishedInvolution ∈ hyp.Q0 := hyp.distinguishedInvolution_mem_Q0
  -- the two elements of `K` realizing the conjugates of `s`
  obtain ⟨a, haK, ha⟩ : ∃ a ∈ hyp.KSet,
      a * hyp.distinguishedInvolution * a⁻¹ = z₁ := by
    obtain ⟨b, hbK, hb⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0 hz₁Q0 hz₁1
    exact ⟨b⁻¹, hyp.inv_mem_KSet hbK, by rwa [inv_inv]⟩
  obtain ⟨a', ha'K, ha'⟩ : ∃ a' ∈ hyp.KSet,
      a' * hyp.distinguishedInvolution * a'⁻¹ = z₂ * y₂ := by
    obtain ⟨b, hbK, hb⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0
      (hyp.Q0.mul_mem hz₂Q0 hy₂Q0) hz₂y₂
    exact ⟨b⁻¹, hyp.inv_mem_KSet hbK, by rwa [inv_inv]⟩
  -- the two instances of (19)
  have hu1 : z₁ * (a * hyp.distinguishedInvolution * a⁻¹) = 1 := by
    rw [ha]
    have hsq := hz₁Q0.1
    rwa [sq] at hsq
  have hu2 : z₂ * (a' * hyp.distinguishedInvolution * a'⁻¹) = y₂ := by
    rw [ha']
    have hsq := hz₂Q0.1
    rw [sq] at hsq
    calc z₂ * (z₂ * y₂) = (z₂ * z₂) * y₂ := by group
      _ = y₂ := by rw [hsq, one_mul]
  have hinv1 : f (ω₁ * 1) = ζ⁻¹ * (ω₁ * y₁) * ζ := by rw [mul_one]; exact hf₁
  have hinv2 : f (ω₂ * y₂) = (ζ⁻¹)⁻¹ * (ω₂ * 1) * ζ⁻¹ := by
    rw [inv_inv, mul_one]
    exact hyp.f_mul_eq_conj_of_normalized H hζ hω₂Q hω₂Q0 hy₂Q0 hf₂
  have e1 := hyp.stepNineteen H hC2 hω₁Q hω₁Q0 hω₂Q hω₂Q0 hz₁Q0 hz₂Q0 hkK haK hpair
    hu1 hinv1
  have e2 := hyp.stepNineteen_swap H hC2 hω₁Q hω₁Q0 hω₂Q hω₂Q0 hz₁Q0 hz₂Q0 hkK ha'K
    hpair hu2 hinv2
  -- memberships
  have hB : a⁻¹ * hyp.distinguishedInvolution * a ∈ hyp.Q0 := by
    have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem haK.1) hsQ0
    rwa [inv_inv] at hmem
  have hB' : a'⁻¹ * hyp.distinguishedInvolution * a' ∈ hyp.Q0 := by
    have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem ha'K.1) hsQ0
    rwa [inv_inv] at hmem
  have hkB : k * (a⁻¹ * hyp.distinguishedInvolution * a) * k⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D hkK.1 hB
  have hkB' : k * (a'⁻¹ * hyp.distinguishedInvolution * a') * k⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D hkK.1 hB'
  have hζB : ζ * (a⁻¹ * hyp.distinguishedInvolution * a) * ζ⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D hζD hB
  have hζB' : ζ⁻¹ * (a'⁻¹ * hyp.distinguishedInvolution * a') * (ζ⁻¹)⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem hζD) hB'
  have hX : z₂ * (k * (a⁻¹ * hyp.distinguishedInvolution * a) * k⁻¹) ∈ hyp.Q0 :=
    hyp.Q0.mul_mem hz₂Q0 hkB
  have hY : y₁ * (ζ * (a⁻¹ * hyp.distinguishedInvolution * a) * ζ⁻¹) ∈ hyp.Q0 :=
    hyp.Q0.mul_mem hy₁Q0 hζB
  have hX₂ : z₁ * (k * (a'⁻¹ * hyp.distinguishedInvolution * a') * k⁻¹) ∈ hyp.Q0 :=
    hyp.Q0.mul_mem hz₁Q0 hkB'
  have hY₂ : (1 : G) * (ζ⁻¹ * (a'⁻¹ * hyp.distinguishedInvolution * a') * (ζ⁻¹)⁻¹)
      ∈ hyp.Q0 := hyp.Q0.mul_mem hyp.Q0.one_mem hζB'
  -- invert the first instance so that both have `ω₁` on the left
  have heD : ζ * (a⁻¹) ^ 2 * k ∈ hyp.D :=
    hyp.D.mul_mem (hyp.D.mul_mem hζD (pow_mem (hyp.D.inv_mem haK.1) 2)) hkK.1
  obtain ⟨hXQ, hXQ0⟩ := hyp.mul_mem_sdiff_Q0 hω₂Q hω₂Q0 hX
  obtain ⟨hYQ, hYQ0⟩ := hyp.mul_mem_sdiff_Q0 hω₁Q hω₁Q0 hY
  have hswap := hyp.f_conj_swap H hXQ (fun hc => hXQ0 (hc ▸ hyp.Q0.one_mem)) hYQ
    (fun hc => hYQ0 (hc ▸ hyp.Q0.one_mem)) heD e1
  have heq₁ : f (ω₁ * (y₁ * (ζ * (a⁻¹ * hyp.distinguishedInvolution * a) * ζ⁻¹)))
      = ((hyp.t * (ζ * (a⁻¹) ^ 2 * k) * hyp.t)⁻¹)⁻¹ *
          (ω₂ * (z₂ * (k * (a⁻¹ * hyp.distinguishedInvolution * a) * k⁻¹))) *
          (hyp.t * (ζ * (a⁻¹) ^ 2 * k) * hyp.t)⁻¹ := by
    rw [inv_inv]
    exact hswap
  -- the two conjugators, in the shape `ζ^{±1} · (element of K)`
  have hκK : (a⁻¹) ^ 2 * k ∈ hyp.KSet := by
    rw [hyp.mem_KSet_iff_mem_K]
    exact hyp.K.mul_mem (pow_mem (hyp.K.inv_mem (hyp.mem_KSet_iff_mem_K.mp haK)) 2)
      (hyp.mem_KSet_iff_mem_K.mp hkK)
  have hκ'K : (a'⁻¹) ^ 2 * k ∈ hyp.KSet := by
    rw [hyp.mem_KSet_iff_mem_K]
    exact hyp.K.mul_mem (pow_mem (hyp.K.inv_mem (hyp.mem_KSet_iff_mem_K.mp ha'K)) 2)
      (hyp.mem_KSet_iff_mem_K.mp hkK)
  have ha₁ : (hyp.t * (ζ * (a⁻¹) ^ 2 * k) * hyp.t)⁻¹ = ζ⁻¹ * ((a⁻¹) ^ 2 * k) := by
    rw [mul_assoc ζ ((a⁻¹) ^ 2) k]
    exact hyp.inv_conj_t_of_mem_W_mul_KSet hζ hκK
  have ha₂ : ζ⁻¹ * (a'⁻¹) ^ 2 * k = ζ⁻¹ * ((a'⁻¹) ^ 2 * k) := by group
  -- the coset and commutation hypotheses of step (7)
  have hcosetK : (ζ⁻¹ * ((a⁻¹) ^ 2 * k))⁻¹ * (ζ⁻¹ * ((a'⁻¹) ^ 2 * k)) ∈ hyp.K := by
    have e : (ζ⁻¹ * ((a⁻¹) ^ 2 * k))⁻¹ * (ζ⁻¹ * ((a'⁻¹) ^ 2 * k))
        = ((a⁻¹) ^ 2 * k)⁻¹ * ((a'⁻¹) ^ 2 * k) := by group
    rw [e]
    exact hyp.K.mul_mem (hyp.K.inv_mem (hyp.mem_KSet_iff_mem_K.mp hκK))
      (hyp.mem_KSet_iff_mem_K.mp hκ'K)
  have hcomm : Commute (ζ⁻¹ * ((a⁻¹) ^ 2 * k)) (ζ⁻¹ * ((a'⁻¹) ^ 2 * k)) := by
    have hκκ' := hyp.commute_of_mem_K (hyp.mem_KSet_iff_mem_K.mp hκK)
      (hyp.mem_KSet_iff_mem_K.mp hκ'K)
    have hζκ := hyp.commute_of_mem_W_of_mem_K (hyp.W.inv_mem hζ)
      (hyp.mem_KSet_iff_mem_K.mp hκK)
    have hζκ' := hyp.commute_of_mem_W_of_mem_K (hyp.W.inv_mem hζ)
      (hyp.mem_KSet_iff_mem_K.mp hκ'K)
    change ζ⁻¹ * ((a⁻¹) ^ 2 * k) * (ζ⁻¹ * ((a'⁻¹) ^ 2 * k))
      = ζ⁻¹ * ((a'⁻¹) ^ 2 * k) * (ζ⁻¹ * ((a⁻¹) ^ 2 * k))
    calc ζ⁻¹ * ((a⁻¹) ^ 2 * k) * (ζ⁻¹ * ((a'⁻¹) ^ 2 * k))
        = ζ⁻¹ * (((a⁻¹) ^ 2 * k) * ζ⁻¹) * ((a'⁻¹) ^ 2 * k) := by group
      _ = ζ⁻¹ * (ζ⁻¹ * ((a⁻¹) ^ 2 * k)) * ((a'⁻¹) ^ 2 * k) := by rw [hζκ]
      _ = ζ⁻¹ * ζ⁻¹ * (((a⁻¹) ^ 2 * k) * ((a'⁻¹) ^ 2 * k)) := by group
      _ = ζ⁻¹ * ζ⁻¹ * (((a'⁻¹) ^ 2 * k) * ((a⁻¹) ^ 2 * k)) := by rw [hκκ']
      _ = ζ⁻¹ * (ζ⁻¹ * ((a'⁻¹) ^ 2 * k)) * ((a⁻¹) ^ 2 * k) := by group
      _ = ζ⁻¹ * (((a'⁻¹) ^ 2 * k) * ζ⁻¹) * ((a⁻¹) ^ 2 * k) := by rw [hζκ']
      _ = ζ⁻¹ * ((a'⁻¹) ^ 2 * k) * (ζ⁻¹ * ((a⁻¹) ^ 2 * k)) := by group
  -- step (7)
  rw [ha₁] at heq₁
  rw [ha₂] at e2
  have hstep7 := hyp.eq_and_eq_of_inv_mul_mem_K H hC2 hω₁Q hω₁Q0 hω₂Q hω₂Q0 hY hX₂ hX hY₂
    (hyp.D.mul_mem (hyp.D.inv_mem hζD) (hyp.K_le_D (hyp.mem_KSet_iff_mem_K.mp hκK)))
    (hyp.D.mul_mem (hyp.D.inv_mem hζD) (hyp.K_le_D (hyp.mem_KSet_iff_mem_K.mp hκ'K)))
    heq₁ e2 hcosetK hcomm
  -- unwind the equality of conjugators
  have hκeq : (a⁻¹) ^ 2 = (a'⁻¹) ^ 2 := by
    have h := mul_left_cancel hstep7.2.1
    exact mul_right_cancel h
  have hainv : a⁻¹ = a'⁻¹ :=
    HypothesisA1.eq_of_sq_eq_of_odd_orderOf (hyp.odd_orderOf_of_mem_D (hyp.D.inv_mem haK.1))
      (hyp.odd_orderOf_of_mem_D (hyp.D.inv_mem ha'K.1)) rfl hκeq.symm
  have haa : a = a' := inv_injective hainv
  rw [← ha, ← ha', haa]

/-- **The `W`-part of a `D`-conjugator moves onto the target** (Peterfalvi Part II,
p. 128, inside step (20)).

Step (20) is proved through `stepTwenty_fst_eq`, which wants the conjugator in `K`; what
a relation `f(ω₁ z) = (ω₂ w)^c` supplies is only `c ∈ D`.  Writing `c = κ v` with `κ ∈ K`
and `v ∈ W`, the `W`-part can be absorbed into `ω₂`: it centralizes `Q₀`, and `ω₂^v`
satisfies the same normalization as `ω₂` because `t` centralizes `W` (so (H3) has no
twist) and `v` commutes with `ζ` (so the normalization survives conjugation).

Both halves of step (20) go through this, so it is stated once.  The conjugator is asked
for in `K W` — which is where §2's orbits live (`KW`); the `V = W` reading `c ∈ D` is the
special case `KW = D` (`KW_eq_D_of_V_eq_W`). -/
theorem exists_mem_K_conj_of_mem_KW (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω₁ ω₂ y z w c : G} (hζ : ζ ∈ hyp.W)
    (hWcard : orderOf ζ = Nat.card ↥hyp.W)
    (hω₂Q : ω₂ ∈ hyp.Q) (hω₂Q0 : ω₂ ∉ hyp.Q0) (hyQ0 : y ∈ hyp.Q0) (hwQ0 : w ∈ hyp.Q0)
    (hcKW : c ∈ hyp.KW) (hf₂ : f ω₂ = ζ⁻¹ * (ω₂ * y) * ζ)
    (hrel : f (ω₁ * z) = c⁻¹ * (ω₂ * w) * c) :
    ∃ ω₂' : G, ω₂' ∈ hyp.Q ∧ ω₂' ∉ hyp.Q0 ∧ ∃ κ : G, κ ∈ hyp.K ∧
      f ω₂' = ζ⁻¹ * (ω₂' * y) * ζ ∧ f (ω₁ * z) = κ⁻¹ * (ω₂' * w) * κ := by
  classical
  have hcD : c ∈ hyp.D := hyp.KW_le_D hcKW
  have hW := hyp.W_eq_zpowers hζ hWcard
  obtain ⟨κ, hκK, v, hvW, hc⟩ := hcKW
  have hvD : v ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hvW)
  have hcomm : κ * v = v * κ := hyp.commute_of_mem_W_of_mem_K hvW hκK
  have hcinv : v⁻¹ * κ⁻¹ = κ⁻¹ * v⁻¹ := by
    calc v⁻¹ * κ⁻¹ = (κ * v)⁻¹ := by group
      _ = (v * κ)⁻¹ := by rw [hcomm]
      _ = κ⁻¹ * v⁻¹ := by group
  have hvw : v * w = w * v := hyp.W_centralizes_Q0 hvW hwQ0
  have hvy : v * y = y * v := hyp.W_centralizes_Q0 hvW hyQ0
  have hvζ : v * ζ = ζ * v := hyp.commute_of_mem_W_of_W_eq_zpowers hW hvW
  have hω₂1 : ω₂ ≠ 1 := fun hcc => hω₂Q0 (hcc ▸ hyp.Q0.one_mem)
  -- the `W`-part moves onto `ω₂`
  have hω₂'Q : v⁻¹ * ω₂ * v ∈ hyp.Q := hyp.rankOneSetup.DQ v hvD ω₂ hω₂Q
  have hω₂'Q0 : v⁻¹ * ω₂ * v ∉ hyp.Q0 := by
    intro hcc
    refine hω₂Q0 ?_
    have e : ω₂ = v * (v⁻¹ * ω₂ * v) * v⁻¹ := by group
    rw [e]
    exact hyp.conj_mem_Q0_of_mem_D hvD hcc
  have hnew : f (ω₁ * z) = κ⁻¹ * ((v⁻¹ * ω₂ * v) * w) * κ := by
    rw [hrel, hc]
    calc (κ * v)⁻¹ * (ω₂ * w) * (κ * v)
        = (v⁻¹ * κ⁻¹) * (ω₂ * w) * (κ * v) := by group
      _ = (κ⁻¹ * v⁻¹) * (ω₂ * w) * (κ * v) := by rw [hcinv]
      _ = κ⁻¹ * (v⁻¹ * ω₂) * (w * (κ * v)) := by group
      _ = κ⁻¹ * (v⁻¹ * ω₂) * (w * (v * κ)) := by rw [hcomm]
      _ = κ⁻¹ * (v⁻¹ * ω₂) * ((w * v) * κ) := by group
      _ = κ⁻¹ * (v⁻¹ * ω₂) * ((v * w) * κ) := by rw [← hvw]
      _ = κ⁻¹ * ((v⁻¹ * ω₂ * v) * w) * κ := by group
  -- the conjugate satisfies the same normalization
  have hf₂' : f (v⁻¹ * ω₂ * v) = ζ⁻¹ * ((v⁻¹ * ω₂ * v) * y) * ζ := by
    have htvt : hyp.t * v * hyp.t = v := by
      have hcv := hyp.commute_t_of_mem_V (hyp.W_le_V hvW)
      rw [← hcv.eq, mul_assoc, hyp.rankOneSetup.invol, mul_one]
    obtain ⟨e3, -, -⟩ := hThree hyp.rankOneSetup H hω₂Q hω₂1 hvD
    rw [htvt] at e3
    rw [e3, hf₂]
    calc v⁻¹ * (ζ⁻¹ * (ω₂ * y) * ζ) * v
        = (v⁻¹ * ζ⁻¹) * (ω₂ * y) * (ζ * v) := by group
      _ = (ζ⁻¹ * v⁻¹) * (ω₂ * y) * (ζ * v) := by
          rw [show v⁻¹ * ζ⁻¹ = ζ⁻¹ * v⁻¹ from by
            calc v⁻¹ * ζ⁻¹ = (ζ * v)⁻¹ := by group
              _ = (v * ζ)⁻¹ := by rw [hvζ]
              _ = ζ⁻¹ * v⁻¹ := by group]
      _ = ζ⁻¹ * (v⁻¹ * ω₂) * (y * (ζ * v)) := by group
      _ = ζ⁻¹ * (v⁻¹ * ω₂) * (y * (v * ζ)) := by rw [← hvζ]
      _ = ζ⁻¹ * (v⁻¹ * ω₂) * ((y * v) * ζ) := by group
      _ = ζ⁻¹ * (v⁻¹ * ω₂) * ((v * y) * ζ) := by rw [← hvy]
      _ = ζ⁻¹ * ((v⁻¹ * ω₂ * v) * y) * ζ := by group
  exact ⟨v⁻¹ * ω₂ * v, hω₂'Q, hω₂'Q0, κ, hκK, hf₂', hnew⟩

/-- **Step (20)**, second assertion (Peterfalvi Part II, p. 128): whenever `f(ω₁ z)` is
`D`-conjugate to `ω₂ w` with `w ∈ Q₀`, necessarily

  `w = z y`,

which is the book's `f(ω₁(0,x)) = (ω₂(0, x + α))^{d(x)}`.

The book reaches this by exhausting the `x` in question with the sequence of (11) and
applying (19)(b) to each; but `stepTwenty_fst_eq` already proves it for every `z` — the
conjugator merely has to be moved into `K`.  Writing `c = κ v` with `κ ∈ K` and `v ∈ W`
(`D = KW`), the `W`-part can be absorbed into `ω₂`: it centralizes `Q₀`, and `ω₂^v`
satisfies the same normalization as `ω₂` because `t` centralizes `W` (so (H3) has no
twist) and `v` commutes with `ζ` (so the normalization survives conjugation). -/
theorem stepTwenty_snd (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω₁ ω₂ y z w c : G} (hζ : ζ ∈ hyp.W)
    (hWcard : orderOf ζ = Nat.card ↥hyp.W)
    (hω₁Q : ω₁ ∈ hyp.Q) (hω₁Q0 : ω₁ ∉ hyp.Q0)
    (hω₂Q : ω₂ ∈ hyp.Q) (hω₂Q0 : ω₂ ∉ hyp.Q0) (hyQ0 : y ∈ hyp.Q0)
    (hf₁ : f ω₁ = ζ⁻¹ * (ω₁ * y) * ζ) (hf₂ : f ω₂ = ζ⁻¹ * (ω₂ * y) * ζ)
    (hzQ0 : z ∈ hyp.Q0) (hwQ0 : w ∈ hyp.Q0) (hcKW : c ∈ hyp.KW)
    (hrel : f (ω₁ * z) = c⁻¹ * (ω₂ * w) * c)
    (hz1 : z ≠ 1) (hwy : w * y ≠ 1) :
    z = w * y := by
  obtain ⟨ω₂', hω₂'Q, hω₂'Q0, κ, hκK, hf₂', hnew⟩ :=
    hyp.exists_mem_K_conj_of_mem_KW H hζ hWcard hω₂Q hω₂Q0 hyQ0 hwQ0 hcKW hf₂ hrel
  exact hyp.stepTwenty_fst_eq H hC2 hζ hω₁Q hω₁Q0 hω₂'Q hω₂'Q0 hyQ0 hyQ0 hzQ0 hwQ0
    hf₁ hf₂' (hyp.mem_KSet_iff_mem_K.mpr hκK) hnew hz1 hwy

/-- **Step (20)**, first assertion (Peterfalvi Part II, p. 128): `α₁ = α₂`.

`stepTwenty_fst_eq` applied twice — once as stated, once with `ω₁` and `ω₂` exchanged
(the same `k` serves, by `f_swap_of_pair`) — gives `z₁ = z₂ y₂` and `z₂ = z₁ y₁`.
Substituting one into the other leaves `y₁ y₂ = 1`, and `y₂` is an involution. -/
theorem stepTwenty (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω₁ ω₂ y₁ y₂ z₁ z₂ k : G} (hζ : ζ ∈ hyp.W)
    (hω₁Q : ω₁ ∈ hyp.Q) (hω₁Q0 : ω₁ ∉ hyp.Q0)
    (hω₂Q : ω₂ ∈ hyp.Q) (hω₂Q0 : ω₂ ∉ hyp.Q0)
    (hy₁Q0 : y₁ ∈ hyp.Q0) (hy₂Q0 : y₂ ∈ hyp.Q0)
    (hz₁Q0 : z₁ ∈ hyp.Q0) (hz₂Q0 : z₂ ∈ hyp.Q0)
    (hf₁ : f ω₁ = ζ⁻¹ * (ω₁ * y₁) * ζ) (hf₂ : f ω₂ = ζ⁻¹ * (ω₂ * y₂) * ζ)
    (hkK : k ∈ hyp.KSet) (hpair : f (ω₁ * z₁) = k⁻¹ * (ω₂ * z₂) * k)
    (hz₁1 : z₁ ≠ 1) (hz₂1 : z₂ ≠ 1)
    (hz₁y₁ : z₁ * y₁ ≠ 1) (hz₂y₂ : z₂ * y₂ ≠ 1) :
    y₁ = y₂ := by
  have h₁ := hyp.stepTwenty_fst_eq H hC2 hζ hω₁Q hω₁Q0 hω₂Q hω₂Q0 hy₁Q0 hy₂Q0 hz₁Q0 hz₂Q0
    hf₁ hf₂ hkK hpair hz₁1 hz₂y₂
  obtain ⟨hω₁z₁Q, hω₁z₁Q0⟩ := hyp.mul_mem_sdiff_Q0 hω₁Q hω₁Q0 hz₁Q0
  obtain ⟨hω₂z₂Q, hω₂z₂Q0⟩ := hyp.mul_mem_sdiff_Q0 hω₂Q hω₂Q0 hz₂Q0
  have hpair' : f (ω₂ * z₂) = k⁻¹ * (ω₁ * z₁) * k :=
    hyp.f_swap_of_pair H hω₁z₁Q (fun hc => hω₁z₁Q0 (hc ▸ hyp.Q0.one_mem)) hω₂z₂Q
      (fun hc => hω₂z₂Q0 (hc ▸ hyp.Q0.one_mem)) hkK hpair
  have h₂ := hyp.stepTwenty_fst_eq H hC2 hζ hω₂Q hω₂Q0 hω₁Q hω₁Q0 hy₂Q0 hy₁Q0 hz₂Q0 hz₁Q0
    hf₂ hf₁ hkK hpair' hz₂1 hz₁y₁
  -- `z₁ = z₂ y₂` and `z₂ = z₁ y₁` force `y₁ y₂ = 1`
  have hcomm : y₁ * y₂ = y₂ * y₁ :=
    (Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hy₁Q0) (y₂ : G)
      (hyp.Q0_le_Q hy₂Q0)).symm
  have hz₁z₁ : z₁ * (y₁ * y₂) = z₁ := by
    calc z₁ * (y₁ * y₂) = (z₁ * y₁) * y₂ := by group
      _ = z₂ * y₂ := by rw [← h₂]
      _ = z₁ := h₁.symm
  have hone : y₁ * y₂ = 1 := by
    have e : z₁⁻¹ * (z₁ * (y₁ * y₂)) = z₁⁻¹ * z₁ := by rw [hz₁z₁]
    simpa using e
  have hy₂inv : y₂⁻¹ = y₂ := by
    have hsq := hy₂Q0.1
    rw [sq] at hsq
    exact inv_eq_of_mul_eq_one_right hsq
  calc y₁ = (y₁ * y₂) * y₂⁻¹ := by group
    _ = y₂⁻¹ := by rw [hone, one_mul]
    _ = y₂ := hy₂inv

/-- **Step (20), first assertion, with a `D`-conjugator** (Peterfalvi Part II, p. 128).

`stepTwenty` wants the conjugator in `K`; the relations that arise from mere orbit
membership have it only in `D = KW`.  `exists_mem_K_conj_of_mem_D` absorbs the `W`-part
into `ω₂`, and the normalization — hence `y₂` — is unchanged, so the conclusion
`y₁ = y₂` is the same one. -/
theorem stepTwenty_of_mem_KW (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω₁ ω₂ y₁ y₂ z₁ z₂ c : G} (hζ : ζ ∈ hyp.W)
    (hWcard : orderOf ζ = Nat.card ↥hyp.W)
    (hω₁Q : ω₁ ∈ hyp.Q) (hω₁Q0 : ω₁ ∉ hyp.Q0)
    (hω₂Q : ω₂ ∈ hyp.Q) (hω₂Q0 : ω₂ ∉ hyp.Q0)
    (hy₁Q0 : y₁ ∈ hyp.Q0) (hy₂Q0 : y₂ ∈ hyp.Q0)
    (hz₁Q0 : z₁ ∈ hyp.Q0) (hz₂Q0 : z₂ ∈ hyp.Q0)
    (hf₁ : f ω₁ = ζ⁻¹ * (ω₁ * y₁) * ζ) (hf₂ : f ω₂ = ζ⁻¹ * (ω₂ * y₂) * ζ)
    (hcKW : c ∈ hyp.KW) (hpair : f (ω₁ * z₁) = c⁻¹ * (ω₂ * z₂) * c)
    (hz₁1 : z₁ ≠ 1) (hz₂1 : z₂ ≠ 1)
    (hz₁y₁ : z₁ * y₁ ≠ 1) (hz₂y₂ : z₂ * y₂ ≠ 1) :
    y₁ = y₂ := by
  obtain ⟨ω₂', hω₂'Q, hω₂'Q0, κ, hκK, hf₂', hnew⟩ :=
    hyp.exists_mem_K_conj_of_mem_KW H hζ hWcard hω₂Q hω₂Q0 hy₂Q0 hz₂Q0 hcKW hf₂ hpair
  exact hyp.stepTwenty H hC2 hζ hω₁Q hω₁Q0 hω₂'Q hω₂'Q0 hy₁Q0 hy₂Q0 hz₁Q0 hz₂Q0
    hf₁ hf₂' (hyp.mem_KSet_iff_mem_K.mpr hκK) hnew hz₁1 hz₂1 hz₁y₁ hz₂y₂

/-! ## §2's closing Proposition: `f(ω) = (ω⁻¹)^ζ`

> **Proposition.** Suppose that `D` acts without fixed points on `(Q/Q₀)^#`.  Then there
> exists an index `i`, `1 ≤ i ≤ n`, such that `f(ω) = (ω⁻¹)^ζ` and `h(ω) ∈ W` for
> `ω = ω_i`.

Its hypothesis is `eq_one_of_conj_eq_mul_Q0_of_mem_D`, and `h(ω) ∈ W` is `h_mem_W`.  What
is left is `ω_i² = (0,α)`, which the book gets from a chain of three orbit identities fed
to (H5).  The last two steps of that argument are here; the chain itself — which needs the
family `ω_1, …, ω_n` of orbit representatives (`exists_normalizedOrbitRep`) — is assembled in
`PSU3BarOrbit.exists_f_eq_conj_inv`, the closing Proposition itself.
-/

/-- **The (H5) chain of §2's closing Proposition** (Peterfalvi Part II, p. 129).

With `ρ = ω²` (so `ω⁻¹ = ωρ`, the square being an involution of `Q₀`), step (20) applied
to the pairs `(ω, ω_i)` and `(ω, ω_k)` gives the two orbit relations assumed here.
Running `(f ∘ j)³` — which is the identity on `D`-orbits by (H5) — from `X = ω_k⁻¹ρ`:

| step | uses | lands on |
|---|---|---|
| `(f∘j)(X)` | `X⁻¹ = ω_k ρ`, the `k`-relation, (H2) | `ω(ρy)` |
| `(f∘j)²(X)` | `(ω(ρy))⁻¹ = ωy`, the normalization, (H2) | `ω` |
| `(f∘j)³(X)` | `ω⁻¹ = ωρ`, the `i`-relation | `ω_i(ρy)` |

so `X` and `ω_i(ρy)` lie in the same `D`-orbit.  The book's side remark that
`h(ω_k⁻¹(0,r)) ∈ KW` is automatic here: `h` always takes values in `D`, and `D = KW`
under Chapter IV's `V = W`. -/
theorem dOrbitRel_of_stepTwenty_chain (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω ωi ωk y ρ : G}
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hωkQ : ωk ∈ hyp.Q) (hωkQ0 : ωk ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hρQ0 : ρ ∈ hyp.Q0) (hρ : ρ = ω * ω) (hζW : ζ ∈ hyp.W)
    (hnorm : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hhX : h (ωk⁻¹ * ρ) ∈ hyp.KW)
    (hi : dOrbitRel hyp.KW (f (ω * ρ)) (ωi * (ρ * y)))
    (hk : dOrbitRel hyp.KW (f (ω * (ρ * y))) (ωk * ρ)) :
    dOrbitRel hyp.KW (ωk⁻¹ * ρ) (ωi * (ρ * y)) := by
  classical
  have hne : ∀ {z : G}, z ∉ hyp.Q0 → z ≠ 1 := fun hz hc => hz (hc ▸ hyp.Q0.one_mem)
  have hinvQ0 : ∀ {z : G}, z ∈ hyp.Q0 → z⁻¹ = z := by
    intro z hz
    have hs := hz.1
    rw [sq] at hs
    exact inv_eq_of_mul_eq_one_right hs
  have hcentQ : ∀ {z w : G}, z ∈ hyp.Q0 → w ∈ hyp.Q → w * z = z * w := by
    intro z w hz hw
    exact Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hz) w hw
  have hρy : ρ * y ∈ hyp.Q0 := hyp.Q0.mul_mem hρQ0 hyQ0
  obtain ⟨hωρQ, hωρQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hρQ0
  obtain ⟨hωρyQ, hωρyQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hρy
  obtain ⟨hωyQ, hωyQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hyQ0
  obtain ⟨hωkρQ, hωkρQ0⟩ := hyp.mul_mem_sdiff_Q0 hωkQ hωkQ0 hρQ0
  -- `ω⁻¹ = ω ρ`, since `ρ = ω²` is an involution
  have hρ1 : ρ * ρ = 1 := by
    have hs := hρQ0.1
    rwa [sq] at hs
  have hωinv : ω⁻¹ = ω * ρ := by
    rw [hρ]
    rw [hρ] at hρ1
    calc ω⁻¹ = ((ω * ω) * (ω * ω)) * ω⁻¹ := by rw [hρ1, one_mul]
      _ = ω * (ω * ω) := by group
  -- `X⁻¹ = ω_k ρ` and `(ω(ρy))⁻¹ = ω y`
  have hXinv : (ωk⁻¹ * ρ)⁻¹ = ωk * ρ := by
    rw [mul_inv_rev, hinvQ0 hρQ0, inv_inv]
    exact (hcentQ hρQ0 hωkQ).symm
  have hprodinv : (ω * (ρ * y))⁻¹ = ω * y := by
    rw [mul_inv_rev, hinvQ0 hρy, hωinv]
    calc (ρ * y) * (ω * ρ) = ω * ((ρ * y) * ρ) := by
          rw [← mul_assoc, ← hcentQ hρy hωQ]
          group
      _ = ω * ((ρ * ρ) * y) := by
          have hcy : y * ρ = ρ * y := hcentQ hρQ0 (hyp.Q0_le_Q hyQ0)
          calc ω * ((ρ * y) * ρ) = ω * (ρ * (y * ρ)) := by group
            _ = ω * (ρ * (ρ * y)) := by rw [hcy]
            _ = ω * ((ρ * ρ) * y) := by group
      _ = ω * y := by rw [hρ1, one_mul]
  -- the two tools: `f ∘ f = id` and `f` descends to orbits
  have hff : ∀ {z : G}, z ∈ hyp.Q → z ≠ 1 → f (f z) = z :=
    fun hzQ hz1 => (hTwo hyp.rankOneSetup H hzQ hz1).1
  have hfrel : ∀ {a b : G}, a ∈ hyp.Q → a ≠ 1 → dOrbitRel hyp.KW a b →
      dOrbitRel hyp.KW (f a) (f b) := by
    intro a b haQ ha1 hab
    obtain ⟨d, hdKW, rfl⟩ := hab
    exact H.dOrbitRel_f_of_le hyp.rankOneSetup haQ ha1 hyp.KW_le_D
      (fun _ ha => hyp.conj_t_mem_KW ha) hdKW
  -- step 1: `f(X⁻¹) ~ ω(ρy)`
  have hs1 : dOrbitRel hyp.KW (ω * (ρ * y)) (f (ωk * ρ)) := by
    have h := hfrel (H.f_mem hωρyQ (hne hωρyQ0))
      (IsFGH.f_ne_one hyp.rankOneSetup H hωρyQ (hne hωρyQ0)) hk
    rwa [hff hωρyQ (hne hωρyQ0)] at h
  -- step 2: `f((f X⁻¹)⁻¹) ~ ω`
  have hs2 : dOrbitRel hyp.KW ω (f ((f (ωk * ρ))⁻¹)) := by
    have hinvrel : dOrbitRel hyp.KW (ω * y) ((f (ωk * ρ))⁻¹) := by
      have h := dOrbitRel.inv hs1
      rwa [hprodinv] at h
    have h1 := hfrel hωyQ (hne hωyQ0) hinvrel
    have h2 : dOrbitRel hyp.KW (f (ω * y)) ω := by
      have hnr : dOrbitRel hyp.KW (ω * y) (f ω) :=
        ⟨ζ, hyp.mem_KW_of_mem_W hζW, hnorm⟩
      have h := hfrel hωyQ (hne hωyQ0) hnr
      rwa [hff hωQ (hne hωQ0)] at h
    exact dOrbitRel.trans h2.symm h1
  -- step 3: `f((f((f X⁻¹)⁻¹))⁻¹) ~ ω_i(ρy)`
  have hs3 : dOrbitRel hyp.KW (ωi * (ρ * y))
      (f ((f ((f (ωk * ρ))⁻¹))⁻¹)) := by
    have hinvrel : dOrbitRel hyp.KW (ω * ρ) ((f ((f (ωk * ρ))⁻¹))⁻¹) := by
      have h := dOrbitRel.inv hs2
      rwa [hωinv] at h
    exact dOrbitRel.trans hi.symm (hfrel hωρQ (hne hωρQ0) hinvrel)
  -- (H5): the cube is the identity on orbits
  have hXQ : ωk⁻¹ * ρ ∈ hyp.Q :=
    hyp.Q.mul_mem (hyp.Q.inv_mem hωkQ) (hyp.Q0_le_Q hρQ0)
  have hX1 : ωk⁻¹ * ρ ≠ 1 := by
    intro hc
    refine hne hωkρQ0 ?_
    rw [← hXinv, hc, inv_one]
  have hcube := H.dOrbitRel_fj_cube_of_mem hyp.rankOneSetup hXQ hX1 hhX
  rw [hXinv] at hcube
  exact dOrbitRel.trans hcube hs3.symm

/-- **`ω² = (0,α)` from the (H5) conclusion** (Peterfalvi Part II, p. 129).

The chain of (17), (20) and (H5) ends with `(ω⁻¹(0,r))^{KW} = (ω(0,α+r))^{KW}`; since
`ω⁻¹ = ω · (ω²)⁻¹`, both sides are translates of `ω` by elements of `Q₀`, so the freeness
of the `D`-action makes the conjugator trivial and the translates equal — which is
`ω² = (0,α)`. -/
theorem sq_eq_of_dOrbitRel (hfree : hyp.FreeD)
    {ω y ρ : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hρQ0 : ρ ∈ hyp.Q0) (hsq : ω * ω ∈ hyp.Q0)
    (hrel : GroupTheory.RankOneBNPair.dOrbitRel hyp.KW (ω⁻¹ * ρ) (ω * (ρ * y))) :
    ω * ω = y := by
  obtain ⟨d, hdKW, hd⟩ := hrel
  have hdD : d ∈ hyp.D := hyp.KW_le_D hdKW
  have hsq1 : (ω * ω) * (ω * ω) = 1 := by
    have hs := hsq.1
    rwa [sq] at hs
  -- `ω⁻¹ ρ` is the `Q₀`-translate of `ω` by `ω² ρ`
  have hleft : ω⁻¹ * ρ = ω * ((ω * ω) * ρ) := by
    have e : ω⁻¹ = ω * (ω * ω) := by
      calc ω⁻¹ = ((ω * ω) * (ω * ω)) * ω⁻¹ := by rw [hsq1, one_mul]
        _ = ω * (ω * ω) := by group
    rw [e]
    group
  have hmemσρ : (ω * ω) * ρ ∈ hyp.Q0 := hyp.Q0.mul_mem hsq hρQ0
  obtain ⟨hωQ', hωQ0'⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hmemσρ
  have hw : ((ω * ω) * ρ)⁻¹ * (ρ * y) ∈ hyp.Q0 :=
    hyp.Q0.mul_mem (hyp.Q0.inv_mem hmemσρ) (hyp.Q0.mul_mem hρQ0 hyQ0)
  have hconj : d⁻¹ * (ω * ((ω * ω) * ρ)) * d
      = (ω * ((ω * ω) * ρ)) * (((ω * ω) * ρ)⁻¹ * (ρ * y)) := by
    have hR : (ω * ((ω * ω) * ρ)) * (((ω * ω) * ρ)⁻¹ * (ρ * y)) = ω * (ρ * y) := by group
    rw [hR, ← hleft, ← hd]
  have hd1 : d = 1 :=
    hfree hωQ' hωQ0' hdD hw hconj
  rw [hd1, inv_one, one_mul, mul_one, hleft] at hd
  -- `Q₀` is abelian, so the two translates cancel
  have hcancel : (ω * ω) * ρ = ρ * y := (mul_left_cancel hd).symm
  have hcy : y * ρ = ρ * y :=
    Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hρQ0) y (hyp.Q0_le_Q hyQ0)
  refine mul_right_cancel (b := ρ) ?_
  rw [hcancel, hcy]

/-- **`f(ω) = (ω⁻¹)^ζ`** (Peterfalvi Part II, p. 129): once `ω² = (0,α)`, the
normalization `f(ω) = (ω(0,α))^ζ` *is* the assertion, because `ω(0,α) = ω³ = ω⁻¹` (the
square lies in `Q₀`, so `ω⁴ = 1`). -/
theorem f_eq_conj_inv_of_sq_eq {ζ ω y : G} (hyQ0 : y ∈ hyp.Q0)
    (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) (hsq : ω * ω = y) :
    f ω = ζ⁻¹ * ω⁻¹ * ζ := by
  have hy1 : (ω * ω) * (ω * ω) = 1 := by
    rw [hsq]
    have hs := hyQ0.1
    rwa [sq] at hs
  have hωy : ω * y = ω⁻¹ := by
    rw [← hsq]
    calc ω * (ω * ω) = ((ω * ω) * (ω * ω)) * ω⁻¹ := by group
      _ = ω⁻¹ := by rw [hy1, one_mul]
  rw [hfω, hωy]

/-- **§2's closing Proposition, second half** (Peterfalvi Part II, p. 129):
`f(ω') = (ω'⁻¹)^ζ`.

Assembles the three pieces: the (H5) chain
(`dOrbitRel_of_stepTwenty_chain`) puts `ω'⁻¹ρ` and `ω'(ρy)` in the same `D`-orbit, the
freeness of the `D`-action (`sq_eq_of_dOrbitRel`) turns that into `ω'² = (0,α)`, and the
normalization then reads as the assertion (`f_eq_conj_inv_of_sq_eq`).

The hypothesis `ω_i = ω_k` is the book's "whence `i = k`", which comes from the
representatives `ω_1, …, ω_n` lying in *distinct* `KW`-orbits; that family is not
formalized here, so the coincidence is assumed. -/
theorem f_eq_conj_inv_of_stepTwenty_chain (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hfree : hyp.FreeD)
    {ζ ω ω' y ρ : G}
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hω'Q : ω' ∈ hyp.Q) (hω'Q0 : ω' ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hρQ0 : ρ ∈ hyp.Q0) (hρ : ρ = ω * ω) (hζW : ζ ∈ hyp.W)
    (hsq' : ω' * ω' ∈ hyp.Q0)
    (hnorm : f ω = ζ⁻¹ * (ω * y) * ζ) (hnorm' : f ω' = ζ⁻¹ * (ω' * y) * ζ)
    (hhX : h (ω'⁻¹ * ρ) ∈ hyp.KW)
    (hi : dOrbitRel hyp.KW (f (ω * ρ)) (ω' * (ρ * y)))
    (hk : dOrbitRel hyp.KW (f (ω * (ρ * y))) (ω' * ρ)) :
    ω' * ω' = y ∧ f ω' = ζ⁻¹ * ω'⁻¹ * ζ := by
  have hchain := hyp.dOrbitRel_of_stepTwenty_chain H hωQ hωQ0 hω'Q hω'Q0 hyQ0 hρQ0 hρ
    hζW hnorm hhX hi hk
  have hsq := hyp.sq_eq_of_dOrbitRel hfree hω'Q hω'Q0 hyQ0 hρQ0 hsq' hchain
  exact ⟨hsq, hyp.f_eq_conj_inv_of_sq_eq hyQ0 hnorm' hsq⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
