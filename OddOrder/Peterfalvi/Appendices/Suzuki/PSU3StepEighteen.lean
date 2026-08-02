/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3StepFifteen

/-!
# Peterfalvi Part II, Ch. IV §2, step (18): `(h(ω)ζ⁻¹)^m = 1`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, p. 127.

> **(18)** `(h(ω)ζ⁻¹)^m = 1`.

The recursion for `h` along the sequence of (11) is `stepEighteen_step` and its closed
form is `stepEighteen_unroll`, which records the accumulated element of `K` as the
*inverse* of the `K`-part of `d_i`.  Step (15) has already shown that at the last index
that `K`-part is trivial (`stepFifteen_length_eq`), which is the book's `c_{m-1} = α`; so
at the stopping index

  `h(ω y) = (h(ω)ζ⁻¹)^{m-1} · h(ω) · ζ^{m-1}`.

Against this the book plays (H4): `h(ω(0,α)) = h(f(ω)^{ζ⁻¹}) = ζ h(ω)⁻¹ ζ⁻¹`.  Since
`D = KW` and `ζ` generates `W`, `h(ω)` commutes with `ζ`, and comparing the two gives
`h(ω)^m = 1`, hence `(h(ω)ζ⁻¹)^m = h(ω)^m ζ^{-m} = 1`.

## Main results

* `Hypothesis.h_mul_eq_conj_inv` — (H4) at the normalization: `h(ω y) = ζ h(ω)⁻¹ ζ⁻¹`.
* `Hypothesis.commute_h_zeta` — `h(ω)` commutes with `ζ` (`D = KW`, `W = ⟨ζ⟩`).
* `Hypothesis.stepEighteen` — **step (18)**.
* `Hypothesis.h_mem_W` — `h(ω) ∈ W`, the first half of §2's closing Proposition.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **(H4) at the normalization** (Peterfalvi Part II, p. 127): from `f(ω) = (ω y)^ζ`,

  `h(ω y) = ζ h(ω)⁻¹ ζ⁻¹`.

`h(f(x)) = h(x)⁻¹` is (H2)'s third clause and `h(x^a) = a^{-t} h(x) a` is (H4); with
`ζ^t = ζ` the twist disappears. -/
theorem h_mul_eq_conj_inv (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) :
    h (ω * y) = ζ * (h ω)⁻¹ * ζ⁻¹ := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨hωyQ, hωyQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hyQ0
  have hωy1 : ω * y ≠ 1 := fun hc => hωyQ0 (hc ▸ hyp.Q0.one_mem)
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have htζt : hyp.t * ζ * hyp.t = ζ := by
    have hc := hyp.commute_t_of_mem_V (hyp.W_le_V hζ)
    rw [← hc.eq, mul_assoc, hyp.rankOneSetup.invol, mul_one]
  obtain ⟨-, -, e4⟩ := hThree hyp.rankOneSetup H hωyQ hωy1 hζD
  rw [htζt] at e4
  have e2 : h (f ω) = (h ω)⁻¹ := (hTwo hyp.rankOneSetup H hωQ hω1).2.2
  rw [hfω, e4] at e2
  calc h (ω * y) = ζ * (ζ⁻¹ * h (ω * y) * ζ) * ζ⁻¹ := by group
    _ = ζ * (h ω)⁻¹ * ζ⁻¹ := by rw [e2]

/-- **`h(ω)` commutes with `ζ`.**

Under Chapter IV's `V = W`, `D = K W` (`exists_mem_K_mem_W_mul`), and `h(ω) ∈ D`.  Its
`K`-part commutes with `ζ` because `W = C_V(K)`, and its `W`-part because `ζ` generates
`W` — which is what `orderOf ζ = |W|` says. -/
theorem commute_h_zeta (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h) (hVW : hyp.V = hyp.W)
    {ζ ω : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hWcard : orderOf ζ = Nat.card ↥hyp.W) :
    Commute (h ω) ζ := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨κ, hκ, v, hv, hHkv⟩ :=
    hyp.exists_mem_K_mem_W_mul hVW (H.h_mem hωQ hω1)
  -- `ζ` generates `W`
  have hW : hyp.W = Subgroup.zpowers ζ := hyp.W_eq_zpowers hζ hWcard
  have hcκ : Commute κ ζ := hyp.commute_of_mem_W_of_mem_K hζ hκ
  have hcv : Commute v ζ := hyp.commute_of_mem_W_of_W_eq_zpowers hW hv
  rw [hHkv]
  exact hcκ.mul_left hcv

/-- **Step (18)** (Peterfalvi Part II, p. 127): `(h(ω)ζ⁻¹)^m = 1`, with `m = orderOf ζ`.

At the stopping index `N` the sequence has `z_N = y`, so `stepEighteen_unroll` reads
`h(ω y) = (h(ω)ζ⁻¹)^N h(ω) ζ^N`, its `K`-part being trivial by step (15).  Comparing with
`h(ω y) = ζ h(ω)⁻¹ ζ⁻¹` and using that `h(ω)` commutes with `ζ` gives
`h(ω)^{N+2} = 1`; and `N + 2 = orderOf ζ`, so `(h(ω)ζ⁻¹)^{N+2} = h(ω)^{N+2} ζ^{-(N+2)}`
is `1`. -/
theorem stepEighteen (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hWcard : orderOf ζ = Nat.card ↥hyp.W)
    {N : ℕ} (hns : ∀ i < N, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hstop : y * (hyp.stepElevenSeq ζ y N).1 = 1) :
    (h ω * ζ⁻¹) ^ orderOf ζ = 1 := by
  -- the stopping rule says `z_N = y`
  have hzy : (hyp.stepElevenSeq ζ y N).1 = y := by
    have hinv : y⁻¹ = (hyp.stepElevenSeq ζ y N).1 := inv_eq_of_mul_eq_one_right hstop
    have hyy : y⁻¹ = y := by
      have h2 := hyQ0.1
      rw [sq] at h2
      exact inv_eq_of_mul_eq_one_right h2
    rw [← hinv, hyy]
  -- the unrolled form, with its `K`-part killed by step (15)
  obtain ⟨k, hkK, hkcoset, hk⟩ :=
    hyp.stepEighteen_unroll H hC2 hζ hωQ hωQ0 hyQ0 hfω N hns
  obtain ⟨hlen, hkone⟩ :=
    hyp.stepFifteen_length_eq H hC2 (hyp.freeD_of_V_eq_W M hZ hmu hVW) hζ hωQ hωQ0
      hyQ0 hfω hns hstop
  rw [hkone k hkK hkcoset, inv_one, mul_one, hzy] at hk
  -- (H4) gives the other reading of `h(ω y)`
  rw [hyp.h_mul_eq_conj_inv H hζ hωQ hωQ0 hyQ0 hfω] at hk
  -- `h(ω)` commutes with `ζ`
  have hc : Commute (h ω) ζ := hyp.commute_h_zeta H hVW hζ hωQ hωQ0 hWcard
  have hcinv : Commute (h ω) ζ⁻¹ := hc.inv_right
  -- unwind to `h(ω)^{N+2} = 1`
  have hleft : ζ * (h ω)⁻¹ * ζ⁻¹ = (h ω)⁻¹ := by
    rw [(hc.symm.inv_right).eq]
    group
  have hright : (h ω * ζ⁻¹) ^ N * h ω * ζ ^ N = (h ω) ^ (N + 1) := by
    rw [hcinv.mul_pow, inv_pow]
    have hcomm2 : (ζ ^ N)⁻¹ * h ω = h ω * (ζ ^ N)⁻¹ := ((hc.pow_right N).symm.inv_left).eq
    calc (h ω) ^ N * (ζ ^ N)⁻¹ * h ω * ζ ^ N
        = (h ω) ^ N * ((ζ ^ N)⁻¹ * h ω) * ζ ^ N := by group
      _ = (h ω) ^ N * (h ω * (ζ ^ N)⁻¹) * ζ ^ N := by rw [hcomm2]
      _ = (h ω) ^ (N + 1) := by rw [pow_succ]; group
  rw [hleft, hright] at hk
  have hpow : (h ω) ^ (N + 2) = 1 := by
    calc (h ω) ^ (N + 2) = (h ω) ^ (N + 1) * h ω := by rw [pow_succ]
      _ = (h ω)⁻¹ * h ω := by rw [← hk]
      _ = 1 := inv_mul_cancel _
  -- assemble
  have hζpow : ζ ^ (N + 2) = 1 := by
    rw [hlen]
    exact pow_orderOf_eq_one ζ
  rw [← hlen, hcinv.mul_pow, hpow, one_mul, inv_pow, hζpow, inv_one]

/-- **`h(ω) ∈ W`** (Peterfalvi Part II, p. 129, first half of §2's closing Proposition).

The book argues that the Sylow subgroups of `D` are cyclic ([H], Kap. V, Satz 8.15), so
that each `p`-component of `h(ω)ζ⁻¹` lands in `W` because `|P ∩ W| = m_p`.  With
`D = K W` in hand the coprimality does it directly: writing `h(ω) = κ v`, step (18) gives
`κ^m = 1` (the `W`-part is killed by `m = |W|` anyway), while `κ^{q-1} = 1` because
`|K| = q − 1`; and `m` divides `q + 1`, which is coprime to `q − 1`. -/
theorem h_mem_W (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W) (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hWcard : orderOf ζ = Nat.card ↥hyp.W)
    {N : ℕ} (hns : ∀ i < N, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hstop : y * (hyp.stepElevenSeq ζ y N).1 = 1) :
    h ω ∈ hyp.W := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  have hc : Commute (h ω) ζ := hyp.commute_h_zeta H hVW hζ hωQ hωQ0 hWcard
  -- step (18), with the `ζ` factored off
  have h18 := hyp.stepEighteen H hC2 M hZ hmu hVW hζ hωQ hωQ0 hyQ0 hfω hWcard hns hstop
  have hζpow : ζ ^ orderOf ζ = 1 := pow_orderOf_eq_one ζ
  have hhpow : (h ω) ^ orderOf ζ = 1 := by
    rw [hc.inv_right.mul_pow, inv_pow, hζpow, inv_one, mul_one] at h18
    exact h18
  -- split `h(ω)` along `D = K W`
  obtain ⟨κ, hκK, v, hvW, hκv⟩ := hyp.exists_mem_K_mem_W_mul hVW (H.h_mem hωQ hω1)
  have hcomm : κ * v = v * κ := hyp.commute_of_mem_W_of_mem_K hvW hκK
  have hvpow : v ^ orderOf ζ = 1 := by
    rw [hWcard]
    have := pow_card_eq_one' (G := ↥hyp.W) (x := ⟨v, hvW⟩)
    exact congrArg Subtype.val this
  have hκpow : κ ^ orderOf ζ = 1 := by
    have hsplit : (κ * v) ^ orderOf ζ = κ ^ orderOf ζ * v ^ orderOf ζ :=
      (Commute.mul_pow (h := hcomm) _)
    rw [hκv, hsplit, hvpow, mul_one] at hhpow
    exact hhpow
  -- `κ` is killed by `q + 1` and by `q − 1`
  have hκadd : κ ^ (2 ^ m + 1) = 1 := by
    obtain ⟨c, hcc⟩ := hWdvd
    rw [hcc, ← hWcard, pow_mul, hκpow, one_pow]
  have hκsub : κ ^ (2 ^ m - 1) = 1 := by
    have hKcard : Nat.card ↥hyp.K = 2 ^ m - 1 := by
      rw [hyp.card_K_eq_card_Q0_sub_one, hQ0card]
    have := pow_card_eq_one' (G := ↥hyp.K) (x := ⟨κ, hκK⟩)
    rw [hKcard] at this
    exact congrArg Subtype.val this
  have hκ1 : κ = 1 :=
    eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one hm hκsub hκadd
  rw [hκv, hκ1, one_mul]
  exact hvW

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
