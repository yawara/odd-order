/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3StepFifteen
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3FrobeniusD
import OddOrder.GroupTheory.ZGroupNormalCyclic

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
`h(ω y) = (h(ω)ζ⁻¹)^N h(ω) ζ^N`, its `K`-part being trivial by step (15).  Since
`N + 2 = orderOf ζ`, the tail `ζ^N` is `ζ^{-2}`, and comparing with (H4)'s
`h(ω y) = ζ h(ω)⁻¹ ζ⁻¹` gives `g^N h(ω) = ζ h(ω)⁻¹ ζ` for `g = h(ω) ζ⁻¹`; two more
factors of `g` then collapse to `1`.

This is the book's own computation (p. 127) and, unlike the repository's previous route,
it uses no commutation between `h(ω)` and `ζ` — hence no `V = W`. -/
theorem stepEighteen (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hfree : hyp.FreeD)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
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
    hyp.stepFifteen_length_eq H hC2 hfree hζ hωQ hωQ0 hyQ0 hfω hns hstop
  rw [hkone k hkK hkcoset, inv_one, mul_one, hzy] at hk
  -- (H4) gives the other reading of `h(ω y)`
  rw [hyp.h_mul_eq_conj_inv H hζ hωQ hωQ0 hyQ0 hfω] at hk
  -- `ζ^N = ζ^{-2}`, since `ζ` has order `N + 2`
  have hζpow : ζ ^ (N + 2) = 1 := by
    rw [hlen]
    exact pow_orderOf_eq_one ζ
  have hζN : ζ ^ N = (ζ ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_add]; exact hζpow)
  -- so the unrolled identity reads `g^N h(ω) = ζ h(ω)⁻¹ ζ`
  have hA : (h ω * ζ⁻¹) ^ N * h ω = ζ * (h ω)⁻¹ * ζ := by
    have h2 : (h ω * ζ⁻¹) ^ N * h ω * (ζ ^ 2)⁻¹ = ζ * (h ω)⁻¹ * ζ⁻¹ := by
      rw [← hζN]; exact hk.symm
    calc (h ω * ζ⁻¹) ^ N * h ω
        = (h ω * ζ⁻¹) ^ N * h ω * (ζ ^ 2)⁻¹ * ζ ^ 2 := by group
      _ = ζ * (h ω)⁻¹ * ζ⁻¹ * ζ ^ 2 := by rw [h2]
      _ = ζ * (h ω)⁻¹ * ζ := by group
  -- two more factors of `g = h(ω) ζ⁻¹` close it
  calc (h ω * ζ⁻¹) ^ orderOf ζ
      = (h ω * ζ⁻¹) ^ (N + 2) := by rw [← hlen]
    _ = (h ω * ζ⁻¹) ^ N * h ω * ζ⁻¹ * (h ω * ζ⁻¹) := by
        rw [pow_succ, pow_succ]; group
    _ = ζ * (h ω)⁻¹ * ζ * ζ⁻¹ * (h ω * ζ⁻¹) := by rw [hA]
    _ = 1 := by group

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
  have h18 := hyp.stepEighteen H hC2 (hyp.freeD_of_V_eq_W M hZ hmu hVW) hζ hωQ hωQ0
    hyQ0 hfω hns hstop
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

/-- **`W` is normal in `D`** — the book's "since `W ⊴ D`" (Peterfalvi Part II, p. 129).

`W = D ∩ C(H ∩ I)` (Ch. I Prop 5, `W_eq_centralizer_involutions_H`) and conjugation by
`d ∈ D ≤ H` permutes the involutions of `H`, so it preserves the centralizer
condition. -/
theorem normal_W_subgroupOf_D : (hyp.W.subgroupOf hyp.D).Normal := by
  refine ⟨fun w hw d => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hw ⊢
  rw [hyp.W_eq_centralizer_involutions_H] at hw ⊢
  refine ⟨hyp.D.mul_mem (hyp.D.mul_mem d.2 hw.1) (hyp.D.inv_mem d.2),
    Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
  obtain ⟨hq2, hq1, hqH⟩ := hq
  have hdH : (d : G) ∈ hyp.H := hyp.D_le_H d.2
  -- conjugation by `d ∈ D ≤ H` permutes the involutions of `H`
  have hqc : (d : G)⁻¹ * q * (d : G) ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := by
    refine ⟨?_, ?_, hyp.H.mul_mem (hyp.H.mul_mem (hyp.H.inv_mem hdH) hqH) hdH⟩
    · have : ((d : G)⁻¹ * q * (d : G)) ^ 2 = (d : G)⁻¹ * q ^ 2 * (d : G) := by
        rw [sq, sq]; group
      rw [this, hq2]; group
    · intro hcon
      refine hq1 ?_
      have : q = (d : G) * ((d : G)⁻¹ * q * (d : G)) * (d : G)⁻¹ := by group
      rw [this, hcon]; group
  have hcw := Subgroup.mem_centralizer_iff.mp hw.2 _ hqc
  push_cast
  calc q * ((d : G) * (w : G) * (d : G)⁻¹)
      = (d : G) * (((d : G)⁻¹ * q * (d : G)) * (w : G)) * (d : G)⁻¹ := by group
    _ = (d : G) * ((w : G) * ((d : G)⁻¹ * q * (d : G))) * (d : G)⁻¹ := by rw [hcw]
    _ = ((d : G) * (w : G) * (d : G)⁻¹) * q := by group

/-- **`h(ω) ∈ W`, by the book's argument** (Peterfalvi Part II, p. 129, first half of §2's
closing Proposition).

Step (18) says `(h(ω)ζ⁻¹)^{|W|} = 1`, and §2's hypothesis makes `D` a Frobenius
complement of odd order, hence a `Z`-group (`isZGroup_D_of_freeD`).  A cyclic normal
subgroup of a `Z`-group absorbs every element it kills
(`mem_of_pow_card_eq_one_of_isZGroup`), which is the book's `p`-component computation.
So `h(ω)ζ⁻¹ ∈ W`, and `ζ ∈ W`.

Unlike `h_mem_W` this never uses `D = K W`, i.e. never uses `V = W` — which is what
Ch. IV §4 needs.  (`PSU3SectionThree.h_mem_W_of_freeD` is a different statement with a
misleadingly similar name: there "free `D`" is spelled as the hypothesis `V = W`.) -/
theorem h_mem_W_of_frobeniusD (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hfree : hyp.FreeD)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hWcyc : IsCyclic ↥hyp.W)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hWcard : orderOf ζ = Nat.card ↥hyp.W)
    {N : ℕ} (hns : ∀ i < N, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hstop : y * (hyp.stepElevenSeq ζ y N).1 = 1) :
    h ω ∈ hyp.W := by
  classical
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  have h18 := hyp.stepEighteen H hC2 hfree hζ hωQ hωQ0 hyQ0 hfω hns hstop
  haveI : IsZGroup ↥hyp.D := hyp.isZGroup_D_of_freeD hfree hZc hωQ hωQ0
  haveI := hyp.normal_W_subgroupOf_D
  have hWle : hyp.W ≤ hyp.D := hyp.W_le_D
  have hcard : Nat.card ↥(hyp.W.subgroupOf hyp.D) = Nat.card ↥hyp.W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv
  haveI : IsCyclic ↥(hyp.W.subgroupOf hyp.D) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWle).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWle).symm.surjective
  have hgD : h ω * ζ⁻¹ ∈ hyp.D :=
    hyp.D.mul_mem (H.h_mem hωQ hω1) (hyp.D.inv_mem (hWle hζ))
  have hpow : (⟨h ω * ζ⁻¹, hgD⟩ : ↥hyp.D) ^ Nat.card ↥(hyp.W.subgroupOf hyp.D) = 1 := by
    refine Subtype.ext ?_
    push_cast
    rw [hcard, ← hWcard]
    exact h18
  have hmem := OddOrder.GroupTheory.mem_of_pow_card_eq_one_of_isZGroup
    (W := hyp.W.subgroupOf hyp.D) inferInstance hpow
  have hgW : h ω * ζ⁻¹ ∈ hyp.W := Subgroup.mem_subgroupOf.mp hmem
  have hrw : h ω = (h ω * ζ⁻¹) * ζ := by group
  rw [hrw]
  exact hyp.W.mul_mem hgW hζ

/-- **The conjugators of §2 lie in `K W`** (Peterfalvi Part II, Ch. IV §2, p. 129:
"Moreover, by (H4), `h(ω_k⁻¹(0,r)) ∈ K W`").

The formula (18) is proved from is exactly `stepEighteen_unroll`,

  `h(ω z_n) = (h(ω) ζ⁻¹)^n · h(ω) · ζ^n · k⁻¹`   with `k ∈ K`,

which the book displays as `h(ω(0,u_i)) = (h(ω)ζ⁻¹)^i ζ^i (α / (β^i + β^{-i}))`.  Once
`h(ω) ∈ W` — the first half of §2's closing Proposition
(`h_mem_W_of_frobeniusD`) — every factor but the last lies in `W`, and the last lies in
`K`; so the whole thing lies in `K W`.

This is what makes §2's orbits genuinely `K W`-orbits, i.e. what the closing Proposition
needs in order to run without `V = W`. -/
theorem h_mul_stepElevenSeq_mem_KW (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) (hhW : h ω ∈ hyp.W)
    (n : ℕ) (hns : ∀ i < n, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1) :
    h (ω * (hyp.stepElevenSeq ζ y n).1) ∈ hyp.KW := by
  obtain ⟨k, hkK, -, hk⟩ := hyp.stepEighteen_unroll H hC2 hζ hωQ hωQ0 hyQ0 hfω n hns
  have hWpart : (h ω * ζ⁻¹) ^ n * h ω * ζ ^ n ∈ hyp.W :=
    hyp.W.mul_mem (hyp.W.mul_mem (pow_mem (hyp.W.mul_mem hhW (hyp.W.inv_mem hζ)) n) hhW)
      (pow_mem hζ n)
  have hrw : (h ω * ζ⁻¹) ^ n * h ω * (ζ ^ n * k⁻¹)
      = ((h ω * ζ⁻¹) ^ n * h ω * ζ ^ n) * k⁻¹ := by group
  rw [hk, hrw]
  exact hyp.mem_KW_of_mul_W_K hWpart (hyp.K.inv_mem hkK)

/-- **The (H4) reduction of the closing Proposition's conjugator** (Peterfalvi Part II,
Ch. IV §2, p. 129: "Moreover, by (H4), `h(ω_k⁻¹(0,r)) ∈ K W`").

Two applications of (H4) move the question from `ω'⁻¹ ρ` to the element it is built from.
`ρ ∈ Q₀` is a central involution of `Q`, so `(ω'⁻¹ρ)⁻¹ = ω' ρ` and
`h(ω'⁻¹ρ) = (h(ω'ρ)^t)⁻¹`; and `ω' ρ = (f z)^c` gives
`h(ω'ρ) = (c^t)⁻¹ · h(z)⁻¹ · c`.  Every twist by `t` stays inside `K W`
(`conj_t_mem_KW`), so `h(z) ∈ K W` is all that is needed.

This is the shape §2's closing Proposition uses it in: `ω'` is the normalized
representative `ω_k`, `ρ = ω₁²`, and `z` is the fibre element `ω₁(0, α + r)` whose
`h`-value `h_mul_stepElevenSeq_mem_KW` places in `K W`. -/
theorem h_inv_mul_mem_KW (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ω' ρ c z : G} (hω'Q : ω' ∈ hyp.Q) (hω'Q0 : ω' ∉ hyp.Q0) (hρQ0 : ρ ∈ hyp.Q0)
    (hzQ : z ∈ hyp.Q) (hz1 : z ≠ 1) (hcKW : c ∈ hyp.KW)
    (hrel : ω' * ρ = c⁻¹ * f z * c) (hhz : h z ∈ hyp.KW) :
    h (ω'⁻¹ * ρ) ∈ hyp.KW := by
  obtain ⟨hω'ρQ, hω'ρQ0⟩ := hyp.mul_mem_sdiff_Q0 hω'Q hω'Q0 hρQ0
  have hω'ρ1 : ω' * ρ ≠ 1 := fun hc => hω'ρQ0 (hc ▸ hyp.Q0.one_mem)
  -- `(ω'⁻¹ ρ)⁻¹ = ω' ρ`, since `ρ` is a central involution of `Q`
  have hρsq : ρ * ρ = 1 := by
    have hs := hρQ0.1
    rwa [sq] at hs
  have hcomm : ω' * ρ = ρ * ω' :=
    Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hρQ0) ω' hω'Q
  have hinv : ω'⁻¹ * ρ = (ω' * ρ)⁻¹ := by
    have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρsq
    have hcomm' : ω'⁻¹ * ρ = ρ * ω'⁻¹ := by
      calc ω'⁻¹ * ρ = ω'⁻¹ * (ρ * ω') * ω'⁻¹ := by group
        _ = ω'⁻¹ * (ω' * ρ) * ω'⁻¹ := by rw [← hcomm]
        _ = ρ * ω'⁻¹ := by group
    rw [mul_inv_rev, hρinv, hcomm']
  -- `h(ω' ρ) = (c^t)⁻¹ h(z)⁻¹ c ∈ K W`
  obtain ⟨-, -, e3⟩ := hThree hyp.rankOneSetup H (H.f_mem hzQ hz1)
    (H.f_ne_one hyp.rankOneSetup hzQ hz1) (hyp.KW_le_D hcKW)
  have e2 : h (f z) = (h z)⁻¹ := (hTwo hyp.rankOneSetup H hzQ hz1).2.2
  have hmid : h (ω' * ρ) ∈ hyp.KW := by
    rw [hrel, e3, e2]
    exact hyp.KW.mul_mem
      (hyp.KW.mul_mem (hyp.KW.inv_mem (hyp.conj_t_mem_KW hcKW)) (hyp.KW.inv_mem hhz))
      hcKW
  -- (H4) again: `h(x⁻¹) = (h(x)^t)⁻¹`
  obtain ⟨-, -, o3⟩ := hOne hyp.rankOneSetup H hω'ρQ hω'ρ1
  rw [hinv, o3]
  exact hyp.KW.inv_mem (hyp.conj_t_mem_KW hmid)

/-- **🎯 `h(ω_k⁻¹(0,r)) ∈ K W`** — the book's one-line "Moreover, by (H4)" (Peterfalvi
Part II, Ch. IV §2, p. 129), in full.

The element the closing Proposition applies (H5) to is `X = ω_k⁻¹(0,r)`, and
`h_inv_mul_mem_KW` reduces `h(X) ∈ K W` to `h(ω(0,α+r)) ∈ K W`, where `ω(0,α+r)` is what
the definition of the index `k` conjugates `ω_k(0,r)` from.  Now

  `ω(0,α+r) = (ω(0,α))⁻¹`,

because `(0,r) = ω²` makes `ω⁻¹ = ω(0,r)`; so (H4)'s `h(x⁻¹) = (h(x)^t)⁻¹` moves the
question to `h(ω(0,α))`.  And `(0,α)` *is* one of the sequence values of (11) — it is the
stopping value `z_N` of step (15) — so `h_mul_stepElevenSeq_mem_KW` applies.

Every `t`-twist on the way stays inside `K W` (`conj_t_mem_KW`). -/
theorem h_inv_mul_mem_KW_of_stepTwenty (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) (hhW : h ω ∈ hyp.W)
    {N : ℕ} (hns : ∀ i < N, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hstop : y * (hyp.stepElevenSeq ζ y N).1 = 1)
    {ωk ρ c : G} (hωkQ : ωk ∈ hyp.Q) (hωkQ0 : ωk ∉ hyp.Q0)
    (hρdef : ρ = ω * ω) (hρQ0 : ρ ∈ hyp.Q0) (hcKW : c ∈ hyp.KW)
    (hrel : ωk * ρ = c⁻¹ * f (ω * (ρ * y)) * c) :
    h (ωk⁻¹ * ρ) ∈ hyp.KW := by
  -- the stopping rule says `z_N = y`
  have hzy : (hyp.stepElevenSeq ζ y N).1 = y := by
    have hinv : y⁻¹ = (hyp.stepElevenSeq ζ y N).1 := inv_eq_of_mul_eq_one_right hstop
    have hyy : y⁻¹ = y := by
      have h2 := hyQ0.1
      rw [sq] at h2
      exact inv_eq_of_mul_eq_one_right h2
    rw [← hinv, hyy]
  -- `h(ω y) ∈ K W`, `y` being the stopping value of the sequence
  have hωy : h (ω * y) ∈ hyp.KW := by
    have := hyp.h_mul_stepElevenSeq_mem_KW H hC2 hζ hωQ hωQ0 hyQ0 hfω hhW N hns
    rwa [hzy] at this
  -- `ω(ρ y) = (ω y)⁻¹`, since `ρ = ω²` gives `ω⁻¹ = ω ρ`
  obtain ⟨hωyQ, hωyQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hyQ0
  have hωy1 : ω * y ≠ 1 := fun hc => hωyQ0 (hc ▸ hyp.Q0.one_mem)
  have hρsq : ρ * ρ = 1 := by
    have hs := hρQ0.1
    rwa [sq] at hs
  have hωinv : ω⁻¹ = ω * ρ := by
    rw [hρdef]
    rw [hρdef] at hρsq
    calc ω⁻¹ = ((ω * ω) * (ω * ω)) * ω⁻¹ := by rw [hρsq, one_mul]
      _ = ω * (ω * ω) := by group
  have hyinv : y⁻¹ = y := by
    have h2 := hyQ0.1
    rw [sq] at h2
    exact inv_eq_of_mul_eq_one_right h2
  have hcy : y * ω = ω * y :=
    (Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hyQ0) ω hωQ).symm
  have hinvωy : (ω * y)⁻¹ = ω * (ρ * y) := by
    rw [mul_inv_rev, hyinv, hωinv]
    calc y * (ω * ρ) = (y * ω) * ρ := by group
      _ = (ω * y) * ρ := by rw [hcy]
      _ = ω * (ρ * y) := by
          have hcρy : y * ρ = ρ * y :=
            (Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hρQ0) y
              (hyp.Q0_le_Q hyQ0))
          rw [mul_assoc, hcρy]
  -- (H4): `h(x⁻¹) = (h(x)^t)⁻¹`
  obtain ⟨-, -, o3⟩ := hOne hyp.rankOneSetup H hωyQ hωy1
  have hz : h (ω * (ρ * y)) ∈ hyp.KW := by
    rw [← hinvωy, o3]
    exact hyp.KW.inv_mem (hyp.conj_t_mem_KW hωy)
  obtain ⟨hωρyQ, hωρyQ0⟩ :=
    hyp.mul_mem_sdiff_Q0 hωQ hωQ0 (hyp.Q0.mul_mem hρQ0 hyQ0)
  exact hyp.h_inv_mul_mem_KW H hωkQ hωkQ0 hρQ0 hωρyQ
    (fun hc => hωρyQ0 (hc ▸ hyp.Q0.one_mem)) hcKW hrel hz

/-- **`h(ω) ∈ W` for a normalized `ω`** (Peterfalvi Part II, Ch. IV §2, p. 129, the first
half of the closing Proposition), with the stopping index of step (15) produced inside.

`exists_stop_lt_orderOf` says the sequence of (11) does stop; `Nat.find` takes the first
index it does, which is what `h_mem_W_of_frobeniusD` consumes. -/
theorem h_mem_W_of_normalized (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hfree : hyp.FreeD)
    (hZc : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hWcyc : IsCyclic ↥hyp.W)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hWcard : orderOf ζ = Nat.card ↥hyp.W) :
    h ω ∈ hyp.W := by
  classical
  have hex : ∃ i, y * (hyp.stepElevenSeq ζ y i).1 = 1 := by
    obtain ⟨i, -, hi⟩ := hyp.exists_stop_lt_orderOf H hC2 hζ hωQ hωQ0 hyQ0 hfω
    exact ⟨i, hi⟩
  exact hyp.h_mem_W_of_frobeniusD H hC2 hfree hZc hWcyc hζ hωQ hωQ0 hyQ0 hfω hWcard
    (fun _ hi => Nat.find_min hex hi) (Nat.find_spec hex)

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
