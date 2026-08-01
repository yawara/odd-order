/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3OrbitCount
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3Sequence
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3PairComparison

/-!
# Peterfalvi Part II, Ch. IV §2, step (15): the sequence of (11) exhausts the orbit

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, p. 126.

Step (15) says two things about the sequence `(u_i), (v_i), (d_i)` of (11):

> `m₁ = m − 1`, `c_{m₁} = α`, `d_{m₁} = ζ⁻¹`, and the elements `u ∈ F` such that
> `f(ω(0,u))‾` lies in the orbit of `ω̄` are exactly `u₁, …, u_{m−1}`.

`PSU3Sequence` already has the easy half of the length — the sequence cannot run past
`ζ^i = 1` — but both the identification `d_{m₁} = ζ⁻¹` and the exhaustion need the
freeness of the `D`-action on `(Q/Q₀)^#` (`eq_one_of_conj_eq_mul_Q0_of_mem_D`), which is
where the standard model enters.

The three steps here are:

* at the stopping index the invariant of (11) and the *inverted* normalization
  `f(ω y) = ω^{ζ⁻¹}` present the same element two ways, so `ζ⁻¹ d_N⁻¹` fixes `ω̄` and is
  therefore trivial — the book's `d_{m₁} = ζ⁻¹`;
* two indices with the same `z_i` would likewise give a nontrivial `d_i d_j⁻¹` fixing
  `ω̄`, so the `z_i` are pairwise distinct;
* the sequence then has exactly `m − 1` distinct entries inside a set step (8) counts to
  have `|W| − 1 = m − 1` elements, so it fills it.

## Main results

* `Hypothesis.stepFifteen_stop_d_eq_inv` — `d_N = ζ⁻¹` at the stopping index.
* `Hypothesis.lt_orderOf_of_not_stopped` — `N + 1 < orderOf ζ` while the sequence runs.
* `Hypothesis.stepFifteen_length_eq` — `N + 2 = orderOf ζ`, the book's `m₁ = m − 1`, and the
  `K`-part of `d_N` is trivial (the book's `c_{m₁} = α`).
* `Hypothesis.stepElevenSeq_fst_injOn` — the `z_i` are pairwise distinct.
* `Hypothesis.stepFifteen_exhaust` — the set counted by step (8) *is* `{z_0, …, z_N}`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **The normalization, inverted** (Peterfalvi Part II, p. 126): from
`f(ω) = (ω y)^ζ` one gets `f(ω y) = ω^{ζ⁻¹}`.

This is `f_conj_swap` at `e = ζ`, where the twist `ζ^t` is `ζ` itself because `ζ ∈ W ≤ V`
centralizes `t`.  It is the second reading of `f(ω y)` that step (15) plays off against
the invariant of (11) at the stopping index. -/
theorem f_mul_eq_conj_of_normalized (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) :
    f (ω * y) = ζ * ω * ζ⁻¹ := by
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨hωyQ, hωyQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hyQ0
  have hωy1 : ω * y ≠ 1 := fun hc => hωyQ0 (hc ▸ hyp.Q0.one_mem)
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  have hswap := hyp.f_conj_swap H hωQ hω1 hωyQ hωy1 hζD hfω
  have htζt : hyp.t * ζ * hyp.t = ζ := by
    have hc := hyp.commute_t_of_mem_V (hyp.W_le_V hζ)
    rw [← hc.eq, mul_assoc, hyp.rankOneSetup.invol, mul_one]
  rwa [htζt] at hswap

/-- **`d_N = ζ⁻¹` at the stopping index** (Peterfalvi Part II, p. 126, step (15)).

At the index where the recursion of (11) stops, `y z_N = 1`, so `z_N = y` (`y` being an
involution) and the invariant reads `f(ω y) = (ω w_N)^{d_N}`.  But
`f_mul_eq_conj_of_normalized` also gives `f(ω y) = ω^{ζ⁻¹}`.  Comparing the two,
`ζ⁻¹ d_N⁻¹ ∈ D` conjugates `ω` to `ω w_N`, hence is trivial by
`eq_one_of_conj_eq_mul_Q0_of_mem_D`.

This is the equation the book's length count is read off from: `d_N` also lies in the
coset `ζ^{N+1}K`, and `K ∩ W = 1` then pins both `N` and the `K`-part. -/
theorem stepFifteen_stop_d_eq_inv (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) {N : ℕ}
    (hstop : y * (hyp.stepElevenSeq ζ y N).1 = 1) :
    (hyp.stepElevenSeq ζ y N).2.2 = ζ⁻¹ := by
  obtain ⟨-, hw, hd⟩ := hyp.stepElevenSeq_mem hζ hyQ0 N
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζ)
  -- the stopping rule says `z_N = y`
  have hzy : (hyp.stepElevenSeq ζ y N).1 = y := by
    have hinv : y⁻¹ = (hyp.stepElevenSeq ζ y N).1 := inv_eq_of_mul_eq_one_right hstop
    have hyy : y⁻¹ = y := by
      have h2 := hyQ0.1
      rw [sq] at h2
      exact inv_eq_of_mul_eq_one_right h2
    rw [← hinv, hyy]
  -- the two readings of `f(ω y)`
  have hspec := hyp.stepElevenSeq_spec H hC2 hζ hωQ hωQ0 hyQ0 hfω N
  rw [hzy] at hspec
  have hswap := hyp.f_mul_eq_conj_of_normalized H hζ hωQ hωQ0 hyQ0 hfω
  -- `ζ⁻¹ d_N⁻¹` fixes the class of `ω`
  have hcD : ζ⁻¹ * ((hyp.stepElevenSeq ζ y N).2.2)⁻¹ ∈ hyp.D :=
    hyp.D.mul_mem (hyp.D.inv_mem hζD) (hyp.D.inv_mem hd)
  have hconj : (ζ⁻¹ * ((hyp.stepElevenSeq ζ y N).2.2)⁻¹)⁻¹ * ω
      * (ζ⁻¹ * ((hyp.stepElevenSeq ζ y N).2.2)⁻¹)
      = ω * (hyp.stepElevenSeq ζ y N).2.1 := by
    calc (ζ⁻¹ * ((hyp.stepElevenSeq ζ y N).2.2)⁻¹)⁻¹ * ω
          * (ζ⁻¹ * ((hyp.stepElevenSeq ζ y N).2.2)⁻¹)
        = (hyp.stepElevenSeq ζ y N).2.2 * (ζ * ω * ζ⁻¹)
            * ((hyp.stepElevenSeq ζ y N).2.2)⁻¹ := by group
      _ = (hyp.stepElevenSeq ζ y N).2.2 * (f (ω * y))
            * ((hyp.stepElevenSeq ζ y N).2.2)⁻¹ := by rw [hswap]
      _ = (hyp.stepElevenSeq ζ y N).2.2 * (((hyp.stepElevenSeq ζ y N).2.2)⁻¹ *
            (ω * (hyp.stepElevenSeq ζ y N).2.1) * (hyp.stepElevenSeq ζ y N).2.2)
            * ((hyp.stepElevenSeq ζ y N).2.2)⁻¹ := by rw [hspec]
      _ = ω * (hyp.stepElevenSeq ζ y N).2.1 := by group
  have hone := hyp.eq_one_of_conj_eq_mul_Q0_of_mem_D M hZ hmu hVW hωQ hωQ0 hcD hw hconj
  have hinv : ((hyp.stepElevenSeq ζ y N).2.2)⁻¹ = ζ := by
    have e : ζ * (ζ⁻¹ * ((hyp.stepElevenSeq ζ y N).2.2)⁻¹) = ζ * 1 := by rw [hone]
    simpa using e
  exact inv_eq_iff_eq_inv.mp hinv

/-- **While the sequence runs, `ζ` has not yet returned to `1`**: if the stopping rule has
not been met before index `N`, then `N + 1 < orderOf ζ`.

`stepElevenSeq_pow_ne_one` says `ζ^{i+1} ≠ 1` for every index `i` the sequence reaches;
were `orderOf ζ ≤ N + 1`, the index `orderOf ζ − 1` would be one of them. -/
theorem lt_orderOf_of_not_stopped (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) {N : ℕ}
    (hns : ∀ i < N, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1) :
    N + 1 < orderOf ζ := by
  by_contra hcon
  have hpos : 0 < orderOf ζ := orderOf_pos ζ
  refine hyp.stepElevenSeq_pow_ne_one H hC2 hζ hωQ hωQ0 hyQ0 hfω (orderOf ζ - 1)
    (fun i hi => hns i (by omega)) ?_
  rw [Nat.sub_add_cancel hpos]
  exact pow_orderOf_eq_one ζ

/-- **The length of the sequence** (Peterfalvi Part II, p. 126, step (15)): with `N` the
first index at which the recursion of (11) stops,

  `N + 2 = orderOf ζ`  and  the `K`-part of `d_N` is trivial.

In the book's indexing (shifted by one, and with `ζ` a generator of `W`, so
`orderOf ζ = m`) these are `m₁ = m − 1` and `c_{m₁} = α`.

`stepElevenSeq_coset` writes `d_N = ζ^{N+1}k` and `stepFifteen_stop_d_eq_inv` says
`d_N = ζ⁻¹`; the resulting `k ζ^{N+2} = 1` splits by `K ∩ W = 1`, and
`lt_orderOf_of_not_stopped` supplies the inequality that turns `ζ^{N+2} = 1` into an
equality of exponents. -/
theorem stepFifteen_length_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) {N : ℕ}
    (hns : ∀ i < N, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hstop : y * (hyp.stepElevenSeq ζ y N).1 = 1) :
    N + 2 = orderOf ζ ∧
      ∀ k ∈ hyp.K, (hyp.stepElevenSeq ζ y N).2.2 = ζ ^ (N + 1) * k → k = 1 := by
  obtain ⟨k, hkK, hk⟩ := hyp.stepElevenSeq_coset hζ hyQ0 N hns
  have hdinv := hyp.stepFifteen_stop_d_eq_inv H hC2 M hZ hmu hVW hζ hωQ hωQ0 hyQ0 hfω hstop
  have hle : N + 1 + 1 ≤ orderOf ζ :=
    hyp.lt_orderOf_of_not_stopped H hC2 hζ hωQ hωQ0 hyQ0 hfω hns
  -- `k ζ^{N+2} = 1`
  have hprod : ∀ l ∈ hyp.K, (hyp.stepElevenSeq ζ y N).2.2 = ζ ^ (N + 1) * l →
      l * ζ ^ (N + 1 + 1) = 1 := by
    intro l hlK hl
    have hcomm : l * ζ = ζ * l := hyp.commute_of_mem_W_of_mem_K hζ hlK
    have hc : Commute l ζ := hcomm
    have hcp : l * ζ ^ (N + 1) = ζ ^ (N + 1) * l := (hc.pow_right (N + 1)).eq
    have he : ζ ^ (N + 1) * l = ζ⁻¹ := by rw [← hl, hdinv]
    calc l * ζ ^ (N + 1 + 1) = (l * ζ ^ (N + 1)) * ζ := by rw [pow_succ]; group
      _ = (ζ ^ (N + 1) * l) * ζ := by rw [hcp]
      _ = ζ⁻¹ * ζ := by rw [he]
      _ = 1 := inv_mul_cancel ζ
  refine ⟨?_, fun l hlK hl => (hyp.stepFifteen_length (m := orderOf ζ) hζ hlK
    (hprod l hlK hl) rfl hle).2⟩
  exact (hyp.stepFifteen_length (m := orderOf ζ) hζ hkK (hprod k hkK hk) rfl hle).1

/-- **The cosets `ζ^{i+1}K` are distinct for distinct exponents**: if `ζ^{i+1}k_i` and
`ζ^{j+1}k_j` agree with `k_i, k_j ∈ K` and `j ≤ i`, then `ζ^{i−j} = 1`.

This is `K ∩ W = 1` again (`eq_one_of_mul_eq_one_of_mem_K_of_mem_W`), with `ζ`
centralizing `K` so that the two parts separate. -/
theorem pow_sub_eq_one_of_coset_eq {ζ ki kj : G} (hζ : ζ ∈ hyp.W)
    (hki : ki ∈ hyp.K) (hkj : kj ∈ hyp.K) {i j : ℕ} (hle : j ≤ i)
    (heq : ζ ^ (i + 1) * ki = ζ ^ (j + 1) * kj) : ζ ^ (i - j) = 1 := by
  have hcomm : ∀ l ∈ hyp.K, ∀ n : ℕ, l * ζ ^ n = ζ ^ n * l := by
    intro l hl n
    have hc : Commute l ζ := hyp.commute_of_mem_W_of_mem_K hζ hl
    exact (hc.pow_right n).eq
  have hsplit : ζ ^ (i + 1) = ζ ^ (j + 1) * ζ ^ (i - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hkk : ki * kj⁻¹ ∈ hyp.K := hyp.K.mul_mem hki (hyp.K.inv_mem hkj)
  have h1 : ζ ^ (i - j) * (ki * kj⁻¹) = 1 := by
    refine mul_left_cancel (a := ζ ^ (j + 1)) ?_
    rw [mul_one]
    calc ζ ^ (j + 1) * (ζ ^ (i - j) * (ki * kj⁻¹))
        = (ζ ^ (j + 1) * ζ ^ (i - j) * ki) * kj⁻¹ := by group
      _ = (ζ ^ (i + 1) * ki) * kj⁻¹ := by rw [← hsplit]
      _ = (ζ ^ (j + 1) * kj) * kj⁻¹ := by rw [heq]
      _ = ζ ^ (j + 1) := by group
  refine (hyp.eq_one_of_mul_eq_one_of_mem_K_of_mem_W hkk (hyp.W.pow_mem hζ _) ?_).2
  rw [hcomm _ hkk (i - j)]
  exact h1

/-- **The entries of the sequence are pairwise distinct** (Peterfalvi Part II, p. 126,
step (15)): the map `i ↦ z_i` is injective on the indices the sequence actually reaches.

If `z_i = z_j` then the invariant of (11) presents the same element `f(ω z_i)` as
`(ω w_i)^{d_i}` and as `(ω w_j)^{d_j}`, so `d_i d_j⁻¹ ∈ D` conjugates `ω w_i` into
`ω w_j` — a translate of itself modulo `Q₀`.  Freeness of the `D`-action
(`eq_one_of_conj_eq_mul_Q0_of_mem_D`) makes it trivial, so `d_i = d_j`; and the cosets
`ζ^{i+1}K` of `stepElevenSeq_coset` are distinct for distinct `i` because `K ∩ W = 1` and
`ζ` has order larger than the range of indices (`lt_orderOf_of_not_stopped`). -/
theorem stepElevenSeq_fst_injOn (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ) {N : ℕ}
    (hns : ∀ i < N, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1) :
    Set.InjOn (fun i => (hyp.stepElevenSeq ζ y i).1) (Set.Iio (N + 1)) := by
  have hord : N + 1 < orderOf ζ :=
    hyp.lt_orderOf_of_not_stopped H hC2 hζ hωQ hωQ0 hyQ0 hfω hns
  -- equal entries force equal conjugators
  have hdd : ∀ i j : ℕ, (hyp.stepElevenSeq ζ y i).1 = (hyp.stepElevenSeq ζ y j).1 →
      (hyp.stepElevenSeq ζ y i).2.2 = (hyp.stepElevenSeq ζ y j).2.2 := by
    intro i j hij
    obtain ⟨-, hwi, hdi⟩ := hyp.stepElevenSeq_mem hζ hyQ0 i
    obtain ⟨-, hwj, hdj⟩ := hyp.stepElevenSeq_mem hζ hyQ0 j
    have hspeci := hyp.stepElevenSeq_spec H hC2 hζ hωQ hωQ0 hyQ0 hfω i
    have hspecj := hyp.stepElevenSeq_spec H hC2 hζ hωQ hωQ0 hyQ0 hfω j
    rw [hij] at hspeci
    obtain ⟨hωiQ, hωiQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hwi
    have hcD : (hyp.stepElevenSeq ζ y i).2.2 * ((hyp.stepElevenSeq ζ y j).2.2)⁻¹ ∈ hyp.D :=
      hyp.D.mul_mem hdi (hyp.D.inv_mem hdj)
    have hconj : ((hyp.stepElevenSeq ζ y i).2.2 * ((hyp.stepElevenSeq ζ y j).2.2)⁻¹)⁻¹
        * (ω * (hyp.stepElevenSeq ζ y i).2.1)
        * ((hyp.stepElevenSeq ζ y i).2.2 * ((hyp.stepElevenSeq ζ y j).2.2)⁻¹)
        = (ω * (hyp.stepElevenSeq ζ y i).2.1) *
            (((hyp.stepElevenSeq ζ y i).2.1)⁻¹ * (hyp.stepElevenSeq ζ y j).2.1) := by
      calc ((hyp.stepElevenSeq ζ y i).2.2 * ((hyp.stepElevenSeq ζ y j).2.2)⁻¹)⁻¹
            * (ω * (hyp.stepElevenSeq ζ y i).2.1)
            * ((hyp.stepElevenSeq ζ y i).2.2 * ((hyp.stepElevenSeq ζ y j).2.2)⁻¹)
          = (hyp.stepElevenSeq ζ y j).2.2 * (((hyp.stepElevenSeq ζ y i).2.2)⁻¹
              * (ω * (hyp.stepElevenSeq ζ y i).2.1) * (hyp.stepElevenSeq ζ y i).2.2)
              * ((hyp.stepElevenSeq ζ y j).2.2)⁻¹ := by group
        _ = (hyp.stepElevenSeq ζ y j).2.2 * (f (ω * (hyp.stepElevenSeq ζ y j).1))
              * ((hyp.stepElevenSeq ζ y j).2.2)⁻¹ := by rw [hspeci]
        _ = (hyp.stepElevenSeq ζ y j).2.2 * (((hyp.stepElevenSeq ζ y j).2.2)⁻¹
              * (ω * (hyp.stepElevenSeq ζ y j).2.1) * (hyp.stepElevenSeq ζ y j).2.2)
              * ((hyp.stepElevenSeq ζ y j).2.2)⁻¹ := by rw [hspecj]
        _ = (ω * (hyp.stepElevenSeq ζ y i).2.1) *
              (((hyp.stepElevenSeq ζ y i).2.1)⁻¹ * (hyp.stepElevenSeq ζ y j).2.1) := by
            group
    have hone := hyp.eq_one_of_conj_eq_mul_Q0_of_mem_D M hZ hmu hVW hωiQ hωiQ0 hcD
      (hyp.Q0.mul_mem (hyp.Q0.inv_mem hwi) hwj) hconj
    exact mul_inv_eq_one.mp hone
  -- distinct indices give distinct cosets `ζ^{i+1}K`
  intro i hi j hj hij
  simp only [Set.mem_Iio] at hi hj
  have hij' : (hyp.stepElevenSeq ζ y i).1 = (hyp.stepElevenSeq ζ y j).1 := hij
  have hdeq := hdd i j hij'
  obtain ⟨ki, hkiK, hki⟩ := hyp.stepElevenSeq_coset hζ hyQ0 i (fun l hl => hns l (by omega))
  obtain ⟨kj, hkjK, hkj⟩ := hyp.stepElevenSeq_coset hζ hyQ0 j (fun l hl => hns l (by omega))
  rw [hki, hkj] at hdeq
  -- reduce to `ζ^{i-j} = 1` after conjugating the `K`-parts together
  rcases le_total j i with hle | hle
  · have hdvd := orderOf_dvd_of_pow_eq_one
      (hyp.pow_sub_eq_one_of_coset_eq hζ hkiK hkjK hle hdeq)
    rcases Nat.eq_zero_or_pos (i - j) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdvd
      omega
  · have hdvd := orderOf_dvd_of_pow_eq_one
      (hyp.pow_sub_eq_one_of_coset_eq hζ hkjK hkiK hle hdeq.symm)
    rcases Nat.eq_zero_or_pos (j - i) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdvd
      omega

/-- **Step (15)'s exhaustion** (Peterfalvi Part II, p. 126): the set step (8) counts is
exactly the set of entries of the sequence of (11).

> the elements `u ∈ F` such that `f(ω(0,u))‾` is in the orbit of `ω̄` are `u₁, …, u_{m−1}`.

The entries lie in that set (`stepElevenSeq_fst_mem_orbitSet`), there are `N + 1` of them
(`stepElevenSeq_fst_injOn`), the length count makes `N + 1 = orderOf ζ − 1`, and step (8)
gives the set exactly `|W| − 1` elements. -/
theorem stepFifteen_exhaust (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W) (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ζ ω y : G} (hζ : ζ ∈ hyp.W) (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hfω : f ω = ζ⁻¹ * (ω * y) * ζ)
    (hWord : orderOf ζ = Nat.card ↥hyp.W) {N : ℕ}
    (hns : ∀ i < N, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1)
    (hstop : y * (hyp.stepElevenSeq ζ y N).1 = 1) :
    (fun i => (hyp.stepElevenSeq ζ y i).1) '' (Set.Iio (N + 1))
      = {x : G | x ∈ hyp.Q0 ∧ ∃ w ∈ hyp.Q0, ∃ a ∈ hyp.D,
          f (ω * x) = a⁻¹ * (ω * w) * a} := by
  classical
  have hlen := (hyp.stepFifteen_length_eq H hC2 M hZ hmu hVW hζ hωQ hωQ0 hyQ0 hfω hns
      hstop).1
  have hinj := hyp.stepElevenSeq_fst_injOn H hC2 M hZ hmu hVW hζ hωQ hωQ0 hyQ0 hfω hns
  have hsub : (fun i => (hyp.stepElevenSeq ζ y i).1) '' (Set.Iio (N + 1))
      ⊆ {x : G | x ∈ hyp.Q0 ∧ ∃ w ∈ hyp.Q0, ∃ a ∈ hyp.D,
          f (ω * x) = a⁻¹ * (ω * w) * a} := by
    rintro _ ⟨i, -, rfl⟩
    exact hyp.stepElevenSeq_fst_mem_orbitSet H hC2 hζ hωQ hωQ0 hyQ0 hfω i
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  have himg : ((fun i => (hyp.stepElevenSeq ζ y i).1) '' (Set.Iio (N + 1))).ncard = N + 1 := by
    rw [Set.InjOn.ncard_image hinj, ← Finset.coe_range, Set.ncard_coe_finset,
      Finset.card_range]
  rw [himg,
    hyp.ncard_eq_card_W_sub_one_of_f_eq_conj_self M hZ H hC2 hVW hm hQ0card hmu hK hWdvd
      hωQ hωQ0]
  omega

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
