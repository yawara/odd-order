/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.RankOneSetup
import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution
import OddOrder.Peterfalvi.Appendices.Suzuki.InvolutionClass
import OddOrder.Peterfalvi.Appendices.Suzuki.QStructure
import OddOrder.Peterfalvi.Appendices.Suzuki.InvertedProduct
import OddOrder.Peterfalvi.Appendices.Suzuki.KCyclic
import OddOrder.Peterfalvi.Appendices.Suzuki.QuotientKWField
import OddOrder.Peterfalvi.Appendices.Suzuki.ModelIsomorphism
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.TConjugateTriple
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.WielandtOnQ

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
* `Hypothesis.f_mem_Q0_of_mem_Q0` and friends — `f` and `g` preserve and reflect `Q₀`.
* `Hypothesis.eq_one_of_f_mul_eq` — step (4).
* `Hypothesis.inv_ne_conj_of_not_mem_Q0`, `Hypothesis.f_ne_conj_of_not_mem_Q0` —
  `j` and `f` act without fixed points on the `D`-orbits of `Q − Q₀`.
* `Hypothesis.ne_one_of_f_eq_conj`, `Hypothesis.not_mem_KSet_of_f_eq_conj` — step (5).
* `Hypothesis.not_mem_KSet_of_f_mul_eq_conj` — step (6).
* `Hypothesis.not_mem_mul_KSet_of_f_mul_eq_conj`, `Hypothesis.eq_of_inv_mul_mem_K` —
  step (7) and its counting form.
* `Hypothesis.index_K_subgroupOf_D` — `|D : K| = |V|`.
* `Hypothesis.ncard_le_card_V_of_f_eq_conj`, `Hypothesis.not_mem_K_of_f_eq_conj_self` —
  step (8)'s bounds `m_i ≤ |V|` and `m₁ ≤ |V| − 1`.
* `Hypothesis.K_inf_W_eq_bot`, `Hypothesis.exists_conj_mul_Q0_iff`,
  `Hypothesis.exists_mem_K_mem_W_mul` — the group-theoretic half of step (8)'s
  translation, including `D = K W` under `V = W`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

/-- `q − 1` and `q + 1` are coprime for `q = 2^m`, `m ≥ 1`: both are odd, and they
differ by `2`.

This is what makes `μ(K) ∩ μ(W) = 1` inside `E^×`: `μ(K)` lies in `F^×`, of order
`q − 1` (`QuotientFieldModel.mu_K_frobFixed`), while `μ(W)` lies in the norm-one
subgroup, of order `q + 1` (`QuotientFieldModel.mu_W_normOne`).  Hence
`|μ(KW)| = |μ(K)| · |μ(W)| = (q − 1) m`, the number behind step (8)'s
`n = (q + 1)/m`. -/
theorem coprime_two_pow_sub_one_two_pow_add_one {m : ℕ} (hm : m ≠ 0) :
    Nat.Coprime (2 ^ m - 1) (2 ^ m + 1) := by
  have hpow : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 hm
  have hle : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h1 := Nat.gcd_dvd_left (2 ^ m - 1) (2 ^ m + 1)
  have h2 := Nat.gcd_dvd_right (2 ^ m - 1) (2 ^ m + 1)
  have hdvd : Nat.gcd (2 ^ m - 1) (2 ^ m + 1) ∣ 2 := by
    have hsub : Nat.gcd (2 ^ m - 1) (2 ^ m + 1) ∣ (2 ^ m + 1) - (2 ^ m - 1) :=
      Nat.dvd_sub h2 h1
    have e : (2 ^ m + 1) - (2 ^ m - 1) = 2 := by omega
    rwa [e] at hsub
  have hodd : ¬ (2 ∣ (2 ^ m - 1)) := by omega
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact h
  · rw [h] at h1
    exact absurd h1 hodd

/-- An element killed by both `q − 1` and `q + 1` is trivial, for `q = 2^m`, `m ≥ 1`.

This is the group-theoretic form of `μ(K) ∩ μ(W) = 1` in `E^×`: an element of `μ(K)`
lies in `F^×` so is killed by `q − 1` (`QuotientFieldModel.mu_K_frobFixed`), and an
element of `μ(W)` is killed by `q + 1` (`QuotientFieldModel.mu_W_normOne`). -/
theorem eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one
    {H : Type*} [Group H] {m : ℕ} (hm : m ≠ 0) {x : H}
    (h1 : x ^ (2 ^ m - 1) = 1) (h2 : x ^ (2 ^ m + 1) = 1) : x = 1 := by
  have d1 : orderOf x ∣ 2 ^ m - 1 := orderOf_dvd_of_pow_eq_one h1
  have d2 : orderOf x ∣ 2 ^ m + 1 := orderOf_dvd_of_pow_eq_one h2
  have hdvd : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd d1 d2
    rwa [coprime_two_pow_sub_one_two_pow_add_one hm] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

/-- The index arithmetic behind step (8)'s `n = (q + 1)/m`:

  `|E^×| / |μ(KW)| = (q² − 1) / ((q − 1) · m) = (q + 1) / m`,

using `q² − 1 = (q − 1)(q + 1)` and cancelling the positive factor `q − 1`. -/
theorem two_pow_sq_sub_one_div {e m : ℕ} (he : e ≠ 0) :
    ((2 ^ e) ^ 2 - 1) / ((2 ^ e - 1) * m) = (2 ^ e + 1) / m := by
  have h2 : (2 : ℕ) ≤ 2 ^ e := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr he)
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ e = r + 1 := ⟨2 ^ e - 1, by omega⟩
  have hrpos : 0 < r := by omega
  rw [hr]
  have hsq : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
  have hone : r + 1 - 1 = r := by omega
  have htwo : r + 1 + 1 = r + 2 := by omega
  rw [hsq, Nat.add_sub_cancel, hone, htwo]
  exact Nat.mul_div_mul_left _ _ hrpos

/-- **The squeeze behind step (8)**.

If `Φ : α → β` has every fibre of size at most `M`, one distinguished fibre of size at
most `M − 1`, and `|α| = |β| · M − 1`, then *all* those bounds are equalities: the
fibre over `b₀` has exactly `M − 1` elements and every other fibre exactly `M`.

This is the book's "whence all the inequalities are in fact equalities" (p. 124), with
`α = Q₀`, `β` the set of `KW`-orbits on `(Q/Q₀)^#`, `M = m = |W|`, and `b₀` the orbit
of `ω̄₁`. -/
theorem card_fiber_eq_of_card_eq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (Φ : α → β) {M : ℕ} (hM : 1 ≤ M) (b₀ : β)
    (hle : ∀ b, (Finset.univ.filter fun a => Φ a = b).card ≤ M)
    (hb₀ : (Finset.univ.filter fun a => Φ a = b₀).card ≤ M - 1)
    (hcard : Fintype.card α = Fintype.card β * M - 1) :
    ∀ b, (Finset.univ.filter fun a => Φ a = b).card = if b = b₀ then M - 1 else M := by
  classical
  set g : β → ℕ := fun b => if b = b₀ then M - 1 else M with hg
  have hpt : ∀ b ∈ (Finset.univ : Finset β),
      (Finset.univ.filter fun a => Φ a = b).card ≤ g b := by
    intro b _
    by_cases h : b = b₀
    · simp only [hg, if_pos h]
      exact h ▸ hb₀
    · simp only [hg, if_neg h]
      exact hle b
  have hsumf : ∑ b : β, (Finset.univ.filter fun a => Φ a = b).card = Fintype.card α := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (Φ a))]
    exact Finset.card_univ
  have hsumg : ∑ b : β, g b = Fintype.card β * M - 1 := by
    have hsplit : ∑ b : β, g b = ∑ b ∈ Finset.univ.erase b₀, g b + g b₀ :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ b₀)).symm
    have hconst : ∀ b ∈ Finset.univ.erase b₀, g b = M := by
      intro b hb
      simp only [hg, if_neg (Finset.ne_of_mem_erase hb)]
    have herase : ∑ b ∈ Finset.univ.erase b₀, g b = (Fintype.card β - 1) * M := by
      rw [Finset.sum_congr rfl hconst, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ b₀), Finset.card_univ, smul_eq_mul]
    rw [hsplit, herase]
    simp only [hg, if_pos rfl]
    have hpos : 1 ≤ Fintype.card β := Fintype.card_pos_iff.mpr ⟨b₀⟩
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card β = k + 1 := ⟨Fintype.card β - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, add_mul, one_mul]
    generalize k * M = t
    omega
  have heq : ∑ b : β, (Finset.univ.filter fun a => Φ a = b).card = ∑ b : β, g b := by
    rw [hsumf, hsumg, hcard]
  exact fun b => (Finset.sum_eq_sum_iff_of_le hpt).mp heq b (Finset.mem_univ b)

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

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

/-! ## `f` and `g` preserve `Q₀`

`Q₀ = (H ∩ I) ∪ {1}` is the set of involutions of `H` together with `1`, and by
`Hypothesis.image_conj_KSet_eq_involutions_H` its nonidentity elements are exactly the
`K`-conjugates `s^k` of the distinguished involution.  Step (1) says `f` and `g` send
`s^k` to `s^{k⁻¹}`, again an involution — so both preserve `Q₀^#`, and being
involutive maps they reflect it as well.

This is the engine of step (4).
-/

/-- Every nonidentity element of `Q₀` is a `K`-conjugate `s^k` of the distinguished
involution (Ch. I; `Hypothesis.image_conj_KSet_eq_involutions_H`). -/
theorem exists_mem_KSet_conj_eq_of_mem_Q0 {z : G} (hzQ0 : z ∈ hyp.Q0) (hz1 : z ≠ 1) :
    ∃ k ∈ hyp.KSet, k⁻¹ * hyp.distinguishedInvolution * k = z := by
  have hmem : z ∈ {x : G | x ^ 2 = 1 ∧ x ≠ 1 ∧ x ∈ hyp.H} := ⟨hzQ0.1, hz1, hzQ0.2⟩
  rw [← hyp.image_conj_KSet_eq_involutions_H hyp.distinguishedInvolution_mem_H
    hyp.distinguishedInvolution_sq hyp.distinguishedInvolution_ne_one] at hmem
  obtain ⟨k, hk, hkz⟩ := hmem
  exact ⟨k, hk, hkz⟩

/-- **`f` maps `Q₀^#` into `Q₀`**: by step (1) it sends `s^k` to `s^{k⁻¹}`. -/
theorem f_mem_Q0_of_mem_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {z : G} (hzQ0 : z ∈ hyp.Q0) (hz1 : z ≠ 1) : f z ∈ hyp.Q0 := by
  obtain ⟨k, hk, rfl⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0 hzQ0 hz1
  rw [(hyp.fgh_at_conj_distinguishedInvolution H hC2 hk).1]
  exact hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H hk.1) hyp.distinguishedInvolution_mem_Q0

/-- **`g` maps `Q₀^#` into `Q₀`**, likewise by step (1). -/
theorem g_mem_Q0_of_mem_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {z : G} (hzQ0 : z ∈ hyp.Q0) (hz1 : z ≠ 1) : g z ∈ hyp.Q0 := by
  obtain ⟨k, hk, rfl⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0 hzQ0 hz1
  rw [(hyp.fgh_at_conj_distinguishedInvolution H hC2 hk).2.1]
  exact hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H hk.1) hyp.distinguishedInvolution_mem_Q0

/-- **`f` reflects `Q₀`**: `f(z) ∈ Q₀ → z ∈ Q₀` for `z ∈ Q^#`, since `f ∘ f = id`. -/
theorem mem_Q0_of_f_mem_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {z : G} (hzQ : z ∈ hyp.Q) (hz1 : z ≠ 1) (hfz : f z ∈ hyp.Q0) : z ∈ hyp.Q0 := by
  have hfz1 : f z ≠ 1 := H.f_ne_one hyp.rankOneSetup hzQ hz1
  have := hyp.f_mem_Q0_of_mem_Q0 H hC2 hfz hfz1
  rwa [(hTwo hyp.rankOneSetup H hzQ hz1).1] at this

/-- **`g` reflects `Q₀`**: `g(z) ∈ Q₀ → z ∈ Q₀` for `z ∈ Q^#`, since `g ∘ g = id`. -/
theorem mem_Q0_of_g_mem_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {z : G} (hzQ : z ∈ hyp.Q) (hz1 : z ≠ 1) (hgz : g z ∈ hyp.Q0) : z ∈ hyp.Q0 := by
  have hgz1 : g z ≠ 1 := H.g_ne_one hyp.rankOneSetup hzQ hz1
  have := hyp.g_mem_Q0_of_mem_Q0 H hC2 hgz hgz1
  rwa [g_involutive hyp.rankOneSetup H hzQ hz1] at this

/-! ## Step (4) -/

/-- **Peterfalvi Part II, Ch. IV §2, step (4)** (p. 123):

> If `f(ωx) = f(ω)y` for some `ω ∈ Q − Q₀` and `x, y ∈ Q₀`, then `x = 1`.

Suppose `x ≠ 1`.  Then `x = s^k` for some `k ∈ K`, and since `Q₀` centralizes `Q` the
hypothesis reads `f(s^k ω) = f(ω) y`.  Comparing with step (3) and solving for the
inner value gives `f(s^{k⁻¹} g(ω)) = (f(ω) y f(ω)⁻¹)^{h(ω)^{-t}}`, which lies in `Q₀`
because `Q₀ ⊴ H`.  As `f` reflects `Q₀`, so does `s^{k⁻¹} g(ω)`, hence `g(ω) ∈ Q₀`;
and as `g` reflects `Q₀` too, `ω ∈ Q₀` — contradiction. -/
theorem eq_one_of_f_mul_eq (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω x y : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hxQ0 : x ∈ hyp.Q0) (hyQ0 : y ∈ hyp.Q0)
    (heq : f (ω * x) = f ω * y) : x = 1 := by
  by_contra hx1
  have hω1 : ω ≠ 1 := fun hc => hωQ0 (hc ▸ hyp.Q0.one_mem)
  obtain ⟨k, hk, rfl⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0 hxQ0 hx1
  -- `Q₀` centralizes `Q`, so `ω` and `s^k` commute
  have hcomm : ω * (k⁻¹ * hyp.distinguishedInvolution * k)
      = (k⁻¹ * hyp.distinguishedInvolution * k) * ω :=
    Subgroup.mem_centralizer_iff.mp
      (hyp.involutions_H_subset_centralizer_Q hxQ0.2 hxQ0.1 hx1) ω hωQ
  have hne : (k⁻¹ * hyp.distinguishedInvolution * k) * ω ≠ 1 := by
    intro hc
    refine hωQ0 ?_
    rw [eq_inv_of_mul_eq_one_right hc]
    exact hyp.Q0.inv_mem hxQ0
  -- step (3), with the hypothesis substituted on the left
  have heq' : f ((k⁻¹ * hyp.distinguishedInvolution * k) * ω) = f ω * y := by
    rw [← hcomm]; exact heq
  have e3 := hyp.f_conj_distinguishedInvolution_mul H hC2 hk hωQ hω1 hne
  rw [heq'] at e3
  -- solve for the inner value
  have hZeq : f ((k * hyp.distinguishedInvolution * k⁻¹) * g ω)
      = (hyp.t * h ω * hyp.t) * (f ω * y * (f ω)⁻¹) * (hyp.t * h ω * hyp.t)⁻¹ := by
    rw [e3]; group
  -- it lies in `Q₀`, because `Q₀ ⊴ H`
  have hbH : hyp.t * h ω * hyp.t ∈ hyp.H :=
    hyp.D_le_H (hyp.rankOneSetup.Dstab _ (H.h_mem hωQ hω1))
  have hZQ0 : f ((k * hyp.distinguishedInvolution * k⁻¹) * g ω) ∈ hyp.Q0 := by
    rw [hZeq]
    exact hyp.conj_mem_Q0_of_mem_H hbH
      (hyp.conj_mem_Q0_of_mem_H (hyp.Q_le_H (H.f_mem hωQ hω1)) hyQ0)
  -- ... hence so does its argument, hence `g ω`, hence `ω`
  have hkS : k * hyp.distinguishedInvolution * k⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H hk.1) hyp.distinguishedInvolution_mem_Q0
  have hargQ : (k * hyp.distinguishedInvolution * k⁻¹) * g ω ∈ hyp.Q :=
    hyp.Q.mul_mem (hyp.Q0_le_Q hkS) (H.g_mem hωQ hω1)
  have harg1 : (k * hyp.distinguishedInvolution * k⁻¹) * g ω ≠ 1 := by
    intro hc
    refine hωQ0 (hyp.mem_Q0_of_g_mem_Q0 H hC2 hωQ hω1 ?_)
    rw [eq_inv_of_mul_eq_one_right hc]
    exact hyp.Q0.inv_mem hkS
  have hargQ0 : (k * hyp.distinguishedInvolution * k⁻¹) * g ω ∈ hyp.Q0 :=
    hyp.mem_Q0_of_f_mem_Q0 H hC2 hargQ harg1 hZQ0
  refine hωQ0 (hyp.mem_Q0_of_g_mem_Q0 H hC2 hωQ hω1 ?_)
  have e : g ω = (k * hyp.distinguishedInvolution * k⁻¹)⁻¹ *
      ((k * hyp.distinguishedInvolution * k⁻¹) * g ω) := by group
  rw [e]
  exact hyp.Q0.mul_mem (hyp.Q0.inv_mem hkS) hargQ0

/-- `Q − Q₀` is stable under right multiplication by `Q₀`.

Used throughout step (8): `ω₁ x` stays in `Q − Q₀` as `x` ranges over `Q₀`, so
`f(ω₁ x)` is defined and again lies in `Q − Q₀`. -/
theorem mul_mem_sdiff_Q0 {ω z : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hz : z ∈ hyp.Q0) : ω * z ∈ hyp.Q ∧ ω * z ∉ hyp.Q0 := by
  refine ⟨hyp.Q.mul_mem hωQ (hyp.Q0_le_Q hz), fun hcc => hωQ0 ?_⟩
  have e : ω = (ω * z) * z⁻¹ := by group
  rw [e]
  exact hyp.Q0.mul_mem hcc (hyp.Q0.inv_mem hz)

/-- **`f` maps `Q − Q₀` into `Q − Q₀`** (positive form of `mem_Q0_of_f_mem_Q0`).

Step (8) needs this to know that `f(ω₁ x)` really has a nontrivial image in `Q/Q₀`,
so that it lies in exactly one `D`-orbit of `(Q/Q₀)^#` and the counts `m_i` sum to
`|Q₀|`. -/
theorem f_mem_sdiff_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {x : G} (hxQ : x ∈ hyp.Q) (hxQ0 : x ∉ hyp.Q0) :
    f x ∈ hyp.Q ∧ f x ∉ hyp.Q0 := by
  have hx1 : x ≠ 1 := fun hc => hxQ0 (hc ▸ hyp.Q0.one_mem)
  exact ⟨H.f_mem hxQ hx1, fun hcc => hxQ0 (hyp.mem_Q0_of_f_mem_Q0 H hC2 hxQ hx1 hcc)⟩

/-- **`g` maps `Q − Q₀` into `Q − Q₀`**, likewise. -/
theorem g_mem_sdiff_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {x : G} (hxQ : x ∈ hyp.Q) (hxQ0 : x ∉ hyp.Q0) :
    g x ∈ hyp.Q ∧ g x ∉ hyp.Q0 := by
  have hx1 : x ≠ 1 := fun hc => hxQ0 (hc ▸ hyp.Q0.one_mem)
  exact ⟨H.g_mem hxQ hx1, fun hcc => hxQ0 (hyp.mem_Q0_of_g_mem_Q0 H hC2 hxQ hx1 hcc)⟩

/-! ## Step (5): no fixed points on the `D`-orbits of `Q − Q₀` -/

/-- **`j : x ↦ x⁻¹` has no fixed point on the `D`-orbits of `Q − Q₀`.**

If `ω⁻¹ = ω^d` with `d ∈ D`, then `d²` centralizes `ω`; since `|D|` is odd, `d` is a
power of `d²`, so `d` itself centralizes `ω` and `ω⁻¹ = ω`, i.e. `ω ∈ Q₀`. -/
theorem inv_ne_conj_of_not_mem_Q0 {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    {d : G} (hd : d ∈ hyp.D) : ω⁻¹ ≠ d⁻¹ * ω * d := by
  intro hc
  -- `d²` centralizes `ω`
  have hsq : (d ^ 2)⁻¹ * ω * d ^ 2 = ω := by
    have e1 : (d ^ 2)⁻¹ * ω * d ^ 2 = d⁻¹ * (d⁻¹ * ω * d) * d := by rw [sq]; group
    rw [e1, ← hc]
    have e2 : d⁻¹ * ω⁻¹ * d = (d⁻¹ * ω * d)⁻¹ := by group
    rw [e2, ← hc, inv_inv]
  have hcomm2 : d ^ 2 * ω = ω * d ^ 2 := by
    have e : d ^ 2 * ((d ^ 2)⁻¹ * ω * d ^ 2) = ω * d ^ 2 := by group
    rwa [hsq] at e
  -- `|D|` odd, so `d` is a power of `d²`
  have hpow : (d ^ 2) ^ ((Nat.card hyp.D + 1) / 2) = d :=
    invertedBy.pow_half_sq hyp.D_odd hd
  have hcomm2' : Commute (d ^ 2) ω := hcomm2
  have hcd : Commute d ω := by
    rw [← hpow]
    exact hcomm2'.pow_left _
  have hdω : d⁻¹ * ω * d = ω := by
    rw [mul_assoc, ← hcd.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hdω] at hc
  refine hωQ0 ⟨?_, hyp.Q_le_H hωQ⟩
  rw [sq]
  nth_rewrite 1 [← hc]
  exact inv_mul_cancel ω

/-- **`f` has no fixed point on the `D`-orbits of `Q − Q₀`** either.

In the permutation group induced by `⟨f, j⟩` on these orbits one has
`f = (f ∘ j)⁻¹ ∘ j ∘ (f ∘ j)`, so `f` is conjugate to `j`.  Concretely: if
`f(ω) = ω^d` then applying `g` gives `g(ω)^{d^t} = g(f(ω)) = (g(ω)⁻¹)^{h(ω)}` by (H3)
and (H2), so `g(ω)⁻¹ = g(ω)^e` with `e = d^t h(ω)⁻¹ ∈ D` — a fixed point of `j` at
`g(ω)`, which lies in `Q − Q₀` because `g` reflects `Q₀`. -/
theorem f_ne_conj_of_not_mem_Q0 (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    {d : G} (hd : d ∈ hyp.D) : f ω ≠ d⁻¹ * ω * d := by
  intro hc
  have hω1 : ω ≠ 1 := fun hcc => hωQ0 (hcc ▸ hyp.Q0.one_mem)
  have hgQ : g ω ∈ hyp.Q := H.g_mem hωQ hω1
  have hgQ0 : g ω ∉ hyp.Q0 := fun hcc =>
    hωQ0 (hyp.mem_Q0_of_g_mem_Q0 H hC2 hωQ hω1 hcc)
  have hbD : hyp.t * d * hyp.t ∈ hyp.D := hyp.rankOneSetup.Dstab d hd
  have hhD : h ω ∈ hyp.D := H.h_mem hωQ hω1
  -- the two evaluations of `g` at `f(ω) = ω^d`
  have e1 : g (d⁻¹ * ω * d) = (hyp.t * d * hyp.t)⁻¹ * g ω * (hyp.t * d * hyp.t) :=
    (hThree hyp.rankOneSetup H hωQ hω1 hd).2.1
  have e2 : g (f ω) = (h ω)⁻¹ * (g ω)⁻¹ * h ω :=
    (hTwo hyp.rankOneSetup H hωQ hω1).2.1
  rw [hc, e1] at e2
  -- read off a `j`-fixed point at `g ω`
  refine hyp.inv_ne_conj_of_not_mem_Q0 hgQ hgQ0
    (hyp.D.mul_mem hbD (hyp.D.inv_mem hhD)) ?_
  have e3 : ((hyp.t * d * hyp.t) * (h ω)⁻¹)⁻¹ * g ω * ((hyp.t * d * hyp.t) * (h ω)⁻¹)
      = h ω * ((hyp.t * d * hyp.t)⁻¹ * g ω * (hyp.t * d * hyp.t)) * (h ω)⁻¹ := by
    group
  rw [e3, e2]
  group

/-- **Peterfalvi Part II, Ch. IV §2, step (5)**, first half (p. 124): if
`f(ω) = (ωy)^a` with `ω ∈ Q − Q₀`, `y ∈ Q₀` and `a ∈ D`, then `y ≠ 1`.

Otherwise `f` would fix the `D`-orbit of `ω`. -/
theorem ne_one_of_f_eq_conj (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω y a : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (haD : a ∈ hyp.D)
    (heq : f ω = a⁻¹ * (ω * y) * a) : y ≠ 1 := by
  intro hy1
  refine hyp.f_ne_conj_of_not_mem_Q0 H hC2 hωQ hωQ0 haD ?_
  rw [heq, hy1, mul_one]

/-- **Peterfalvi Part II, Ch. IV §2, step (5)**, second half (p. 124): in the same
situation, `a ∉ K`.

The book computes, by (H2) and (H3),

  `f(ωy) = ω^{a^{-t}} = (f(ω)^{a⁻¹} y)^{a^{-t}} = (f(ω) y^a)^{a⁻¹ a^{-t}}`

and concludes from (4) that `a⁻¹ a^{-t} ≠ 1`.  Here the contrapositive is taken
directly: if `a ∈ K` then `a^t = a⁻¹`, so the twist `a⁻¹ a^{-t}` is trivial, the
displayed identity collapses to `f(ωy) = f(ω) y^a`, and (4) forces `y = 1` — against
the first half. -/
theorem not_mem_KSet_of_f_eq_conj (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω y a : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hyQ0 : y ∈ hyp.Q0)
    (haD : a ∈ hyp.D) (heq : f ω = a⁻¹ * (ω * y) * a) : a ∉ hyp.KSet := by
  intro haK
  have hy1 : y ≠ 1 := hyp.ne_one_of_f_eq_conj H hC2 hωQ hωQ0 haD heq
  have hω1 : ω ≠ 1 := fun hcc => hωQ0 (hcc ▸ hyp.Q0.one_mem)
  have hyQ : y ∈ hyp.Q := hyp.Q0_le_Q hyQ0
  have hωyQ : ω * y ∈ hyp.Q := hyp.Q.mul_mem hωQ hyQ
  have hωy1 : ω * y ≠ 1 := by
    intro hcc
    refine hωQ0 ?_
    rw [eq_inv_of_mul_eq_one_left hcc]
    exact hyp.Q0.inv_mem hyQ0
  -- apply `f` to the hypothesis: (H2) on the left, (H3) on the right
  have hfω : f (f ω) = ω := (hTwo hyp.rankOneSetup H hωQ hω1).1
  have hstep : f (a⁻¹ * (ω * y) * a)
      = (hyp.t * a * hyp.t)⁻¹ * f (ω * y) * (hyp.t * a * hyp.t) :=
    (hThree hyp.rankOneSetup H hωyQ hωy1 haD).1
  rw [heq, hstep, haK.2] at hfω
  have hfωy : f (ω * y) = a⁻¹ * ω * a := by
    have e : a⁻¹ * (a⁻¹⁻¹ * f (ω * y) * a⁻¹) * a = f (ω * y) := by group
    rw [hfω] at e
    exact e.symm
  -- rewrite `ω` using the hypothesis and `y² = 1`
  have hω : ω = a * f ω * a⁻¹ * y := by
    rw [heq]
    have e : a * (a⁻¹ * (ω * y) * a) * a⁻¹ * y = ω * (y * y) := by group
    rw [e, ← sq, hyQ0.1, mul_one]
  have hgoal : f (ω * y) = f ω * (a⁻¹ * y * a) := by
    rw [hfωy]
    have e : a⁻¹ * (a * f ω * a⁻¹ * y) * a = f ω * (a⁻¹ * y * a) := by group
    rw [← hω] at e
    exact e
  -- step (4) now forces `y = 1`
  have hyaQ0 : a⁻¹ * y * a ∈ hyp.Q0 := by
    have := hyp.conj_mem_Q0_of_mem_H (hyp.H.inv_mem (hyp.D_le_H haD)) hyQ0
    rwa [inv_inv] at this
  exact hy1 (hyp.eq_one_of_f_mul_eq H hC2 hωQ hωQ0 hyQ0 hyaQ0 hgoal)

/-! ## Step (6) -/

/-- Elements of `K` commute: `K` is cyclic (`Hypothesis.K_isCyclic`). -/
theorem commute_of_mem_K {a b : G} (ha : a ∈ hyp.K) (hb : b ∈ hyp.K) : a * b = b * a := by
  haveI := hyp.K_isCyclic
  letI : CommGroup ↥hyp.K := IsCyclic.commGroup
  exact congrArg (Subtype.val (p := fun z => z ∈ hyp.K))
    (mul_comm (⟨a, ha⟩ : ↥hyp.K) ⟨b, hb⟩)

/-- `K` is closed under `a, k ↦ a k²`: `t`-inversion is multiplicative here because
`a` and `k²` commute inside the cyclic group `K`.  This is what turns step (6)'s
`a k² ∉ K` into `a ∉ K`. -/
theorem mul_sq_mem_KSet {a k : G} (ha : a ∈ hyp.KSet) (hk : k ∈ hyp.KSet) :
    a * k ^ 2 ∈ hyp.KSet := by
  refine ⟨hyp.D.mul_mem ha.1 (hyp.D.pow_mem hk.1 2), ?_⟩
  have hinvol : hyp.t * hyp.t = 1 := hyp.rankOneSetup.invol
  have e1 : hyp.t * (a * k ^ 2) * hyp.t
      = (hyp.t * a * hyp.t) * (hyp.t * k * hyp.t) * (hyp.t * k * hyp.t) := by
    have e : (hyp.t * a * hyp.t) * (hyp.t * k * hyp.t) * (hyp.t * k * hyp.t)
        = hyp.t * a * (hyp.t * hyp.t) * k * (hyp.t * hyp.t) * k * hyp.t := by group
    rw [e, hinvol, sq]
    group
  have haK : a ∈ hyp.K := Subgroup.subset_closure ha
  have hkK : k ∈ hyp.K := Subgroup.subset_closure hk
  have hc : a⁻¹ * k⁻¹ = k⁻¹ * a⁻¹ :=
    hyp.commute_of_mem_K (hyp.K.inv_mem haK) (hyp.K.inv_mem hkK)
  rw [e1, ha.2, hk.2, mul_inv_rev, sq, mul_inv_rev]
  calc a⁻¹ * k⁻¹ * k⁻¹ = (k⁻¹ * a⁻¹) * k⁻¹ := by rw [hc]
    _ = k⁻¹ * (a⁻¹ * k⁻¹) := by group
    _ = k⁻¹ * (k⁻¹ * a⁻¹) := by rw [hc]
    _ = k⁻¹ * k⁻¹ * a⁻¹ := by group

/-- **Peterfalvi Part II, Ch. IV §2, step (6)** (p. 124):

> If `f(ωx) = (f(ω)y)^a` for some `ω ∈ Q − Q₀`, `x, y ∈ Q₀`, `x ≠ 1`, and `a ∈ D`,
> then `a ∉ K`.

Write `x = s^k` with `k ∈ K` and `u = s^{k⁻¹}`.  Step (2) evaluates `f(ωx)`, and
solving for the inner value turns the hypothesis into

  `f(f(ω)u) = ((f(ω)u) · y')^{a k²}`,  `y' = u y u^{a⁻¹} ∈ Q₀`,

which is exactly the shape of step (5) at `f(ω)u ∈ Q − Q₀`.  Hence `a k² ∉ K`, and
`mul_sq_mem_KSet` upgrades that to `a ∉ K`. -/
theorem not_mem_KSet_of_f_mul_eq_conj (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω x y a : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hxQ0 : x ∈ hyp.Q0) (hx1 : x ≠ 1) (hyQ0 : y ∈ hyp.Q0) (haD : a ∈ hyp.D)
    (heq : f (ω * x) = a⁻¹ * (f ω * y) * a) : a ∉ hyp.KSet := by
  intro haK
  have hω1 : ω ≠ 1 := fun hcc => hωQ0 (hcc ▸ hyp.Q0.one_mem)
  obtain ⟨k, hk, hxk⟩ := hyp.exists_mem_KSet_conj_eq_of_mem_Q0 hxQ0 hx1
  -- `u = s^{k⁻¹}` is an involution of `Q₀`
  have huQ0 : k * hyp.distinguishedInvolution * k⁻¹ ∈ hyp.Q0 :=
    hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H hk.1) hyp.distinguishedInvolution_mem_Q0
  have huu : (k * hyp.distinguishedInvolution * k⁻¹) *
      (k * hyp.distinguishedInvolution * k⁻¹) = 1 := by
    have := huQ0.1; rwa [sq] at this
  -- step (2)
  have hne : ω * (k⁻¹ * hyp.distinguishedInvolution * k) ≠ 1 := by
    intro hcc
    refine hωQ0 ?_
    rw [eq_inv_of_mul_eq_one_left hcc, hxk]
    exact hyp.Q0.inv_mem hxQ0
  have h2 := hyp.f_mul_conj_distinguishedInvolution H hC2 hk hωQ hω1 hne
  rw [hxk, heq] at h2
  -- solve for the inner value
  have hsolve : f (f ω * (k * hyp.distinguishedInvolution * k⁻¹))
      = (k ^ 2)⁻¹ * (a⁻¹ * (f ω * y) * a * (k * hyp.distinguishedInvolution * k⁻¹)) *
        ((k⁻¹) ^ 2)⁻¹ := by
    rw [h2]
    have e : (k ^ 2)⁻¹ * ((k ^ 2 * f (f ω * (k * hyp.distinguishedInvolution * k⁻¹)) *
          (k⁻¹) ^ 2 * (k * hyp.distinguishedInvolution * k⁻¹)) *
          (k * hyp.distinguishedInvolution * k⁻¹)) * ((k⁻¹) ^ 2)⁻¹
        = (k ^ 2)⁻¹ * (k ^ 2 * f (f ω * (k * hyp.distinguishedInvolution * k⁻¹)) *
          (k⁻¹) ^ 2 * ((k * hyp.distinguishedInvolution * k⁻¹) *
          (k * hyp.distinguishedInvolution * k⁻¹))) * ((k⁻¹) ^ 2)⁻¹ := by group
    rw [e, huu]
    group
  -- put it in the shape of step (5)
  have hZ : f (f ω * (k * hyp.distinguishedInvolution * k⁻¹))
      = (a * k ^ 2)⁻¹ *
        ((f ω * (k * hyp.distinguishedInvolution * k⁻¹)) *
          ((k * hyp.distinguishedInvolution * k⁻¹) * y *
            (a * (k * hyp.distinguishedInvolution * k⁻¹) * a⁻¹))) *
        (a * k ^ 2) := by
    rw [hsolve]
    have e2 : (a * k ^ 2)⁻¹ *
        ((f ω * (k * hyp.distinguishedInvolution * k⁻¹)) *
          ((k * hyp.distinguishedInvolution * k⁻¹) * y *
            (a * (k * hyp.distinguishedInvolution * k⁻¹) * a⁻¹))) * (a * k ^ 2)
        = (k ^ 2)⁻¹ * (a⁻¹ * (f ω * ((k * hyp.distinguishedInvolution * k⁻¹) *
            (k * hyp.distinguishedInvolution * k⁻¹)) * y) * a *
            (k * hyp.distinguishedInvolution * k⁻¹)) * ((k⁻¹) ^ 2)⁻¹ := by
      group
    rw [e2, huu]
    group
  -- apply step (5)
  have hωuQ : f ω * (k * hyp.distinguishedInvolution * k⁻¹) ∈ hyp.Q :=
    hyp.Q.mul_mem (H.f_mem hωQ hω1) (hyp.Q0_le_Q huQ0)
  have hωuQ0 : f ω * (k * hyp.distinguishedInvolution * k⁻¹) ∉ hyp.Q0 := by
    intro hcc
    refine hωQ0 (hyp.mem_Q0_of_f_mem_Q0 H hC2 hωQ hω1 ?_)
    have e : f ω = (f ω * (k * hyp.distinguishedInvolution * k⁻¹)) *
        (k * hyp.distinguishedInvolution * k⁻¹)⁻¹ := by group
    rw [e]
    exact hyp.Q0.mul_mem hcc (hyp.Q0.inv_mem huQ0)
  have hy'Q0 : (k * hyp.distinguishedInvolution * k⁻¹) * y *
      (a * (k * hyp.distinguishedInvolution * k⁻¹) * a⁻¹) ∈ hyp.Q0 :=
    hyp.Q0.mul_mem (hyp.Q0.mul_mem huQ0 hyQ0)
      (hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H haD) huQ0)
  have hak2 : a * k ^ 2 ∉ hyp.KSet :=
    hyp.not_mem_KSet_of_f_eq_conj H hC2 hωuQ hωuQ0 hy'Q0
      (hyp.D.mul_mem haD (hyp.D.pow_mem hk.1 2)) hZ
  exact hak2 (hyp.mul_sq_mem_KSet haK hk)

/-! ## Step (7) -/

/-- **Peterfalvi Part II, Ch. IV §2, step (7)** (p. 124):

> Let `ω, ω' ∈ Q − Q₀` and let `x_i, y_i ∈ Q₀` and `a_i ∈ D` (`i = 1, 2`) be such that
> `x₁ ≠ x₂` and `f(ω x_i) = (ω' y_i)^{a_i}`.  Then `a₂ ∉ a₁ K`.

Eliminating `ω'` between the two hypotheses gives

  `f(ω x₂) = (f(ω x₁)^{a₁⁻¹} y₁ y₂)^{a₂} = (f(ω x₁) (y₁y₂)^{a₁})^{a₁⁻¹ a₂}`,

which is step (6) at `ω x₁ ∈ Q − Q₀` with `x = x₁⁻¹ x₂ ≠ 1` — note
`(ω x₁)(x₁⁻¹ x₂) = ω x₂`.  Hence `a₁⁻¹ a₂ ∉ K`. -/
theorem not_mem_mul_KSet_of_f_mul_eq_conj (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω ω' x₁ x₂ y₁ y₂ a₁ a₂ : G}
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hx₁ : x₁ ∈ hyp.Q0) (hx₂ : x₂ ∈ hyp.Q0) (hxne : x₁ ≠ x₂)
    (hy₁ : y₁ ∈ hyp.Q0) (hy₂ : y₂ ∈ hyp.Q0)
    (ha₁ : a₁ ∈ hyp.D) (ha₂ : a₂ ∈ hyp.D)
    (heq₁ : f (ω * x₁) = a₁⁻¹ * (ω' * y₁) * a₁)
    (heq₂ : f (ω * x₂) = a₂⁻¹ * (ω' * y₂) * a₂) :
    a₁⁻¹ * a₂ ∉ hyp.KSet := by
  have hωx₁Q : ω * x₁ ∈ hyp.Q := hyp.Q.mul_mem hωQ (hyp.Q0_le_Q hx₁)
  have hωx₁Q0 : ω * x₁ ∉ hyp.Q0 := by
    intro hcc
    refine hωQ0 ?_
    have e : ω = (ω * x₁) * x₁⁻¹ := by group
    rw [e]
    exact hyp.Q0.mul_mem hcc (hyp.Q0.inv_mem hx₁)
  have hx'Q0 : x₁⁻¹ * x₂ ∈ hyp.Q0 := hyp.Q0.mul_mem (hyp.Q0.inv_mem hx₁) hx₂
  have hx'1 : x₁⁻¹ * x₂ ≠ 1 := fun hcc => hxne (inv_mul_eq_one.mp hcc)
  have hy'Q0 : a₁⁻¹ * (y₁ * y₂) * a₁ ∈ hyp.Q0 := by
    have := hyp.conj_mem_Q0_of_mem_H (hyp.H.inv_mem (hyp.D_le_H ha₁))
      (hyp.Q0.mul_mem hy₁ hy₂)
    rwa [inv_inv] at this
  have hy₁sq : y₁ * y₁ = 1 := by have := hy₁.1; rwa [sq] at this
  -- eliminate `ω'`
  have hkey : f ((ω * x₁) * (x₁⁻¹ * x₂))
      = (a₁⁻¹ * a₂)⁻¹ * (f (ω * x₁) * (a₁⁻¹ * (y₁ * y₂) * a₁)) * (a₁⁻¹ * a₂) := by
    have hprod : (ω * x₁) * (x₁⁻¹ * x₂) = ω * x₂ := by group
    rw [hprod, heq₂, heq₁]
    have e : (a₁⁻¹ * a₂)⁻¹ *
          ((a₁⁻¹ * (ω' * y₁) * a₁) * (a₁⁻¹ * (y₁ * y₂) * a₁)) * (a₁⁻¹ * a₂)
        = a₂⁻¹ * (ω' * (y₁ * y₁) * y₂) * a₂ := by group
    rw [e, hy₁sq]
    group
  exact hyp.not_mem_KSet_of_f_mul_eq_conj H hC2 hωx₁Q hωx₁Q0 hx'Q0 hx'1 hy'Q0
    (hyp.D.mul_mem (hyp.D.inv_mem ha₁) ha₂) hkey

/-! ## Towards step (8): the index of `K` in `D`

Step (8) counts, for each `KW`-orbit on `(Q/Q₀)^#`, how many `x ∈ Q₀` send
`f(ω₁ x)` into it.  Step (7) says distinct `x` produce elements `a ∈ D` lying in
**distinct cosets of `K`**, so the count is bounded by `|D : K|`.

By the inverted-product decomposition `|D| = |C_D(t)| · |K| = |V| · |K|`, that index
is `|V|` — and `|V| = |W| = m` under Chapter IV's standing hypothesis `V = W`, which
is what makes the book's bound read `m_i ≤ m`.
-/

/-- `|K| = |KSet|`: the subgroup `K` generated by `KSet` has `KSet` as its carrier. -/
theorem card_K_eq_ncard_KSet : Nat.card ↥hyp.K = hyp.KSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← hyp.coe_K]
  rfl

/-- **`|D| = |V| · |K|`** (Peterfalvi Part II, Ch. I §2, Lemma (a)): the inverted
product decomposition of an odd-order subgroup normalized by an involution. -/
theorem card_D_eq_card_V_mul_card_K :
    Nat.card ↥hyp.D = Nat.card ↥hyp.V * Nat.card ↥hyp.K := by
  rw [hyp.card_K_eq_ncard_KSet]
  exact card_eq_card_centralizer_mul_ncard_invertedBy hyp.rankOneSetup.invol
    hyp.D_odd hyp.rankOneSetup.Dstab

/-- **`|D : K| = |V|`** — the number of cosets of `K` in `D`.

Under Chapter IV's standing hypothesis `V = W` this is `|W| = m`, the bound step (8)
needs. -/
theorem index_K_subgroupOf_D : (hyp.K.subgroupOf hyp.D).index = Nat.card ↥hyp.V := by
  have hcard : Nat.card ↥(hyp.K.subgroupOf hyp.D) = Nat.card ↥hyp.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.K_le_D).toEquiv
  have hmul := (hyp.K.subgroupOf hyp.D).index_mul_card
  rw [hcard, hyp.card_D_eq_card_V_mul_card_K] at hmul
  have hKpos : 0 < Nat.card ↥hyp.K := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hKpos hmul

/-- **The counting form of step (7)**: for fixed `ω, ω' ∈ Q − Q₀`, two elements
`x₁, x₂ ∈ Q₀` whose associated `a₁, a₂ ∈ D` lie in the *same* coset of `K` must be
equal.

Equivalently, `x ↦ a_x K` is injective on the set of `x ∈ Q₀` admitting such a
presentation, so at most `|D : K| = |V|` of them occur — the bound behind step (8)'s
`m_i ≤ m`. -/
theorem eq_of_inv_mul_mem_K (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω ω' x₁ x₂ y₁ y₂ a₁ a₂ : G}
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hx₁ : x₁ ∈ hyp.Q0) (hx₂ : x₂ ∈ hyp.Q0)
    (hy₁ : y₁ ∈ hyp.Q0) (hy₂ : y₂ ∈ hyp.Q0)
    (ha₁ : a₁ ∈ hyp.D) (ha₂ : a₂ ∈ hyp.D)
    (heq₁ : f (ω * x₁) = a₁⁻¹ * (ω' * y₁) * a₁)
    (heq₂ : f (ω * x₂) = a₂⁻¹ * (ω' * y₂) * a₂)
    (hcoset : a₁⁻¹ * a₂ ∈ hyp.K) : x₁ = x₂ := by
  by_contra hxne
  have hmem : a₁⁻¹ * a₂ ∈ hyp.KSet := by
    have h : a₁⁻¹ * a₂ ∈ (hyp.K : Set G) := hcoset
    rwa [hyp.coe_K] at h
  exact hyp.not_mem_mul_KSet_of_f_mul_eq_conj H hC2 hωQ hωQ0 hx₁ hx₂ hxne hy₁ hy₂
    ha₁ ha₂ heq₁ heq₂ hmem

/-- **The bound behind step (8)**: for fixed `ω, ω' ∈ Q − Q₀`, at most `|D : K| = |V|`
elements `x ∈ Q₀` satisfy `f(ω x) = (ω' y)^a` for some `y ∈ Q₀` and `a ∈ D`.

Choosing such an `a` for each `x` and passing to its coset in `D/K` gives an injection
by `eq_of_inv_mul_mem_K`, which is step (7).

Under Chapter IV's standing hypothesis `V = W` this reads `≤ |W| = m`, the book's
`m_i ≤ m`; the case `i = 1` sharpens it to `m − 1` via step (5). -/
theorem ncard_le_card_V_of_f_eq_conj (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω ω' : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    {x : G | x ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
        f (ω * x) = a⁻¹ * (ω' * y) * a}.ncard ≤ Nat.card ↥hyp.V := by
  classical
  set S : Set G := {x : G | x ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
    f (ω * x) = a⁻¹ * (ω' * y) * a} with hSdef
  have key : ∀ x ∈ S, ∃ a, a ∈ hyp.D ∧ ∃ b, b ∈ hyp.Q0 ∧
      f (ω * x) = a⁻¹ * (ω' * b) * a := by
    rintro x ⟨-, b, hb, a, ha, heq⟩
    exact ⟨a, ha, b, hb, heq⟩
  choose! A hAD B hBQ0 hAeq using key
  -- lift the chosen `a` into `D`
  set A' : G → ↥hyp.D := fun x => if h : A x ∈ hyp.D then ⟨A x, h⟩ else 1 with hA'def
  have hA'val : ∀ x ∈ S, (A' x : G) = A x := by
    intro x hx
    simp only [hA'def, dif_pos (hAD x hx)]
  have hinj : Set.InjOn
      (fun x => (QuotientGroup.mk (A' x) : ↥hyp.D ⧸ hyp.K.subgroupOf hyp.D)) S := by
    intro x₁ hx₁ x₂ hx₂ hxy
    have hmem : (A' x₁)⁻¹ * A' x₂ ∈ hyp.K.subgroupOf hyp.D :=
      QuotientGroup.eq.mp hxy
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmem' : (A x₁)⁻¹ * A x₂ ∈ hyp.K := by
      have e : (((A' x₁)⁻¹ * A' x₂ : ↥hyp.D) : G) = (A x₁)⁻¹ * A x₂ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hA'val x₁ hx₁, hA'val x₂ hx₂]
      rwa [e] at hmem
    exact hyp.eq_of_inv_mul_mem_K H hC2 hωQ hωQ0 hx₁.1 hx₂.1
      (hBQ0 x₁ hx₁) (hBQ0 x₂ hx₂) (hAD x₁ hx₁) (hAD x₂ hx₂)
      (hAeq x₁ hx₁) (hAeq x₂ hx₂) hmem'
  have hbound := Set.ncard_le_ncard_of_injOn
    (fun x => (QuotientGroup.mk (A' x) : ↥hyp.D ⧸ hyp.K.subgroupOf hyp.D))
    (fun _ _ => Set.mem_univ _) hinj Set.finite_univ
  rwa [Set.ncard_univ, ← Subgroup.index_eq_card, hyp.index_K_subgroupOf_D] at hbound

/-- **The sharpening for `i = 1`**: when `ω' = ω`, the element `a` can never lie in
`K`.  This is what turns the bound `m₁ ≤ m` into `m₁ ≤ m − 1`.

If `a ∈ K` then `a^t = a⁻¹`, so applying `f` to `f(ωx) = (ωy)^a` and using (H2), (H3)
gives the *symmetric* relation `f(ωy) = (ωx)^a` with the **same** `a`.  Step (7) then
forces `x = y` (else `a ∉ aK`, absurd), whence `f(ωx) = (ωx)^a` — that is, `f` fixes
the `D`-orbit of `ωx ∈ Q − Q₀`, contradicting `f_ne_conj_of_not_mem_Q0`. -/
theorem not_mem_K_of_f_eq_conj_self (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω x y a : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hxQ0 : x ∈ hyp.Q0) (hyQ0 : y ∈ hyp.Q0) (haD : a ∈ hyp.D)
    (heq : f (ω * x) = a⁻¹ * (ω * y) * a) : a ∉ hyp.K := by
  intro haK
  have haKSet : a ∈ hyp.KSet := by
    have h : a ∈ (hyp.K : Set G) := haK
    rwa [hyp.coe_K] at h
  -- `ω x` and `ω y` lie in `Q − Q₀`
  obtain ⟨hωxQ, hωxQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hxQ0
  obtain ⟨hωyQ, hωyQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hyQ0
  have hωx1 : ω * x ≠ 1 := fun hcc => hωxQ0 (hcc ▸ hyp.Q0.one_mem)
  have hωy1 : ω * y ≠ 1 := fun hcc => hωyQ0 (hcc ▸ hyp.Q0.one_mem)
  -- apply `f`: (H2) on the left, (H3) on the right, and `a^t = a⁻¹`
  have hff : f (f (ω * x)) = ω * x := (hTwo hyp.rankOneSetup H hωxQ hωx1).1
  have hstep : f (a⁻¹ * (ω * y) * a)
      = (hyp.t * a * hyp.t)⁻¹ * f (ω * y) * (hyp.t * a * hyp.t) :=
    (hThree hyp.rankOneSetup H hωyQ hωy1 haD).1
  rw [heq, hstep, haKSet.2] at hff
  have hsym : f (ω * y) = a⁻¹ * (ω * x) * a := by
    have e : a⁻¹ * (a⁻¹⁻¹ * f (ω * y) * a⁻¹) * a = f (ω * y) := by group
    rw [hff] at e
    exact e.symm
  -- step (7) forces `x = y`
  have hxy : x = y :=
    hyp.eq_of_inv_mul_mem_K H hC2 hωQ hωQ0 hxQ0 hyQ0 hyQ0 hxQ0 haD haD heq hsym
      (by simp)
  -- ... and then `f` fixes the `D`-orbit of `ω x`
  rw [hxy] at heq
  exact hyp.f_ne_conj_of_not_mem_Q0 H hC2 hωyQ hωyQ0 haD heq

/-! ## Translating "lies in the orbit modulo `Q₀`"

Step (8) speaks of `f(ω₁ x)` lying, *modulo `Q₀`*, in the `KW`-orbit of `ω_i`.  The
lemmas above instead consume the shape `f(ω₁ x) = (ω_i y)^a` with `y ∈ Q₀`, `a ∈ D`.
The two agree because `D` normalizes `Q₀`, which is pure group theory; what still
needs the standard model is only the identification of the `KW`-action on `Q/Q₀` with
`D`-conjugacy, for which `D = KW` — and that follows from `K ∩ W = 1` together with
Chapter IV's `V = W`, since `|D| = |V| · |K|`.
-/

/-- `K ∩ W = 1`: an element of `K` is inverted by `t` and an element of `W ≤ C_D(t)`
is centralized by it, so a common element squares to `1` — impossible in the
odd-order group `D`. -/
theorem K_inf_W_eq_bot : hyp.K ⊓ hyp.W = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxW⟩
  have hxD : x ∈ hyp.D := hyp.K_le_D hxK
  -- `t x t = x⁻¹` from `K`
  have hinv : hyp.t * x * hyp.t = x⁻¹ := by
    have h : x ∈ (hyp.K : Set G) := hxK
    rw [hyp.coe_K] at h
    exact h.2
  -- `t x t = x` from `W ≤ C_D(t)`
  have hfix : hyp.t * x * hyp.t = x := by
    have hxV : x ∈ hyp.V := hxW.1
    have hcent : x ∈ Subgroup.centralizer ({hyp.t} : Set G) := hxV.2
    have hcomm : hyp.t * x = x * hyp.t :=
      (Subgroup.mem_centralizer_singleton_iff.mp hcent).symm
    rw [hcomm, mul_assoc, hyp.rankOneSetup.invol, mul_one]
  have hsq : x ^ 2 = 1 := by
    have hxx : x = x⁻¹ := hfix.symm.trans hinv
    rw [sq]
    nth_rewrite 1 [hxx]
    exact inv_mul_cancel x
  -- odd order forces `x = 1`
  have hodd : Odd (orderOf x) := invertedBy.odd_orderOf_of_mem hyp.D_odd hxD
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h)
  · exact absurd (h ▸ hodd) (by decide)

/-- The two shapes agree: `z` is congruent modulo `Q₀` to a `D`-conjugate of `ω'`
exactly when `z = (ω' y)^a` for some `y ∈ Q₀` and `a ∈ D`. -/
theorem exists_conj_mul_Q0_iff {ω' z : G} :
    (∃ a ∈ hyp.D, ∃ w ∈ hyp.Q0, z = a⁻¹ * ω' * a * w)
      ↔ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D, z = a⁻¹ * (ω' * y) * a := by
  constructor
  · rintro ⟨a, ha, w, hw, rfl⟩
    refine ⟨a * w * a⁻¹, hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H ha) hw, a, ha, by group⟩
  · rintro ⟨y, hy, a, ha, rfl⟩
    refine ⟨a, ha, a⁻¹ * y * a, ?_, by group⟩
    have := hyp.conj_mem_Q0_of_mem_H (hyp.H.inv_mem (hyp.D_le_H ha)) hy
    rwa [inv_inv] at this

/-- **`D = K W`** under Chapter IV's standing hypothesis `V = W`.

`K ∩ W = 1` makes `(k, w) ↦ k w` injective from `K × W` into `D`, and
`|K| · |W| = |K| · |V| = |D|` makes it surjective.  This is what identifies the
`KW`-orbits of step (8) with `D`-conjugacy classes modulo `Q₀`. -/
theorem exists_mem_K_mem_W_mul (hVW : hyp.V = hyp.W) {d : G} (hd : d ∈ hyp.D) :
    ∃ k ∈ hyp.K, ∃ w ∈ hyp.W, d = k * w := by
  classical
  have hWD : hyp.W ≤ hyp.D := le_trans inf_le_left hyp.V_le_D
  set F : ↥hyp.K × ↥hyp.W → ↥hyp.D := fun p =>
    ⟨(p.1 : G) * (p.2 : G), hyp.D.mul_mem (hyp.K_le_D p.1.2) (hWD p.2.2)⟩ with hFdef
  have hinj : Function.Injective F := by
    rintro ⟨⟨k₁, hk₁⟩, ⟨w₁, hw₁⟩⟩ ⟨⟨k₂, hk₂⟩, ⟨w₂, hw₂⟩⟩ hEq
    have hval : k₁ * w₁ = k₂ * w₂ := congrArg Subtype.val hEq
    have hmem : k₂⁻¹ * k₁ ∈ hyp.K ⊓ hyp.W := by
      refine ⟨hyp.K.mul_mem (hyp.K.inv_mem hk₂) hk₁, ?_⟩
      have e : k₂⁻¹ * k₁ = w₂ * w₁⁻¹ := by
        calc k₂⁻¹ * k₁ = k₂⁻¹ * (k₁ * w₁) * w₁⁻¹ := by group
          _ = k₂⁻¹ * (k₂ * w₂) * w₁⁻¹ := by rw [hval]
          _ = w₂ * w₁⁻¹ := by group
      rw [e]
      exact hyp.W.mul_mem hw₂ (hyp.W.inv_mem hw₁)
    rw [hyp.K_inf_W_eq_bot, Subgroup.mem_bot] at hmem
    have hk : k₁ = k₂ := (inv_mul_eq_one.mp hmem).symm
    subst hk
    have hw : w₁ = w₂ := mul_left_cancel hval
    subst hw
    rfl
  have hcard : Nat.card (↥hyp.K × ↥hyp.W) = Nat.card ↥hyp.D := by
    rw [Nat.card_prod, hyp.card_D_eq_card_V_mul_card_K, hVW, mul_comm]
  have hbij : Function.Bijective F :=
    (Nat.bijective_iff_injective_and_card F).mpr ⟨hinj, hcard⟩
  obtain ⟨p, hp⟩ := hbij.2 ⟨d, hd⟩
  exact ⟨(p.1 : G), p.1.2, (p.2 : G), p.2.2, (congrArg Subtype.val hp).symm⟩

/-! ## The scalar group `μ(KW)` inside `E^×`

Step (8) counts the `KW`-orbits on `(Q/Q₀)^# ≅ E^×`, i.e. the index of `μ(KW)` in
`E^×`.  The two containments recorded in `QuotientFieldModel` — `μ(K) ⊆ F^×` and
`μ(W)` in the norm-one subgroup — pin its order down to `(q − 1) · |W|`.
-/

/-- `μ(k)^{q−1} = 1`: `μ(K)` lies in `F^× = 𝐅_q^×`
(`QuotientFieldModel.mu_K_frobFixed` says `μ(k)^q = μ(k)`). -/
theorem mu_K_pow_two_pow_sub_one {m : ℕ} (M : hyp.QuotientFieldModel m)
    (k : ↥hyp.actualKActor) : M.mu (k, 1) ^ (2 ^ m - 1) = 1 := by
  have hfix : M.mu (k, 1) ^ (2 ^ m) = M.mu (k, 1) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact M.mu_K_frobFixed k
  have hle : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have e : (2 : ℕ) ^ m = 1 + (2 ^ m - 1) := by omega
  rw [e, pow_add, pow_one] at hfix
  have h2 : M.mu (k, 1) * M.mu (k, 1) ^ (2 ^ m - 1) = M.mu (k, 1) * 1 := by
    rw [mul_one]; exact hfix
  exact mul_left_cancel h2

/-- **`|K| = q − 1`**: `μ` maps `K` bijectively onto `F^× = 𝐅_q^×`.

Injectivity is `QuotientFieldModel.mu_K_injective`; surjectivity is
`exists_actualKActor_mu_eq`; and `|F| = q` is
`OddOrder.FiniteField.natCard_frobFixedSubfield`. -/
theorem card_actualKActor_eq {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m) (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) :
    Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
  classical
  set f : ↥hyp.actualKActor → M.E := fun k => ((M.mu (k, 1) : M.Eˣ) : M.E) with hf
  have hinj : Function.Injective f := fun k k' h => M.mu_K_injective (Units.ext h)
  have hrange : Set.range f
      = ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E) \ {0}) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨k, rfl⟩
      exact ⟨OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed k),
        Units.ne_zero _⟩
    · rintro a ⟨haF, ha0⟩
      obtain ⟨k, hk⟩ := hyp.exists_actualKActor_mu_eq s M hm hQ0card haF
        (by simpa using ha0)
      exact ⟨k, hk⟩
  have hcardF : ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E)).ncard
      = 2 ^ m := by
    rw [← Nat.card_coe_set_eq]
    exact OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm
  have hT : ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E) \ {0}).ncard
      = 2 ^ m - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem
      (OddOrder.FiniteField.frobFixedSubfield M.E 2 m).zero_mem, hcardF]
  have hcard : Nat.card ↥hyp.actualKActor = (Set.range f).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_range_of_injective hinj).symm
  rw [hcard, hrange, hT]

/-- **`μ(K) ∩ μ(W) = 1`**: a common value is killed by both `q − 1` and `q + 1`, which
are coprime. -/
theorem mu_K_eq_mu_W_imp_eq_one {m : ℕ} (hm : m ≠ 0) (M : hyp.QuotientFieldModel m)
    {k : ↥hyp.actualKActor} {v : ↥hyp.W} (heq : M.mu (k, 1) = M.mu (1, v)) :
    M.mu (k, 1) = 1 :=
  eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one hm
    (hyp.mu_K_pow_two_pow_sub_one M k)
    (by rw [heq]; exact M.mu_W_normOne v)

/-- **The number of `KW`-orbits on `(Q/Q₀)^#` is `n = (q + 1)/|W|`.**

Since `KW` acts on `Q/Q₀ ≅ E` by scalars, its orbits on `E^×` are the cosets of the
subgroup `μ(KW) ≤ E^×`, so their number is the index of that subgroup.  Its order is
`|K| · |W| = (q − 1)|W|` (by injectivity of `μ`), and `|E^×| = q² − 1`. -/
theorem index_range_mu {m : ℕ} (hm : m ≠ 0) (M : hyp.QuotientFieldModel m)
    (hinj : Function.Injective M.mu)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1) :
    (MonoidHom.range M.mu).index = (2 ^ m + 1) / Nat.card ↥hyp.W := by
  classical
  haveI : Fintype M.E := Fintype.ofFinite _
  have hrange : Nat.card ↥(MonoidHom.range M.mu)
      = (2 ^ m - 1) * Nat.card ↥hyp.W := by
    have e1 : Nat.card (↥hyp.actualKActor × ↥hyp.W) = Nat.card ↥(MonoidHom.range M.mu) :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [← e1, Nat.card_prod, hK]
  have hunits : Nat.card M.Eˣ = (2 ^ m) ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, M.card]
  have hidx := (MonoidHom.range M.mu).index_mul_card
  rw [hrange, hunits] at hidx
  have hpos : 0 < (2 ^ m - 1) * Nat.card ↥hyp.W := by
    have h2 : (2 : ℕ) ≤ 2 ^ m := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
    have hW : 0 < Nat.card ↥hyp.W := Nat.card_pos
    have h1 : 0 < 2 ^ m - 1 := by omega
    exact Nat.mul_pos h1 hW
  rw [← two_pow_sq_sub_one_div (e := m) (m := Nat.card ↥hyp.W) hm]
  rw [← hidx, Nat.mul_div_cancel _ hpos]

/-- The coordinate of an element of `Q − Q₀` is a **nonzero** element of `E`.

`coord` is an additive isomorphism `Q/Z(Q) ≃+ E`, and under `Z(Q) = Q₀` (the
`LemmaFiveSetup` hypothesis) an element of `Q` has trivial image in the quotient
exactly when it lies in `Q₀`.  This is what lets step (8) send `x ∈ Q₀` to a *unit*
of `E`, hence to a coset of `μ(KW)`. -/
theorem coord_ne_zero_of_not_mem_Q0 {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z : G} (hzQ : z ∈ hyp.Q) (hzQ0 : z ∉ hyp.Q0) :
    M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) ≠ 0 := by
  intro hc
  refine hzQ0 ?_
  have hzero : (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) = 0 :=
    (AddEquiv.map_eq_zero_iff M.coord).mp hc
  have hone : (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q) :
      ↥hyp.Q ⧸ Subgroup.center hyp.Q) = 1 := hzero
  have hmem : (⟨z, hzQ⟩ : ↥hyp.Q) ∈ Subgroup.center hyp.Q :=
    QuotientGroup.eq_one_iff _ |>.mp hone
  rw [hZ, Subgroup.mem_subgroupOf] at hmem
  exact hmem

/-- **The map of step (8)**: `x ∈ Q₀ ↦` the `μ(KW)`-coset of the coordinate of
`f(ω x)`.

Well-defined because `ω x` and hence `f(ω x)` stay in `Q − Q₀`
(`mul_mem_sdiff_Q0`, `f_mem_sdiff_Q0`), so the coordinate is a nonzero element of `E`
(`coord_ne_zero_of_not_mem_Q0`), i.e. a unit.  Its class modulo `μ(KW)` is exactly the
`KW`-orbit the book refers to, because `KW` acts by scalars. -/
noncomputable def orbitOfF {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) :
    M.Eˣ ⧸ (MonoidHom.range M.mu) :=
  let hx := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 x.2
  let hfx := hyp.f_mem_sdiff_Q0 H hC2 hx.1 hx.2
  QuotientGroup.mk (Units.mk0 _ (hyp.coord_ne_zero_of_not_mem_Q0 M hZ hfx.1 hfx.2))

/-- **`conjQHom kv` is conjugation by an element of `D`.**

`actualKActor` is the range of `conjQByK`, and both `conjQByK k` and `conjQByW v` are
literally `x ↦ k x k⁻¹` and `x ↦ v x v⁻¹`; composing them gives conjugation by `k v`,
which lies in `D` since `K ≤ D` and `W ≤ V ≤ D`.

This is what turns the `KW`-orbit of step (8) into a `D`-conjugacy class, so that
`exists_conj_mul_Q0_iff` applies. -/
theorem exists_mem_D_conjQHom (kv : ↥hyp.actualKActor × ↥hyp.W) :
    ∃ d ∈ hyp.D, ∀ x : ↥hyp.Q,
      ((hyp.conjQHom kv x : ↥hyp.Q) : G) = d * (x : G) * d⁻¹ := by
  obtain ⟨k, hk⟩ := (MonoidHom.mem_range).mp kv.1.2
  have hWD : hyp.W ≤ hyp.D := le_trans inf_le_left hyp.V_le_D
  refine ⟨(k : G) * (kv.2 : G),
    hyp.D.mul_mem (hyp.K_le_D k.2) (hWD kv.2.2), fun x => ?_⟩
  rw [hyp.conjQHom_apply, MulAut.mul_apply]
  simp only [Subgroup.coe_subtype]
  rw [← hk]
  change (k : G) * ((kv.2 : G) * (x : G) * (kv.2 : G)⁻¹) * (k : G)⁻¹ = _
  group

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
