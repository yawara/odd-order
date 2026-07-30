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
* `Hypothesis.not_mem_mul_KSet_of_f_mul_eq_conj` — step (7).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
