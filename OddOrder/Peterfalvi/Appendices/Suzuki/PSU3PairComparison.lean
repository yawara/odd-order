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

* `Hypothesis.f_conj_swap`, `Hypothesis.f_swap_of_pair` — inverting a relation
  `f(x) = y^e`; the second is what lets (19)(b) be (19)(a) with the roles of `ω₁` and
  `ω₂` interchanged.
* `Hypothesis.stepNineteen` — step (19)(a).
* `Hypothesis.stepNineteen_swap` — step (19)(b).
* `Hypothesis.eq_one_of_conj_eq_mul_Q0` — `K` acts freely on `(Q/Q₀)^#`.
* `Hypothesis.inv_conj_t_of_mem_W_mul_KSet` — the `t`-twist on `D = KW` reverses the
  `W`-part and fixes the `K`-part.
* `Hypothesis.eq_and_conj_of_inv_mul_mem_K`, `Hypothesis.eq_and_eq_of_inv_mul_mem_K` —
  what step (7) extracts from the two instances of (19): the book's (∗), (∗∗) and
  (∗∗∗).

What remains of (20) is the indexed family: the sequences `(u_i), (v_i), (d_i)` of (11)
realized in `G`, so that (∗∗∗) can be read at `i = 1` and `i = m − 1`.  The arithmetic
that then closes (20) is `PSU3FieldArithmetic.eq_add_of_add_char_two`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

/-- **Inverting a relation `f(x) = y^e`** (Peterfalvi Part II, pp. 127–128): for `e ∈ D`,

  `f(x) = y^e`  implies  `f(y) = x^{e^{-t}}`.

Applying `f` to `f(x) = y^e` gives `x = f(f(x)) = f(y^e) = f(y)^{e^t}` by (H2) and (H3);
solving for `f(y)` produces the inverse twist `e^{-t} = (t e t)⁻¹`.

Step (20) uses it to turn (19)(a) around — the book's

  `f(ω₁(0, v_i + …)) = (ω₂(0, x₂ + …))^{e_i^{-t}}`

— so that both of the equations fed to step (7) have `ω₁` on the left and `ω₂` on the
right. -/
theorem f_conj_swap (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {x y e : G} (hxQ : x ∈ hyp.Q) (hx1 : x ≠ 1) (hyQ : y ∈ hyp.Q) (hy1 : y ≠ 1)
    (heD : e ∈ hyp.D) (hrel : f x = e⁻¹ * y * e) :
    f y = (hyp.t * e * hyp.t) * x * (hyp.t * e * hyp.t)⁻¹ := by
  obtain ⟨h3, -, -⟩ := hThree hyp.rankOneSetup H hyQ hy1 heD
  have h2 : f (f x) = x := (hTwo hyp.rankOneSetup H hxQ hx1).1
  rw [hrel, h3] at h2
  rw [← h2]
  group

/-- **Interchanging the two representatives** (Peterfalvi Part II, p. 128): if
`f(x) = y^k` with `k ∈ K`, then `f(y) = x^k`, with the *same* `k`.

This is `f_conj_swap` at `e = k ∈ K`, where the twist `k^t` is `k⁻¹`, so that
`x^{k^{-t}}` is again `x^k`.

It is the one line the book spends on step (19)(b): "`f(ω₂(0,x₂))^{k⁻¹} = ω₁(0,x₁)`,
so that `f(ω₂(0,x₂)) = (ω₁(0,x₁))^k`, and so we get (b) on interchanging the roles of
`ω₁` and `ω₂`". -/
theorem f_swap_of_pair (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {x y k : G} (hxQ : x ∈ hyp.Q) (hx1 : x ≠ 1) (hyQ : y ∈ hyp.Q) (hy1 : y ≠ 1)
    (hkK : k ∈ hyp.KSet) (hpair : f x = k⁻¹ * y * k) :
    f y = k⁻¹ * x * k := by
  have hswap := hyp.f_conj_swap H hxQ hx1 hyQ hy1 hkK.1 hpair
  rwa [hkK.2, inv_inv] at hswap

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

/-! ## Step (20): what step (7) extracts from the two instances of (19)

Step (20) feeds the inverted (19)(a) and the plain (19)(b) — two equations of the shape
`f(ω₁ x) = (ω₂ y)^a` — to step (7).  Since the two conjugators lie in the same coset of
`K`, step (7) forces the two arguments `x` to agree, which is the book's (∗); and the
two right-hand sides then agree as well, which pins the conjugators to each other up to
the stabilizer of `ω̄₂` and gives (∗∗∗).  Interchanging `ω₁` and `ω₂` gives (∗∗).
-/

/-- **The two conclusions step (7) yields in step (20)** (Peterfalvi Part II, p. 128).

Given two presentations `f(ω x_j) = (ω' y_j)^{a_j}` with `a₁, a₂` in the same coset of
`K`, step (7) says the arguments coincide — the book's (∗) — and then the two conjugates
of `ω'` coincide too:

  `ω' y₂ = (ω' y₁)^{a₁ a₂⁻¹}`.

The book's (∗∗∗) is the statement that `a₁ a₂⁻¹` is trivial, i.e. that the presentation
`(ω' y)^a` is unique; that is the freeness of the `KW`-action on `(Q/Q₀)^#`, and is what
the standard model supplies.  Everything before it is this lemma. -/
theorem eq_and_conj_of_inv_mul_mem_K (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω ω' x₁ x₂ y₁ y₂ a₁ a₂ : G}
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hx₁ : x₁ ∈ hyp.Q0) (hx₂ : x₂ ∈ hyp.Q0)
    (hy₁ : y₁ ∈ hyp.Q0) (hy₂ : y₂ ∈ hyp.Q0)
    (ha₁ : a₁ ∈ hyp.D) (ha₂ : a₂ ∈ hyp.D)
    (heq₁ : f (ω * x₁) = a₁⁻¹ * (ω' * y₁) * a₁)
    (heq₂ : f (ω * x₂) = a₂⁻¹ * (ω' * y₂) * a₂)
    (hcoset : a₁⁻¹ * a₂ ∈ hyp.K) :
    x₁ = x₂ ∧ ω' * y₂ = (a₁ * a₂⁻¹)⁻¹ * (ω' * y₁) * (a₁ * a₂⁻¹) := by
  have hx : x₁ = x₂ :=
    hyp.eq_of_inv_mul_mem_K H hC2 hωQ hωQ0 hx₁ hx₂ hy₁ hy₂ ha₁ ha₂ heq₁ heq₂ hcoset
  refine ⟨hx, ?_⟩
  rw [hx] at heq₁
  have hEq : a₁⁻¹ * (ω' * y₁) * a₁ = a₂⁻¹ * (ω' * y₂) * a₂ := heq₁.symm.trans heq₂
  calc ω' * y₂ = a₂ * (a₂⁻¹ * (ω' * y₂) * a₂) * a₂⁻¹ := by group
    _ = a₂ * (a₁⁻¹ * (ω' * y₁) * a₁) * a₂⁻¹ := by rw [hEq]
    _ = (a₁ * a₂⁻¹)⁻¹ * (ω' * y₁) * (a₁ * a₂⁻¹) := by group

/-- **`K` acts freely on `(Q/Q₀)^#`** (Peterfalvi Part II, p. 128, behind step (20)'s
(∗∗∗)): a `c ∈ K` fixing the class of some `ω ∈ Q − Q₀` modulo `Q₀` is trivial.

The book reads this off the standard model, where `KW` acts on `Q/Q₀ ≅ E` by
multiplication by `μ(kv)` and `μ` is injective.  It needs no model: by Prop 1(a)
(`Q_inf_centralizer_eq_bot_of_mem_KSet`) a nontrivial `c ∈ K` fixes no nonidentity
element of `Q`, and that already forbids it from fixing a coset of `Q₀`.

Indeed `ψ : z ↦ z · z^c` maps `Q₀` to itself and is injective — if `z ψ` and `z' ψ`
agree then `z z'` is fixed by `c`, using only `z⁻¹ = z` and `(z'^c)² = 1` — hence
surjective, `Q₀` being finite.  So if `ω^c = ω y` with `y ∈ Q₀`, choosing `z` with
`ψ(z) = y` makes `ω z` a nonidentity element of `Q` fixed by `c`. -/
theorem eq_one_of_conj_eq_mul_Q0 {ω c y : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hcK : c ∈ hyp.KSet) (hy : y ∈ hyp.Q0) (hconj : c⁻¹ * ω * c = ω * y) : c = 1 := by
  by_contra hc1
  -- Prop 1(a): a nontrivial element of `K` fixes only `1` in `Q`
  have hfpf : ∀ x ∈ hyp.Q, c⁻¹ * x * c = x → x = 1 := by
    intro x hxQ hfix
    have hcomm : x * c = c * x := by
      calc x * c = (c * (c⁻¹ * x * c)) := by group
        _ = c * x := by rw [hfix]
    have hmem : x ∈ hyp.Q ⊓ Subgroup.centralizer {c} :=
      ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [hyp.Q_inf_centralizer_eq_bot_of_mem_KSet hcK hc1, Subgroup.mem_bot] at hmem
    exact hmem
  -- conjugation by `c` preserves `Q₀`
  have hnorm : ∀ z ∈ hyp.Q0, c⁻¹ * z * c ∈ hyp.Q0 := by
    intro z hz
    have hcD : c ∈ hyp.D := hcK.1
    have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem hcD) hz
    rwa [inv_inv] at hmem
  -- `ψ : z ↦ z · z^c` is injective on `Q₀`, hence surjective
  have hsqinv : ∀ z ∈ hyp.Q0, z⁻¹ = z := by
    intro z hz
    have h2 := hyp.sq_eq_one_of_mem_Q0 hz
    rw [sq] at h2
    exact inv_eq_of_mul_eq_one_right h2
  have hψinj : Function.Injective
      (fun z : ↥hyp.Q0 => (⟨(z : G) * (c⁻¹ * (z : G) * c),
        hyp.Q0.mul_mem z.2 (hnorm _ z.2)⟩ : ↥hyp.Q0)) := by
    intro z z' hzz
    have hz : (z : G) * (c⁻¹ * (z : G) * c) = (z' : G) * (c⁻¹ * (z' : G) * c) :=
      congrArg Subtype.val hzz
    have hconjsq : (c⁻¹ * (z' : G) * c) * (c⁻¹ * (z' : G) * c) = 1 := by
      have h2 := hyp.sq_eq_one_of_mem_Q0 z'.2
      rw [sq] at h2
      calc (c⁻¹ * (z' : G) * c) * (c⁻¹ * (z' : G) * c)
          = c⁻¹ * ((z' : G) * (z' : G)) * c := by group
        _ = 1 := by rw [h2]; group
    have heq : c⁻¹ * (z : G) * c = (z : G) * ((z' : G) * (c⁻¹ * (z' : G) * c)) := by
      calc c⁻¹ * (z : G) * c = (z : G)⁻¹ * ((z : G) * (c⁻¹ * (z : G) * c)) := by group
        _ = (z : G)⁻¹ * ((z' : G) * (c⁻¹ * (z' : G) * c)) := by rw [hz]
        _ = (z : G) * ((z' : G) * (c⁻¹ * (z' : G) * c)) := by rw [hsqinv _ z.2]
    have hfix : c⁻¹ * ((z : G) * (z' : G)) * c = (z : G) * (z' : G) := by
      calc c⁻¹ * ((z : G) * (z' : G)) * c
          = (c⁻¹ * (z : G) * c) * (c⁻¹ * (z' : G) * c) := by group
        _ = ((z : G) * ((z' : G) * (c⁻¹ * (z' : G) * c))) * (c⁻¹ * (z' : G) * c) := by
            rw [heq]
        _ = (z : G) * (z' : G) *
              ((c⁻¹ * (z' : G) * c) * (c⁻¹ * (z' : G) * c)) := by group
        _ = (z : G) * (z' : G) := by rw [hconjsq, mul_one]
    have hone : (z : G) * (z' : G) = 1 :=
      hfpf _ (hyp.Q0_le_Q (hyp.Q0.mul_mem z.2 z'.2)) hfix
    refine Subtype.ext ?_
    calc (z : G) = ((z : G) * (z' : G)) * (z' : G)⁻¹ := by group
      _ = (z' : G) := by rw [hone, hsqinv _ z'.2]; group
  obtain ⟨z, hz⟩ := Finite.surjective_of_injective hψinj ⟨y, hy⟩
  have hzy : (z : G) * (c⁻¹ * (z : G) * c) = y := congrArg Subtype.val hz
  -- `ω z` is a nonidentity element of `Q` fixed by `c`
  obtain ⟨hωzQ, hωzQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 z.2
  have hconjsq : (c⁻¹ * (z : G) * c) * (c⁻¹ * (z : G) * c) = 1 := by
    have h2 := hyp.sq_eq_one_of_mem_Q0 z.2
    rw [sq] at h2
    calc (c⁻¹ * (z : G) * c) * (c⁻¹ * (z : G) * c)
        = c⁻¹ * ((z : G) * (z : G)) * c := by group
      _ = 1 := by rw [h2]; group
  have hfixω : c⁻¹ * (ω * (z : G)) * c = ω * (z : G) := by
    calc c⁻¹ * (ω * (z : G)) * c = (c⁻¹ * ω * c) * (c⁻¹ * (z : G) * c) := by group
      _ = ω * y * (c⁻¹ * (z : G) * c) := by rw [hconj]
      _ = ω * ((z : G) * (c⁻¹ * (z : G) * c)) * (c⁻¹ * (z : G) * c) := by rw [hzy]
      _ = ω * (z : G) * ((c⁻¹ * (z : G) * c) * (c⁻¹ * (z : G) * c)) := by group
      _ = ω * (z : G) := by rw [hconjsq, mul_one]
  have hone : ω * (z : G) = 1 := hfpf _ hωzQ hfixω
  refine hωzQ0 ?_
  rw [hone]
  exact hyp.Q0.one_mem

/-- **The `t`-twist on `D = K W`** (Peterfalvi Part II, p. 128, behind step (20)'s
`e_i^{-t} ∈ e'_{m-i}K`): since `t` centralizes `W` and inverts `K`,

  `(w k)^{-t} = w⁻¹ k`   (`w ∈ W`, `k ∈ K`),

so the twist reverses the `W`-part and leaves the `K`-part alone.

That is what makes the book's `e_i^{-t} ∈ e'_{m-i}K` a statement about `W`-parts only:
by (14) the `W`-part of `e_i` is `ζ^i`, so that of `e_i^{-t}` is `ζ^{-i}`, which by (16)
(`ζ^m = 1`) is the `W`-part `ζ^{m-i}` of `e'_{m-i}`. -/
theorem inv_conj_t_of_mem_W_mul_KSet {w k : G} (hw : w ∈ hyp.W) (hkK : k ∈ hyp.KSet) :
    (hyp.t * (w * k) * hyp.t)⁻¹ = w⁻¹ * k := by
  have htwt : hyp.t * w * hyp.t = w := by
    have hc := hyp.commute_t_of_mem_V (hyp.W_le_V hw)
    rw [← hc.eq, mul_assoc, hyp.rankOneSetup.invol, mul_one]
  have hsplit : hyp.t * (w * k) * hyp.t = w * k⁻¹ := by
    have e : (hyp.t * w * hyp.t) * (hyp.t * k * hyp.t)
        = hyp.t * (w * (hyp.t * hyp.t) * k) * hyp.t := by group
    rw [hyp.rankOneSetup.invol, mul_one] at e
    rw [← e, htwt, hkK.2]
  have hkK' : k ∈ hyp.K := by
    have hx : k ∈ hyp.KSet := hkK
    rw [← hyp.coe_K] at hx
    exact hx
  rw [hsplit, mul_inv_rev, inv_inv]
  exact hyp.commute_of_mem_W_of_mem_K (hyp.W.inv_mem hw) hkK'

/-- **Step (20)'s (∗) and (∗∗∗) together** (Peterfalvi Part II, p. 128).

Two presentations `f(ω x_j) = (ω' y_j)^{a_j}` with `a₁, a₂` in the same coset of `K` are
*identical*: the arguments agree (the book's (∗)), the conjugators agree (its (∗∗∗)),
and hence so do the `y_j`.

Step (7) supplies the first (`eq_and_conj_of_inv_mul_mem_K`) and freeness of the
`K`-action on `(Q/Q₀)^#` the second (`eq_one_of_conj_eq_mul_Q0`).  The commutation
hypothesis is what turns "`a₁⁻¹a₂ ∈ K`" into "`a₁a₂⁻¹ ∈ K`"; it holds where the book
applies this, `D = KW` being abelian under Chapter IV's standing hypothesis `V = W`.

The book's (∗∗) is this same statement with `ω₁` and `ω₂` interchanged. -/
theorem eq_and_eq_of_inv_mul_mem_K (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω ω' x₁ x₂ y₁ y₂ a₁ a₂ : G}
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hω'Q : ω' ∈ hyp.Q) (hω'Q0 : ω' ∉ hyp.Q0)
    (hx₁ : x₁ ∈ hyp.Q0) (hx₂ : x₂ ∈ hyp.Q0)
    (hy₁ : y₁ ∈ hyp.Q0) (hy₂ : y₂ ∈ hyp.Q0)
    (ha₁ : a₁ ∈ hyp.D) (ha₂ : a₂ ∈ hyp.D)
    (heq₁ : f (ω * x₁) = a₁⁻¹ * (ω' * y₁) * a₁)
    (heq₂ : f (ω * x₂) = a₂⁻¹ * (ω' * y₂) * a₂)
    (hcoset : a₁⁻¹ * a₂ ∈ hyp.K) (hcomm : Commute a₁ a₂) :
    x₁ = x₂ ∧ a₁ = a₂ ∧ y₁ = y₂ := by
  obtain ⟨hx, hconj⟩ := hyp.eq_and_conj_of_inv_mul_mem_K H hC2 hωQ hωQ0 hx₁ hx₂ hy₁ hy₂
    ha₁ ha₂ heq₁ heq₂ hcoset
  have hcK : a₁ * a₂⁻¹ ∈ hyp.K := by
    have e : a₁ * a₂⁻¹ = (a₁⁻¹ * a₂)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact hcomm.inv_right.eq
    rw [e]
    exact hyp.K.inv_mem hcoset
  have hcKSet : a₁ * a₂⁻¹ ∈ hyp.KSet := by
    have hx' : a₁ * a₂⁻¹ ∈ (hyp.K : Set G) := hcK
    rwa [hyp.coe_K] at hx'
  have hy1conj : (a₁ * a₂⁻¹)⁻¹ * y₁ * (a₁ * a₂⁻¹) ∈ hyp.Q0 := by
    have hmem := hyp.conj_mem_Q0_of_mem_D (hyp.D.inv_mem (hyp.K_le_D hcK)) hy₁
    rwa [inv_inv] at hmem
  have hω'conj : (a₁ * a₂⁻¹)⁻¹ * ω' * (a₁ * a₂⁻¹)
      = ω' * (y₂ * ((a₁ * a₂⁻¹)⁻¹ * y₁ * (a₁ * a₂⁻¹))⁻¹) := by
    calc (a₁ * a₂⁻¹)⁻¹ * ω' * (a₁ * a₂⁻¹)
        = ((a₁ * a₂⁻¹)⁻¹ * (ω' * y₁) * (a₁ * a₂⁻¹)) *
            ((a₁ * a₂⁻¹)⁻¹ * y₁ * (a₁ * a₂⁻¹))⁻¹ := by group
      _ = (ω' * y₂) * ((a₁ * a₂⁻¹)⁻¹ * y₁ * (a₁ * a₂⁻¹))⁻¹ := by rw [← hconj]
      _ = ω' * (y₂ * ((a₁ * a₂⁻¹)⁻¹ * y₁ * (a₁ * a₂⁻¹))⁻¹) := by group
  have hc1 : a₁ * a₂⁻¹ = 1 :=
    hyp.eq_one_of_conj_eq_mul_Q0 hω'Q hω'Q0 hcKSet
      (hyp.Q0.mul_mem hy₂ (hyp.Q0.inv_mem hy1conj)) hω'conj
  refine ⟨hx, mul_inv_eq_one.mp hc1, ?_⟩
  rw [hc1] at hconj
  simp only [inv_one, one_mul, mul_one] at hconj
  exact (mul_left_cancel hconj).symm

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
