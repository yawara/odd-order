/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3StepEighteen
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3StepTwenty

/-!
# The `KW`-orbits of `Q/Q₀`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, pp. 124–129.

Throughout §2 the book fixes representatives `ω_1, …, ω_n` of the orbits of `KW` on
`(Q/Q₀)^#` and indexes everything by them; the closing Proposition (p. 129) ends with

> whence `i = k` and `ω_i² = (0, α)`,

which is *only* the statement that `ω_i` and `ω_k` represent **distinct** orbits unless
`i = k`.  This file introduces that orbit relation directly, so no indexed family is
needed: `x` and `y` are related when their images in `Q/Q₀` lie in one `D`-orbit
(`D = KW` by §1).

`barOrbitRel` is the relation `y ∈ (x Q₀)^D`.  It is an equivalence relation because `D`
normalizes `Q₀` (`conj_mem_Q0_of_mem_H`), and it is what `stepNine` preserves: the
normalized element it produces is `c⁻¹ (ω z) c` with `z ∈ Q₀` and `c ∈ K`, so it lies in
the orbit of `ω` — the book's "`ω̄'_i` is in the orbit of `ω̄_i` under `KW`".

## Main results

* `Hypothesis.barOrbitRel` — the relation, with `refl` / `symm` / `trans` and
  `Hypothesis.barOrbitSetoid`.
* `Hypothesis.barOrbitRel.mem_Q`, `Hypothesis.barOrbitRel.notMem_Q0` — the relation stays
  inside `Q − Q₀`.
* `Hypothesis.barOrbitRel_of_stepNine` — §2 (9) produces a normalized element *of the same
  orbit*.
* `Hypothesis.exists_normalizedOrbitRep` — the normalized transversal, i.e. the book's
  `ω_1, …, ω_n` as an orbit-invariant map.
* `Hypothesis.not_dOrbitRel_self_mul_Q0` — freeness of the `D`-action, in the shape used.
* `Hypothesis.dOrbitRel_of_stepTwenty_degenerate`,
  `Hypothesis.dOrbitRel_of_stepTwenty_degenerate_one` — the two degenerate cases of
  step (20), each of which puts a `Q₀`-translate of `ω'` in the orbit of `ω z`.
* `Hypothesis.dOrbitRel_mul_of_barOrbitRel` — step (20)'s precise form
  `f(ω z) = (ω'(z y))^d` from mere orbit membership.
* `Hypothesis.y_eq_of_barOrbitRel` — step (20)'s first assertion `α₁ = α₂` in the same
  setting.
* `Hypothesis.exists_f_eq_conj_inv` — **§2's closing Proposition** (p. 129):
  `∃ ω ∈ Q − Q₀`, `ω² = y` and `f(ω) = (ω⁻¹)^ζ`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

/-- **The book's `ω̄^{KW}`** (Peterfalvi Part II, Ch. IV §2, p. 124): `x` and `y` have
images in `Q/Q₀` lying in the same orbit of `D = KW`.

Written out, `y = d⁻¹ (x z) d` for some `z ∈ Q₀` and `d ∈ D` — the `Q₀`-translate absorbs
the passage to the quotient, so no quotient group has to be formed. -/
def barOrbitRel (x y : G) : Prop := ∃ z ∈ hyp.Q0, dOrbitRel hyp.KW (x * z) y

namespace barOrbitRel

variable {hyp}

@[refl] theorem refl (x : G) : hyp.barOrbitRel x x :=
  ⟨1, hyp.Q0.one_mem, by rw [mul_one]; exact dOrbitRel.refl _⟩

/-- The `Q₀`-translates of `x` are in its orbit. -/
theorem mul_Q0 {x z : G} (hz : z ∈ hyp.Q0) : hyp.barOrbitRel x (x * z) :=
  ⟨z, hz, dOrbitRel.refl _⟩

/-- `D`-conjugates of `x` are in its orbit. -/
theorem of_dOrbitRel {x y : G} (hxy : dOrbitRel hyp.KW x y) : hyp.barOrbitRel x y :=
  ⟨1, hyp.Q0.one_mem, by rwa [mul_one]⟩

theorem symm {x y : G} (hxy : hyp.barOrbitRel x y) : hyp.barOrbitRel y x := by
  obtain ⟨z, hz, d, hd, rfl⟩ := hxy
  refine ⟨d⁻¹ * z⁻¹ * d, ?_, d⁻¹, hyp.KW.inv_mem hd, ?_⟩
  · have := hyp.conj_mem_Q0_of_mem_H
      (hyp.D_le_H (hyp.KW_le_D (hyp.KW.inv_mem hd))) (hyp.Q0.inv_mem hz)
    rwa [inv_inv] at this
  · group

theorem trans {x y w : G} (hxy : hyp.barOrbitRel x y) (hyw : hyp.barOrbitRel y w) :
    hyp.barOrbitRel x w := by
  obtain ⟨z₁, hz₁, d₁, hd₁, rfl⟩ := hxy
  obtain ⟨z₂, hz₂, d₂, hd₂, rfl⟩ := hyw
  refine ⟨z₁ * (d₁ * z₂ * d₁⁻¹), hyp.Q0.mul_mem hz₁
    (hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H (hyp.KW_le_D hd₁)) hz₂), d₁ * d₂,
      hyp.KW.mul_mem hd₁ hd₂, ?_⟩
  group

/-- The orbit of an element of `Q` stays in `Q`. -/
theorem mem_Q {x y : G} (hx : x ∈ hyp.Q) (hxy : hyp.barOrbitRel x y) : y ∈ hyp.Q := by
  obtain ⟨z, hz, d, hd, rfl⟩ := hxy
  exact hyp.rankOneSetup.DQ d (hyp.KW_le_D hd) _ (hyp.Q.mul_mem hx (hyp.Q0_le_Q hz))

/-- The orbit of an element outside `Q₀` stays outside `Q₀`. -/
theorem notMem_Q0 {x y : G} (hx0 : x ∉ hyp.Q0)
    (hxy : hyp.barOrbitRel x y) : y ∉ hyp.Q0 := by
  obtain ⟨z, hz, d, hd, rfl⟩ := hxy
  intro hc
  refine hx0 ?_
  have hxz : x * z ∈ hyp.Q0 := by
    have := hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H (hyp.KW_le_D hd)) hc
    rw [show d * (d⁻¹ * (x * z) * d) * d⁻¹ = x * z from by group] at this
    exact this
  have := hyp.Q0.mul_mem hxz (hyp.Q0.inv_mem hz)
  rwa [mul_assoc, mul_inv_cancel, mul_one] at this

end barOrbitRel

/-- The `KW`-orbit relation of `Q/Q₀` as a setoid, so that "distinct representatives" is
literally distinctness of classes. -/
def barOrbitSetoid : Setoid G where
  r := hyp.barOrbitRel
  iseqv := ⟨barOrbitRel.refl, barOrbitRel.symm, barOrbitRel.trans⟩

/-- **§2 (9) produces a normalized element of the same orbit** (Peterfalvi Part II,
p. 124–125): the book's "`ω̄'_i` is in the orbit of `ω̄_i` under `KW`".

This is `stepNine` with its orbit clause read through `barOrbitRel`; it is what makes a
transversal of the orbits *by normalized elements* possible, which the closing
Proposition of §2 (p. 129) indexes by. -/
theorem barOrbitRel_of_stepNine {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    {ζ : G} (hζW : ζ ∈ hyp.W) (hζ1 : ζ ≠ 1) :
    ∃ ω' ∈ hyp.Q, ω' ∉ hyp.Q0 ∧ hyp.barOrbitRel ω ω' ∧
      ∃ y ∈ hyp.Q0, y ≠ 1 ∧ f ω' = ζ⁻¹ * (ω' * y) * ζ := by
  obtain ⟨ω', hω'Q, hω'Q0, ⟨z, hz, horb⟩, y, hyQ0, hy1, hnorm⟩ :=
    hyp.stepNine_of_KW M hZ H hC2 hm hQ0card hinj hKcard hWdvd hωQ hωQ0 hζW hζ1
  exact ⟨ω', hω'Q, hω'Q0, ⟨z, hz, horb⟩, y, hyQ0, hy1, hnorm⟩

/-- **A normalized transversal of the `KW`-orbits** (Peterfalvi Part II, Ch. IV §2,
p. 124–125): the book's `ω_1, …, ω_n`, chosen normalized by (9).

The book indexes the orbits and picks one representative each; the same data is a map
`r : G → G` that is *constant on orbits* and lands on a normalized element of the orbit.
Constancy is the book's "distinct representatives", which is all its "whence `i = k`"
(p. 129) uses: two orbits named by the same `r`-value are the same orbit.

`r` is built by normalizing `Quotient.out` of the class, so it depends on the class only;
the normalization is (9) (`barOrbitRel_of_stepNine`), which lands in the same orbit. -/
theorem exists_normalizedOrbitRep {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ζ : G} (hζW : ζ ∈ hyp.W) (hζ1 : ζ ≠ 1) :
    ∃ r : G → G,
      (∀ x x' : G, hyp.barOrbitRel x x' → r x = r x') ∧
      ∀ x ∈ hyp.Q, x ∉ hyp.Q0 →
        r x ∈ hyp.Q ∧ r x ∉ hyp.Q0 ∧ hyp.barOrbitRel x (r x) ∧
          ∃ y ∈ hyp.Q0, y ≠ 1 ∧ f (r x) = ζ⁻¹ * (r x * y) * ζ := by
  classical
  -- a class-invariant choice of a point of the orbit
  set o : G → G := fun x => Quotient.out (Quotient.mk hyp.barOrbitSetoid x) with ho
  have hox : ∀ x : G, hyp.barOrbitRel x (o x) := fun x =>
    barOrbitRel.symm (Quotient.mk_out (s := hyp.barOrbitSetoid) x)
  have hoeq : ∀ x x' : G, hyp.barOrbitRel x x' → o x = o x' := fun x x' hxx' =>
    congrArg Quotient.out (Quotient.sound (s := hyp.barOrbitSetoid) hxx')
  -- normalize it by (9)
  have key : ∀ w : G, w ∈ hyp.Q ∧ w ∉ hyp.Q0 →
      ∃ ω' : G, ω' ∈ hyp.Q ∧ ω' ∉ hyp.Q0 ∧ hyp.barOrbitRel w ω' ∧
        ∃ y ∈ hyp.Q0, y ≠ 1 ∧ f ω' = ζ⁻¹ * (ω' * y) * ζ := by
    rintro w ⟨hwQ, hwQ0⟩
    obtain ⟨ω', h1, h2, h3, h4⟩ := hyp.barOrbitRel_of_stepNine M hZ H hC2 hm hQ0card
      hinj hKcard hWdvd hwQ hwQ0 hζW hζ1
    exact ⟨ω', h1, h2, h3, h4⟩
  choose! N hNQ hNQ0 hNrel hNnorm using key
  refine ⟨fun x => N (o x), fun x x' hxx' => by simp only [hoeq x x' hxx'],
    fun x hxQ hxQ0 => ?_⟩
  have hoP : o x ∈ hyp.Q ∧ o x ∉ hyp.Q0 :=
    ⟨barOrbitRel.mem_Q hxQ (hox x), barOrbitRel.notMem_Q0 hxQ0 (hox x)⟩
  exact ⟨hNQ _ hoP, hNQ0 _ hoP, barOrbitRel.trans (hox x) (hNrel _ hoP), hNnorm _ hoP⟩

/-! ## From orbit membership to step (20)'s precise form -/

/-- **Freeness of the `D`-action, in the form the closing Proposition uses**: `ω` is never
`D`-conjugate to a *nontrivial* `Q₀`-translate of itself (Peterfalvi Part II, Ch. IV §2,
p. 129: "`D` acts without fixed points on `(Q/Q₀)^#`"). -/
theorem not_dOrbitRel_self_mul_Q0 (hfree : hyp.FreeD)
    {ω z : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hzQ0 : z ∈ hyp.Q0) (hz1 : z ≠ 1) :
    ¬ dOrbitRel hyp.KW ω (ω * z) := by
  rintro ⟨d, hdD, hd⟩
  have hd1 : d = 1 :=
    hfree hωQ hωQ0 (hyp.KW_le_D hdD) hzQ0 hd.symm
  rw [hd1, inv_one, one_mul, mul_one] at hd
  exact hz1 (mul_left_cancel (a := ω) (by rw [mul_one]; exact hd))

/-- **The degenerate case of step (20)** (Peterfalvi Part II, Ch. IV §2, p. 128).

Step (20) reads `f(ω₁ z) = (ω₂ w)^c` as `z = w y`; the argument needs `w y ≠ 1`, and this
is what the excluded case says: if `w = y` then, `ω₂` being normalized, `ω₂ y = ζ f(ω₂) ζ⁻¹`
and so `f(ω₁ z)` is a `D`-conjugate of `f(ω₂)`.  Applying `f` — (H3) moves the conjugator
to `a^t`, (H2) cancels the two `f`'s — puts `ω₁ z` in the `D`-orbit of `ω₂`.

Together with `not_dOrbitRel_self_mul_Q0` that is a contradiction whenever `ω₁ = ω₂` and
`z ≠ 1`, which is how the closing Proposition disposes of the case. -/
theorem dOrbitRel_of_stepTwenty_degenerate (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω₁ ω₂ y z c : G} (hζW : ζ ∈ hyp.W)
    (hω₁Q : ω₁ ∈ hyp.Q) (hω₁Q0 : ω₁ ∉ hyp.Q0)
    (hω₂Q : ω₂ ∈ hyp.Q) (hω₂Q0 : ω₂ ∉ hyp.Q0)
    (hzQ0 : z ∈ hyp.Q0) (hcKW : c ∈ hyp.KW)
    (hf₂ : f ω₂ = ζ⁻¹ * (ω₂ * y) * ζ)
    (hrel : f (ω₁ * z) = c⁻¹ * (ω₂ * y) * c) :
    dOrbitRel hyp.KW ω₂ (ω₁ * z) := by
  obtain ⟨hω₁zQ, hω₁zQ0⟩ := hyp.mul_mem_sdiff_Q0 hω₁Q hω₁Q0 hzQ0
  have hω₁z1 : ω₁ * z ≠ 1 := fun hc => hω₁zQ0 (hc ▸ hyp.Q0.one_mem)
  have hω₂1 : ω₂ ≠ 1 := fun hc => hω₂Q0 (hc ▸ hyp.Q0.one_mem)
  have haKW : ζ⁻¹ * c ∈ hyp.KW :=
    hyp.KW.mul_mem (hyp.KW.inv_mem (hyp.mem_KW_of_mem_W hζW)) hcKW
  have haD : ζ⁻¹ * c ∈ hyp.D := hyp.KW_le_D haKW
  -- `f(ω₁ z) = (f ω₂)^{ζ⁻¹c}`
  have hstep : f (ω₁ * z) = (ζ⁻¹ * c)⁻¹ * f ω₂ * (ζ⁻¹ * c) := by
    rw [hrel, hf₂]
    group
  have hcong := congrArg f hstep
  obtain ⟨e3, -, -⟩ := hThree hyp.rankOneSetup H (H.f_mem hω₂Q hω₂1)
    (H.f_ne_one hyp.rankOneSetup hω₂Q hω₂1) haD
  rw [(hTwo hyp.rankOneSetup H hω₁zQ hω₁z1).1, e3,
    (hTwo hyp.rankOneSetup H hω₂Q hω₂1).1] at hcong
  exact ⟨hyp.t * (ζ⁻¹ * c) * hyp.t, hyp.conj_t_mem_KW haKW, hcong⟩

/-- **Step (20)'s precise form, from mere orbit membership** (Peterfalvi Part II,
Ch. IV §2, p. 128).

The book's (20) reads: for every `x` such that `f(ω₁(0,x))‾` lies in the orbit of `ω̄₂`,

  `f(ω₁(0,x)) = (ω₂(0, x + α))^{d(x)}` with `d(x) ∈ KW`.

So orbit membership alone pins the `Q₀`-coordinate of the image.  Here that is
`stepTwenty_snd` (which gives `z = w y`) plus the disposal of its side condition
`w y ≠ 1` by `dOrbitRel_of_stepTwenty_degenerate`, whose conclusion `hdeg` excludes.

`hdeg` is not a real restriction: when `ω' = ω` it is `not_dOrbitRel_self_mul_Q0`, and
otherwise it follows from the orbit-invariance of a transversal. -/
theorem dOrbitRel_mul_of_barOrbitRel (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω ω' y z : G} (hζ : ζ ∈ hyp.W) (hWcard : orderOf ζ = Nat.card ↥hyp.W)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hω'Q : ω' ∈ hyp.Q) (hω'Q0 : ω' ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hzQ0 : z ∈ hyp.Q0)
    (hf : f ω = ζ⁻¹ * (ω * y) * ζ) (hf' : f ω' = ζ⁻¹ * (ω' * y) * ζ)
    (hz1 : z ≠ 1) (hbar : hyp.barOrbitRel (f (ω * z)) ω')
    (hdeg : ¬ dOrbitRel hyp.KW ω' (ω * z)) :
    dOrbitRel hyp.KW (f (ω * z)) (ω' * (z * y)) := by
  obtain ⟨w, hwQ0, c, hcKW, hc⟩ := hbar.symm
  by_cases hwy : w * y = 1
  · -- the degenerate case: `w = y`, which puts `ω'` in the orbit of `ω z`
    refine absurd ?_ hdeg
    have hyinv : y⁻¹ = y := by
      have hs := hyQ0.1
      rw [sq] at hs
      exact inv_eq_of_mul_eq_one_right hs
    have hwy' : w = y := by
      rw [← hyinv]
      exact eq_inv_of_mul_eq_one_left hwy
    rw [hwy'] at hc
    exact hyp.dOrbitRel_of_stepTwenty_degenerate H hζ hωQ hωQ0 hω'Q hω'Q0 hzQ0 hcKW hf' hc
  · -- the generic case: step (20) reads off `w = z y`
    have hzw : z = w * y :=
      hyp.stepTwenty_snd H hC2 hζ hWcard hωQ hωQ0 hω'Q hω'Q0 hyQ0 hf hf' hzQ0 hwQ0
        hcKW hc hz1 hwy
    have hyinv : y * y = 1 := by
      have hs := hyQ0.1
      rwa [sq] at hs
    have hwz : w = z * y := by
      rw [hzw, mul_assoc, hyinv, mul_one]
    rw [hwz] at hc
    exact ⟨c⁻¹, hyp.KW.inv_mem hcKW, by rw [hc]; group⟩

/-- **The other degenerate case of step (20)**: `w = 1` collapses the two orbits too.

If `f(ω z) = (ω')^c` outright then, applying `f` — (H3) for the conjugator, (H2) for the
two `f`'s — and reading `f(ω')` through its normalization, `ω z` lies in the `D`-orbit of
`ω' y'` — so `ω` and `ω'` share an orbit, and when `ω' = ω` the freeness of the action
(`not_dOrbitRel_self_mul_Q0`) turns that into a contradiction. -/
theorem dOrbitRel_of_stepTwenty_degenerate_one
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    {ζ ω ω' y' z c : G} (hζW : ζ ∈ hyp.W)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hω'Q : ω' ∈ hyp.Q) (hω'Q0 : ω' ∉ hyp.Q0)
    (hzQ0 : z ∈ hyp.Q0) (hcKW : c ∈ hyp.KW)
    (hf' : f ω' = ζ⁻¹ * (ω' * y') * ζ)
    (hrel : f (ω * z) = c⁻¹ * ω' * c) :
    dOrbitRel hyp.KW (ω' * y') (ω * z) := by
  obtain ⟨hωzQ, hωzQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hzQ0
  have hωz1 : ω * z ≠ 1 := fun hc => hωzQ0 (hc ▸ hyp.Q0.one_mem)
  have hω'1 : ω' ≠ 1 := fun hc => hω'Q0 (hc ▸ hyp.Q0.one_mem)
  have hcong := congrArg f hrel
  obtain ⟨e3, -, -⟩ := hThree hyp.rankOneSetup H hω'Q hω'1 (hyp.KW_le_D hcKW)
  rw [(hTwo hyp.rankOneSetup H hωzQ hωz1).1, e3, hf'] at hcong
  have hb : ω * z
      = (ζ * (hyp.t * c * hyp.t))⁻¹ * (ω' * y') * (ζ * (hyp.t * c * hyp.t)) := by
    rw [hcong]
    group
  have hbKW : ζ * (hyp.t * c * hyp.t) ∈ hyp.KW :=
    hyp.KW.mul_mem (hyp.mem_KW_of_mem_W hζW) (hyp.conj_t_mem_KW hcKW)
  exact ⟨_, hbKW, hb⟩

/-- **All normalized representatives of distinct orbits share the same `y`** (Peterfalvi
Part II, p. 128: step (20)'s first assertion `α₁ = α₂`), read through orbit membership.

`stepTwenty_of_mem_D` needs four nondegeneracy conditions; two of them concern the
`Q₀`-coordinate `w` of the pairing, and the two degenerate cases (`w = 1`, `w = y'`) are
excluded by `hdeg2` and `hdeg1`.  The remaining two are about `z`, and in the closing
Proposition they are `ω² ≠ 1` and the case `ω² = y` in which there is nothing left to
prove. -/
theorem y_eq_of_barOrbitRel (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ζ ω ω' y y' z : G} (hζ : ζ ∈ hyp.W) (hWcard : orderOf ζ = Nat.card ↥hyp.W)
    (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hω'Q : ω' ∈ hyp.Q) (hω'Q0 : ω' ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hy'Q0 : y' ∈ hyp.Q0) (hzQ0 : z ∈ hyp.Q0)
    (hf : f ω = ζ⁻¹ * (ω * y) * ζ) (hf' : f ω' = ζ⁻¹ * (ω' * y') * ζ)
    (hz1 : z ≠ 1) (hzy : z * y ≠ 1)
    (hbar : hyp.barOrbitRel (f (ω * z)) ω')
    (hdeg1 : ¬ dOrbitRel hyp.KW ω' (ω * z))
    (hdeg2 : ¬ dOrbitRel hyp.KW (ω' * y') (ω * z)) :
    y = y' := by
  obtain ⟨w, hwQ0, c, hcKW, hc⟩ := hbar.symm
  have hw1 : w ≠ 1 := by
    intro hcc
    refine hdeg2 ?_
    rw [hcc, mul_one] at hc
    exact hyp.dOrbitRel_of_stepTwenty_degenerate_one H hζ hωQ hωQ0 hω'Q hω'Q0
      hzQ0 hcKW hf' hc
  have hwy' : w * y' ≠ 1 := by
    intro hcc
    refine hdeg1 ?_
    have hyinv : y'⁻¹ = y' := by
      have hs := hy'Q0.1
      rw [sq] at hs
      exact inv_eq_of_mul_eq_one_right hs
    have hwy'' : w = y' := by
      rw [← hyinv]
      exact eq_inv_of_mul_eq_one_left hcc
    rw [hwy''] at hc
    exact hyp.dOrbitRel_of_stepTwenty_degenerate H hζ hωQ hωQ0 hω'Q hω'Q0 hzQ0 hcKW hf' hc
  exact hyp.stepTwenty_of_mem_KW H hC2 hζ hWcard hωQ hωQ0 hω'Q hω'Q0 hyQ0 hy'Q0 hzQ0
    hwQ0 hf hf' hcKW hc hz1 hw1 hzy hwy'

/-- Freeness again, for two `Q₀`-translates of one `ω`. -/
theorem not_dOrbitRel_mul_Q0_mul_Q0 (hfree : hyp.FreeD)
    {ω y z : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hyQ0 : y ∈ hyp.Q0) (hzQ0 : z ∈ hyp.Q0) (hyz : y * z ≠ 1) :
    ¬ dOrbitRel hyp.KW (ω * y) (ω * z) := by
  intro hcon
  obtain ⟨hωyQ, hωyQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hyQ0
  obtain ⟨d, hdD, hd⟩ := hcon
  have hyy : y * y = 1 := by
    have hs := hyQ0.1
    rwa [sq] at hs
  have hrw : ω * y * (y * z) = ω * z := by
    rw [← mul_assoc, mul_assoc ω y y, hyy, mul_one]
  exact hyp.not_dOrbitRel_self_mul_Q0 hfree hωyQ hωyQ0
    (hyp.Q0.mul_mem hyQ0 hzQ0) hyz ⟨d, hdD, by rw [hrw]; exact hd⟩

omit [Finite G] in
/-- The `y` of a normalization is determined by `ω` (and `ζ`). -/
theorem normalization_y_unique {ζ ω y y' : G}
    (hf : f ω = ζ⁻¹ * (ω * y) * ζ) (hf' : f ω = ζ⁻¹ * (ω * y') * ζ) : y = y' := by
  have h := hf.symm.trans hf'
  exact mul_left_cancel (mul_left_cancel (mul_right_cancel h))

/-- **Squares of `Q` lie in `Q₀`** — the centre of `Q` is `Q₀` and squares are central
(`LemmaFiveSetup.sqMem`). -/
theorem sq_mem_Q0_of_lemmaFiveSetup {m : ℕ} (sfive : hyp.LemmaFiveSetup m)
    {x : G} (hx : x ∈ hyp.Q) : x * x ∈ hyp.Q0 := by
  have hmem := sfive.sqMem ⟨x, hx⟩
  rw [sfive.centerEqQ0, Subgroup.mem_subgroupOf] at hmem
  simpa [sq] using hmem

/-- **§2's closing Proposition** (Peterfalvi Part II, Ch. IV §2, p. 129):

> Suppose that `D` acts without fixed points on `(Q/Q₀)^#`.  Then there exists an index
> `i`, `1 ≤ i ≤ n`, such that `f(ω) = (ω⁻¹)^ζ` and `h(ω) ∈ W` for `ω = ω_i`.

The freeness hypothesis is `hfree` (`FreeD`; it is
`eq_one_of_conj_eq_mul_Q0_of_mem_D`); `h(ω) ∈ W` is `h_mem_W`, proved separately.

The proof is the book's.  Take `ω` a normalized representative, `ρ = ω²` and `y` its
normalization element.  If `ρ = y` there is nothing to do.  Otherwise let `ω_i` and `ω_k`
be the representatives of the orbits of `f(ω⁻¹) = f(ωρ)` and of `f(ω⁻¹(0,α)) = f(ω(ρy))`.
Step (20) — available through orbit membership by `dOrbitRel_mul_of_barOrbitRel`, its side
conditions being the freeness — turns those memberships into the two precise relations
that the (H5) chain consumes, and the chain returns
`(ω_k⁻¹ρ)^{KW} = (ω_i(ρy))^{KW}`.  Both sides are `Q₀`-translates, so `ω_i` and `ω_k` share
an orbit and the transversal makes them equal: the book's "whence `i = k`".  Freeness once
more (`sq_eq_of_dOrbitRel`) then gives `ω_i² = y`. -/
theorem exists_f_eq_conj_inv {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hmu : Function.Injective M.mu) (hfree : hyp.FreeD) (hWcyc : IsCyclic ↥hyp.W)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    (hsqQ0 : ∀ x ∈ hyp.Q, x * x ∈ hyp.Q0)
    {ζ : G} (hζW : ζ ∈ hyp.W) (hζ1 : ζ ≠ 1)
    (hWcard : orderOf ζ = Nat.card ↥hyp.W)
    {x₀ : G} (hx₀Q : x₀ ∈ hyp.Q) (hx₀Q0 : x₀ ∉ hyp.Q0) :
    ∃ ω ∈ hyp.Q, ω ∉ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ω * ω = y ∧ f ω = ζ⁻¹ * ω⁻¹ * ζ := by
  classical
  have hζD : ζ ∈ hyp.D := hyp.V_le_D (hyp.W_le_V hζW)
  obtain ⟨r, hrinv, hrspec⟩ := hyp.exists_normalizedOrbitRep M hZ H hC2 hm hQ0card hmu
    hKcard hWdvd hζW hζ1
  have hrfix : ∀ x ∈ hyp.Q, x ∉ hyp.Q0 → r (r x) = r x := fun x hxQ hxQ0 =>
    (hrinv x (r x) (hrspec x hxQ hxQ0).2.2.1).symm
  obtain ⟨hωQ, hωQ0, -, y, hyQ0, -, hnorm⟩ := hrspec x₀ hx₀Q hx₀Q0
  set ω := r x₀ with hωdef
  -- `ρ = ω²`
  have hρQ0 : ω * ω ∈ hyp.Q0 := hsqQ0 ω hωQ
  have hρ1 : ω * ω ≠ 1 := fun hc => hωQ0 ⟨by rw [sq]; exact hc, hyp.Q_le_H hωQ⟩
  by_cases hcase : ω * ω = y
  · exact ⟨ω, hωQ, hωQ0, y, hyQ0, hcase, hyp.f_eq_conj_inv_of_sq_eq hyQ0 hnorm hcase⟩
  -- `y ≠ ρ`, in the two forms the side conditions take
  have hyinv : y⁻¹ = y := by
    have hs := hyQ0.1
    rw [sq] at hs
    exact inv_eq_of_mul_eq_one_right hs
  have hyρ : y * (ω * ω) ≠ 1 := by
    intro hc
    exact hcase (by rw [← hyinv]; exact (inv_eq_of_mul_eq_one_right hc).symm)
  have hρy : ω * ω * y ≠ 1 := by
    intro hc
    exact hcase (by rw [← hyinv]; exact (inv_eq_of_mul_eq_one_left hc).symm)
  -- `ω` is fixed by the transversal, so anything in its orbit and in the image is `ω`
  have hcoll : ∀ x : G, x ∈ hyp.Q → x ∉ hyp.Q0 → hyp.barOrbitRel ω (r x) → r x = ω := by
    intro x hxQ hxQ0 hbar
    have h1 : r ω = r (r x) := hrinv ω (r x) hbar
    rw [hrfix x hxQ hxQ0, hωdef, hrfix x₀ hx₀Q hx₀Q0] at h1
    exact h1.symm
  set ρ := ω * ω with hρdef
  have hρyQ0 : ρ * y ∈ hyp.Q0 := hyp.Q0.mul_mem hρQ0 hyQ0
  have hyy : y * y = 1 := by
    have hs := hyQ0.1
    rwa [sq] at hs
  have hcomm : y * ρ = ρ * y :=
    Subgroup.mem_centralizer_iff.mp (hyp.Q0_le_centralizer_Q hρQ0) y (hyp.Q0_le_Q hyQ0)
  have hρyy : ρ * y * y = ρ := by rw [mul_assoc, hyy, mul_one]
  have hyρy : y * (ρ * y) = ρ := by rw [← mul_assoc, hcomm, mul_assoc, hyy, mul_one]
  -- the `i`-side: the representative of the orbit of `f(ω ρ)`
  obtain ⟨hωρQ, hωρQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hρQ0
  obtain ⟨hfρQ, hfρQ0⟩ := hyp.f_mem_sdiff_Q0 H hC2 hωρQ hωρQ0
  obtain ⟨hωiQ, hωiQ0, hωibar, yi, hyiQ0, -, hnormi⟩ := hrspec _ hfρQ hfρQ0
  set ωi := r (f (ω * ρ)) with hωidef
  -- the `k`-side: the representative of the orbit of `f(ω ρ y)`
  obtain ⟨hωρyQ, hωρyQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hρyQ0
  obtain ⟨hfρyQ, hfρyQ0⟩ := hyp.f_mem_sdiff_Q0 H hC2 hωρyQ hωρyQ0
  obtain ⟨hωkQ, hωkQ0, hωkbar, yk, hykQ0, -, hnormk⟩ := hrspec _ hfρyQ hfρyQ0
  set ωk := r (f (ω * (ρ * y))) with hωkdef
  -- nondegeneracy on the `i`-side
  have hdeg_i : ¬ dOrbitRel hyp.KW ωi (ω * ρ) := by
    intro hcon
    have heq : ωi = ω := hcoll _ hfρQ hfρQ0 (barOrbitRel.trans (barOrbitRel.mul_Q0 hρQ0)
      (barOrbitRel.symm (barOrbitRel.of_dOrbitRel hcon)))
    rw [heq] at hcon
    exact hyp.not_dOrbitRel_self_mul_Q0 hfree hωQ hωQ0 hρQ0 hρ1 hcon
  have hdeg2_i : ¬ dOrbitRel hyp.KW (ωi * yi) (ω * ρ) := by
    intro hcon
    have heq : ωi = ω := hcoll _ hfρQ hfρQ0 (barOrbitRel.trans (barOrbitRel.mul_Q0 hρQ0)
      (barOrbitRel.symm (barOrbitRel.trans (barOrbitRel.mul_Q0 hyiQ0)
        (barOrbitRel.of_dOrbitRel hcon))))
    rw [heq] at hcon hnormi
    rw [normalization_y_unique hnormi hnorm] at hcon
    exact hyp.not_dOrbitRel_mul_Q0_mul_Q0 hfree hωQ hωQ0 hyQ0 hρQ0 hyρ hcon
  -- nondegeneracy on the `k`-side
  have hdeg_k : ¬ dOrbitRel hyp.KW ωk (ω * (ρ * y)) := by
    intro hcon
    have heq : ωk = ω := hcoll _ hfρyQ hfρyQ0 (barOrbitRel.trans (barOrbitRel.mul_Q0 hρyQ0)
      (barOrbitRel.symm (barOrbitRel.of_dOrbitRel hcon)))
    rw [heq] at hcon
    exact hyp.not_dOrbitRel_self_mul_Q0 hfree hωQ hωQ0 hρyQ0 hρy hcon
  have hdeg2_k : ¬ dOrbitRel hyp.KW (ωk * yk) (ω * (ρ * y)) := by
    intro hcon
    have heq : ωk = ω := hcoll _ hfρyQ hfρyQ0 (barOrbitRel.trans (barOrbitRel.mul_Q0 hρyQ0)
      (barOrbitRel.symm (barOrbitRel.trans (barOrbitRel.mul_Q0 hykQ0)
        (barOrbitRel.of_dOrbitRel hcon))))
    rw [heq] at hcon hnormk
    rw [normalization_y_unique hnormk hnorm] at hcon
    exact hyp.not_dOrbitRel_mul_Q0_mul_Q0 hfree hωQ hωQ0 hyQ0 hρyQ0
      (by rw [hyρy]; exact hρ1) hcon
  -- step (20)'s first assertion: the two representatives carry the same `y`
  have hnormi' : f ωi = ζ⁻¹ * (ωi * y) * ζ := by
    rw [hyp.y_eq_of_barOrbitRel H hC2 hζW hWcard hωQ hωQ0 hωiQ hωiQ0 hyQ0 hyiQ0
      hρQ0 hnorm hnormi hρ1 hρy hωibar hdeg_i hdeg2_i]
    exact hnormi
  have hnormk' : f ωk = ζ⁻¹ * (ωk * y) * ζ := by
    rw [hyp.y_eq_of_barOrbitRel H hC2 hζW hWcard hωQ hωQ0 hωkQ hωkQ0 hyQ0 hykQ0
      hρyQ0 hnorm hnormk hρy (by rw [hρyy]; exact hρ1) hωkbar hdeg_k hdeg2_k]
    exact hnormk
  -- step (20)'s second assertion on both sides: the two inputs of the (H5) chain
  have hi : dOrbitRel hyp.KW (f (ω * ρ)) (ωi * (ρ * y)) :=
    hyp.dOrbitRel_mul_of_barOrbitRel H hC2 hζW hWcard hωQ hωQ0 hωiQ hωiQ0 hyQ0 hρQ0
      hnorm hnormi' hρ1 hωibar hdeg_i
  have hk : dOrbitRel hyp.KW (f (ω * (ρ * y))) (ωk * ρ) := by
    have hkk := hyp.dOrbitRel_mul_of_barOrbitRel H hC2 hζW hWcard hωQ hωQ0 hωkQ hωkQ0
      hyQ0 hρyQ0 hnorm hnormk' hρy hωkbar hdeg_k
    rwa [hρyy] at hkk
  -- the book's "Moreover, by (H4), `h(ω_k⁻¹(0,r)) ∈ K W`"
  have hex : ∃ i, y * (hyp.stepElevenSeq ζ y i).1 = 1 := by
    obtain ⟨i, -, hi'⟩ := hyp.exists_stop_lt_orderOf H hC2 hζW hωQ hωQ0 hyQ0 hnorm
    exact ⟨i, hi'⟩
  have hstop : y * (hyp.stepElevenSeq ζ y (Nat.find hex)).1 = 1 := Nat.find_spec hex
  have hns : ∀ i < Nat.find hex, y * (hyp.stepElevenSeq ζ y i).1 ≠ 1 :=
    fun _ hi' => Nat.find_min hex hi'
  have hhW : h ω ∈ hyp.W :=
    hyp.h_mem_W_of_frobeniusD H hC2 hfree hZ hWcyc hζW hωQ hωQ0 hyQ0 hnorm hWcard hns
      hstop
  obtain ⟨c, hcKW, hcrel⟩ := id hk
  have hhX : h (ωk⁻¹ * ρ) ∈ hyp.KW :=
    hyp.h_inv_mul_mem_KW_of_stepTwenty H hC2 hζW hωQ hωQ0 hyQ0 hnorm hhW hns hstop
      hωkQ hωkQ0 hρdef hρQ0 hcKW hcrel
  -- the (H5) chain, and the book's "whence `i = k`"
  have hchain := hyp.dOrbitRel_of_stepTwenty_chain H hωQ hωQ0 hωkQ hωkQ0 hyQ0 hρQ0
    hρdef hζW hnorm hhX hi hk
  have hωksq : ωk * ωk ∈ hyp.Q0 := hsqQ0 ωk hωkQ
  have hωkinv : ωk⁻¹ = ωk * (ωk * ωk) := by
    have h4 : ωk * ωk * (ωk * ωk) = 1 := by
      have hs := hωksq.1
      rwa [sq] at hs
    calc ωk⁻¹ = ωk * ωk * (ωk * ωk) * ωk⁻¹ := by rw [h4, one_mul]
      _ = ωk * (ωk * ωk) := by group
  have hbarki : hyp.barOrbitRel ωk ωi := by
    refine barOrbitRel.trans ?_ (barOrbitRel.symm (barOrbitRel.mul_Q0 hρyQ0))
    refine barOrbitRel.trans ?_ (barOrbitRel.of_dOrbitRel hchain)
    rw [hωkinv, mul_assoc]
    exact barOrbitRel.mul_Q0 (hyp.Q0.mul_mem hωksq hρQ0)
  have hωifix : r ωi = ωi := by rw [hωidef]; exact hrfix _ hfρQ hfρQ0
  have hωkfix : r ωk = ωk := by rw [hωkdef]; exact hrfix _ hfρyQ hfρyQ0
  have hki : ωk = ωi := by rw [← hωkfix, ← hωifix]; exact hrinv _ _ hbarki
  rw [hki] at hchain
  have hsqi : ωi * ωi = y :=
    hyp.sq_eq_of_dOrbitRel hfree hωiQ hωiQ0 hyQ0 hρQ0 (hsqQ0 ωi hωiQ) hchain
  exact ⟨ωi, hωiQ, hωiQ0, y, hyQ0, hsqi, hyp.f_eq_conj_inv_of_sq_eq hyQ0 hnormi' hsqi⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
