/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
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
def barOrbitRel (x y : G) : Prop := ∃ z ∈ hyp.Q0, dOrbitRel hyp.D (x * z) y

namespace barOrbitRel

variable {hyp}

@[refl] theorem refl (x : G) : hyp.barOrbitRel x x :=
  ⟨1, hyp.Q0.one_mem, by rw [mul_one]; exact dOrbitRel.refl _⟩

/-- The `Q₀`-translates of `x` are in its orbit. -/
theorem mul_Q0 {x z : G} (hz : z ∈ hyp.Q0) : hyp.barOrbitRel x (x * z) :=
  ⟨z, hz, dOrbitRel.refl _⟩

/-- `D`-conjugates of `x` are in its orbit. -/
theorem of_dOrbitRel {x y : G} (hxy : dOrbitRel hyp.D x y) : hyp.barOrbitRel x y :=
  ⟨1, hyp.Q0.one_mem, by rwa [mul_one]⟩

theorem symm {x y : G} (hxy : hyp.barOrbitRel x y) : hyp.barOrbitRel y x := by
  obtain ⟨z, hz, d, hd, rfl⟩ := hxy
  refine ⟨d⁻¹ * z⁻¹ * d, ?_, d⁻¹, hyp.D.inv_mem hd, ?_⟩
  · have := hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H (hyp.D.inv_mem hd)) (hyp.Q0.inv_mem hz)
    rwa [inv_inv] at this
  · group

theorem trans {x y w : G} (hxy : hyp.barOrbitRel x y) (hyw : hyp.barOrbitRel y w) :
    hyp.barOrbitRel x w := by
  obtain ⟨z₁, hz₁, d₁, hd₁, rfl⟩ := hxy
  obtain ⟨z₂, hz₂, d₂, hd₂, rfl⟩ := hyw
  refine ⟨z₁ * (d₁ * z₂ * d₁⁻¹), hyp.Q0.mul_mem hz₁
    (hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H hd₁) hz₂), d₁ * d₂, hyp.D.mul_mem hd₁ hd₂, ?_⟩
  group

/-- The orbit of an element of `Q` stays in `Q`. -/
theorem mem_Q {x y : G} (hx : x ∈ hyp.Q) (hxy : hyp.barOrbitRel x y) : y ∈ hyp.Q := by
  obtain ⟨z, hz, d, hd, rfl⟩ := hxy
  exact hyp.rankOneSetup.DQ d hd _ (hyp.Q.mul_mem hx (hyp.Q0_le_Q hz))

/-- The orbit of an element outside `Q₀` stays outside `Q₀`. -/
theorem notMem_Q0 {x y : G} (hx0 : x ∉ hyp.Q0)
    (hxy : hyp.barOrbitRel x y) : y ∉ hyp.Q0 := by
  obtain ⟨z, hz, d, hd, rfl⟩ := hxy
  intro hc
  refine hx0 ?_
  have hxz : x * z ∈ hyp.Q0 := by
    have := hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H hd) hc
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
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    {ζ : G} (hζW : ζ ∈ hyp.W) (hζ1 : ζ ≠ 1) :
    ∃ ω' ∈ hyp.Q, ω' ∉ hyp.Q0 ∧ hyp.barOrbitRel ω ω' ∧
      ∃ y ∈ hyp.Q0, y ≠ 1 ∧ f ω' = ζ⁻¹ * (ω' * y) * ζ := by
  obtain ⟨ω', hω'Q, hω'Q0, ⟨z, hz, horb⟩, y, hyQ0, hy1, hnorm⟩ :=
    hyp.stepNine M hZ H hC2 hVW hm hQ0card hinj hKcard hWdvd hωQ hωQ0 hζW hζ1
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
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
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
    obtain ⟨ω', h1, h2, h3, h4⟩ := hyp.barOrbitRel_of_stepNine M hZ H hC2 hVW hm hQ0card
      hinj hKcard hWdvd hwQ hwQ0 hζW hζ1
    exact ⟨ω', h1, h2, h3, h4⟩
  choose! N hNQ hNQ0 hNrel hNnorm using key
  refine ⟨fun x => N (o x), fun x x' hxx' => by simp only [hoeq x x' hxx'],
    fun x hxQ hxQ0 => ?_⟩
  have hoP : o x ∈ hyp.Q ∧ o x ∉ hyp.Q0 :=
    ⟨barOrbitRel.mem_Q hxQ (hox x), barOrbitRel.notMem_Q0 hxQ0 (hox x)⟩
  exact ⟨hNQ _ hoP, hNQ0 _ hoP, barOrbitRel.trans (hox x) (hNrel _ hoP), hNnorm _ hoP⟩

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
