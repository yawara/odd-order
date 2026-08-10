/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Basic
import OddOrder.BG.AppC_LemmaC3_ConjugateLine

/-!
# BG Appendix C, Problem 1: the group-theoretic core

Bender--Glauberman, *Local Analysis for the Odd Order Theorem*, Appendix C, p. 152, Problem 1
(= Glauberman--Norton, Proc. Amer. Math. Soc. **119** (1993), p. 1094, "Problem (Péterfalvi)"):

> Can the hypothesis of Proposition 9 be satisfied for `p = 3`?

This is **open** (since 1993); it is not a formalization debt.  What *is* settled — and what this
file carries — are the two elementary group-theoretic steps behind the partial resolution
recorded in `notes/bg/appC_problem1_partial_resolution.md` (issue 0180):

* **Lemma A′** (`pow_three_mul_eq_pow_three_of_commute`): if `x³ = 1` and `c` commutes with its
  conjugate `x⁻¹cx`, then `(x * c * x)³ = (x * c)³`.  Both sides expand to the three conjugates
  `c^{x²}`, `c^x`, `c` in opposite orders, so one commutation identifies them.

  Applied to a witness of hypothesis (B) with `x` a generator of `σ(P₀)`, `g = x^y` and
  `c = x⁻¹g = ⁅x, y⁆ ∈ Q`, this reads `(g * x)³ = g³ = 1`: since `Q` is *abelian* the hypothesis
  is automatic.  So (B) forces the product of the two order-three elements `g` and `x` to have
  order dividing three again — the single non-trivial relation that (B) yields, and the seed of
  everything downstream.

* **Lemma C** (`cross_commute_of_three_relations`): a pure cancellation.  Three "layered"
  relations `a₂a₁a₀ = 1`, `b₂b₁b₀ = 1`, `(a₂b₂)(a₁b₁)(a₀b₀) = 1` together with the two same-layer
  commutations force the *cross-layer* commutation `a₁b₀ = b₀a₁`.

  In the application the layers are `P`, `P^g`, `P^{g²}`, the three relations are the
  `σ(U)`-conjugates of `(g * x)³ = 1` taken at `s`, `t` and `s + t` inside the set `S` of squares
  of `𝔽_{3^q}`, and the same-layer commutations hold because each layer is abelian.  The
  conclusion is the vanishing cross-commutator `⁅t, (s^e)^g⁆ = 1` that drives the partial
  resolution.

## Main results

* `pow_three_mul_eq_pow_three_of_commute` — Lemma A′.
* `pow_three_mul_pow_three_eq_one` — the form used downstream: `(g * x)³ = 1`.
* `cross_commute_of_three_relations` — Lemma C.
-/

namespace OddOrder.BG.AppC.Problem1

variable {G : Type*} [Group G]

section LemmaA

variable {x c : G}

/-- `x³ = 1`, unfolded. -/
private theorem mul_mul_eq_one_of_pow_three (hx : x ^ 3 = 1) : x * (x * x) = 1 := by
  rw [pow_succ, pow_succ, pow_one] at hx
  rwa [← mul_assoc]

/-- With `x³ = 1` the inverse of `x` is `x * x`. -/
private theorem inv_eq_mul_self (hx : x ^ 3 = 1) : x⁻¹ = x * x :=
  inv_eq_of_mul_eq_one_left (by
    have h := mul_mul_eq_one_of_pow_three hx
    rwa [mul_assoc])

/-- Cancelling a block `x * x * x` anywhere inside a right-associated product. -/
private theorem cancel_three (hx : x ^ 3 = 1) (r : G) : x * (x * (x * r)) = r := by
  have h : x * x * x = 1 := by
    have h := mul_mul_eq_one_of_pow_three hx
    rwa [← mul_assoc] at h
  rw [← mul_assoc, ← mul_assoc, h, one_mul]

/-- **Lemma A′.**  Let `x` have order dividing three and let `c` commute with its conjugate
`x⁻¹cx`.  Then

`(x * c * x)³ = (x * c)³`.

Indeed both sides equal `c^{x²} · c^x · c` up to the order of the last two factors:
`(x * c)³ = c^{x²} c^{x} c` and `(x * c * x)³ = c^{x²} c c^{x}`.

This is the first step of the partial resolution of BG Appendix C, Problem 1: for a witness of
hypothesis (B) one takes `c = ⁅x, y⁆`, which lies in the abelian subgroup `Q`, so the commutation
hypothesis is free and the conclusion says `(g * x)³ = g³` for `g = x * c`. -/
theorem pow_three_mul_eq_pow_three_of_commute (hx : x ^ 3 = 1)
    (h : Commute c (x⁻¹ * c * x)) : (x * c * x) ^ 3 = (x * c) ^ 3 := by
  have hxi : x⁻¹ = x * x := inv_eq_mul_self hx
  have hcan : ∀ r : G, x * (x * (x * r)) = r := cancel_three hx
  have e₁ : (x * c) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * ((x⁻¹ * c * x) * c) := by
    simp only [hxi, pow_succ, pow_zero, one_mul, mul_assoc, hcan]
  have e₂ : (x * c * x) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * (c * (x⁻¹ * c * x)) := by
    simp only [hxi, pow_succ, pow_zero, one_mul, mul_assoc, hcan]
  rw [e₁, e₂, h.eq]

/-- The shape used downstream.  If `g = x * c` has order dividing three — automatic when `g` is a
conjugate of the order-three element `x` — and `c` commutes with `x⁻¹cx`, then the product
`g * x` also has order dividing three. -/
theorem pow_three_mul_pow_three_eq_one (hx : x ^ 3 = 1) (h : Commute c (x⁻¹ * c * x))
    (hg : (x * c) ^ 3 = 1) : (x * c * x) ^ 3 = 1 := by
  rw [pow_three_mul_eq_pow_three_of_commute hx h, hg]

end LemmaA

section LemmaC

variable {a₀ a₁ a₂ b₀ b₁ b₂ : G}

/-- **Lemma C** (the cancellation behind the partial resolution of BG Appendix C, Problem 1).

Suppose three "layered" relations hold,

* `a₂ * a₁ * a₀ = 1`,
* `b₂ * b₁ * b₀ = 1`,
* `(a₂ * b₂) * (a₁ * b₁) * (a₀ * b₀) = 1`,

and that same-layer elements commute, `a₁ * b₁ = b₁ * a₁` and `a₀ * b₀ = b₀ * a₀`.  Then the
*cross-layer* pair commutes as well: `a₁ * b₀ = b₀ * a₁`.

Solving the first two relations for the top layer turns the third into
`(a₁b₁)(a₀b₀) = (b₁b₀)(a₁a₀)`; cancelling `b₁` on the left and `a₀` on the right — each licensed
by one of the same-layer commutations — leaves exactly `a₁b₀ = b₀a₁`.

In the application the three layers are `P`, `P^g` and `P^{g²}` for an element `g` of order three,
and the three relations are the `σ(U)`-conjugates of `(g * x)³ = 1` evaluated at `s`, `t` and
`s + t` in the set of squares of `𝔽_{3^q}`; the hypotheses hold because each layer is abelian and
because conjugation is additive on `P`. -/
theorem cross_commute_of_three_relations (ha : a₂ * a₁ * a₀ = 1) (hb : b₂ * b₁ * b₀ = 1)
    (hab : a₂ * b₂ * (a₁ * b₁) * (a₀ * b₀) = 1) (h₁ : a₁ * b₁ = b₁ * a₁)
    (h₀ : a₀ * b₀ = b₀ * a₀) : a₁ * b₀ = b₀ * a₁ := by
  -- Solve the first two relations for the top layer.
  have ha₂ : a₂ = (a₁ * a₀)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc]; exact ha
  have hb₂ : b₂ = (b₁ * b₀)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc]; exact hb
  -- Substituting them turns the third relation into `(a₁b₁)(a₀b₀) = (b₁b₀)(a₁a₀)`.
  have key : a₁ * b₁ * (a₀ * b₀) = b₁ * b₀ * (a₁ * a₀) := by
    rw [ha₂, hb₂] at hab
    have h : (a₁ * a₀)⁻¹ * ((b₁ * b₀)⁻¹ * (a₁ * b₁ * (a₀ * b₀))) = 1 := by
      simpa [mul_assoc] using hab
    exact inv_mul_eq_iff_eq_mul.mp (inv_mul_eq_one.mp h).symm
  -- Cancel `b₁` on the left, using `a₁b₁ = b₁a₁`.
  have step : a₁ * (a₀ * b₀) = b₀ * (a₁ * a₀) := by
    have hL : a₁ * b₁ * (a₀ * b₀) = b₁ * (a₁ * (a₀ * b₀)) := by
      rw [h₁, mul_assoc]
    have hR : b₁ * b₀ * (a₁ * a₀) = b₁ * (b₀ * (a₁ * a₀)) := mul_assoc _ _ _
    rw [hL, hR] at key
    exact mul_left_cancel key
  -- Cancel `a₀` on the right, using `a₀b₀ = b₀a₀`.
  have step₂ : a₁ * b₀ * a₀ = b₀ * a₁ * a₀ := by
    rw [mul_assoc, mul_assoc, ← h₀]
    exact step
  exact mul_right_cancel step₂

end LemmaC

section Witness

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **The single relation hypothesis (B) yields**, for `p = 3`.

Let `data` be a witness of BG Appendix C, hypothesis (B), let `x = σ(1)` be the distinguished
generator of `σ(P₀)` (`FieldNormalizerData.s`) and let `g = x^y` be its conjugate by the element
`y ∈ Q`, so that `⟨g⟩ = σ(P₀)^y` is the subgroup (B) requires to normalize `σ(U)`.  Then

`(g * x)³ = 1`.

Both `g` and `x` have order three, so the assertion is that their *product* again has order
dividing three.  Nothing else about (B) is used downstream: conjugating this one relation by
`σ(U)` produces the whole family that drives the partial resolution of Problem 1 recorded in
`notes/bg/appC_problem1_partial_resolution.md`.

The proof is `pow_three_mul_pow_three_eq_one` applied to `c = x⁻¹g = ⁅x, y⁆`: since `x`
normalizes `Q` and `y ∈ Q` the element `c` lies in `Q`, and `Q` is abelian, so `c` commutes with
its conjugate `x⁻¹cx ∈ Q`. -/
theorem conj_mul_pow_three_eq_one (data : FieldNormalizerData p q G) (hp : p = 3) :
    (MulAut.conj data.y data.s * data.s) ^ 3 = 1 := by
  subst hp
  have hx3 : data.s ^ 3 = 1 := by
    rw [FieldNormalizerData.s, ← map_pow, primeLineGenerator_pow_p, map_one]
  -- `x` normalizes `Q`, so conjugation by it preserves `Q`.
  have hxn : data.s ∈ Subgroup.normalizer (data.Q : Set G) :=
    data.W2_normalizes_Q data.s_mem_W2
  have hconj : ∀ z ∈ data.Q, data.s⁻¹ * z * data.s ∈ data.Q := fun z hz =>
    (Subgroup.mem_normalizer_iff''.mp hxn z).mp hz
  -- `c = x⁻¹ g = ⁅x, y⁆` lies in `Q`.
  have hcQ : data.s⁻¹ * MulAut.conj data.y data.s ∈ data.Q := by
    have h1 : data.s⁻¹ * data.y * data.s ∈ data.Q := hconj data.y data.y_mem_Q
    have h2 : data.s⁻¹ * MulAut.conj data.y data.s
        = (data.s⁻¹ * data.y * data.s) * data.y⁻¹ := by
      simp only [MulAut.conj_apply]
      group
    rw [h2]
    exact data.Q.mul_mem h1 (data.Q.inv_mem data.y_mem_Q)
  have hcxQ : data.s⁻¹ * (data.s⁻¹ * MulAut.conj data.y data.s) * data.s ∈ data.Q :=
    hconj _ hcQ
  have hcomm : Commute (data.s⁻¹ * MulAut.conj data.y data.s)
      (data.s⁻¹ * (data.s⁻¹ * MulAut.conj data.y data.s) * data.s) :=
    data.Q_mul_comm hcQ hcxQ
  -- `x * c = g` has order dividing three, being a conjugate of `x`.
  have hxc : data.s * (data.s⁻¹ * MulAut.conj data.y data.s) = MulAut.conj data.y data.s := by
    group
  have hg3 : (data.s * (data.s⁻¹ * MulAut.conj data.y data.s)) ^ 3 = 1 := by
    rw [hxc, ← map_pow, hx3, map_one]
  have key := pow_three_mul_pow_three_eq_one hx3 hcomm hg3
  rwa [hxc] at key

end Witness

section TheoremTwo

/-! ### The abelianisation step behind Theorem 2

For an exponent `e` that is *not* a power of the Frobenius, the elimination of Lemma C is
unavailable (the map `s ↦ s^e` is no longer additive).  What replaces it is a dimension count.
Writing `π_i` for the three layer maps `V → N^{ab}`, `v ↦ ⟦v^{gⁱ}⟧`, the relation

`(s^{e²})^{g²} · (s^e)^g · s = 1   (s ∈ S)`

becomes `π₀ s + π₁ s^e + π₂ s^{e²} = 0`, so the linear form `Φ(a, b, c) = π₀a + π₁b + π₂c`
annihilates the *relation lattice* `L_e` spanned by the triples `(s, s^e, s^{e²})`.  When
`L_e` is everything — which happens exactly when `e` is not a Frobenius power — the form `Φ`
vanishes identically, all three layers die in `N^{ab}`, and `N` is therefore perfect.

The two abstract steps of that argument are `eq_zero_of_closure_eq_top` and
`eq_top_of_generators_mem`. -/

/-- **Theorem 2, linear step.**  Three homomorphisms into an abelian group whose "diagonal" form
kills a generating set of the triple product are all zero.

In the application `V` is the additive group of `𝔽_{3^q}`, `A` is `N^{ab}`, the `π_i` are the
three layer maps and `T` is the set of triples `(s, s^e, s^{e²})` for `s` in the set of squares:
the hypothesis `hspan` is then exactly `L_e = V³`, which holds iff `e` is not a power of the
Frobenius. -/
theorem eq_zero_of_closure_eq_top {V A : Type*} [AddCommGroup V] [AddCommGroup A]
    (π₀ π₁ π₂ : V →+ A) {T : Set (V × V × V)}
    (hT : ∀ t ∈ T, π₀ t.1 + π₁ t.2.1 + π₂ t.2.2 = 0)
    (hspan : AddSubgroup.closure T = ⊤) :
    (∀ v, π₀ v = 0) ∧ (∀ v, π₁ v = 0) ∧ (∀ v, π₂ v = 0) := by
  let Φ : (V × V × V) →+ A :=
    { toFun := fun t => π₀ t.1 + π₁ t.2.1 + π₂ t.2.2
      map_zero' := by simp
      map_add' := by intro a b; simp only [Prod.fst_add, Prod.snd_add, map_add]; abel }
  have hker : AddSubgroup.closure T ≤ Φ.ker :=
    (AddSubgroup.closure_le _).mpr fun t ht => by simpa [Φ, AddMonoidHom.mem_ker] using hT t ht
  rw [hspan, top_le_iff] at hker
  have hzero : ∀ t : V × V × V, Φ t = 0 := fun t => by
    have : t ∈ Φ.ker := hker ▸ AddSubgroup.mem_top t
    simpa [AddMonoidHom.mem_ker] using this
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · simpa [Φ] using hzero (v, 0, 0)
  · simpa [Φ] using hzero (0, v, 0)
  · simpa [Φ] using hzero (0, 0, v)

/-- **Theorem 2, group step.**  A group generated by elements that all lie in its derived subgroup
is perfect.

In the application the generators are the elements of the three layers `P`, `P^g`, `P^{g²}` of
`N = ⟨P, P^g, P^{g²}⟩`; `eq_zero_of_closure_eq_top` puts each of them in `[N, N]`, so `N` is
perfect — and hence non-trivial and perfect, which is what rules out solvable ambient groups (and,
by the odd order theorem, finite ambient groups of odd order). -/
theorem eq_top_of_generators_mem {N : Type*} [Group N] {X : Set N}
    (hgen : Subgroup.closure X = ⊤) (hX : ∀ x ∈ X, x ∈ commutator N) :
    commutator N = ⊤ :=
  top_le_iff.mp (hgen ▸ (Subgroup.closure_le _).mpr hX)

end TheoremTwo

end OddOrder.BG.AppC.Problem1
