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
* `conj_mul_pow_three_eq_one` — the same relation read off a witness of hypothesis (B).
* `cross_commute_of_three_relations` — Lemma C.
* `eq_one_of_closure_eq_top`, `eq_top_of_generators_mem` — the two abstract steps of Theorem 2,
  assembled in `commutator_eq_top_of_relations`: for an exponent that is not a Frobenius power
  the three layers die in `N^{ab}`, so `N` is perfect.
* `commute_conj_of_le_closure` — Theorem 1's engine: the relation family plus a spanning set
  makes the cross-commutator vanish.
* `injective_pow_mul` — the coset separation behind Lemma D.
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

/-- Expansion of `(x · c)³` into the three `x`-conjugates of `c`, valid whenever `x³ = 1`:

`(x c)³ = c^{x²} · (c^x · c)`.

Equivalently `(x c)³ = 1` says that the "norm" of `c` along `⟨x⟩` is trivial. -/
theorem pow_three_eq_conj_mul (hx : x ^ 3 = 1) (c : G) :
    (x * c) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * ((x⁻¹ * c * x) * c) := by
  have hxi : x⁻¹ = x * x := inv_eq_mul_self hx
  have hcan : ∀ r : G, x * (x * (x * r)) = r := cancel_three hx
  simp only [hxi, pow_succ, pow_zero, one_mul, mul_assoc, hcan]

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
  have e₂ : (x * c * x) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * (c * (x⁻¹ * c * x)) := by
    simp only [hxi, pow_succ, pow_zero, one_mul, mul_assoc, hcan]
  rw [pow_three_eq_conj_mul hx c, e₂, h.eq]

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

/-- **Theorem 2, linear step.**  Three homomorphisms into a commutative group whose "diagonal"
form kills a generating set of the triple product are all trivial.

In the application `V` is the additive group of `𝔽_{3^q}`, `A` is the abelianisation `N^{ab}`, the
`π_i` are the three layer maps `v ↦ ⟦v^{gⁱ}⟧` and `T` is the set of triples `(s, s^e, s^{e²})` for
`s` in the set of squares: the hypothesis `hspan` is then exactly `L_e = V³`, which holds iff `e`
is not a power of the Frobenius. -/
@[to_additive]
theorem eq_one_of_closure_eq_top {V A : Type*} [CommGroup V] [CommGroup A]
    (π₀ π₁ π₂ : V →* A) {T : Set (V × V × V)}
    (hT : ∀ t ∈ T, π₀ t.1 * π₁ t.2.1 * π₂ t.2.2 = 1)
    (hspan : Subgroup.closure T = ⊤) :
    (∀ v, π₀ v = 1) ∧ (∀ v, π₁ v = 1) ∧ (∀ v, π₂ v = 1) := by
  let Φ : (V × V × V) →* A :=
    { toFun := fun t => π₀ t.1 * π₁ t.2.1 * π₂ t.2.2
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        simp only [mul_left_comm, mul_comm] }
  have hker : Subgroup.closure T ≤ Φ.ker :=
    (Subgroup.closure_le _).mpr fun t ht => by simpa [Φ, MonoidHom.mem_ker] using hT t ht
  rw [hspan, top_le_iff] at hker
  have hone : ∀ t : V × V × V, Φ t = 1 := fun t => by
    have : t ∈ Φ.ker := hker ▸ Subgroup.mem_top t
    simpa [MonoidHom.mem_ker] using this
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · simpa [Φ] using hone (v, 1, 1)
  · simpa [Φ] using hone (1, v, 1)
  · simpa [Φ] using hone (1, 1, v)

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

/-- **Theorem 2, assembled.**  Let `N` be generated by the images of three homomorphisms
`ι₀, ι₁, ι₂ : V →* N` out of a commutative group `V`, and suppose that for every triple `t` in a
set `T` generating `V × V × V` one has `ι₀ t.1 · ι₁ t.2.1 · ι₂ t.2.2 = 1`.  Then `N` is **perfect**.

In the application `V` is the additive group of `𝔽_{3^q}`, the `ι_i` send `v` to `v^{gⁱ}` (so their
images are the three layers `P`, `P^g`, `P^{g²}` generating `N`), and `T` is the relation lattice
`{(s, s^e, s^{e²}) : s ∈ S}`, which spans exactly when the exponent `e` is not a power of the
Frobenius.  A witness of hypothesis (B) with such an `e` therefore contains a non-trivial perfect
subgroup, so no solvable group — hence, by the odd order theorem, no finite group of odd order —
can be a witness. -/
theorem commutator_eq_top_of_relations {V N : Type*} [CommGroup V] [Group N]
    (ι₀ ι₁ ι₂ : V →* N)
    (hgen : Subgroup.closure (Set.range ι₀ ∪ Set.range ι₁ ∪ Set.range ι₂) = ⊤)
    {T : Set (V × V × V)} (hT : ∀ t ∈ T, ι₀ t.1 * ι₁ t.2.1 * ι₂ t.2.2 = 1)
    (hspan : Subgroup.closure T = ⊤) :
    commutator N = ⊤ := by
  have hab := eq_one_of_closure_eq_top ((Abelianization.of).comp ι₀)
    ((Abelianization.of).comp ι₁) ((Abelianization.of).comp ι₂)
    (fun t ht => by
      simp only [MonoidHom.comp_apply, ← map_mul]
      rw [hT t ht, map_one]) hspan
  refine eq_top_of_generators_mem hgen ?_
  intro x hx
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  rcases hx with (hx | hx) | hx
  · obtain ⟨v, rfl⟩ := hx; simpa using hab.1 v
  · obtain ⟨v, rfl⟩ := hx; simpa using hab.2.1 v
  · obtain ⟨v, rfl⟩ := hx; simpa using hab.2.2 v

end TheoremTwo

section TheoremOne

/-- **Theorem 1's engine.**  Let `P` be an abelian subgroup, `g` an element with `g³ = 1`, and
`S ⊆ P` a set of elements satisfying the norm relation `(g · s)³ = 1`.  Fix `t ∈ S`.  If the
elements `s ∈ S` for which `s · t` also lies in `S` generate `P`, then `t` commutes with the whole
of `P^g`:

`t · v^g = v^g · t` for every `v ∈ P`.

This is the step that turns the family of relations produced by conjugating `(g x)³ = 1` with
`σ(U)` into the vanishing cross-commutator.  For each admissible `s` the three relations at `s`,
`t` and `s · t` feed `cross_commute_of_three_relations`; the elements that commute with `t^g` form
a subgroup, so a generating set suffices.

In the application `P` is the additive group of `𝔽_{3^q}`, `S` is the set of squares, `t = 1`, and
the admissible `s` are those with `s` and `s + 1` both squares — a Paley-type set whose spanning
is the one analytic ingredient (Lemma B). -/
theorem commute_conj_of_le_closure {P : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {g : G} (hg3 : g ^ 3 = 1) {S : Set G} (hSP : S ⊆ (P : Set G))
    (hrel : ∀ s ∈ S, (g * s) ^ 3 = 1) {t : G} (ht : t ∈ S)
    (hspan : P ≤ Subgroup.closure {s | s ∈ S ∧ s * t ∈ S}) :
    ∀ v ∈ P, t * (g⁻¹ * v * g) = (g⁻¹ * v * g) * t := by
  -- The elements commuting with `t` after conjugation form a subgroup.
  set C : Subgroup G :=
    (Subgroup.centralizer ({t} : Set G)).comap (MulAut.conj g⁻¹).toMonoidHom with hC
  have hmemC : ∀ v : G, v ∈ C ↔ t * (g⁻¹ * v * g) = (g⁻¹ * v * g) * t := by
    intro v
    constructor
    · intro hv
      have := (Subgroup.mem_centralizer_iff.mp hv) t rfl
      simpa [MulAut.conj_apply, mul_assoc] using this
    · intro hv
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro m rfl
      simpa [MulAut.conj_apply, mul_assoc] using hv
  -- Every admissible generator lies in `C`, by Lemma C.
  have hgen : {s | s ∈ S ∧ s * t ∈ S} ⊆ (C : Set G) := by
    rintro s ⟨hs, hst⟩
    have hlayer : ∀ w ∈ S, (g⁻¹ * (g⁻¹ * w * g) * g) * (g⁻¹ * w * g) * w = 1 := by
      intro w hw
      have h := hrel w hw
      rw [pow_three_eq_conj_mul hg3 w] at h
      rw [← mul_assoc] at h
      exact h
    have ha := hlayer s hs
    have hb := hlayer t ht
    have hab := hlayer (s * t) hst
    have hab' : (g⁻¹ * (g⁻¹ * s * g) * g) * (g⁻¹ * (g⁻¹ * t * g) * g) *
        ((g⁻¹ * s * g) * (g⁻¹ * t * g)) * (s * t) = 1 := by
      have hconj : ∀ w : G, g⁻¹ * (s * t) * g = (g⁻¹ * s * g) * (g⁻¹ * t * g) := fun _ => by
        group
      rw [← hab]
      rw [hconj s]
      group
    have h₁ : (g⁻¹ * s * g) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * (g⁻¹ * s * g) := by
      have := hP s (hSP hs) t (hSP ht)
      have hcs : g⁻¹ * s * g * (g⁻¹ * t * g) = g⁻¹ * (s * t) * g := by group
      have hct : g⁻¹ * t * g * (g⁻¹ * s * g) = g⁻¹ * (t * s) * g := by group
      rw [hcs, hct, this]
    have h₀ : s * t = t * s := hP s (hSP hs) t (hSP ht)
    have := cross_commute_of_three_relations ha hb hab' h₁ h₀
    exact (hmemC s).mpr this.symm
  intro v hv
  exact (hmemC v).mp ((Subgroup.closure_le C).mpr hgen (hspan hv))

end TheoremOne

section CosetSeparation

/-! ### The combinatorial half of Lemma D

Whether the relation lattice `L_e` is all of `V³` is decided by a coset computation.  Expanding
the trace turns the annihilator condition into a vanishing combination of power monomials
`a ↦ a^{d·3ʲ}` with `d ∈ {1, e, e²}`, and the exponents involved run through the three cosets
`⟨3⟩`, `e⟨3⟩`, `e²⟨3⟩` of the Frobenius subgroup.  Cosets are equal or disjoint, and since
`e² = e⁻¹` the three are pairwise disjoint precisely when `e ∉ ⟨3⟩`.  That is the content of
`injective_pow_mul` and `injective_pow_mul_pow` below; combined with
`OddOrder.PowerMonomial.eq_zero_of_forall_trace_sum_eq_zero` it gives Lemma D. -/

/-- **Coset separation.**  In a commutative group, an element `e ∉ A` with `e³ = 1` makes the
three cosets `A`, `eA`, `e²A` pairwise disjoint: the map `(i, x) ↦ eⁱ · x` from `Fin 3 × A` is
injective.

The only arithmetic used is `e = (e²)²`, which turns "`e² ∈ A`" into "`e ∈ A`". -/
theorem injective_pow_mul {H : Type*} [CommGroup H] {A : Subgroup H} {e : H}
    (he3 : e ^ 3 = 1) (heA : e ∉ A) :
    Function.Injective fun x : Fin 3 × A => e ^ (x.1 : ℕ) * (x.2 : H) := by
  -- `e² ∈ A` would give `e = (e²)² ∈ A`.
  have he2 : e ^ 2 ∉ A := fun h => heA (by
    have h4 : e ^ 4 = e := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, he3, one_mul]
    have hmul : e ^ 2 * e ^ 2 ∈ A := A.mul_mem h h
    rwa [← pow_add, show 2 + 2 = 4 from rfl, h4] at hmul)
  have hinv : e⁻¹ = e ^ 2 := inv_eq_of_mul_eq_one_right (by
    rw [← pow_succ']; exact he3)
  have hinv2 : (e ^ 2)⁻¹ = e := by
    rw [← hinv, inv_inv]
  have hd12 : e / e ^ 2 = e ^ 2 := by rw [div_eq_mul_inv, hinv2, ← pow_two]
  have hd21 : e ^ 2 / e = e := by rw [pow_two, mul_div_assoc, div_self', mul_one]
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  simp only at hxy
  have hdiv : e ^ (i : ℕ) / e ^ (j : ℕ) ∈ A := by
    have hEq : e ^ (i : ℕ) / e ^ (j : ℕ) = (y : H) / (x : H) := by
      rw [div_eq_div_iff_mul_eq_mul, hxy, mul_comm]
    rw [hEq]
    exact A.div_mem y.2 x.2
  have hij : i = j := by
    fin_cases i <;> fin_cases j <;>
      simp_all [pow_zero, pow_one, one_div, div_self']
  subst hij
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel hxy))

end CosetSeparation

end OddOrder.BG.AppC.Problem1
