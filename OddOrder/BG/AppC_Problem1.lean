/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Basic
import OddOrder.Algebra.PowerMonomialIndependence
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
* `inv_mul_pow_three_eq_one_of_commute_conj` — Theorem 1's last mile: once `x` commutes with
  `x^g`, the element `c = x⁻¹g` satisfies `c³ = 1`, so `c = 1` in the `3′`-group `Q`.
* `cross_commute_of_three_relations` — Lemma C.
* `eq_one_of_closure_eq_top`, `eq_top_of_generators_mem` — the two abstract steps of Theorem 2,
  assembled in `commutator_eq_top_of_relations`: for an exponent that is not a Frobenius power
  the three layers die in `N^{ab}`, so `N` is perfect.
* `commute_conj_of_le_closure_twisted` — Theorem 1's engine (Frobenius-twisted form), with
  `commute_conj_of_le_closure` its untwisted specialisation: the relation family plus a spanning
  set makes the cross-commutator vanish.
* `injective_pow_mul_pow` — the `3q` exponents of Lemma D are pairwise distinct.
* `injective_pow_mul`, `injective_pow_mul_pow`, `injective_powHom_pow_mul_pow` — Lemma D: the
  coset separation, the resulting distinctness of the `3q` exponents, and the wiring that turns
  it into the hypothesis of `OddOrder.PowerMonomial.eq_zero_of_forall_trace_sum_eq_zero`.
* `commutator_layerClosure_eq_top` — **Theorem 2 in the ambient group**: the layered relation
  family plus the spanning of the relation lattice makes `⟨P, P^g, P^{g²}⟩` perfect, so a witness
  with a non-Frobenius exponent forces the ambient group to be non-solvable.
* `false_of_centralizing_of_spanning` — **Theorem 1 (centralising case), assembled**: no witness
  exists, given only the Paley-type spanning hypothesis (Lemma B, not formalized: its general-`q`
  proof needs a Weil bound).
-/

namespace OddOrder.BG.AppC.Problem1

variable {G : Type*} [Group G]

section LemmaA

variable {x c g : G}

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

/-- **The last mile of Theorem 1.**  Let `x` and `g` have order dividing three, let `g · x` also
have order dividing three, and suppose `x` commutes with its `g`-conjugate.  Then

`(x⁻¹ g)³ = 1`.

Since `x⁻¹g = ⁅x, y⁆` lies in the `3′`-group `Q` for a witness of hypothesis (B), this forces
`x⁻¹g = 1`, i.e. `g = x` — and `⟨g⟩` normalizes `σ(U)` whereas `⟨x⟩` does not.  That is the final
contradiction of Theorem 1.

The computation: `(g x)³ = 1` says `x^{g²} · x^g · x = 1`, so also `x · x^{g²} · x^g = 1` after a
cyclic shift; commuting the last two factors (the hypothesis, conjugated by `g`) gives
`x · x^g · x^{g²} = 1`, which is exactly `(g x⁻¹)³ = 1`, and `x⁻¹g` is conjugate to `g x⁻¹`. -/
theorem inv_mul_pow_three_eq_one_of_commute_conj (hg : g ^ 3 = 1) (hgx : (g * x) ^ 3 = 1)
    (hcomm : x * (g⁻¹ * x * g) = (g⁻¹ * x * g) * x) : (x⁻¹ * g) ^ 3 = 1 := by
  -- `x^{g²} · (x^g · x) = 1`.
  have h1 : g⁻¹ * (g⁻¹ * x * g) * g * ((g⁻¹ * x * g) * x) = 1 := by
    rw [← pow_three_eq_conj_mul hg x]; exact hgx
  -- Cyclic shift: `x · x^{g²} · x^g = 1`.
  have h2 : x * (g⁻¹ * (g⁻¹ * x * g) * g) * (g⁻¹ * x * g) = 1 := by
    have := h1
    rw [mul_assoc] at this
    have hx1 : g⁻¹ * (g⁻¹ * x * g) * g * (g⁻¹ * x * g) = x⁻¹ := by
      rw [← mul_one (g⁻¹ * (g⁻¹ * x * g) * g * (g⁻¹ * x * g)), ← mul_inv_cancel x,
        ← mul_assoc, ← mul_assoc, ← mul_assoc]
      simp only [← mul_assoc] at this ⊢
      rw [this, one_mul]
    calc x * (g⁻¹ * (g⁻¹ * x * g) * g) * (g⁻¹ * x * g)
        = x * (g⁻¹ * (g⁻¹ * x * g) * g * (g⁻¹ * x * g)) := by rw [mul_assoc]
      _ = x * x⁻¹ := by rw [hx1]
      _ = 1 := mul_inv_cancel x
  -- The `g`-conjugate of the commutation hypothesis swaps the last two factors.
  have hcomm' : (g⁻¹ * x * g) * (g⁻¹ * (g⁻¹ * x * g) * g) =
      (g⁻¹ * (g⁻¹ * x * g) * g) * (g⁻¹ * x * g) := by
    have := congrArg (fun z => g⁻¹ * z * g) hcomm
    simpa [mul_assoc] using this
  have h3 : x * (g⁻¹ * x * g) * (g⁻¹ * (g⁻¹ * x * g) * g) = 1 := by
    rw [mul_assoc, hcomm', ← mul_assoc]; exact h2
  -- Read this as `(g x⁻¹)³ = 1`, then conjugate by `x`.
  have h4 : (g * x⁻¹) ^ 3 = 1 := by
    rw [pow_three_eq_conj_mul hg x⁻¹]
    have hid : g⁻¹ * (g⁻¹ * x⁻¹ * g) * g * ((g⁻¹ * x⁻¹ * g) * x⁻¹)
        = (x * (g⁻¹ * x * g) * (g⁻¹ * (g⁻¹ * x * g) * g))⁻¹ := by group
    rw [hid, h3, inv_one]
  calc (x⁻¹ * g) ^ 3 = x⁻¹ * (g * x⁻¹) ^ 3 * x := by
        simp only [pow_succ, pow_zero, one_mul]; group
    _ = 1 := by rw [h4]; group

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

section Semilinear

/-- **Semilinearity of the layer map.**  Suppose `g` normalizes a subgroup with exponent `e`, in
the sense `g · v = vᵉ · g`.  Then conjugating the `g`-layer by `v` shifts the base point by `vᵉ`:

`(z^g)^v = (z^{vᵉ})^g`.

This is the rule that produces the relation family for a *non-centralising* action: conjugating
`x^{g²} · x^g · x = 1` by `v ∈ σ(U)` gives

`(x^{v^{e²}})^{g²} · (x^{v^e})^g · x^v = 1`,

the twisted relation `R(s)` of the partial resolution.  For `e = 1` it degenerates to the plain
statement that conjugation by `v` commutes with the layer map, which is what
`pow_three_mul_conj_eq_one` uses. -/
theorem conj_layer_of_exp {g v : G} {e : ℕ} (hexp : g * v = v ^ e * g) (z : G) :
    v⁻¹ * (g⁻¹ * z * g) * v = g⁻¹ * ((v ^ e)⁻¹ * z * v ^ e) * g := by
  calc v⁻¹ * (g⁻¹ * z * g) * v = (g * v)⁻¹ * z * (g * v) := by group
    _ = (v ^ e * g)⁻¹ * z * (v ^ e * g) := by rw [hexp]
    _ = g⁻¹ * ((v ^ e)⁻¹ * z * v ^ e) * g := by group

/-- Iterating `conj_layer_of_exp`: the second layer moves by `v^{e²}`. -/
theorem conj_layer_two_of_exp {g v : G} {e : ℕ} (h₁ : g * v = v ^ e * g)
    (h₂ : g * v ^ e = (v ^ e) ^ e * g) (z : G) :
    v⁻¹ * (g⁻¹ * (g⁻¹ * z * g) * g) * v
      = g⁻¹ * (g⁻¹ * ((v ^ (e * e))⁻¹ * z * v ^ (e * e)) * g) * g := by
  rw [conj_layer_of_exp h₁ (g⁻¹ * z * g), conj_layer_of_exp h₂ z, ← pow_mul]

end Semilinear

end LemmaC

section Witness

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- Conjugation by the generator `x = σ(1)` of `σ(P₀)` preserves `Q`, since `σ(P₀)` normalizes
`Q` by hypothesis (B). -/
theorem conj_mem_Q (data : FieldNormalizerData p q G) (z : G) (hz : z ∈ data.Q) :
    data.s⁻¹ * z * data.s ∈ data.Q :=
  (Subgroup.mem_normalizer_iff''.mp (data.W2_normalizes_Q data.s_mem_W2) z).mp hz

/-- The commutator `c = x⁻¹ · x^y = ⁅x, y⁆` lies in `Q`: it is the product of `x⁻¹ y x ∈ Q` and
`y⁻¹ ∈ Q`. -/
theorem inv_mul_conj_mem_Q (data : FieldNormalizerData p q G) :
    data.s⁻¹ * MulAut.conj data.y data.s ∈ data.Q := by
  have h1 : data.s⁻¹ * data.y * data.s ∈ data.Q := conj_mem_Q data data.y data.y_mem_Q
  have h2 : data.s⁻¹ * MulAut.conj data.y data.s
      = (data.s⁻¹ * data.y * data.s) * data.y⁻¹ := by
    simp only [MulAut.conj_apply]
    group
  rw [h2]
  exact data.Q.mul_mem h1 (data.Q.inv_mem data.y_mem_Q)

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
  have hcQ := inv_mul_conj_mem_Q data
  have hcxQ : data.s⁻¹ * (data.s⁻¹ * MulAut.conj data.y data.s) * data.s ∈ data.Q :=
    conj_mem_Q data _ hcQ
  have hcomm : Commute (data.s⁻¹ * MulAut.conj data.y data.s)
      (data.s⁻¹ * (data.s⁻¹ * MulAut.conj data.y data.s) * data.s) :=
    data.Q_mul_comm hcQ hcxQ
  have hxc : data.s * (data.s⁻¹ * MulAut.conj data.y data.s) = MulAut.conj data.y data.s := by
    group
  have hg3 : (data.s * (data.s⁻¹ * MulAut.conj data.y data.s)) ^ 3 = 1 := by
    rw [hxc, ← map_pow, hx3, map_one]
  have key := pow_three_mul_pow_three_eq_one hx3 hcomm hg3
  rwa [hxc] at key

/-- The `σ(U)`-orbit of `x` stays inside `σ(P)`: `σ(U)` normalizes `σ(P)` because anything
normalizing `σ(P)σ(U)` normalizes `σ(P)` (BG Appendix C, Step 3, `P char PU`). -/
theorem conj_s_mem_P (data : FieldNormalizerData p q G) {v : G} (hv : v ∈ data.U) :
    v⁻¹ * data.s * v ∈ data.P := by
  have hvN : v ∈ Subgroup.normalizer (data.P : Set G) :=
    data.normalizer_P_sup_U_le_normalizer_P
      (Subgroup.le_normalizer (le_sup_right (a := data.P) hv))
  exact (Subgroup.mem_normalizer_iff''.mp hvN data.s).mp data.s_mem_P

/-- The conjugate `g = x^y` of the generator `x = σ(1)` of `σ(P₀)`: a generator of the subgroup
`σ(P₀)^y` that hypothesis (B) requires to normalize `σ(U)`. -/
noncomputable def conjGen (data : FieldNormalizerData p q G) : G := MulAut.conj data.y data.s

@[simp]
theorem conjGen_def (data : FieldNormalizerData p q G) :
    conjGen data = MulAut.conj data.y data.s := rfl

/-- **The twisted relation family.**  Suppose `g = x^y` normalizes `σ(U)` with exponent `e`, i.e.
`g w = wᵉ g` for `w ∈ σ(U)` (the general case `e ≠ 1`).  Conjugating `(g x)³ = 1` by `v ∈ σ(U)`
and pushing the conjugation through the layers with `conj_layer_of_exp` gives

`(x^{v^{e²}})^{g²} · (x^{v^e})^g · x^v = 1`.

This is the relation `R(s)` of `notes/bg/appC_problem1_partial_resolution.md` in its layered form:
the three layers are based at `v^{e²}`, `v^e` and `v`, which under the identification of `σ(P)`
with `𝔽_{3^q}` are the field elements `s^{e²}`, `s^e` and `s`.  Feeding this family to
`commutator_eq_top_of_relations` is what makes `N` perfect when the relation lattice spans. -/
theorem layered_relation_of_exp (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data) {v : G} (hv : v ∈ data.U) :
    (conjGen data)⁻¹ * ((conjGen data)⁻¹ * ((v ^ (e * e))⁻¹ * data.s * v ^ (e * e)) *
        conjGen data) * conjGen data *
      (((conjGen data)⁻¹ * ((v ^ e)⁻¹ * data.s * v ^ e) * conjGen data) *
        (v⁻¹ * data.s * v)) = 1 := by
  have hx3 : data.s ^ 3 = 1 := by
    subst hp
    rw [FieldNormalizerData.s, ← map_pow, primeLineGenerator_pow_p, map_one]
  have hg3 : (conjGen data) ^ 3 = 1 := by
    rw [conjGen_def, ← map_pow, hx3, map_one]
  -- The layered form of `(g x)³ = 1`.
  have hlayer : (conjGen data)⁻¹ * ((conjGen data)⁻¹ * data.s * conjGen data) * conjGen data *
      (((conjGen data)⁻¹ * data.s * conjGen data) * data.s) = 1 :=
    (pow_three_eq_conj_mul hg3 data.s).symm.trans (conj_mul_pow_three_eq_one data hp)
  -- Conjugate by `v` and push the conjugation through the three layers.
  have hconj := congrArg (fun z => v⁻¹ * z * v) hlayer
  simp only [mul_one, inv_mul_cancel] at hconj
  have hdist : v⁻¹ * ((conjGen data)⁻¹ * ((conjGen data)⁻¹ * data.s * conjGen data) *
        conjGen data * (((conjGen data)⁻¹ * data.s * conjGen data) * data.s)) * v
      = (v⁻¹ * ((conjGen data)⁻¹ * ((conjGen data)⁻¹ * data.s * conjGen data) * conjGen data) * v)
        * ((v⁻¹ * ((conjGen data)⁻¹ * data.s * conjGen data) * v) * (v⁻¹ * data.s * v)) := by
    group
  rw [hdist, conj_layer_two_of_exp (hexp v hv) (hexp (v ^ e) (data.U.pow_mem hv e)) data.s,
    conj_layer_of_exp (hexp v hv) data.s] at hconj
  exact hconj

/-- **The relation family.**  If `g = x^y` centralizes `σ(U)` — the case `e = 1`, which the book's
remark makes automatic whenever `3 ∤ |Aut U|` — then conjugating `(g x)³ = 1` by `σ(U)` produces
the whole family

`(g · s)³ = 1` for every `s` in the `σ(U)`-orbit of `x`,

which is exactly the input `hrel` of `commute_conj_of_le_closure`.  Under the identification of
`σ(P)` with `𝔽_{3^q}` that orbit is the set of squares. -/
theorem pow_three_mul_conj_eq_one (data : FieldNormalizerData p q G) (hp : p = 3)
    (hcent : ∀ v ∈ data.U, Commute (MulAut.conj data.y data.s) v) {v : G} (hv : v ∈ data.U) :
    (MulAut.conj data.y data.s * (v⁻¹ * data.s * v)) ^ 3 = 1 := by
  have h := conj_mul_pow_three_eq_one data hp
  have hg : v⁻¹ * MulAut.conj data.y data.s * v = MulAut.conj data.y data.s := by
    have := (hcent v hv).eq
    calc v⁻¹ * MulAut.conj data.y data.s * v = v⁻¹ * (MulAut.conj data.y data.s * v) := by
          rw [mul_assoc]
      _ = v⁻¹ * (v * MulAut.conj data.y data.s) := by rw [this]
      _ = MulAut.conj data.y data.s := by group
  have hconj : (v⁻¹ * (MulAut.conj data.y data.s * data.s) * v) ^ 3
      = v⁻¹ * (MulAut.conj data.y data.s * data.s) ^ 3 * v := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  have hsplit : v⁻¹ * (MulAut.conj data.y data.s * data.s) * v
      = MulAut.conj data.y data.s * (v⁻¹ * data.s * v) := by
    calc v⁻¹ * (MulAut.conj data.y data.s * data.s) * v
        = (v⁻¹ * MulAut.conj data.y data.s * v) * (v⁻¹ * data.s * v) := by group
      _ = MulAut.conj data.y data.s * (v⁻¹ * data.s * v) := by rw [hg]
  rw [← hsplit, hconj, h, mul_one, inv_mul_cancel]

/-- **Theorem 1, assembled.**  In a witness of hypothesis (B) with `p = 3`, the generator
`x = σ(1)` of `σ(P₀)` cannot commute with its conjugate `x^g`, where `g = x^y` generates
`σ(P₀)^y`.

This is everything of Theorem 1 except the production of the relation family (conjugating
`(g x)³ = 1` by `σ(U)`) and the Paley-type spanning lemma: given those,
`commute_conj_of_le_closure_twisted` supplies the commutation and this theorem closes the
argument.  The chain here is `(g x)³ = 1` (from (B)) → `(x⁻¹g)³ = 1` (the last mile) →
`x⁻¹g = 1` (because `Q` is a `3′`-group) → `g = x`, which is absurd since `⟨g⟩` normalizes `σ(U)`
while `x` does not (`FieldNormalizerData.s_not_normalizes_U`). -/
theorem not_commute_conj (data : FieldNormalizerData p q G) (hp : p = 3) :
    ¬ Commute data.s ((MulAut.conj data.y data.s)⁻¹ * data.s * MulAut.conj data.y data.s) := by
  intro hcomm
  subst hp
  have hx3 : data.s ^ 3 = 1 := by
    rw [FieldNormalizerData.s, ← map_pow, primeLineGenerator_pow_p, map_one]
  have hg3 : (MulAut.conj data.y data.s) ^ 3 = 1 := by
    rw [← map_pow, hx3, map_one]
  have hgx : (MulAut.conj data.y data.s * data.s) ^ 3 = 1 :=
    conj_mul_pow_three_eq_one data rfl
  -- `c = x⁻¹g` has order dividing three and lies in the `3′`-group `Q`, so it is trivial.
  have hc3 : (data.s⁻¹ * MulAut.conj data.y data.s) ^ 3 = 1 :=
    inv_mul_pow_three_eq_one_of_commute_conj hg3 hgx hcomm.eq
  have hc1 : data.s⁻¹ * MulAut.conj data.y data.s = 1 :=
    data.eq_one_of_mem_Q_of_pow_p_eq_one (inv_mul_conj_mem_Q data) hc3
  -- Hence `g = x`, but `⟨g⟩` normalizes `σ(U)` and `x` does not.
  have hgx' : MulAut.conj data.y data.s = data.s := by
    have := congrArg (fun z => data.s * z) hc1
    simpa using this
  refine data.s_not_normalizes_U ?_
  have hmem : MulAut.conj data.y data.s ∈ Subgroup.normalizer (data.U : Set G) := by
    refine data.W2_conj_y_normalizes_U ?_
    exact ⟨data.s, data.s_mem_W2, rfl⟩
  rwa [hgx'] at hmem

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
theorem eq_one_of_closure_eq_top {V A : Type*} [Group V] [CommGroup A]
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
theorem commutator_eq_top_of_relations {V N : Type*} [Group V] [Group N]
    (ι₀ ι₁ ι₂ : V →* N)
    (hgen : Subgroup.closure (Set.range ι₀ ∪ Set.range ι₁ ∪ Set.range ι₂) = ⊤)
    {T : Set (V × V × V)} (hT : ∀ t ∈ T, ι₂ t.2.2 * ι₁ t.2.1 * ι₀ t.1 = 1)
    (hspan : Subgroup.closure T = ⊤) :
    commutator N = ⊤ := by
  have hab := eq_one_of_closure_eq_top ((Abelianization.of).comp ι₀)
    ((Abelianization.of).comp ι₁) ((Abelianization.of).comp ι₂)
    (fun t ht => by
      have h := congrArg Abelianization.of (hT t ht)
      simp only [map_mul, map_one] at h
      simp only [MonoidHom.comp_apply]
      calc Abelianization.of (ι₀ t.1) * Abelianization.of (ι₁ t.2.1) *
            Abelianization.of (ι₂ t.2.2)
          = Abelianization.of (ι₂ t.2.2) * Abelianization.of (ι₁ t.2.1) *
            Abelianization.of (ι₀ t.1) := by
            simp only [mul_comm, mul_left_comm]
        _ = 1 := h) hspan
  refine eq_top_of_generators_mem hgen ?_
  intro x hx
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  rcases hx with (hx | hx) | hx
  · obtain ⟨v, rfl⟩ := hx; simpa using hab.1 v
  · obtain ⟨v, rfl⟩ := hx; simpa using hab.2.1 v
  · obtain ⟨v, rfl⟩ := hx; simpa using hab.2.2 v

/-- The `i`-th **layer map** `v ↦ v^{gⁱ}` from a subgroup `P` into a subgroup `N` containing all
the layers, packaged as a group homomorphism `P →* N`.

These are the `ι_i` of `commutator_eq_top_of_relations`: with `P = σ(P)`, `g = x^y` and
`N = ⟨P, P^g, P^{g²}⟩`, the twisted relation family `layered_relation_of_exp` says exactly that
the triples `(x^{v}, x^{v^e}, x^{v^{e²}})` are killed by `ι₀ · ι₁ · ι₂`, so once those triples
generate `P × P × P` — which is Lemma D's `L_e = V³` — the group `N` is perfect. -/
noncomputable def layerHom (P N : Subgroup G) (g : G) (i : ℕ)
    (h : ∀ v ∈ P, (g ^ i)⁻¹ * v * g ^ i ∈ N) : P →* N :=
  MonoidHom.codRestrict (((MulAut.conj (g ^ i)⁻¹).toMonoidHom).comp P.subtype) N
    (fun v => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact h v v.2)

@[simp]
theorem coe_layerHom (P N : Subgroup G) (g : G) (i : ℕ)
    (h : ∀ v ∈ P, (g ^ i)⁻¹ * v * g ^ i ∈ N) (v : P) :
    ((layerHom P N g i h v : N) : G) = (g ^ i)⁻¹ * (v : G) * g ^ i := by
  simp only [layerHom, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

/-- The `i`-th layer `P^{gⁱ}` of a subgroup, as a set. -/
def layerSet (P : Subgroup G) (g : G) (i : ℕ) : Set G :=
  (fun v => (g ^ i)⁻¹ * v * g ^ i) '' (P : Set G)

/-- The subgroup `N = ⟨P, P^g, P^{g²}⟩` generated by the three layers. -/
abbrev layerClosure (P : Subgroup G) (g : G) : Subgroup G :=
  Subgroup.closure (layerSet P g 0 ∪ layerSet P g 1 ∪ layerSet P g 2)

theorem mem_layerClosure (P : Subgroup G) (g : G) {i : ℕ} (hi : i = 0 ∨ i = 1 ∨ i = 2) {v : G}
    (hv : v ∈ P) : (g ^ i)⁻¹ * v * g ^ i ∈ layerClosure P g := by
  refine Subgroup.subset_closure ?_
  rcases hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl ⟨v, hv, rfl⟩)
  · exact Or.inl (Or.inr ⟨v, hv, rfl⟩)
  · exact Or.inr ⟨v, hv, rfl⟩

/-- **Theorem 2 in the ambient group.**  Let `P ≤ G` and `g ∈ G`, and let `N = ⟨P, P^g, P^{g²}⟩`.
If a set `T` of triples of elements of `P` generates `P × P × P` and every triple satisfies the
layered relation

`(t₂)^{g²} · (t₁)^g · t₀ = 1`,

then `N` is **perfect**.

This is Theorem 2 of `notes/bg/appC_problem1_partial_resolution.md` in the shape produced by
`layered_relation_of_exp`: for a witness of hypothesis (B) with exponent `e ∉ ⟨3⟩` the triples are
`(x^v, x^{v^e}, x^{v^{e²}})` and the spanning hypothesis is Lemma D's `L_e = V³`, so the witness
contains a non-trivial perfect subgroup and its ambient group cannot be solvable. -/
theorem commutator_layerClosure_eq_top (P : Subgroup G) (g : G) {T : Set (P × P × P)}
    (hT : ∀ t ∈ T, ((g ^ 2)⁻¹ * (t.2.2 : G) * g ^ 2) * ((g ^ 1)⁻¹ * (t.2.1 : G) * g ^ 1) *
      ((g ^ 0)⁻¹ * (t.1 : G) * g ^ 0) = 1)
    (hspan : Subgroup.closure T = ⊤) :
    commutator (layerClosure P g) = ⊤ := by
  have hmem : ∀ i : ℕ, i = 0 ∨ i = 1 ∨ i = 2 → ∀ v ∈ P,
      (g ^ i)⁻¹ * v * g ^ i ∈ layerClosure P g := fun i hi v hv => mem_layerClosure P g hi hv
  refine commutator_eq_top_of_relations
    (layerHom P (layerClosure P g) g 0 (hmem 0 (Or.inl rfl)))
    (layerHom P (layerClosure P g) g 1 (hmem 1 (Or.inr (Or.inl rfl))))
    (layerHom P (layerClosure P g) g 2 (hmem 2 (Or.inr (Or.inr rfl)))) ?_ ?_ hspan
  · -- The three layers generate `N`, so their preimages generate the whole of `↥N`.
    refine top_le_iff.mp ?_
    have hcl := Subgroup.closure_closure_coe_preimage
      (k := layerSet P g 0 ∪ layerSet P g 1 ∪ layerSet P g 2)
    rw [← hcl]
    refine Subgroup.closure_mono ?_
    rintro ⟨n, hn⟩ hmemk
    rcases hmemk with (⟨v, hv, hveq⟩ | ⟨v, hv, hveq⟩) | ⟨v, hv, hveq⟩
    · exact Or.inl (Or.inl ⟨⟨v, hv⟩, Subtype.ext (by rw [coe_layerHom]; exact hveq)⟩)
    · exact Or.inl (Or.inr ⟨⟨v, hv⟩, Subtype.ext (by rw [coe_layerHom]; exact hveq)⟩)
    · exact Or.inr ⟨⟨v, hv⟩, Subtype.ext (by rw [coe_layerHom]; exact hveq)⟩
  · -- The relations transfer from `G` to `↥N` because the coercion is injective.
    intro t ht
    refine Subtype.ext ?_
    push_cast
    rw [coe_layerHom, coe_layerHom, coe_layerHom]
    exact hT t ht

end TheoremTwo

section TheoremOne

/-- **Theorem 1's engine** (twisted form).  Let `P` be an abelian subgroup, `g` an element with
`σ` an endomorphism preserving `P`, and `S ⊆ P` a set of elements satisfying the *layered*
relation

`(σ²s)^{g²} · (σs)^g · s = 1`.

Fix `t ∈ S`.  If `σ` maps the elements `s ∈ S` with `s · t ∈ S` onto a generating set of `P`, then

`t · v^g = v^g · t` for every `v ∈ P`.

For each admissible `s` the three relations at `s`, `t` and `s · t` feed
`cross_commute_of_three_relations` — the middle layers multiply correctly because `σ` is a
homomorphism — and the elements commuting with `t` after conjugation form a subgroup, so a
generating set suffices.

In the application `P` is the additive group of `𝔽_{3^q}`, `S` the set of squares, `t = 1`, and
`σ` a power of the Frobenius: that is exactly the case `e ∈ ⟨3⟩` of the partial resolution, where
`s ↦ s^e` is additive.  `commute_conj_of_le_closure` is the untwisted specialisation `σ = id`
(the centralising case `e = 1`, available for every `q`). -/
theorem commute_conj_of_le_closure_twisted {P : Subgroup G}
    (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {g : G} (σ : G →* G)
    (hσP : ∀ v ∈ P, σ v ∈ P) {S : Set G} (hSP : S ⊆ (P : Set G))
    (hrel : ∀ s ∈ S,
      (g⁻¹ * (g⁻¹ * σ (σ s) * g) * g) * (g⁻¹ * σ s * g) * s = 1)
    {t : G} (ht : t ∈ S)
    (hspan : P ≤ Subgroup.closure (σ '' {s | s ∈ S ∧ s * t ∈ S})) :
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
  have hgen : σ '' {s | s ∈ S ∧ s * t ∈ S} ⊆ (C : Set G) := by
    rintro _ ⟨s, ⟨hs, hst⟩, rfl⟩
    have ha := hrel s hs
    have hb := hrel t ht
    have hab := hrel (s * t) hst
    have hab' : (g⁻¹ * (g⁻¹ * σ (σ s) * g) * g) * (g⁻¹ * (g⁻¹ * σ (σ t) * g) * g) *
        ((g⁻¹ * σ s * g) * (g⁻¹ * σ t * g)) * (s * t) = 1 := by
      rw [← hab]
      simp only [map_mul]
      group
    have h₁ : (g⁻¹ * σ s * g) * (g⁻¹ * σ t * g) = (g⁻¹ * σ t * g) * (g⁻¹ * σ s * g) := by
      have hcomm := hP (σ s) (hσP s (hSP hs)) (σ t) (hσP t (hSP ht))
      have hcs : g⁻¹ * σ s * g * (g⁻¹ * σ t * g) = g⁻¹ * (σ s * σ t) * g := by group
      have hct : g⁻¹ * σ t * g * (g⁻¹ * σ s * g) = g⁻¹ * (σ t * σ s) * g := by group
      rw [hcs, hct, hcomm]
    have h₀ : s * t = t * s := hP s (hSP hs) t (hSP ht)
    exact (hmemC (σ s)).mpr (cross_commute_of_three_relations ha hb hab' h₁ h₀).symm
  intro v hv
  exact (hmemC v).mp ((Subgroup.closure_le C).mpr hgen (hspan hv))

/-- **Theorem 1's engine**, untwisted (`σ = id`): the centralising case `e = 1`, available for
every `q`.  Here the relation is simply `(g · s)³ = 1` for `s ∈ S`. -/
theorem commute_conj_of_le_closure {P : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {g : G} (hg3 : g ^ 3 = 1) {S : Set G} (hSP : S ⊆ (P : Set G))
    (hrel : ∀ s ∈ S, (g * s) ^ 3 = 1) {t : G} (ht : t ∈ S)
    (hspan : P ≤ Subgroup.closure {s | s ∈ S ∧ s * t ∈ S}) :
    ∀ v ∈ P, t * (g⁻¹ * v * g) = (g⁻¹ * v * g) * t := by
  refine commute_conj_of_le_closure_twisted hP (MonoidHom.id G) (fun v hv => hv) hSP ?_ ht ?_
  · intro s hs
    have h := hrel s hs
    rw [pow_three_eq_conj_mul hg3 s] at h
    simpa [← mul_assoc] using h
  · simpa using hspan

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

/-- **The exponent family of Lemma D is injective.**  Let `φ` have order `r` in a commutative
group and let `ε ∉ ⟨φ⟩` satisfy `ε³ = 1`.  Then

`(k, j) ↦ ε^k · φ^j`  (`k < 3`, `j < r`)

is injective.  Combining `injective_pow_mul` (the three cosets of `⟨φ⟩` are disjoint) with the
injectivity of `j ↦ φ^j` below the order of `φ`.

For Lemma D one takes the group of units mod `|F| - 1`, `φ = 3` (of order `q`) and `ε = e`: the
`3q` exponents `e^k · 3^j` are then pairwise incongruent, which is exactly the hypothesis of
`OddOrder.PowerMonomial.eq_zero_of_forall_trace_sum_eq_zero`. -/
theorem injective_pow_mul_pow {H : Type*} [CommGroup H] {ε φ : H} {r : ℕ}
    (he3 : ε ^ 3 = 1) (heφ : ε ∉ Subgroup.zpowers φ) (hr : orderOf φ = r) :
    Function.Injective fun x : Fin 3 × Fin r => ε ^ (x.1 : ℕ) * φ ^ (x.2 : ℕ) := by
  have hbase := injective_pow_mul (A := Subgroup.zpowers φ) he3 heφ
  rintro ⟨k, j⟩ ⟨k', j'⟩ hEq
  have h : (fun x : Fin 3 × Subgroup.zpowers φ => ε ^ (x.1 : ℕ) * (x.2 : H))
      (k, ⟨φ ^ (j : ℕ), Subgroup.mem_zpowers_iff.mpr ⟨(j : ℕ), by simp⟩⟩) =
      (fun x : Fin 3 × Subgroup.zpowers φ => ε ^ (x.1 : ℕ) * (x.2 : H))
      (k', ⟨φ ^ (j' : ℕ), Subgroup.mem_zpowers_iff.mpr ⟨(j' : ℕ), by simp⟩⟩) := hEq
  have hpair := hbase h
  have hk : k = k' := congrArg Prod.fst hpair
  have hφ : φ ^ (j : ℕ) = φ ^ (j' : ℕ) := congrArg (fun z => (z.2 : H)) hpair
  have hj : j = j' := by
    have hjlt : (j : ℕ) < orderOf φ := by rw [hr]; exact j.isLt
    have hj'lt : (j' : ℕ) < orderOf φ := by rw [hr]; exact j'.isLt
    exact Fin.ext (pow_injOn_Iio_orderOf hjlt hj'lt hφ)
  exact Prod.ext hk hj

/-- **Lemma D, wiring.**  Let `a` generate the unit group of a finite field `F`, of order `N`, and
let `e`, `f` be natural numbers whose classes mod `N` are units `ε`, `φ` with `ε³ = 1`,
`ε ∉ ⟨φ⟩` and `φ` of order `r`.  Then the `3r` power maps

`z ↦ z ^ (eᵏ · fʲ)`  (`k < 3`, `j < r`)

on `Fˣ` are pairwise distinct.

Together with `OddOrder.PowerMonomial.eq_zero_of_forall_trace_sum_eq_zero` this is Lemma D: for
`F = 𝔽_{3^q}`, `f = 3` (of order `q` mod `N = 3^q - 1`) and `e` of order three, a vanishing trace
form `Tr(λ z + μ z^e + ν z^{e²})` has `λ = μ = ν = 0` exactly when `e ∉ ⟨3⟩`. -/
theorem injective_powHom_pow_mul_pow {F : Type*} [Field F] [Finite F] {N : ℕ} (a : Fˣ)
    (ha : orderOf a = N) {ε φ : (ZMod N)ˣ} {r e f : ℕ}
    (he3 : ε ^ 3 = 1) (heφ : ε ∉ Subgroup.zpowers φ) (hr : orderOf φ = r)
    (hE : ((e : ℕ) : ZMod N) = (ε : ZMod N)) (hF : ((f : ℕ) : ZMod N) = (φ : ZMod N)) :
    Function.Injective fun x : Fin 3 × Fin r =>
      OddOrder.PowerMonomial.powHom F (e ^ (x.1 : ℕ) * f ^ (x.2 : ℕ)) := by
  refine OddOrder.PowerMonomial.injective_powHom_of_apply_injective _ a ?_
  intro x x' hxx
  -- Pass from `F` to `Fˣ`, then to congruences mod `N = orderOf a`.
  have hunits : a ^ (e ^ (x.1 : ℕ) * f ^ (x.2 : ℕ)) = a ^ (e ^ (x'.1 : ℕ) * f ^ (x'.2 : ℕ)) := by
    apply Units.ext
    simpa using hxx
  have hmod : (e ^ (x.1 : ℕ) * f ^ (x.2 : ℕ)) ≡ (e ^ (x'.1 : ℕ) * f ^ (x'.2 : ℕ)) [MOD N] := by
    rw [← ha]; exact (pow_eq_pow_iff_modEq).mp hunits
  have hcast : ((e ^ (x.1 : ℕ) * f ^ (x.2 : ℕ) : ℕ) : ZMod N)
      = ((e ^ (x'.1 : ℕ) * f ^ (x'.2 : ℕ) : ℕ) : ZMod N) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  -- Read the two sides as units and apply the coset separation.
  have hval : ((ε ^ (x.1 : ℕ) * φ ^ (x.2 : ℕ) : (ZMod N)ˣ) : ZMod N)
      = ((ε ^ (x'.1 : ℕ) * φ ^ (x'.2 : ℕ) : (ZMod N)ˣ) : ZMod N) := by
    simpa [hE, hF] using hcast
  exact injective_pow_mul_pow he3 heφ hr (Units.ext hval)

end CosetSeparation

section Assembled

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- The image `σ(P)` of the additive kernel is abelian. -/
theorem P_mul_comm (data : FieldNormalizerData p q G) {a b : G} (ha : a ∈ data.P)
    (hb : b ∈ data.P) : a * b = b * a := by
  haveI : IsMulCommutative (NormSet.normOneFrobeniusKernel p q) := by
    unfold NormSet.normOneFrobeniusKernel
    infer_instance
  rw [← data.sigma_P_eq_P] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact setLike_mul_comm (s := NormSet.normOneFrobeniusKernel p q) ha' hb'

/-- The `σ(U)`-orbit of the generator `x = σ(1)` of `σ(P₀)`.  Under the identification of `σ(P)`
with `𝔽_{3^q}` this is the set of squares — the set `S` of the partial resolution. -/
def orbitS (data : FieldNormalizerData p q G) : Set G :=
  {s | ∃ v ∈ data.U, s = v⁻¹ * data.s * v}

/-- The additive group of `𝔽_{p^q}`, written multiplicatively, mapped into `G` by
`a ↦ σ(inl a)`.  Its range is `σ(P)`. -/
noncomputable def fieldHom (data : FieldNormalizerData p q G) :
    Multiplicative (GaloisField p q) →* G :=
  data.sigma.comp SemidirectProduct.inl

theorem fieldHom_injective (data : FieldNormalizerData p q G) :
    Function.Injective (fieldHom data) :=
  data.sigma_injective.comp SemidirectProduct.inl_injective

theorem fieldHom_range (data : FieldNormalizerData p q G) :
    (fieldHom data).range = data.P := by
  rw [← data.sigma_P_eq_P, NormSet.normOneFrobeniusKernel, fieldHom, MonoidHom.range_comp]

theorem fieldHom_mem (data : FieldNormalizerData p q G) (a : GaloisField p q) :
    fieldHom data (Multiplicative.ofAdd a) ∈ data.P := by
  rw [← fieldHom_range data]
  exact ⟨Multiplicative.ofAdd a, rfl⟩

/-- **`σ(P)` is the additive group of `𝔽_{p^q}` written multiplicatively.**  This is the
identification that turns the spanning hypotheses of `false_of_centralizing_of_spanning` and
`commutator_layerClosure_eq_top` into statements about `ZMod p`-spans in the field — the form in
which Lemma B and Lemma D of `notes/bg/appC_problem1_partial_resolution.md` are stated.

Combined with `Submodule.span_eq_top_iff_closure_eq_top` it is the last piece of plumbing between
the group-theoretic and the arithmetic sides of the partial resolution. -/
noncomputable def fieldMulEquiv (data : FieldNormalizerData p q G) :
    Multiplicative (GaloisField p q) ≃* data.P :=
  MulEquiv.ofBijective ((fieldHom data).codRestrict data.P (fun a => by
      rw [← fieldHom_range data]; exact ⟨a, rfl⟩))
    ⟨fun a b hab => fieldHom_injective data (congrArg Subtype.val hab), by
      rintro ⟨x, hx⟩
      rw [← fieldHom_range data] at hx
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, rfl⟩⟩

@[simp]
theorem coe_fieldMulEquiv (data : FieldNormalizerData p q G)
    (a : Multiplicative (GaloisField p q)) :
    ((fieldMulEquiv data a : data.P) : G) = fieldHom data a := rfl

/-- **The orbit `S` in field terms.**  The `σ(U)`-orbit of `x = σ(1)` is precisely the `σ`-image
of the *norm-one set* of `𝔽_{p^q}`, embedded additively:

`orbitS data = { σ(inl u) : u a norm-one unit }`.

This is the translation promised by `AppC.inr_inv_mul_primeLineGenerator_mul_inr`: conjugation by
`σ(inr u)` multiplies the base point by `u⁻¹`, and inversion permutes the norm-one units.  For
`p = 3` the norm-one set is the set of squares, so the spanning hypothesis of
`false_of_centralizing_of_spanning` becomes exactly Lemma B of
`notes/bg/appC_problem1_partial_resolution.md`. -/
theorem mem_orbitS_iff (data : FieldNormalizerData p q G) {s : G} :
    s ∈ orbitS data ↔ ∃ u : NormSet.normOneUnits p q,
      s = data.sigma (SemidirectProduct.inl (Multiplicative.ofAdd
        (((u : (GaloisField p q)ˣ) : GaloisField p q)))) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [← data.sigma_U_eq_U] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨u, rfl⟩ := hw
    refine ⟨u⁻¹, ?_⟩
    rw [FieldNormalizerData.s, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [inr_inv_mul_primeLineGenerator_mul_inr]
    simp
  · rintro ⟨u, rfl⟩
    refine ⟨data.sigma (SemidirectProduct.inr u⁻¹), ?_, ?_⟩
    · rw [← data.sigma_U_eq_U]
      exact ⟨SemidirectProduct.inr u⁻¹, ⟨u⁻¹, rfl⟩, rfl⟩
    · rw [FieldNormalizerData.s, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [inr_inv_mul_primeLineGenerator_mul_inr]
      simp

/-- **Theorem 1 (centralising case), assembled.**  There is no witness of BG Appendix C,
hypothesis (B), for `p = 3` in which `g = x^y` centralises `σ(U)` — *provided* the Paley-type
spanning holds: the elements `s` of the `σ(U)`-orbit of `x` for which `s · x` is again in the
orbit must generate `σ(P)`.

Under the identification of `σ(P)` with `𝔽_{3^q}` the orbit is the set of squares and the
admissible `s` are those with `s` and `s + 1` both squares, so the hypothesis is exactly Lemma B
of `notes/bg/appC_problem1_partial_resolution.md`; that lemma is the one analytic ingredient of
Theorem 1 (its general-`q` proof uses a Weil bound) and is not formalized here.

Everything else *is*: the relation family `pow_three_mul_conj_eq_one`, the engine
`commute_conj_of_le_closure`, and the closing contradiction `not_commute_conj`.

Since the book's remark makes the centralising case automatic whenever `3 ∤ |Aut U|`, this covers
in particular every `q` with `3 ∤ φ((3^q - 1)/2)` — e.g. `q = 5, 11, 17, 23, 37, 43`. -/
theorem false_of_centralizing_of_spanning (data : FieldNormalizerData p q G) (hp : p = 3)
    (hcent : ∀ v ∈ data.U, Commute (MulAut.conj data.y data.s) v)
    (hspan : data.P ≤ Subgroup.closure
      {s | s ∈ orbitS data ∧ s * data.s ∈ orbitS data}) : False := by
  have hx3 : data.s ^ 3 = 1 := by
    subst hp
    rw [FieldNormalizerData.s, ← map_pow, primeLineGenerator_pow_p, map_one]
  have hg3 : (MulAut.conj data.y data.s) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hSP : orbitS data ⊆ (data.P : Set G) := by
    rintro s ⟨v, hv, rfl⟩
    exact conj_s_mem_P data hv
  have hrel : ∀ s ∈ orbitS data, (MulAut.conj data.y data.s * s) ^ 3 = 1 := by
    rintro s ⟨v, hv, rfl⟩
    exact pow_three_mul_conj_eq_one data hp hcent hv
  have ht : data.s ∈ orbitS data := ⟨1, data.U.one_mem, by group⟩
  have hcomm := commute_conj_of_le_closure (P := data.P)
    (fun a ha b hb => P_mul_comm data ha hb) hg3 hSP hrel ht hspan data.s data.s_mem_P
  exact not_commute_conj data hp (Commute.symm (by
    have := hcomm
    exact this.symm))

end Assembled

end OddOrder.BG.AppC.Problem1
