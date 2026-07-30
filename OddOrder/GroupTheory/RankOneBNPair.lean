/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Complement
import Mathlib.Tactic.Group

/-!
# The mappings `f`, `g`, `h` of a rank-one split BN-pair

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §1, p. 122:

> Suppose that `L` is a finite group acting doubly transitively on a set `X`, that
> `M` is the stabilizer in `L` of a point of `X`, `t` is an involution in `L − M`
> and `D = M ∩ M^t`.  Assume there is `Q ≤ M` with `M = Q ⋊ D` (these hypotheses
> mean that `L` has a split BN-pair of rank 1).  Then there are uniquely determined
> mappings `f, g : Q^# → Q^#` and `h : Q^# → D` such that, for `x ∈ Q^#`,
> `t x t = g(x) h(x) t f(x)`.

The existence and uniqueness rest on just two structural facts, which are what this
file takes as hypotheses rather than re-deriving from double transitivity:

* `M = Q ⋊ D`, i.e. every element of `M` is uniquely `q · d`;
* every element of `L − M` is uniquely `a · t · b` with `a ∈ M`, `b ∈ Q`
  (Peterfalvi Ch. I §1, Proposition 4);

together with `t x t ∉ M` for `x ∈ Q^#`, which is where `Q^t ∩ M = 1` enters.

The chapter uses these mappings to pin down `G` in the characterization of
`PSU(3,q)`; the identities (H1)–(H6) and the lemma that `f` determines `L` are the
next steps.

## Main results

* `exists_fgh` — the mappings exist, with the defining equation.
* `fgh_unique` — they are unique.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.RankOneBNPair

universe u

variable {L : Type u} [Group L] {M Q D : Subgroup L} {t : L}

/-- **The mappings `f`, `g`, `h`** (Peterfalvi Part II, Ch. IV §1, p. 122).

For `x ∈ Q^#` the element `t x t` lies outside `M`, so it factors uniquely as
`a · t · b` with `a ∈ M` and `b ∈ Q`; splitting `a = g(x) · h(x)` along `M = Q ⋊ D`
gives the defining equation `t x t = g(x) h(x) t f(x)`. -/
theorem exists_fgh
    (hsplit : ∀ a ∈ M, ∃! p : ↥Q × ↥D, a = (p.1 : L) * (p.2 : L))
    (hfact : ∀ y : L, y ∉ M → ∃! p : ↥M × ↥Q, y = (p.1 : L) * t * (p.2 : L))
    (hconj : ∀ x ∈ Q, x ≠ 1 → t * x * t ∉ M) :
    ∃ f g h : L → L,
      (∀ x ∈ Q, x ≠ 1 → f x ∈ Q ∧ g x ∈ Q ∧ h x ∈ D) ∧
      ∀ x ∈ Q, x ≠ 1 → t * x * t = g x * h x * t * f x := by
  classical
  have key : ∀ x : L, ∃ gx hx fx : L,
      x ∈ Q → x ≠ 1 →
        (gx ∈ Q ∧ hx ∈ D ∧ fx ∈ Q ∧ t * x * t = gx * hx * t * fx) := by
    intro x
    by_cases hx : x ∈ Q ∧ x ≠ 1
    · obtain ⟨p, hp, -⟩ := hfact (t * x * t) (hconj x hx.1 hx.2)
      obtain ⟨r, hr, -⟩ := hsplit (p.1 : L) p.1.2
      refine ⟨(r.1 : L), (r.2 : L), (p.2 : L), fun _ _ => ⟨r.1.2, r.2.2, p.2.2, ?_⟩⟩
      rw [hp, hr]
    · exact ⟨1, 1, 1, fun h1 h2 => absurd ⟨h1, h2⟩ hx⟩
  choose g h f hfgh using key
  exact ⟨f, g, h,
    fun x hxQ hx1 => ⟨(hfgh x hxQ hx1).2.2.1, (hfgh x hxQ hx1).1, (hfgh x hxQ hx1).2.1⟩,
    fun x hxQ hx1 => (hfgh x hxQ hx1).2.2.2⟩

/-- **Uniqueness of `f`, `g`, `h`**: two triples satisfying the defining equation
agree on `Q^#`.  Both factorizations are unique, so the values must match. -/
theorem fgh_unique
    (hsplit : ∀ a ∈ M, ∃! p : ↥Q × ↥D, a = (p.1 : L) * (p.2 : L))
    (hfact : ∀ y : L, y ∉ M → ∃! p : ↥M × ↥Q, y = (p.1 : L) * t * (p.2 : L))
    {f₁ g₁ h₁ f₂ g₂ h₂ : L → L}
    (hmem₁ : ∀ x ∈ Q, x ≠ 1 → f₁ x ∈ Q ∧ g₁ x ∈ Q ∧ h₁ x ∈ D)
    (hmem₂ : ∀ x ∈ Q, x ≠ 1 → f₂ x ∈ Q ∧ g₂ x ∈ Q ∧ h₂ x ∈ D)
    (heq₁ : ∀ x ∈ Q, x ≠ 1 → t * x * t = g₁ x * h₁ x * t * f₁ x)
    (heq₂ : ∀ x ∈ Q, x ≠ 1 → t * x * t = g₂ x * h₂ x * t * f₂ x)
    (hQM : Q ≤ M) (hDM : D ≤ M)
    {x : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hxM : t * x * t ∉ M) :
    f₁ x = f₂ x ∧ g₁ x = g₂ x ∧ h₁ x = h₂ x := by
  classical
  obtain ⟨hf₁, hg₁, hh₁⟩ := hmem₁ x hxQ hx1
  obtain ⟨hf₂, hg₂, hh₂⟩ := hmem₂ x hxQ hx1
  -- both give a factorization of `t x t` as `a · t · b`
  obtain ⟨w, -, huniq⟩ := hfact (t * x * t) hxM
  have hM₁ : g₁ x * h₁ x ∈ M := M.mul_mem (hQM hg₁) (hDM hh₁)
  have hM₂ : g₂ x * h₂ x ∈ M := M.mul_mem (hQM hg₂) (hDM hh₂)
  have e₁ := huniq (⟨⟨g₁ x * h₁ x, hM₁⟩, ⟨f₁ x, hf₁⟩⟩) (by rw [heq₁ x hxQ hx1])
  have e₂ := huniq (⟨⟨g₂ x * h₂ x, hM₂⟩, ⟨f₂ x, hf₂⟩⟩) (by rw [heq₂ x hxQ hx1])
  have hpair := e₁.trans e₂.symm
  have hfst : g₁ x * h₁ x = g₂ x * h₂ x :=
    congrArg (Subtype.val (p := fun z => z ∈ M)) (congrArg Prod.fst hpair)
  have hsnd : f₁ x = f₂ x :=
    congrArg (Subtype.val (p := fun z => z ∈ Q)) (congrArg Prod.snd hpair)
  -- and the `Q ⋊ D` factorization of the `M`-part is unique too
  obtain ⟨w', -, huniq'⟩ := hsplit (g₁ x * h₁ x) hM₁
  have d₁ := huniq' (⟨⟨g₁ x, hg₁⟩, ⟨h₁ x, hh₁⟩⟩) rfl
  have d₂ := huniq' (⟨⟨g₂ x, hg₂⟩, ⟨h₂ x, hh₂⟩⟩) hfst
  have hpair' := d₁.trans d₂.symm
  exact ⟨hsnd,
    congrArg (Subtype.val (p := fun z => z ∈ Q)) (congrArg Prod.fst hpair'),
    congrArg (Subtype.val (p := fun z => z ∈ D)) (congrArg Prod.snd hpair')⟩

/-! ## The identities (H1)–(H6)

All of (H1)–(H4) follow the same two-step pattern: exhibit a factorization
`t y t = p · d · t · q` with `p ∈ Q`, `d ∈ D`, `q ∈ Q`, then invoke uniqueness.
`fgh_eq_of_canonical` packages the second step, so each identity reduces to the
group-theoretic rearrangement recorded in the `canonical_*` lemmas below.
-/

/-- Read-off lemma: **any** canonical factorization `t y t = p · d · t · q` with
`p ∈ Q`, `d ∈ D` and `q ∈ Q` is *the* one produced by `f, g, h`.

Both uniqueness statements are used: `hfact` identifies the `M`-part `p d` and the
`Q`-part `q`, and `hsplit` then separates `p` from `d` inside `M = Q ⋊ D`. -/
theorem fgh_eq_of_canonical
    (hsplit : ∀ a ∈ M, ∃! p : ↥Q × ↥D, a = (p.1 : L) * (p.2 : L))
    (hfact : ∀ y : L, y ∉ M → ∃! p : ↥M × ↥Q, y = (p.1 : L) * t * (p.2 : L))
    (hQM : Q ≤ M) (hDM : D ≤ M)
    {f g h : L → L}
    (hmem : ∀ x ∈ Q, x ≠ 1 → f x ∈ Q ∧ g x ∈ Q ∧ h x ∈ D)
    (heq : ∀ x ∈ Q, x ≠ 1 → t * x * t = g x * h x * t * f x)
    {y p d q : L} (hyQ : y ∈ Q) (hy1 : y ≠ 1) (hyM : t * y * t ∉ M)
    (hp : p ∈ Q) (hd : d ∈ D) (hq : q ∈ Q)
    (hcan : t * y * t = p * d * t * q) :
    f y = q ∧ g y = p ∧ h y = d := by
  classical
  obtain ⟨hfQ, hgQ, hhD⟩ := hmem y hyQ hy1
  obtain ⟨w, -, huniq⟩ := hfact (t * y * t) hyM
  have hM₁ : g y * h y ∈ M := M.mul_mem (hQM hgQ) (hDM hhD)
  have hM₂ : p * d ∈ M := M.mul_mem (hQM hp) (hDM hd)
  have e₁ := huniq (⟨⟨g y * h y, hM₁⟩, ⟨f y, hfQ⟩⟩) (by rw [heq y hyQ hy1])
  have e₂ := huniq (⟨⟨p * d, hM₂⟩, ⟨q, hq⟩⟩) (by rw [hcan])
  have hpair := e₁.trans e₂.symm
  have hfst : g y * h y = p * d :=
    congrArg (Subtype.val (p := fun z => z ∈ M)) (congrArg Prod.fst hpair)
  have hsnd : f y = q :=
    congrArg (Subtype.val (p := fun z => z ∈ Q)) (congrArg Prod.snd hpair)
  obtain ⟨w', -, huniq'⟩ := hsplit (g y * h y) hM₁
  have d₁ := huniq' (⟨⟨g y, hgQ⟩, ⟨h y, hhD⟩⟩) rfl
  have d₂ := huniq' (⟨⟨p, hp⟩, ⟨d, hd⟩⟩) hfst
  have hpair' := d₁.trans d₂.symm
  exact ⟨hsnd,
    congrArg (Subtype.val (p := fun z => z ∈ Q)) (congrArg Prod.fst hpair'),
    congrArg (Subtype.val (p := fun z => z ∈ D)) (congrArg Prod.snd hpair')⟩

/-! ### The three canonical factorizations

Each is a pure rearrangement of the defining equation using only `t * t = 1`.
-/

/-- Inverting `t x t = g(x) h(x) t f(x)` and moving `h(x)⁻¹` across `t`. -/
theorem canonical_inv (ht : t * t = 1) {f g h : L → L}
    (heq : ∀ x ∈ Q, x ≠ 1 → t * x * t = g x * h x * t * f x)
    {x : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    t * x⁻¹ * t = (f x)⁻¹ * (t * (h x)⁻¹ * t) * t * (g x)⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hinv : t * x⁻¹ * t = (t * x * t)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, htinv]
    group
  rw [hinv, heq x hxQ hx1, mul_inv_rev, mul_inv_rev, mul_inv_rev, htinv]
  have hcancel : (f x)⁻¹ * (t * (h x)⁻¹ * t) * t * (g x)⁻¹
      = (f x)⁻¹ * (t * (h x)⁻¹ * (t * t)) * (g x)⁻¹ := by group
  rw [hcancel, ht]
  group

/-- Solving `t x t = g(x) h(x) t f(x)` for `t f(x) t`; the result
`h(x)⁻¹ g(x)⁻¹ t x` is already canonical. -/
theorem canonical_f (ht : t * t = 1) {f g h : L → L}
    (heq : ∀ x ∈ Q, x ≠ 1 → t * x * t = g x * h x * t * f x)
    {x : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    t * f x * t = ((h x)⁻¹ * (g x)⁻¹ * h x) * (h x)⁻¹ * t * x := by
  have e2 : (h x)⁻¹ * (g x)⁻¹ * (t * x * t) * t
      = (h x)⁻¹ * (g x)⁻¹ * (g x * h x * t * f x) * t := by
    rw [heq x hxQ hx1]
  have lhs : (h x)⁻¹ * (g x)⁻¹ * (t * x * t) * t
      = (h x)⁻¹ * (g x)⁻¹ * t * x * (t * t) := by group
  have rhs : (h x)⁻¹ * (g x)⁻¹ * (g x * h x * t * f x) * t = t * f x * t := by group
  rw [lhs, rhs, ht, mul_one] at e2
  rw [← e2]
  group

/-- Conjugating the defining equation by `t`: writing `b = a^t = t a t`, we get
`t x^a t = (g(x)^b) · (b⁻¹ h(x) a) · t · (f(x)^b)`. -/
theorem canonical_conj (ht : t * t = 1) {f g h : L → L}
    (heq : ∀ x ∈ Q, x ≠ 1 → t * x * t = g x * h x * t * f x)
    {x a : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    t * (a⁻¹ * x * a) * t
      = ((t * a⁻¹ * t) * g x * (t * a * t)) * ((t * a⁻¹ * t) * h x * a) * t *
        ((t * a⁻¹ * t) * f x * (t * a * t)) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  -- Both rearrangements are genuine free-group identities once the *second* `t` of
  -- each conjugating pair is written as `t⁻¹`; `t * t = 1` then turns them into the
  -- displayed form.
  have hexp : t * (a⁻¹ * x * a) * t
      = (t * a⁻¹ * t) * (t * x * t) * (t * a * t) := by
    have e : t * (a⁻¹ * x * a) * t
        = (t * a⁻¹ * t⁻¹) * (t * x * t⁻¹) * (t * a * t) := by group
    rwa [htinv] at e
  have key : ∀ u v w : L,
      (t * a⁻¹ * t) * (u * v * t * w) * (t * a * t)
      = ((t * a⁻¹ * t) * u * (t * a * t)) * ((t * a⁻¹ * t) * v * a) * t *
        ((t * a⁻¹ * t) * w * (t * a * t)) := by
    intro u v w
    have e : (t⁻¹ * a⁻¹ * t) * (u * v * t * w) * (t⁻¹ * a * t)
        = ((t⁻¹ * a⁻¹ * t) * u * (t⁻¹ * a * t)) * ((t⁻¹ * a⁻¹ * t) * v * a) * t *
          ((t⁻¹ * a⁻¹ * t) * w * (t⁻¹ * a * t)) := by group
    rwa [htinv] at e
  rw [hexp, heq x hxQ hx1, key]

/-! ### (H1)–(H4) -/

/-- **(H1)**: `f(x⁻¹) = g(x)⁻¹`, together with its `g`-companion `g(x⁻¹) = f(x)⁻¹`
and **(H4)**'s `h(x⁻¹) = h(x)^{-t}` (Peterfalvi Part II, Ch. IV §1, p. 122).

All three fall out of the single canonical factorization `canonical_inv`, whose
`D`-part is `t h(x)⁻¹ t = (h(x)^t)⁻¹` — an element of `D` because `D = M ∩ M^t`. -/
theorem hOne
    (hsplit : ∀ a ∈ M, ∃! p : ↥Q × ↥D, a = (p.1 : L) * (p.2 : L))
    (hfact : ∀ y : L, y ∉ M → ∃! p : ↥M × ↥Q, y = (p.1 : L) * t * (p.2 : L))
    (hQM : Q ≤ M) (hDM : D ≤ M)
    (ht : t * t = 1) (hDstab : ∀ d ∈ D, t * d * t ∈ D)
    {f g h : L → L}
    (hmem : ∀ x ∈ Q, x ≠ 1 → f x ∈ Q ∧ g x ∈ Q ∧ h x ∈ D)
    (heq : ∀ x ∈ Q, x ≠ 1 → t * x * t = g x * h x * t * f x)
    {x : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hinvM : t * x⁻¹ * t ∉ M) :
    f x⁻¹ = (g x)⁻¹ ∧ g x⁻¹ = (f x)⁻¹ ∧ h x⁻¹ = (t * h x * t)⁻¹ := by
  obtain ⟨hfQ, hgQ, hhD⟩ := hmem x hxQ hx1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hdD : t * (h x)⁻¹ * t ∈ D := hDstab _ (D.inv_mem hhD)
  have hdeq : t * (h x)⁻¹ * t = (t * h x * t)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, htinv]
    group
  obtain ⟨h₁, h₂, h₃⟩ := fgh_eq_of_canonical hsplit hfact hQM hDM hmem heq
    (Q.inv_mem hxQ) (fun hc => hx1 (inv_eq_one.mp hc)) hinvM
    (Q.inv_mem hfQ) hdD (Q.inv_mem hgQ)
    (canonical_inv ht heq hxQ hx1)
  exact ⟨h₁, h₂, hdeq ▸ h₃⟩

/-- **(H2)**: `f(f(x)) = x`, together with **(H4)**'s `h(f(x)) = h(x)⁻¹`
(Peterfalvi Part II, Ch. IV §1, p. 122).

`canonical_f` says `t f(x) t = h(x)⁻¹ g(x)⁻¹ t x`, which is *already* canonical:
splitting `h(x)⁻¹ g(x)⁻¹` as `(g(x)⁻¹)^{h(x)} · h(x)⁻¹` inside `M = Q ⋊ D` reads off
`f(f(x)) = x` and `h(f(x)) = h(x)⁻¹` at once. -/
theorem hTwo
    (hsplit : ∀ a ∈ M, ∃! p : ↥Q × ↥D, a = (p.1 : L) * (p.2 : L))
    (hfact : ∀ y : L, y ∉ M → ∃! p : ↥M × ↥Q, y = (p.1 : L) * t * (p.2 : L))
    (hQM : Q ≤ M) (hDM : D ≤ M) (ht : t * t = 1)
    (hDQ : ∀ d ∈ D, ∀ q ∈ Q, d⁻¹ * q * d ∈ Q)
    {f g h : L → L}
    (hmem : ∀ x ∈ Q, x ≠ 1 → f x ∈ Q ∧ g x ∈ Q ∧ h x ∈ D)
    (heq : ∀ x ∈ Q, x ≠ 1 → t * x * t = g x * h x * t * f x)
    {x : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1)
    (hfne : f x ≠ 1) (hfM : t * f x * t ∉ M) :
    f (f x) = x ∧ g (f x) = (h x)⁻¹ * (g x)⁻¹ * h x ∧ h (f x) = (h x)⁻¹ := by
  obtain ⟨hfQ, hgQ, hhD⟩ := hmem x hxQ hx1
  exact fgh_eq_of_canonical hsplit hfact hQM hDM hmem heq hfQ hfne hfM
    (hDQ (h x) hhD (g x)⁻¹ (Q.inv_mem hgQ)) (D.inv_mem hhD) hxQ
    (canonical_f ht heq hxQ hx1)

/-- **(H3)**: `f(x^a) = f(x)^{a^t}` for `a ∈ D`, together with its `g`-companion
`g(x^a) = g(x)^{a^t}` and **(H4)**'s `h(x^a) = a^{-t} h(x) a`
(Peterfalvi Part II, Ch. IV §1, p. 122).

Conjugating the defining equation by `t` turns `a` into `a^t`, which again lies in
`D` because `D = M ∩ M^t`; the `M`-part `(g(x)^{a^t}) · (a^{-t} h(x) a)` is already
displayed in its `Q ⋊ D` form by `canonical_conj`. -/
theorem hThree
    (hsplit : ∀ a ∈ M, ∃! p : ↥Q × ↥D, a = (p.1 : L) * (p.2 : L))
    (hfact : ∀ y : L, y ∉ M → ∃! p : ↥M × ↥Q, y = (p.1 : L) * t * (p.2 : L))
    (hQM : Q ≤ M) (hDM : D ≤ M)
    (ht : t * t = 1) (hDstab : ∀ d ∈ D, t * d * t ∈ D)
    (hDQ : ∀ d ∈ D, ∀ q ∈ Q, d⁻¹ * q * d ∈ Q)
    {f g h : L → L}
    (hmem : ∀ x ∈ Q, x ≠ 1 → f x ∈ Q ∧ g x ∈ Q ∧ h x ∈ D)
    (heq : ∀ x ∈ Q, x ≠ 1 → t * x * t = g x * h x * t * f x)
    {x a : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (haD : a ∈ D)
    (hconjQ : a⁻¹ * x * a ∈ Q) (hconj1 : a⁻¹ * x * a ≠ 1)
    (hconjM : t * (a⁻¹ * x * a) * t ∉ M) :
    f (a⁻¹ * x * a) = (t * a * t)⁻¹ * f x * (t * a * t) ∧
      g (a⁻¹ * x * a) = (t * a * t)⁻¹ * g x * (t * a * t) ∧
      h (a⁻¹ * x * a) = (t * a * t)⁻¹ * h x * a := by
  obtain ⟨hfQ, hgQ, hhD⟩ := hmem x hxQ hx1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hbD : t * a * t ∈ D := hDstab a haD
  have hbinv : (t * a * t)⁻¹ = t * a⁻¹ * t := by
    rw [mul_inv_rev, mul_inv_rev, htinv]
    group
  have hconjMem : ∀ z ∈ Q, (t * a⁻¹ * t) * z * (t * a * t) ∈ Q := by
    intro z hz
    have := hDQ (t * a * t) hbD z hz
    rwa [hbinv] at this
  have hdD : (t * a⁻¹ * t) * h x * a ∈ D :=
    D.mul_mem (D.mul_mem (hbinv ▸ D.inv_mem hbD) hhD) haD
  obtain ⟨e₁, e₂, e₃⟩ := fgh_eq_of_canonical hsplit hfact hQM hDM hmem heq
    hconjQ hconj1 hconjM (hconjMem _ hgQ) hdD (hconjMem _ hfQ)
    (canonical_conj ht heq hxQ hx1)
  exact ⟨by rw [e₁, hbinv], by rw [e₂, hbinv], by rw [e₃, hbinv]⟩

end OddOrder.GroupTheory.RankOneBNPair
