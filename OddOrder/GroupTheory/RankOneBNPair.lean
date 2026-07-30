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

The existence and uniqueness rest on just a handful of structural facts, collected in
`Setup`, which is what this file takes as its hypothesis rather than re-deriving them
from double transitivity:

* `M = Q ⋊ D`, i.e. every element of `M` is uniquely `q · d`;
* every element of `L − M` is uniquely `a · t · b` with `a ∈ M`, `b ∈ Q`
  (Peterfalvi Ch. I §1, Proposition 4);
* `t x t ∉ M` and `t x ∉ M` for `x ∈ Q^#`, which is where `Q^t ∩ M = 1` enters.

The chapter uses these mappings to pin down `G` in the characterization of
`PSU(3,q)`.

## Main results

* `Setup.exists_fgh` / `IsFGH.unique` — the mappings exist and are unique.
* `IsFGH.f_ne_one`, `IsFGH.g_ne_one` — `f` and `g` really map `Q^#` into `Q^#`.
* `hOne`, `hTwo`, `hThree` — the identities (H1)–(H4).
* `hFive` — the identity (H5), `(f ∘ j)³(x) = x^{h(x)⁻¹}` for `j : x ↦ x⁻¹`.
* `hSix` — the identity (H6), the addition formulas for `f`, `g`, `h` at `xy`.
* `Setup.closure_M_union_t`, `Setup.closure_conj_Q` — `L = ⟨M, t⟩` and
  `⟨Q^x | x ∈ L⟩ = ⟨Q, Q^t⟩`, the generation half of the Lemma of §1.
* `IsFGH.dOrbitRel_f`, `IsFGH.dOrbitRel_fj_cube` — `⟨f, j⟩` acts on the `D`-orbits of
  `Q^#` as a quotient of the dihedral group of order `6`.
* `coordsEquiv`, `coords_smul_t_some`, `coords_smul_some_of_mem_M` — the permutation
  model `X ≅ Q ∪ {a}` of the Lemma of §1, in which `t` acts by `f` and `M` acts
  through its `Q ⋊ D` structure.

## Implementation notes

The `t`-twist in (H3)–(H6) is essential: `D = M ∩ M^t` is normalized by `t` but need
not be centralized, so `a^t ≠ a` in general.  The `pdftotext` extraction of p. 122
silently drops these superscript `t`'s; the statements here follow the page image.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.RankOneBNPair

universe u

variable {L : Type u} [Group L] {M Q D : Subgroup L} {t : L}

/-- The standing hypotheses of Peterfalvi Part II, Ch. IV §1 — a rank-one split
BN-pair, in the form the calculation actually uses.

Double transitivity is not assumed directly: what the argument needs is the pair of
unique factorizations (`split`, `fact`) together with the two non-membership facts
(`tconj`, `tleft`) coming from `Q^t ∩ M = 1`. -/
structure Setup (M Q D : Subgroup L) (t : L) : Prop where
  /-- `Q ≤ M`. -/
  QM : Q ≤ M
  /-- `D ≤ M`. -/
  DM : D ≤ M
  /-- `t` is an involution. -/
  invol : t * t = 1
  /-- `D = M ∩ M^t` is normalized by `t`. -/
  Dstab : ∀ d ∈ D, t * d * t ∈ D
  /-- `D` normalizes `Q`; part of the semidirect decomposition `M = Q ⋊ D`. -/
  DQ : ∀ d ∈ D, ∀ q ∈ Q, d⁻¹ * q * d ∈ Q
  /-- `M = Q ⋊ D`: every element of `M` is uniquely a product `q · d`. -/
  split : ∀ a ∈ M, ∃! p : ↥Q × ↥D, a = (p.1 : L) * (p.2 : L)
  /-- Every element of `L − M` is uniquely `a · t · b` with `a ∈ M` and `b ∈ Q`
  (Peterfalvi Ch. I §1, Proposition 4). -/
  fact : ∀ y : L, y ∉ M → ∃! p : ↥M × ↥Q, y = (p.1 : L) * t * (p.2 : L)
  /-- `t ∉ M`: Peterfalvi's `t` is an involution in `L − M`. -/
  tnotmem : t ∉ M
  /-- `t x t ∉ M` for `x ∈ Q^#`; this is `Q^t ∩ M = 1`. -/
  tconj : ∀ x ∈ Q, x ≠ 1 → t * x * t ∉ M
  /-- `t x ∉ M` for `x ∈ Q^#`; equivalently `t x t ∉ M t`.  This is what forces `f`
  and `g` to take values in `Q^#` rather than merely in `Q`. -/
  tleft : ∀ x ∈ Q, x ≠ 1 → t * x ∉ M

namespace Setup

theorem tinv (hS : Setup M Q D t) : t⁻¹ = t := inv_eq_of_mul_eq_one_right hS.invol

theorem tright (hS : Setup M Q D t) {x : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    x * t ∉ M := by
  intro hc
  refine hS.tleft x⁻¹ (Q.inv_mem hxQ) (fun hcc => hx1 (inv_eq_one.mp hcc)) ?_
  have e : t * x⁻¹ = (x * t)⁻¹ := by rw [mul_inv_rev, hS.tinv]
  rw [e]
  exact M.inv_mem hc

end Setup

/-! ## Generation

The two generation facts used at the end of the Lemma of Ch. IV §1 (p. 123):
`L = ⟨M, t⟩` and `⟨Q^x | x ∈ L⟩ = ⟨Q, Q^{tx} | x ∈ Q⟩ = ⟨Q, Q^t⟩`.  Neither needs the
mappings `f, g, h`; both are immediate from the factorization `L = M ∪ M t Q`.
-/

/-- `Q` is normal in `M`, the remaining half of `M = Q ⋊ D`: writing `m = q · d`,
conjugation by `q` preserves `Q` trivially and conjugation by `d` does by `Setup.DQ`. -/
theorem Setup.conj_mem_Q (hS : Setup M Q D t) {m : L} (hm : m ∈ M) {q : L}
    (hq : q ∈ Q) : m⁻¹ * q * m ∈ Q := by
  obtain ⟨r, hr, -⟩ := hS.split m hm
  rw [hr]
  have e : ((r.1 : L) * (r.2 : L))⁻¹ * q * ((r.1 : L) * (r.2 : L))
      = (r.2 : L)⁻¹ * ((r.1 : L)⁻¹ * q * (r.1 : L)) * (r.2 : L) := by group
  rw [e]
  exact hS.DQ _ r.2.2 _ (Q.mul_mem (Q.mul_mem (Q.inv_mem r.1.2) hq) r.1.2)

/-- **`L = ⟨M, t⟩`** (Peterfalvi Part II, Ch. IV §1, p. 123).  Every element outside
`M` is `a · t · b` with `a ∈ M` and `b ∈ Q ≤ M`. -/
theorem Setup.closure_M_union_t (hS : Setup M Q D t) :
    Subgroup.closure ((M : Set L) ∪ {t}) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  by_cases hy : y ∈ M
  · exact Subgroup.subset_closure (Or.inl hy)
  · obtain ⟨p, hp, -⟩ := hS.fact y hy
    rw [hp]
    exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl p.1.2))
      (Subgroup.subset_closure (Or.inr rfl)))
      (Subgroup.subset_closure (Or.inl (hS.QM p.2.2)))

/-- **`⟨Q^x | x ∈ L⟩ = ⟨Q, Q^t⟩`** (Peterfalvi Part II, Ch. IV §1, p. 123).

For `y ∈ M` one has `Q^y = Q`, and for `y = a t b` outside `M` one has
`Q^y = (Q^a)^{tb} = (Q^t)^b`, so only `Q` and `Q^t` are ever needed. -/
theorem Setup.closure_conj_Q (hS : Setup M Q D t) :
    Subgroup.closure (⋃ y : L, ((fun q => y⁻¹ * q * y) '' (Q : Set L)))
      = Subgroup.closure ((Q : Set L) ∪ (fun z => t * z * t) '' (Q : Set L)) := by
  set N := Subgroup.closure ((Q : Set L) ∪ (fun z => t * z * t) '' (Q : Set L)) with hNdef
  have hQN : ∀ z ∈ Q, z ∈ N := fun z hz => Subgroup.subset_closure (Or.inl hz)
  have hQtN : ∀ z ∈ Q, t * z * t ∈ N := fun z hz =>
    Subgroup.subset_closure (Or.inr ⟨z, hz, rfl⟩)
  -- the key computation: every `L`-conjugate of an element of `Q` lies in `N`
  have key : ∀ y q : L, q ∈ Q → y⁻¹ * q * y ∈ N := by
    intro y q hq
    by_cases hy : y ∈ M
    · exact hQN _ (hS.conj_mem_Q hy hq)
    · obtain ⟨p, hp, -⟩ := hS.fact y hy
      have hqa : (p.1 : L)⁻¹ * q * (p.1 : L) ∈ Q := hS.conj_mem_Q p.1.2 hq
      have e : y⁻¹ * q * y
          = (p.2 : L)⁻¹ * (t * ((p.1 : L)⁻¹ * q * (p.1 : L)) * t) * (p.2 : L) := by
        rw [hp]
        have e' : ((p.1 : L) * t * (p.2 : L))⁻¹ * q * ((p.1 : L) * t * (p.2 : L))
            = (p.2 : L)⁻¹ * (t⁻¹ * ((p.1 : L)⁻¹ * q * (p.1 : L)) * t) * (p.2 : L) := by
          group
        rwa [hS.tinv] at e'
      rw [e]
      exact N.mul_mem (N.mul_mem (N.inv_mem (hQN _ p.2.2)) (hQtN _ hqa)) (hQN _ p.2.2)
  refine le_antisymm ((Subgroup.closure_le N).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
  · rintro w hw
    simp only [Set.mem_iUnion, Set.mem_image] at hw
    obtain ⟨y, q, hq, rfl⟩ := hw
    exact key y q hq
  · rintro w (hw | ⟨z, hz, rfl⟩)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨1, ⟨w, hw, by group⟩⟩)
    · refine Subgroup.subset_closure (Set.mem_iUnion.2 ⟨t, ⟨z, hz, ?_⟩⟩)
      rw [hS.tinv]

/-- The defining property of the triple `f, g, h` (Peterfalvi Part II, Ch. IV §1,
p. 122): `t x t = g(x) h(x) t f(x)` for `x ∈ Q^#`, with `f x, g x ∈ Q` and
`h x ∈ D`. -/
structure IsFGH (M Q D : Subgroup L) (t : L) (f g h : L → L) : Prop where
  /-- The values lie where they should. -/
  mem : ∀ x ∈ Q, x ≠ 1 → f x ∈ Q ∧ g x ∈ Q ∧ h x ∈ D
  /-- The defining equation. -/
  eq : ∀ x ∈ Q, x ≠ 1 → t * x * t = g x * h x * t * f x

variable {f g h : L → L} {x a : L}

namespace IsFGH

theorem f_mem (H : IsFGH M Q D t f g h) (hxQ : x ∈ Q) (hx1 : x ≠ 1) : f x ∈ Q :=
  (H.mem x hxQ hx1).1

theorem g_mem (H : IsFGH M Q D t f g h) (hxQ : x ∈ Q) (hx1 : x ≠ 1) : g x ∈ Q :=
  (H.mem x hxQ hx1).2.1

theorem h_mem (H : IsFGH M Q D t f g h) (hxQ : x ∈ Q) (hx1 : x ≠ 1) : h x ∈ D :=
  (H.mem x hxQ hx1).2.2

/-- `f` maps `Q^#` into `Q^#`: if `f x = 1` then `t x = g(x) h(x) ∈ M`, contradicting
`Setup.tleft`. -/
theorem f_ne_one (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) : f x ≠ 1 := by
  intro hc
  have e := H.eq x hxQ hx1
  rw [hc, mul_one] at e
  refine hS.tleft x hxQ hx1 ?_
  have key : t * x = g x * h x := by
    calc t * x = t * x * (t * t) := by rw [hS.invol, mul_one]
    _ = t * x * t * t := by group
    _ = g x * h x * t * t := by rw [e]
    _ = g x * h x * (t * t) := by group
    _ = g x * h x := by rw [hS.invol, mul_one]
  rw [key]
  exact M.mul_mem (hS.QM (H.g_mem hxQ hx1)) (hS.DM (H.h_mem hxQ hx1))

/-- `g` maps `Q^#` into `Q^#`: if `g x = 1` then `x t = (t h(x) t) f(x) ∈ M`,
contradicting `Setup.tright`. -/
theorem g_ne_one (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) : g x ≠ 1 := by
  intro hc
  have e := H.eq x hxQ hx1
  rw [hc, one_mul] at e
  refine hS.tright hxQ hx1 ?_
  have key : x * t = t * h x * t * f x := by
    calc x * t = t * t * x * t := by rw [hS.invol, one_mul]
    _ = t * (t * x * t) := by group
    _ = t * (h x * t * f x) := by rw [e]
    _ = t * h x * t * f x := by group
  rw [key]
  exact M.mul_mem (hS.DM (hS.Dstab _ (H.h_mem hxQ hx1))) (hS.QM (H.f_mem hxQ hx1))

end IsFGH

/-- **The mappings `f`, `g`, `h` exist** (Peterfalvi Part II, Ch. IV §1, p. 122).

For `x ∈ Q^#` the element `t x t` lies outside `M`, so it factors uniquely as
`a · t · b` with `a ∈ M` and `b ∈ Q`; splitting `a = g(x) · h(x)` along `M = Q ⋊ D`
gives the defining equation `t x t = g(x) h(x) t f(x)`. -/
theorem Setup.exists_fgh (hS : Setup M Q D t) :
    ∃ f g h : L → L, IsFGH M Q D t f g h := by
  classical
  have key : ∀ x : L, ∃ gx hx fx : L,
      x ∈ Q → x ≠ 1 →
        (gx ∈ Q ∧ hx ∈ D ∧ fx ∈ Q ∧ t * x * t = gx * hx * t * fx) := by
    intro x
    by_cases hx : x ∈ Q ∧ x ≠ 1
    · obtain ⟨p, hp, -⟩ := hS.fact (t * x * t) (hS.tconj x hx.1 hx.2)
      obtain ⟨r, hr, -⟩ := hS.split (p.1 : L) p.1.2
      refine ⟨(r.1 : L), (r.2 : L), (p.2 : L), fun _ _ => ⟨r.1.2, r.2.2, p.2.2, ?_⟩⟩
      rw [hp, hr]
    · exact ⟨1, 1, 1, fun h1 h2 => absurd ⟨h1, h2⟩ hx⟩
  choose g h f hfgh using key
  exact ⟨f, g, h,
    fun x hxQ hx1 => ⟨(hfgh x hxQ hx1).2.2.1, (hfgh x hxQ hx1).1, (hfgh x hxQ hx1).2.1⟩,
    fun x hxQ hx1 => (hfgh x hxQ hx1).2.2.2⟩

/-! ## Uniqueness, and the read-off lemma

Every identity below is proved by the same two-step pattern: exhibit a factorization
`t y t = p · d · t · q` with `p ∈ Q`, `d ∈ D`, `q ∈ Q`, then invoke uniqueness.
`fgh_eq_of_canonical` packages the second step, so each identity reduces to the pure
group-theoretic rearrangement recorded in the `canonical_*` lemmas.
-/

/-- Read-off lemma: **any** canonical factorization `t y t = p · d · t · q` with
`p ∈ Q`, `d ∈ D` and `q ∈ Q` is *the* one produced by `f, g, h`.

Both unique factorizations are used: `Setup.fact` identifies the `M`-part `p d` and
the `Q`-part `q`, and `Setup.split` then separates `p` from `d` inside `M = Q ⋊ D`. -/
theorem fgh_eq_of_canonical (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    {y p d q : L} (hyQ : y ∈ Q) (hy1 : y ≠ 1)
    (hp : p ∈ Q) (hd : d ∈ D) (hq : q ∈ Q)
    (hcan : t * y * t = p * d * t * q) :
    f y = q ∧ g y = p ∧ h y = d := by
  classical
  obtain ⟨hfQ, hgQ, hhD⟩ := H.mem y hyQ hy1
  obtain ⟨w, -, huniq⟩ := hS.fact (t * y * t) (hS.tconj y hyQ hy1)
  have hM₁ : g y * h y ∈ M := M.mul_mem (hS.QM hgQ) (hS.DM hhD)
  have hM₂ : p * d ∈ M := M.mul_mem (hS.QM hp) (hS.DM hd)
  have e₁ := huniq (⟨⟨g y * h y, hM₁⟩, ⟨f y, hfQ⟩⟩) (by rw [H.eq y hyQ hy1])
  have e₂ := huniq (⟨⟨p * d, hM₂⟩, ⟨q, hq⟩⟩) (by rw [hcan])
  have hpair := e₁.trans e₂.symm
  have hfst : g y * h y = p * d :=
    congrArg (Subtype.val (p := fun z => z ∈ M)) (congrArg Prod.fst hpair)
  have hsnd : f y = q :=
    congrArg (Subtype.val (p := fun z => z ∈ Q)) (congrArg Prod.snd hpair)
  obtain ⟨w', -, huniq'⟩ := hS.split (g y * h y) hM₁
  have d₁ := huniq' (⟨⟨g y, hgQ⟩, ⟨h y, hhD⟩⟩) rfl
  have d₂ := huniq' (⟨⟨p, hp⟩, ⟨d, hd⟩⟩) hfst
  have hpair' := d₁.trans d₂.symm
  exact ⟨hsnd,
    congrArg (Subtype.val (p := fun z => z ∈ Q)) (congrArg Prod.fst hpair'),
    congrArg (Subtype.val (p := fun z => z ∈ D)) (congrArg Prod.snd hpair')⟩

/-- **Uniqueness of `f`, `g`, `h`**: two triples satisfying the defining equation
agree on `Q^#`. -/
theorem IsFGH.unique (hS : Setup M Q D t) {f₁ g₁ h₁ f₂ g₂ h₂ : L → L}
    (H₁ : IsFGH M Q D t f₁ g₁ h₁) (H₂ : IsFGH M Q D t f₂ g₂ h₂)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    f₁ x = f₂ x ∧ g₁ x = g₂ x ∧ h₁ x = h₂ x := by
  obtain ⟨e₁, e₂, e₃⟩ := fgh_eq_of_canonical hS H₁ hxQ hx1
    (H₂.g_mem hxQ hx1) (H₂.h_mem hxQ hx1) (H₂.f_mem hxQ hx1) (H₂.eq x hxQ hx1)
  exact ⟨e₁, e₂, e₃⟩

/-! ## The three canonical factorizations

Each is a pure rearrangement of the defining equation using only `t * t = 1`.  Note
that `group` cannot use that relation; writing the *second* `t` of each conjugating
pair as `t⁻¹` turns these into genuine free-group identities, after which
`Setup.tinv` restores the displayed form.
-/

/-- Inverting `t x t = g(x) h(x) t f(x)` and moving `h(x)⁻¹` across `t`. -/
theorem canonical_inv (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    t * x⁻¹ * t = (f x)⁻¹ * (t * (h x)⁻¹ * t) * t * (g x)⁻¹ := by
  have hinv : t * x⁻¹ * t = (t * x * t)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, hS.tinv]
    group
  rw [hinv, H.eq x hxQ hx1, mul_inv_rev, mul_inv_rev, mul_inv_rev, hS.tinv]
  have hcancel : (f x)⁻¹ * (t * (h x)⁻¹ * t) * t * (g x)⁻¹
      = (f x)⁻¹ * (t * (h x)⁻¹ * (t * t)) * (g x)⁻¹ := by group
  rw [hcancel, hS.invol]
  group

/-- Solving `t x t = g(x) h(x) t f(x)` for `t f(x) t`; the result `h(x)⁻¹ g(x)⁻¹ t x`
is already canonical, its `Q`-part being `x` itself. -/
theorem canonical_f (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    t * f x * t = ((h x)⁻¹ * (g x)⁻¹ * h x) * (h x)⁻¹ * t * x := by
  have e2 : (h x)⁻¹ * (g x)⁻¹ * (t * x * t) * t
      = (h x)⁻¹ * (g x)⁻¹ * (g x * h x * t * f x) * t := by
    rw [H.eq x hxQ hx1]
  have lhs : (h x)⁻¹ * (g x)⁻¹ * (t * x * t) * t
      = (h x)⁻¹ * (g x)⁻¹ * t * x * (t * t) := by group
  have rhs : (h x)⁻¹ * (g x)⁻¹ * (g x * h x * t * f x) * t = t * f x * t := by group
  rw [lhs, rhs, hS.invol, mul_one] at e2
  rw [← e2]
  group

/-- Conjugating the defining equation by `t`: writing `b = a^t = t a t`, we get
`t x^a t = (g(x)^b) · (b⁻¹ h(x) a) · t · (f(x)^b)`. -/
theorem canonical_conj (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    t * (a⁻¹ * x * a) * t
      = ((t * a⁻¹ * t) * g x * (t * a * t)) * ((t * a⁻¹ * t) * h x * a) * t *
        ((t * a⁻¹ * t) * f x * (t * a * t)) := by
  have hexp : t * (a⁻¹ * x * a) * t
      = (t * a⁻¹ * t) * (t * x * t) * (t * a * t) := by
    have e : t * (a⁻¹ * x * a) * t
        = (t * a⁻¹ * t⁻¹) * (t * x * t⁻¹) * (t * a * t) := by group
    rwa [hS.tinv] at e
  have key : ∀ u v w : L,
      (t * a⁻¹ * t) * (u * v * t * w) * (t * a * t)
      = ((t * a⁻¹ * t) * u * (t * a * t)) * ((t * a⁻¹ * t) * v * a) * t *
        ((t * a⁻¹ * t) * w * (t * a * t)) := by
    intro u v w
    have e : (t⁻¹ * a⁻¹ * t) * (u * v * t * w) * (t⁻¹ * a * t)
        = ((t⁻¹ * a⁻¹ * t) * u * (t⁻¹ * a * t)) * ((t⁻¹ * a⁻¹ * t) * v * a) * t *
          ((t⁻¹ * a⁻¹ * t) * w * (t⁻¹ * a * t)) := by group
    rwa [hS.tinv] at e
  rw [hexp, H.eq x hxQ hx1, key]

/-! ## The identities (H1)–(H5) -/

/-- **(H1)** `f(x⁻¹) = g(x)⁻¹`, together with its `g`-companion `g(x⁻¹) = f(x)⁻¹` and
**(H4)**'s `h(x⁻¹) = h(x)^{-t}` (Peterfalvi Part II, Ch. IV §1, p. 122).

All three fall out of the single canonical factorization `canonical_inv`, whose
`D`-part is `t h(x)⁻¹ t = (h(x)^t)⁻¹` — an element of `D` because `D = M ∩ M^t`. -/
theorem hOne (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    f x⁻¹ = (g x)⁻¹ ∧ g x⁻¹ = (f x)⁻¹ ∧ h x⁻¹ = (t * h x * t)⁻¹ := by
  have hdD : t * (h x)⁻¹ * t ∈ D := hS.Dstab _ (D.inv_mem (H.h_mem hxQ hx1))
  have hdeq : t * (h x)⁻¹ * t = (t * h x * t)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, hS.tinv]
    group
  obtain ⟨e₁, e₂, e₃⟩ := fgh_eq_of_canonical hS H
    (Q.inv_mem hxQ) (fun hc => hx1 (inv_eq_one.mp hc))
    (Q.inv_mem (H.f_mem hxQ hx1)) hdD (Q.inv_mem (H.g_mem hxQ hx1))
    (canonical_inv hS H hxQ hx1)
  exact ⟨e₁, e₂, hdeq ▸ e₃⟩

/-- **(H2)** `f(f(x)) = x`, together with **(H4)**'s `h(f(x)) = h(x)⁻¹`
(Peterfalvi Part II, Ch. IV §1, p. 122).

`canonical_f` says `t f(x) t = h(x)⁻¹ g(x)⁻¹ t x`, which is *already* canonical:
splitting `h(x)⁻¹ g(x)⁻¹` as `(g(x)⁻¹)^{h(x)} · h(x)⁻¹` inside `M = Q ⋊ D` reads off
`f(f(x)) = x` and `h(f(x)) = h(x)⁻¹` at once. -/
theorem hTwo (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    f (f x) = x ∧ g (f x) = (h x)⁻¹ * (g x)⁻¹ * h x ∧ h (f x) = (h x)⁻¹ :=
  fgh_eq_of_canonical hS H (H.f_mem hxQ hx1) (H.f_ne_one hS hxQ hx1)
    (hS.DQ (h x) (H.h_mem hxQ hx1) (g x)⁻¹ (Q.inv_mem (H.g_mem hxQ hx1)))
    (D.inv_mem (H.h_mem hxQ hx1)) hxQ (canonical_f hS H hxQ hx1)

/-- **(H3)** `f(x^a) = f(x)^{a^t}` for `a ∈ D`, together with its `g`-companion
`g(x^a) = g(x)^{a^t}` and **(H4)**'s `h(x^a) = a^{-t} h(x) a`
(Peterfalvi Part II, Ch. IV §1, p. 122).

Conjugating the defining equation by `t` turns `a` into `a^t`, which again lies in
`D` because `D = M ∩ M^t`; the `M`-part `(g(x)^{a^t}) · (a^{-t} h(x) a)` is already
displayed in its `Q ⋊ D` form by `canonical_conj`. -/
theorem hThree (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) (haD : a ∈ D) :
    f (a⁻¹ * x * a) = (t * a * t)⁻¹ * f x * (t * a * t) ∧
      g (a⁻¹ * x * a) = (t * a * t)⁻¹ * g x * (t * a * t) ∧
      h (a⁻¹ * x * a) = (t * a * t)⁻¹ * h x * a := by
  have hbD : t * a * t ∈ D := hS.Dstab a haD
  have hbinv : (t * a * t)⁻¹ = t * a⁻¹ * t := by
    rw [mul_inv_rev, mul_inv_rev, hS.tinv]
    group
  have hconjMem : ∀ z ∈ Q, (t * a⁻¹ * t) * z * (t * a * t) ∈ Q := by
    intro z hz
    have := hS.DQ (t * a * t) hbD z hz
    rwa [hbinv] at this
  have hconjQ : a⁻¹ * x * a ∈ Q := hS.DQ a haD x hxQ
  have hconj1 : a⁻¹ * x * a ≠ 1 := by
    intro hc
    refine hx1 ?_
    have e : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
    rw [hc] at e
    simpa using e
  have hdD : (t * a⁻¹ * t) * h x * a ∈ D :=
    D.mul_mem (D.mul_mem (hbinv ▸ D.inv_mem hbD) (H.h_mem hxQ hx1)) haD
  obtain ⟨e₁, e₂, e₃⟩ := fgh_eq_of_canonical hS H hconjQ hconj1
    (hconjMem _ (H.g_mem hxQ hx1)) hdD (hconjMem _ (H.f_mem hxQ hx1))
    (canonical_conj hS H hxQ hx1)
  exact ⟨by rw [e₁, hbinv], by rw [e₂, hbinv], by rw [e₃, hbinv]⟩

/-- **(H5)** `(f ∘ j)³(x) = x^{h(x)⁻¹}`, where `j : x ↦ x⁻¹`
(Peterfalvi Part II, Ch. IV §1, p. 122).

As maps on `Q^#`, (H1) says `f ∘ j = j ∘ g` and `g ∘ j = j ∘ f`, so
`(f ∘ j)³ = j ∘ (g ∘ f) ∘ g`; (H2) supplies `g ∘ f` as conjugation of `j ∘ g` by
`h`, and the two auxiliary facts `g(g(x)) = x` and `h(g(x)) = h(x)⁻¹` — both
consequences of (H1), (H2) and `t² = 1` — collapse the result to `h(x) x h(x)⁻¹`. -/
theorem hFive (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    f ((f ((f x⁻¹)⁻¹))⁻¹) = h x * x * (h x)⁻¹ := by
  have hxinvQ : x⁻¹ ∈ Q := Q.inv_mem hxQ
  have hxinv1 : x⁻¹ ≠ 1 := fun hc => hx1 (inv_eq_one.mp hc)
  obtain ⟨o₁, -, o₃⟩ := hOne hS H hxQ hx1
  have hgQ : g x ∈ Q := H.g_mem hxQ hx1
  have hg1 : g x ≠ 1 := H.g_ne_one hS hxQ hx1
  have harg : (f x⁻¹)⁻¹ = g x := by rw [o₁, inv_inv]
  -- `g ∘ g = id` on `Q^#`
  have hB : g (g x) = x := by
    have e := (hOne hS H hgQ hg1).1
    rw [← o₁, (hTwo hS H hxinvQ hxinv1).1] at e
    exact (inv_injective e).symm
  -- `h(g(x)) = h(x)⁻¹`
  have hC : h (g x) = (h x)⁻¹ := by
    have hfQ' : f x⁻¹ ∈ Q := H.f_mem hxinvQ hxinv1
    have hf1' : f x⁻¹ ≠ 1 := H.f_ne_one hS hxinvQ hxinv1
    have hval : h (f x⁻¹) = t * h x * t := by
      rw [(hTwo hS H hxinvQ hxinv1).2.2, o₃, inv_inv]
    have hstep := (hOne hS H hfQ' hf1').2.2
    rw [hval, harg] at hstep
    rw [hstep]
    have e : t * (t * h x * t) * t = t * t * h x * (t * t) := by group
    rw [e, hS.invol, one_mul, mul_one]
  rw [harg, (hOne hS H (H.f_mem hgQ hg1) (H.f_ne_one hS hgQ hg1)).1,
    (hTwo hS H hgQ hg1).2.1, hB, hC]
  group

/-! ## (H6): the addition formulas

For `x, y ∈ Q^#` with `xy ≠ 1`, splitting `t (xy) t = (t x t)(t y t)` and pushing the
inner `f(x) g(y)` through `t` expresses `f, g, h` at `xy` in terms of their values at
`x`, `y` and `z = f(x) g(y)`.
-/

/-- The two-factor expansion `t (xy) t = g(x) h(x) · (t z t) · (t h(y) t) · f(y)`
with `z = f(x) g(y)`, obtained from `t (xy) t = (t x t)(t y t)` by inserting `t t = 1`
around `z`.  This does not yet require `z ≠ 1`. -/
theorem expand_mul (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    {x y : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hyQ : y ∈ Q) (hy1 : y ≠ 1) :
    t * (x * y) * t
      = g x * h x * (t * (f x * g y) * t) * (t * h y * t) * f y := by
  have e1 : t * (x * y) * t = (t * x * t) * (t * y * t) := by
    have e : t * (x * y) * t = (t * x * t⁻¹) * (t * y * t) := by group
    rwa [hS.tinv] at e
  have e3 : (g x * h x * t * f x) * (g y * h y * t * f y)
      = g x * h x * (t * (f x * g y) * t) * (t * h y * t) * f y := by
    have e : (g x * h x * t * f x) * (g y * h y * t * f y)
        = g x * h x * (t * (f x * g y) * t⁻¹) * (t * h y * t) * f y := by group
    rwa [hS.tinv] at e
  rw [e1, H.eq x hxQ hx1, H.eq y hyQ hy1, e3]

/-- **(H6), first part**: `f(x) g(y) ≠ 1` whenever `x, y, xy ∈ Q^#`.

Otherwise the middle factor `t (f(x)g(y)) t` of `expand_mul` collapses to `1`, leaving
`t (xy) t = g(x) h(x) (t h(y) t) f(y) ∈ M`, which contradicts `Q^t ∩ M = 1`. -/
theorem f_mul_g_ne_one (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    {x y : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hyQ : y ∈ Q) (hy1 : y ≠ 1)
    (hxy1 : x * y ≠ 1) : f x * g y ≠ 1 := by
  intro hc
  refine hS.tconj (x * y) (Q.mul_mem hxQ hyQ) hxy1 ?_
  have e : t * (x * y) * t = g x * h x * (t * h y * t) * f y := by
    rw [expand_mul hS H hxQ hx1 hyQ hy1, hc]
    have e' : g x * h x * (t * 1 * t) * (t * h y * t) * f y
        = g x * h x * (t * t) * ((t * h y * t) * f y) := by group
    rw [e', hS.invol]
    group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.mul_mem (hS.QM (H.g_mem hxQ hx1)) (hS.DM (H.h_mem hxQ hx1)))
    (hS.DM (hS.Dstab _ (H.h_mem hyQ hy1)))) (hS.QM (H.f_mem hyQ hy1))

/-- The canonical factorization of `t (xy) t`: expanding `t z t` by the defining
equation and moving `h(x)` past `g(z)`, respectively `h(y)` past `t`, puts it in the
form `p · d · t · q` with `p ∈ Q`, `d ∈ D`, `q ∈ Q`. -/
theorem canonical_mul (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    {x y : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hyQ : y ∈ Q) (hy1 : y ≠ 1)
    (hz1 : f x * g y ≠ 1) :
    t * (x * y) * t
      = (g x * (h x * g (f x * g y) * (h x)⁻¹)) *
        (h x * h (f x * g y) * h y) * t *
        ((t * h y * t)⁻¹ * f (f x * g y) * (t * h y * t) * f y) := by
  have hzQ : f x * g y ∈ Q := Q.mul_mem (H.f_mem hxQ hx1) (H.g_mem hyQ hy1)
  have hbinv : (t * h y * t)⁻¹ = t * (h y)⁻¹ * t := by
    rw [mul_inv_rev, mul_inv_rev, hS.tinv]
    group
  have e5 : g x * h x * (g (f x * g y) * h (f x * g y) * t * f (f x * g y)) *
        (t * h y * t) * f y
      = (g x * (h x * g (f x * g y) * (h x)⁻¹)) *
        (h x * h (f x * g y) * h y) * t *
        ((t * (h y)⁻¹ * t) * f (f x * g y) * (t * h y * t) * f y) := by
    have e : g x * h x * (g (f x * g y) * h (f x * g y) * t * f (f x * g y)) *
          (t * h y * t) * f y
        = (g x * (h x * g (f x * g y) * (h x)⁻¹)) *
          (h x * h (f x * g y) * h y) * t *
          ((t⁻¹ * (h y)⁻¹ * t) * f (f x * g y) * (t * h y * t) * f y) := by group
    rwa [hS.tinv] at e
  rw [expand_mul hS H hxQ hx1 hyQ hy1, H.eq _ hzQ hz1, e5, hbinv]

/-- **(H6)** (Peterfalvi Part II, Ch. IV §1, p. 122–123).  For `x, y ∈ Q^#` with
`xy ≠ 1`, writing `z = f(x) g(y)` (which is again in `Q^#`):

* `f(xy) = f(z)^{h(y)^t} f(y)`;
* `h(xy) = h(x) h(z) h(y)`;

together with the `g`-companion `g(xy) = g(x) · g(z)^{h(x)⁻¹}`. -/
theorem hSix (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    {x y : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hyQ : y ∈ Q) (hy1 : y ≠ 1)
    (hxy1 : x * y ≠ 1) :
    f x * g y ≠ 1 ∧
      f (x * y) = (t * h y * t)⁻¹ * f (f x * g y) * (t * h y * t) * f y ∧
      g (x * y) = g x * (h x * g (f x * g y) * (h x)⁻¹) ∧
      h (x * y) = h x * h (f x * g y) * h y := by
  have hne : f x * g y ≠ 1 := f_mul_g_ne_one hS H hxQ hx1 hyQ hy1 hxy1
  have hzQ : f x * g y ∈ Q := Q.mul_mem (H.f_mem hxQ hx1) (H.g_mem hyQ hy1)
  have hp : g x * (h x * g (f x * g y) * (h x)⁻¹) ∈ Q := by
    refine Q.mul_mem (H.g_mem hxQ hx1) ?_
    have := hS.DQ (h x)⁻¹ (D.inv_mem (H.h_mem hxQ hx1)) (g (f x * g y)) (H.g_mem hzQ hne)
    rwa [inv_inv] at this
  have hd : h x * h (f x * g y) * h y ∈ D :=
    D.mul_mem (D.mul_mem (H.h_mem hxQ hx1) (H.h_mem hzQ hne)) (H.h_mem hyQ hy1)
  have hq : (t * h y * t)⁻¹ * f (f x * g y) * (t * h y * t) * f y ∈ Q :=
    Q.mul_mem (hS.DQ (t * h y * t) (hS.Dstab _ (H.h_mem hyQ hy1))
      (f (f x * g y)) (H.f_mem hzQ hne)) (H.f_mem hyQ hy1)
  obtain ⟨e₁, e₂, e₃⟩ := fgh_eq_of_canonical hS H (Q.mul_mem hxQ hyQ) hxy1 hp hd hq
    (canonical_mul hS H hxQ hx1 hyQ hy1 hne)
  exact ⟨hne, e₁, e₂, e₃⟩

/-! ## The action of `⟨f, j⟩` on the `D`-orbits of `Q^#`

Peterfalvi Part II, Ch. IV §1, p. 123:

> We note that, by (H2), (H3) and (H5), `⟨f, j⟩` acts on the set of orbits of `Q^#`
> under `D`, and that the permutation group induced by `⟨f, j⟩` on this set is
> isomorphic to a quotient of the dihedral group of order 6.

Both maps descend to the orbit set — `j` trivially, `f` by (H3), whose twist `a ↦ a^t`
stays inside `D` — and there they satisfy `j² = f² = (f ∘ j)³ = 1`, which is exactly a
presentation of the dihedral group of order `6`.  The third relation is (H5): the
discrepancy `x^{h(x)⁻¹}` is invisible on orbits because `h(x)⁻¹ ∈ D`.

§2 uses this to transfer a fixed-point statement from `j` to `f` (step (5), p. 124).
-/

/-- The `D`-orbit relation on `Q^#`, in Peterfalvi's exponent convention
`x^d = d⁻¹ x d`. -/
def dOrbitRel (D : Subgroup L) (x y : L) : Prop := ∃ d ∈ D, y = d⁻¹ * x * d

namespace dOrbitRel

theorem refl (x : L) : dOrbitRel D x x := ⟨1, D.one_mem, by group⟩

theorem symm {x y : L} (hxy : dOrbitRel D x y) : dOrbitRel D y x := by
  obtain ⟨d, hd, rfl⟩ := hxy
  exact ⟨d⁻¹, D.inv_mem hd, by group⟩

theorem trans {x y z : L} (hxy : dOrbitRel D x y) (hyz : dOrbitRel D y z) :
    dOrbitRel D x z := by
  obtain ⟨d, hd, rfl⟩ := hxy
  obtain ⟨e, he, rfl⟩ := hyz
  exact ⟨d * e, D.mul_mem hd he, by group⟩

/-- `j : x ↦ x⁻¹` descends to the orbit set. -/
theorem inv {x y : L} (hxy : dOrbitRel D x y) : dOrbitRel D x⁻¹ y⁻¹ := by
  obtain ⟨d, hd, rfl⟩ := hxy
  exact ⟨d, hd, by group⟩

end dOrbitRel

/-- **`f` descends to the orbit set**, by (H3): conjugating `x` by `a ∈ D` conjugates
`f(x)` by `a^t`, which again lies in `D` because `D = M ∩ M^t`. -/
theorem IsFGH.dOrbitRel_f (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) {a : L} (haD : a ∈ D) :
    dOrbitRel D (f x) (f (a⁻¹ * x * a)) :=
  ⟨t * a * t, hS.Dstab a haD, (hThree hS H hxQ hx1 haD).1⟩

/-- **`(f ∘ j)³ = 1` on the orbit set**, by (H5): `(f ∘ j)³(x) = x^{h(x)⁻¹}` and
`h(x)⁻¹ ∈ D`. -/
theorem IsFGH.dOrbitRel_fj_cube (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    dOrbitRel D x (f ((f ((f x⁻¹)⁻¹))⁻¹)) :=
  ⟨(h x)⁻¹, D.inv_mem (H.h_mem hxQ hx1), by rw [hFive hS H hxQ hx1]; group⟩

/-! ## The permutation model

The rest of the Lemma of Ch. IV §1 (p. 123): *if `L` acts faithfully on `X` then
`⟨Q^x | x ∈ L⟩` is determined up to isomorphism by `Q` and `f`, and `L` is determined
up to isomorphism by `M = Q ⋊ D` and `f`.*

Peterfalvi identifies `X` with `Q ∪ {a}`, the element `x ∈ Q` naming the point `a t x`.
Here `X` is the coset space `L ⧸ M`, `a` is the coset of `1`, and `a t x` is the left
coset of `x⁻¹ t`.  The content of the Lemma is then the pair of formulas
`coords_smul_t` and `coords_smul_of_mem_M` below: **`t` acts by `f`** (interchanging
`a` with `1`), and `M` acts through its `Q ⋊ D` structure alone.  Since `L = ⟨M, t⟩`
(`Setup.closure_M_union_t`) and the action is faithful exactly when `M` has trivial
normal core (mathlib's `Subgroup.normalCore_eq_ker`), `L` is recovered inside
`Equiv.Perm X` from `M = Q ⋊ D` and `f`.
-/

/-- Coordinates on `X = L ⧸ M`: the point `a` (the coset of `1`) together with a copy
of `Q`, where `x ∈ Q` names the point `a t x` of Peterfalvi's right-action notation,
i.e. the left coset of `x⁻¹ t`. -/
def coords (M Q : Subgroup L) (t : L) : Option ↥Q → L ⧸ M
  | none => ((1 : L) : L ⧸ M)
  | some x => (((x : L)⁻¹ * t : L) : L ⧸ M)

@[simp] theorem coords_none : coords M Q t none = ((1 : L) : L ⧸ M) := rfl

@[simp] theorem coords_some (x : ↥Q) :
    coords M Q t (some x) = (((x : L)⁻¹ * t : L) : L ⧸ M) := rfl

/-- `coords` is a bijection: this is the identification `X ≅ Q ∪ {a}`. -/
theorem coords_bijective (hS : Setup M Q D t) :
    Function.Bijective (coords M Q t) := by
  constructor
  · rintro (_ | x) (_ | y) hxy
    · rfl
    · rw [coords_none, coords_some, QuotientGroup.eq] at hxy
      refine absurd ?_ hS.tnotmem
      have h1 : (y : L)⁻¹ * t ∈ M := by simpa using hxy
      simpa using M.mul_mem (hS.QM y.2) h1
    · rw [coords_some, coords_none, QuotientGroup.eq] at hxy
      refine absurd ?_ hS.tnotmem
      have h1 : t⁻¹ * (x : L) ∈ M := by simpa using hxy
      have h3 : t⁻¹ ∈ M := by
        simpa using M.mul_mem h1 (M.inv_mem (hS.QM x.2))
      rwa [hS.tinv] at h3
    · rw [coords_some, coords_some, QuotientGroup.eq] at hxy
      have e : ((x : L)⁻¹ * t)⁻¹ * ((y : L)⁻¹ * t) = t * ((x : L) * (y : L)⁻¹) * t := by
        have e' : ((x : L)⁻¹ * t)⁻¹ * ((y : L)⁻¹ * t)
            = t⁻¹ * ((x : L) * (y : L)⁻¹) * t := by group
        rwa [hS.tinv] at e'
      rw [e] at hxy
      by_cases hc : (x : L) * (y : L)⁻¹ = 1
      · exact congrArg some (Subtype.ext (mul_inv_eq_one.mp hc))
      · exact absurd hxy (hS.tconj _ (Q.mul_mem x.2 (Q.inv_mem y.2)) hc)
  · intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    by_cases hy : y ∈ M
    · exact ⟨none, by rw [coords_none, QuotientGroup.eq]; simpa using hy⟩
    · obtain ⟨p, hp, -⟩ := hS.fact y hy
      obtain ⟨r, hr, -⟩ := hS.split (p.1 : L) p.1.2
      refine ⟨some ⟨(r.1 : L)⁻¹, Q.inv_mem r.1.2⟩, ?_⟩
      rw [coords_some, hp, hr, inv_inv, QuotientGroup.eq]
      have e : ((r.1 : L) * t)⁻¹ * ((r.1 : L) * (r.2 : L) * t * (p.2 : L))
          = (t * (r.2 : L) * t) * (p.2 : L) := by
        have e' : ((r.1 : L) * t)⁻¹ * ((r.1 : L) * (r.2 : L) * t * (p.2 : L))
            = (t⁻¹ * (r.2 : L) * t) * (p.2 : L) := by group
        rwa [hS.tinv] at e'
      rw [e]
      exact M.mul_mem (hS.DM (hS.Dstab _ r.2.2)) (hS.QM p.2.2)

/-- The identification `X ≅ Q ∪ {a}` of Peterfalvi Part II, Ch. IV §1, p. 123. -/
noncomputable def coordsEquiv (hS : Setup M Q D t) : Option ↥Q ≃ L ⧸ M :=
  Equiv.ofBijective _ (coords_bijective hS)

@[simp] theorem coordsEquiv_apply (hS : Setup M Q D t) (o : Option ↥Q) :
    coordsEquiv hS o = coords M Q t o := rfl

/-! ### The action in coordinates

These three formulas are the content of the Lemma: `t` acts by `f` (interchanging the
point `a` with the point `1`), and `M` acts through its `Q ⋊ D` structure alone.
-/

/-- `t` maps the point `a` to the point `1`. -/
theorem coords_smul_t_none :
    (t : L) • coords M Q t (none : Option ↥Q) = coords M Q t (some 1) := by
  change ((t * (1 : L) : L) : L ⧸ M) = _
  rw [coords_some]
  simp

/-- ... and the point `1` back to `a`, `t` being an involution. -/
theorem coords_smul_t_one (hS : Setup M Q D t) :
    (t : L) • coords M Q t (some (1 : ↥Q)) = coords M Q t (none : Option ↥Q) := by
  change ((t * (((1 : ↥Q) : L)⁻¹ * t) : L) : L ⧸ M) = _
  rw [coords_none]
  have e : t * ((((1 : ↥Q) : L))⁻¹ * t) = t * t := by
    simp
  rw [e, hS.invol]

/-- **The action of `t` on `X` is determined by `f`** (Peterfalvi Part II, Ch. IV §1,
p. 123): in the coordinates `X ≅ Q ∪ {a}`, `t` sends the point `x` to the point
`f(x)`.

Indeed `t · (a t x) = a t x t = a · g(x)h(x) · t f(x) = a t f(x)`, because
`g(x) h(x) ∈ M` fixes `a`.  In left-coset form the same computation reads
`t · x⁻¹ t M = g(x⁻¹) h(x⁻¹) t f(x⁻¹) M = g(x⁻¹) t M`, and `g(x⁻¹) = f(x)⁻¹` by (H1). -/
theorem coords_smul_t_some (hS : Setup M Q D t) (H : IsFGH M Q D t f g h)
    {x : ↥Q} (hx1 : (x : L) ≠ 1) :
    (t : L) • coords M Q t (some x)
      = coords M Q t (some ⟨f (x : L), H.f_mem x.2 hx1⟩) := by
  have hxinvQ : (x : L)⁻¹ ∈ Q := Q.inv_mem x.2
  have hxinv1 : (x : L)⁻¹ ≠ 1 := fun hc => hx1 (inv_eq_one.mp hc)
  have hteq : t * ((x : L)⁻¹ * t)
      = (f (x : L))⁻¹ * h ((x : L)⁻¹) * t * f ((x : L)⁻¹) := by
    have e : t * ((x : L)⁻¹ * t) = t * (x : L)⁻¹ * t := by group
    rw [e, H.eq _ hxinvQ hxinv1, (hOne hS H x.2 hx1).2.1]
  change ((t * ((x : L)⁻¹ * t) : L) : L ⧸ M) = _
  rw [hteq, QuotientGroup.mk_mul_of_mem _ (hS.QM (H.f_mem hxinvQ hxinv1)),
    coords_some, QuotientGroup.eq]
  have e2 : ((f (x : L))⁻¹ * h ((x : L)⁻¹) * t)⁻¹ * ((f (x : L))⁻¹ * t)
      = t * (h ((x : L)⁻¹))⁻¹ * t := by
    have e' : ((f (x : L))⁻¹ * h ((x : L)⁻¹) * t)⁻¹ * ((f (x : L))⁻¹ * t)
        = t⁻¹ * (h ((x : L)⁻¹))⁻¹ * t := by group
    rwa [hS.tinv] at e'
  rw [e2]
  exact hS.DM (hS.Dstab _ (D.inv_mem (H.h_mem hxinvQ hxinv1)))

/-- `M` fixes the point `a`. -/
theorem coords_smul_none_of_mem_M {m : L} (hm : m ∈ M) :
    m • coords M Q t (none : Option ↥Q) = coords M Q t (none : Option ↥Q) := by
  change ((m * (1 : L) : L) : L ⧸ M) = _
  rw [coords_none, QuotientGroup.eq]
  simpa using M.inv_mem hm

/-- **The action of `M` on `X` is determined by `M = Q ⋊ D`** (Peterfalvi Part II,
Ch. IV §1, p. 123): the image of the point `x` under `m` is read off from the
`Q ⋊ D` decomposition `m x⁻¹ = q · d`, the `D`-part being absorbed by
`d t M = t (t d t) M = t M`. -/
theorem coords_smul_some_of_mem_M (hS : Setup M Q D t) (x : ↥Q)
    {m q d : L} (hq : q ∈ Q) (hd : d ∈ D) (hqd : m * (x : L)⁻¹ = q * d) :
    m • coords M Q t (some x) = coords M Q t (some ⟨q⁻¹, Q.inv_mem hq⟩) := by
  change ((m * ((x : L)⁻¹ * t) : L) : L ⧸ M) = _
  have e : m * ((x : L)⁻¹ * t) = q * d * t := by
    rw [← hqd]; group
  rw [e, coords_some, inv_inv, QuotientGroup.eq]
  have e2 : (q * d * t)⁻¹ * (q * t) = t * d⁻¹ * t := by
    have e' : (q * d * t)⁻¹ * (q * t) = t⁻¹ * d⁻¹ * t := by group
    rwa [hS.tinv] at e'
  rw [e2]
  exact hS.DM (hS.Dstab _ (D.inv_mem hd))

end OddOrder.GroupTheory.RankOneBNPair
