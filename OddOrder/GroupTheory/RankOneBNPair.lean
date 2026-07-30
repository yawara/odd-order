/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Complement

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

end OddOrder.GroupTheory.RankOneBNPair
