/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The permutation character of a transitive action

For a finite group `G` acting transitively on a finite set `Ω` with point
stabilizer `H = MulAction.stabilizer G ω₀`, the induced trivial character
`Ind_H^G 1_H` is the permutation character `g ↦ |Fix_Ω(g)|`; its norm
`⟨Ind_H^G 1_H, Ind_H^G 1_H⟩_G` is the number of orbits of `G` on `Ω × Ω`
(Burnside's lemma), which is `2` for a doubly transitive action on a
nontrivial `Ω`.

Peterfalvi Part II, Ch. III, Theorem C, step (7) consumes the last statement:
`⟨Ind_H^G λ, Ind_H^G λ⟩ = ⟨Ind_H^G 1_H, Ind_H^G 1_H⟩ = 2` for the doubly
transitive Zassenhaus configuration (p. 115).

## Main results

* `ClassFunction.induce_trivial_stabilizer_apply` —
  `(Ind_H^G 1_H)(g) = |Fix_Ω(g)|`.
* `ClassFunction.inner_induce_trivial_stabilizer` — the norm of the
  permutation character counts the orbits of `G` on `Ω × Ω`.
* `MulAction.card_orbits_prod_eq_two` — a doubly transitive action has exactly
  two orbits on `Ω × Ω` (the diagonal and its complement).
* `ClassFunction.inner_induce_trivial_stabilizer_of_two_pretransitive` — the
  norm is `2` in the doubly transitive case.
-/

noncomputable section

namespace OddOrder.GroupTheory

open MulAction

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

/-- In a transitive action the transporter `{x | x • ω₀ = ω}` is a coset of the
stabilizer of `ω₀`; in particular its cardinality is `|Stab(ω₀)|`. -/
theorem card_transporter_eq_card_stabilizer (ω₀ : Ω) [IsPretransitive G Ω] (ω : Ω) :
    Nat.card {x : G // x • ω₀ = ω} = Nat.card (stabilizer G ω₀) := by
  obtain ⟨y, hy⟩ := exists_smul_eq G ω₀ ω
  refine Nat.card_congr
    ⟨fun p => ⟨y⁻¹ * p.1, mem_stabilizer_iff.mpr ?_⟩,
     fun s => ⟨y * s.1, ?_⟩, fun p => ?_, fun s => ?_⟩
  · rw [mul_smul, p.2, ← hy, inv_smul_smul]
  · rw [mul_smul, mem_stabilizer_iff.mp s.2, hy]
  · exact Subtype.ext (mul_inv_cancel_left y p.1)
  · exact Subtype.ext (inv_mul_cancel_left y s.1)

/-- The fixed points of `g` on `Ω × Ω` (diagonal action) are the pairs of fixed
points on `Ω`. -/
theorem card_fixedBy_prod (g : G) :
    Nat.card (fixedBy (Ω × Ω) g) = Nat.card (fixedBy Ω g) * Nat.card (fixedBy Ω g) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    ⟨fun p => (⟨p.1.1, ?_⟩, ⟨p.1.2, ?_⟩), fun q => ⟨(q.1.1, q.2.1), ?_⟩,
     fun p => ?_, fun q => ?_⟩
  · have h := p.2
    rw [mem_fixedBy] at h ⊢
    simpa using (Prod.ext_iff.mp h).1
  · have h := p.2
    rw [mem_fixedBy] at h ⊢
    simpa using (Prod.ext_iff.mp h).2
  · have h1 := q.1.2
    have h2 := q.2.2
    rw [mem_fixedBy] at h1 h2
    rw [mem_fixedBy]
    exact Prod.ext_iff.mpr ⟨by simpa using h1, by simpa using h2⟩
  · exact Subtype.ext rfl
  · exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- **A doubly transitive action has exactly two orbits on `Ω × Ω`**: the
diagonal and its complement. -/
theorem card_orbits_prod_eq_two [Nontrivial Ω]
    (h2 : IsMultiplyPretransitive G Ω 2) :
    Nat.card (orbitRel.Quotient G (Ω × Ω)) = 2 := by
  classical
  have : IsMultiplyPretransitive G Ω 2 := h2
  have : IsPretransitive G Ω := isPretransitive_of_is_two_pretransitive
  obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
  rw [Nat.card_eq_two_iff]
  refine ⟨⟦(a, a)⟧, ⟦(a, b)⟧, fun h => ?_, ?_⟩
  · -- the diagonal orbit is not the off-diagonal orbit
    rw [Quotient.eq] at h
    obtain ⟨g, hg⟩ := h
    have h1 : (g : G) • a = a := congrArg Prod.fst hg
    have h2' : (g : G) • b = a := congrArg Prod.snd hg
    exact hab (smul_left_cancel (g : G) (h1.trans h2'.symm))
  · -- the two orbits cover
    rw [Set.eq_univ_iff_forall]
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      obtain ⟨c, d⟩ := p
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hcd : c = d
      · left
        subst hcd
        rw [Quotient.eq]
        obtain ⟨g, hg⟩ := exists_smul_eq G a c
        exact ⟨g, Prod.ext hg hg⟩
      · right
        rw [Quotient.eq]
        obtain ⟨g, hg1, hg2⟩ :=
          (is_two_pretransitive_iff.mp h2) hab hcd
        exact ⟨g, Prod.ext hg1 hg2⟩

end OddOrder.GroupTheory

namespace OddOrder.RepresentationTheory.ClassFunction

open MulAction

variable {G : Type*} [Group G] [Fintype G] {Ω : Type*} [Finite Ω] [MulAction G Ω]

/-- **The permutation character** (Isaacs CTFG (5.14)): for a transitive action
with point stabilizer `H = stabilizer G ω₀`, the induced trivial character
counts fixed points: `(Ind_H^G 1_H)(g) = |Fix_Ω(g)|`. -/
theorem induce_trivial_stabilizer_apply (ω₀ : Ω) [IsPretransitive G Ω]
    [Invertible (Nat.card (stabilizer G ω₀) : ℂ)] (g : G) :
    induce (stabilizer G ω₀) (trivialClassFunction ↥(stabilizer G ω₀)) g
      = (Nat.card (fixedBy Ω g) : ℂ) := by
  classical
  let : Fintype Ω := Fintype.ofFinite Ω
  rw [induce_apply]
  have hterm : ∀ x : G,
      induceTerm (stabilizer G ω₀) (trivialClassFunction ↥(stabilizer G ω₀)) x g
        = if g • (x • ω₀) = x • ω₀ then (1 : ℂ) else 0 := by
    intro x
    have hmem : x⁻¹ * g * x ∈ stabilizer G ω₀ ↔ g • (x • ω₀) = x • ω₀ := by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff, eq_comm]
    by_cases hx : g • (x • ω₀) = x • ω₀
    · rw [induceTerm_of_mem _ (hmem.mpr hx), trivialClassFunction_apply, if_pos hx]
    · rw [induceTerm_of_not_mem _ (fun h => hx (hmem.mp h)), if_neg hx]
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_boole]
  have hcount : (Finset.univ.filter fun x : G => g • (x • ω₀) = x • ω₀).card
      = Nat.card (fixedBy Ω g) * Nat.card (stabilizer G ω₀) := by
    have hfw := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : G => g • (x • ω₀) = x • ω₀)
      (t := (fixedBy Ω g).toFinset) (f := fun x : G => x • ω₀)
      (fun x hx => Set.mem_toFinset.mpr (Finset.mem_filter.mp hx).2)
    rw [hfw]
    have hfiber : ∀ ω ∈ (fixedBy Ω g).toFinset,
        ((Finset.univ.filter fun x : G => g • (x • ω₀) = x • ω₀).filter
          fun x => x • ω₀ = ω).card = Nat.card (stabilizer G ω₀) := by
      intro ω hω
      rw [Set.mem_toFinset, mem_fixedBy] at hω
      rw [Finset.filter_filter]
      have heq : (Finset.univ.filter fun x : G => g • (x • ω₀) = x • ω₀ ∧ x • ω₀ = ω)
          = Finset.univ.filter fun x : G => x • ω₀ = ω :=
        Finset.filter_congr fun x _ =>
          ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hω, h⟩⟩
      rw [heq, ← OddOrder.GroupTheory.card_transporter_eq_card_stabilizer ω₀ ω,
        Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul,
      Set.toFinset_card, ← Nat.card_eq_fintype_card]
  rw [hcount]
  push_cast
  rw [mul_comm ((Nat.card (fixedBy Ω g) : ℂ)), ← mul_assoc, invOf_mul_self, one_mul]

/-- **Burnside's lemma for the permutation character**: the norm of
`Ind_H^G 1_H` (`H` a point stabilizer of a transitive action) is the number of
orbits of `G` on `Ω × Ω`. -/
theorem inner_induce_trivial_stabilizer (ω₀ : Ω) [IsPretransitive G Ω]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card (stabilizer G ω₀) : ℂ)] :
    ClassFunction.inner
        (induce (stabilizer G ω₀) (trivialClassFunction ↥(stabilizer G ω₀)))
        (induce (stabilizer G ω₀) (trivialClassFunction ↥(stabilizer G ω₀)))
      = (Nat.card (orbitRel.Quotient G (Ω × Ω)) : ℂ) := by
  classical
  rw [inner_eq_inv_card_mul_innerSum, innerSum]
  have happ : ∀ g : G,
      induce (stabilizer G ω₀) (trivialClassFunction ↥(stabilizer G ω₀)) g
        * star (induce (stabilizer G ω₀) (trivialClassFunction ↥(stabilizer G ω₀)) g)
      = (Nat.card (fixedBy (Ω × Ω) g) : ℂ) := by
    intro g
    rw [induce_trivial_stabilizer_apply ω₀ g, star_natCast, ← Nat.cast_mul,
      ← OddOrder.GroupTheory.card_fixedBy_prod g]
  rw [Finset.sum_congr rfl fun g _ => happ g, ← Nat.cast_sum]
  have hburn : (∑ g : G, Nat.card (fixedBy (Ω × Ω) g))
      = Nat.card (orbitRel.Quotient G (Ω × Ω)) * Nat.card G := by
    let : ∀ a : G, Fintype (fixedBy (Ω × Ω) a) := fun a => Fintype.ofFinite _
    let : Fintype (orbitRel.Quotient G (Ω × Ω)) := Fintype.ofFinite _
    simp_rw [Nat.card_eq_fintype_card]
    exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Ω × Ω)
  rw [hburn]
  push_cast
  rw [mul_comm ((Nat.card (orbitRel.Quotient G (Ω × Ω)) : ℂ)), ← mul_assoc,
    invOf_mul_self, one_mul]

/-- **The norm of the permutation character of a doubly transitive action is
`2`** — the final input of Peterfalvi Part II, Ch. III, Theorem C, step (7)
(p. 115): `⟨Ind_H^G 1_H, Ind_H^G 1_H⟩ = 2`. -/
theorem inner_induce_trivial_stabilizer_of_two_pretransitive (ω₀ : Ω)
    [Nontrivial Ω] (h2 : IsMultiplyPretransitive G Ω 2)
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card (stabilizer G ω₀) : ℂ)] :
    ClassFunction.inner
        (induce (stabilizer G ω₀) (trivialClassFunction ↥(stabilizer G ω₀)))
        (induce (stabilizer G ω₀) (trivialClassFunction ↥(stabilizer G ω₀)))
      = 2 := by
  have : IsMultiplyPretransitive G Ω 2 := h2
  have : IsPretransitive G Ω := isPretransitive_of_is_two_pretransitive
  rw [inner_induce_trivial_stabilizer ω₀,
    OddOrder.GroupTheory.card_orbits_prod_eq_two h2]
  norm_num

/-- Restatement of `inner_induce_trivial_stabilizer_of_two_pretransitive` through
an equality `H = stabilizer G ω₀`, as point stabilizers arise in concrete
configurations (Peterfalvi Part II: `H_def : H = stabilizer G basept`). -/
theorem inner_induce_trivial_of_eq_stabilizer {H : Subgroup G} {ω₀ : Ω}
    (hH : H = stabilizer G ω₀) [Nontrivial Ω]
    (h2 : IsMultiplyPretransitive G Ω 2) [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥H : ℂ)] :
    ClassFunction.inner (induce H (trivialClassFunction ↥H))
      (induce H (trivialClassFunction ↥H)) = 2 := by
  subst hH
  exact inner_induce_trivial_stabilizer_of_two_pretransitive ω₀ h2

end OddOrder.RepresentationTheory.ClassFunction
