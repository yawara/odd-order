/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.Inertia

/-!
# Frobenius irreducibility of induced characters ([Is] Theorem 6.34)

For a normal subgroup `H ⊴ G` (Peterfalvi's `H ⊴ L`, with quotient `W₁ = G/H`) this file
builds toward **[Is] Theorem 6.34**: when `W₁` acts freely on `Irr H ∖ {1}` (the
Frobenius/Dade situation of Peterfalvi §6), the induced character `Ind_H^G θ` of a
nontrivial `θ ∈ Irr H` is irreducible of degree `[G : H] · θ(1) = |W₁| · θ(1)`.

This supplies the two facts Peterfalvi (6.8) needs to feed `coherentUnion_of_glued`: that the
constituents live in `Irr G`, and that every constituent has the common degree `|W₁|`.

## Build chain

* `card_smul_restrict_induce` — **Mackey restriction** (normal-subgroup case, unnormalized
  to avoid choosing coset representatives): `|H| • Res_H (Ind_H^G θ) = ∑_{x ∈ G} θ^{x⁻¹}`.
  Here `θ^{x⁻¹} = ClassFunction.conjBy x⁻¹ θ`. This is the heaviest analytic brick; the rest
  are consequences via Frobenius reciprocity.
* (degree) `OddOrder.RepresentationTheory.induce_apply_one` (already proved in
  `InducedCharacter`): `Ind_H^G θ (1) = [G : H] · θ(1)`.

## References

* I. M. Isaacs, *Finite Group Theory* (AMS GSM 92), Theorem 6.34.
* Peterfalvi, *Character Theory for the Odd Order Theorem*, §6 (used in the proof of (6.8)).
-/

namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]
variable {k : Type*} [CommRing k]

/-- Evaluation of a finite sum of class functions is the sum of the evaluations.

A pointwise companion to `ClassFunction.add_apply`/`zero_apply`, needed to unfold the
right-hand side of the Mackey restriction formula. -/
@[simp] theorem ClassFunction.finset_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → ClassFunction G k) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]

variable [Fintype G] [Invertible (Nat.card H : k)]

/-- **Mackey restriction formula** (normal-subgroup case), in unnormalized form.

For `H ⊴ G` and `θ : ClassFunction ↥H k`,
`|H| • Res_H (Ind_H^G θ) = ∑_{x ∈ G} θ^{x⁻¹}`,
where `θ^{x⁻¹} = ClassFunction.conjBy x⁻¹ θ`.

Summing over the *whole* group `G` (rather than a transversal) keeps the statement free of a
choice of coset representatives: each left coset `xH` contributes `|H|` equal summands
`θ^{x⁻¹}` — equal because `conjBy` is constant along the coset
(`ClassFunction.conjBy_eq_self_of_mem`) — so the global `|H|` factor exactly cancels the
`|H|⁻¹` built into `induce`. The classical transversal form
`Res_H (Ind_H^G θ) = ∑_{w ∈ G/H} θ^{w⁻¹}` is the same identity divided by `|H|`.

The proof is pointwise: for `h ∈ H` every conjugate `x⁻¹ h x` stays in `H` (normality), so
no induction term vanishes (`induceTerm_of_mem_normal`), and `θ(x⁻¹ h x)` is exactly
`(conjBy x⁻¹ θ)(h)`. -/
theorem card_smul_restrict_induce (θ : ClassFunction ↥H k) :
    (Nat.card H : k) • restrict H (induce H θ) = ∑ x : G, conjBy x⁻¹ θ := by
  ext h
  rw [smul_apply, restrict_apply, induce_apply, ClassFunction.finset_sum_apply,
    ← mul_assoc, mul_invOf_self, one_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [induceTerm_of_mem_normal (le_refl H) θ h.property x, conjBy_apply]
  exact congrArg θ (Subtype.ext (by group))

end OddOrder.RepresentationTheory
