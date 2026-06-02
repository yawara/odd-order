/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.Inertia
import OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier
import OddOrder.GroupTheory.RepresentationTheory.Clifford
import OddOrder.GroupTheory.RepresentationTheory.ConjugationBrauer
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

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

section FrobeniusInertia

variable [Finite G] [Finite H]

/-- Frobenius-group specialization of the Brauer-conjugation inertia bridge.

If `G = H ⋊ W` is a Frobenius group with kernel `H`, every nontrivial irreducible character of
`H` has inertia subgroup exactly `H`.  This is the form needed in Peterfalvi (6.8), where
`[Is]` Theorem 6.34 is applied to `Ind_H^L θ` in the Frobenius case. -/
theorem inertia_eq_of_frobeniusGroup {W : Subgroup G}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G H W)
    {θ : IrreducibleCharacter H} (hθ_ne : θ ≠ trivialIrreducibleCharacter H) :
    ClassFunction.inertia (G := G) (H := H) (θ : ClassFunction H ℂ) = H := by
  refine inertia_eq_of_freeAction (G := G) (H := H) ?_ hθ_ne
  intro h hh
  have hhG : (h : G) ≠ 1 := by
    intro h1
    exact hh (Subtype.ext h1)
  exact hF.centralizer_kernel_le (h : G) h.property hhG

end FrobeniusInertia

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

section Complex

variable [Fintype H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]

/-- **Norm of an induced character via the Mackey sum** (any class function).

`|H| · ⟨Ind_H^G θ, Ind_H^G θ⟩ = ∑_{x ∈ G} ⟨θ, θ^{x⁻¹}⟩`.

This is Frobenius reciprocity combined with the Mackey restriction formula
`card_smul_restrict_induce`: pairing `θ` against `|H| • Res_H (Ind θ) = ∑_x θ^{x⁻¹}` and using
that the inner product is conjugate-linear on the right (`inner_smul_right`, with
`star (|H| : ℂ) = |H|`). No irreducibility is needed yet. -/
theorem card_mul_inner_self_induce (θ : ClassFunction ↥H ℂ) :
    (Nat.card H : ℂ) *
        ClassFunction.inner (induce H θ) (induce H θ) =
      ∑ x : G, ClassFunction.inner θ (conjBy x⁻¹ θ) := by
  have key : ClassFunction.inner θ ((Nat.card H : ℂ) • restrict H (induce H θ))
      = (Nat.card H : ℂ) * ClassFunction.inner (induce H θ) (induce H θ) := by
    rw [inner_smul_right, star_natCast, ← inner_induce_eq_inner_restrict]
  rw [← key, card_smul_restrict_induce, inner_sum_right]

/-- **Norm of an induced irreducible character** ([Is] Thm 6.34, norm part).

For an irreducible character `θ` of `H ⊴ G`, `|H| · ‖Ind_H^G θ‖² = |I_G(θ)|`, equivalently
`‖Ind_H^G θ‖² = [I_G(θ) : H]`: the squared norm counts the cosets of `H` in the inertia group.

Each Mackey summand `⟨θ, θ^{x⁻¹}⟩` is `1` if `x ∈ I_G(θ)` and `0` otherwise, by orthonormality
of irreducible characters (`irreducibleCharacter_inner_eq_ite`) together with
`θ^{x⁻¹} = θ ⇔ x ∈ I_G(θ)`. Summing the indicator over `G` gives `|I_G(θ)|`. -/
theorem card_mul_inner_self_induce_eq_card_inertia (θ : IrreducibleCharacter H) :
    (Nat.card H : ℂ) *
        ClassFunction.inner (induce H (θ : ClassFunction ↥H ℂ))
          (induce H (θ : ClassFunction ↥H ℂ))
      = (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥H ℂ)) : ℂ) := by
  classical
  rw [card_mul_inner_self_induce]
  have hterm : ∀ x : G,
      ClassFunction.inner (θ : ClassFunction ↥H ℂ) (conjBy x⁻¹ (θ : ClassFunction ↥H ℂ))
        = if x ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) then (1 : ℂ) else 0 := by
    intro x
    rw [← IrreducibleCharacter.coe_conjBy, irreducibleCharacter_inner_eq_ite]
    have hcond : (θ = IrreducibleCharacter.conjBy x⁻¹ θ)
        ↔ x ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      rw [eq_comm, IrreducibleCharacter.ext_iff, IrreducibleCharacter.coe_conjBy,
        ← ClassFunction.mem_inertia, Subgroup.inv_mem_iff]
    simp only [hcond]
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_boole, ← Fintype.card_subtype,
    Nat.card_eq_fintype_card]

/-- Integer-vector combinatorics: if nonzero integer coefficients on a finite set have squares
summing to `1`, the set is a singleton with coefficient `±1`. (The `∑ = 1` analogue of
`exists_pair_of_sum_sq_eq_two`.) -/
theorem exists_single_of_sum_sq_eq_one {ι : Type*} [DecidableEq ι] {s : Finset ι} {c : ι → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hsum : ∑ a ∈ s, c a ^ 2 = 1) :
    ∃ α, s = {α} ∧ (c α = 1 ∨ c α = -1) := by
  classical
  have hge : ∀ a ∈ s, 1 ≤ c a ^ 2 := fun a ha => by
    have h := Int.one_le_abs (hne a ha)
    calc (1 : ℤ) = 1 ^ 2 := by ring
      _ ≤ |c a| ^ 2 := by gcongr
      _ = c a ^ 2 := sq_abs (c a)
  have hcard : s.card = 1 := by
    have hle : (s.card : ℤ) ≤ ∑ a ∈ s, c a ^ 2 := by
      calc (s.card : ℤ) = ∑ _a ∈ s, (1 : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ a ∈ s, c a ^ 2 := Finset.sum_le_sum hge
    rw [hsum] at hle
    have hpos : 0 < s.card := by
      rcases Finset.eq_empty_or_nonempty s with rfl | h
      · simp at hsum
      · exact Finset.card_pos.mpr h
    omega
  obtain ⟨α, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.sum_singleton] at hsum
  refine ⟨α, rfl, ?_⟩
  have hmul : c α * c α = 1 := by rw [← sq]; exact hsum
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmul with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- **A virtual character of squared norm `1` and positive degree is irreducible.**

If `φ ∈ ℤ[Irr G]` has `‖φ‖² = 1` and `φ(1)` is a positive natural number, then `φ` is an
irreducible character. By Parseval its Fourier coefficients are integers with `∑ cᵢ² = 1`, so
exactly one is `±1`; positivity of `φ(1)` rules out the `-1` case, leaving `φ = χ` for an
irreducible `χ`. (The norm-`1` analogue of `exists_irr_sub_irr_of_inner_self_two`.) -/
theorem isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    (hnorm : ClassFunction.inner φ φ = 1)
    (hpos : ∃ d : ℕ, 0 < d ∧ (φ : G → ℂ) 1 = (d : ℂ)) :
    IsIrreducibleCharacter φ := by
  classical
  haveI : Finite G := Finite.of_fintype G
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 1 := hsq.symm.trans hnorm
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 1 := by exact_mod_cast hsumC
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨α₀, hs, hcα⟩ := exists_single_of_sum_sq_eq_one hne hsumZ
  have hα₀ : α₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  rw [hs, Finset.sum_singleton] at hrepr
  obtain ⟨d, hd, hφ1⟩ := hpos
  obtain ⟨e, he, hα1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨α₀, hα₀⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at hα1
  rcases hcα with hcα | hcα
  · -- c α₀ = 1: φ = α₀, which is irreducible
    rw [hrepr, hcα]
    simp only [Int.cast_one, one_smul]
    exact hα₀
  · -- c α₀ = -1: φ(1) = -e < 0, contradicting φ(1) = d > 0
    exfalso
    have hval : (φ : G → ℂ) 1 = -(e : ℂ) := by
      rw [hrepr, hcα]
      simp only [Int.cast_neg, Int.cast_one, ClassFunction.smul_apply, hα1]
      ring
    rw [hval] at hφ1
    have hsum0 : (d : ℂ) + (e : ℂ) = 0 := by linear_combination -hφ1
    rw [← Nat.cast_add] at hsum0
    have : d + e = 0 := by exact_mod_cast hsum0
    omega

/-- **[Is] Theorem 6.34** (Frobenius/Dade induced irreducibility).

For `H ⊴ G` and an irreducible character `θ` of `H` whose inertia group in `G` is just `H`
(the free-action / Frobenius condition — which holds for `θ ≠ 1` when `G/H` acts freely on
`Irr H ∖ {1}`), the induced character `Ind_H^G θ` is irreducible. Its degree is `[G : H] · θ(1)`
(`induce_apply_one`).

Proof: `Ind θ ∈ ℤ[Irr G]` (`induce_mem_ZIrr`); `‖Ind θ‖² = |I_G(θ)|/|H| = 1` from
`card_mul_inner_self_induce_eq_card_inertia` with `I_G(θ) = H`; and `Ind θ (1) = [G:H]·θ(1) > 0`.
Norm `1` with positive degree forces irreducibility. -/
theorem isIrreducibleCharacter_induce_of_inertia_eq (θ : IrreducibleCharacter H)
    (hfree : ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H) :
    IsIrreducibleCharacter (induce H (θ : ClassFunction ↥H ℂ)) := by
  have hmem : induce H (θ : ClassFunction ↥H ℂ) ∈ ZIrr G :=
    induce_mem_ZIrr H θ.property.mem_ZIrr
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  have hnorm : ClassFunction.inner (induce H (θ : ClassFunction ↥H ℂ))
      (induce H (θ : ClassFunction ↥H ℂ)) = 1 := by
    have h := card_mul_inner_self_induce_eq_card_inertia θ
    rw [hfree] at h
    exact mul_left_cancel₀ hcardH (by rw [h, mul_one])
  have hpos : ∃ d : ℕ, 0 < d ∧ (induce H (θ : ClassFunction ↥H ℂ) : G → ℂ) 1 = (d : ℂ) := by
    haveI : Finite G := Finite.of_fintype G
    obtain ⟨e, he, hθ1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hidx : 0 < H.index := Nat.pos_of_ne_zero fun h0 => by
      have hmc := H.index_mul_card
      rw [h0, zero_mul] at hmc
      exact (Nat.card_pos (α := G)).ne' hmc.symm
    refine ⟨H.index * e, Nat.mul_pos hidx he, ?_⟩
    rw [induce_apply_one, hθ1, Nat.cast_mul]
  exact isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos hmem hnorm hpos

/-- Frobenius-group form of **[Is] Theorem 6.34**.

In a Frobenius group with kernel `H`, inducing any nontrivial irreducible character of `H`
to the ambient group gives an irreducible character.  The proof combines
`inertia_eq_of_frobeniusGroup` with `isIrreducibleCharacter_induce_of_inertia_eq`; the degree
formula remains `ClassFunction.induce_apply_one`. -/
theorem isIrreducibleCharacter_induce_of_frobeniusGroup {W : Subgroup G}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G H W)
    (θ : IrreducibleCharacter H) (hθ_ne : θ ≠ trivialIrreducibleCharacter H) :
    IsIrreducibleCharacter (induce H (θ : ClassFunction H ℂ)) :=
  isIrreducibleCharacter_induce_of_inertia_eq θ
    (inertia_eq_of_frobeniusGroup hF hθ_ne)

end Complex

end OddOrder.RepresentationTheory
