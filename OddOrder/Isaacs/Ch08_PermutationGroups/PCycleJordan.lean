/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Isaacs, Finite Group Theory — Ch. 8: the `p`-cycle Jordan theorem (Thm 8.23)

Formalizes **Isaacs Thm 8.23** (pp. 236–237; Wielandt 13.9): a primitive
subgroup `G ≤ Sym(Ω)` containing a `p`-cycle with `p` prime and
`p ≤ |Ω| - 3` contains the alternating group.  This is mathlib's
`proof_wanted alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`
(`Mathlib.GroupTheory.GroupAction.Jordan`).

Current contents: the groundwork —

* agreement-transport lemmas: if permutations agree on an invariant set,
  so do their inverses, products, commutators and powers
  (`commutator_apply_eq_of_agree`, `pow_apply_eq_of_agree`);
* the realization lemma (`exists_agree_of_isMultiplyPretransitive`): an
  `|S|`-transitive subgroup of `Perm α` contains an element agreeing with
  any prescribed permutation on `S`.

The main theorem (Frattini/Sylow correction, centralizer of the `p`-cycle
via `IsCycle.commute_iff`, and the `x^p` three-cycle) follows in this file.
-/

namespace OddOrder.Isaacs.Ch08

open Equiv Equiv.Perm MulAction

open scoped commutatorElement

variable {α : Type*}

/-! ### Agreement transport on an invariant set -/

section Agree

variable {x w x₁ x₂ w₁ w₂ : Perm α} {S : Set α}

/-- Invariance of a set under `w` transfers to `w⁻¹`. -/
private lemma inv_invariant (hwS : ∀ b, b ∈ S ↔ w b ∈ S) (b : α) :
    b ∈ S ↔ w⁻¹ b ∈ S := by
  constructor
  · intro hb
    exact (hwS (w⁻¹ b)).mpr (by simpa using hb)
  · intro hb
    have := (hwS (w⁻¹ b)).mp hb
    simpa using this

/-- Two permutations agreeing on a `w`-invariant set have agreeing
inverses there. -/
private lemma inv_apply_eq_of_agree (hwS : ∀ b, b ∈ S ↔ w b ∈ S)
    (h : ∀ b ∈ S, x b = w b) : ∀ b ∈ S, x⁻¹ b = w⁻¹ b := by
  intro b hb
  have hw : w⁻¹ b ∈ S := (inv_invariant hwS b).mp hb
  have hx : x (w⁻¹ b) = b := (h _ hw).trans (by simp)
  apply x.injective
  rw [hx]
  simp

/-- Agreement on an invariant set is preserved by products. -/
private lemma mul_apply_eq_of_agree (h₂S : ∀ b, b ∈ S ↔ w₂ b ∈ S)
    (h₁ : ∀ b ∈ S, x₁ b = w₁ b) (h₂ : ∀ b ∈ S, x₂ b = w₂ b) :
    ∀ b ∈ S, (x₁ * x₂) b = (w₁ * w₂) b := by
  intro b hb
  rw [Perm.mul_apply, Perm.mul_apply, h₂ b hb]
  exact h₁ _ ((h₂S b).mp hb)

/-- Agreement on an invariant set is preserved by commutators. -/
private lemma commutator_apply_eq_of_agree
    (h₁S : ∀ b, b ∈ S ↔ w₁ b ∈ S) (h₂S : ∀ b, b ∈ S ↔ w₂ b ∈ S)
    (h₁ : ∀ b ∈ S, x₁ b = w₁ b) (h₂ : ∀ b ∈ S, x₂ b = w₂ b) :
    ∀ b ∈ S, ⁅x₁, x₂⁆ b = ⁅w₁, w₂⁆ b := by
  intro b hb
  rw [commutatorElement_def, commutatorElement_def]
  exact mul_apply_eq_of_agree (inv_invariant h₂S)
    (mul_apply_eq_of_agree (inv_invariant h₁S)
      (mul_apply_eq_of_agree h₂S h₁ h₂)
      (inv_apply_eq_of_agree h₁S h₁))
    (inv_apply_eq_of_agree h₂S h₂) b hb

/-- Agreement on an invariant set is preserved by powers. -/
private lemma pow_apply_eq_of_agree (hwS : ∀ b, b ∈ S ↔ w b ∈ S)
    (h : ∀ b ∈ S, x b = w b) (n : ℕ) :
    ∀ b ∈ S, (x ^ n) b = (w ^ n) b := by
  induction n with
  | zero => intro b _; simp
  | succ n ih =>
    intro b hb
    rw [pow_succ, pow_succ, Perm.mul_apply, Perm.mul_apply, h b hb]
    exact ih _ ((hwS b).mp hb)

end Agree

/-! ### Realizing prescribed behavior by multiple transitivity -/

/-- A subgroup of `Perm α` that is `|S|`-transitive contains an element
agreeing with any prescribed permutation on the finset `S`. -/
private lemma exists_agree_of_isMultiplyPretransitive
    {G : Subgroup (Perm α)} {S : Finset α}
    (hT : IsMultiplyPretransitive G α S.card) (τ : Perm α) :
    ∃ k : Perm α, k ∈ G ∧ ∀ b ∈ S, k b = τ b := by
  classical
  haveI := hT
  set e : Fin S.card ≃ {b // b ∈ S} := S.equivFin.symm with he
  set ι₁ : Fin S.card ↪ α :=
    ⟨fun i => ↑(e i), fun i j hij => e.injective (Subtype.ext hij)⟩ with hι₁
  set ι₂ : Fin S.card ↪ α :=
    ⟨fun i => τ ↑(e i), fun i j hij =>
      e.injective (Subtype.ext (τ.injective hij))⟩ with hι₂
  obtain ⟨k, hk⟩ := exists_smul_eq (M := G) ι₁ ι₂
  refine ⟨(k : Perm α), k.2, fun b hb => ?_⟩
  have happ : (k • ι₁) (e.symm ⟨b, hb⟩) = ι₂ (e.symm ⟨b, hb⟩) := by rw [hk]
  rw [Function.Embedding.smul_apply] at happ
  have hb1 : ι₁ (e.symm ⟨b, hb⟩) = b := by simp [hι₁]
  have hb2 : ι₂ (e.symm ⟨b, hb⟩) = τ b := by simp [hι₂]
  rw [hb1, hb2] at happ
  exact happ

end OddOrder.Isaacs.Ch08
