/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A set closed under right translation by a subgroup has divisible cardinality

If `A ⊆ G` satisfies `A · P ⊆ A` for a subgroup `P ≤ G`, then `A` is a union of left cosets `xP`,
so `|P|` divides `|A|`.

This is the counting step of Gorenstein Lemma 7.6(i) (issue 9508, 段 E): the set

`{x ∈ G | x⁻¹ y x ∈ uP}`

is closed under `x ↦ x v` for `v ∈ P` (because `v` centralises `u` and normalises `P`), so the
induced function `ψ*(y) = σ(y) / |P|` is an integer.

## Main results

* `OddOrder.GroupTheory.card_filter_quotientMk_eq` — the fibres of `G → G ⧸ P` have size `|P|`
* `OddOrder.GroupTheory.card_subgroup_dvd_card_of_mul_mem`

## References

* D. Gorenstein, *Finite Groups*, §4.7, Lemma 7.6 (`references/gorenstein/pages/`).
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G] (P : Subgroup G)

open scoped Classical in
/-- The fibre of `G → G ⧸ P` over `mk x₀` is the left coset `x₀ P`, of size `|P|`. -/
theorem card_filter_quotientMk_eq [Fintype G] (x₀ : G) :
    (Finset.univ.filter fun x : G => (QuotientGroup.mk x : G ⧸ P) = QuotientGroup.mk x₀).card
      = Nat.card ↥P := by
  classical
  have himg : (Finset.univ.filter fun x : G => (QuotientGroup.mk x : G ⧸ P)
        = QuotientGroup.mk x₀)
      = (Finset.univ.filter fun v : G => v ∈ P).image (fun v => x₀ * v) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      exact ⟨x₀⁻¹ * x, QuotientGroup.eq.mp hx.symm, mul_inv_cancel_left x₀ x⟩
    · rintro ⟨v, hv, rfl⟩
      refine QuotientGroup.eq.mpr ?_
      have hrw : (x₀ * v)⁻¹ * x₀ = v⁻¹ := by
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      rw [hrw]
      exact P.inv_mem hv
  rw [himg, Finset.card_image_of_injective _ (mul_right_injective x₀),
    Nat.card_eq_fintype_card, Fintype.card_subtype]

open scoped Classical in
/-- **A set closed under right translation by `P` has cardinality divisible by `|P|`.** -/
theorem card_subgroup_dvd_card_of_mul_mem [Finite G] (A : Finset G)
    (hA : ∀ x ∈ A, ∀ v : G, v ∈ P → x * v ∈ A) : Nat.card ↥P ∣ A.card := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hmaps : ∀ x ∈ A, (QuotientGroup.mk x : G ⧸ P)
      ∈ A.image fun x : G => (QuotientGroup.mk x : G ⧸ P) := fun x hx =>
    Finset.mem_image_of_mem _ hx
  have hfib : ∀ q ∈ A.image fun x : G => (QuotientGroup.mk x : G ⧸ P),
      (A.filter fun x => (QuotientGroup.mk x : G ⧸ P) = q).card = Nat.card ↥P := by
    intro q hq
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hq
    have hset : (A.filter fun x => (QuotientGroup.mk x : G ⧸ P) = QuotientGroup.mk x₀)
        = Finset.univ.filter fun x : G => (QuotientGroup.mk x : G ⧸ P) = QuotientGroup.mk x₀ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      have hmem : x₀⁻¹ * x ∈ P := QuotientGroup.eq.mp h.symm
      have hx := hA x₀ hx₀ (x₀⁻¹ * x) hmem
      simpa using hx
    rw [hset, card_filter_quotientMk_eq]
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_const,
    smul_eq_mul]
  exact ⟨_, mul_comm _ _⟩

end OddOrder.GroupTheory
