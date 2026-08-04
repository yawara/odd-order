/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow

/-!
# Factorisations through a subgroup, and pairs in the same coset

For subsets `S`, `T ⊆ G` and a subgroup `P ≤ G`, the two sets

`{(x, y) : x ∈ P, y ∈ T, x y ∈ S}`  and  `Ω = {(u, y) : u ∈ S, y ∈ T, u y⁻¹ ∈ P}`

are in bijection via `(x, y) ↦ (x y, y)`.  The second set is Navarro's `Ω_{K,L}`, the pairs of a
class `K` and a class `L` lying in the same right coset of a Sylow `p`-subgroup, and the first is
what the coefficient of `K̂` in `P̂ · L̂` counts.  Summing over the Sylow subgroups turns
`Ĝ_p · L̂` (`pElementSum_eq_sum_sylow`) into `|Ω_{K,L}|`, which is the combinatorial half of
Navarro (4.23).

`Ω` does not depend on which Sylow subgroup is chosen: conjugation moves it to the corresponding
set for the conjugate subgroup, and `S`, `T` are unions of conjugacy classes.

## Main results

* `OddOrder.GroupTheory.factorThroughEquivCosetPairs` — the bijection
* `OddOrder.GroupTheory.cosetPairsEquivConj` — independence of the chosen Sylow subgroup
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- The pairs `(x, y)` with `x ∈ P`, `y ∈ T` and `x y ∈ S`. -/
abbrev FactorThrough (P : Subgroup G) (S T : Set G) : Type _ :=
  {q : G × G // q.1 ∈ P ∧ q.2 ∈ T ∧ q.1 * q.2 ∈ S}

/-- Navarro's `Ω`: the pairs `(u, y) ∈ S × T` lying in the same right coset of `P`. -/
abbrev CosetPairs (P : Subgroup G) (S T : Set G) : Type _ :=
  {q : G × G // q.1 ∈ S ∧ q.2 ∈ T ∧ q.1 * q.2⁻¹ ∈ P}

/-- **`(x, y) ↦ (x y, y)` matches the two descriptions.** -/
def factorThroughEquivCosetPairs (P : Subgroup G) (S T : Set G) :
    FactorThrough P S T ≃ CosetPairs P S T where
  toFun q := ⟨(q.1.1 * q.1.2, q.1.2), q.2.2.2, q.2.2.1, by
    simpa [mul_assoc] using q.2.1⟩
  invFun q := ⟨(q.1.1 * q.1.2⁻¹, q.1.2), q.2.2.2, q.2.2.1, by
    simpa [mul_assoc] using q.2.1⟩
  left_inv q := Subtype.ext (Prod.ext (by simp [mul_assoc]) rfl)
  right_inv q := Subtype.ext (Prod.ext (by simp [mul_assoc]) rfl)

theorem card_factorThrough_eq_card_cosetPairs (P : Subgroup G) (S T : Set G) :
    Nat.card (FactorThrough P S T) = Nat.card (CosetPairs P S T) :=
  Nat.card_congr (factorThroughEquivCosetPairs P S T)

/-- **`Ω` does not see which conjugate of `P` is used**, provided `S` and `T` are stable under
conjugation — as they are when they are unions of conjugacy classes. -/
def cosetPairsEquivConj (P : Subgroup G) {S T : Set G} (g : G)
    (hS : ∀ x ∈ S, g * x * g⁻¹ ∈ S) (hS' : ∀ x ∈ S, g⁻¹ * x * g ∈ S)
    (hT : ∀ x ∈ T, g * x * g⁻¹ ∈ T) (hT' : ∀ x ∈ T, g⁻¹ * x * g ∈ T) :
    CosetPairs P S T ≃ CosetPairs (P.map (MulAut.conj g).toMonoidHom) S T where
  toFun q := ⟨(g * q.1.1 * g⁻¹, g * q.1.2 * g⁻¹), hS _ q.2.1, hT _ q.2.2.1, by
    refine ⟨q.1.1 * q.1.2⁻¹, q.2.2.2, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩
  invFun q := ⟨(g⁻¹ * q.1.1 * g, g⁻¹ * q.1.2 * g), hS' _ q.2.1, hT' _ q.2.2.1, by
    obtain ⟨w, hw, hwq⟩ := q.2.2.2
    have hval : g⁻¹ * q.1.1 * g * (g⁻¹ * q.1.2 * g)⁻¹ = g⁻¹ * (q.1.1 * q.1.2⁻¹) * g := by group
    rw [hval, ← hwq]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hcancel : g⁻¹ * (g * w * g⁻¹) * g = w := by group
    rwa [hcancel]⟩
  left_inv q := Subtype.ext (Prod.ext (by group) (by group))
  right_inv q := Subtype.ext (Prod.ext (by group) (by group))

end OddOrder.GroupTheory
