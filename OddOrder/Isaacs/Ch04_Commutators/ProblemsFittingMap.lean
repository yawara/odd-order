/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime

/-!
# Isaacs Chapter 4 — Problem 4D.6 (Fitting の定理の写像 `θ`)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4D.6 (書籍 p. 146)。

Theorem 4.34 (Fitting) の証明に現れる写像 `θ : G → G`, `θ(g) = ∏_{a ∈ A} (φ a) g`
(repo では `fittingProductHom`) について:

* `range_fittingProductHom_eq_fixedPoints` — `θ(G) = C_G(A)`
* `ker_fittingProductHom_eq_actionCommutator` — `ker θ = ⁅G, A⁆`

`G` は可換, `A` は `G` に coprime に作用しているとする (Thm 4.34 の設定)。

## 証明

* `θ(g)` が `A`-固定なのは添字の付け替え `a ↦ b * a` から。逆に `c ∈ C_G(A)` なら
  `θ(c) = c^{|A|}` (`fittingProductHom_apply_of_fixed`) で, coprime から
  `x ↦ x^{|A|}` は `C_G(A)` 上単射, 有限性より全射なので `c` は像に入る。
* `⁅G, A⁆ ⊆ ker θ` は既存 (`actionCommutator_le_ker_fittingProductHom`)。逆は
  Lemma 4.28 の `G = C_G(A)·⁅G, A⁆` で `g = c * x` と分解すると
  `1 = θ(g) = c^{|A|}` となり, coprime から `c = 1`, すなわち `g = x ∈ ⁅G, A⁆`。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4D.6 (p. 146) -/

variable {A G : Type*} [Group A] [CommGroup G] [Fintype A] [Finite G]

omit [Finite G] in
/-- `θ(g)` は常に `A`-固定 (`a ↦ b * a` による添字の付け替え). -/
theorem fittingProductHom_mem_fixedPoints (φ : A →* MulAut G) (g : G) :
    fittingProductHom φ g ∈ Subgroup.fixedPointsOfMulAut φ := by
  rw [Subgroup.mem_fixedPointsOfMulAut]
  intro b
  change (φ b) (∏ a : A, (φ a) g) = ∏ a : A, (φ a) g
  rw [map_prod]
  have hcompose : ∀ a : A, (φ b) ((φ a) g) = (φ (b * a)) g := fun a => by
    rw [← MulAut.mul_apply, ← map_mul]
  rw [Finset.prod_congr (rfl : (Finset.univ : Finset A) = Finset.univ) (fun a _ => hcompose a)]
  exact Finset.prod_bijective (fun a => b * a) (Group.mulLeft_bijective b)
    (fun a => by simp) (fun _ _ => rfl)

/-- **Isaacs Problem 4D.6** (像): `θ(G) = C_G(A)`。 -/
theorem range_fittingProductHom_eq_fixedPoints (φ : A →* MulAut G)
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    (fittingProductHom φ).range = Subgroup.fixedPointsOfMulAut φ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, rfl⟩
    exact fittingProductHom_mem_fixedPoints φ g
  · intro c hc
    -- `x ↦ x ^ |A|` は `C_G(A)` 上単射, 有限性から全射
    have hinj : Function.Injective
        (fun x : ↥(Subgroup.fixedPointsOfMulAut φ) => x ^ Nat.card A) := by
      intro x y hxy
      simp only at hxy
      have h1 : (x * y⁻¹) ^ Nat.card A = 1 := by
        rw [mul_pow, inv_pow, hxy, mul_inv_cancel]
      have h2 : orderOf (x * y⁻¹) ∣ Nat.card A := orderOf_dvd_of_pow_eq_one h1
      have h3 : orderOf (x * y⁻¹) ∣ Nat.card G :=
        (orderOf_dvd_natCard _).trans
          (Subgroup.card_subgroup_dvd_card (Subgroup.fixedPointsOfMulAut φ))
      have h4 : orderOf (x * y⁻¹) = 1 :=
        Nat.eq_one_of_dvd_one (hCop ▸ Nat.dvd_gcd h2 h3)
      exact mul_inv_eq_one.mp (orderOf_eq_one_iff.mp h4)
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨c, hc⟩
    refine ⟨(x : G), ?_⟩
    rw [fittingProductHom_apply_of_fixed (Subgroup.mem_fixedPointsOfMulAut.mp x.2)]
    exact congrArg Subtype.val hx

/-- **Isaacs Problem 4D.6** (核): `ker θ = ⁅G, A⁆`。 -/
theorem ker_fittingProductHom_eq_actionCommutator [Finite A] (φ : A →* MulAut G)
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    (fittingProductHom φ).ker = actionCommutator φ := by
  refine le_antisymm ?_ (actionCommutator_le_ker_fittingProductHom φ)
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  -- Lemma 4.28: `G = C_G(A) · ⁅G, A⁆`
  have hsup : Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ = ⊤ :=
    fixedPoints_sup_actionCommutator_eq_top hCop (Or.inr inferInstance)
  have hmem : g ∈ Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ := by
    rw [hsup]; exact Subgroup.mem_top g
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨c, hc, x, hx, rfl⟩ := hmem
  -- `θ (c * x) = θ c = c ^ |A|`
  have hθx : fittingProductHom φ x = 1 :=
    MonoidHom.mem_ker.mp (actionCommutator_le_ker_fittingProductHom φ hx)
  have hθc : c ^ Nat.card A = 1 := by
    rw [← fittingProductHom_apply_of_fixed (Subgroup.mem_fixedPointsOfMulAut.mp hc)]
    rw [map_mul, hθx, mul_one] at hg
    exact hg
  -- coprime から `c = 1`
  have h2 : orderOf c ∣ Nat.card A := orderOf_dvd_of_pow_eq_one hθc
  have h3 : orderOf c ∣ Nat.card G := orderOf_dvd_natCard c
  have h4 : orderOf c = 1 := Nat.eq_one_of_dvd_one (hCop ▸ Nat.dvd_gcd h2 h3)
  rw [orderOf_eq_one_iff.mp h4, one_mul]
  exact hx

end

end OddOrder.Isaacs.Ch04
