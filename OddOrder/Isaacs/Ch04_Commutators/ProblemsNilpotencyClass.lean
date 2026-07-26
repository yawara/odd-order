/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ProblemsMaximalClass

/-!
# Isaacs Chapter 4 — Problem 4A.13 (`G'⟨a⟩` の冪零類)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4A.13 (書籍 p. 125)。

`G` が冪零で類 `m > 1`, `a ∈ G` なら **`H = G'⟨a⟩` の冪零類は `m` 未満**
(`nilpotencyClass_commutator_sup_zpowers_lt`)。

## 方針

古典的な添字で `γ_i(H) ≤ γ_{i+1}(G)` (`i ≥ 2`) を示す (mathlib の添字では
`H.lowerCentralSeries (k+1) ≤ (⊤ : Subgroup G).lowerCentralSeries (k+2)`)。帰納段は
`⁅·, H⁆ ≤ ⁅·, ⊤⁆` で自明で, **基底 `⁅H, H⁆ ≤ γ₃(G)` が本体**。

`G/γ₃` では `Ḡ'` が中心的なので `H̄ = Ḡ'⟨ā⟩` は可換, というのが理由だが,
`⁅H ⊔ K, ·⁆` の分配は使えないので **good-elements 二段**で実装する:
`N = γ₃` は正規なので `{x | ⁅x, y⁆ ∈ N}` は部分群 (`commutatorMemLeft`) であり,
これが `G'` と `a` を含むことを 2 段階で確かめる。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4A.13 (p. 125) -/

variable {G : Type*} [Group G]

/-! ### `N` を法として `y` と可換な元 -/

/-- `N ⊴ G` のとき `{x | ⁅x, y⁆ ∈ N}` は部分群 (`N` を法とする `y` の中心化群).

`⁅x₁x₂, y⁆ = x₁⁅x₂,y⁆x₁⁻¹ · ⁅x₁,y⁆` と `N` の正規性から積で閉じる. -/
def commutatorMemLeft (N : Subgroup G) [N.Normal] (y : G) : Subgroup G where
  carrier := {x | ⁅x, y⁆ ∈ N}
  one_mem' := by
    change ⁅(1 : G), y⁆ ∈ N
    rw [commutatorElement_one_left]
    exact N.one_mem
  mul_mem' {x₁ x₂} h₁ h₂ := by
    change ⁅x₁ * x₂, y⁆ ∈ N
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact N.mul_mem (‹N.Normal›.conj_mem _ h₂ x₁) h₁
  inv_mem' {x} h := by
    change ⁅x⁻¹, y⁆ ∈ N
    rw [commutatorElement_inv_left]
    have hyx : ⁅y, x⁆ ∈ N := by
      rw [← commutatorElement_inv]
      exact N.inv_mem h
    have := ‹N.Normal›.conj_mem _ hyx x⁻¹
    rwa [inv_inv] at this

@[simp]
theorem mem_commutatorMemLeft_iff (N : Subgroup G) [N.Normal] (x y : G) :
    x ∈ commutatorMemLeft N y ↔ ⁅x, y⁆ ∈ N := Iff.rfl

/-- `⁅x,y⁆ ∈ N ⟺ ⁅y,x⁆ ∈ N` (`⁅y,x⁆ = ⁅x,y⁆⁻¹`). -/
theorem commutatorElement_mem_comm {N : Subgroup G} {x y : G} (h : ⁅x, y⁆ ∈ N) :
    ⁅y, x⁆ ∈ N := by
  rw [← commutatorElement_inv]
  exact N.inv_mem h

/-! ### `⁅H, H⁆ ≤ γ₃(G)` -/

/-- **4A.13 の基底**: `⁅G'⟨a⟩, G'⟨a⟩⁆ ≤ γ₃(G)`.

`N = γ₃` として, まず `⁅a, H⁆ ≤ N` (`H ≤ commutatorMemLeft N a`; `G'` 側は
`⁅G', ⊤⁆ = N`, `⟨a⟩` 側は `a` と可換), 次に各 `y ∈ H` で `H ≤ commutatorMemLeft N y`
(`G'` 側は同じ, `⟨a⟩` 側は第 1 段より `a ∈ commutatorMemLeft N y`). -/
theorem commutator_self_le_lowerCentralSeries_two (a : G) :
    ⁅commutator G ⊔ Subgroup.zpowers a, commutator G ⊔ Subgroup.zpowers a⁆
      ≤ Subgroup.lowerCentralSeries (⊤ : Subgroup G) 2 := by
  set N : Subgroup G := Subgroup.lowerCentralSeries (⊤ : Subgroup G) 2 with hN
  haveI : N.Normal := by rw [hN]; infer_instance
  set H : Subgroup G := commutator G ⊔ Subgroup.zpowers a with hH
  -- `G'` の元は任意の元と `N` の中で交換する
  have hderived : ∀ x ∈ commutator G, ∀ y : G, ⁅x, y⁆ ∈ N := by
    intro x hx y
    rw [hN, Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y)
  -- 第 1 段: `⁅a, y⁆ ∈ N` (`y ∈ H`)
  have hstep1 : ∀ y ∈ H, ⁅a, y⁆ ∈ N := by
    have hsub : H ≤ commutatorMemLeft N a := by
      refine sup_le (fun x hx => hderived x hx a) ?_
      rw [Subgroup.zpowers_le]
      change ⁅a, a⁆ ∈ N
      rw [commutatorElement_self]
      exact N.one_mem
    intro y hy
    exact commutatorElement_mem_comm (hsub hy)
  -- 第 2 段
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  have hsub : H ≤ commutatorMemLeft N y := by
    refine sup_le (fun z hz => hderived z hz y) ?_
    rw [Subgroup.zpowers_le]
    exact hstep1 y hy
  exact hsub hx

/-! ### `γ_i(H) ≤ γ_{i+1}(G)` -/

/-- **4A.13 の帰納**: `H = G'⟨a⟩` の下降中心列は `G` のそれより 1 段先行する. -/
theorem lowerCentralSeries_commutator_sup_zpowers_le (a : G) (k : ℕ) :
    Subgroup.lowerCentralSeries (commutator G ⊔ Subgroup.zpowers a) (k + 1)
      ≤ Subgroup.lowerCentralSeries (⊤ : Subgroup G) (k + 2) := by
  induction k with
  | zero =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
    exact commutator_self_le_lowerCentralSeries_two a
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mono ih le_top

/-! ### Problem 4A.13 -/

/-- **Isaacs Problem 4A.13**: `G` が冪零で類 `m > 1` なら, 任意の `a ∈ G` に対して
`H = G'⟨a⟩` の冪零類は `m` 未満.

`γ_m(H) ≤ γ_{m+1}(G) = 1` (`lowerCentralSeries_commutator_sup_zpowers_le`) から
`class(H) ≤ m − 1 < m`. -/
theorem nilpotencyClass_commutator_sup_zpowers_lt [Group.IsNilpotent G] (a : G)
    (hm : 1 < Group.nilpotencyClass G) :
    Group.nilpotencyClass ↥(commutator G ⊔ Subgroup.zpowers a) < Group.nilpotencyClass G := by
  set m := Group.nilpotencyClass G with hmdef
  set H : Subgroup G := commutator G ⊔ Subgroup.zpowers a with hH
  have hbot : Subgroup.lowerCentralSeries H (m - 1) = ⊥ := by
    have hk := lowerCentralSeries_commutator_sup_zpowers_le (G := G) a (m - 2)
    rw [show m - 2 + 1 = m - 1 by omega, show m - 2 + 2 = m by omega,
      Subgroup.lowerCentralSeries_nilpotencyClass] at hk
    exact le_bot_iff.mp hk
  haveI : Group.IsNilpotent ↥H := (Subgroup.isNilpotent_iff_lowerCentralSeries _).mpr ⟨_, hbot⟩
  have hle := (nilpotencyClass_le_iff_lowerCentralSeries_eq_bot H).mpr hbot
  omega

end

end OddOrder.Isaacs.Ch04
