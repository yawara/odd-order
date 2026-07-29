/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-!
# 中心的交換子の双線形性

`OddOrder.GroupTheory` shared module: `⁅x, y⁆ ∈ Z(G)` のとき

* `⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n`
* `⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n`

系として、中心的交換子の位数は `x`・`y` 双方の位数を割る
(`orderOf_commutatorElement_dvd_orderOf_right`)。したがって位数が互いに素な
2 元の交換子が中心的なら、その 2 元は可換
(`commute_of_commutatorElement_mem_of_coprime_natCard`)。

**群全体の類が 2 である必要はない** — 当該の 1 つの交換子が中心的でありさえすればよい。

⚠ 同内容が `OddOrder/BG/Ch1_Preliminary/S04_CommutatorCollection.lean`
(`BG.Ch1.S04.commutatorElement_pow_{left,right}_of_central`, BG Lemma 4.2(a)) にもあるが、
BG は Isaacs の**下流**なので Isaacs 側から import できない。本 leaf を両者の上流に置き、
BG 側の重複解消は hub の判断に委ねる (issue 9207)。
`Isaacs/Ch04_Commutators/Problems.lean` の
`commutatorElement_pow_left_of_commutator_le_center` は本補題の類 2 特殊化にあたる。
-/

open scoped commutatorElement

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- `⁅x, y⁆` が中心的なら `⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n`。

`⁅ab, c⁆ = a ⁅b,c⁆ a⁻¹ ⁅a,c⁆` (`commutatorElement_mul_left_eq_conj_mul`) の共役部分が
中心性で消えるので `⁅x^{n+1}, y⁆ = ⁅x,y⁆ · ⁅x^n, y⁆`。 -/
theorem commutatorElement_pow_left_of_central {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G) (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : x ^ (n + 1) = x ^ n * x := pow_succ x n
    rw [hx, commutatorElement_mul_left_eq_conj_mul, ih]
    have hc : x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ = ⁅x, y⁆ := by
      rw [Subgroup.mem_center_iff.mp hz (x ^ n)]
      group
    rw [hc, pow_succ']

/-- `⁅x, y⁆` が中心的なら `⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n`。

`⁅x, y⁆⁻¹ = ⁅y, x⁆` で左版に帰着する。 -/
theorem commutatorElement_pow_right_of_central {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G) (n : ℕ) : ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  have hz' : ⁅y, x⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ hz
  have h1 : ⁅y ^ n, x⁆ = ⁅y, x⁆ ^ n := commutatorElement_pow_left_of_central hz' n
  have h2 : ⁅x, y ^ n⁆ = (⁅y ^ n, x⁆)⁻¹ := by rw [commutatorElement_inv]
  rw [h2, h1, ← commutatorElement_inv, inv_pow, inv_inv]

/-- `⁅x, y⁆` が中心的なら `⁅x ^ m, y ^ n⁆ = ⁅x, y⁆ ^ (m * n)`。 -/
theorem commutatorElement_pow_pow_of_central {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G) (m n : ℕ) : ⁅x ^ m, y ^ n⁆ = ⁅x, y⁆ ^ (m * n) := by
  have hzm : ⁅x ^ m, y⁆ ∈ Subgroup.center G := by
    rw [commutatorElement_pow_left_of_central hz m]
    exact Subgroup.pow_mem _ hz m
  rw [commutatorElement_pow_right_of_central hzm n,
    commutatorElement_pow_left_of_central hz m, ← pow_mul]

/-! ## 位数の帰結 -/

/-- 中心的交換子の位数は `y` の位数を割る: `⁅x, y⁆ ^ (orderOf y) = ⁅x, y ^ (orderOf y)⁆ = 1`。 -/
theorem orderOf_commutatorElement_dvd_orderOf_right {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G) : orderOf ⁅x, y⁆ ∣ orderOf y := by
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [← commutatorElement_pow_right_of_central hz, pow_orderOf_eq_one,
    commutatorElement_one_right]

/-- 中心的交換子の位数は `x` の位数も割る。 -/
theorem orderOf_commutatorElement_dvd_orderOf_left {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G) : orderOf ⁅x, y⁆ ∣ orderOf x := by
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [← commutatorElement_pow_left_of_central hz, pow_orderOf_eq_one,
    commutatorElement_one_left]

/-- `⁅x, y⁆` が中心的で、その位数が `y` の位数と互いに素なら `x` と `y` は可換。 -/
theorem commute_of_commutatorElement_mem_center_of_coprime {x y : G}
    (hz : ⁅x, y⁆ ∈ Subgroup.center G)
    (hcop : Nat.Coprime (orderOf ⁅x, y⁆) (orderOf y)) : Commute x y := by
  have h1 : orderOf ⁅x, y⁆ = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
      (orderOf_commutatorElement_dvd_orderOf_right hz)
  have h2 : ⁅x, y⁆ = 1 := orderOf_eq_one_iff.mp h1
  exact commutatorElement_eq_one_iff_commute.mp h2

/-- **位数が互いに素なら中心的交換子は消える** (本リポジトリでの用途: `Z(F)` が
奇位数で `y` が 2-元のとき、`[x, y] ∈ Z(F)` から `x` が `y` を中心化する)。

`Z` は中心に含まれる有限部分群で、その位数が `y` の位数と互いに素であればよい。 -/
theorem commute_of_commutatorElement_mem_of_coprime_natCard {Z : Subgroup G} [Finite ↥Z]
    (hZ : Z ≤ Subgroup.center G) {x y : G} (hmem : ⁅x, y⁆ ∈ Z)
    (hcop : Nat.Coprime (Nat.card ↥Z) (orderOf y)) : Commute x y := by
  refine commute_of_commutatorElement_mem_center_of_coprime (hZ hmem) ?_
  refine Nat.Coprime.coprime_dvd_left ?_ hcop
  simpa using orderOf_dvd_natCard (⟨⁅x, y⁆, hmem⟩ : ↥Z)

end OddOrder.GroupTheory
