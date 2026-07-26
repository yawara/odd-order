/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-!
# 中心的交換子の双線形性

`OddOrder.GroupTheory` shared module: `⁅x, y⁆ ∈ Z(G)` のとき

* `⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n`
* `⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n`

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

end OddOrder.GroupTheory
