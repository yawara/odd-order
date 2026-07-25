/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main.BaerMulGroup

/-!
# Isaacs Chapter 4 — Problem 4D.2 (Baer 加法における `xy - yx = ⁅x, y⁆`)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4D.2 (書籍 p. 145)。

`G` を奇数位数の class `≤ 2` の冪零群とすると, Lemma 4.36/4.37 の Baer trick で
`x +' y := x * y * √⁅y, x⁆` (`baerAdd`) が `G` 上の可換群構造を与える (`BaerMul G`)。
このとき **群の積 `xy` と `yx` の加法的な差が交換子に一致する**:

`(x * y) - (y * x) = ⁅x, y⁆`.

`BaerMul G` の減法 `u / v = u +' (-v)` (`-v` は `G` の逆元) で述べる
(`baerMul_div_eq_commutator`)。素の形は `baerAdd_mul_inv_of_commutator_le_center`。

⚠ この等式自体には**奇数位数は不要** — `⁅x, y⁆` が中心的 (class `≤ 2`) であれば
`x * y` と `y * x` は可換なので `√⁅(y*x)⁻¹, x*y⁆ = √1 = 1` となり, 残るのは群の恒等式
`(x * y) * (y * x)⁻¹ = ⁅x, y⁆`。奇数位数が要るのは `baerAdd` が群構造になる部分
(`BaerMul.instCommGroup`) であって, 差の計算そのものではない。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4D.2 (p. 145) -/

variable {G : Type*} [Group G]

/-- class `≤ 2` の群では `x * y` と `y * x` は可換 (`x * y = ⁅x, y⁆ * (y * x)` で
`⁅x, y⁆` は中心的)。 -/
theorem commute_mul_mul_comm_of_commutator_le_center
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    Commute (x * y) (y * x) := by
  have hc : ⁅x, y⁆ ∈ Subgroup.center G :=
    hC (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hcb : Commute ⁅x, y⁆ (y * x) := (Subgroup.mem_center_iff.mp hc (y * x)).symm
  have hxy : x * y = ⁅x, y⁆ * (y * x) := by
    rw [commutatorElement_def]; group
  rw [hxy]
  exact hcb.mul_left (Commute.refl (y * x))

/-- **Isaacs Problem 4D.2** (素の形): class `≤ 2` の群で
`(x * y) +' (y * x)⁻¹ = ⁅x, y⁆`。 -/
theorem baerAdd_mul_inv_of_commutator_le_center
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    baerAdd (x * y) (y * x)⁻¹ = ⁅x, y⁆ := by
  rw [baerAdd_eq_mul_of_commute
    ((commute_mul_mul_comm_of_commutator_le_center hC x y).inv_right),
    commutatorElement_def]
  group

/-- **Isaacs Problem 4D.2**: 奇数位数の class `≤ 2` の群 `G` の Baer 加法構造
(`BaerMul G`) において `(x * y) - (y * x) = ⁅x, y⁆`。 -/
theorem baerMul_div_eq_commutator [Fact (Odd (Nat.card G))]
    [hC : Fact (_root_.commutator G ≤ Subgroup.center G)] (x y : G) :
    (BaerMul.ofG (x * y) : BaerMul G) / BaerMul.ofG (y * x) = BaerMul.ofG ⁅x, y⁆ := by
  change BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (x * y)))
      (BaerMul.toG (BaerMul.ofG (BaerMul.toG (BaerMul.ofG (y * x)))⁻¹))) = _
  simp only [BaerMul.toG_ofG]
  exact congr_arg BaerMul.ofG (baerAdd_mul_inv_of_commutator_le_center hC.out x y)

end

end OddOrder.Isaacs.Ch04
