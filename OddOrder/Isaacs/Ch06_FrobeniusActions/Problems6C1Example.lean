/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6C1
import OddOrder.Mathlib.SemidirectProduct

/-!
# Isaacs Problem 6C.1(b) — 位数 4 の固定点自由自己同型では冪零にならない例 (書籍 p. 197)

6C.1(a) は「素数位数の固定点自由な自己同型をもつ群は冪零」だが, **位数 `4`** では結論が壊れる。
書籍の hint どおり `|G| = 75` の例を構成する。

**構成**: `V := (ℤ/5)²` (乗法記法), `B := ` `x² + x + 1` の companion 行列
(`B (x, y) = (-y, x - y)`; `x² + x + 1` は mod 5 で既約なので `B` は固有値 `1` を持たない,
位数 `3`)。`G := V ⋊ ⟨B⟩` は位数 `75` で, `⟨B⟩` の作用が固定点自由なので `Z(G) = 1`,
したがって**非冪零**。

自己同型は `α (v, c) := (A v, c⁻¹)` (`A := 2σ`, `σ` は Frobenius `x ↦ x⁵` の行列
`A (x, y) = (2x - 2y, -2y)`)。`A B A⁻¹ = B⁻¹` なので `α` は準同型で
(`SemidirectProduct.congr`), `A² = -1` から

* `α² (v, c) = (v⁻¹, c)` ゆえ `α` の位数はちょうど `4`,
* `α` の固定点は `A v = v` かつ `c⁻¹ = c` を満たすもの = 単位元のみ

となる (`A` は固有値 `1` を持たず, `|⟨B⟩| = 3` は奇数)。
-/

namespace OddOrder.Isaacs.Ch06

namespace Order75Example

/-- 反例の核: `(ℤ/5)²` を乗法記法で見たもの (位数 `25` の elementary abelian 群)。 -/
abbrev Kernel : Type := Multiplicative (ZMod 5 × ZMod 5)

/-- `x² + x + 1` の companion 行列の作用 `(x, y) ↦ (-y, x - y)` (位数 `3`)。 -/
def bMap (p : ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 := (-p.2, p.1 - p.2)

/-- `bMap` の逆写像 (`= bMap²`)。 -/
def bMapInv (p : ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 := (p.2 - p.1, -p.1)

/-- `A = 2σ` の作用 `(x, y) ↦ (2x - 2y, -2y)` (`σ` は Frobenius, `A² = -1`)。 -/
def aMap (p : ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 := (2 * p.1 - 2 * p.2, -(2 * p.2))

/-- `aMap` の逆写像 (`= -aMap`)。 -/
def aMapInv (p : ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 := (2 * p.2 - 2 * p.1, 2 * p.2)

/-- 核の位数 `3` の自己同型 `B`。 -/
def bAut : MulAut Kernel where
  toFun v := Multiplicative.ofAdd (bMap (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd (bMapInv (Multiplicative.toAdd v))
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- 核の位数 `4` の自己同型 `A`。 -/
def aAut : MulAut Kernel where
  toFun v := Multiplicative.ofAdd (aMap (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd (aMapInv (Multiplicative.toAdd v))
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

@[simp] theorem bAut_apply (v : Kernel) :
    bAut v = Multiplicative.ofAdd (bMap (Multiplicative.toAdd v)) := rfl

@[simp] theorem aAut_apply (v : Kernel) :
    aAut v = Multiplicative.ofAdd (aMap (Multiplicative.toAdd v)) := rfl

theorem bAut_pow_three : bAut ^ 3 = 1 := by
  refine MulEquiv.ext ?_
  decide

theorem bAut_ne_one : bAut ≠ 1 := by
  intro h
  have := congrArg (fun f : MulAut Kernel => f (Multiplicative.ofAdd (1, 0))) h
  simp only [bAut_apply, bMap] at this
  revert this
  decide

theorem orderOf_bAut : orderOf bAut = 3 := by
  have hdvd : orderOf bAut ∣ 3 := orderOf_dvd_of_pow_eq_one bAut_pow_three
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) bAut_ne_one
  · exact h3

/-- `A` は `B` を反転する: `A B A⁻¹ = B⁻¹` (Frobenius が `ω ↦ ω⁵ = ω²` を与えることの行列版)。 -/
theorem aAut_mul_bAut : aAut * bAut = bAut⁻¹ * aAut := by
  refine MulEquiv.ext ?_
  decide

theorem aAut_pow_two_apply (v : Kernel) : (aAut * aAut) v = v⁻¹ := by
  revert v
  decide

theorem aAut_pow_four : aAut ^ 4 = 1 := by
  refine MulEquiv.ext ?_
  decide

/-- `A` は固有値 `1` を持たない: 固定点は単位元のみ。 -/
theorem aAut_fixedFree (v : Kernel) (h : aAut v = v) : v = 1 := by
  revert h
  revert v
  decide

/-- `B` は固有値 `1` を持たない: 固定点は単位元のみ。 -/
theorem bAut_fixedFree (v : Kernel) (h : bAut v = v) : v = 1 := by
  revert h
  revert v
  decide

/-- 反例の補群 `⟨B⟩ ≤ Aut(V)` (位数 `3`)。 -/
abbrev Complement : Subgroup (MulAut Kernel) := Subgroup.zpowers bAut

theorem card_complement : Nat.card ↥Complement = 3 := by
  rw [Nat.card_zpowers, orderOf_bAut]

/-- **反例の群** `G = V ⋊ ⟨B⟩` (位数 `75`, 非冪零)。 -/
abbrev Group75 : Type := SemidirectProduct Kernel ↥Complement Complement.subtype

/-- `⟨B⟩` の非自明元は `V` に固定点自由に作用する (素数位数なので `⟨c⟩ = ⟨B⟩ ∋ B`)。 -/
theorem complement_fixedFree {c : ↥Complement} (hc : c ≠ 1) {v : Kernel}
    (h : (c : MulAut Kernel) v = v) : v = 1 := by
  have hgen : Subgroup.zpowers ((c : MulAut Kernel)) = Complement :=
    Subgroup.zpowers_eq_of_prime_card (by rw [card_complement]; exact Nat.prime_three) c.2
      (fun hcc => hc (Subtype.ext hcc))
  have hmem : bAut ∈ Subgroup.zpowers ((c : MulAut Kernel)) := by
    rw [hgen]; exact Subgroup.mem_zpowers bAut
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine bAut_fixedFree v ?_
  have hstab : (c : MulAut Kernel) ∈ MulAction.stabilizer (MulAut Kernel) v := h
  have := zpow_mem hstab m
  rw [hm] at this
  exact this

/-- `⟨B⟩` の元は互いに可換 (巡回群)。 -/
theorem complement_comm (a b : ↥Complement) : a * b = b * a := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hk, ← zpow_add, ← zpow_add, add_comm]

/-- 補群の反転写像 (巡回群なので自己同型)。 -/
def complementInv : ↥Complement ≃* ↥Complement where
  toFun c := c⁻¹
  invFun c := c⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' a b := by rw [mul_inv_rev, complement_comm]

/-- `A` は `⟨B⟩` の任意の元を反転する: `A c A⁻¹ = c⁻¹`。 -/
theorem aAut_mul_complement (c : ↥Complement) :
    aAut * (c : MulAut Kernel) = ((c : MulAut Kernel))⁻¹ * aAut := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp c.2
  have hconj : MulAut.conj aAut bAut = bAut⁻¹ := by
    change aAut * bAut * aAut⁻¹ = bAut⁻¹
    rw [aAut_mul_bAut, mul_assoc, mul_inv_cancel, mul_one]
  have hzpow : MulAut.conj aAut (bAut ^ m) = (bAut ^ m)⁻¹ := by
    rw [map_zpow, hconj, inv_zpow]
  rw [← hm]
  have h : aAut * bAut ^ m * aAut⁻¹ = (bAut ^ m)⁻¹ := hzpow
  calc aAut * bAut ^ m = (aAut * bAut ^ m * aAut⁻¹) * aAut := by group
    _ = (bAut ^ m)⁻¹ * aAut := by rw [h]

/-- **反例の位数 `4` の自己同型** `α (v, c) = (A v, c⁻¹)`。 -/
def alphaAut : MulAut Group75 :=
  SemidirectProduct.congr aAut complementInv (fun c => by
    refine MulEquiv.ext fun v => ?_
    exact congrArg (fun f : MulAut Kernel => f v) (aAut_mul_complement c))

@[simp] theorem alphaAut_left (x : Group75) : (alphaAut x).left = aAut x.left := rfl

@[simp] theorem alphaAut_right (x : Group75) : (alphaAut x).right = (x.right)⁻¹ := rfl

theorem card_group75 : Nat.card Group75 = 75 := by
  rw [SemidirectProduct.card, card_complement]
  have hker : Nat.card Kernel = 25 := by
    have h : Nat.card (ZMod 5 × ZMod 5) = 25 := by
      simp [Nat.card_eq_fintype_card]
    exact (Nat.card_congr (Equiv.refl _)).trans h
  rw [hker]

theorem alphaAut_sq_left (x : Group75) : ((alphaAut * alphaAut) x).left = (x.left)⁻¹ := by
  change aAut (aAut x.left) = (x.left)⁻¹
  exact aAut_pow_two_apply x.left

theorem alphaAut_sq_right (x : Group75) : ((alphaAut * alphaAut) x).right = x.right := by
  change ((x.right)⁻¹)⁻¹ = x.right
  exact inv_inv _

theorem alphaAut_pow_four : alphaAut ^ 4 = 1 := by
  have h : alphaAut ^ 4 = (alphaAut * alphaAut) * (alphaAut * alphaAut) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [h]
  refine MulEquiv.ext fun x => ?_
  refine SemidirectProduct.ext ?_ ?_
  · change ((alphaAut * alphaAut) ((alphaAut * alphaAut) x)).left = x.left
    rw [alphaAut_sq_left, alphaAut_sq_left, inv_inv]
  · change ((alphaAut * alphaAut) ((alphaAut * alphaAut) x)).right = x.right
    rw [alphaAut_sq_right, alphaAut_sq_right]

theorem alphaAut_sq_ne_one : alphaAut * alphaAut ≠ 1 := by
  intro h
  have hx : ((alphaAut * alphaAut) (SemidirectProduct.inl
      (Multiplicative.ofAdd ((1, 0) : ZMod 5 × ZMod 5)))).left
      = (Multiplicative.ofAdd ((1, 0) : ZMod 5 × ZMod 5)) := by
    rw [h]
    rfl
  rw [alphaAut_sq_left] at hx
  have : (Multiplicative.ofAdd ((1, 0) : ZMod 5 × ZMod 5))⁻¹
      ≠ Multiplicative.ofAdd ((1, 0) : ZMod 5 × ZMod 5) := by decide
  exact this hx

theorem orderOf_alphaAut : orderOf alphaAut = 4 := by
  have hdvd : orderOf alphaAut ∣ 2 ^ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    simpa using alphaAut_pow_four
  obtain ⟨i, hi, hpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hle : ¬ orderOf alphaAut ∣ 2 := by
    intro hd
    refine alphaAut_sq_ne_one ?_
    have := orderOf_dvd_iff_pow_eq_one.mp hd
    rw [← sq]
    exact this
  interval_cases i
  · exact absurd (by rw [hpow]; norm_num : orderOf alphaAut ∣ 2) hle
  · exact absurd (by rw [hpow]; norm_num : orderOf alphaAut ∣ 2) hle
  · rw [hpow]; norm_num

/-- `α` の固定点は単位元のみ。 -/
theorem alphaAut_fixedFree (x : Group75) (h : alphaAut x = x) : x = 1 := by
  have hleft : aAut x.left = x.left := by rw [← alphaAut_left, h]
  have hright : (x.right)⁻¹ = x.right := by rw [← alphaAut_right, h]
  refine SemidirectProduct.ext ?_ ?_
  · rw [aAut_fixedFree x.left hleft]; rfl
  · -- `|⟨B⟩| = 3` は奇数なので `c⁻¹ = c` は `c = 1` を強制する
    have hsq : x.right ^ 2 = 1 := by
      have h1 : x.right⁻¹ * x.right = 1 := inv_mul_cancel _
      rw [hright] at h1
      rw [pow_two]
      exact h1
    have hdvd3 : orderOf x.right ∣ 3 := by
      have h := orderOf_dvd_natCard x.right
      rwa [card_complement] at h
    have hdvd2 : orderOf x.right ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hone : orderOf x.right = 1 :=
      Nat.eq_one_of_dvd_coprimes (by norm_num) hdvd3 hdvd2
    rw [orderOf_eq_one_iff.mp hone]; rfl

/-- `G` の中心は自明 (`⟨B⟩` の作用が固定点自由だから)。 -/
theorem center_eq_bot : Subgroup.center Group75 = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hmem := Subgroup.mem_center_iff.mp hx
  -- (1) `x.right` は `V` 上自明に作用するので `x.right = 1`
  have hright : x.right = 1 := by
    by_contra hne
    have hfix : ∀ w : Kernel, (x.right : MulAut Kernel) w = w := by
      intro w
      have hl : w * x.left = x.left * ((x.right : MulAut Kernel) w) :=
        congrArg SemidirectProduct.left (hmem (SemidirectProduct.inl w))
      have hcancel : x.left * w = x.left * ((x.right : MulAut Kernel) w) := by
        rw [← hl, mul_comm]
      exact (mul_left_cancel hcancel).symm
    exact absurd (complement_fixedFree hne (hfix (Multiplicative.ofAdd ((1, 0) : ZMod 5 × ZMod 5))))
      (by decide)
  -- (2) `x.left` は `B` に固定されるので `x.left = 1`
  have hleft : x.left = 1 := by
    have hl : (1 : Kernel) * bAut x.left = x.left * ((x.right : MulAut Kernel) 1) :=
      congrArg SemidirectProduct.left
        (hmem (SemidirectProduct.inr ⟨bAut, Subgroup.mem_zpowers bAut⟩))
    rw [one_mul, map_one, mul_one] at hl
    exact bAut_fixedFree x.left hl
  refine Subgroup.mem_bot.mpr (SemidirectProduct.ext ?_ ?_)
  · rw [hleft]; rfl
  · rw [hright]; rfl

theorem not_isNilpotent_group75 : ¬ Group.IsNilpotent Group75 := by
  intro hnil
  have : Nontrivial Group75 := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [card_group75]
    norm_num
  exact Group.IsNilpotent.center_ne_bot (G := Group75) center_eq_bot

end Order75Example

section /- 6C.1(b): 位数 4 では冪零にならない例 (p. 197) -/

/-- **Isaacs Problem 6C.1(b)** (p. 197) ⭐: 6C.1(a) の「素数位数」は落とせない —
位数 `75` の**非冪零**群 `G = (ℤ/5)² ⋊ ⟨B⟩` と, 単位元しか固定しない**位数 `4`** の
`α ∈ Aut(G)` が存在する。 -/
theorem exists_orderOf_four_mulAut_fixedFree_not_isNilpotent :
    Nat.card Order75Example.Group75 = 75 ∧ orderOf Order75Example.alphaAut = 4 ∧
      (∀ g : Order75Example.Group75, Order75Example.alphaAut g = g → g = 1) ∧
      ¬ Group.IsNilpotent Order75Example.Group75 :=
  ⟨Order75Example.card_group75, Order75Example.orderOf_alphaAut,
    Order75Example.alphaAut_fixedFree, Order75Example.not_isNilpotent_group75⟩

end

end OddOrder.Isaacs.Ch06
