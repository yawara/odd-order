/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionTI

/-!
# Isaacs Problem 6B.4 — 部分が互いに可換な分割 (書籍 p. 195)

**主張**: 群 `G` が分割 `Π` を持ち, 相異なる部分 `X ≠ Y` について常に `⁅X, Y⁆ = 1` なら

* **(a)** `G` は可換
* **(b)** `G` の非単位元はすべて等しい素数位数を持つ (したがって `G` は基本可換)

**証明の要**: `1 ≠ x ∈ X`, `1 ≠ z ∈ Y` (`X ≠ Y`) のとき `xz` の属する部分 `W` は
**`X` でも `Y` でもない** (`W = X` なら `z = x⁻¹(xz) ∈ X ⊓ Y = 1`, `W = Y` も同様)。

* **(a)**: `x, y` が同じ部分 `X` にあるとき, `X` は真部分群なので別の部分の非単位元 `g` が
  取れる。上の事実で `xg` は `X` と異なる部分に入るから `(xg)y = y(xg)`, また `gy = yg`
  なので `xy = yx`。
* **(b)**: 異なる部分の `x, y` について `m = o(x)` とすると `(xy)^m = y^m` は `W` にも `Y` にも
  入るので `y^m = 1`, すなわち `o(y) ∣ o(x)`。対称性から `o(x) = o(y)`。同じ部分の場合は
  第三の部分を経由する。最後に共通の位数 `n` が素数であること (`n` の素因子 `p` について
  `x^(n/p)` の位数が `p` かつ `= n`) を見る。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6B.4: 部分が互いに可換な分割 (p. 195) -/

variable {G : Type*} [Group G]

/-- 相異なる部分の元は可換 (`⁅X, Y⁆ = ⊥` の元レベル版)。 -/
theorem commute_of_mem_parts_ne (P : SubgroupPartition G)
    (hcomm : ∀ X ∈ P.parts, ∀ Y ∈ P.parts, X ≠ Y → ⁅X, Y⁆ = ⊥)
    {X Y : Subgroup G} (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hne : X ≠ Y)
    {x y : G} (hx : x ∈ X) (hy : y ∈ Y) : x * y = y * x := by
  have h := Subgroup.commutator_mem_commutator (H₁ := X) (H₂ := Y) hx hy
  rw [hcomm X hX Y hY hne, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

/-- **鍵となる事実**: 相異なる部分の非単位元の積は, どちらの部分とも異なる部分に入る。 -/
theorem exists_part_ne_of_mul (P : SubgroupPartition G)
    {X Y : Subgroup G} (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hXY : X ≠ Y)
    {x z : G} (hx : x ∈ X) (hxne : x ≠ 1) (hz : z ∈ Y) (hzne : z ≠ 1) :
    ∃ W, W ∈ P.parts ∧ x * z ∈ W ∧ W ≠ X ∧ W ≠ Y := by
  obtain ⟨W, hW, hxzW⟩ := P.cover (x * z)
  refine ⟨W, hW, hxzW, ?_, ?_⟩
  · rintro rfl
    have hzXY : z ∈ W ⊓ Y := ⟨by simpa using W.mul_mem (W.inv_mem hx) hxzW, hz⟩
    rw [P.inf_eq_bot_of_ne hX hY hXY, Subgroup.mem_bot] at hzXY
    exact hzne hzXY
  · rintro rfl
    have hxXY : x ∈ X ⊓ W := ⟨hx, by simpa using W.mul_mem hxzW (W.inv_mem hz)⟩
    rw [P.inf_eq_bot_of_ne hX hY hXY, Subgroup.mem_bot] at hxXY
    exact hxne hxXY

/-- 部分 `X` の外の非単位元と, それを含む別の部分。 -/
theorem exists_part_ne_of_mem_parts (P : SubgroupPartition G)
    {X : Subgroup G} (hX : X ∈ P.parts) :
    ∃ (Z : Subgroup G) (g : G), Z ∈ P.parts ∧ Z ≠ X ∧ g ∈ Z ∧ g ≠ 1 ∧ g ∉ X := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ X := by
    by_contra hcon
    exact P.proper X hX
      (eq_top_iff.mpr fun g _ => not_not.mp fun hgX => hcon ⟨g, hgX⟩)
  obtain ⟨Z, hZ, hgZ⟩ := P.cover g
  exact ⟨Z, g, hZ, fun h => hg (h ▸ hgZ), hgZ, fun h => hg (h ▸ X.one_mem), hg⟩

/-- **Isaacs Problem 6B.4(a)** (p. 195) ⭐: 分割の相異なる部分が互いに可換なら `G` は可換。 -/
theorem mul_comm_of_partition_of_commutator_eq_bot (P : SubgroupPartition G)
    (hcomm : ∀ X ∈ P.parts, ∀ Y ∈ P.parts, X ≠ Y → ⁅X, Y⁆ = ⊥) (x y : G) :
    x * y = y * x := by
  classical
  rcases eq_or_ne x 1 with rfl | hxne
  · simp
  rcases eq_or_ne y 1 with rfl | hyne
  · simp
  obtain ⟨X, hX, hxX⟩ := P.cover x
  obtain ⟨Y, hY, hyY⟩ := P.cover y
  by_cases hXY : X = Y
  · subst hXY
    obtain ⟨Z, g, hZ, hZX, hgZ, hgne, _⟩ := exists_part_ne_of_mem_parts P hX
    obtain ⟨W, hW, hxgW, hWX, _⟩ :=
      exists_part_ne_of_mul P hX hZ (Ne.symm hZX) hxX hxne hgZ hgne
    have h1 : (x * g) * y = y * (x * g) :=
      commute_of_mem_parts_ne P hcomm hW hX hWX hxgW hyY
    have h2 : g * y = y * g := commute_of_mem_parts_ne P hcomm hZ hX hZX hgZ hyY
    have h3 : (x * y) * g = (y * x) * g := by
      calc (x * y) * g = x * (y * g) := by group
        _ = x * (g * y) := by rw [h2]
        _ = (x * g) * y := by group
        _ = y * (x * g) := h1
        _ = (y * x) * g := by group
    exact mul_right_cancel h3
  · exact commute_of_mem_parts_ne P hcomm hX hY hXY hxX hyY

/-- 異なる部分の非単位元の位数は互いに割り切る。 -/
theorem orderOf_dvd_of_mem_parts_ne [Finite G] (P : SubgroupPartition G)
    (hcomm : ∀ X ∈ P.parts, ∀ Y ∈ P.parts, X ≠ Y → ⁅X, Y⁆ = ⊥)
    {X Y : Subgroup G} (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hXY : X ≠ Y)
    {x y : G} (hx : x ∈ X) (hxne : x ≠ 1) (hy : y ∈ Y) (hyne : y ≠ 1) :
    orderOf y ∣ orderOf x := by
  obtain ⟨W, hW, hxyW, _, hWY⟩ := exists_part_ne_of_mul P hX hY hXY hx hxne hy hyne
  have hc : Commute x y := commute_of_mem_parts_ne P hcomm hX hY hXY hx hy
  have hpow : (x * y) ^ orderOf x = y ^ orderOf x := by
    rw [hc.mul_pow, pow_orderOf_eq_one, one_mul]
  have hmem : y ^ orderOf x ∈ W := hpow ▸ W.pow_mem hxyW (orderOf x)
  by_contra hnd
  have hne : y ^ orderOf x ≠ 1 := fun h => hnd (orderOf_dvd_of_pow_eq_one h)
  have hin : y ^ orderOf x ∈ W ⊓ Y := ⟨hmem, Y.pow_mem hy (orderOf x)⟩
  rw [P.inf_eq_bot_of_ne hW hY hWY, Subgroup.mem_bot] at hin
  exact hne hin

/-- 非単位元の位数はすべて等しい。 -/
theorem orderOf_eq_orderOf_of_partition [Finite G] (P : SubgroupPartition G)
    (hcomm : ∀ X ∈ P.parts, ∀ Y ∈ P.parts, X ≠ Y → ⁅X, Y⁆ = ⊥)
    {x y : G} (hxne : x ≠ 1) (hyne : y ≠ 1) : orderOf x = orderOf y := by
  classical
  obtain ⟨X, hX, hxX⟩ := P.cover x
  obtain ⟨Y, hY, hyY⟩ := P.cover y
  by_cases hXY : X = Y
  · subst hXY
    obtain ⟨Z, g, hZ, hZX, hgZ, hgne, _⟩ := exists_part_ne_of_mem_parts P hX
    have e1 : orderOf x = orderOf g :=
      Nat.dvd_antisymm
        (orderOf_dvd_of_mem_parts_ne P hcomm hZ hX hZX hgZ hgne hxX hxne)
        (orderOf_dvd_of_mem_parts_ne P hcomm hX hZ (Ne.symm hZX) hxX hxne hgZ hgne)
    have e2 : orderOf y = orderOf g :=
      Nat.dvd_antisymm
        (orderOf_dvd_of_mem_parts_ne P hcomm hZ hX hZX hgZ hgne hyY hyne)
        (orderOf_dvd_of_mem_parts_ne P hcomm hX hZ (Ne.symm hZX) hyY hyne hgZ hgne)
    rw [e1, e2]
  · exact Nat.dvd_antisymm
      (orderOf_dvd_of_mem_parts_ne P hcomm hY hX (Ne.symm hXY) hyY hyne hxX hxne)
      (orderOf_dvd_of_mem_parts_ne P hcomm hX hY hXY hxX hxne hyY hyne)

/-- **Isaacs Problem 6B.4(b)** (p. 195) ⭐: (a) と合わせて `G` は基本可換 —
非単位元の位数はすべて等しい素数。 -/
theorem exists_prime_forall_orderOf_eq_of_partition [Finite G] [Nontrivial G]
    (P : SubgroupPartition G)
    (hcomm : ∀ X ∈ P.parts, ∀ Y ∈ P.parts, X ≠ Y → ⁅X, Y⁆ = ⊥) :
    ∃ p : ℕ, p.Prime ∧ ∀ x : G, x ≠ 1 → orderOf x = p := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_ne (1 : G)
  refine ⟨orderOf x₀, ?_, fun x hx => orderOf_eq_orderOf_of_partition P hcomm hx hx₀⟩
  by_contra hnp
  have hne1 : orderOf x₀ ≠ 1 := fun h => hx₀ (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne1
  have hpos : 0 < orderOf x₀ := orderOf_pos x₀
  have hw : orderOf (x₀ ^ (orderOf x₀ / p)) = p := by
    rw [orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd hpos hdvd) hp.pos).ne'
      (Nat.div_dvd_of_dvd hdvd)]
    exact Nat.div_div_self hdvd hpos.ne'
  have hwne : x₀ ^ (orderOf x₀ / p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw
    exact hp.one_lt.ne hw
  have := orderOf_eq_orderOf_of_partition P hcomm hwne hx₀
  rw [hw] at this
  exact hnp (this ▸ hp)

end

end OddOrder.Isaacs.Ch06
