/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# 可換群の冪核 `Ω` と冪像 `℧`

`OddOrder.GroupTheory` shared module。可換群 `Q` (`[Group Q] [IsMulCommutative Q]`) に対し

* `powKernel Q n = {x | x ^ n = 1}` — `p`-群の文脈での `Ω_i(Q)` (`n = p ^ i`)
* `powImage Q n = {x ^ n | x ∈ Q}` — 同じく `℧^i(Q)`

を `n` 乗写像 `powHom Q n : Q →* Q` の核・像として定義する。どちらも**特性部分群**であり、
第一同型定理から `|Ω_n| · |℧_n| = |Q|` が従う。

⚠ `IsMulCommutative` は mixin (Prop クラス) なので `CommGroup` instance を新たに入れる必要が無く、
`↥(P : Subgroup G)` のような部分群の carrier にそのまま使える (`CommGroup` を `letI` すると
`Subgroup.toGroup` との instance diamond が起きる)。

用途: Isaacs Problem 5C.3 (可換 Sylow-2 が位数 `2^5` なら初等可換) — `Ω`/`℧` の位数を
数え上げて「指数 2 の特性部分群対」を作り Problem 5C.2 に流し込む。
-/

namespace OddOrder.GroupTheory

variable {Q : Type*} [Group Q] [IsMulCommutative Q]

section /- 定義 -/

/-- 可換群の `n` 乗写像 (可換性より準同型)。 -/
def powHom (Q : Type*) [Group Q] [IsMulCommutative Q] (n : ℕ) : Q →* Q where
  toFun x := x ^ n
  map_one' := one_pow n
  map_mul' a b := Commute.mul_pow (show Commute a b from mul_comm' a b) n

@[simp]
theorem powHom_apply (n : ℕ) (x : Q) : powHom Q n x = x ^ n := rfl

/-- `Ω_n(Q) := {x ∈ Q | x ^ n = 1}` (`n` 乗写像の核)。 -/
def powKernel (Q : Type*) [Group Q] [IsMulCommutative Q] (n : ℕ) : Subgroup Q :=
  (powHom Q n).ker

/-- `℧_n(Q) := {x ^ n | x ∈ Q}` (`n` 乗写像の像)。 -/
def powImage (Q : Type*) [Group Q] [IsMulCommutative Q] (n : ℕ) : Subgroup Q :=
  (powHom Q n).range

@[simp]
theorem mem_powKernel {n : ℕ} {x : Q} : x ∈ powKernel Q n ↔ x ^ n = 1 := Iff.rfl

@[simp]
theorem mem_powImage {n : ℕ} {x : Q} : x ∈ powImage Q n ↔ ∃ y : Q, y ^ n = x := Iff.rfl

end

section /- 特性部分群 -/

/-- `Ω_n(Q)` は特性部分群 (自己同型は `n` 乗と可換)。 -/
instance powKernel_characteristic (n : ℕ) : (powKernel Q n).Characteristic :=
  Subgroup.characteristic_iff_comap_eq.mpr fun ϕ => by
    ext x
    rw [Subgroup.mem_comap, mem_powKernel, mem_powKernel, MulEquiv.coe_toMonoidHom,
      ← map_pow, map_eq_one_iff _ ϕ.injective]

/-- `℧_n(Q)` は特性部分群。 -/
instance powImage_characteristic (n : ℕ) : (powImage Q n).Characteristic :=
  Subgroup.characteristic_iff_comap_eq.mpr fun ϕ => by
    ext x
    rw [Subgroup.mem_comap, mem_powImage, mem_powImage, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨ϕ.symm y, ϕ.injective (by rw [map_pow, MulEquiv.apply_symm_apply, hy])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨ϕ y, (map_pow ϕ y n).symm⟩

end

section /- 位数 -/

/-- **第一同型定理**: `|Ω_n(Q)| · |℧_n(Q)| = |Q|`。 -/
theorem card_powKernel_mul_card_powImage [Finite Q] (n : ℕ) :
    Nat.card (powKernel Q n) * Nat.card (powImage Q n) = Nat.card Q := by
  have h := Subgroup.card_mul_index (powKernel Q n)
  rw [← h]
  congr 1
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (powHom Q n)).toEquiv.symm

end

section /- 単調性・不動点 -/

/-- `℧_{m·n}(Q) ≤ ℧_n(Q)`。 -/
theorem powImage_mul_le (m n : ℕ) : powImage Q (m * n) ≤ powImage Q n := by
  rintro - ⟨y, rfl⟩
  refine ⟨y ^ m, ?_⟩
  simp only [powHom_apply, ← pow_mul]

/-- `Ω_n(Q) ≤ Ω_{m·n}(Q)`。 -/
theorem powKernel_le_mul (m n : ℕ) : powKernel Q n ≤ powKernel Q (m * n) := by
  intro x hx
  rw [mem_powKernel] at hx ⊢
  rw [mul_comm, pow_mul, hx, one_pow]

/-- `Ω_{m·n}(Q) = ⊤` なら `℧_m(Q) ≤ Ω_n(Q)`。 -/
theorem powImage_le_powKernel {m n : ℕ} (h : powKernel Q (m * n) = ⊤) :
    powImage Q m ≤ powKernel Q n := by
  rintro - ⟨y, rfl⟩
  have hy : y ∈ powKernel Q (m * n) := h ▸ Subgroup.mem_top y
  rw [mem_powKernel] at hy ⊢
  simp only [powHom_apply, ← pow_mul]
  exact hy

/-- `∀ x, x ^ n = 1` なら `Ω_n(Q) = ⊤`。 -/
theorem powKernel_eq_top {n : ℕ} (h : ∀ x : Q, x ^ n = 1) : powKernel Q n = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr h

/-- ⭐ **`Ω` の不動点補題**: `Ω_{2n}(Q) = Ω_n(Q)` なら `Ω_{2^k·n}(Q) = Ω_n(Q)` (全ての `k`)。

冪核の鎖が一度でも止まれば以後ずっと止まる。有限 2-群では `Ω_{2^k}(Q) = ⊤` になる `k` が
取れるので、「`Ω` の鎖が止まる ⇒ `Ω_n(Q) = ⊤`」という形で使う。 -/
theorem powKernel_two_pow_mul_eq {n : ℕ} (h : powKernel Q (2 * n) = powKernel Q n) :
    ∀ k : ℕ, powKernel Q (2 ^ k * n) = powKernel Q n := by
  intro k
  induction k with
  | zero => rw [pow_zero, one_mul]
  | succ k ih =>
    refine le_antisymm (fun x hx => ?_) (powKernel_le_mul _ _)
    rw [mem_powKernel] at hx
    have he : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by
      rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc]
    rw [he] at hx
    have hx2 : x ^ 2 ∈ powKernel Q (2 ^ k * n) := by
      rw [mem_powKernel, ← pow_mul]
      exact hx
    rw [ih, mem_powKernel] at hx2
    have hx2n : x ∈ powKernel Q (2 * n) := by
      rw [mem_powKernel, pow_mul]
      exact hx2
    rwa [h] at hx2n

end

end OddOrder.GroupTheory
