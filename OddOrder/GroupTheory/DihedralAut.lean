/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.ZMod.Aut
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.LinearCombination

/-!
# 二面体群の自己同型群 `Aut(D_{2n})` (`n` 奇数)

`n` が奇数のとき `Aut(D_{2n}) ≅ Hol(ℤ/n) = ℤ/n ⋊ (ℤ/n)ˣ` であり, さらにこの群は
**complete** (中心自明かつ自己同型がすべて内部) である。Isaacs Problem 9B.4
(書籍 p. 285, `D_{2n}` の automorphism tower は高々 2 種類の群しか含まない) の本体。

## 主結果

* `dihedralAut a u` — `r i ↦ r (u i)`, `sr i ↦ sr (u i + a)` で定まる `D_{2n}` の自己同型。
* `dihedralAut_mul` — 合成則 `(a, u) * (b, v) = (a + u b, u v)` (= holomorph の積)。
* `exists_dihedralAut` — `n` 奇数なら **すべての**自己同型がこの形 (全射性)。
* `dihedralAut_eq_iff` — 座標は一意 (単射性)。

## 実装ノート

抽象的な半直積 `SemidirectProduct` を経由せず, 座標 `(a, u)` を直接扱う。座標の抽出は
`rCoord` / `srCoord` (コンストラクタの成分を読むだけ) で行うので選択公理を使わない。

全射性の鍵は「回転部分群 `= {x | x ^ n = 1}`」(`n` 奇数) — これで任意の自己同型が回転を
回転へ写すことが分かり, `ℤ/n` の加法自己同型 = 単元倍 (`ZMod.AddAutEquivUnits` と同じ
`f x = f 1 * x` の筋) に帰着する。
-/

namespace OddOrder.GroupTheory

open DihedralGroup

open scoped commutatorElement

variable {n : ℕ}

section /- 回転部分群の characteristic 性 -/

/-- **`n` 奇数なら `D_{2n}` で `x ^ n = 1` ⟺ `x` は回転** (`r i` の形)。

回転は `(r i)^n = r (n • i) = r 0 = 1`, 鏡映は位数 2 で `n` が奇数なので `(sr i)^n ≠ 1`。
すなわち回転部分群は `{x | x ^ n = 1}` という自己同型不変な条件で書けるので
**characteristic**。 -/
theorem dihedral_pow_eq_one_iff_exists_r (hodd : Odd n) (x : DihedralGroup n) :
    x ^ n = 1 ↔ ∃ i : ZMod n, x = r i := by
  cases x with
  | r i =>
    refine ⟨fun _ => ⟨i, rfl⟩, fun _ => ?_⟩
    rw [r_pow]
    simp
  | sr i =>
    constructor
    · intro hx
      exfalso
      have h2 : (2 : ℕ) ∣ n := by
        have hdvd := orderOf_dvd_of_pow_eq_one hx
        rwa [orderOf_sr] at hdvd
      obtain ⟨k, hk⟩ := hodd
      omega
    · rintro ⟨j, hj⟩
      simp at hj

/-- 自己同型は回転を回転へ写す (`n` 奇数)。 -/
theorem exists_r_of_mulAut_r (hodd : Odd n) (α : MulAut (DihedralGroup n)) (i : ZMod n) :
    ∃ j, α (r i) = r j := by
  refine (dihedral_pow_eq_one_iff_exists_r hodd _).mp ?_
  rw [← map_pow]
  have : (r i : DihedralGroup n) ^ n = 1 := by
    rw [r_pow]; simp
  rw [this, map_one]

/-- 自己同型は鏡映を鏡映へ写す (`n` 奇数)。 -/
theorem exists_sr_of_mulAut_sr (hodd : Odd n) (α : MulAut (DihedralGroup n)) (i : ZMod n) :
    ∃ j, α (sr i) = sr j := by
  rcases h : α (sr i) with j | j
  · exfalso
    have hpow : (sr i : DihedralGroup n) ^ n = 1 := by
      have h1 : (α (sr i)) ^ n = 1 := by rw [h, r_pow]; simp
      rw [← map_pow] at h1
      exact α.injective (h1.trans (map_one α).symm)
    obtain ⟨k, hk⟩ := (dihedral_pow_eq_one_iff_exists_r hodd _).mp hpow
    exact absurd hk (by simp)
  · exact ⟨j, rfl⟩

end /- 回転部分群の characteristic 性 -/

section /- 座標 `(a, u)` による記述 -/

/-- `D_{2n}` の元の回転成分 (鏡映には `0` を返す)。座標抽出用の補助関数。 -/
def rCoord : DihedralGroup n → ZMod n
  | .r i => i
  | .sr _ => 0

/-- `D_{2n}` の元の鏡映成分 (回転には `0` を返す)。座標抽出用の補助関数。 -/
def srCoord : DihedralGroup n → ZMod n
  | .r _ => 0
  | .sr i => i

@[simp] theorem rCoord_r (i : ZMod n) : rCoord (r i) = i := rfl
@[simp] theorem srCoord_sr (i : ZMod n) : srCoord (sr i) = i := rfl
@[simp] theorem rCoord_one : rCoord (1 : DihedralGroup n) = 0 := rfl

/-- `Aut(D_{2n})` の元の下敷きになる写像: `r i ↦ r (u i)`, `sr i ↦ sr (u i + a)`。 -/
def dihedralAutFun (a : ZMod n) (u : (ZMod n)ˣ) : DihedralGroup n → DihedralGroup n
  | .r i => r ((u : ZMod n) * i)
  | .sr i => sr ((u : ZMod n) * i + a)

/-- **`D_{2n}` の自己同型 `φ_{a,u}`**: `r i ↦ r (u i)`, `sr i ↦ sr (u i + a)`。

`n` が奇数ならこれで `Aut(D_{2n})` を尽くす (`exists_dihedralAut`)。座標の積は
holomorph `ℤ/n ⋊ (ℤ/n)ˣ` の積 `(a, u)(b, v) = (a + u b, u v)` (`dihedralAut_mul`)。 -/
def dihedralAut (a : ZMod n) (u : (ZMod n)ˣ) : MulAut (DihedralGroup n) where
  toFun := dihedralAutFun a u
  invFun := dihedralAutFun (-((↑u⁻¹ : ZMod n) * a)) u⁻¹
  left_inv x := by
    cases x with
    | r i => simp only [dihedralAutFun, r.injEq, ← mul_assoc]; rw [← Units.val_mul]; simp
    | sr i =>
      simp only [dihedralAutFun, sr.injEq, mul_add, ← mul_assoc]
      rw [← Units.val_mul]
      simp
  right_inv x := by
    cases x with
    | r i => simp only [dihedralAutFun, r.injEq, ← mul_assoc]; rw [← Units.val_mul]; simp
    | sr i =>
      simp only [dihedralAutFun, sr.injEq, mul_add, mul_neg, ← mul_assoc]
      rw [← Units.val_mul]
      simp
  map_mul' x y := by
    cases x with
    | r i => cases y with
      | r j => simp only [r_mul_r, dihedralAutFun, r.injEq]; ring
      | sr j => simp only [r_mul_sr, dihedralAutFun, r_mul_sr, sr.injEq]; ring
    | sr i => cases y with
      | r j => simp only [sr_mul_r, dihedralAutFun, sr_mul_r, sr.injEq]; ring
      | sr j => simp only [sr_mul_sr, dihedralAutFun, sr_mul_sr, r.injEq]; ring

@[simp] theorem dihedralAut_r (a : ZMod n) (u : (ZMod n)ˣ) (i : ZMod n) :
    dihedralAut a u (r i) = r ((u : ZMod n) * i) := rfl

@[simp] theorem dihedralAut_sr (a : ZMod n) (u : (ZMod n)ˣ) (i : ZMod n) :
    dihedralAut a u (sr i) = sr ((u : ZMod n) * i + a) := rfl

/-- 座標の一致は写像の一致から従う (単射性)。 -/
theorem dihedralAut_eq_iff {a b : ZMod n} {u v : (ZMod n)ˣ} :
    dihedralAut a u = dihedralAut b v ↔ a = b ∧ u = v := by
  constructor
  · intro h
    have h1 := congrArg (fun α : MulAut (DihedralGroup n) => α (sr 0)) h
    have h2 := congrArg (fun α : MulAut (DihedralGroup n) => α (r 1)) h
    simp only [dihedralAut_sr, dihedralAut_r, mul_zero, zero_add, mul_one, sr.injEq,
      r.injEq] at h1 h2
    exact ⟨h1, Units.ext h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **合成則** = holomorph `ℤ/n ⋊ (ℤ/n)ˣ` の積。 -/
theorem dihedralAut_mul (a b : ZMod n) (u v : (ZMod n)ˣ) :
    dihedralAut a u * dihedralAut b v = dihedralAut (a + (u : ZMod n) * b) (u * v) := by
  ext x
  cases x with
  | r i => simp [MulAut.mul_apply]; ring
  | sr i => simp [MulAut.mul_apply]; ring

@[simp] theorem dihedralAut_zero_one : dihedralAut (0 : ZMod n) 1 = 1 := by
  ext x; cases x <;> simp

theorem dihedralAut_inv (a : ZMod n) (u : (ZMod n)ˣ) :
    (dihedralAut a u)⁻¹ = dihedralAut (-((↑u⁻¹ : ZMod n) * a)) u⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, dihedralAut_mul]
  simp

end /- 座標 `(a, u)` による記述 -/

section /- 全射性 (`n` 奇数) -/

/-- `n` 奇数のとき自己同型 `α` が回転部分に誘導する加法自己準同型 `ℤ/n →+ ℤ/n`。 -/
def rotAddHom (hodd : Odd n) (α : MulAut (DihedralGroup n)) : ZMod n →+ ZMod n where
  toFun i := rCoord (α (r i))
  map_zero' := by change rCoord (α (r 0)) = 0; rw [r_zero, map_one]; simp
  map_add' i j := by
    obtain ⟨p, hp⟩ := exists_r_of_mulAut_r hodd α i
    obtain ⟨q, hq⟩ := exists_r_of_mulAut_r hodd α j
    have : α (r (i + j)) = r (p + q) := by
      rw [← r_mul_r, map_mul, hp, hq, r_mul_r]
    simp [this, hp, hq]

theorem rotAddHom_apply (hodd : Odd n) (α : MulAut (DihedralGroup n)) (i : ZMod n) :
    α (r i) = r (rotAddHom hodd α i) := by
  obtain ⟨j, hj⟩ := exists_r_of_mulAut_r hodd α i
  rw [hj]
  simp [rotAddHom, hj]

/-- `ℤ/n` の加法準同型は `1` の像の掛け算 (mathlib `ZMod.AddAutEquivUnits` と同じ筋)。 -/
theorem addHom_zmod_apply (f : ZMod n →+ ZMod n) (x : ZMod n) : f x = f 1 * x := by
  rw [mul_comm, ← x.intCast_zmod_cast, ← zsmul_eq_mul, ← map_zsmul, zsmul_one]

/-- 全射な `ℤ/n` の加法自己準同型は**単元倍**。 -/
theorem exists_unit_of_surjective_addHom {f : ZMod n →+ ZMod n}
    (hf : Function.Surjective f) : ∃ u : (ZMod n)ˣ, ∀ x, f x = (u : ZMod n) * x := by
  obtain ⟨k, hk⟩ := hf 1
  have hunit : f 1 * k = 1 := by rw [← addHom_zmod_apply f k]; exact hk
  exact ⟨Units.mkOfMulEqOne _ k hunit, fun x => addHom_zmod_apply f x⟩

/-- 回転部分に誘導される作用は単元倍 (`n` 奇数)。 -/
theorem exists_unit_mulAut_r (hodd : Odd n) (α : MulAut (DihedralGroup n)) :
    ∃ u : (ZMod n)ˣ, ∀ i : ZMod n, α (r i) = r ((u : ZMod n) * i) := by
  -- `α⁻¹` も回転を回転へ写すので誘導された加法準同型は全射, よって `1` の像は単元
  have hsurj : Function.Surjective (rotAddHom hodd α) := by
    intro j
    obtain ⟨k, hk⟩ := exists_r_of_mulAut_r hodd α⁻¹ j
    refine ⟨k, ?_⟩
    have h1 : α (r k) = r j := by rw [← hk]; simp
    rw [rotAddHom_apply hodd α k] at h1
    simpa using h1
  obtain ⟨u, hu⟩ := exists_unit_of_surjective_addHom hsurj
  exact ⟨u, fun i => by rw [rotAddHom_apply hodd α i, hu i]⟩

/-- **全射性**: `n` 奇数なら `D_{2n}` の任意の自己同型は `dihedralAut a u` の形。 -/
theorem exists_dihedralAut (hodd : Odd n) (α : MulAut (DihedralGroup n)) :
    ∃ (a : ZMod n) (u : (ZMod n)ˣ), α = dihedralAut a u := by
  obtain ⟨u, hu⟩ := exists_unit_mulAut_r hodd α
  obtain ⟨a, ha⟩ := exists_sr_of_mulAut_sr hodd α 0
  refine ⟨a, u, ?_⟩
  ext x
  cases x with
  | r i => rw [hu i, dihedralAut_r]
  | sr i =>
    have hsplit : (sr i : DihedralGroup n) = r (-i) * sr 0 := by simp
    have hlhs : α (sr i) = sr ((u : ZMod n) * i + a) := by
      rw [hsplit, map_mul, ha, hu (-i), r_mul_sr]
      congr 1
      ring
    rw [hlhs, dihedralAut_sr]

end /- 全射性 (`n` 奇数) -/

section /- 平行移動部分群 = 交換子部分群 -/

/-- `n` 奇数なら `2` は `ℤ/n` で可逆 (`n = 2k+1` なので `2 (k+1) = n + 1 ≡ 1`)。 -/
theorem exists_two_mul_eq_one (hodd : Odd n) : ∃ h : ZMod n, 2 * h = 1 := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨((k + 1 : ℕ) : ZMod n), ?_⟩
  have hnat : 2 * (k + 1) = n + 1 := by omega
  calc (2 : ZMod n) * ((k + 1 : ℕ) : ZMod n)
      = ((2 * (k + 1) : ℕ) : ZMod n) := by push_cast; ring
    _ = ((n + 1 : ℕ) : ZMod n) := by rw [hnat]
    _ = 1 := by push_cast; simp

/-- **平行移動部分群** `N = {φ_{a,1}}` — holomorph 表示での `ℤ/n` 部分。

`n` 奇数のとき `Aut(D_{2n})` の**交換子部分群**に一致し (`commutator_eq_transSubgroup`),
したがって characteristic。これが completeness 証明の起点になる。 -/
def transSubgroup (n : ℕ) : Subgroup (MulAut (DihedralGroup n)) where
  carrier := Set.range fun a : ZMod n => dihedralAut a 1
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [dihedralAut_mul]; simp⟩
  one_mem' := ⟨0, dihedralAut_zero_one⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by rw [dihedralAut_inv]; simp⟩

theorem mem_transSubgroup_iff {α : MulAut (DihedralGroup n)} :
    α ∈ transSubgroup n ↔ ∃ a : ZMod n, α = dihedralAut a 1 :=
  ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

theorem dihedralAut_one_mem_transSubgroup (a : ZMod n) :
    dihedralAut a 1 ∈ transSubgroup n := ⟨a, rfl⟩

/-- `(a, u)` は `(a, 1) * (0, u)` に分解する。 -/
theorem dihedralAut_decomp (a : ZMod n) (u : (ZMod n)ˣ) :
    dihedralAut a 1 * dihedralAut 0 u = dihedralAut a u := by
  rw [dihedralAut_mul]; simp

/-- 平行移動の共役は unit 成分による掛け算 (`(A,B)(a,1)(A,B)⁻¹ = (B a, 1)`)。 -/
theorem conj_dihedralAut_one (A a : ZMod n) (B : (ZMod n)ˣ) :
    dihedralAut A B * dihedralAut a 1 * (dihedralAut A B)⁻¹
      = dihedralAut ((B : ZMod n) * a) 1 := by
  have hBB : (B : ZMod n) * ((B⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by
    rw [← Units.val_mul]; simp
  rw [dihedralAut_mul, dihedralAut_inv, dihedralAut_mul]
  congr 1
  · simp only [mul_one]
    rw [mul_neg, ← mul_assoc, hBB, one_mul]
    ring
  · simp

/-- `(c,1)` による共役: `(a,u) ↦ (a + (1-u) c, u)`。 -/
theorem conj_dihedralAut (c a : ZMod n) (u : (ZMod n)ˣ) :
    MulAut.conj (dihedralAut c 1) (dihedralAut a u)
      = dihedralAut (a + (1 - (u : ZMod n)) * c) u := by
  rw [MulAut.conj_apply, dihedralAut_inv, dihedralAut_mul, dihedralAut_mul]
  congr 1
  · simp; ring
  · simp

/-- `⁅(0,-1), (b,1)⁆ = (-2b, 1)` — 平行移動部分群を交換子で作り出す計算。 -/
theorem commutatorElement_negOne_trans (b : ZMod n) :
    ⁅dihedralAut (0 : ZMod n) (-1), dihedralAut b 1⁆ = dihedralAut (-(2 * b)) 1 := by
  rw [commutatorElement_def, dihedralAut_inv, dihedralAut_inv, dihedralAut_mul,
    dihedralAut_mul, dihedralAut_mul]
  congr 1
  · simp; ring
  · simp

/-- **交換子部分群 = 平行移動部分群** (`n` 奇数) ⭐。

`⊆` は `(ℤ/n)ˣ` が可換なので unit 成分が消えること, `⊇` は
`⁅(0,-1), (b,1)⁆ = (-2b, 1)` と `2` の可逆性による。これで `N` は **characteristic**
(交換子部分群だから) となり, 9B.4 の completeness 証明が回りだす。 -/
theorem commutator_eq_transSubgroup (hodd : Odd n) :
    ⁅(⊤ : Subgroup (MulAut (DihedralGroup n))), ⊤⁆ = transSubgroup n := by
  refine le_antisymm (Subgroup.commutator_le.mpr ?_) ?_
  · rintro α - β -
    obtain ⟨a, u, rfl⟩ := exists_dihedralAut hodd α
    obtain ⟨b, v, rfl⟩ := exists_dihedralAut hodd β
    rw [commutatorElement_def, dihedralAut_inv, dihedralAut_inv, dihedralAut_mul,
      dihedralAut_mul, dihedralAut_mul]
    have hone : u * v * u⁻¹ * v⁻¹ = 1 := by rw [mul_comm u v]; group
    rw [hone]
    exact dihedralAut_one_mem_transSubgroup _
  · rintro _ ⟨c, rfl⟩
    obtain ⟨h, hh⟩ := exists_two_mul_eq_one (n := n) hodd
    have hc : -(2 * -(h * c)) = c := by
      rw [mul_neg, neg_neg, ← mul_assoc, hh, one_mul]
    have key : ⁅dihedralAut (0 : ZMod n) (-1), dihedralAut (-(h * c)) 1⁆ = dihedralAut c 1 := by
      rw [commutatorElement_negOne_trans, hc]
    have hmem : dihedralAut c 1 ∈ ⁅(⊤ : Subgroup (MulAut (DihedralGroup n))), ⊤⁆ :=
      key ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact hmem

end /- 平行移動部分群 = 交換子部分群 -/

section /- `Aut(D_{2n})` は complete (`n` 奇数) -/

/-- `Aut(D_{2n})` の中心は自明 (`n` 奇数)。

`(a,u)` が `(b,1)` 全部と可換 ⟹ `u b = b` ⟹ `u = 1`; さらに `(0,v)` 全部と可換 ⟹
`a = v a`, `v = -1` と `2` の可逆性で `a = 0`。 -/
theorem center_mulAut_dihedral_eq_bot (hodd : Odd n) :
    Subgroup.center (MulAut (DihedralGroup n)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_center_iff] at hα
  obtain ⟨a, u, rfl⟩ := exists_dihedralAut hodd α
  have hu : u = 1 := by
    have h := hα (dihedralAut 1 1)
    rw [dihedralAut_mul, dihedralAut_mul] at h
    have h1 := (dihedralAut_eq_iff.mp h).1
    simp only [Units.val_one, one_mul, mul_one] at h1
    have hval : (u : ZMod n) = 1 := by linear_combination -h1
    exact Units.ext (by simpa using hval)
  subst hu
  have ha : a = 0 := by
    have h := hα (dihedralAut 0 (-1))
    rw [dihedralAut_mul, dihedralAut_mul] at h
    have h1 := (dihedralAut_eq_iff.mp h).1
    simp only [Units.val_neg, Units.val_one, zero_add, mul_zero, add_zero, neg_mul,
      one_mul] at h1
    obtain ⟨h2, hh2⟩ := exists_two_mul_eq_one (n := n) hodd
    have h2a : 2 * a = 0 := by linear_combination -h1
    calc a = (2 * h2) * a := by rw [hh2, one_mul]
      _ = h2 * (2 * a) := by ring
      _ = 0 := by rw [h2a, mul_zero]
  subst ha
  exact Subgroup.mem_bot.mpr dihedralAut_zero_one

/-- 平行移動部分群は `Aut(D_{2n})` の交換子部分群なので **characteristic**: 任意の
`Φ ∈ Aut(Aut(D_{2n}))` で保たれる。 -/
theorem map_mem_transSubgroup (hodd : Odd n) (Φ : MulAut (MulAut (DihedralGroup n)))
    {α : MulAut (DihedralGroup n)} (hα : α ∈ transSubgroup n) : Φ α ∈ transSubgroup n := by
  have hchar : Subgroup.Characteristic
      ⁅(⊤ : Subgroup (MulAut (DihedralGroup n))), (⊤ : Subgroup (MulAut (DihedralGroup n)))⁆ :=
    inferInstance
  rw [← commutator_eq_transSubgroup hodd] at hα ⊢
  exact Subgroup.characteristic_iff_map_le.mp hchar Φ ⟨α, hα, rfl⟩

/-- `Φ ∈ Aut(Aut(D_{2n}))` が平行移動部分群 `≅ ℤ/n` に誘導する加法自己準同型。 -/
def transAddHom (hodd : Odd n) (Φ : MulAut (MulAut (DihedralGroup n))) : ZMod n →+ ZMod n where
  toFun a := srCoord (Φ (dihedralAut a 1) (sr 0))
  map_zero' := by
    change srCoord (Φ (dihedralAut 0 1) (sr 0)) = 0
    rw [dihedralAut_zero_one, map_one]
    simp [srCoord]
  map_add' a b := by
    obtain ⟨ca, hca⟩ := mem_transSubgroup_iff.mp
      (map_mem_transSubgroup hodd Φ (dihedralAut_one_mem_transSubgroup a))
    obtain ⟨cb, hcb⟩ := mem_transSubgroup_iff.mp
      (map_mem_transSubgroup hodd Φ (dihedralAut_one_mem_transSubgroup b))
    have hsum : Φ (dihedralAut (a + b) 1) = dihedralAut (ca + cb) 1 := by
      have hprod : (dihedralAut (a + b) 1 : MulAut (DihedralGroup n))
          = dihedralAut a 1 * dihedralAut b 1 := by rw [dihedralAut_mul]; simp
      rw [hprod, map_mul, hca, hcb, dihedralAut_mul]
      simp
    have e1 : srCoord (Φ (dihedralAut a 1) (sr 0)) = ca := by rw [hca]; simp
    have e2 : srCoord (Φ (dihedralAut b 1) (sr 0)) = cb := by rw [hcb]; simp
    have e3 : srCoord (Φ (dihedralAut (a + b) 1) (sr 0)) = ca + cb := by rw [hsum]; simp
    simp only [e1, e2, e3]

theorem transAddHom_coe (hodd : Odd n) (Φ : MulAut (MulAut (DihedralGroup n))) (a : ZMod n) :
    transAddHom hodd Φ a = srCoord (Φ (dihedralAut a 1) (sr 0)) := rfl

theorem transAddHom_apply (hodd : Odd n) (Φ : MulAut (MulAut (DihedralGroup n))) (a : ZMod n) :
    Φ (dihedralAut a 1) = dihedralAut (transAddHom hodd Φ a) 1 := by
  obtain ⟨c, hc⟩ := mem_transSubgroup_iff.mp
    (map_mem_transSubgroup hodd Φ (dihedralAut_one_mem_transSubgroup a))
  rw [hc]
  refine dihedralAut_eq_iff.mpr ⟨?_, rfl⟩
  rw [transAddHom_coe, hc]
  simp

/-- `Φ` の平行移動部分群への制限は**単元倍**。 -/
theorem exists_unit_map_trans (hodd : Odd n) (Φ : MulAut (MulAut (DihedralGroup n))) :
    ∃ w : (ZMod n)ˣ, ∀ a : ZMod n, Φ (dihedralAut a 1) = dihedralAut ((w : ZMod n) * a) 1 := by
  have hsurj : Function.Surjective (transAddHom hodd Φ) := by
    intro c
    obtain ⟨b, hb⟩ := mem_transSubgroup_iff.mp
      (map_mem_transSubgroup hodd Φ⁻¹ (dihedralAut_one_mem_transSubgroup c))
    refine ⟨b, ?_⟩
    have hΦb : Φ (dihedralAut b 1) = dihedralAut c 1 := by rw [← hb]; simp
    rw [transAddHom_apply hodd Φ b] at hΦb
    exact (dihedralAut_eq_iff.mp hΦb).1
  obtain ⟨w, hw⟩ := exists_unit_of_surjective_addHom hsurj
  exact ⟨w, fun a => by rw [transAddHom_apply hodd Φ a, hw a]⟩

/-- **1-cocycle の消滅** ⭐: 平行移動部分群を各点固定する `Ψ ∈ Aut(Aut(D_{2n}))` は
`(c,1)` による共役。

`Ψ (0,u) = (A u, u)` の `A` は 1-cocycle `A(uv) = A u + u · A v`。`u = -1` を
`(ℤ/n)ˣ` の可換性で両側から使うと `2 A u = (1 - u) A(-1)`, `n` 奇数なので `2` を割って
`A u = (1 - u) c` (`c = A(-1)/2`) — これはちょうど `(c,1)` 共役の形。 -/
theorem eq_conj_of_fixes_trans (hodd : Odd n) (Ψ : MulAut (MulAut (DihedralGroup n)))
    (hΨ : ∀ a : ZMod n, Ψ (dihedralAut a 1) = dihedralAut a 1) :
    ∃ c : ZMod n, Ψ = MulAut.conj (dihedralAut c 1) := by
  -- (1) `Ψ` は `(0,u)` の unit 成分を保つ
  have hunit : ∀ u : (ZMod n)ˣ, ∃ A : ZMod n, Ψ (dihedralAut 0 u) = dihedralAut A u := by
    intro u
    obtain ⟨A, B, hAB⟩ := exists_dihedralAut hodd (Ψ (dihedralAut 0 u))
    refine ⟨A, ?_⟩
    rw [hAB]
    have hB : B = u := by
      have h1 : ∀ a : ZMod n,
          dihedralAut ((B : ZMod n) * a) 1 = dihedralAut ((u : ZMod n) * a) 1 := by
        intro a
        have hcj := congrArg Ψ (conj_dihedralAut_one (0 : ZMod n) a u)
        rw [map_mul, map_mul, map_inv, hΨ a, hAB, hΨ ((u : ZMod n) * a),
          conj_dihedralAut_one] at hcj
        exact hcj
      have h2 := h1 1
      rw [mul_one, mul_one] at h2
      exact Units.ext (dihedralAut_eq_iff.mp h2).1
    rw [hB]
  choose A hA using hunit
  -- (2) `A` は 1-cocycle
  have hcocycle : ∀ u v : (ZMod n)ˣ, A (u * v) = A u + (u : ZMod n) * A v := by
    intro u v
    have hprod : (dihedralAut (0 : ZMod n) u * dihedralAut (0 : ZMod n) v
        : MulAut (DihedralGroup n)) = dihedralAut 0 (u * v) := by rw [dihedralAut_mul]; simp
    have h := congrArg Ψ hprod
    rw [map_mul, hA u, hA v, hA (u * v), dihedralAut_mul] at h
    exact (dihedralAut_eq_iff.mp h).1.symm
  -- (3) `u = -1` を使って cocycle を coboundary にする
  obtain ⟨h2, hh2⟩ := exists_two_mul_eq_one (n := n) hodd
  refine ⟨h2 * A (-1), ?_⟩
  have hAu : ∀ u : (ZMod n)ˣ, A u = (1 - (u : ZMod n)) * (h2 * A (-1)) := by
    intro u
    have e1 := hcocycle u (-1)
    have e2 := hcocycle (-1) u
    rw [mul_comm u (-1 : (ZMod n)ˣ)] at e1
    have hneg : ((-1 : (ZMod n)ˣ) : ZMod n) = -1 := by simp
    rw [hneg] at e2
    have key : 2 * A u = (1 - (u : ZMod n)) * A (-1) := by
      rw [e1] at e2; linear_combination e2
    calc A u = (2 * h2) * A u := by rw [hh2, one_mul]
      _ = h2 * (2 * A u) := by ring
      _ = h2 * ((1 - (u : ZMod n)) * A (-1)) := by rw [key]
      _ = (1 - (u : ZMod n)) * (h2 * A (-1)) := by ring
  -- (4) 両者は生成元 `(a,1)`, `(0,u)` で一致
  refine MulEquiv.ext fun α => ?_
  obtain ⟨a, u, rfl⟩ := exists_dihedralAut hodd α
  have hlhs : Ψ (dihedralAut a u)
      = dihedralAut (a + (1 - (u : ZMod n)) * (h2 * A (-1))) u := by
    rw [← dihedralAut_decomp a u, map_mul, hΨ a, hA u, hAu u, dihedralAut_mul]
    refine dihedralAut_eq_iff.mpr ⟨?_, ?_⟩ <;> simp
  rw [hlhs, conj_dihedralAut]

/-- **`Aut(D_{2n})` の自己同型はすべて内部** (`n` 奇数) ⭐。 -/
theorem mulAut_conj_surjective (hodd : Odd n) :
    Function.Surjective (MulAut.conj (G := MulAut (DihedralGroup n))) := by
  intro Φ
  obtain ⟨w, hw⟩ := exists_unit_map_trans hodd Φ
  -- `conj ((0,w)⁻¹)` を掛けると平行移動部分群を各点固定する `Ψ` になる
  have hΨ : ∀ a : ZMod n,
      (MulAut.conj ((dihedralAut (0 : ZMod n) w)⁻¹) * Φ) (dihedralAut a 1)
        = dihedralAut a 1 := by
    intro a
    change MulAut.conj ((dihedralAut (0 : ZMod n) w)⁻¹) (Φ (dihedralAut a 1)) = _
    rw [hw a, MulAut.conj_apply, dihedralAut_inv, conj_dihedralAut_one]
    refine dihedralAut_eq_iff.mpr ⟨?_, rfl⟩
    rw [← mul_assoc, ← Units.val_mul]
    simp
  obtain ⟨c, hc⟩ := eq_conj_of_fixes_trans hodd _ hΨ
  refine ⟨dihedralAut (0 : ZMod n) w * dihedralAut c 1, ?_⟩
  rw [map_mul, ← hc, ← mul_assoc, ← map_mul]
  simp

end /- `Aut(D_{2n})` は complete (`n` 奇数) -/

end OddOrder.GroupTheory
