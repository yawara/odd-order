/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.OrderOfElement

/-!
# Isaacs Chapter 3 — Problems §3A (Split Extensions)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3 "Split Extensions" の章末演習 §3A
(pp. 74-75)。半直積 (`SemidirectProduct`) を扱う。

方針は Ch.1/Ch.2 の `Problems.lean` と同じ (ラッパーは書かず実証明; 教科書番号は docstring)。
-/

namespace OddOrder.Isaacs.Ch03

section /- Problems 3A: Split extensions (pp. 74-75) -/

/-! ### Problem 3A.1(a) — semidihedral の特徴的自己同型

位数 `n` (ただし `8 ∣ n`) の巡回群 `C`。`z` を一意の対合とすると、任意の生成元 `c` に対し
`c^a = c⁻¹ z` を満たす自己同型 `a` が一意に存在し、位数 2。`C = ZMod n` (加法的) で形式化する。
生成元 = 単元 `c`、`z = n/2`、条件は加法的に `a(c) = -c + z`。この `a` は乗数 `w = z - 1` による
乗法 `x ↦ w·x` で、`4 ∣ n` から `w² = 1` ゆえ自身が逆写像 (対合自己同型)。 -/

/-- `w = n/2 - 1` は `w² = 1` (`z = n/2` が `z² = 0`, `2z = 0` を満たすため; `4 ∣ n`)。 -/
theorem semidihedral_sub_one_sq (n : ℕ) (hn : 4 ∣ n) :
    (((n / 2 : ℕ) : ZMod n) - 1) * (((n / 2 : ℕ) : ZMod n) - 1) = 1 := by
  have hz2 : ((n / 2 : ℕ) : ZMod n) * ((n / 2 : ℕ) : ZMod n) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    obtain ⟨k, rfl⟩ := hn
    rw [show 4 * k / 2 = 2 * k by omega]
    exact ⟨k, by ring⟩
  have hz1 : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    obtain ⟨k, rfl⟩ := hn
    rw [show 4 * k / 2 = 2 * k by omega]
    exact ⟨1, by ring⟩
  have expand : (((n / 2 : ℕ) : ZMod n) - 1) * (((n / 2 : ℕ) : ZMod n) - 1)
      = ((n / 2 : ℕ) : ZMod n) * ((n / 2 : ℕ) : ZMod n)
        - (((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n)) + 1 := by ring
  rw [expand, hz2, hz1]; ring

/-- **Isaacs Problem 3A.1(a)** の特徴的自己同型 `a : x ↦ (n/2 - 1)·x` (乗数は自身が逆)。 -/
def semidihedralAut (n : ℕ) (hn : 8 ∣ n) : AddAut (ZMod n) where
  toFun x := (((n / 2 : ℕ) : ZMod n) - 1) * x
  invFun x := (((n / 2 : ℕ) : ZMod n) - 1) * x
  left_inv x := by
    have h := semidihedral_sub_one_sq n (dvd_trans (by norm_num) hn)
    simp only [← mul_assoc, h, one_mul]
  right_inv x := by
    have h := semidihedral_sub_one_sq n (dvd_trans (by norm_num) hn)
    simp only [← mul_assoc, h, one_mul]
  map_add' x y := mul_add _ x y

@[simp] theorem semidihedralAut_apply (n : ℕ) (hn : 8 ∣ n) (x : ZMod n) :
    semidihedralAut n hn x = (((n / 2 : ℕ) : ZMod n) - 1) * x := rfl

/-- `z·c = z` for a unit (generator) `c`: `c` is odd (as `n` is even) and `z = n/2` is 2-torsion. -/
theorem semidihedral_invol_mul_unit (n : ℕ) [NeZero n] (hn : 2 ∣ n) {c : ZMod n}
    (hc : IsUnit c) : ((n / 2 : ℕ) : ZMod n) * c = ((n / 2 : ℕ) : ZMod n) := by
  have hz1 : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    obtain ⟨k, rfl⟩ := hn
    rw [show 2 * k / 2 = k by omega]
    exact ⟨1, by ring⟩
  have hcop : Nat.Coprime c.val n := by
    have := ZMod.val_coe_unit_coprime hc.unit
    rwa [hc.unit_spec] at this
  have hodd : Odd c.val :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right hn hcop)
  obtain ⟨m, hm⟩ := hodd
  have hcval : c = ((c.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val c).symm
  have h2z : (2 : ZMod n) * ((n / 2 : ℕ) : ZMod n) = 0 := by rw [two_mul]; exact hz1
  rw [hcval, hm]
  push_cast
  have : ((n / 2 : ℕ) : ZMod n) * (2 * (m : ZMod n) + 1)
      = (2 * ((n / 2 : ℕ) : ZMod n)) * (m : ZMod n) + ((n / 2 : ℕ) : ZMod n) := by ring
  rw [this, h2z, zero_mul, zero_add]

/-- **Isaacs Problem 3A.1(a)** (存在 + 特徴づけ). 任意の生成元 (単元) `c` に対し `a(c) = c⁻¹z`
(加法的に `-c + z`, `z = n/2`)。 -/
theorem semidihedralAut_apply_isUnit (n : ℕ) [NeZero n] (hn : 8 ∣ n) {c : ZMod n}
    (hc : IsUnit c) : semidihedralAut n hn c = -c + ((n / 2 : ℕ) : ZMod n) := by
  have hzc := semidihedral_invol_mul_unit n (dvd_trans (by norm_num) hn) hc
  rw [semidihedralAut_apply, sub_one_mul, hzc]; ring

/-- **Isaacs Problem 3A.1(a)** (一意性). `a(c) = -c + z` を全生成元で満たす自己同型は `a` に限る
(自己同型は生成元 `1` での値で定まり、両者とも `1 ↦ z - 1`)。 -/
theorem semidihedralAut_unique (n : ℕ) [NeZero n] (hn : 8 ∣ n) (b : AddAut (ZMod n))
    (hb : ∀ c : ZMod n, IsUnit c → b c = -c + ((n / 2 : ℕ) : ZMod n)) :
    b = semidihedralAut n hn := by
  refine AddEquiv.ext fun x => ?_
  have hb1 : b 1 = semidihedralAut n hn 1 := by
    rw [hb 1 isUnit_one, semidihedralAut_apply, mul_one]; ring
  have hx : x = x.val • (1 : ZMod n) := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rw [hx, map_nsmul, map_nsmul, hb1]

/-- **Isaacs Problem 3A.1(a)** (位数 2). `a` は対合自己同型 (`a + a = 0`, 合成が恒等) で `a ≠ 0`。 -/
theorem semidihedralAut_add_self (n : ℕ) (hn : 8 ∣ n) :
    semidihedralAut n hn + semidihedralAut n hn = 0 := by
  have h := semidihedral_sub_one_sq n (dvd_trans (by norm_num) hn)
  refine AddEquiv.ext fun x => ?_
  rw [AddAut.add_apply, AddAut.zero_apply, semidihedralAut_apply, semidihedralAut_apply,
    ← mul_assoc, h, one_mul]

theorem semidihedralAut_ne_zero (n : ℕ) [NeZero n] (hn : 8 ∣ n) : semidihedralAut n hn ≠ 0 := by
  intro hcontra
  have hn0 : n ≠ 0 := NeZero.ne n
  have h1 : ((n / 2 : ℕ) : ZMod n) - 1 = 1 := by
    have hthis := DFunLike.congr_fun hcontra (1 : ZMod n)
    simpa only [semidihedralAut_apply, mul_one, AddAut.zero_apply] using hthis
  have hle : 2 ≤ n / 2 := by omega
  have h2 : ((n / 2 : ℕ) : ZMod n) = ((2 : ℕ) : ZMod n) := by
    rw [sub_eq_iff_eq_add] at h1; rw [h1]; push_cast; ring
  rw [← sub_eq_zero, ← Nat.cast_sub hle, ZMod.natCast_eq_zero_iff] at h2
  have hdvd := Nat.le_of_dvd (by omega) h2
  omega

/-- **Isaacs Problem 3A.1(a)** (位数 2, まとめ). -/
theorem semidihedralAut_addOrderOf (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    addOrderOf (semidihedralAut n hn) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine addOrderOf_eq_prime ?_ (semidihedralAut_ne_zero n hn)
  rw [two_nsmul]; exact semidihedralAut_add_self n hn

/-- **Isaacs Problem 3A.5**. 有限群 `G` について、`G` の自身への共役作用で作った半直積 `G ⋊ G` は
直積 `G × G` に同型。同型 `(n, g) ↦ (n·g, g)` は準同型: 半直積の積 `(a.left · a.right·b.left·a.right⁻¹,
a.right·b.right)` を写すと `(a.left·a.right·b.left·b.right, a.right·b.right)` = 直積の積の像。 -/
def semidirectConjEquivProd (G : Type*) [Group G] :
    SemidirectProduct G G MulAut.conj ≃* G × G where
  toFun x := (x.left * x.right, x.right)
  invFun p := ⟨p.1 * p.2⁻¹, p.2⟩
  left_inv x := SemidirectProduct.ext (by simp) rfl
  right_inv p := by simp
  map_mul' a b := by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, MulAut.conj_apply,
      Prod.mk_mul_mk, Prod.mk.injEq]
    refine ⟨?_, ?_⟩ <;> group

end

end OddOrder.Isaacs.Ch03
