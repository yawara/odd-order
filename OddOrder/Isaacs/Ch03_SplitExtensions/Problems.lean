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
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic

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

/-! ### Problem 3A.1(b) — semidihedral 群 `S = C ⋊ ⟨a⟩` 内の元の位数分布

`a` を `Multiplicative (ZMod n)` の乗法的自己同型 `σ` (位数 2) とみて、`H = ⟨σ⟩ ≤ MulAut` による
半直積 `S = Multiplicative (ZMod n) ⋊ H`。`S - C` (= `H` 成分が非自明な元) の各元 `(x, σ)` は
`(x, σ)² = (z·x, 1)` (`z = n/2`)、`(x, σ)⁴ = 1`。`z·x = 0 ⟺ x` 偶ゆえ、`x` 偶なら位数 2、
`x` 奇なら位数 4。両者は `ZMod n` の偶元・奇元でちょうど半々。 -/

/-- `semidihedralAut` に対応する `Multiplicative (ZMod n)` の乗法的自己同型 `σ` (位数 2)。 -/
noncomputable def semidihedralMulAut (n : ℕ) (hn : 8 ∣ n) :
    MulAut (Multiplicative (ZMod n)) :=
  (MulAutMultiplicative (ZMod n)).symm (Multiplicative.ofAdd (semidihedralAut n hn))

@[simp] theorem semidihedralMulAut_apply (n : ℕ) (hn : 8 ∣ n) (x : Multiplicative (ZMod n)) :
    semidihedralMulAut n hn x
      = Multiplicative.ofAdd ((((n / 2 : ℕ) : ZMod n) - 1) * Multiplicative.toAdd x) := rfl

/-- `σ² = 1` (対合自己同型). -/
theorem semidihedralMulAut_sq (n : ℕ) (hn : 8 ∣ n) :
    semidihedralMulAut n hn * semidihedralMulAut n hn = 1 := by
  have hw := semidihedral_sub_one_sq n (dvd_trans (by norm_num) hn)
  ext x
  set w : ZMod n := ((n / 2 : ℕ) : ZMod n) - 1 with hwdef
  have harith : w * (w * Multiplicative.toAdd x) = Multiplicative.toAdd x := by
    rw [← mul_assoc, hw, one_mul]
  simp only [MulAut.mul_apply, semidihedralMulAut_apply, MulAut.one_apply, toAdd_ofAdd, ← hwdef,
    harith, ofAdd_toAdd]

/-- semidihedral 群 `SD(n) = C_n ⋊ ⟨a⟩` (`C_n = Multiplicative (ZMod n)`, `⟨a⟩ = ⟨σ⟩ ≤ MulAut`). -/
abbrev SemidihedralGroup (n : ℕ) (hn : 8 ∣ n) :=
  SemidirectProduct (Multiplicative (ZMod n)) (Subgroup.zpowers (semidihedralMulAut n hn))
    (Subgroup.zpowers (semidihedralMulAut n hn)).subtype

/-- `S - C` の元 `(x, σ)` (`σ` を非自明な `H` 成分とする reflection)。 -/
noncomputable def semidihedralReflection (n : ℕ) (hn : 8 ∣ n) (x : Multiplicative (ZMod n)) :
    SemidihedralGroup n hn :=
  ⟨x, ⟨semidihedralMulAut n hn, Subgroup.mem_zpowers _⟩⟩

/-- reflection の 2 乗は base の元 `z·x` (`z = n/2`): `(x,σ)² = (x·σ(x), σ²) = (z·x, 1)`. -/
theorem semidihedralReflection_sq (n : ℕ) (hn : 8 ∣ n) (x : Multiplicative (ZMod n)) :
    (semidihedralReflection n hn x) ^ 2
      = SemidirectProduct.inl
          (Multiplicative.ofAdd (((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x)) := by
  rw [sq]
  refine SemidirectProduct.ext ?_ ?_
  · simp only [semidihedralReflection, SemidirectProduct.mul_left, SemidirectProduct.left_inl]
    change x * semidihedralMulAut n hn x
        = Multiplicative.ofAdd (((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x)
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, semidihedralMulAut_apply, toAdd_ofAdd, toAdd_ofAdd]
    ring
  · simp only [semidihedralReflection, SemidirectProduct.mul_right, SemidirectProduct.right_inl]
    refine Subtype.ext ?_
    change semidihedralMulAut n hn * semidihedralMulAut n hn = 1
    exact semidihedralMulAut_sq n hn

/-- `z ≠ 2` (`n ≥ 8` ゆえ `n/2 ≥ 4`): `w = z - 1 ≠ 1`。 -/
theorem semidihedral_sub_one_ne_one (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    ((n / 2 : ℕ) : ZMod n) - 1 ≠ 1 := by
  intro h1
  have hn0 : n ≠ 0 := NeZero.ne n
  have hle : 2 ≤ n / 2 := by omega
  have h2 : ((n / 2 : ℕ) : ZMod n) = ((2 : ℕ) : ZMod n) := by
    rw [sub_eq_iff_eq_add] at h1; rw [h1]; push_cast; ring
  rw [← sub_eq_zero, ← Nat.cast_sub hle, ZMod.natCast_eq_zero_iff] at h2
  have hdvd := Nat.le_of_dvd (by omega) h2
  omega

/-- `σ ≠ 1` (非自明な自己同型). -/
theorem semidihedralMulAut_ne_one (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    semidihedralMulAut n hn ≠ 1 := by
  intro h
  apply semidihedral_sub_one_ne_one n hn
  have h1 := DFunLike.congr_fun h (Multiplicative.ofAdd (1 : ZMod n))
  rw [semidihedralMulAut_apply, MulAut.one_apply, toAdd_ofAdd, mul_one] at h1
  exact Multiplicative.ofAdd.injective h1

/-- reflection `(x, σ)` は非自明 (`H` 成分 `σ ≠ 1`)。 -/
theorem semidihedralReflection_ne_one (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    (x : Multiplicative (ZMod n)) : semidihedralReflection n hn x ≠ 1 := by
  intro h
  apply semidihedralMulAut_ne_one n hn
  have hr : (semidihedralReflection n hn x).right = (1 : SemidihedralGroup n hn).right := by rw [h]
  rw [SemidirectProduct.one_right] at hr
  have hval := congrArg Subtype.val hr
  simpa [semidihedralReflection] using hval

/-- reflection の 4 乗は恒等: `(x,σ)⁴ = ((x,σ)²)² = (2z·x, 1) = (0, 1) = 1` (`2z = 0`)。 -/
theorem semidihedralReflection_pow_four (n : ℕ) (hn : 8 ∣ n) (x : Multiplicative (ZMod n)) :
    (semidihedralReflection n hn x) ^ 4 = 1 := by
  have hz1 : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    have h2n : (2 : ℕ) ∣ n := dvd_trans (by norm_num) hn
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    obtain ⟨k, rfl⟩ := h2n
    rw [show 2 * k / 2 = k by omega]
    exact ⟨1, by ring⟩
  calc (semidihedralReflection n hn x) ^ 4
      = ((semidihedralReflection n hn x) ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    _ = (SemidirectProduct.inl
          (Multiplicative.ofAdd (((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x))) ^ 2 := by
        rw [semidihedralReflection_sq]
    _ = SemidirectProduct.inl
          ((Multiplicative.ofAdd (((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x)) ^ 2) := by
        rw [← map_pow]
    _ = SemidirectProduct.inl 1 := by
        congr 1
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_ofAdd, toAdd_one, two_nsmul, ← add_mul, hz1, zero_mul]
    _ = 1 := map_one _

/-- reflection の 2 乗が恒等 ⟺ `z·x = 0` (⟺ `x` が偶). -/
theorem semidihedralReflection_sq_eq_one_iff (n : ℕ) (hn : 8 ∣ n) (x : Multiplicative (ZMod n)) :
    (semidihedralReflection n hn x) ^ 2 = 1
      ↔ ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x = 0 := by
  rw [semidihedralReflection_sq, map_eq_one_iff _ SemidirectProduct.inl_injective,
    ofAdd_eq_one]

/-- **Isaacs Problem 3A.1(b)** (位数 2 の判定). `x` が偶 (`z·x = 0`) ⟺ `(x,σ)` の位数 = 2。 -/
theorem semidihedralReflection_orderOf_eq_two_iff (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    (x : Multiplicative (ZMod n)) :
    orderOf (semidihedralReflection n hn x) = 2
      ↔ ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← semidihedralReflection_sq_eq_one_iff n hn x]
  constructor
  · intro h; rw [← h]; exact pow_orderOf_eq_one _
  · intro h; exact orderOf_eq_prime h (semidihedralReflection_ne_one n hn x)

/-- **Isaacs Problem 3A.1(b)** (位数 4 の判定). `x` が奇 (`z·x ≠ 0`) ⟺ `(x,σ)` の位数 = 4。 -/
theorem semidihedralReflection_orderOf_eq_four_iff (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    (x : Multiplicative (ZMod n)) :
    orderOf (semidihedralReflection n hn x) = 4
      ↔ ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ne_eq, ← semidihedralReflection_sq_eq_one_iff n hn x]
  constructor
  · intro h hsq
    have h2 := orderOf_eq_prime hsq (semidihedralReflection_ne_one n hn x)
    omega
  · intro h
    have hpp : orderOf (semidihedralReflection n hn x) = 2 ^ 2 :=
      orderOf_eq_prime_pow (n := 1) (by simpa using h)
        (by simpa using semidihedralReflection_pow_four n hn x)
    exact hpp.trans (by norm_num)

/-- **Isaacs Problem 3A.1(b)** (位数分布). `S - C` の各元 `(x, σ)` の位数は 2 か 4。 -/
theorem semidihedralReflection_orderOf_eq_two_or_four (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    (x : Multiplicative (ZMod n)) :
    orderOf (semidihedralReflection n hn x) = 2 ∨ orderOf (semidihedralReflection n hn x) = 4 := by
  by_cases h : ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x = 0
  · exact Or.inl ((semidihedralReflection_orderOf_eq_two_iff n hn x).mpr h)
  · exact Or.inr ((semidihedralReflection_orderOf_eq_four_iff n hn x).mpr h)

/-- `z = n/2 ≠ 0` (`0 < n/2 < n`). -/
theorem semidihedral_invol_ne_zero (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    ((n / 2 : ℕ) : ZMod n) ≠ 0 := by
  have hn0 : n ≠ 0 := NeZero.ne n
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- `z·a ∈ {0, z}` (`z = n/2` は 2-torsion): `a` の偶奇で `z·a` は `0` か `z`。 -/
theorem semidihedral_invol_mul_dichotomy (n : ℕ) [NeZero n] (hn : 2 ∣ n) (a : ZMod n) :
    ((n / 2 : ℕ) : ZMod n) * a = 0 ∨ ((n / 2 : ℕ) : ZMod n) * a = ((n / 2 : ℕ) : ZMod n) := by
  have hz1 : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    obtain ⟨k, rfl⟩ := hn
    rw [show 2 * k / 2 = k by omega]; exact ⟨1, by ring⟩
  have key : ∀ k : ℕ, ((n / 2 : ℕ) : ZMod n) * (k : ZMod n) = 0
      ∨ ((n / 2 : ℕ) : ZMod n) * (k : ZMod n) = ((n / 2 : ℕ) : ZMod n) := by
    intro k
    induction k with
    | zero => left; simp
    | succ j ih =>
      push_cast
      rcases ih with h | h
      · right; rw [mul_add, h, mul_one, zero_add]
      · left; rw [mul_add, h, mul_one, hz1]
  have hkey := key a.val
  rwa [ZMod.natCast_zmod_val] at hkey

/-- **Isaacs Problem 3A.1(b)** (半々). `S - C` の位数 2 の元と位数 4 の元は同数。`refl x` (`x ∈ C_n`)
で `S - C` を径数付けると、位数 2 ⟺ `z·x = 0` (偶)、位数 4 ⟺ `z·x ≠ 0` (奇)。`x ↦ x·ofAdd 1` の
parity flip がこの 2 集合を全単射に交換する。 -/
def semidihedralOrderFlip (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    {x : Multiplicative (ZMod n) // ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x = 0}
      ≃ {x : Multiplicative (ZMod n) // ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x ≠ 0} where
  toFun p := ⟨p.1 * Multiplicative.ofAdd 1, by
    rw [toAdd_mul, toAdd_ofAdd, mul_add, p.2, mul_one, zero_add]
    exact semidihedral_invol_ne_zero n hn⟩
  invFun q := ⟨q.1 * Multiplicative.ofAdd (-1), by
    rcases semidihedral_invol_mul_dichotomy n (dvd_trans (by norm_num) hn)
        (Multiplicative.toAdd q.1) with h | h
    · exact absurd h q.2
    · rw [toAdd_mul, toAdd_ofAdd, mul_add, h, mul_neg_one, add_neg_cancel]⟩
  left_inv p := by
    refine Subtype.ext ?_
    change (p.1 * Multiplicative.ofAdd 1) * Multiplicative.ofAdd (-1) = p.1
    rw [mul_assoc, ← ofAdd_add, add_neg_cancel, ofAdd_zero, mul_one]
  right_inv q := by
    refine Subtype.ext ?_
    change (q.1 * Multiplicative.ofAdd (-1)) * Multiplicative.ofAdd 1 = q.1
    rw [mul_assoc, ← ofAdd_add, neg_add_cancel, ofAdd_zero, mul_one]

/-! ### Problem 3A.1(c) — `S - C` の位数 2・位数 4 の元はそれぞれ単一共役類

`refl x` を `inl y` (= `(y, 1)`) で共役すると `refl (y·x·σ(y⁻¹))` になり、加法的には `toAdd x` が
`(2 - z)·toAdd y` だけシフトする (`z = n/2`)。`u = 1 + n/4` は `(2-z)·u = 2` を満たすので、シフト集合は
`ℤ/n` の偶元全体。位数 2 (resp 4) の元 = `x` 偶 (resp 奇) ゆえ、差 (偶) は必ずシフトで実現でき、
互いに共役 = 単一共役類。 -/

/-- reflection `(x,σ)` を `inl y = (y,1)` で共役すると `(y·x·σ(y⁻¹), σ)`。 -/
theorem semidihedralReflection_conj (n : ℕ) (hn : 8 ∣ n) (x y : Multiplicative (ZMod n)) :
    SemidirectProduct.inl y * semidihedralReflection n hn x * (SemidirectProduct.inl y)⁻¹
      = semidihedralReflection n hn (y * x * semidihedralMulAut n hn y⁻¹) := by
  rw [← map_inv SemidirectProduct.inl]
  refine SemidirectProduct.ext ?_ ?_
  · simp only [semidihedralReflection, SemidirectProduct.mul_left, SemidirectProduct.left_inl]
    rfl
  · simp only [semidihedralReflection, SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      mul_one, one_mul]

/-- `(2-z)·(·)` (共役シフト) は偶元全体を覆う: `z·d = 0` (d 偶) なら `∃ t, (2-z)·t = d`。
`u = 1 + n/4` が `(2-z)·u = 2` (`(2-4k)(1+2k) = 2 - 8k² ≡ 2`) ゆえ、`d = 2s` に対し `t = u·s`。 -/
theorem semidihedral_shift_surj (n : ℕ) [NeZero n] (hn : 8 ∣ n) {d : ZMod n}
    (hd : ((n / 2 : ℕ) : ZMod n) * d = 0) :
    ∃ t : ZMod n, (2 - ((n / 2 : ℕ) : ZMod n)) * t = d := by
  obtain ⟨k, rfl⟩ := hn
  have hk : 0 < k := by have := NeZero.ne (8 * k); omega
  have d2 : 8 * k / 2 = 4 * k := by omega
  rw [d2] at hd ⊢
  have hu : ((2 : ZMod (8 * k)) - ((4 * k : ℕ) : ZMod (8 * k))) * ((1 + 2 * k : ℕ) : ZMod (8 * k))
      = 2 := by
    have h8k : (8 : ZMod (8 * k)) * (k : ZMod (8 * k)) = 0 := by
      have hh : ((8 * k : ℕ) : ZMod (8 * k)) = 0 := ZMod.natCast_self _
      push_cast at hh; linear_combination hh
    push_cast
    linear_combination (-(k : ZMod (8 * k))) * h8k
  have hs : ∃ s : ZMod (8 * k), d = 2 * s := by
    have hdv : 2 ∣ d.val := by
      have h0 : ((4 * k * d.val : ℕ) : ZMod (8 * k)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact hd
      rw [ZMod.natCast_eq_zero_iff] at h0
      have h1 : 4 * k * 2 ∣ 4 * k * d.val := by rw [show 4 * k * 2 = 8 * k by ring]; exact h0
      rwa [Nat.mul_dvd_mul_iff_left (show 0 < 4 * k by omega)] at h1
    obtain ⟨j, hj⟩ := hdv
    exact ⟨(j : ZMod (8 * k)), by rw [← ZMod.natCast_zmod_val d, hj]; push_cast; ring⟩
  obtain ⟨s, rfl⟩ := hs
  exact ⟨((1 + 2 * k : ℕ) : ZMod (8 * k)) * s, by rw [← mul_assoc, hu]⟩

/-- 差 `z·(toAdd x' - toAdd x) = 0` なら `refl x` と `refl x'` は共役 (共役子 `inl (ofAdd t)`)。 -/
theorem semidihedralReflection_isConj (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    {x x' : Multiplicative (ZMod n)}
    (hxx' : ((n / 2 : ℕ) : ZMod n) * (Multiplicative.toAdd x' - Multiplicative.toAdd x) = 0) :
    IsConj (semidihedralReflection n hn x) (semidihedralReflection n hn x') := by
  obtain ⟨t, ht⟩ := semidihedral_shift_surj n hn hxx'
  rw [isConj_iff]
  refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd t), ?_⟩
  rw [semidihedralReflection_conj]
  congr 1
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, semidihedralMulAut_apply, toAdd_ofAdd, toAdd_inv]
  linear_combination ht

/-- **Isaacs Problem 3A.1(c)** (位数 2 は単一共役類). `S - C` の位数 2 の元 (x 偶) は互いに共役。 -/
theorem semidihedralReflection_isConj_of_two (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    {x x' : Multiplicative (ZMod n)}
    (hx : ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x = 0)
    (hx' : ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x' = 0) :
    IsConj (semidihedralReflection n hn x) (semidihedralReflection n hn x') :=
  semidihedralReflection_isConj n hn (by rw [mul_sub, hx', hx, sub_zero])

/-- **Isaacs Problem 3A.1(c)** (位数 4 は単一共役類). `S - C` の位数 4 の元 (x 奇) は互いに共役。 -/
theorem semidihedralReflection_isConj_of_four (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    {x x' : Multiplicative (ZMod n)}
    (hx : ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x ≠ 0)
    (hx' : ((n / 2 : ℕ) : ZMod n) * Multiplicative.toAdd x' ≠ 0) :
    IsConj (semidihedralReflection n hn x) (semidihedralReflection n hn x') := by
  apply semidihedralReflection_isConj n hn
  have e1 := (semidihedral_invol_mul_dichotomy n (dvd_trans (by norm_num) hn)
    (Multiplicative.toAdd x)).resolve_left hx
  have e2 := (semidihedral_invol_mul_dichotomy n (dvd_trans (by norm_num) hn)
    (Multiplicative.toAdd x')).resolve_left hx'
  rw [mul_sub, e2, e1, sub_self]

/-! ### Problem 3A.2 — 一般化四元数群 `Q_n = ⟨σ⟩·B ∪ B` (位数 n)

`S = C_n ⋊ ⟨σ⟩` から `ℤ/2` への準同型 `ψ(x,h) = (x の parity) + (h の parity)` を作り、`Q := ker ψ`
とする。`ψ` 全射ゆえ `|Q| = |S|/2 = n` (= 一般化四元数群 `Q_n`)。左 parity `fn`・H parity `fg` を
`SemidirectProduct.lift` で束ねる (σ は parity を保存: `w = z-1` 奇)。 -/

/-- `σ` の位数は 2。 -/
theorem semidihedralMulAut_orderOf (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    orderOf (semidihedralMulAut n hn) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact semidihedralMulAut_sq n hn)
    (semidihedralMulAut_ne_one n hn)

/-- `H = ⟨σ⟩` の元は `1` か `σ` (位数 2 ゆえ). -/
theorem semidihedral_H_cases (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    (h : Subgroup.zpowers (semidihedralMulAut n hn)) :
    h = 1 ∨ h = ⟨semidihedralMulAut n hn, Subgroup.mem_zpowers _⟩ := by
  rcases eq_or_ne h 1 with rfl | hne
  · exact Or.inl rfl
  · refine Or.inr ?_
    have hcard : Nat.card (Subgroup.zpowers (semidihedralMulAut n hn)) = 2 := by
      rw [Nat.card_zpowers, semidihedralMulAut_orderOf]
    obtain ⟨y, -, huniq⟩ :=
      (Nat.card_eq_two_iff' (1 : Subgroup.zpowers (semidihedralMulAut n hn))).mp hcard
    have hσ : (⟨semidihedralMulAut n hn, Subgroup.mem_zpowers _⟩ :
        Subgroup.zpowers (semidihedralMulAut n hn)) ≠ 1 :=
      fun hcon => semidihedralMulAut_ne_one n hn (by simpa using Subtype.ext_iff.mp hcon)
    rw [huniq h hne, huniq _ hσ]

/-- 左成分の parity 準同型 `C_n → ℤ/2`。 -/
def semidihedralLeftParity (n : ℕ) (hn : 8 ∣ n) :
    Multiplicative (ZMod n) →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd
    (ZMod.castHom (dvd_trans (by norm_num) hn) (ZMod 2) (Multiplicative.toAdd x))
  map_one' := by simp
  map_mul' x y := by simp only [toAdd_mul, map_add, ofAdd_add]

@[simp] theorem semidihedralLeftParity_apply (n : ℕ) (hn : 8 ∣ n) (x : Multiplicative (ZMod n)) :
    semidihedralLeftParity n hn x = Multiplicative.ofAdd
      (ZMod.castHom (dvd_trans (by norm_num) hn) (ZMod 2) (Multiplicative.toAdd x)) := rfl

open Classical in
/-- H 成分の parity 準同型 `⟨σ⟩ → ℤ/2` (`σ ↦ 1`)。 -/
noncomputable def semidihedralRightParity (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    Subgroup.zpowers (semidihedralMulAut n hn) →* Multiplicative (ZMod 2) where
  toFun h := if h = 1 then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' h h' := by
    have hσσ : (⟨semidihedralMulAut n hn, Subgroup.mem_zpowers _⟩ :
        Subgroup.zpowers (semidihedralMulAut n hn)) *
        ⟨semidihedralMulAut n hn, Subgroup.mem_zpowers _⟩ = 1 :=
      Subtype.ext (by change semidihedralMulAut n hn * semidihedralMulAut n hn = 1
                      exact semidihedralMulAut_sq n hn)
    have hσ1 : (⟨semidihedralMulAut n hn, Subgroup.mem_zpowers _⟩ :
        Subgroup.zpowers (semidihedralMulAut n hn)) ≠ 1 :=
      fun hcon => semidihedralMulAut_ne_one n hn (by simpa using Subtype.ext_iff.mp hcon)
    have hof : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases semidihedral_H_cases n hn h with rfl | rfl <;>
      rcases semidihedral_H_cases n hn h' with rfl | rfl <;>
      simp [hσσ, hσ1, hof]

/-- `σ` は左 parity を保存: `fn(σ x) = fn(x)` (`w = z-1` が奇 ⟹ `cast w = 1` in `ℤ/2`)。 -/
theorem semidihedralLeftParity_mulAut (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    (x : Multiplicative (ZMod n)) :
    semidihedralLeftParity n hn (semidihedralMulAut n hn x) = semidihedralLeftParity n hn x := by
  have hn2 : ((n / 2 : ℕ) : ZMod 2) = 0 := by rw [ZMod.natCast_eq_zero_iff]; omega
  have hw : (ZMod.castHom (dvd_trans (by norm_num) hn) (ZMod 2)) (((n / 2 : ℕ) : ZMod n) - 1)
      = 1 := by rw [map_sub, map_natCast, map_one, hn2]; decide
  simp only [semidihedralLeftParity_apply, semidihedralMulAut_apply, toAdd_ofAdd, map_mul, hw,
    one_mul]

/-- **Isaacs Problem 3A.2** の parity 準同型 `ψ : S →* ℤ/2`, `ψ(x,h) = fn(x)·fg(h)`。 -/
noncomputable def semidihedralParity (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    SemidihedralGroup n hn →* Multiplicative (ZMod 2) :=
  SemidirectProduct.lift (semidihedralLeftParity n hn) (semidihedralRightParity n hn)
    (fun g => MonoidHom.ext fun x => by
      have hcancel : (semidihedralRightParity n hn) g * semidihedralLeftParity n hn x *
          ((semidihedralRightParity n hn) g)⁻¹ = semidihedralLeftParity n hn x := by
        rw [mul_comm ((semidihedralRightParity n hn) g), mul_assoc, mul_inv_cancel, mul_one]
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, hcancel]
      rcases semidihedral_H_cases n hn g with rfl | rfl
      · rfl
      · exact semidihedralLeftParity_mulAut n hn x)

@[simp] theorem semidihedralParity_inl (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    (x : Multiplicative (ZMod n)) :
    semidihedralParity n hn (SemidirectProduct.inl x) = semidihedralLeftParity n hn x := by
  rw [semidihedralParity, SemidirectProduct.lift_inl]

/-- **Isaacs Problem 3A.2** の一般化四元数群 `Q_n := ker ψ`。`ψ` 全射ゆえ位数 `|S|/2 = n`。 -/
noncomputable def semidihedralQuaternion (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    Subgroup (SemidihedralGroup n hn) :=
  (semidihedralParity n hn).ker

theorem semidihedralParity_surjective (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    Function.Surjective (semidihedralParity n hn) := by
  have hcases : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := fun z => by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (Multiplicative.toAdd z) with h | h
    · exact Or.inl (Multiplicative.toAdd.injective (by rw [h]; rfl))
    · exact Or.inr (Multiplicative.toAdd.injective (by rw [h]; rfl))
  intro y
  rcases hcases y with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨SemidirectProduct.inl (Multiplicative.ofAdd 1), by
      rw [semidihedralParity_inl, semidihedralLeftParity_apply, toAdd_ofAdd, map_one]⟩

/-- **Isaacs Problem 3A.2**. `Q_n` は位数 `n` の部分群 (= 一般化四元数群)。 -/
theorem semidihedralQuaternion_card (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    Nat.card (semidihedralQuaternion n hn) = n := by
  have hZn : Nat.card (Multiplicative (ZMod n)) = n := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod n)), Nat.card_zmod]
  have hZ2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod 2)), Nat.card_zmod]
  have hS : Nat.card (SemidihedralGroup n hn) = 2 * n := by
    rw [SemidirectProduct.card, Nat.card_zpowers, semidihedralMulAut_orderOf, hZn]; ring
  have hidx : (semidihedralQuaternion n hn).index = 2 := by
    rw [semidihedralQuaternion, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (semidihedralParity_surjective n hn),
      Nat.card_congr (Subgroup.topEquiv).toEquiv, hZ2]
  have hcard := Subgroup.card_mul_index (semidihedralQuaternion n hn)
  rw [hidx, hS] at hcard
  omega

theorem semidihedralRightParity_sigma (n : ℕ) [NeZero n] (hn : 8 ∣ n) :
    semidihedralRightParity n hn ⟨semidihedralMulAut n hn, Subgroup.mem_zpowers _⟩
      = Multiplicative.ofAdd 1 := by
  have hσ1 : (⟨semidihedralMulAut n hn, Subgroup.mem_zpowers _⟩ :
      Subgroup.zpowers (semidihedralMulAut n hn)) ≠ 1 :=
    fun hcon => semidihedralMulAut_ne_one n hn (by simpa using Subtype.ext_iff.mp hcon)
  simp only [semidihedralRightParity, MonoidHom.coe_mk, OneHom.coe_mk, if_neg hσ1]

theorem semidihedralParity_reflection (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    (x : Multiplicative (ZMod n)) :
    semidihedralParity n hn (semidihedralReflection n hn x)
      = semidihedralLeftParity n hn x * Multiplicative.ofAdd 1 := by
  rw [show semidihedralParity n hn (semidihedralReflection n hn x)
      = semidihedralLeftParity n hn x *
        semidihedralRightParity n hn ⟨semidihedralMulAut n hn, Subgroup.mem_zpowers _⟩ from rfl,
    semidihedralRightParity_sigma]

/-- **Isaacs Problem 3A.2** (`B ⊆ Q`). `inl x` (`= C_n` の元) が `Q` に属す ⟺ `x` が偶。
`B` = index-2 部分群 (偶元) はちょうど `Q ∩ C`。 -/
theorem inl_mem_quaternion_iff (n : ℕ) [NeZero n] (hn : 8 ∣ n) (x : Multiplicative (ZMod n)) :
    SemidirectProduct.inl x ∈ semidihedralQuaternion n hn
      ↔ (ZMod.castHom (dvd_trans (by norm_num) hn) (ZMod 2)) (Multiplicative.toAdd x) = 0 := by
  rw [semidihedralQuaternion, MonoidHom.mem_ker, semidihedralParity_inl,
    semidihedralLeftParity_apply, ofAdd_eq_one]

/-- **Isaacs Problem 3A.2** (位数 4 の coset ⊆ Q). reflection `(x,σ)` が `Q` に属す ⟺ `x` が奇。
位数 4 の元 (`x` 奇) 全体は `Q` 内の `B`-coset をなす。 -/
theorem reflection_mem_quaternion_iff (n : ℕ) [NeZero n] (hn : 8 ∣ n)
    (x : Multiplicative (ZMod n)) :
    semidihedralReflection n hn x ∈ semidihedralQuaternion n hn
      ↔ (ZMod.castHom (dvd_trans (by norm_num) hn) (ZMod 2)) (Multiplicative.toAdd x) = 1 := by
  rw [semidihedralQuaternion, MonoidHom.mem_ker, semidihedralParity_reflection,
    semidihedralLeftParity_apply, ← ofAdd_add, ofAdd_eq_one]
  exact (by decide : ∀ a : ZMod 2, (a + 1 = 0 ↔ a = 1)) _

/-! ### Problem 3A.3 — 位数 pm の群 (正規 P 位数 p, G/P 巡回, Z(G)=1)

`p` 素数, `m ∣ p-1`, `m > 1`。`(ZMod p)ˣ` (巡回, 位数 p-1) の位数 m 元 `u` から自己同型
`σ = ×u` を作り、`G = Multiplicative (ZMod p) ⋊ ⟨σ⟩`。`|G| = p·m`、`P = inl 像` 正規 位数 p、
`G/P ≅ ⟨σ⟩` 巡回、`Z(G) = 1` (作用が忠実 + 非自明: 体で `u-1` 可逆)。 -/

/-- 単元 `u` による `Multiplicative (ZMod p)` の乗法的自己同型 `σ = ×u`。 -/
noncomputable def sigmaOf {p : ℕ} (u : (ZMod p)ˣ) : MulAut (Multiplicative (ZMod p)) :=
  (MulAutMultiplicative (ZMod p)).symm (AddAut.mulLeft u)

theorem sigmaOf_orderOf {p : ℕ} (u : (ZMod p)ˣ) : orderOf (sigmaOf u) = orderOf u := by
  have hinj : Function.Injective
      (AddAut.mulLeft : (ZMod p)ˣ →* Multiplicative (AddAut (ZMod p))) := by
    intro a b h
    have h2 : (↑a : ZMod p) * 1 = (↑b : ZMod p) * 1 :=
      DFunLike.congr_fun (congrArg Multiplicative.toAdd h) (1 : ZMod p)
    rw [mul_one, mul_one] at h2
    exact Units.ext h2
  calc orderOf (sigmaOf u)
      = orderOf (AddAut.mulLeft u) :=
        orderOf_injective (MulAutMultiplicative (ZMod p)).symm.toMonoidHom
          (MulAutMultiplicative (ZMod p)).symm.injective _
    _ = orderOf u := orderOf_injective AddAut.mulLeft hinj u

/-- `σ` の作用: `σ(x) = ↑u · toAdd x` (乗法的). -/
@[simp] theorem sigmaOf_apply {p : ℕ} (u : (ZMod p)ˣ) (x : Multiplicative (ZMod p)) :
    sigmaOf u x = Multiplicative.ofAdd ((↑u : ZMod p) * Multiplicative.toAdd x) := rfl

/-- 位数 pm の群 `G = Multiplicative (ZMod p) ⋊ ⟨σ⟩`。 -/
abbrev affineGroup {p : ℕ} (u : (ZMod p)ˣ) :=
  SemidirectProduct (Multiplicative (ZMod p)) (Subgroup.zpowers (sigmaOf u))
    (Subgroup.zpowers (sigmaOf u)).subtype

/-- **Isaacs Problem 3A.3** (位数). `|G| = p · orderOf u`。 -/
theorem affineGroup_card {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    Nat.card (affineGroup u) = p * orderOf u := by
  rw [affineGroup, SemidirectProduct.card, Nat.card_zpowers, sigmaOf_orderOf,
    Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]

/-- **Isaacs Problem 3A.3** (存在). 位数 `pm` の群で、位数 `p` の正規部分群 `P` をもち、
`G/P` が巡回, `Z(G) = 1`。 -/
theorem exists_group_card_eq_center_trivial (p m : ℕ) [Fact p.Prime] (hm : m ∣ p - 1)
    (hm1 : 1 < m) : ∃ u : (ZMod p)ˣ, orderOf u = m := by
  haveI := ZMod.isCyclic_units_prime (Fact.out (p := p.Prime))
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hp2 := (Fact.out (p := p.Prime)).two_le
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  have hng : orderOf g = p - 1 := by rw [hg, hcard]
  have hmle : m ≤ p - 1 := Nat.le_of_dvd (by omega) hm
  have hne : (p - 1) / m ≠ 0 := by have := Nat.div_pos hmle (by omega); omega
  have hdvd : (p - 1) / m ∣ orderOf g := by rw [hng]; exact Nat.div_dvd_of_dvd hm
  exact ⟨g ^ ((p - 1) / m), by
    rw [orderOf_pow_of_dvd hne hdvd, hng, Nat.div_div_self hm (by omega)]⟩

/-- **Isaacs Problem 3A.3** (P = ker rightHom の位数). `|P| = p`。P は正規 (`MonoidHom.normal_ker`)。 -/
theorem affineGroup_card_ker {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    Nat.card (SemidirectProduct.rightHom :
      affineGroup u →* Subgroup.zpowers (sigmaOf u)).ker = p := by
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom,
    ← Nat.card_congr (MonoidHom.ofInjective
      (SemidirectProduct.inl_injective
        (φ := (Subgroup.zpowers (sigmaOf u)).subtype))).toEquiv,
    Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]

/-- **Isaacs Problem 3A.3** (G/P 巡回). `G/ker rightHom ≅ ⟨σ⟩` (巡回)。 -/
theorem affineGroup_quotient_isCyclic {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    IsCyclic (affineGroup u ⧸
      (SemidirectProduct.rightHom : affineGroup u →* Subgroup.zpowers (sigmaOf u)).ker) := by
  have e := QuotientGroup.quotientKerEquivOfSurjective
    (SemidirectProduct.rightHom : affineGroup u →* Subgroup.zpowers (sigmaOf u))
    SemidirectProduct.rightHom_surjective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

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
