/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Nat.Choose.Sum
import OddOrder.Isaacs.Ch04_Commutators.ProblemsWreath

/-!
# Isaacs Chapter 4 — Problem 4A.8(d): 正則 wreath product の冪零類

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4A.8(d) (書籍 p. 124)。

`C` を位数 `p^n` の巡回群, `Q` を位数 `p` の巡回群, `P = C ≀ Q` とすると

* `class(P) = n(p-1) + 1` (`nilpotencyClass_wreath_eq`)
* `|P| = p^{np+1}` なので **`n = 1` のとき, かつそのときに限り `P` は maximal class**
* `P'U = ker(増大射)` は `|P'U| = p^{n(p-1)+1}`, `class(P'U) = n(p-1)` で**常に maximal class**

`γ_{i+1}(P) = Δ^i(A)` ([`ProblemsWreath`](ProblemsWreath.lean) の
`lowerCentralSeries_eq_map_shiftSubSeq`) なので, すべては base 群上の「`1 - x` 作用素」
`Δ_q f = f · (f ∘ shift_q)⁻¹` の冪零指数の計算に帰着する。

## 手法: 群環 `ℤ/p^n[x]/(x^p-1)` の `(1-x)`-filtration を作用素の言葉で

`y = 1 - x`, `N = 1 + x + ⋯ + x^{p-1}` (作用素では `Δ`, `T_p`) とおくと群環で

* `y^{p-1} = N + p·s` (linchpin `(1-X)^{p-1} = ∑_j X^j` in `F_p[X]` の持ち上げ)
* `y · N = 0` (ノルム関係式), `N · s = s(1) · N = -N` (`s(1) = -1`)

が成り立ち, ここから `y^{k(p-1)} = (-1)^{k-1} p^{k-1} N` が帰納で出る。作用素版では

* **基底** `Δ^{p-1} f = T_p f · g^p` かつ `T_p g = (T_p f)⁻¹`
  (`exists_witness_shiftSubHom_iterate_prime_sub_one`; 重み `e_j = ((-1)^j C(p-1,j) - 1)/p`)
* **帰納** `Δ^{k(p-1)} f = (T_p f)^{(-1)^{k-1}p^{k-1}} · g^{p^k}`
  (`exists_shiftSubHom_iterate_mul_prime_sub_one`)

となり, `D` の指数が `p^n` なら第 2 因子が消えて `Δ^{n(p-1)} f = (T_p f)^{±p^{n-1}}`。
上界は `Δ ∘ T_p = 1` から, 下界は `f = δ₁ c` で `T_p f = const c` かつ
`c^{p^{n-1}} ≠ 1` から出る。群環や加群を構成せずに済むのが要点。
-/

namespace OddOrder.Isaacs.Ch04

open OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch03.WreathProduct

open scoped commutatorElement

section /- Problem 4A.8(d): 冪零類 (p. 124) -/

variable {D Q : Type*} [CommGroup D] [Group Q]

/-! ### `Δ^{p-1} = T_p · (p 乗)` — 群環の `y^{p-1} = N + p·s` -/

/-- `∏_{j ∈ s} v ^ e j = v ^ ∑_{j ∈ s} e j` (可換群の zpow 版). -/
theorem prod_zpow_eq_zpow_sum (v : D) (s : Finset ℕ) (e : ℕ → ℤ) :
    (∏ j ∈ s, v ^ e j) = v ^ (∑ j ∈ s, e j) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

/-- **群環の `y^{p-1} = N + p·s`** の作用素版 (`s(1) = -1` 込み).

`Δ^{p-1} f = T_p f · g^p` かつ `T_p g = (T_p f)⁻¹` なる `g` が存在する.
`g` は重み `e_j = ((-1)^j C(p-1,j) - 1)/p` (整数; `cast_choose_prime_sub_one` で割り切れる)
による重み付き shift 積 `g ω = ∏_{j<p} f((q^j)⁻¹ω)^{e_j}`.

第 2 条件は `∑_{j<p} e_j = -1` (交代和 `∑_j (-1)^j C(p-1,j) = 0` から) の言い換えで,
群環の `N·s = s(1)·N = -N` にあたる. `D` の指数には**何も仮定しない**. -/
theorem exists_witness_shiftSubHom_iterate_prime_sub_one [Fintype Q] {r : ℕ} (hr : Nat.Prime r)
    {q : Q} (hq : orderOf q = Fintype.card Q) (hQcard : Fintype.card Q = r) (f : Q → D) :
    ∃ g : Q → D, (⇑(shiftSubHom (D := D) q))^[r - 1] f = shiftSumHom q r f * g ^ r
      ∧ shiftSumHom q r g = (shiftSumHom q r f)⁻¹ := by
  have hr2 := hr.two_le
  have hr1 : r - 1 + 1 = r := by omega
  -- 重み `e_j`
  set e : ℕ → ℤ := fun j => ((-1) ^ j * ((r - 1).choose j : ℤ) - 1) / (r : ℤ) with he
  have hwe : ∀ j < r, (r : ℤ) * e j = (-1) ^ j * ((r - 1).choose j : ℤ) - 1 := by
    intro j hj
    refine Int.mul_ediv_cancel' ?_
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    rw [Int.cast_sub, cast_neg_one_pow_mul_choose_prime_sub_one hr hj, Int.cast_one, sub_self]
  -- 重みの総和は `-1`
  have hsum : (∑ j ∈ Finset.range r, e j) = -1 := by
    have halt : (∑ j ∈ Finset.range r, ((-1) ^ j * ((r - 1).choose j : ℤ))) = 0 := by
      have := Int.alternating_sum_range_choose_of_ne (n := r - 1) (by omega)
      rwa [hr1] at this
    have hmul : (r : ℤ) * (∑ j ∈ Finset.range r, e j) = (r : ℤ) * (-1) := by
      rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl fun j hj => hwe j (Finset.mem_range.mp hj)]
      rw [Finset.sum_sub_distrib, halt]
      simp
    exact mul_left_cancel₀ (by exact_mod_cast hr.ne_zero) hmul
  refine ⟨fun ω => ∏ j ∈ Finset.range r, f ((q ^ j)⁻¹ * ω) ^ e j, ?_, ?_⟩
  · funext ω
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [shiftSubHom_iterate_apply, shiftSumHom_apply, hr1, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    calc f ((q ^ j)⁻¹ * ω) ^ ((-1) ^ j * ((r - 1).choose j : ℤ))
        = f ((q ^ j)⁻¹ * ω) ^ (1 + e j * (r : ℤ)) := by
          congr 1
          have := hwe j hj'
          linarith
      _ = f ((q ^ j)⁻¹ * ω) * (f ((q ^ j)⁻¹ * ω) ^ e j) ^ r := by
          rw [zpow_add, zpow_one, zpow_mul, zpow_natCast]
  · have hconst : ∀ h : Q → D, shiftSumHom q r h = Function.const Q (∏ y, h y) := by
      intro h
      rw [← hQcard]
      exact shiftSumHom_card_eq_const hq h
    rw [hconst, hconst]
    have hprod : (∏ y : Q, ∏ j ∈ Finset.range r, f ((q ^ j)⁻¹ * y) ^ e j)
        = (∏ y : Q, f y)⁻¹ := by
      rw [Finset.prod_comm]
      have hinner : ∀ j ∈ Finset.range r,
          (∏ y : Q, f ((q ^ j)⁻¹ * y) ^ e j) = (∏ y : Q, f y) ^ e j := by
        intro j _
        rw [← Finset.prod_zpow]
        exact prod_smul_eq (fun y => f y ^ e j) (q ^ j)
      rw [Finset.prod_congr rfl hinner, prod_zpow_eq_zpow_sum, hsum, zpow_neg, zpow_one]
    rw [hprod]
    rfl

/-! ### `Δ^{k(p-1)}` の閉じた形 -/

/-- `Δ^{p-1}` は定数関数を消す (`p ≥ 2` ゆえ `Δ` を 1 回は当てられる): 群環の `y·N = 0`. -/
theorem shiftSubHom_iterate_prime_sub_one_shiftSumHom [Fintype Q] {r : ℕ} (hr : Nat.Prime r)
    {q : Q} (hq : orderOf q = Fintype.card Q) (hQcard : Fintype.card Q = r) (f : Q → D) :
    (⇑(shiftSubHom (D := D) q))^[r - 1] (shiftSumHom q r f) = 1 := by
  have hr2 := hr.two_le
  have hnorm := shiftSubHom_shiftSumHom_card (D := D) hq f
  rw [hQcard] at hnorm
  rw [show r - 1 = (r - 2) + 1 by omega, Function.iterate_succ_apply, hnorm,
    iterate_map_one (shiftSubHom (D := D) q)]

/-- **`Δ^{k(p-1)}` の閉じた形**: `Δ^{(m+1)(p-1)} f = (T_p f)^{(-1)^m p^m} · g^{p^{m+1}}` で,
さらに `T_p g = (T_p f)^{(-1)^{m+1}}`.

群環の `y^{k(p-1)} = (-1)^{k-1}p^{k-1}N + p^k(⋯)` にあたる. 帰納段は
`Δ^{p-1}` を掛けて基底 (`exists_witness_shiftSubHom_iterate_prime_sub_one`) を `g` に当て,
第 1 因子が `Δ^{p-1}(T_p f) = 1` で消えることを使う. -/
theorem exists_shiftSubHom_iterate_mul_prime_sub_one [Fintype Q] {r : ℕ} (hr : Nat.Prime r)
    {q : Q} (hq : orderOf q = Fintype.card Q) (hQcard : Fintype.card Q = r) (f : Q → D) (m : ℕ) :
    ∃ g : Q → D,
      (⇑(shiftSubHom (D := D) q))^[(m + 1) * (r - 1)] f
          = shiftSumHom q r f ^ ((-1 : ℤ) ^ m * (r : ℤ) ^ m) * g ^ r ^ (m + 1)
        ∧ shiftSumHom q r g = shiftSumHom q r f ^ ((-1 : ℤ) ^ (m + 1)) := by
  induction m with
  | zero =>
    obtain ⟨g, hg1, hg2⟩ := exists_witness_shiftSubHom_iterate_prime_sub_one hr hq hQcard f
    exact ⟨g, by simpa using hg1, by simpa using hg2⟩
  | succ m ih =>
    obtain ⟨h, hh1, hh2⟩ := ih
    obtain ⟨g, hg1, hg2⟩ := exists_witness_shiftSubHom_iterate_prime_sub_one hr hq hQcard h
    refine ⟨g, ?_, ?_⟩
    · rw [show (m + 1 + 1) * (r - 1) = (r - 1) + (m + 1) * (r - 1) by ring,
        Function.iterate_add_apply, hh1, iterate_map_mul, iterate_map_zpow, iterate_map_pow,
        shiftSubHom_iterate_prime_sub_one_shiftSumHom hr hq hQcard, one_zpow, one_mul, hg1,
        mul_pow, ← pow_mul, hh2, ← zpow_natCast (shiftSumHom q r f ^ ((-1 : ℤ) ^ (m + 1))),
        ← zpow_mul]
      congr 2
      ring
    · rw [hg2, hh2, ← zpow_neg]
      congr 1
      ring

/-! ### 指数 `p^n` の base に対する上下界 -/

/-- **上界** `Δ^{n(p-1)+1} = 1` (base の指数が `p^n` のとき). -/
theorem shiftSubHom_iterate_eq_one_of_exponent [Fintype Q] {r n : ℕ} (hr : Nat.Prime r)
    (hn : n ≠ 0) (hD : ∀ d : D, d ^ r ^ n = 1) {q : Q} (hq : orderOf q = Fintype.card Q)
    (hQcard : Fintype.card Q = r) (f : Q → D) :
    (⇑(shiftSubHom (D := D) q))^[n * (r - 1) + 1] f = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨g, hg1, -⟩ := exists_shiftSubHom_iterate_mul_prime_sub_one hr hq hQcard f m
  have hgone : g ^ r ^ (m + 1) = 1 := by
    funext ω
    exact hD (g ω)
  have hnorm := shiftSubHom_shiftSumHom_card (D := D) hq f
  rw [hQcard] at hnorm
  rw [Function.iterate_succ_apply', hg1, hgone, mul_one, map_zpow, hnorm, one_zpow]

/-- **閉じた形 (指数 `p^n`)**: `Δ^{n(p-1)} f = (T_p f)^{(-1)^{n-1}p^{n-1}}`. -/
theorem shiftSubHom_iterate_mul_prime_sub_one_eq [Fintype Q] {r n : ℕ} (hr : Nat.Prime r)
    (hn : n ≠ 0) (hD : ∀ d : D, d ^ r ^ n = 1) {q : Q} (hq : orderOf q = Fintype.card Q)
    (hQcard : Fintype.card Q = r) (f : Q → D) :
    (⇑(shiftSubHom (D := D) q))^[n * (r - 1)] f
      = shiftSumHom q r f ^ ((-1 : ℤ) ^ (n - 1) * (r : ℤ) ^ (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨g, hg1, -⟩ := exists_shiftSubHom_iterate_mul_prime_sub_one hr hq hQcard f m
  have hgone : g ^ r ^ (m + 1) = 1 := by
    funext ω
    exact hD (g ω)
  simpa [hgone] using hg1

/-! ### 下降中心列の両端と冪零類 -/

/-- **上界 (部分群版)** `Δ^{n(p-1)+1}(⊤) = ⊥`. -/
theorem shiftSubSeq_eq_bot_of_exponent [Fintype Q] {r n : ℕ} (hr : Nat.Prime r) (hn : n ≠ 0)
    (hD : ∀ d : D, d ^ r ^ n = 1) {q : Q} (hq : orderOf q = Fintype.card Q)
    (hQcard : Fintype.card Q = r) : shiftSubSeq (D := D) q (n * (r - 1) + 1) = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => ?_
  obtain ⟨f, rfl⟩ := (mem_shiftSubSeq_iff q _ g).mp hg
  rw [Subgroup.mem_bot]
  exact shiftSubHom_iterate_eq_one_of_exponent hr hn hD hq hQcard f

/-- **下界 (部分群版)** `Δ^{n(p-1)}(⊤) ≠ ⊥`: witness は指示関数 `δ₁ c` (`c^{p^{n-1}} ≠ 1`).

閉じた形 `Δ^{n(p-1)}(δ₁ c) = (T_p (δ₁ c))^{±p^{n-1}} = const (c^{±p^{n-1}})` から. -/
theorem shiftSubSeq_ne_bot_of_exponent [Fintype Q] {r n : ℕ} (hr : Nat.Prime r) (hn : n ≠ 0)
    (hD : ∀ d : D, d ^ r ^ n = 1) {c : D} (hc : c ^ r ^ (n - 1) ≠ 1) {q : Q}
    (hq : orderOf q = Fintype.card Q) (hQcard : Fintype.card Q = r) :
    shiftSubSeq (D := D) q (n * (r - 1)) ≠ ⊥ := by
  classical
  intro hbot
  have hmem := (mem_shiftSubSeq_iff (D := D) q (n * (r - 1))
    ((⇑(shiftSubHom (D := D) q))^[n * (r - 1)] fun ω : Q => if ω = 1 then c else 1)).mpr ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot,
    shiftSubHom_iterate_mul_prime_sub_one_eq hr hn hD hq hQcard] at hmem
  have hconst : shiftSumHom q r (fun ω : Q => if ω = 1 then c else 1) = Function.const Q c := by
    rw [← hQcard, shiftSumHom_card_eq_const hq]
    exact congrArg _ (prod_ite_eq_self 1 c)
  rw [hconst] at hmem
  have hval : c ^ ((-1 : ℤ) ^ (n - 1) * (r : ℤ) ^ (n - 1)) = 1 := congrFun hmem 1
  refine hc ?_
  have hsq : ((-1 : ℤ) ^ (n - 1)) * ((-1 : ℤ) ^ (n - 1)) = 1 := by
    rw [← mul_pow]; norm_num
  have h2 : (c ^ ((-1 : ℤ) ^ (n - 1) * (r : ℤ) ^ (n - 1))) ^ ((-1 : ℤ) ^ (n - 1)) = 1 := by
    rw [hval, one_zpow]
  rw [← zpow_mul, show (-1 : ℤ) ^ (n - 1) * (r : ℤ) ^ (n - 1) * (-1) ^ (n - 1)
      = (r : ℤ) ^ (n - 1) by rw [mul_right_comm, hsq, one_mul]] at h2
  exact_mod_cast h2

/-- **Problem 4A.8(d) の核 (一般 `n`)**: base `D` の指数がちょうど `p^n`
(`∀ d, d^{p^n} = 1` かつ `c^{p^{n-1}} ≠ 1` なる `c` がある), `Q` が位数 `p` の巡回群なら

`class(D ≀ Q) = n(p-1) + 1`.

`γ_{i+1}(P) = Δ^i(A)` と `Δ` の冪零指数 (上界 `shiftSubSeq_eq_bot_of_exponent` /
下界 `shiftSubSeq_ne_bot_of_exponent`) から. -/
theorem nilpotencyClass_wreath_eq [Fintype Q] {r n : ℕ} (hr : Nat.Prime r) (hn : n ≠ 0)
    (hD : ∀ d : D, d ^ r ^ n = 1) {c : D} (hc : c ^ r ^ (n - 1) ≠ 1) {q : Q}
    (hqgen : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k) (hQcard : Fintype.card Q = r) :
    Group.nilpotencyClass (D ≀[Q] Q) = n * (r - 1) + 1 := by
  have hr2 := hr.two_le
  have hq : orderOf q = Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    refine orderOf_eq_card_of_forall_mem_zpowers fun x => ?_
    obtain ⟨k, rfl⟩ := hqgen x
    exact ⟨(k : ℤ), by simp⟩
  have hpos : 1 ≤ n * (r - 1) := Nat.one_le_iff_ne_zero.mpr (by
    simpa using Nat.mul_ne_zero hn (by omega))
  have htop : Subgroup.lowerCentralSeries (⊤ : Subgroup (D ≀[Q] Q)) (n * (r - 1) + 1) = ⊥ := by
    rw [lowerCentralSeries_eq_map_shiftSubSeq (D := D) hqgen (n * (r - 1)),
      shiftSubSeq_eq_bot_of_exponent hr hn hD hq hQcard, Subgroup.map_bot]
  haveI : Group.IsNilpotent (D ≀[Q] Q) :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨_, htop⟩
  have hle := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp htop
  have hlow : Subgroup.lowerCentralSeries (⊤ : Subgroup (D ≀[Q] Q)) (n * (r - 1)) ≠ ⊥ := by
    have hidx := lowerCentralSeries_eq_map_shiftSubSeq (D := D) hqgen (n * (r - 1) - 1)
    rw [show n * (r - 1) - 1 + 1 = n * (r - 1) by omega] at hidx
    rw [hidx]
    intro h
    exact shiftSubSeq_ne_bot_of_exponent hr hn hD hc hq hQcard
      ((Subgroup.map_eq_bot_iff_of_injective _ inl_injective).mp h)
  have hlt : ¬ Group.nilpotencyClass (D ≀[Q] Q) ≤ n * (r - 1) := fun h =>
    hlow (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h)
  omega

/-! ### `P'U = ker(増大射)` の下降中心列 -/

/-- `q` の冪で尽くされる群は可換. -/
theorem mul_comm_of_forall_eq_pow {q : Q} (hq : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k) (a b : Q) :
    a * b = b * a := by
  obtain ⟨j, rfl⟩ := hq a
  obtain ⟨k, rfl⟩ := hq b
  exact (Commute.pow_pow (Commute.refl q) j k).eq

/-- `inr` の像は増大射の核に入る. -/
theorem inr_mem_ker_augHom [Fintype Q] (a : Q) :
    (inr a : D ≀[Q] Q) ∈ (augHom (D := D) (Q := Q)).ker := by
  change (∏ ω, (inr a : D ≀[Q] Q).left ω) = 1
  simp

/-- 4A.8(b) の言い換え: `P' = ⁅A,U⁆` の base 側は `Δ_q(A)`. -/
theorem ker_coordProdHom_eq_shiftSubSeq [Fintype Q] {q : Q}
    (hq : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k) :
    (coordProdHom (D := D) (Q := Q)).ker = shiftSubSeq (D := D) q 1 := by
  refine Subgroup.map_injective (inl_injective (D := D) (Q := Q) (Ω := Q)) ?_
  rw [← commutator_eq_coordProdHom_ker_map (mul_comm_of_forall_eq_pow hq),
    ← Subgroup.top_lowerCentralSeries_one, lowerCentralSeries_eq_map_shiftSubSeq hq 0]

/-- **`P'U` の導来部分群** `⁅P'U, P'U⁆ = Δ²(A) の像`.

`P'U` の元は `inl x.left · inr x.right` (`x.left ∈ ker(coordProd)`) と分解でき,
`inr` 成分どうしの交換子は `Q` 可換ゆえ消えるので, 交換子はすべて
`⁅inl(base 元), P'U⁆` に落ちる. あとは `commutator_map_inl_eq`. -/
theorem commutator_ker_augHom_self [Fintype Q] {q : Q} (hq : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k) :
    ⁅(augHom (D := D) (Q := Q)).ker, (augHom (D := D) (Q := Q)).ker⁆
      = (shiftSubSeq (D := D) q 2).map inl := by
  have hSseq : (coordProdHom (D := D) (Q := Q)).ker = shiftSubSeq (D := D) q 1 :=
    ker_coordProdHom_eq_shiftSubSeq hq
  have hstable : (coordProdHom (D := D) (Q := Q)).ker.map (shiftHom q)
      ≤ (coordProdHom (D := D) (Q := Q)).ker := by
    rw [hSseq]; exact shiftSubSeq_shift_stable q 1
  have hkey : ⁅(coordProdHom (D := D) (Q := Q)).ker.map (inl : (Q → D) →* D ≀[Q] Q),
      (augHom (D := D) (Q := Q)).ker⁆ = (shiftSubSeq (D := D) q 2).map inl := by
    rw [commutator_map_inl_eq hq hstable (inr_mem_ker_augHom q), hSseq]
    rfl
  have hle : (coordProdHom (D := D) (Q := Q)).ker.map (inl : (Q → D) →* D ≀[Q] Q)
      ≤ (augHom (D := D) (Q := Q)).ker := by
    rintro _ ⟨f, hf, rfl⟩
    exact hf
  refine le_antisymm ?_ (hkey ▸ Subgroup.commutator_mono hle le_rfl)
  rw [← hkey]
  haveI hnormal : (⁅(coordProdHom (D := D) (Q := Q)).ker.map (inl : (Q → D) →* D ≀[Q] Q),
      (augHom (D := D) (Q := Q)).ker⁆).Normal := by
    rw [hkey, ← lowerCentralSeries_eq_map_shiftSubSeq hq 1]
    infer_instance
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  -- `⁅inr t, y⁆` は base 側の交換子に落ちる
  have hinr : ∀ t : Q, ⁅(inr t : D ≀[Q] Q), y⁆
      ∈ ⁅(coordProdHom (D := D) (Q := Q)).ker.map (inl : (Q → D) →* D ≀[Q] Q),
          (augHom (D := D) (Q := Q)).ker⁆ := by
    intro t
    have hbase : ⁅y, (inr t : D ≀[Q] Q)⁆ = ⁅(inl y.left : D ≀[Q] Q), inr t⁆ := by
      conv_lhs => rw [← inl_left_mul_inr_right y]
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hzero : ⁅(inr y.right : D ≀[Q] Q), (inr t : D ≀[Q] Q)⁆ = 1 := by
        rw [← map_commutatorElement, commutatorElement_eq_one_iff_commute.mpr
          (mul_comm_of_forall_eq_pow hq y.right t), map_one]
      rw [hzero]
      group
    rw [← commutatorElement_inv y, hbase]
    exact Subgroup.inv_mem _
      (Subgroup.commutator_mem_commutator ⟨y.left, hy, rfl⟩ (inr_mem_ker_augHom t))
  have hxe : ⁅x, y⁆ = ⁅(inl x.left : D ≀[Q] Q) * inr x.right, y⁆ := by
    rw [inl_left_mul_inr_right]
  rw [hxe, commutatorElement_mul_left_eq_conj_mul]
  exact Subgroup.mul_mem _ (hnormal.conj_mem _ (hinr x.right) _)
    (Subgroup.commutator_mem_commutator ⟨x.left, hx, rfl⟩ hy)

/-- **`P'U` の下降中心列**: `γ_{i+2}(P'U) = Δ^{i+2}(A) の像` (= `γ_{i+3}(P)`).

基底は `commutator_ker_augHom_self`, 帰納段は `commutator_map_inl_eq` (`inr q ∈ P'U`). -/
theorem lowerCentralSeries_ker_augHom_eq [Fintype Q] {q : Q}
    (hq : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k) (i : ℕ) :
    Subgroup.lowerCentralSeries ((augHom (D := D) (Q := Q)).ker) (i + 1)
      = (shiftSubSeq (D := D) q (i + 2)).map inl := by
  induction i with
  | zero =>
    rw [Subgroup.lowerCentralSeries_succ]
    exact commutator_ker_augHom_self hq
  | succ i ih =>
    rw [Subgroup.lowerCentralSeries_succ, ih]
    exact commutator_map_inl_eq hq (shiftSubSeq_shift_stable q (i + 2)) (inr_mem_ker_augHom q)

/-- 部分群の冪零類は**環境群の中で計算した**下降中心列で判定できる. -/
theorem nilpotencyClass_le_iff_lowerCentralSeries_eq_bot {G : Type*} [Group G] (S : Subgroup G)
    [Group.IsNilpotent ↥S] {m : ℕ} :
    Group.nilpotencyClass ↥S ≤ m ↔ S.lowerCentralSeries m = ⊥ := by
  rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    ← Subgroup.top_subtype_lowerCentralSeries S m,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective S)]

/-- **`class(P'U) = n(p-1)`** (`P'U = ker(増大射)`).

`γ_{i+2}(P'U) = Δ^{i+2}(A)` なので `P` より 1 段だけ短い. -/
theorem nilpotencyClass_ker_augHom_eq [Fintype Q] {r n : ℕ} (hr : Nat.Prime r) (hn : n ≠ 0)
    (hD : ∀ d : D, d ^ r ^ n = 1) {c : D} (hc : c ^ r ^ (n - 1) ≠ 1) {q : Q}
    (hqgen : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k) (hQcard : Fintype.card Q = r) :
    Group.nilpotencyClass ↥((augHom (D := D) (Q := Q)).ker) = n * (r - 1) := by
  have hr2 := hr.two_le
  have hq : orderOf q = Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    refine orderOf_eq_card_of_forall_mem_zpowers fun x => ?_
    obtain ⟨k, rfl⟩ := hqgen x
    exact ⟨(k : ℤ), by simp⟩
  have hm1 : 1 ≤ n * (r - 1) :=
    Nat.one_le_iff_ne_zero.mpr (by simpa using Nat.mul_ne_zero hn (by omega))
  have hbot : ((augHom (D := D) (Q := Q)).ker).lowerCentralSeries (n * (r - 1)) = ⊥ := by
    have hidx := lowerCentralSeries_ker_augHom_eq (D := D) hqgen (n * (r - 1) - 1)
    rw [show n * (r - 1) - 1 + 1 = n * (r - 1) by omega,
      show n * (r - 1) - 1 + 2 = n * (r - 1) + 1 by omega] at hidx
    rw [hidx, shiftSubSeq_eq_bot_of_exponent hr hn hD hq hQcard, Subgroup.map_bot]
  haveI : Group.IsNilpotent ↥((augHom (D := D) (Q := Q)).ker) :=
    (Subgroup.isNilpotent_iff_lowerCentralSeries _).mpr ⟨_, hbot⟩
  have hle := (nilpotencyClass_le_iff_lowerCentralSeries_eq_bot _).mpr hbot
  have hnlt : ¬ Group.nilpotencyClass ↥((augHom (D := D) (Q := Q)).ker) ≤ n * (r - 1) - 1 := by
    intro hcon
    have hb := (nilpotencyClass_le_iff_lowerCentralSeries_eq_bot _).mp hcon
    rcases Nat.eq_zero_or_pos (n * (r - 1) - 1) with h0 | hpos
    · rw [h0, Subgroup.lowerCentralSeries_zero] at hb
      have hmem : (inr q : D ≀[Q] Q) ∈ (⊥ : Subgroup (D ≀[Q] Q)) := hb ▸ inr_mem_ker_augHom q
      have hq1 : q = 1 :=
        inr_injective ((Subgroup.mem_bot.mp hmem).trans (map_one inr).symm)
      rw [hq1, orderOf_one, hQcard] at hq
      omega
    · obtain ⟨i, hi⟩ : ∃ i, n * (r - 1) - 1 = i + 1 := ⟨n * (r - 1) - 2, by omega⟩
      rw [hi, lowerCentralSeries_ker_augHom_eq hqgen i,
        show i + 2 = n * (r - 1) by omega] at hb
      exact shiftSubSeq_ne_bot_of_exponent hr hn hD hc hq hQcard
        ((Subgroup.map_eq_bot_iff_of_injective _ inl_injective).mp hb)
  omega

/-! ### maximal class の判定 -/

/-- 位数 `p^n` の巡回群の生成元は `p^{n-1}` 乗しても `1` にならない. -/
theorem exists_pow_prime_pow_sub_one_ne_one [Finite D] [IsCyclic D] {r n : ℕ} (hr : 1 < r)
    (hn : n ≠ 0) (hD : Nat.card D = r ^ n) : ∃ c : D, c ^ r ^ (n - 1) ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
  refine ⟨g, fun hcon => ?_⟩
  have horder : orderOf g = r ^ n := by
    rw [← hD]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : r ^ n ∣ r ^ (n - 1) := horder ▸ orderOf_dvd_of_pow_eq_one hcon
  have hle := Nat.le_of_dvd (pow_pos (by omega) _) hdvd
  have hlt : r ^ (n - 1) < r ^ n := Nat.pow_lt_pow_right hr (by omega)
  omega

omit [CommGroup D] [Group Q] in
/-- `|C ≀ Q| = p^{np+1}` (`|C| = p^n`, `|Q| = p`). -/
theorem card_wreath_eq_pow [Finite Q] [Finite D] {r n : ℕ} (hD : Nat.card D = r ^ n)
    (hQ : Nat.card Q = r) : Nat.card (D ≀[Q] Q) = r ^ (n * r + 1) := by
  rw [OddOrder.Isaacs.Ch03.WreathProduct.card (D := D) (Q := Q) (Ω := Q), hD, hQ, ← pow_mul,
    ← pow_succ]

/-- `|P'U| = p^{n(p-1)+1}` (`P'U` は増大射の核, 指数 `|C| = p^n`). -/
theorem card_ker_augHom_eq_pow [Fintype Q] [Finite D] {r n : ℕ} (hr : 1 < r)
    (hD : Nat.card D = r ^ n) (hQ : Nat.card Q = r) :
    Nat.card ((augHom (D := D) (Q := Q)).ker) = r ^ (n * (r - 1) + 1) := by
  have hmul := card_ker_augHom_eq (D := D) (Q := Q)
  rw [hD, hQ] at hmul
  have hkey : r ^ (n * (r - 1) + 1) * r ^ n = (r ^ n) ^ r * r := by
    rw [← pow_add, ← pow_mul, ← pow_succ]
    congr 1
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (by omega) n) (hmul.trans hkey.symm)

/-- **Problem 4A.8(d) 後半**: `P'U = ker(増大射)` は**つねに maximal class**.

`|P'U| = p^{n(p-1)+1}` かつ `class(P'U) = n(p-1)` なので指数と類がちょうど 1 違い. -/
theorem isMaximalClassPGroup_ker_augHom [Fintype Q] [Finite D] [IsCyclic D] {r n : ℕ}
    (hr : Nat.Prime r) (hn : n ≠ 0) (hD : Nat.card D = r ^ n) {q : Q}
    (hqgen : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k) (hQ : Nat.card Q = r) :
    IsMaximalClassPGroup r ↥((augHom (D := D) (Q := Q)).ker) := by
  have hexp : ∀ d : D, d ^ r ^ n = 1 := fun d => by rw [← hD]; exact pow_card_eq_one'
  obtain ⟨c, hc⟩ := exists_pow_prime_pow_sub_one_ne_one hr.one_lt hn hD
  have hcard := card_ker_augHom_eq_pow (D := D) (Q := Q) hr.one_lt hD hQ
  refine ⟨IsPGroup.of_card hcard, n * (r - 1) + 1, hcard, ?_⟩
  rw [nilpotencyClass_ker_augHom_eq hr hn hexp hc hqgen
    (by rw [← Nat.card_eq_fintype_card]; exact hQ)]

/-- **Problem 4A.8(d) 前半**: `P = C ≀ Q` が maximal class ⟺ `n = 1`.

`|P| = p^{np+1}` なので maximal class は `class(P) = np` を要求するが,
実際の類は `n(p-1)+1` (`nilpotencyClass_wreath_eq`) で, 両者が一致するのは `n = 1` のときのみ. -/
theorem isMaximalClassPGroup_wreath_iff [Finite Q] [Finite D] [IsCyclic D] {r n : ℕ}
    (hr : Nat.Prime r) (hn : n ≠ 0) (hD : Nat.card D = r ^ n) {q : Q}
    (hqgen : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k) (hQ : Nat.card Q = r) :
    IsMaximalClassPGroup r (D ≀[Q] Q) ↔ n = 1 := by
  letI : Fintype Q := Fintype.ofFinite Q
  have hr2 := hr.two_le
  have hexp : ∀ d : D, d ^ r ^ n = 1 := fun d => by rw [← hD]; exact pow_card_eq_one'
  obtain ⟨c, hc⟩ := exists_pow_prime_pow_sub_one_ne_one hr.one_lt hn hD
  have hcard := card_wreath_eq_pow (D := D) (Q := Q) hD hQ
  have hclass := nilpotencyClass_wreath_eq hr hn hexp hc hqgen
    (by rw [← Nat.card_eq_fintype_card]; exact hQ)
  have harith : n * (r - 1) + n = n * r := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  constructor
  · rintro ⟨-, m, hm, hmax⟩
    have hmeq : m = n * r + 1 := Nat.pow_right_injective hr2 (hm.symm.trans hcard)
    rw [hclass, hmeq] at hmax
    omega
  · rintro rfl
    refine ⟨IsPGroup.of_card hcard, _, hcard, ?_⟩
    rw [hclass]
    omega

end

end OddOrder.Isaacs.Ch04
