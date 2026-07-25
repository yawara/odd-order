/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import OddOrder.Isaacs.Ch02_Subnormality.Theorem211Wielandt

/-!
# Isaacs Chapter 2 — Problems §2B: involution と二面体群 (p. 57)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) の章末演習 §2B のうち **involution
(位数 2 の元) と二面体群**を扱う問題 (2B.2-2B.5)。§2B の部分正規性の問題 (2B.1) は
`Problems.lean` (実体は `Basic.lean` の `isSubnormal_of_forall_nilpotent_or_permutable`)。

⚠ 同ディレクトリの `DihedralBasics.lean` は「巡回部分群を反転する involution」型の**抽象**
補題群 (Lemma 2.14 / Matsuyama で使う) であって、mathlib の具体的な `DihedralGroup n` は
扱っていない。本ファイルは mathlib `DihedralGroup n` (元は `r i` / `sr i`, `i : ZMod n`,
位数 `2n`) の上で議論する。

## 主な内容

- involution の分類 (`orderOf_r_eq_two_iff` / `orderOf_sr` (mathlib) / `orderOf_eq_two_iff`)
- 共役計算 (`r_conj_sr` / `sr_conj_sr` / `exists_sr_of_isConj_sr` / `not_isConj_sr_r`)
- **2B.2(a)** (`n` 奇): involution はちょうど `n` 個 (`card_involutions_of_odd`) で、
  すべて単一の共役類 (`isConj_sr_of_odd`)。
- **2B.2(b)** (`n = m + m` 偶): involution はちょうど `n + 1` 個
  (`card_involutions_of_even`)、共役類はちょうど 3 つでサイズ `1, m, m`
  (`conjClass_r_natCast_half_eq` / `ncard_conjClass_sr` / `not_isConj_sr_zero_sr_one`)。
  鏡映の共役類は添字の「偶奇」で決まる (`parityHom : ZMod (m+m) →+* ZMod 2`,
  `isConj_sr_sr_iff_of_even`)。
- **2B.3** (一般の有限群): 共役でない 2 つの involution `s, t` に対し、両方と可換で
  どちらとも異なる involution が存在する (`exists_involution_commuting_of_not_isConj`)。
  二面体群の構造定理は使わず、`s`, `t` が `st` を反転することだけから示す。
- **2B.4** (一般の有限群): Sylow 2-部分群が 2 つ以上あり互いに自明交叉 (TI) なら、involution は
  ちょうど 1 つの共役類をなす (`isConj_of_orderOf_eq_two_of_sylow_ti` +
  `exists_orderOf_eq_two_of_exists_sylow_two_ne`)。2B.3 が核。
- **2B.5** (generalized dihedral): 指数 2 の部分群 `B ≤ G` について 3 条件の同値
  (`generalizedDihedral_tfae`) と、そのとき `B` が可換であること
  (`isMulCommutative_of_generalizedDihedral`)。
- **2B.6**: 有限群 `G` が正規 Sylow `p`-部分群をもつ ⟺ `p`-冪位数の共役元が生成する
  `⟨x, x^g⟩` がすべて正規 Sylow `p`-部分群をもつ (`exists_normal_sylow_iff_forall_conj_pair`)。
  Baer-Suzuki (Thm 2.15) が核。

⚠ 本ファイルは §2B の involution / 二面体群まわりの問題を集めた leaf だが、2B.6 だけは
Sylow の局所判定 (involution とは無関係) — §2B の残り 1 問なのでここに置いている。
-/

namespace OddOrder.Isaacs.Ch02

namespace DihedralGroup

open _root_.DihedralGroup

variable {n : ℕ}

section /- Problems 2B: involutions in dihedral groups (p. 57) -/

/-- `r i = 1` は `i = 0` と同値。 -/
theorem r_eq_one_iff (i : ZMod n) : (r i : _root_.DihedralGroup n) = 1 ↔ i = 0 := by
  rw [one_def]
  exact ⟨fun h => by injection h, fun h => by rw [h]⟩

/-- **回転部分の involution 判定**: `r i` の位数が `2` ⟺ `i ≠ 0` かつ `2i = 0`。 -/
theorem orderOf_r_eq_two_iff (i : ZMod n) :
    orderOf (r i : _root_.DihedralGroup n) = 2 ↔ i ≠ 0 ∧ i + i = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    have hsq : (r i : _root_.DihedralGroup n) ^ 2 = 1 := h ▸ pow_orderOf_eq_one _
    rw [sq, r_mul_r, r_eq_one_iff] at hsq
    refine ⟨fun hi => ?_, hsq⟩
    rw [hi, r_zero, orderOf_one] at h
    exact absurd h (by norm_num)
  · rintro ⟨hne, hsum⟩
    refine orderOf_eq_prime ?_ ((r_eq_one_iff i).not.mpr hne)
    rw [sq, r_mul_r, hsum, r_zero]

/-- **involution の分類**: `DihedralGroup n` の位数 2 の元は、すべての鏡映 `sr i` と、
`2i = 0` をみたす非自明な回転 `r i` である。 -/
theorem orderOf_eq_two_iff (g : _root_.DihedralGroup n) :
    orderOf g = 2 ↔ (∃ i, g = sr i) ∨ ∃ i, g = r i ∧ i ≠ 0 ∧ i + i = 0 := by
  cases g with
  | r i =>
    rw [orderOf_r_eq_two_iff]
    constructor
    · exact fun h => Or.inr ⟨i, rfl, h⟩
    · rintro (⟨j, hj⟩ | ⟨j, hj, h⟩)
      · exact absurd hj (by simp)
      · injection hj with hij; exact hij ▸ h
  | sr i => simp

/-! ### 2B.2(a): `n` が奇数のとき -/

/-- `n` が奇数なら `2i = 0` をみたす `i : ZMod n` は `0` のみ (`2` が `ZMod n` の単元)。 -/
theorem eq_zero_of_add_self_eq_zero_of_odd (hn : Odd n) {i : ZMod n} (h : i + i = 0) :
    i = 0 := by
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have h2 : (2 : ZMod n) * i = 0 := by rw [two_mul]; exact h
  have hu : IsUnit (2 : ZMod n) :=
    (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr hn)
  obtain ⟨u, hu⟩ := hu
  rw [← hu] at h2
  simpa using congrArg (fun x => (↑u⁻¹ : ZMod n) * x) h2

/-- **Isaacs Problem 2B.2(a)** (involution の記述). `n` 奇数のとき `DihedralGroup n` の
involution はちょうど鏡映 `sr i` (`i : ZMod n`) 全体。 -/
theorem orderOf_eq_two_iff_of_odd (hn : Odd n) (g : _root_.DihedralGroup n) :
    orderOf g = 2 ↔ ∃ i, g = sr i := by
  rw [orderOf_eq_two_iff]
  refine or_iff_left ?_
  rintro ⟨i, -, hne, hsum⟩
  exact hne (eq_zero_of_add_self_eq_zero_of_odd hn hsum)

/-- **Isaacs Problem 2B.2(a)** (個数). `n` 奇数のとき `DihedralGroup n` の involution は
ちょうど `n` 個。 -/
theorem card_involutions_of_odd (hn : Odd n) :
    Nat.card {g : _root_.DihedralGroup n // orderOf g = 2} = n := by
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have hset : {g : _root_.DihedralGroup n | orderOf g = 2} = Set.range sr := by
    ext g
    simpa [eq_comm] using orderOf_eq_two_iff_of_odd hn g
  calc Nat.card {g : _root_.DihedralGroup n // orderOf g = 2}
      = Nat.card (Set.range (sr : ZMod n → _root_.DihedralGroup n)) := by rw [← hset]; rfl
    _ = Nat.card (ZMod n) :=
        Nat.card_range_of_injective (fun i j h => by injection h)
    _ = n := Nat.card_zmod n

/-- 鏡映どうしの共役: `sr j` で `sr i` を共役すると `sr (2j - i)`。 -/
theorem sr_conj_sr (i j : ZMod n) :
    (sr j : _root_.DihedralGroup n) * sr i * (sr j)⁻¹ = sr (j + j - i) := by
  rw [inv_sr, sr_mul_sr, r_mul_sr]
  ring_nf

/-- 回転による鏡映の共役: `r j` で `sr i` を共役すると `sr (i - 2j)`。 -/
theorem r_conj_sr (i j : ZMod n) :
    (r j : _root_.DihedralGroup n) * sr i * (r j)⁻¹ = sr (i - (j + j)) := by
  rw [inv_r, r_mul_sr, sr_mul_r]
  ring_nf

/-- **Isaacs Problem 2B.2(a)** (共役類). `n` 奇数のとき、すべての involution は
単一の共役類をなす (`2` が `ZMod n` の単元なので `sr i ↦ sr (i - 2j)` が推移的)。 -/
theorem isConj_sr_of_odd (hn : Odd n) (i j : ZMod n) :
    IsConj (sr i : _root_.DihedralGroup n) (sr j) := by
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  -- `2` は単元ゆえ `k + k = i - j` なる `k` が取れる
  obtain ⟨u, hu⟩ : IsUnit (2 : ZMod n) :=
    (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr hn)
  have hkey : (↑u⁻¹ : ZMod n) * (i - j) + (↑u⁻¹ : ZMod n) * (i - j) = i - j := by
    rw [← two_mul, ← mul_assoc, ← hu]
    simp
  rw [isConj_iff]
  refine ⟨r ((↑u⁻¹ : ZMod n) * (i - j)), ?_⟩
  rw [r_conj_sr]
  congr 1
  rw [hkey]
  ring

/-! ### 2B.2(b): `n` が偶数のとき

`n = m + m` (`m ≥ 1`) と書く。回転側の involution は `r m` ちょうど 1 つで、これは中心に入る。
鏡映は `2·ZMod n` の剰余類 (= `i` の「偶奇」) ごとに共役類をなし、ちょうど 2 類・各 `m` 個。 -/

/-- `n = m + m` (偶数, `m ≥ 1`) のとき `2i = 0` の解はちょうど `i = 0` と `i = m` の 2 つ。 -/
theorem add_self_eq_zero_iff_of_even {m : ℕ} (hm : 0 < m) (i : ZMod (m + m)) :
    i + i = 0 ↔ i = 0 ∨ i = (m : ZMod (m + m)) := by
  haveI : NeZero (m + m) := ⟨by omega⟩
  constructor
  · intro h
    have hcast : ((i.val + i.val : ℕ) : ZMod (m + m)) = 0 := by
      rw [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id]
      exact h
    obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hcast
    have hlt : i.val < m + m := ZMod.val_lt i
    have hc2 : c < 2 := by
      by_contra hcc
      push Not at hcc
      have hle : (m + m) * 2 ≤ (m + m) * c := Nat.mul_le_mul_left _ hcc
      rw [← hc] at hle
      omega
    have hcval : i.val = 0 ∨ i.val = m := by interval_cases c <;> omega
    rcases hcval with h0 | hmv
    · exact Or.inl ((ZMod.val_eq_zero i).mp h0)
    · refine Or.inr ?_
      have hstep : ((i.val : ℕ) : ZMod (m + m)) = ((m : ℕ) : ZMod (m + m)) := by rw [hmv]
      rwa [ZMod.natCast_val, ZMod.cast_id] at hstep
  · rintro (rfl | rfl)
    · simp
    · rw [← Nat.cast_add, ZMod.natCast_self]

/-- `n = m + m` (`m ≥ 1`) のとき `(m : ZMod n) ≠ 0` (`0 < m < n` ゆえ `n ∤ m`)。 -/
theorem natCast_half_ne_zero {m : ℕ} (hm : 0 < m) : (m : ZMod (m + m)) ≠ 0 := by
  intro h
  have := Nat.le_of_dvd hm ((ZMod.natCast_eq_zero_iff _ _).mp h)
  omega

/-- **Isaacs Problem 2B.2(b)** (involution の記述). `n = m + m` が偶数のとき、
`DihedralGroup n` の involution は鏡映 `sr i` 全体と、ただ 1 つの回転 `r m`。 -/
theorem orderOf_eq_two_iff_of_even {m : ℕ} (hm : 0 < m)
    (g : _root_.DihedralGroup (m + m)) :
    orderOf g = 2 ↔ (∃ i, g = sr i) ∨ g = r (m : ZMod (m + m)) := by
  rw [orderOf_eq_two_iff]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨i, rfl, hne, hsum⟩
    rcases (add_self_eq_zero_iff_of_even hm i).mp hsum with h | h
    · exact absurd h hne
    · rw [h]
  · rintro rfl
    exact ⟨(m : ZMod (m + m)), rfl, natCast_half_ne_zero hm,
      by rw [← Nat.cast_add, ZMod.natCast_self]⟩

/-- **Isaacs Problem 2B.2(b)** (個数). `n = m + m` が偶数のとき involution はちょうど
`n + 1` 個 (鏡映 `n` 個 + 回転 `r m` 1 個)。 -/
theorem card_involutions_of_even {m : ℕ} (hm : 0 < m) :
    Nat.card {g : _root_.DihedralGroup (m + m) // orderOf g = 2} = m + m + 1 := by
  haveI : NeZero (m + m) := ⟨by omega⟩
  have hset : {g : _root_.DihedralGroup (m + m) | orderOf g = 2}
      = Set.range sr ∪ {r (m : ZMod (m + m))} := by
    ext g
    rw [Set.mem_setOf_eq, orderOf_eq_two_iff_of_even hm g]
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
    exact or_congr (exists_congr fun _ => eq_comm) Iff.rfl
  have hrange : (Set.range (sr : ZMod (m + m) → _root_.DihedralGroup (m + m))).ncard = m + m := by
    rw [Set.ncard_range_of_injective (fun i j h => by injection h), Nat.card_zmod]
  have hdisj : Disjoint (Set.range (sr : ZMod (m + m) → _root_.DihedralGroup (m + m)))
      ({r (m : ZMod (m + m))} : Set (_root_.DihedralGroup (m + m))) := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨i, hi⟩
    exact absurd hi (by simp)
  change ({g : _root_.DihedralGroup (m + m) | orderOf g = 2}).ncard = m + m + 1
  rw [hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hrange,
    Set.ncard_singleton]

/-- `n = m + m` のとき `-m = m` (`2m = 0` ゆえ)。 -/
theorem neg_natCast_half {m : ℕ} : -(m : ZMod (m + m)) = (m : ZMod (m + m)) :=
  neg_eq_of_add_eq_zero_left (by rw [← Nat.cast_add, ZMod.natCast_self])

/-- **Isaacs Problem 2B.2(b)** (中心的 involution). `n = m + m` が偶数のとき、回転側の
involution `r m` は `DihedralGroup n` の中心に属する — したがってその共役類はサイズ 1。 -/
theorem r_natCast_half_mem_center {m : ℕ} :
    (r (m : ZMod (m + m)) : _root_.DihedralGroup (m + m)) ∈ Subgroup.center _ := by
  rw [Subgroup.mem_center_iff]
  intro g
  cases g with
  | r j =>
    rw [r_mul_r, r_mul_r]
    congr 1
    ring
  | sr j =>
    rw [sr_mul_r, r_mul_sr, sub_eq_add_neg, neg_natCast_half]

/-! ### 2B.2(b) の共役類: 鏡映の「偶奇」

`n = m + m` のとき `2·ZMod n` は指数 2 の部分群で、`sr i` の共役類は `i` の属する剰余類で
決まる。剰余類の判定は環準同型 `ZMod n →+* ZMod 2` (`parityHom`) で行う。 -/

/-- `n = m + m` のとき `2 ∣ n` による剰余環準同型 `ZMod n →+* ZMod 2` (添字の「偶奇」)。 -/
def parityHom (m : ℕ) : ZMod (m + m) →+* ZMod 2 :=
  ZMod.castHom ⟨m, by ring⟩ (ZMod 2)

theorem parityHom_apply {m : ℕ} [NeZero m] (i : ZMod (m + m)) :
    parityHom m i = ((i.val : ℕ) : ZMod 2) := by
  haveI : NeZero (m + m) := ⟨by have := NeZero.ne m; omega⟩
  rw [parityHom, ZMod.castHom_apply, ← ZMod.natCast_val]

/-- 「和が 2 で割れる」判定: `parityHom m i = 0 ⟺ i` が二倍元。 -/
theorem parityHom_eq_zero_iff {m : ℕ} [NeZero m] (i : ZMod (m + m)) :
    parityHom m i = 0 ↔ ∃ t : ZMod (m + m), i = t + t := by
  constructor
  · intro h
    rw [parityHom_apply, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨s, hs⟩ := h
    haveI : NeZero (m + m) := ⟨by have := NeZero.ne m; omega⟩
    refine ⟨(s : ZMod (m + m)), ?_⟩
    have : ((i.val : ℕ) : ZMod (m + m)) = ((s : ZMod (m + m)) + (s : ZMod (m + m))) := by
      rw [hs]; push_cast; ring
    rwa [ZMod.natCast_val, ZMod.cast_id] at this
  · rintro ⟨t, rfl⟩
    rw [map_add]
    exact (by decide : ∀ x : ZMod 2, x + x = 0) _

/-- **Isaacs Problem 2B.2(b)** (鏡映の共役条件). `n = m + m` が偶数のとき、鏡映
`sr i` と `sr j` が共役 ⟺ 添字の偶奇が一致 (`j - i` が二倍元)。

`⟸` は `j - i = t + t` として `r (-t)` で共役 (`r_conj_sr`)。`⟹` は共役元が `r` か `sr` かで
場合分けし、`r_conj_sr` / `sr_conj_sr` の像 `i - 2t` / `2t - i` がいずれも `i` と同じ剰余類に
入ること (`parityHom` で計算) から。 -/
theorem isConj_sr_sr_iff_of_even {m : ℕ} [NeZero m] (i j : ZMod (m + m)) :
    IsConj (sr i : _root_.DihedralGroup (m + m)) (sr j) ↔ parityHom m i = parityHom m j := by
  constructor
  · rw [isConj_iff]
    rintro ⟨c, hc⟩
    cases c with
    | r t =>
      rw [r_conj_sr] at hc
      injection hc with hij
      rw [← hij, map_sub, (parityHom_eq_zero_iff _).mpr ⟨t, rfl⟩, sub_zero]
    | sr t =>
      rw [sr_conj_sr] at hc
      injection hc with hij
      rw [← hij, map_sub, (parityHom_eq_zero_iff _).mpr ⟨t, rfl⟩, zero_sub]
      exact (neg_eq_iff_add_eq_zero.mpr
        ((by decide : ∀ x : ZMod 2, x + x = 0) (parityHom m i))).symm
  · intro h
    obtain ⟨t, ht⟩ := (parityHom_eq_zero_iff (j - i)).mp (by rw [map_sub, h, sub_self])
    rw [isConj_iff]
    refine ⟨r (-t), ?_⟩
    rw [r_conj_sr]
    congr 1
    rw [show i - (-t + -t) = i + (t + t) from by ring, ← ht]
    ring

/-- 鏡映の共役元はやはり鏡映 (`r`/`sr` の場合分けで `r_conj_sr` / `sr_conj_sr`)。 -/
theorem exists_sr_of_isConj_sr {i : ZMod n} {g : _root_.DihedralGroup n}
    (h : IsConj (sr i : _root_.DihedralGroup n) g) : ∃ k, g = sr k := by
  rw [isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  cases c with
  | r t => exact ⟨i - (t + t), by rw [← hc, r_conj_sr]⟩
  | sr t => exact ⟨t + t - i, by rw [← hc, sr_conj_sr]⟩

/-- 鏡映は回転と共役でない。 -/
theorem not_isConj_sr_r (i j : ZMod n) :
    ¬ IsConj (sr i : _root_.DihedralGroup n) (r j) := fun h => by
  obtain ⟨k, hk⟩ := exists_sr_of_isConj_sr h
  exact absurd hk (by simp)

/-- **Isaacs Problem 2B.2(b)** (`r m` の共役類). `r m` は中心的ゆえ共役類は `{r m}`。 -/
theorem conjClass_r_natCast_half_eq {m : ℕ} :
    {g : _root_.DihedralGroup (m + m) | IsConj (r (m : ZMod (m + m))) g}
      = {r (m : ZMod (m + m))} := by
  ext g
  rw [Set.mem_setOf_eq, Set.mem_singleton_iff, isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subgroup.mem_center_iff.mp r_natCast_half_mem_center c]
    group
  · rintro rfl
    exact ⟨1, by group⟩

/-- 偶奇の fiber `{k | parityHom m k = c}` はどちらも `m` 個 (`k ↦ k + 1` が 2 つの fiber の
間の全単射、かつ 2 つで `ZMod (m+m)` を分割する)。 -/
theorem ncard_parityHom_fiber {m : ℕ} [NeZero m] (c : ZMod 2) :
    {k : ZMod (m + m) | parityHom m k = c}.ncard = m := by
  haveI : NeZero (m + m) := ⟨by have := NeZero.ne m; omega⟩
  -- fiber 1 は fiber 0 の `(· + 1)` 像
  have himg : {k : ZMod (m + m) | parityHom m k = 1}
      = (fun x => x + 1) '' {k : ZMod (m + m) | parityHom m k = 0} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · exact fun h => ⟨k - 1, by rw [map_sub, h, map_one, sub_self], by ring⟩
    · rintro ⟨x, hx, rfl⟩
      rw [map_add, hx, map_one, zero_add]
  have heq : {k : ZMod (m + m) | parityHom m k = 1}.ncard
      = {k : ZMod (m + m) | parityHom m k = 0}.ncard := by
    rw [himg, Set.ncard_image_of_injective _ (add_left_injective 1)]
  -- 2 つの fiber は互いに補集合
  have hcompl : {k : ZMod (m + m) | parityHom m k = 0}ᶜ
      = {k : ZMod (m + m) | parityHom m k = 1} := by
    ext k
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (parityHom m k) with h0 | h1
      · exact absurd h0 h
      · exact h1
    · intro h hc
      rw [hc] at h
      exact absurd h (by decide)
  have hsum := Set.ncard_add_ncard_compl {k : ZMod (m + m) | parityHom m k = 0}
  rw [hcompl, heq, Nat.card_zmod] at hsum
  have hzero : {k : ZMod (m + m) | parityHom m k = 0}.ncard = m := by omega
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with rfl | rfl
  · exact hzero
  · rw [heq, hzero]

/-- **Isaacs Problem 2B.2(b)** (鏡映の共役類). `sr i` の共役類は「偶奇が `i` と等しい」
鏡映全体で、サイズは `n/2 = m`。 -/
theorem conjClass_sr_eq {m : ℕ} [NeZero m] (i : ZMod (m + m)) :
    {g : _root_.DihedralGroup (m + m) | IsConj (sr i) g}
      = sr '' {k : ZMod (m + m) | parityHom m k = parityHom m i} := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := exists_sr_of_isConj_sr h
    exact ⟨k, ((isConj_sr_sr_iff_of_even i k).mp h).symm, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact (isConj_sr_sr_iff_of_even i k).mpr hk.symm

theorem ncard_conjClass_sr {m : ℕ} [NeZero m] (i : ZMod (m + m)) :
    {g : _root_.DihedralGroup (m + m) | IsConj (sr i) g}.ncard = m := by
  rw [conjClass_sr_eq, Set.ncard_image_of_injective _ (fun a b h => by injection h),
    ncard_parityHom_fiber]

/-- **Isaacs Problem 2B.2(b)** (共役類はちょうど 3 つ). `n = m + m` が偶数のとき involution は
3 つの共役類に分かれ、それらは互いに非共役: `sr 0` の類 (サイズ `m`)、`sr 1` の類
(サイズ `m`)、`r m` の類 (サイズ 1)。 -/
theorem not_isConj_sr_zero_sr_one {m : ℕ} [NeZero m] :
    ¬ IsConj (sr 0 : _root_.DihedralGroup (m + m)) (sr 1) := by
  rw [isConj_sr_sr_iff_of_even, map_zero, map_one]
  exact fun h => absurd h.symm (by decide)

end

end DihedralGroup

section /- Problem 2B.3: 非共役な involution から可換な第 3 の involution (p. 57) -/

variable {G : Type*} [Group G]

/-- involution `s` は `s * t` を反転する。 -/
private theorem conj_mul_eq_inv_left {s t : G} (hs : s * s = 1) (ht : t * t = 1) :
    s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_left hs, inv_eq_of_mul_eq_one_left ht]
  calc s * (s * t) * s = s * s * (t * s) := by group
    _ = t * s := by rw [hs, one_mul]

/-- involution `t` も `s * t` を反転する。 -/
private theorem conj_mul_eq_inv_right {s t : G} (hs : s * s = 1) (ht : t * t = 1) :
    t * (s * t) * t⁻¹ = (s * t)⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_left hs, inv_eq_of_mul_eq_one_left ht]
  calc t * (s * t) * t = (t * s) * (t * t) := by group
    _ = t * s := by rw [ht, mul_one]

/-- `u` を反転する元は `u` の冪も反転する (共役写像が群準同型であることの `map_pow`)。 -/
private theorem conj_pow_eq_inv {x u : G} (h : x * u * x⁻¹ = u⁻¹) (j : ℕ) :
    x * u ^ j * x⁻¹ = (u ^ j)⁻¹ := by
  have hmap : (MulAut.conj x) (u ^ j) = ((MulAut.conj x) u) ^ j := map_pow _ _ _
  simpa [MulAut.conj_apply, h, inv_pow] using hmap

/-- **Isaacs Problem 2B.3**. `s`, `t` を有限群 `G` の involution とし、`G` で共役でないとする。
このとき `s`, `t` と異なる involution `z ∈ G` で `s`, `t` の両方と可換なものが存在する。

証明: `u := s * t` とおくと `s`, `t` はいずれも `u` を反転する (`s u s⁻¹ = u⁻¹`)。
`n := |u|` が**奇数**なら `K := (n+1)/2` として `u^K` による共役が
`s ↦ u^{K+K} s = u^{n+1} s = u s = s t s⁻¹` を与え、`s ~ sts⁻¹ ~ t` で共役になってしまう —
ゆえに `n` は偶数。`n = 2q` として `z := u^q` が求めるもの: `z² = u^n = 1`、`z ≠ 1`
(`0 < q < n`)、`s z s⁻¹ = z⁻¹ = z` で可換。`z = s` なら `z = u^q` は `u` と可換なので
`u = s u s⁻¹ = u⁻¹`, ゆえに `n ∣ 2`, `q = 1`, `z = u = st = s` から `t = 1` で矛盾
(`z = t` も同様に `s = 1`)。

⚠ 有限性は本質的: 無限二面体群 `D∞` は反例 (中心が自明で、`s` と可換な involution は `s` のみ)。 -/
theorem exists_involution_commuting_of_not_isConj [Finite G] {s t : G}
    (hs : orderOf s = 2) (ht : orderOf t = 2) (hnc : ¬ IsConj s t) :
    ∃ z : G, orderOf z = 2 ∧ z ≠ s ∧ z ≠ t ∧ Commute z s ∧ Commute z t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : s * s = 1 := by rw [← sq]; exact hs ▸ pow_orderOf_eq_one s
  have ht2 : t * t = 1 := by rw [← sq]; exact ht ▸ pow_orderOf_eq_one t
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs; omega
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
  set u : G := s * t with hudef
  have hsu : s * u * s⁻¹ = u⁻¹ := conj_mul_eq_inv_left hs2 ht2
  have htu : t * u * t⁻¹ = u⁻¹ := conj_mul_eq_inv_right hs2 ht2
  have hnpos : 0 < orderOf u := orderOf_pos u
  -- `|u|` は偶数 (奇数だと `s ~ t` になる)
  have heven : 2 ∣ orderOf u := by
    by_contra hodd
    apply hnc
    have hmod : orderOf u % 2 = 1 := Nat.two_dvd_ne_zero.mp hodd
    set K := (orderOf u + 1) / 2 with hKdef
    have hKK : K + K = orderOf u + 1 := by omega
    have hconj : s * u ^ K * s⁻¹ = (u ^ K)⁻¹ := conj_pow_eq_inv hsu K
    have hconj' : s * (u ^ K)⁻¹ * s⁻¹ = u ^ K := by
      rw [show s * (u ^ K)⁻¹ * s⁻¹ = (s * u ^ K * s⁻¹)⁻¹ from by group, hconj, inv_inv]
    have hmove : s * (u ^ K)⁻¹ = u ^ K * s := mul_inv_eq_iff_eq_mul.mp hconj'
    have hkey : u ^ K * s * (u ^ K)⁻¹ = u * s := by
      rw [mul_assoc, hmove, ← mul_assoc, ← pow_add, hKK, pow_succ, pow_orderOf_eq_one, one_mul]
    refine (isConj_iff.mpr ⟨u ^ K, hkey⟩).trans (isConj_iff.mpr ⟨s, ?_⟩).symm
    rw [inv_eq_of_mul_eq_one_left hs2, hudef]
  obtain ⟨q, hq⟩ := heven
  have hqpos : 0 < q := by omega
  have hzsq : u ^ q * u ^ q = 1 := by
    rw [← pow_add, show q + q = orderOf u from by omega, pow_orderOf_eq_one]
  have hzne : u ^ q ≠ 1 := fun h => by
    have := Nat.le_of_dvd hqpos (orderOf_dvd_of_pow_eq_one h)
    omega
  have hzinv : (u ^ q)⁻¹ = u ^ q := inv_eq_of_mul_eq_one_left hzsq
  -- `z = u^q` が `s`, `t` と可換
  have hcomm : ∀ x : G, x * u * x⁻¹ = u⁻¹ → Commute (u ^ q) x := fun x hx => by
    have h := conj_pow_eq_inv hx q
    rw [hzinv] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  -- `z = s` や `z = t` は `u² = 1` を強制し `s = 1` / `t = 1` に至る
  have hforce : ∀ x : G, x * u * x⁻¹ = u⁻¹ → u ^ q = x → q = 1 := fun x hx hxq => by
    have hxu : x * u = u * x := by rw [← hxq]; exact ((Commute.refl u).pow_left q).eq
    have hinv : u = u⁻¹ := by rw [← hx, hxu, mul_assoc, mul_inv_cancel, mul_one]
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [sq]; exact mul_eq_one_iff_eq_inv.mpr hinv)
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  refine ⟨u ^ q, orderOf_eq_prime (by rw [sq]; exact hzsq) hzne, ?_, ?_, hcomm s hsu, hcomm t htu⟩
  · intro h
    have hq1 : q = 1 := hforce s hsu h
    rw [hq1, pow_one, hudef] at h
    exact ht1 (by simpa using h)
  · intro h
    have hq1 : q = 1 := hforce t htu h
    rw [hq1, pow_one, hudef] at h
    exact hs1 (by simpa using h)

end

section /- Problem 2B.4: TI Sylow 2-部分群と involution の共役類 (p. 57) -/

variable {G : Type*} [Group G]

/-- involution はある Sylow 2-部分群に属する (`⟨s⟩` は位数 2 の 2-群)。 -/
theorem exists_sylow_two_mem [Finite G] {s : G} (hs : orderOf s = 2) :
    ∃ P : Sylow 2 G, s ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  exact ⟨P, hP (Subgroup.mem_zpowers s)⟩

/-- **可換な 2 つの involution は共通の Sylow 2-部分群に属する**: `⟨s, z⟩` は生成元が可換ゆえ
可換群で、生成元の 2 乗が `1` だから全元の 2 乗も `1` — すなわち 2-群。 -/
theorem exists_sylow_two_mem_of_commute [Finite G] {s z : G}
    (hs : orderOf s = 2) (hz : orderOf z = 2) (hcz : Commute s z) :
    ∃ P : Sylow 2 G, s ∈ P ∧ z ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : s * s = 1 := by rw [← sq]; exact hs ▸ pow_orderOf_eq_one s
  have hz2 : z * z = 1 := by rw [← sq]; exact hz ▸ pow_orderOf_eq_one z
  set k : Set G := {s, z} with hkdef
  -- `k` の元は互いに可換 ⟹ `closure k` の元も互いに可換
  have hkc : k ⊆ (Subgroup.centralizer k : Set G) := by
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hx with rfl | rfl <;> rcases hh with rfl | rfl
    exacts [rfl, hcz.symm.eq, hcz.eq, rfl]
  have h1 : Subgroup.closure k ≤ Subgroup.centralizer k := (Subgroup.closure_le _).mpr hkc
  have h2 := Subgroup.closure_le_centralizer_centralizer k
  have hcomm : ∀ x ∈ Subgroup.closure k, ∀ y ∈ Subgroup.closure k, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (h2 hx) y (h1 hy)).symm
  -- 全元が 2 乗して `1`
  have hsq : ∀ g ∈ Subgroup.closure k, g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl; exacts [hs2, hz2]
    | one => rw [mul_one]
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hcomm y hy x hx]
        _ = x * x * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x _ ih => rw [inv_eq_of_mul_eq_one_left ih]; exact ih
  have hpg : IsPGroup 2 (Subgroup.closure k) := fun g => ⟨1, by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, sq]
    exact hsq (g : G) g.2⟩
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  exact ⟨P, hP (Subgroup.subset_closure (by simp [hkdef])),
    hP (Subgroup.subset_closure (by simp [hkdef]))⟩

/-- Sylow 2-部分群が互いに自明交叉 (TI) なら、involution を含む Sylow 2-部分群は一意。 -/
theorem sylow_two_eq_of_ti [Finite G]
    (hti : ∀ P Q : Sylow 2 G, P ≠ Q → (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥)
    {s : G} (hs : orderOf s = 2) {P Q : Sylow 2 G} (hP : s ∈ P) (hQ : s ∈ Q) : P = Q := by
  by_contra hne
  have hmem : s ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) := ⟨hP, hQ⟩
  rw [hti P Q hne, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hs
  omega

/-- 相異なる Sylow 2-部分群に属する involution は共役 (2B.4 の核)。

対偶: 共役でなければ 2B.3 で両方と可換な involution `z` が取れ、`⟨s, z⟩` と `⟨t, z⟩` は
それぞれ Sylow 2-部分群 `R`, `S` に入る。`z ≠ 1` が両方に属すので TI 仮定で `R = S`、
さらに一意性で `P = R = S = Q` となって仮定に反する。 -/
theorem isConj_of_sylow_two_ne [Finite G]
    (hti : ∀ P Q : Sylow 2 G, P ≠ Q → (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥)
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) {P Q : Sylow 2 G}
    (haP : a ∈ P) (hbQ : b ∈ Q) (hPQ : P ≠ Q) : IsConj a b := by
  by_contra hnc
  obtain ⟨z, hz, -, -, hca, hcb⟩ := exists_involution_commuting_of_not_isConj ha hb hnc
  obtain ⟨R, haR, hzR⟩ := exists_sylow_two_mem_of_commute ha hz hca.symm
  obtain ⟨S, hbS, hzS⟩ := exists_sylow_two_mem_of_commute hb hz hcb.symm
  exact hPQ ((sylow_two_eq_of_ti hti ha haP haR).trans
    ((sylow_two_eq_of_ti hti hz hzR hzS).trans (sylow_two_eq_of_ti hti hb hbS hbQ)))

/-- **Isaacs Problem 2B.4**. `G` が 2 つ以上の Sylow 2-部分群をもち、相異なる Sylow 2-部分群が
自明にしか交わらない (TI) ならば、`G` の involution は**ちょうど 1 つの共役類**をなす。

`isConj_of_sylow_two_ne` で「相異なる Sylow 2-部分群の involution は共役」。同じ Sylow
`P` に属する `s, t` については、`P` と異なる Sylow `Q` を取り (Sylow 2-部分群は 2 つ以上)、
Sylow の共役性 `Q = g • P` から `Q` 内の involution `g s g⁻¹` を作って経由すればよい。 -/
theorem isConj_of_orderOf_eq_two_of_sylow_ti [Finite G]
    (hmany : ∃ P Q : Sylow 2 G, P ≠ Q)
    (hti : ∀ P Q : Sylow 2 G, P ≠ Q → (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥)
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2) : IsConj s t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Ps, hsP⟩ := exists_sylow_two_mem hs
  obtain ⟨Pt, htP⟩ := exists_sylow_two_mem ht
  by_cases hPQ : Ps = Pt
  · -- 同じ Sylow に属する場合: 別の Sylow の involution を経由する
    obtain ⟨P₁, P₂, hne⟩ := hmany
    obtain ⟨Q, hQne⟩ : ∃ Q : Sylow 2 G, Q ≠ Ps := by
      by_cases h : P₁ = Ps
      · exact ⟨P₂, fun hc => hne (h.trans hc.symm)⟩
      · exact ⟨P₁, h⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Ps Q
    have hu : orderOf (g * s * g⁻¹) = 2 := by
      rw [← hs]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
    have huQ : g * s * g⁻¹ ∈ (Q : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul s (MulAut.conj g) _ hsP
    exact (isConj_iff.mpr ⟨g, rfl⟩).trans
      (isConj_of_sylow_two_ne hti ht hu htP huQ (hPQ ▸ fun hc => hQne hc.symm)).symm
  · exact isConj_of_sylow_two_ne hti hs ht hsP htP hPQ

/-- **Isaacs Problem 2B.4** (共役類が空でないこと). Sylow 2-部分群が 2 つ以上あれば involution は
実在する — したがって 2B.4 の結論は「ちょうど 1 つの共役類」であって空ではない。

`P ≠ Q` なら少なくとも一方の Sylow 2-部分群は `⊥` でなく、非自明な 2-群には Cauchy で
位数 2 の元がある。 -/
theorem exists_orderOf_eq_two_of_exists_sylow_two_ne [Finite G]
    (hmany : ∃ P Q : Sylow 2 G, P ≠ Q) : ∃ s : G, orderOf s = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₁, P₂, hne⟩ := hmany
  obtain ⟨P, hP⟩ : ∃ P : Sylow 2 G, (P : Subgroup G) ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hne (Sylow.ext ((h P₁).trans (h P₂).symm))
  haveI : Nontrivial ↥(P : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hP
  obtain ⟨n, hn⟩ := P.2.exists_card_eq
  have hcard1 : 1 < Nat.card ↥(P : Subgroup G) := Finite.one_lt_card
  have hdvd : 2 ∣ Nat.card ↥(P : Subgroup G) := by
    rw [hn] at hcard1 ⊢
    rcases n with _ | n
    · simp at hcard1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P : Subgroup G)) 2 hdvd
  exact ⟨(x : G), (Subgroup.orderOf_coe x).trans hx⟩

end

section /- Problem 2B.5: generalized dihedral (指数 2 の部分群) (p. 57) -/

variable {G : Type*} [Group G] {B : Subgroup G}

/-- 指数 2 の部分群の外にある 2 元は同じ剰余類に属する。 -/
theorem inv_mul_mem_of_notMem_of_index_eq_two (hB : B.index = 2) {x y : G}
    (hx : x ∉ B) (hy : y ∉ B) : x⁻¹ * y ∈ B := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp hB
  have hax : a * x ∈ B := by rcases ha x with ⟨h, -⟩ | ⟨h, -⟩; exacts [h, absurd h hx]
  have hay : a * y ∈ B := by rcases ha y with ⟨h, -⟩ | ⟨h, -⟩; exacts [h, absurd h hy]
  have := B.mul_mem (B.inv_mem hax) hay
  simpa [mul_assoc] using this

/-- 部分群の元と外の元の積は外にある。 -/
theorem mul_notMem_of_mem_of_notMem {b t : G} (hb : b ∈ B) (ht : t ∉ B) : b * t ∉ B :=
  fun h => ht (by simpa using B.mul_mem (B.inv_mem hb) h)

/-- 指数 2 の部分群は真部分群ゆえ外に元がある。 -/
theorem exists_notMem_of_index_eq_two (hB : B.index = 2) : ∃ t : G, t ∉ B := by
  by_contra hcon
  push Not at hcon
  have hBtop : B = ⊤ := le_antisymm le_top fun x _ => hcon x
  rw [hBtop, Subgroup.index_top] at hB
  omega

/-- **Isaacs Problem 2B.5**. `B ≤ G` を指数 2 の部分群とすると、次は同値:
1. `G ∖ B` に involution `t` があって全ての `b ∈ B` を反転する (`b^t = b⁻¹`)。
2. `G ∖ B` は involution だけからなる。
3. `G ∖ B` の全ての元 `t` は involution であり、全ての `b ∈ B` を反転する。

(この状況で `G` は **generalized dihedral** と呼ばれる。)

`t` は involution なので `t⁻¹ = t`、したがって Isaacs の `b^t = t⁻¹ b t` と
ここでの `t * b * t⁻¹` は一致する。

- (1) ⟹ (2): `x ∉ B` は `x = t * b` (`b := t⁻¹ * x ∈ B`) と書け、反転則から
  `x² = (t b)(t b) = (b⁻¹ t)(t b) = b⁻¹ b = 1`、かつ `x ≠ 1` (`1 ∈ B`)。
- (2) ⟹ (3): `b ∈ B`, `t ∉ B` なら `b * t ∉ B` も involution ゆえ `b t b t = 1`、
  すなわち `t b t = b⁻¹`。
- (3) ⟹ (1): 指数 2 ゆえ `G ∖ B` は空でない。 -/
theorem generalizedDihedral_tfae (hB : B.index = 2) :
    List.TFAE
      [∃ t : G, t ∉ B ∧ orderOf t = 2 ∧ ∀ b ∈ B, t * b * t⁻¹ = b⁻¹,
        ∀ t : G, t ∉ B → orderOf t = 2,
        ∀ t : G, t ∉ B → orderOf t = 2 ∧ ∀ b ∈ B, t * b * t⁻¹ = b⁻¹] := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  tfae_have 1 → 2 := by
    rintro ⟨t, htB, ht2, htinv⟩ x hx
    have htt : t * t = 1 := by rw [← sq]; exact ht2 ▸ pow_orderOf_eq_one t
    have hbmem : t⁻¹ * x ∈ B := inv_mul_mem_of_notMem_of_index_eq_two hB (by simpa using htB) hx
    have hxeq : x = t * (t⁻¹ * x) := by group
    refine orderOf_eq_prime ?_ (fun h => hx (h ▸ B.one_mem))
    rw [sq]
    nth_rewrite 1 [hxeq]
    nth_rewrite 2 [hxeq]
    have hinv := htinv _ hbmem
    calc t * (t⁻¹ * x) * (t * (t⁻¹ * x))
        = (t * (t⁻¹ * x) * t⁻¹) * (t * t) * (t⁻¹ * x) := by group
      _ = (t⁻¹ * x)⁻¹ * (t * t) * (t⁻¹ * x) := by rw [hinv]
      _ = 1 := by rw [htt, mul_one, inv_mul_cancel]
  tfae_have 2 → 3 := by
    intro h t htB
    refine ⟨h t htB, fun b hb => ?_⟩
    have htt : t * t = 1 := by rw [← sq]; exact (h t htB) ▸ pow_orderOf_eq_one t
    have hbt := mul_notMem_of_mem_of_notMem hb htB
    have hbt2 : b * t * (b * t) = 1 := by
      rw [← sq]; exact (h _ hbt) ▸ pow_orderOf_eq_one _
    rw [inv_eq_of_mul_eq_one_left htt]
    calc t * b * t = b⁻¹ * (b * t * (b * t)) := by group
      _ = b⁻¹ := by rw [hbt2, mul_one]
  tfae_have 3 → 1 := by
    intro h
    obtain ⟨t, ht⟩ := exists_notMem_of_index_eq_two hB
    exact ⟨t, ht, (h t ht).1, (h t ht).2⟩
  tfae_finish

/-- **Isaacs Problem 2B.5** (最後の主張). generalized dihedral のとき `B` は可換。

`t ∉ B` を取ると `t (bc) t⁻¹ = (bc)⁻¹ = c⁻¹b⁻¹` と
`t (bc) t⁻¹ = (t b t⁻¹)(t c t⁻¹) = b⁻¹c⁻¹` から `b⁻¹c⁻¹ = c⁻¹b⁻¹`、逆元をとって `bc = cb`。 -/
theorem isMulCommutative_of_generalizedDihedral (hB : B.index = 2)
    (h : ∀ t : G, t ∉ B → orderOf t = 2) : IsMulCommutative B := by
  obtain ⟨t, ht⟩ := exists_notMem_of_index_eq_two hB
  have h23 : (∀ t : G, t ∉ B → orderOf t = 2) →
      ∀ t : G, t ∉ B → orderOf t = 2 ∧ ∀ b ∈ B, t * b * t⁻¹ = b⁻¹ :=
    ((generalizedDihedral_tfae hB).out 1 2).mp
  have hinv : ∀ b ∈ B, t * b * t⁻¹ = b⁻¹ := (h23 h t ht).2
  refine ⟨⟨fun b c => Subtype.ext ?_⟩⟩
  have hbc : t * ((b : G) * c) * t⁻¹ = ((b : G) * c)⁻¹ := hinv _ (B.mul_mem b.2 c.2)
  rw [show t * ((b : G) * c) * t⁻¹ = (t * (b : G) * t⁻¹) * (t * (c : G) * t⁻¹) from by group,
    hinv _ b.2, hinv _ c.2, mul_inv_rev] at hbc
  push_cast
  exact inv_injective (by rw [mul_inv_rev, mul_inv_rev]; exact hbc.symm)

end

section /- Problem 2B.6: 正規 Sylow p-部分群の局所判定 (p. 58) -/

open OddOrder.Isaacs.Ch01

variable {G : Type*} [Group G] {p : ℕ}

/-- 正規 Sylow `p`-部分群は `O_p(G)` に一致する。 -/
theorem coe_eq_opCore_of_normal [Finite G] [Fact p.Prime] (P : Sylow p G)
    (hP : (P : Subgroup G).Normal) : (P : Subgroup G) = opCore p G := by
  haveI := hP
  exact le_antisymm (normal_pgroup_le_opCore P.2) (opCore_le P)

/-- `p`-冪位数の元で生成される有限群が正規 Sylow `p`-部分群をもつ ⟺ それ自身が `p`-群。

`⟸` は `⊤` を含む Sylow が `⊤` に一致するから。`⟹` は正規 Sylow が一意
(`Sylow.unique_of_normal`) ゆえ各生成元の `⟨x⟩` がそこに含まれ、生成で `⊤` に一致する。 -/
theorem exists_normal_sylow_iff_isPGroup {K : Type*} [Group K] [Finite K] [Fact p.Prime]
    {S : Set K} (hS : ∀ x ∈ S, ∃ n : ℕ, orderOf x = p ^ n) (hgen : Subgroup.closure S = ⊤) :
    (∃ Q : Sylow p K, (Q : Subgroup K).Normal) ↔ IsPGroup p K := by
  constructor
  · rintro ⟨Q, hQ⟩
    letI := Q.unique_of_normal hQ
    have htop : (Q : Subgroup K) = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hgen, Subgroup.closure_le]
      intro x hx
      obtain ⟨n, hn⟩ := hS x hx
      have hpg : IsPGroup p ↥(Subgroup.zpowers x) :=
        IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
      obtain ⟨Q', hQ'⟩ := hpg.exists_le_sylow
      exact (Subsingleton.elim Q' Q) ▸ hQ' (Subgroup.mem_zpowers x)
    intro g
    obtain ⟨n, hn⟩ := Q.2 (⟨g, htop.ge (Subgroup.mem_top g)⟩ : ↥(Q : Subgroup K))
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  · intro hK
    obtain ⟨Q, hQ⟩ := (hK.to_subgroup ⊤).exists_le_sylow
    exact ⟨Q, by rw [top_le_iff.mp hQ]; infer_instance⟩

/-- **Isaacs Problem 2B.6** (p. 58). 有限群 `G` が正規 Sylow `p`-部分群をもつ ⟺
`p`-冪位数の共役元 `x`, `y = x^g` の生成する部分群 `⟨x, y⟩` がすべて正規 Sylow `p`-部分群をもつ。

`⟨x, x^g⟩` は `p`-冪位数の元で生成されるので、前補題より「正規 Sylow をもつ」と「`p`-群である」
は同値。したがって右辺は **Baer-Suzuki** (Thm 2.15, `baerSuzuki_pCore`:
`x ∈ O_p(G) ↔ ∀ g, ⟨x, x^g⟩` が `p`-群) の右辺そのもの。

- `⟸`: 全ての `p`-冪位数の元が `O_p(G)` に入る ⟹ Sylow `P ≤ O_p(G)`、逆は `opCore_le` ゆえ
  `P = O_p(G)` は正規。
- `⟹`: 正規 Sylow `P` は `O_p(G)` に一致し (`coe_eq_opCore_of_normal`)、`p`-元は一意な Sylow
  `P` に入るので `x ∈ O_p(G)`、Baer-Suzuki の順方向で `⟨x, x^g⟩` は `p`-群。 -/
theorem exists_normal_sylow_iff_forall_conj_pair [Finite G] [Fact p.Prime] :
    (∃ P : Sylow p G, (P : Subgroup G).Normal) ↔
      ∀ x g : G, (∃ n : ℕ, orderOf x = p ^ n) →
        ∃ Q : Sylow p ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G)),
          (Q : Subgroup ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G))).Normal := by
  have bridge : ∀ x g : G, (∃ n : ℕ, orderOf x = p ^ n) →
      ((∃ Q : Sylow p ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G)),
          (Q : Subgroup ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G))).Normal)
        ↔ IsPGroup p ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G))) := by
    intro x g hx
    set H : Subgroup G := Subgroup.closure ({x, g * x * g⁻¹} : Set G) with hH
    have hxH : x ∈ H := Subgroup.subset_closure (by simp)
    have hyH : g * x * g⁻¹ ∈ H := Subgroup.subset_closure (by simp)
    refine exists_normal_sylow_iff_isPGroup
      (S := {(⟨x, hxH⟩ : ↥H), (⟨g * x * g⁻¹, hyH⟩ : ↥H)}) ?_ ?_
    · obtain ⟨n, hn⟩ := hx
      rintro z (rfl | rfl)
      · exact ⟨n, (Subgroup.orderOf_coe _).symm.trans hn⟩
      · refine ⟨n, (Subgroup.orderOf_coe _).symm.trans ?_⟩
        rw [← hn]
        exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    · apply Subgroup.map_injective H.subtype_injective
      rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        Set.image_insert_eq, Set.image_singleton]
      exact hH.symm
  constructor
  · rintro ⟨P, hP⟩ x g hx
    refine (bridge x g hx).mpr ?_
    have hxP : x ∈ (P : Subgroup G) := by
      obtain ⟨n, hn⟩ := hx
      have hpg : IsPGroup p ↥(Subgroup.zpowers x) :=
        IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
      obtain ⟨P', hP'⟩ := hpg.exists_le_sylow
      letI := P.unique_of_normal hP
      exact (Subsingleton.elim P' P) ▸ hP' (Subgroup.mem_zpowers x)
    refine (baerSuzuki_pCore x).mp ?_ g
    rw [← coe_eq_opCore_of_normal P hP]
    exact hxP
  · intro h
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    have hPle : (P : Subgroup G) ≤ opCore p G := by
      intro y hy
      have hy' : ∃ n : ℕ, orderOf y = p ^ n := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp P.2 (⟨y, hy⟩ : ↥(P : Subgroup G))
        exact ⟨n, (Subgroup.orderOf_coe _).trans hn⟩
      exact (baerSuzuki_pCore y).mpr fun g => (bridge y g hy').mp (h y g hy')
    exact ⟨P, by rw [le_antisymm hPle (opCore_le P)]; infer_instance⟩

end

end OddOrder.Isaacs.Ch02
