/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import OddOrder.Isaacs.Ch02_Subnormality.Basic

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

end OddOrder.Isaacs.Ch02
