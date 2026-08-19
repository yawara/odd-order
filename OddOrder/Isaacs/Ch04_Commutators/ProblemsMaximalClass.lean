/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.ProblemsFrobeniusFrattini
import OddOrder.Isaacs.Ch04_Commutators.Problems

/-!
# Isaacs Chapter 4 — Problem 4A.6 (maximal class の `p`-群)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4A.6 (書籍 p. 124)。

`P` が **maximal class** (`|P| = p^n` で冪零類が `n - 1`) の `p`-群で `N ⊴ P`,
`|P : N| ≥ p²` なら, `N` は下降中心列の項の 1 つであり, 特に位数 `|N|` の正規部分群は
`N` ただ 1 つ。

構成:

* `p`-群の下降中心列は類の下で真に減少し, 各段で位数が `p` 倍以上 (`card_lowerCentralSeries_*`)
* `P / P'` が巡回なら `P` は可換 (`isCyclic_of_frattiniQuotient_isCyclic` 経由) ⟹
  非可換 `p`-群では `p² ∣ |P : P'|`
* この 2 つで maximal class なら `|L_i| = p^{n - 1 - i}` (`i ≥ 1`) が確定する
  (`card_lowerCentralSeries_of_maximalClass`)
* `|G| = p^k` (`k ≥ 2`) の `p`-群は類 `≤ k - 1` (`nilpotencyClass_le_of_card_eq_pow`) なので
  `L_{k-1}(P) ≤ N`, 位数を比べて `N = L_{k-1}(P)`

⚠ mathlib の添字は古典的な `γ_i` から 1 ずれる (`lowerCentralSeries ⊤ 0 = P`,
`lowerCentralSeries ⊤ 1 = P'`): 古典的 `γ_k` = `lowerCentralSeries ⊤ (k - 1)`。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

universe u

section /- Problem 4A.6: maximal class p-groups (p. 124) -/

variable {p : ℕ} {P : Type u} [Group P]

/-! ### `p`-群の下降中心列の位数 -/

/-- 真の部分群では位数が `p` 倍以上違う (`p`-群). -/
theorem prime_mul_card_dvd_card_of_lt [Finite P] [Fact p.Prime] (hP : IsPGroup p P)
    {H K : Subgroup P} (hlt : H < K) : p * Nat.card H ∣ Nat.card K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hlt.le
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p) (G := K)).mp (hP.to_subgroup K)
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact (ne_of_lt hlt) (Subgroup.eq_of_le_of_card_ge hlt.le (le_of_eq hm))
  have hmdvd : m ∣ p ^ a := ⟨Nat.card H, by rw [← ha, hm]; ring⟩
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hmdvd
  have hb0 : b ≠ 0 := by rintro rfl; exact hm1 (by simpa using hb)
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  exact ⟨p ^ b', by rw [hm, hb]; ring⟩

/-- 下降中心列は冪零類の下では真に減少する. -/
theorem lowerCentralSeries_lt_of_lt_nilpotencyClass [Group.IsNilpotent P] {i : ℕ}
    (hi : i < Group.nilpotencyClass P) :
    Subgroup.lowerCentralSeries (⊤ : Subgroup P) (i + 1)
      < Subgroup.lowerCentralSeries (⊤ : Subgroup P) i := by
  refine lt_of_le_of_ne (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup P) (Nat.le_succ i))
    fun heq => ?_
  -- `L_{i+1} = L_i` なら以降ずっと同じで `L_i = ⊥`, ゆえに類 `≤ i`
  have hstab : ∀ j, Subgroup.lowerCentralSeries (⊤ : Subgroup P) (i + j)
      = Subgroup.lowerCentralSeries (⊤ : Subgroup P) i := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have : i + (j + 1) = (i + j) + 1 := by ring
      rw [this, Subgroup.lowerCentralSeries_succ, ih, ← Subgroup.lowerCentralSeries_succ, heq]
  have hbot : Subgroup.lowerCentralSeries (⊤ : Subgroup P) i = ⊥ := by
    rw [← hstab (Group.nilpotencyClass P)]
    have hle : Group.nilpotencyClass P ≤ i + Group.nilpotencyClass P := Nat.le_add_left _ _
    exact le_antisymm (le_trans (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup P) hle)
      (le_of_eq Subgroup.lowerCentralSeries_nilpotencyClass)) bot_le
  exact absurd (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot) (by omega)

/-- **下方評価**: `p ^ j ∣ |L_{c - j}|` (`c` = 冪零類, `j ≤ c`). -/
theorem prime_pow_dvd_card_lowerCentralSeries [Finite P] [Fact p.Prime] (hP : IsPGroup p P)
    [Group.IsNilpotent P] {j : ℕ} (hj : j ≤ Group.nilpotencyClass P) :
    p ^ j ∣ Nat.card (Subgroup.lowerCentralSeries (⊤ : Subgroup P)
      (Group.nilpotencyClass P - j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjc : j ≤ Group.nilpotencyClass P := by omega
    have hidx : Group.nilpotencyClass P - j = (Group.nilpotencyClass P - (j + 1)) + 1 := by omega
    have hlt := lowerCentralSeries_lt_of_lt_nilpotencyClass (P := P)
      (i := Group.nilpotencyClass P - (j + 1)) (by omega)
    have hdvd := prime_mul_card_dvd_card_of_lt hP hlt
    rw [← hidx] at hdvd
    calc p ^ (j + 1) = p * p ^ j := by ring
      _ ∣ p * Nat.card (Subgroup.lowerCentralSeries (⊤ : Subgroup P)
            (Group.nilpotencyClass P - j)) := mul_dvd_mul_left p (ih hjc)
      _ ∣ _ := hdvd

/-- **上方評価**: `p ^ i ∣ |P| / |L_i|` の乗法形 — `p ^ i * |L_i| ∣ |P|` (`i ≤ c`). -/
theorem prime_pow_mul_card_lowerCentralSeries_dvd [Finite P] [Fact p.Prime] (hP : IsPGroup p P)
    [Group.IsNilpotent P] {i : ℕ} (hi : i ≤ Group.nilpotencyClass P) :
    p ^ i * Nat.card (Subgroup.lowerCentralSeries (⊤ : Subgroup P) i) ∣ Nat.card P := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hic : i ≤ Group.nilpotencyClass P := by omega
    have hlt := lowerCentralSeries_lt_of_lt_nilpotencyClass (P := P) (i := i) (by omega)
    have hstep := prime_mul_card_dvd_card_of_lt hP hlt
    obtain ⟨s, hs⟩ := hstep
    obtain ⟨t, ht⟩ := ih hic
    refine ⟨s * t, ?_⟩
    have : Nat.card (Subgroup.lowerCentralSeries (⊤ : Subgroup P) i)
        = p * Nat.card (Subgroup.lowerCentralSeries (⊤ : Subgroup P) (i + 1)) * s := hs
    rw [ht, this]
    ring

/-! ### 非可換 `p`-群では `p² ∣ |P : P'|` -/

/-- `p`-群 `P` で `P / P'` が巡回なら `P` は可換 (`P / Φ(P)` は `P / P'` の商だから巡回,
Burnside の基底定理 `isCyclic_of_frattiniQuotient_isCyclic` で `P` が巡回). -/
theorem isMulCommutative_of_isCyclic_quotient_commutator [Finite P] [Fact p.Prime]
    (hP : IsPGroup p P) (h : IsCyclic (P ⧸ commutator P)) : IsMulCommutative P := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hle : commutator P ≤ frattini P := Ch01.commutator_le_frattini
  have : IsCyclic (P ⧸ frattini P) := by
    have hsurj : Function.Surjective (QuotientGroup.map (commutator P) (frattini P)
        (MonoidHom.id P) (by simpa using hle)) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨(g : P ⧸ commutator P), rfl⟩
    exact isCyclic_of_surjective _ hsurj
  have := Ch01.isCyclic_of_frattiniQuotient_isCyclic (P := P) inferInstance
  exact ⟨⟨fun a b => (IsCyclic.commGroup (α := P)).mul_comm a b⟩⟩

/-- 非可換な `p`-群では `p² · |P'| ∣ |P|`, すなわち `p² ∣ |P : P'|`.

`|P / P'|` が `p` 以下なら `P / P'` は巡回で, 上の補題から `P` は可換. -/
theorem prime_sq_mul_card_commutator_dvd [Finite P] [Fact p.Prime] (hP : IsPGroup p P)
    (hnc : ¬ IsMulCommutative P) : p ^ 2 * Nat.card (commutator P) ∣ Nat.card P := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p) (G := P ⧸ commutator P)).mp
    (hP.to_quotient (commutator P))
  have ha2 : 2 ≤ a := by
    by_contra hcon
    refine hnc (isMulCommutative_of_isCyclic_quotient_commutator hP ?_)
    interval_cases a
    · have : Subsingleton (P ⧸ commutator P) :=
        (Nat.card_eq_one_iff_unique.mp (by simpa using ha)).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (p := p) (by simpa using ha)
  have hidx : (commutator P).index = p ^ a := by
    rw [Subgroup.index_eq_card]; exact ha
  have hmul : Nat.card (commutator P) * (commutator P).index = Nat.card P :=
    Subgroup.card_mul_index _
  have hpow : p ^ a = p ^ 2 * p ^ (a - 2) := by rw [← pow_add]; congr 1; omega
  exact ⟨p ^ (a - 2), by rw [← hmul, hidx, hpow]; ring⟩

/-- `i ≥ 1` では `p ^ (i + 1) · |L_i| ∣ |P|` (非可換 `p`-群). -/
theorem prime_pow_succ_mul_card_lowerCentralSeries_dvd [Finite P] [Fact p.Prime]
    (hP : IsPGroup p P) (hnc : ¬ IsMulCommutative P) {i : ℕ} (hi1 : 1 ≤ i)
    (hi : i ≤ Group.nilpotencyClass P) :
    p ^ (i + 1) * Nat.card (Subgroup.lowerCentralSeries (⊤ : Subgroup P) i) ∣ Nat.card P := by
  have : Group.IsNilpotent P := hP.isNilpotent
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_or_lt_of_le hi1 with h1 | h1
    · -- `i + 1 = 1`: `P' = L_1`
      have hi0 : i = 0 := by omega
      subst hi0
      have hL1 : Subgroup.lowerCentralSeries (⊤ : Subgroup P) 1 = commutator P :=
        Subgroup.top_lowerCentralSeries_one
      rw [hL1]
      exact prime_sq_mul_card_commutator_dvd hP hnc
    · -- 段を 1 つ下げる
      have hi1' : 1 ≤ i := by omega
      have hic : i ≤ Group.nilpotencyClass P := by omega
      obtain ⟨t, ht⟩ := ih hi1' hic
      have hlt := lowerCentralSeries_lt_of_lt_nilpotencyClass (P := P) (i := i) (by omega)
      obtain ⟨s, hs⟩ := prime_mul_card_dvd_card_of_lt hP hlt
      refine ⟨s * t, ?_⟩
      rw [ht, hs]
      ring

/-- **`p`-群の類の上界**: `|G| = p ^ k` (`k ≥ 2`) なら冪零類は `≤ k - 1`. -/
theorem nilpotencyClass_le_of_card_eq_prime_pow [Finite P] [Fact p.Prime] (hP : IsPGroup p P)
    {k : ℕ} (hk : 2 ≤ k) (hcard : Nat.card P = p ^ k) : Group.nilpotencyClass P ≤ k - 1 := by
  have : Group.IsNilpotent P := hP.isNilpotent
  by_cases hab : IsMulCommutative P
  · have := Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr hab
    omega
  · set c := Group.nilpotencyClass P with hc
    have hc2 : 2 ≤ c := by
      by_contra hcon
      exact hab (Group.IsNilpotent.nilpotencyClass_le_one_iff.mp (by omega))
    -- `p^(c-1) ∣ |L_1|` と `p² · |L_1| ∣ |P|`
    have hlow := prime_pow_dvd_card_lowerCentralSeries hP (P := P) (j := c - 1) (by omega)
    have hidx : c - (c - 1) = 1 := by omega
    rw [hidx] at hlow
    obtain ⟨u, hu⟩ := hlow
    obtain ⟨v, hv⟩ := prime_sq_mul_card_commutator_dvd hP hab
    have hL1 : Subgroup.lowerCentralSeries (⊤ : Subgroup P) 1 = commutator P :=
      Subgroup.top_lowerCentralSeries_one
    rw [hL1] at hu
    have hdvd : p ^ (c + 1) ∣ p ^ k := by
      refine ⟨u * v, ?_⟩
      rw [← hcard, hv, hu]
      have : c + 1 = 2 + (c - 1) := by omega
      rw [this]
      ring
    have := (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : p.Prime))).mp hdvd
    omega

/-! ### maximal class -/

/-- **maximal class**: `|P| = p ^ n` で冪零類が `n - 1` (書籍 p. 124 の定義). -/
def IsMaximalClassPGroup (p : ℕ) (P : Type u) [Group P] : Prop :=
  IsPGroup p P ∧ ∃ n : ℕ, Nat.card P = p ^ n ∧ Group.nilpotencyClass P + 1 = n

/-- maximal class の `p`-群 (`|P| = p^n`, `n ≥ 3`) では `|L_i| = p^{n - 1 - i}` (`1 ≤ i ≤ n - 1`).

下方 `p^{c-i} ∣ |L_i|` と上方 `p^{i+1} · |L_i| ∣ |P|` を合わせるだけ (`c = n - 1`). -/
theorem card_lowerCentralSeries_of_isMaximalClass [Finite P] [Fact p.Prime]
    (hP : IsMaximalClassPGroup p P) {n : ℕ} (hn : Nat.card P = p ^ n) (h3 : 3 ≤ n)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ n - 1) :
    Nat.card (Subgroup.lowerCentralSeries (⊤ : Subgroup P) i) = p ^ (n - 1 - i) := by
  obtain ⟨hpg, m, hm, hclass⟩ := hP
  have : Group.IsNilpotent P := hpg.isNilpotent
  have hp1 : 1 < p := Nat.Prime.one_lt (Fact.out : p.Prime)
  -- `m = n`
  have hmn : m = n := by
    have := hm.symm.trans hn
    exact Nat.pow_right_injective hp1 this
  subst hmn
  have hc : Group.nilpotencyClass P = m - 1 := by omega
  -- `P` は非可換 (類 `= m - 1 ≥ 2`)
  have hnc : ¬ IsMulCommutative P := by
    intro hab
    have := Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr hab
    omega
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p)
    (G := Subgroup.lowerCentralSeries (⊤ : Subgroup P) i)).mp
    (hpg.to_subgroup (Subgroup.lowerCentralSeries (⊤ : Subgroup P) i))
  -- 下方: `p^{c-i} ∣ |L_i|`
  have hlow := prime_pow_dvd_card_lowerCentralSeries hpg (P := P) (j := Group.nilpotencyClass P - i)
    (by omega)
  have hidx : Group.nilpotencyClass P - (Group.nilpotencyClass P - i) = i := by omega
  rw [hidx, hb] at hlow
  have hble : m - 1 - i ≤ b := by
    have := (Nat.pow_dvd_pow_iff_le_right hp1).mp hlow
    omega
  -- 上方: `p^{i+1} · |L_i| ∣ |P|`
  obtain ⟨w, hw⟩ := prime_pow_succ_mul_card_lowerCentralSeries_dvd hpg hnc hi1 (by omega)
  have hupper : p ^ (i + 1 + b) ∣ p ^ m := by
    refine ⟨w, ?_⟩
    rw [← hm, hw, hb, pow_add, pow_add, pow_one]
    ring
  have hbge : i + 1 + b ≤ m := (Nat.pow_dvd_pow_iff_le_right hp1).mp hupper
  rw [hb]
  congr 1
  omega

/-! ### Problem 4A.6 -/

/-- **Isaacs Problem 4A.6** (書籍 p. 124): `P` が maximal class の `p`-群, `N ⊴ P`,
`|P : N| = p^k` (`k ≥ 2`) なら `N` は下降中心列の項 `L_{k-1}` に一致する.

`|P ⧸ N| = p^k` の類は `≤ k - 1` (`nilpotencyClass_le_of_card_eq_prime_pow`) なので
`L_{k-1}(P ⧸ N) = ⊥`, すなわち `L_{k-1}(P) ≤ N`. 一方 maximal class から
`|L_{k-1}(P)| = p^{n-k} = |N|` なので一致する. -/
theorem eq_lowerCentralSeries_of_isMaximalClass_of_index_eq [Finite P] [Fact p.Prime]
    (hP : IsMaximalClassPGroup p P) {n : ℕ} (hn : Nat.card P = p ^ n) (h3 : 3 ≤ n)
    {N : Subgroup P} [N.Normal] {k : ℕ} (hk : 2 ≤ k) (hidx : N.index = p ^ k) :
    N = Subgroup.lowerCentralSeries (⊤ : Subgroup P) (k - 1) := by
  obtain ⟨hpg, -⟩ := id hP
  have hp1 : 1 < p := Nat.Prime.one_lt (Fact.out : p.Prime)
  -- `k ≤ n`
  have hcardN : Nat.card N * p ^ k = p ^ n := by rw [← hidx, ← hn]; exact Subgroup.card_mul_index N
  have hkn : k ≤ n := by
    have : p ^ k ∣ p ^ n := ⟨Nat.card N, by rw [← hcardN]; ring⟩
    exact (Nat.pow_dvd_pow_iff_le_right hp1).mp this
  -- `|N| = p ^ (n - k)`
  have hNcard : Nat.card N = p ^ (n - k) := by
    have hsplit : p ^ n = p ^ (n - k) * p ^ k := by rw [← pow_add]; congr 1; omega
    rw [hsplit] at hcardN
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by omega : 0 < p) k) hcardN
  -- `L_{k-1}(P) ≤ N`
  have hquot : Nat.card (P ⧸ N) = p ^ k := by rw [← Subgroup.index_eq_card]; exact hidx
  have hclassQ : Group.nilpotencyClass (P ⧸ N) ≤ k - 1 :=
    nilpotencyClass_le_of_card_eq_prime_pow (hpg.to_quotient N) hk hquot
  have : Group.IsNilpotent (P ⧸ N) := (hpg.to_quotient N).isNilpotent
  have hbotQ : Subgroup.lowerCentralSeries (⊤ : Subgroup (P ⧸ N)) (k - 1) = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hclassQ
  have hle : Subgroup.lowerCentralSeries (⊤ : Subgroup P) (k - 1) ≤ N := by
    have hmap := Subgroup.map_lowerCentralSeries (⊤ : Subgroup P) (QuotientGroup.mk' N) (k - 1)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), hbotQ] at hmap
    intro g hg
    have : (QuotientGroup.mk' N) g ∈ (⊥ : Subgroup (P ⧸ N)) := hmap ▸ Subgroup.mem_map_of_mem _ hg
    rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at this
    exact this
  -- 位数を比べる
  have hLcard : Nat.card (Subgroup.lowerCentralSeries (⊤ : Subgroup P) (k - 1))
      = p ^ (n - k) := by
    have := card_lowerCentralSeries_of_isMaximalClass hP hn h3 (i := k - 1) (by omega) (by omega)
    rw [this]
    congr 1
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hLcard, hNcard])).symm

/-- **Isaacs Problem 4A.6** (書籍そのままの形, p. 124): maximal class の `p`-群で
`N ⊴ P` かつ `p² ∣ |P : N|` なら, `N` は下降中心列の項の 1 つ.

`P` は `p`-群なので `|P : N|` は `p` 冪, `p² ∣ |P : N|` からその指数は `≥ 2`. -/
theorem exists_eq_lowerCentralSeries_of_isMaximalClass [Finite P] [Fact p.Prime]
    (hP : IsMaximalClassPGroup p P) {n : ℕ} (hn : Nat.card P = p ^ n) (h3 : 3 ≤ n)
    {N : Subgroup P} [N.Normal] (hidx : p ^ 2 ∣ N.index) :
    ∃ i : ℕ, N = Subgroup.lowerCentralSeries (⊤ : Subgroup P) i := by
  have hp1 : 1 < p := Nat.Prime.one_lt (Fact.out : p.Prime)
  have hdvd : N.index ∣ p ^ n := hn ▸ N.index_dvd_card
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  have hk2 : 2 ≤ k := by
    rw [hk] at hidx
    exact (Nat.pow_dvd_pow_iff_le_right hp1).mp hidx
  exact ⟨k - 1, eq_lowerCentralSeries_of_isMaximalClass_of_index_eq hP hn h3 hk2 hk⟩

/-- **Isaacs Problem 4A.6** (系, 書籍 p. 124): maximal class の `p`-群では, 指数が `p²` 以上の
正規部分群はその位数で一意に決まる. -/
theorem eq_of_normal_of_card_eq_of_isMaximalClass [Finite P] [Fact p.Prime]
    (hP : IsMaximalClassPGroup p P) {n : ℕ} (hn : Nat.card P = p ^ n) (h3 : 3 ≤ n)
    {N M : Subgroup P} [N.Normal] [M.Normal] {k : ℕ} (hk : 2 ≤ k)
    (hN : N.index = p ^ k) (hM : M.index = p ^ k) : N = M :=
  (eq_lowerCentralSeries_of_isMaximalClass_of_index_eq hP hn h3 hk hN).trans
    (eq_lowerCentralSeries_of_isMaximalClass_of_index_eq hP hn h3 hk hM).symm

/-! ### 部分群の冪零類 -/

/-- 部分群の冪零類は**環境群の中で計算した**下降中心列で判定できる. -/
theorem nilpotencyClass_le_iff_lowerCentralSeries_eq_bot {G : Type*} [Group G] (S : Subgroup G)
    [Group.IsNilpotent ↥S] {m : ℕ} :
    Group.nilpotencyClass ↥S ≤ m ↔ S.lowerCentralSeries m = ⊥ := by
  rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    ← Subgroup.top_subtype_lowerCentralSeries S m,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective S)]


end

end OddOrder.Isaacs.Ch04
