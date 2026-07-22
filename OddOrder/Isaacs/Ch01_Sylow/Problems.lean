/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.GroupAction.Quotient
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# Isaacs Chapter 1 — Problems (演習問題)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 1 "Sylow Theory"
(pp. 1-44) の章末演習問題 (Problems 1A–1G) の Lean 化。

**scope 拡大** (issue 9205 ③ / campaign 1055、ユーザー裁定 2026-07-22): 従来の被覆測定
(`notes/isaacs/frontier_measured_2026_07_19.md`) は「番号付き結果のみ」で演習を対象外に
していたが、本ファイル以降で演習も形式化対象に加える。

## 方針 (CLAUDE.md ラッパー方針)

- mathlib / repo に直接対応がある演習は **docstring で対応を記録** (純粋リネームは書かない)。
- Isaacs の仮定形が mathlib と異なる (例: 「`p` より小さい素数が `|G|` を割らない」vs `minFac`)
  場合は **仮定変換の橋渡し補題**を書く (意味のあるラッパー例外)。
- それ以外は実証明。
-/

namespace OddOrder.Isaacs.Ch01

section /- Problems 1A: Group actions and counting (pp. 7-8) -/

/-- **Isaacs Problem 1A.1**. 有限群 `G` の素数指数 `p` の部分群 `H` について、
`p` より小さい素数が `|G|` を割らないならば `H ⊴ G`。

mathlib の `Subgroup.normal_of_index_eq_minFac_card` (指数 = `|G|` の最小素因数 ⟹ 正規) への
橋渡し: Isaacs の「`p` より小さい素数が `|G|` を割らない」仮定を `p = (Nat.card G).minFac` に
変換する (`p` は素数で `|G|` を割る ⟹ `minFac ≤ p`、仮定 ⟹ `p ≤ minFac`)。 -/
theorem normal_of_prime_index_of_no_smaller_prime {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hHp : H.index = p)
    (hsmall : ∀ q, q.Prime → q ∣ Nat.card G → p ≤ q) : H.Normal := by
  apply Subgroup.normal_of_index_eq_minFac_card
  have hdvd : p ∣ Nat.card G := hHp ▸ H.index_dvd_card
  have hcard1 : Nat.card G ≠ 1 := fun h1 => hp.ne_one (Nat.dvd_one.mp (h1 ▸ hdvd))
  rw [hHp]
  exact le_antisymm (hsmall _ (Nat.minFac_prime hcard1) (Nat.minFac_dvd _))
    (Nat.minFac_le_of_dvd hp.two_le hdvd)

/-- **Isaacs Problem 1A.9**. `|G| = p·m` で `p` は素数かつ `p > m` ならば、`G` は位数 `p` の
部分群をちょうど 1 つ持つ。

証明: `0 < m < p` ゆえ `p ∤ m`、よって `|G|` の `p`-部分は `p` ちょうど (`v_p(|G|) = 1`)、
Sylow `p`-部分群は位数 `p`。Sylow の個数 `nₚ ∣ [G:P] = m < p` かつ `nₚ ≡ 1 (mod p)` から
`nₚ = 1` ⟹ Sylow は一意。位数 `p` の部分群は必ず Sylow `p`-部分群ゆえ一意。 -/
theorem exists_unique_subgroup_card_eq_of_prime_gt {G : Type*} [Group G] [Finite G] {p m : ℕ}
    (hp : p.Prime) (hcard : Nat.card G = p * m) (hpm : m < p) :
    ∃! P : Subgroup G, Nat.card P = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  have hcardpos : 0 < Nat.card G := Nat.card_pos
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.mul_zero] at hcard; omega
    · exact h
  have hpm_ndvd : ¬ p ∣ m := Nat.not_dvd_of_pos_of_lt hm0 hpm
  have hfact : (Nat.card G).factorization p = 1 := by
    rw [hcard, Nat.factorization_mul hp.pos.ne' hm0.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self hp, Nat.factorization_eq_zero_of_not_dvd hpm_ndvd]
  have hPcard : Nat.card (P : Subgroup G) = p := by
    rw [Sylow.card_eq_multiplicity, hfact, pow_one]
  -- Sylow の個数 nₚ = 1
  have hnp : Nat.card (Sylow p G) = 1 := by
    have hPindex : P.index = m := by
      have h := Subgroup.card_mul_index (P : Subgroup G)
      rw [hPcard, hcard] at h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    have hdvd : Nat.card (Sylow p G) ∣ m := hPindex ▸ P.card_dvd_index
    have hlt : Nat.card (Sylow p G) < p := lt_of_le_of_lt (Nat.le_of_dvd hm0 hdvd) hpm
    have hmodeq : Nat.card (Sylow p G) % p = 1 % p := card_sylow_modEq_one p G
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp.one_lt] at hmodeq
  have hsub : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hnp).1
  refine ⟨(P : Subgroup G), hPcard, ?_⟩
  intro Q hQ
  have hQfact : Nat.card (Q : Subgroup G) = p ^ (Nat.card G).factorization p := by
    rw [hQ, hfact, pow_one]
  have hQP : Sylow.ofCard Q hQfact = P := Subsingleton.elim _ _
  rw [← Sylow.coe_ofCard Q hQfact, hQP]

/-- **Isaacs Problem 1A.4** (核となる被覆補題). 部分群 `H, K` が `H·K = G` (任意の `g` が
`h·k`, `h∈H`, `k∈K` と書ける) をみたすなら、任意の `z` で `H·(z⁻¹Kz) = G`。

証明: `z⁻¹ = h₀·k₀`, `g·z⁻¹ = h₁·k₁` と分解し、`g = (h₁h₀⁻¹)·(z⁻¹(k₀⁻¹k₁)z)` を確認する
(中央の `z⁻¹` を `h₀k₀` に置換すると `h₀⁻¹h₀`, `k₀k₀⁻¹` が消えて `h₁k₁z = (gz⁻¹)z = g`)。 -/
theorem exists_mem_mul_conj_of_covers {G : Type*} [Group G] {H K : Subgroup G}
    (hcov : ∀ g : G, ∃ h ∈ H, ∃ k ∈ K, h * k = g) (z g : G) :
    ∃ h ∈ H, ∃ k ∈ K, h * (z⁻¹ * k * z) = g := by
  obtain ⟨h₀, hh₀, k₀, hk₀, e0⟩ := hcov z⁻¹
  obtain ⟨h₁, hh₁, k₁, hk₁, e1⟩ := hcov (g * z⁻¹)
  refine ⟨h₁ * h₀⁻¹, mul_mem hh₁ (inv_mem hh₀), k₀⁻¹ * k₁, mul_mem (inv_mem hk₀) hk₁, ?_⟩
  have step : h₁ * h₀⁻¹ * (z⁻¹ * (k₀⁻¹ * k₁) * z) = h₁ * k₁ * z := by
    rw [← e0]; group
  rw [step, e1]; group

open Pointwise in
/-- **Isaacs Problem 1A.4** (帰結). `H·H^x = G` (`H^x = x⁻¹Hx`、任意の `g` が
`h·(x⁻¹h'x)`, `h,h'∈H` と書ける) ならば `H = ⊤`。

上の被覆補題を `K = x⁻¹Hx`, `z = x⁻¹` に適用すると `H·(x·(x⁻¹Hx)·x⁻¹) = H·H = G` を得るが、
`H·H = H` (`H` は部分群) ゆえ `H = ⊤`。 -/
theorem eq_top_of_mul_conj_covers {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hcov : ∀ g : G, ∃ h ∈ H, ∃ h' ∈ H, h * (x⁻¹ * h' * x) = g) : H = ⊤ := by
  set K : Subgroup G := MulAut.conj x⁻¹ • H with hK
  -- H·K = G (K = x⁻¹Hx)
  have hcovK : ∀ g : G, ∃ h ∈ H, ∃ k ∈ K, h * k = g := by
    intro g
    obtain ⟨h, hh, h', hh', hg⟩ := hcov g
    refine ⟨h, hh, x⁻¹ * h' * x, ?_, hg⟩
    rw [hK, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hconj : (MulAut.conj x⁻¹)⁻¹ • (x⁻¹ * h' * x) = h' := by
      simp only [← map_inv, inv_inv, MulAut.smul_def, MulAut.conj_apply]; group
    rw [hconj]; exact hh'
  -- 被覆補題 (z = x⁻¹) を適用
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨h, hh, k, hk, hg⟩ := exists_mem_mul_conj_of_covers hcovK x⁻¹ g
  -- k ∈ K = x⁻¹Hx ⟹ x·k·x⁻¹ ∈ H
  have hxk : x * k * x⁻¹ ∈ H := by
    rw [hK, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hk
    have hconj : (MulAut.conj x⁻¹)⁻¹ • k = x * k * x⁻¹ := by
      simp only [← map_inv, inv_inv, MulAut.smul_def, MulAut.conj_apply]
    rwa [hconj] at hk
  -- g = h · (x·k·x⁻¹)、両方 H の元
  have : g = h * (x * k * x⁻¹) := by rw [← hg]; group
  rw [this]
  exact mul_mem hh hxk

/-- **Isaacs Problem 1A.10(b)**. `|H|` が素数 `p` の冪で `p ∣ |G:H|` ならば `p ∣ |N_G(H):H|`。

mathlib の `Sylow.prime_dvd_card_quotient_normalizer` (前提が `p^(n+1) ∣ |G|`) への仮定変換:
`|H| = p^n` かつ `p ∣ [G:H]` から `|G| = |H|·[G:H] = p^n·(p·s) = p^(n+1)·s` を得る。結論の
`N_G(H) ⧸ H.comap (N_G(H)).subtype` は `N_G(H)/H`、その位数が指数 `[N_G(H):H]`。 -/
theorem prime_dvd_index_normalizer_of_prime_pow {G : Type*} [Group G] [Finite G] {p n : ℕ}
    (hp : p.Prime) {H : Subgroup G} (hH : Nat.card H = p ^ n) (hdvd : p ∣ H.index) :
    p ∣ Nat.card (Subgroup.normalizer (H : Set G) ⧸
      H.comap (Subgroup.normalizer (H : Set G)).subtype) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hs⟩ := hdvd
  refine Sylow.prime_dvd_card_quotient_normalizer ⟨s, ?_⟩ hH
  rw [← Subgroup.card_mul_index H, hH, hs, pow_succ]; ring

open Pointwise MulAction in
/-- **Isaacs Problem 1A.2**. 二重剰余類の位数公式: `|HgK| · |K ∩ H^g| = |H| · |K|`
(`H^g = g⁻¹Hg = MulAut.conj g⁻¹ • H`)。除算形は `|HgK| = |H||K| / |K ∩ H^g|`。`g = 1` で
通常の `|HK| = |H||K|/|H∩K|` 公式。

`H × K` を `(h,k)•x = h·x·k⁻¹` で `G` に作用させると、`g` の軌道が `HgK` (集合として)、
固定化群 `{(h,k) : h·g·k⁻¹ = g}` が `k ↦ (g k g⁻¹, k)` で `K ∩ H^g` と同型。軌道-固定化群定理
(`orbitProdStabilizerEquivGroup`) より従う。 -/
theorem card_doubleCoset_mul_card_inf_conj {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (g : G) :
    Nat.card (DoubleCoset.doubleCoset g (H : Set G) K) * Nat.card ↥(K ⊓ MulAut.conj g⁻¹ • H)
      = Nat.card H * Nat.card K := by
  -- `H^g` の membership 判定
  have hmem : ∀ y : G, y ∈ MulAut.conj g⁻¹ • H ↔ g * y * g⁻¹ ∈ H := fun y => by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hy : (MulAut.conj g⁻¹)⁻¹ • y = g * y * g⁻¹ := by
      simp only [← map_inv, inv_inv, MulAut.smul_def, MulAut.conj_apply]
    rw [hy]
  -- 両側作用 (h,k)•x = h x k⁻¹
  letI act : MulAction (H × K) G :=
    { smul := fun p x => (p.1 : G) * x * (p.2 : G)⁻¹
      one_smul := fun x => by
        change ((1 : H × K).1 : G) * x * ((1 : H × K).2 : G)⁻¹ = x
        simp
      mul_smul := fun p q x => by
        change ((p * q).1 : G) * x * ((p * q).2 : G)⁻¹
          = (p.1 : G) * ((q.1 : G) * x * (q.2 : G)⁻¹) * (p.2 : G)⁻¹
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]; group }
  -- 軌道 = HgK
  have horb : orbit (H × K) g = DoubleCoset.doubleCoset g (H : Set G) K := by
    ext x
    rw [mem_orbit_iff, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨⟨h, k⟩, rfl⟩
      exact ⟨h, h.2, (k : G)⁻¹, K.inv_mem k.2, rfl⟩
    · rintro ⟨h, hh, k, hk, rfl⟩
      exact ⟨(⟨h, hh⟩, ⟨k⁻¹, K.inv_mem hk⟩), by
        change (h : G) * g * ((k : G)⁻¹)⁻¹ = h * g * k; group⟩
  -- 固定化群条件: (h,k)•g = g ⟹ g·k·g⁻¹ = h
  have hstabeq : ∀ p : stabilizer (H × K) g, g * (p.1.2 : G) * g⁻¹ = (p.1.1 : G) := fun p => by
    have hp : (p.1.1 : G) * g * (p.1.2 : G)⁻¹ = g := p.2
    calc g * (p.1.2 : G) * g⁻¹
        = (p.1.1 : G) * g * (p.1.2 : G)⁻¹ * (p.1.2 : G) * g⁻¹ := by rw [hp]
      _ = (p.1.1 : G) := by group
  -- 固定化群 ≅ K ⊓ H^g  (k ↦ (g k g⁻¹, k))
  have hstab : Nat.card (stabilizer (H × K) g) = Nat.card ↥(K ⊓ MulAut.conj g⁻¹ • H) := by
    apply Nat.card_congr
    refine
      { toFun := fun p => ⟨(p.1.2 : G), Subgroup.mem_inf.2 ⟨p.1.2.2, ?_⟩⟩
        invFun := fun t => ⟨(⟨g * (t : G) * g⁻¹, (hmem t).1 (Subgroup.mem_inf.1 t.2).2⟩,
          ⟨(t : G), (Subgroup.mem_inf.1 t.2).1⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · -- (p.1.2 : G) ∈ H^g
      rw [hmem, hstabeq p]; exact p.1.1.2
    · -- (g t g⁻¹, t) ∈ stabilizer
      change (g * (t : G) * g⁻¹) * g * ((t : G))⁻¹ = g
      group
    · -- left_inv
      intro p
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext (hstabeq p)
      · exact Subtype.ext rfl
    · -- right_inv
      intro t
      exact Subtype.ext rfl
  rw [← horb, ← hstab, ← Nat.card_prod,
    Nat.card_congr (orbitProdStabilizerEquivGroup (H × K) g), Nat.card_prod]

open Pointwise in
/-- 部分群積の位数公式 `|HK| · |H∩K| = |H| · |K|` (Isaacs 1A.2 の Note の「よく知られた公式」、
上の `card_doubleCoset_mul_card_inf_conj` を `g = 1` に適用したもの)。 -/
theorem card_mul_card_inf {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    Nat.card (↑H * ↑K : Set G) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h2 := card_doubleCoset_mul_card_inf_conj H K 1
  have hdc : DoubleCoset.doubleCoset (1 : G) (↑H) (↑K) = (↑H * ↑K : Set G) := by
    ext x
    rw [DoubleCoset.mem_doubleCoset, Set.mem_mul]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, by group⟩
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, by group⟩
  have hconj : MulAut.conj (1 : G)⁻¹ • H = H := by rw [inv_one, map_one, one_smul]
  rw [hdc, hconj, inf_comm] at h2
  exact h2

open Pointwise in
/-- **Isaacs Problem 1A.3(a)** (不等式). `|H : H∩K| ≤ |G : K|`、乗法形 `|H|·|K| ≤ |G|·|H∩K|`。
`|H|·|K| = |HK|·|H∩K| ≤ |G|·|H∩K|` (`HK ⊆ G`)。index 形 `(H⊓K).index ≤ H.index·K.index` は
mathlib の `Subgroup.index_inf_le`。 -/
theorem card_mul_le_card_mul_card_inf {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    Nat.card H * Nat.card K ≤ Nat.card G * Nat.card ↥(H ⊓ K) := by
  rw [← card_mul_card_inf H K]
  gcongr
  rw [Nat.card_coe_set_eq, ← Set.ncard_univ G]
  exact Set.ncard_le_ncard (Set.subset_univ _)

open Pointwise in
/-- **Isaacs Problem 1A.3(a)** (等号条件). `|H|·|K| = |G|·|H∩K| ⟺ HK = G` (集合として)。 -/
theorem card_mul_eq_iff_mul_eq_univ {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    Nat.card H * Nat.card K = Nat.card G * Nat.card ↥(H ⊓ K) ↔ (↑H * ↑K : Set G) = Set.univ := by
  rw [← card_mul_card_inf H K, Set.eq_univ_iff_ncard, ← Nat.card_coe_set_eq]
  constructor
  · exact fun h => Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  · exact fun h => by rw [h]

open Pointwise in
/-- **Isaacs Problem 1A.3(b)**. `|G:H|` と `|G:K|` が互いに素ならば `HK = G` (集合として)。

`[G:H] ∣ [G:H∩K]` かつ `[G:K] ∣ [G:H∩K]` (∵ `H∩K ≤ H,K`)、互いに素ゆえ `[G:H]·[G:K] ∣ [G:H∩K]`。
一方 `[G:H∩K] ≤ [G:H]·[G:K]` (`Subgroup.index_inf_le`)。よって `[G:H∩K] = [G:H]·[G:K]`、
これは (a) の等号条件 `|H|·|K| = |G|·|H∩K|` と同値ゆえ `HK = G`。 -/
theorem mul_eq_univ_of_coprime_index {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hcop : Nat.Coprime H.index K.index) : (↑H * ↑K : Set G) = Set.univ := by
  rw [← card_mul_eq_iff_mul_eq_univ]
  have hdvd : H.index * K.index ∣ (H ⊓ K).index :=
    hcop.mul_dvd_of_dvd_of_dvd (Subgroup.index_dvd_of_le inf_le_left)
      (Subgroup.index_dvd_of_le inf_le_right)
  have hpos : 0 < (H ⊓ K).index := Nat.pos_of_ne_zero fun h => by
    have hc := Subgroup.card_mul_index (H ⊓ K)
    rw [h, Nat.mul_zero] at hc
    exact (Nat.card_pos).ne' hc.symm
  have hidx : (H ⊓ K).index = H.index * K.index :=
    le_antisymm Subgroup.index_inf_le (Nat.le_of_dvd hpos hdvd)
  have eH : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
  have eK : Nat.card K * K.index = Nat.card G := Subgroup.card_mul_index K
  have eI : Nat.card ↥(H ⊓ K) * (H.index * K.index) = Nat.card G := by
    rw [← hidx]; exact Subgroup.card_mul_index (H ⊓ K)
  have hprodpos : 0 < H.index * K.index := hidx ▸ hpos
  apply Nat.eq_of_mul_eq_mul_right hprodpos
  calc Nat.card H * Nat.card K * (H.index * K.index)
      = (Nat.card H * H.index) * (Nat.card K * K.index) := by ring
    _ = Nat.card G * Nat.card G := by rw [eH, eK]
    _ = Nat.card G * (Nat.card ↥(H ⊓ K) * (H.index * K.index)) := by rw [eI]
    _ = Nat.card G * Nat.card ↥(H ⊓ K) * (H.index * K.index) := by ring

open Pointwise MulAction in
/-- **Isaacs Problem 1A.5**. `G` が `α`, `β` に推移的に作用するとき、積 `α × β` への (対角) 作用が
推移的 ⟺ `G_a · G_b = G` (安定化群の集合積、`a`, `b` は任意の基点)。

⟹: `c ∈ G` に対し `(a,b) → (a, c·b)` を送る `g` (推移性) は `g∈G_a` かつ `g⁻¹c∈G_b`、
`c = g·(g⁻¹c)`。⟸: `(a',b')` に対し `g₁·a=a'`, `g₂·b=b'` を取り、`g₂⁻¹g₁ ∈ G_b·G_a`
(= `univ`) を `t·s` と分解して `g = g₂·t` とすると `g·a=a'`, `g·b=b'`。 -/
theorem isPretransitive_prod_iff {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]
    [IsPretransitive G α] [IsPretransitive G β] (a : α) (b : β) :
    IsPretransitive G (α × β) ↔
      (↑(stabilizer G a) * ↑(stabilizer G b) : Set G) = Set.univ := by
  constructor
  · intro h
    ext c
    simp only [Set.mem_univ, iff_true, Set.mem_mul, SetLike.mem_coe]
    obtain ⟨g, hg⟩ := h.exists_smul_eq (a, b) (a, c • b)
    obtain ⟨hga, hgb⟩ := Prod.ext_iff.mp hg
    have hga : g • a = a := hga
    have hgb : g • b = c • b := hgb
    refine ⟨g, ?_, g⁻¹ * c, ?_, by group⟩
    · rw [mem_stabilizer_iff]; exact hga
    · rw [mem_stabilizer_iff, mul_smul, ← hgb, inv_smul_smul]
  · intro h
    have hconnect : ∀ (a' : α) (b' : β), ∃ g : G, g • a = a' ∧ g • b = b' := by
      intro a' b'
      obtain ⟨g₁, hg₁⟩ := exists_smul_eq G a a'
      obtain ⟨g₂, hg₂⟩ := exists_smul_eq G b b'
      have hmem : g₁⁻¹ * g₂ ∈ (↑(stabilizer G a) * ↑(stabilizer G b) : Set G) :=
        h ▸ Set.mem_univ _
      rw [Set.mem_mul] at hmem
      obtain ⟨s, hs, t, ht, hst⟩ := hmem
      rw [SetLike.mem_coe, mem_stabilizer_iff] at hs ht
      refine ⟨g₁ * s, ?_, ?_⟩
      · rw [mul_smul, hs, hg₁]
      · have hg : g₁ * s = g₂ * t⁻¹ := by
          have h2 : g₁ * (s * t) = g₂ := by rw [hst]; group
          rw [← h2]; group
        rw [hg, mul_smul]
        rw [show t⁻¹ • b = b by rw [inv_smul_eq_iff, ht], hg₂]
    refine ⟨fun x y => ?_⟩
    obtain ⟨gx, hgx1, hgx2⟩ := hconnect x.1 x.2
    obtain ⟨gy, hgy1, hgy2⟩ := hconnect y.1 y.2
    refine ⟨gy * gx⁻¹, ?_⟩
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · change (gy * gx⁻¹) • x.1 = y.1
      rw [← hgx1, mul_smul, inv_smul_smul]; exact hgy1
    · change (gy * gx⁻¹) • x.2 = y.2
      rw [← hgx2, mul_smul, inv_smul_smul]; exact hgy2

open MulAction in
/-- Burnside の補題 (Nat.card 版): 有限群 `M` が有限集合 `β` に作用するとき
`∑_{m∈M}|Fix(m)| = (#軌道)·|M|`。mathlib の Fintype 版
`sum_card_fixedBy_eq_card_orbits_mul_card_group` の Nat.card 化 (Isaacs 1A.6 の置換指標による
軌道計数、1A.7 で使用)。`∑ m : M` の総和記法のため `[Fintype M]` が必要。 -/
theorem sum_card_fixedBy_nat {M β : Type*} [Group M] [Fintype M] [MulAction M β] [Finite β] :
    ∑ m : M, Nat.card (fixedBy β m) = Nat.card (orbitRel.Quotient M β) * Nat.card M := by
  classical
  obtain ⟨_⟩ := nonempty_fintype β
  haveI : Fintype (orbitRel.Quotient M β) := Fintype.ofFinite _
  simp only [Nat.card_eq_fintype_card]
  exact sum_card_fixedBy_eq_card_orbits_mul_card_group M β

open MulAction in
/-- **Isaacs Problem 1A.7**. 有限群 `G` の真部分群 `H` の共役のいずれにも属さない元
(`∀ x, x⁻¹gx ∉ H`) は `|H|` 個以上ある。

`χ(g) = |Fix_{G⧸H}(g)|` について Burnside を `G`, `H` に適用: `∑_{g∈G}χ(g) = |G|` (推移的)、
`∑_{h∈H}χ(h) = |H|·(#H-軌道) ≥ 2|H|` (真部分群ゆえ H-軌道 = 二重剰余類が 2 個以上)。
`χ(g)=0 ⟺ g⁻¹ が共役に入らない`、counting `z ≥ (|G|-|H|)-∑_{g∉H}χ ≥ |H|`、`g↦g⁻¹` 双射。 -/
theorem card_not_mem_conj_ge {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : H ≠ ⊤) :
    Nat.card H ≤ Nat.card {g : G // ∀ x : G, x⁻¹ * g * x ∉ H} := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- (a) g fixes QuotientGroup.mk x ⟺ x⁻¹g⁻¹x ∈ H
  have hfix : ∀ g x : G,
      g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x ↔ x⁻¹ * g⁻¹ * x ∈ H := fun g x => by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_inv_rev]
  -- (b) χ g = 0 ⟺ ∀ x, x⁻¹g⁻¹x ∉ H
  have hχzero : ∀ g : G, Nat.card (fixedBy (G ⧸ H) g) = 0 ↔ ∀ x : G, x⁻¹ * g⁻¹ * x ∉ H := by
    intro g
    rw [Nat.card_eq_zero, or_iff_left (not_infinite_iff_finite.mpr inferInstance),
      Set.isEmpty_coe_sort, Set.eq_empty_iff_forall_notMem]
    refine ⟨fun h x hx => h (QuotientGroup.mk x : G ⧸ H) (mem_fixedBy.mpr ((hfix g x).mpr hx)),
      fun h c => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    exact fun hc => h x ((hfix g x).mp (mem_fixedBy.mp hc))
  -- (G-side) ∑ χ = |G|
  have hsumG : ∑ g : G, Nat.card (fixedBy (G ⧸ H) g) = Nat.card G := by
    rw [sum_card_fixedBy_nat]
    haveI : Subsingleton (orbitRel.Quotient G (G ⧸ H)) :=
      (pretransitive_iff_subsingleton_quotient G (G ⧸ H)).mp inferInstance
    rw [show Nat.card (orbitRel.Quotient G (G ⧸ H)) = 1 from Nat.card_unique, one_mul]
  -- (H-side) 2|H| ≤ ∑_{h∈H} χ(↑h)
  have hsumH : 2 * Nat.card H ≤ ∑ h : H, Nat.card (fixedBy (G ⧸ H) (h : G)) := by
    have heq : ∑ h : H, Nat.card (fixedBy (G ⧸ H) (h : G))
        = Nat.card (orbitRel.Quotient H (G ⧸ H)) * Nat.card H := sum_card_fixedBy_nat
    rw [heq]
    gcongr
    -- 2 ≤ #H-軌道: [1] と [x] (x∉H) が別軌道
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hH)
    have hnt : Nontrivial (orbitRel.Quotient H (G ⧸ H)) := by
      refine ⟨Quotient.mk'' (QuotientGroup.mk (1 : G) : G ⧸ H),
        Quotient.mk'' (QuotientGroup.mk x : G ⧸ H), ?_⟩
      rw [ne_eq, Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      rintro ⟨h, hh⟩
      rw [show (h • (QuotientGroup.mk x : G ⧸ H)) = QuotientGroup.mk ((h : G) * x) from rfl,
        QuotientGroup.eq, mul_one, mul_inv_rev] at hh
      exact hx (H.inv_mem_iff.mp (by simpa using H.mul_mem hh h.2))
    exact Finite.one_lt_card_iff_nontrivial.mpr hnt
  -- target ≃ {χ = 0} (g ↦ g⁻¹, hχzero)
  rw [show Nat.card {g : G // ∀ x : G, x⁻¹ * g * x ∉ H}
      = Nat.card {g : G // Nat.card (fixedBy (G ⧸ H) g) = 0} from
    Nat.card_congr ((Equiv.inv G).subtypeEquiv fun g => by
      rw [Equiv.inv_apply, hχzero]; simp only [inv_inv])]
  -- Finset counting
  haveI : Fintype {g : G // Nat.card (fixedBy (G ⧸ H) g) = 0} := Fintype.ofFinite _
  set f : G → ℕ := fun g => Nat.card (fixedBy (G ⧸ H) g) with hf
  set SH := Finset.univ.filter (fun g => g ∈ H) with hSHd
  set SHc := Finset.univ.filter (fun g => g ∉ H) with hSHcd
  set Z := Finset.univ.filter (fun g => f g = 0) with hZd
  have hcardH : SH.card = Nat.card H := by
    rw [hSHd, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcardZ : Z.card = Nat.card {g : G // f g = 0} := by
    rw [hZd, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← hcardH, ← hcardZ]
  -- 和の分割 A + B = |G|
  have hsum : (∑ g ∈ SH, f g) + (∑ g ∈ SHc, f g) = Nat.card G :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ H) f).trans hsumG
  -- H 側 ≥ 2·|SH|
  have hSHge : 2 * SH.card ≤ ∑ g ∈ SH, f g := by
    rw [hcardH]
    calc 2 * Nat.card H ≤ ∑ h : H, f (h : G) := hsumH
      _ = ∑ g ∈ SH, f g := (Finset.sum_subtype _ (fun g => by rw [hSHd]; simp) f).symm
  -- Hᶜ 側: |SHc| ≤ B + |Z|
  have hB : SHc.card ≤ (∑ g ∈ SHc, f g) + Z.card := by
    have hle : SHc.card ≤ ∑ g ∈ SHc, (f g + if f g = 0 then 1 else 0) := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun g _ => by
        by_cases h : f g = 0
        · rw [if_pos h]; omega
        · rw [if_neg h]; omega
    refine hle.trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_boole]
    gcongr
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  -- |SH| + |SHc| = |G|
  have hcompl : SH.card + SHc.card = Nat.card G := by
    rw [hSHd, hSHcd, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Nat.card_eq_fintype_card]
  omega

end

/-! ## mathlib で被覆される演習 (続き)

- **Problem 1A.10(a)** (`|N_G(H):H|` = `H` の右移動で不変な右剰余類の個数): `H` が右剰余類
  `G⧸H` に左移動で作用するときの不動点が `N_G(H)/H` と一致することを述べており、mathlib の
  `Sylow.fixedPointsMulLeftCosetsEquivQuotient H : fixedPoints H (G ⧸ H) ≃ N_G(H) ⧸ (H の像)`
  が与える (これは 1A.10(b) = `prime_dvd_card_quotient_normalizer` の証明の中核でもある)。
-/

/-! ## mathlib で被覆される演習 (docstring 記録、純粋ラッパーは書かない)

- **Problem 1A.6** (置換指標による軌道計数 = Burnside / Cauchy–Frobenius の補題):
  置換指標 `χ(g) = |{a | a·g = a}|` について `∑_{g∈G} χ(g) = n·|G|` (`n` = 軌道数) は
  mathlib の `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` そのもの
  (`Mathlib/GroupTheory/GroupAction/Quotient.lean`)。中間項 `∑_{a} |G_a|` との等式は
  orbit–stabilizer から従う。

- **Problem 1A.8** (Cauchy の定理): 素数 `p ∣ |G|` ⟹ `G` は位数 `p` の元を持つ、は mathlib の
  `exists_prime_orderOf_dvd_card`。McKay の証明 (`ℤ/p` が `x₁⋯xₚ=1` なる `p`-組の集合に
  巡回シフトで作用し、不動点 = 対角 `(x,…,x)` with `xᵖ=1`) が、まさに mathlib の証明戦略。
  位数 `p` の元の個数 `≡ -1 (mod p)` の精緻化は本ファイルの 1A.9 で使う。
-/

section /- Problems 1B: Sylow subgroups and normalizers (pp. 12-14) -/

open Pointwise in
/-- **Isaacs Problem 1B.1(a)**. `S` を Sylow `p`-部分群、`P` を `p`-部分群とすると、集合積
`P·S` が部分群 (= ある部分群 `K` の台と一致) であるための必要十分条件は `P ≤ S`。

⟸: `P ≤ S` なら `↑P·↑S = ↑S` (部分群の台)。⟹: `↑P·↑S` が部分群 `K` の台なら `S ≤ K` かつ
`P ≤ K`、`|K|·|P∩S| = |P|·|S|` (`card_mul_card_inf` = 1A.2/1A.3) より `|K| ∣ p^(a+b)` すなわち
`|K|` は `p` の冪。ゆえに `K` は `S` を含む `p`-部分群、Sylow の極大性 (`is_maximal'`) で `K = S`、
よって `P ≤ K = S`。 -/
theorem mul_isSubgroup_iff_le_sylow {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} (hP : IsPGroup p P) (S : Sylow p G) :
    (∃ K : Subgroup G, (K : Set G) = (P : Set G) * ((S : Subgroup G) : Set G))
      ↔ P ≤ (S : Subgroup G) := by
  constructor
  · rintro ⟨K, hK⟩
    -- S ≤ K かつ P ≤ K (1 ∈ P, 1 ∈ S ゆえ)
    have hSK : (S : Subgroup G) ≤ K := fun s hs => by
      rw [← SetLike.mem_coe, hK]; exact ⟨1, P.one_mem, s, hs, one_mul s⟩
    have hPK : P ≤ K := fun x hx => by
      rw [← SetLike.mem_coe, hK]; exact ⟨x, hx, 1, (S : Subgroup G).one_mem, mul_one x⟩
    -- |K|·|P∩S| = |P|·|S| = p^(a+b) ⟹ |K| ∣ p^(a+b) ⟹ K は p-群
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp S.isPGroup'
    have hmul := card_mul_card_inf P (S : Subgroup G)
    rw [← hK, SetLike.coe_sort_coe, ha, hb, ← pow_add] at hmul
    have hdvd : Nat.card K ∣ p ^ (a + b) := ⟨_, hmul.symm⟩
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
    -- Sylow の極大性で K = S、ゆえ P ≤ K = S
    have hKS : K = (S : Subgroup G) := S.is_maximal' (IsPGroup.of_card hc) hSK
    exact hKS ▸ hPK
  · intro hPS
    refine ⟨(S : Subgroup G), ?_⟩
    ext x
    simp only [SetLike.mem_coe, Set.mem_mul]
    constructor
    · intro hx; exact ⟨1, P.one_mem, x, hx, one_mul x⟩
    · rintro ⟨h, hh, k, hk, rfl⟩; exact (S : Subgroup G).mul_mem (hPS hh) hk

/-- 一般補題 (1B.4 の核): 有限群からの全射 `f : A ↠ B` と素数 `p ∣ |B|` に対し、`f` の核を含み
位数 `p·|ker f|` の部分群 `R` が存在する。`B` で Cauchy (`exists_prime_orderOf_dvd_card'`) を使い
位数 `p` の巡回部分群 `C` を取り、その逆像 `C.comap f` を `R` とする。指数計算
(`index_comap_of_surjective` + `card_mul_index`) で `|R| = p·|ker f|`。 -/
theorem exists_subgroup_card_eq_prime_mul_ker {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f) {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card B) :
    ∃ R : Subgroup A, f.ker ≤ R ∧ Nat.card R = p * Nat.card f.ker := by
  haveI : Finite B := Finite.of_surjective f hf
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' p hp
  set C : Subgroup B := Subgroup.zpowers b with hCdef
  have hCcard : Nat.card C = p := by rw [hCdef, Nat.card_zpowers, hb]
  refine ⟨C.comap f, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]; exact one_mem _
  · have hCidx_pos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have e1 : Nat.card (C.comap f) * C.index = Nat.card A := by
      rw [← Subgroup.index_comap_of_surjective (H := C) hf]; exact Subgroup.card_mul_index _
    have e2 : Nat.card C * C.index = Nat.card B := Subgroup.card_mul_index C
    have hkerB : f.ker.index = Nat.card B := by
      change Nat.card (A ⧸ f.ker) = Nat.card B
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
    have e3 : Nat.card f.ker * Nat.card B = Nat.card A := by
      rw [← hkerB]; exact Subgroup.card_mul_index f.ker
    apply Nat.eq_of_mul_eq_mul_right hCidx_pos
    rw [e1, ← e3, ← e2, hCcard]; ring

/-- **Isaacs Problem 1B.4**. `p`-部分群 `P` の指数 `|G:P|` が `p` で割れるならば、`P` を含み
`|Q:P| = p` (すなわち `|Q| = p·|P|`) となる部分群 `Q` が存在する。Sylow の定理を使わず Cauchy
の定理 (1A.8) から示す (Isaacs のヒント: `N_G(P)/P` を考える)。

`p ∣ |N_G(P):P|` (Problem 1A.10(b) = `prime_dvd_index_normalizer_of_prime_pow`) と `N_G(P)/P`
での Cauchy から `exists_subgroup_card_eq_prime_mul_ker` を適用し、逆像 `R ≤ N_G(P)` を `G` に
落として `Q` を得る。系 (下記 `isSylow_of_maximal_pGroup`): 極大 `p`-部分群は Sylow `p`-部分群。 -/
theorem exists_le_card_eq_prime_mul_of_prime_dvd_index {p : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] [Finite G] {P : Subgroup G} (hP : IsPGroup p P) (hdvd : p ∣ P.index) :
    ∃ Q : Subgroup G, P ≤ Q ∧ Nat.card Q = p * Nat.card P := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hPN : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
  -- p ∣ |N_G(P)/P|  (1A.10(b))
  have hpdvd := prime_dvd_index_normalizer_of_prime_pow (Fact.out : p.Prime) hn hdvd
  -- 逆像 R ≤ N_G(P) を helper で取る
  obtain ⟨R, hkerR, hRcard⟩ := exists_subgroup_card_eq_prime_mul_ker
    (QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))))
    (QuotientGroup.mk'_surjective _) hpdvd
  rw [QuotientGroup.ker_mk'] at hkerR hRcard
  refine ⟨R.map (Subgroup.normalizer (P : Set G)).subtype, ?_, ?_⟩
  · -- P ≤ Q: P = (P.subgroupOf N).map N.subtype ≤ R.map N.subtype
    have hPeq : (P.subgroupOf (Subgroup.normalizer (P : Set G))).map
        (Subgroup.normalizer (P : Set G)).subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPN]
    have hmono := Subgroup.map_mono (f := (Subgroup.normalizer (P : Set G)).subtype) hkerR
    rwa [hPeq] at hmono
  · -- |Q| = |R| = p·|P.subgroupOf N| = p·|P|
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hRcard,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv]

/-- **Isaacs Problem 1B.4** (系). `G` の極大 `p`-部分群 `P` (真に大きい `p`-部分群を持たない) の
指数 `|G:P|` は `p` で割れない。これが Sylow E-定理の Cauchy による別証明: mathlib では Sylow の
定義そのものが「極大 `p`-部分群」なので `P` は自動的に Sylow `p`-部分群 (`⟨P, hP, hmax⟩ : Sylow p G`)
であり、本補題はその指数が `p` と互いに素であること (= 位数計算による Sylow 性の特徴付け) を、
Sylow の定理を使わず 1B.4 の拡大補題から導く: `p ∣ |G:P|` ならば真に大きい `p`-部分群に拡大でき、
極大性に矛盾する。 -/
theorem not_dvd_index_of_maximal_pGroup {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} (hP : IsPGroup p P)
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → P ≤ Q → Q = P) :
    ¬ p ∣ P.index := by
  intro hdvd
  obtain ⟨Q, hPQ, hQcard⟩ := exists_le_card_eq_prime_mul_of_prime_dvd_index hP hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hQpg : IsPGroup p Q :=
    IsPGroup.of_card (show Nat.card Q = p ^ (n + 1) by rw [hQcard, hn, pow_succ'])
  rw [hmax Q hQpg hPQ, hn] at hQcard
  exact absurd (Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos n)
    (by rw [one_mul]; exact hQcard)) (Fact.out : p.Prime).one_lt.ne

end

/-! ## Problems 1B: mathlib / repo で被覆される演習 (docstring 記録)

- **Problem 1B.1(b)** (正規 Sylow は一意かつ characteristic): `S ⊴ G` が Sylow `p`-部分群なら
  `Sylp(G) = {S}`、さらに `S` は `G` で characteristic。前半は mathlib の
  `Sylow.unique_of_normal : P.Normal → Unique (Sylow p G)`、後半は
  `Sylow.characteristic_of_normal : P.Normal → P.Characteristic`
  (`Mathlib/GroupTheory/Sylow.lean`)。Isaacs は Sylow C-定理を使わない証明を要求するが
  (章の教育的制約)、形式化する対象は結果そのもの。

- **Problem 1B.2** (`O_p(G)` = 最大の正規 `p`-部分群): 本リポジトリの
  `OddOrder.Isaacs.Ch01.opCore p G` (= 全 Sylow `p`-部分群の共通部分) が `p`-部分群
  (`opCore_isPGroup`) かつ正規 (`opCore.normal`) かつ characteristic (`opCore.characteristic`)
  であり、任意の正規 `p`-部分群 `N` を含む (`normal_pgroup_le_opCore` = まさに Problem 1B.2)
  ことが `OddOrder/Isaacs/Ch01_Sylow/Basic.lean` で示されている。

- **Problem 1B.3** (Sylow 正規化群は自己正規化: `N = N_G(N)` where `N = N_G(S)`): mathlib の
  `Sylow.normalizer_normalizer : normalizer (normalizer (P : Set G)) = normalizer (P : Set G)`
  (`Mathlib/GroupTheory/Sylow.lean`) がまさにこれ。証明は Frattini 論法
  (`S ⊴ N` かつ 1B.1(b) で `N` 内の Sylow が一意 ⟹ `N_G(N) ⊆ N`)。
-/

section /- Problems 1B: Hall π-subgroups (1B.5-1B.8, Ch.3 の Hall/π 理論を前借り) -/

open OddOrder.Isaacs.Ch03

/-- **Isaacs Problem 1B.5(a)**. `θ : G ↠ K` が有限群の全射準同型で `H` が `G` の π-Hall 部分群
ならば、像 `θ(H)` (= `H.map θ`) は `K` の π-Hall 部分群。

`|θ(H)| ∣ |H|` (任意の準同型で `card_map_dvd`) より `|θ(H)|` の素因子 ⊆ `|H|` の素因子 ⊆ π。
`|K:θ(H)| ∣ |G:H|` (全射で `index_map_dvd`) より素因子は π を避ける。
(`IsHallSubgroup.map_quotient` = `θ = mk' N` の特殊化を全射一般に拡張。) -/
theorem IsHallSubgroup.map_of_surjective {G K : Type*} [Group G] [Group K] [Finite G]
    {π : Set ℕ} {θ : G →* K} (hθ : Function.Surjective θ) {H : Subgroup G}
    (hH : IsHallSubgroup π H) : IsHallSubgroup π (H.map θ) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · apply hH.1
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, hp.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩
  · apply hH.2
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, hp.2.1.trans (H.index_map_dvd hθ), Subgroup.index_ne_zero_of_finite⟩

/-- Sylow `p`-部分群は `{p}`-Hall 部分群 (`|S| = p^n`、`|G:S|` は `p` と互いに素)。 -/
theorem sylow_isHallSubgroup_singleton {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) : IsHallSubgroup ({p} : Set ℕ) (S : Subgroup G) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · rw [Nat.mem_primeFactors] at hq
    have hqS : q ∣ p ^ n := hn ▸ hq.2.1
    exact (Nat.prime_dvd_prime_iff_eq hq.1 Fact.out).mp (hq.1.dvd_of_dvd_pow hqS)
  · rw [Nat.mem_primeFactors] at hq
    intro (hqp : q = p)
    exact S.not_dvd_index (hqp ▸ hq.2.1)

/-- `{p}`-Hall 部分群は Sylow `p`-部分群 (橋渡しの逆): `IsHallSubgroup {p} H` なる `H` は
ある Sylow `p`-部分群と一致する。`H` は `p`-群 (`|H|` の素因子はすべて `p`)、Sylow `S ⊇ H` を
取ると `[S:H]` を割る素数は `p` (∣`|S|`) かつ `≠ p` (∣`[G:H]`) で矛盾 → `relIndex_eq_one` で `S ≤ H`。 -/
theorem exists_sylow_coe_eq_of_isHallSubgroup_singleton {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} (hH : IsHallSubgroup ({p} : Set ℕ) H) :
    ∃ S : Sylow p G, (S : Subgroup G) = H := by
  have hHp : IsPGroup p H := IsPGroup.of_card
    (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd =>
      hH.1 d (Nat.mem_primeFactors.mpr ⟨hd, hdvd, Nat.card_pos.ne'⟩))
  obtain ⟨S, hHS⟩ := hHp.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hHS⟩
  rw [← Subgroup.relIndex_eq_one]
  by_contra hne
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
  -- q ∣ [S:H] ∣ |S| = p^m ⟹ q = p
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq Fact.out).mp
    (hq.dvd_of_dvd_pow (hm ▸ hqdvd.trans (Subgroup.relIndex_dvd_card H S)))
  -- q ∣ [S:H] ∣ [G:H] ⟹ q ≠ p (H が {p}-Hall)
  exact hH.2 q (Nat.mem_primeFactors.mpr ⟨hq,
    hqdvd.trans (Subgroup.relIndex_dvd_index_of_le hHS), Subgroup.index_ne_zero_of_finite⟩) hqp

/-- `(MulAut.conj a)⁻¹` を元 `z` に作用させると `a⁻¹ z a` (共役)。`map_conj_smul` の補助。 -/
private theorem inv_conj_smul_apply {L : Type*} [Group L] (a z : L) :
    ((MulAut.conj a)⁻¹ • z : L) = a⁻¹ * z * a := by
  rw [← map_inv]; simp [MulAut.smul_def]

open Pointwise in
/-- 準同型は共役と可換: `θ(g H g⁻¹) = θ(g) · θ(H) · θ(g)⁻¹`。共役の pointwise 作用
`MulAut.conj g • H` と像の相互作用 (1B.5(b) で `θ(g • S₀) = θ(g) • θ(S₀)` に使用)。 -/
theorem map_conj_smul {G K : Type*} [Group G] [Group K] (θ : G →* K) (g : G) (H : Subgroup G) :
    (MulAut.conj g • H).map θ = MulAut.conj (θ g) • (H.map θ) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_conj_smul_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g⁻¹ * x * g, hx, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨g * x * g⁻¹, by rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]; exact hx,
      by rw [map_mul, map_mul, map_inv, hxy]; group⟩

open Pointwise in
/-- **Isaacs Problem 1B.5(b)**. `θ : G ↠ K` が有限群の全射で `T` が `K` の Sylow `p`-部分群
ならば、`T = θ(S)` となる `G` の Sylow `p`-部分群 `S` が存在する。

任意の Sylow `S₀ : Sylow p G` の像 `θ(S₀)` は `{p}`-Hall (1B.5(a) + `sylow_isHallSubgroup_singleton`)
なので Sylow `Q` を与える。`T`, `Q` は `K` で共役 `T = k • Q` (Sylow C)、`k = θ g` と書くと
`T = θ(g) • θ(S₀) = θ(g • S₀)` (`map_conj_smul`)、`S := g • S₀` が求めるもの。 -/
theorem exists_sylow_map_eq {G K : Type*} [Group G] [Group K] [Finite G]
    {θ : G →* K} (hθ : Function.Surjective θ) {p : ℕ} [Fact p.Prime] (T : Sylow p K) :
    ∃ S : Sylow p G, (S : Subgroup G).map θ = (T : Subgroup K) := by
  haveI : Finite K := Finite.of_surjective θ hθ
  obtain ⟨S₀⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  obtain ⟨Q, hQ⟩ := exists_sylow_coe_eq_of_isHallSubgroup_singleton
    (IsHallSubgroup.map_of_surjective hθ (sylow_isHallSubgroup_singleton S₀))
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q T
  obtain ⟨g, rfl⟩ := hθ k
  refine ⟨g • S₀, ?_⟩
  rw [Sylow.coe_subgroup_smul, map_conj_smul, ← hQ, ← Sylow.coe_subgroup_smul, hk]

/-- **Isaacs Problem 1B.5(c)**. `θ : G ↠ K` が有限群の全射ならば、各素数 `p` について
`|Syl_p(K)| ≤ |Syl_p(G)|`。1B.5(b) より `S ↦ (θ(S) を Sylow とみたもの)` が
`Syl_p(G) ↠ Syl_p(K)` の全射を与える。 -/
theorem card_sylow_le_of_surjective {G K : Type*} [Group G] [Group K] [Finite G]
    {θ : G →* K} (hθ : Function.Surjective θ) {p : ℕ} [Fact p.Prime] :
    Nat.card (Sylow p K) ≤ Nat.card (Sylow p G) := by
  haveI : Finite K := Finite.of_surjective θ hθ
  refine Nat.card_le_card_of_surjective
    (fun S : Sylow p G => (exists_sylow_coe_eq_of_isHallSubgroup_singleton
      (IsHallSubgroup.map_of_surjective hθ (sylow_isHallSubgroup_singleton S))).choose) ?_
  intro T
  obtain ⟨S, hS⟩ := exists_sylow_map_eq hθ T
  refine ⟨S, Sylow.ext ?_⟩
  rw [(exists_sylow_coe_eq_of_isHallSubgroup_singleton
    (IsHallSubgroup.map_of_surjective hθ (sylow_isHallSubgroup_singleton S))).choose_spec, hS]

open Pointwise in
/-- **Isaacs Problem 1B.6**. `H` を `G` の π-Hall 部分群、`K ≤ G` を部分群とする。`HK` が部分群
(ある `L : Subgroup G` の台が `↑H·↑K`) ならば `H ∩ K` は `K` の π-Hall 部分群
(`(H ⊓ K).subgroupOf K`)。

`|H∩K|` の素因子: `H∩K ≤ H` ゆえ `|H∩K| ∣ |H|`、`H` が π-Hall で `|H|` の素因子 ⊆ π。
`|K:H∩K|`: ダイヤモンド `|L|·|H∩K| = |H|·|K|` (1A.2/1A.3 `card_mul_card_inf`) と `H ≤ L` から
`|K:H∩K| = |L:H|` が `|G:H|` を割り、`H` が π-Hall で `|G:H|` の素因子は π を避ける。 -/
theorem isHallSubgroup_inf_of_mul_isSubgroup {π : Set ℕ} {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hH : IsHallSubgroup π H)
    (hHK : ∃ L : Subgroup G, (L : Set G) = (H : Set G) * (K : Set G)) :
    IsHallSubgroup π ((H ⊓ K).subgroupOf K) := by
  obtain ⟨L, hLeq⟩ := hHK
  have hHL : H ≤ L := fun x hx => by
    rw [← SetLike.mem_coe, hLeq]; exact ⟨x, hx, 1, K.one_mem, mul_one x⟩
  -- ダイヤモンド |L|·|H∩K| = |H|·|K|
  have ehk : Nat.card L * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
    have h := card_mul_card_inf H K
    rwa [← hLeq, SetLike.coe_sort_coe] at h
  -- |H|·|L:H| = |L|,  |H∩K|·|K:H∩K| = |K|
  have eL : Nat.card H * H.relIndex L = Nat.card ↥L := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
    exact Subgroup.card_mul_index (H.subgroupOf L)
  have eK : Nat.card ↥(H ⊓ K) * H.relIndex K = Nat.card K := by
    rw [← Subgroup.inf_relIndex_right (H := H) (K := K),
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)).toEquiv]
    exact Subgroup.card_mul_index ((H ⊓ K).subgroupOf K)
  -- |K:H∩K| = |L:H|
  have hrel_eq : H.relIndex K = H.relIndex L := by
    have key : Nat.card H * (Nat.card ↥(H ⊓ K) * H.relIndex L)
        = Nat.card H * (Nat.card ↥(H ⊓ K) * H.relIndex K) := by
      calc Nat.card H * (Nat.card ↥(H ⊓ K) * H.relIndex L)
          = Nat.card H * H.relIndex L * Nat.card ↥(H ⊓ K) := by ring
        _ = Nat.card ↥L * Nat.card ↥(H ⊓ K) := by rw [eL]
        _ = Nat.card H * Nat.card K := ehk
        _ = Nat.card H * (Nat.card ↥(H ⊓ K) * H.relIndex K) := by rw [eK]
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos
      (Nat.eq_of_mul_eq_mul_left Nat.card_pos key)).symm
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · -- |M| = |H∩K| ∣ |H|
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)).toEquiv] at hq
    exact hH.1 q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left)
      Nat.card_pos.ne' hq)
  · -- M.index = |K:H∩K| = |L:H| ∣ |G:H|
    have hMidx : ((H ⊓ K).subgroupOf K).index = H.relIndex K := Subgroup.inf_relIndex_right H K
    rw [hMidx, hrel_eq] at hq
    exact hH.2 q (Nat.primeFactors_mono (Subgroup.relIndex_dvd_index_of_le hHL)
      Subgroup.index_ne_zero_of_finite hq)

/-- **Isaacs Problem 1B.7(b)**. `O_π(G)` (= `oPiCore π G`) は `G` の任意の π-Hall 部分群 `H` に
含まれる。

`N := O_π(G)` は正規 π-群。`N ⊔ H` の指数 `[N⊔H : H] = H.relIndex (N⊔H)` を割る素数 `q` は、
`[N⊔H:H] ∣ |N⊔H| ∣ |N|·|H|` (`normal_mul` + `card_mul_card_inf`) より π に属し (`N`,`H` とも
π-群)、同時に `[N⊔H:H] ∣ |G:H|` (`H ≤ N⊔H`) より π を避ける (`H` が π-Hall) — 矛盾。よって
`[N⊔H:H] = 1`、`relIndex_eq_one` から `N⊔H ≤ H`、ゆえ `N ≤ N⊔H ≤ H`。 -/
theorem oPiCore_le_of_isHallSubgroup {π : Set ℕ} {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsHallSubgroup π H) : oPiCore π G ≤ H := by
  set N := oPiCore π G with hN
  haveI : N.Normal := by rw [hN]; infer_instance
  have hNpi : Subgroup.IsPiGroup π N := by rw [hN]; exact oPiCore.isPiGroup π
  have hsub : N ⊔ H ≤ H := by
    rw [← Subgroup.relIndex_eq_one]
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    -- q ∈ π : [N⊔H:H] ∣ |N⊔H| ∣ |N|·|H|、素因子は π
    have hcard_dvd : Nat.card ↥(N ⊔ H) ∣ Nat.card N * Nat.card H := by
      have hmul := card_mul_card_inf N H
      rw [← Subgroup.normal_mul N H, SetLike.coe_sort_coe] at hmul
      exact ⟨_, hmul.symm⟩
    have hqπ : q ∈ π := by
      have hq2 : q ∣ Nat.card N * Nat.card H :=
        (hqdvd.trans (Subgroup.relIndex_dvd_card H (N ⊔ H))).trans hcard_dvd
      rcases (Nat.Prime.dvd_mul hq).mp hq2 with h | h
      · exact hNpi q (Nat.mem_primeFactors.mpr ⟨hq, h, Nat.card_pos.ne'⟩)
      · exact hH.1 q (Nat.mem_primeFactors.mpr ⟨hq, h, Nat.card_pos.ne'⟩)
    -- q ∉ π : [N⊔H:H] ∣ |G:H|、素因子は π を避ける
    exact hH.2 q (Nat.mem_primeFactors.mpr ⟨hq,
      hqdvd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right),
      Subgroup.index_ne_zero_of_finite⟩) hqπ
  exact le_sup_left.trans hsub

open Pointwise in
/-- **Isaacs Problem 1B.7(c)**. `G` が π-Hall 部分群を持つとき、`O_π(G)` は `G` の全 π-Hall 部分群
の共通部分に一致する。

`⊇`: `O_π ≤` 各 π-Hall (1B.7(b)) より `O_π ≤ ⨅`。`⊆`: 交叉 `N := ⨅` は (i) π-群 (`N ≤ H₀` で
`|N| ∣ |H₀|`)、(ii) 正規 — 共役 `g` は π-Hall 族を並べ替える (`IsHallSubgroup.mulAut_smul`) ので
`g⁻¹xg ∈ 全 π-Hall ⟺ x ∈ 全 π-Hall`。正規 π-群ゆえ `N ≤ O_π` (1B.7(a) `le_oPiCore`)。 -/
theorem oPiCore_eq_iInf_isHallSubgroup {π : Set ℕ} {G : Type*} [Group G] [Finite G]
    (hne : ∃ H : Subgroup G, IsHallSubgroup π H) :
    oPiCore π G = ⨅ H : {H : Subgroup G // IsHallSubgroup π H}, (H : Subgroup G) := by
  obtain ⟨H₀, hH₀⟩ := hne
  have hmem : ∀ x : G,
      x ∈ (⨅ H : {H : Subgroup G // IsHallSubgroup π H}, (H : Subgroup G))
        ↔ ∀ H : {H : Subgroup G // IsHallSubgroup π H}, x ∈ (H : Subgroup G) :=
    fun _ => Subgroup.mem_iInf
  have hNle : (⨅ H : {H : Subgroup G // IsHallSubgroup π H}, (H : Subgroup G)) ≤ H₀ :=
    iInf_le _ (⟨H₀, hH₀⟩ : {H : Subgroup G // IsHallSubgroup π H})
  have hNpi : Subgroup.IsPiGroup π
      (⨅ H : {H : Subgroup G // IsHallSubgroup π H}, (H : Subgroup G)) :=
    fun q hq => hH₀.1 q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hNle) Nat.card_pos.ne' hq)
  haveI hNnorm : (⨅ H : {H : Subgroup G // IsHallSubgroup π H}, (H : Subgroup G)).Normal := by
    apply Subgroup.Normal.of_conjugate_fixed
    intro g
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hmem, hmem]
    constructor
    · intro h H
      have hh := h (⟨MulAut.conj g⁻¹ • (H : Subgroup G), H.2.mulAut_smul (MulAut.conj g⁻¹)⟩ :
        {H : Subgroup G // IsHallSubgroup π H})
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, smul_inv_smul] at hh
      exact hh
    · intro h H
      have hh := h (⟨MulAut.conj g • (H : Subgroup G), H.2.mulAut_smul (MulAut.conj g)⟩ :
        {H : Subgroup G // IsHallSubgroup π H})
      rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hh
  exact le_antisymm (le_iInf fun H => oPiCore_le_of_isHallSubgroup H.2) hNpi.le_oPiCore

/-! ### Problems 1B: mathlib / repo で被覆される Hall/π 演習 (docstring 記録)

- **Problem 1B.7(a)** (`O_π(G)` = 最大の正規 π-部分群): 本リポジトリの
  `OddOrder.Isaacs.Ch03.oPiCore π G` (= 正規 π-部分群の sup) が正規 (`oPiCore.normal`) かつ
  characteristic (`oPiCore.characteristic`) な π-部分群であり、任意の正規 π-部分群 `H` を含む
  (`Subgroup.IsPiGroup.le_oPiCore` = まさに Problem 1B.7(a)) ことが
  `OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean` で示されている。この一意最大性から
  `O_π(G)` は characteristic (Isaacs の Note)。1B.7(b) = `oPiCore_le_of_isHallSubgroup`、
  1B.7(c) = `oPiCore_eq_iInf_isHallSubgroup` (上に実証明)。
-/

end

end OddOrder.Isaacs.Ch01
