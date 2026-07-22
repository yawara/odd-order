/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.DoubleCoset

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

end OddOrder.Isaacs.Ch01
