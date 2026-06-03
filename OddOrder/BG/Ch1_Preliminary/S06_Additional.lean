/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main
import OddOrder.GroupTheory.ThompsonSubgroup

/-!
# BG §6: Additional Results — the normal-J hub (FT critical)

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §6 (pp. 49-66), mmd `references/bg/local-analysis.mmd`
L1957-2128, **7 結果** (Thm 6.1, 6.2, 6.3, 6.4, 6.7 + Lem 6.5, 6.6).

§6 は局所解析の「道具袋」で、特に **Thm 6.2 `Z(J(S))·O_{p'}(G) ⊴ G`** が §7-§9
(Uniqueness) と App.A-C で **7+ 箇所**引用される FT クリティカルパスの核心。

## BG "**G**" 引用 → Isaacs FGT / mathlib / shared module 対応

CLAUDE.md no-wrapper policy 準拠: 完成済 Isaacs Ch.7 を直接呼ぶ。教科書間対応は本表に記録。

| BG | 内容 | Isaacs FGT / repo | 状態 |
|---|---|---|---|
| **Thm 6.1** | G solvable odd, S∈Syl_p ⇒ `O_{p',p}(G)` が S の全 abelian normal 部分群を含む | Thm 3.21 (Hall-Higman 1.2.3) `hall_higman_1_2_3` の系 / `normal_J` 中間補題 | core 完成 (本ファイル), 一般形 TODO |
| **Thm 6.2** | (normal-J) G solvable odd, S∈Syl_p ⇒ `Z(J(S))·O_{p'}(G) ⊴ G` | **Thm 7.6** `OddOrder.Isaacs.Ch07.normal_J` (odd-order 等価) | core 完成 (本ファイル, reduced case), 一般形 (O_{p'} 簡約) TODO |
| 6.3-6.7, 6.5-6.6 | solvable + p-length 1 + Frobenius factorization | Isaacs Ch.5/Ch.7 | TODO |

## このコミット (core results)

`OddOrder.Isaacs.Ch07.normal_J` は `P = C_G(Z(P))` + `O_{p'}(G) = ⊥` の **reduced
case** で `J(P) ⊴ G` を与える。本ファイルでは、その awkward な仮説のうち **奇数位数で
自動充足する 2 つ** を discharge する:

- `h2abelian` (Sylow-2 が可換) — 奇数位数では 2-部分群が自明 (`comm_of_isPGroup_two_of_odd`)。
- `h_pSolvable` (p-separable) — `[IsSolvable G]` から `isPiSeparable_of_solvable` instance で自動。

残る `O_{p'}(G) = ⊥` と `P = C_G(Z(P))` は reduced case の条件。BG Thm 6.2 の一般形
(`Z(J(S))·O_{p'}(G) ⊴ G`, 任意 S) は `O_{p'}(G)` で商を取り reduced case に簡約する
ステップが要る — 後続コミットで対応。
-/

namespace OddOrder.BG.Ch1.S06

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- 奇数位数群では `2`-部分群は自明、特に可換。

`OddOrder.Isaacs.Ch07.normal_J` の `h2abelian` 仮説 (Sylow-2 abelian) を奇数位数の下で
discharge するためのヘルパ。`IsPGroup 2 S` なら `|S| = 2^n` が奇数 `|G|` を割るので `n = 0`、
すなわち `S` は自明。 -/
private theorem comm_of_isPGroup_two_of_odd [Finite G]
    (hodd : Odd (Nat.card G)) :
    ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS x y
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hS
  have hdvd : Nat.card ↥S ∣ Nat.card G := S.card_subgroup_dvd_card
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hcard : Nat.card ↥S = 1 := by rw [hn, pow_zero]
    haveI : Subsingleton ↥S := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact Subsingleton.elim _ _
  · exfalso
    have h2dvd : (2 : ℕ) ∣ Nat.card G :=
      (dvd_pow_self 2 hnpos.ne').trans (hn ▸ hdvd)
    rw [Nat.odd_iff] at hodd
    omega

/-- **(infra)** `O_p(G) ≤ O_{p',p}(G)`: 正規 `p`-core は第 2 Fitting 層に含まれる。

BG Thm 6.1/6.2 が含意を `O_{p',p}(G)` で述べるための再利用可能な橋。`O_p(G)` の
`G ⧸ O_{p'}(G)` への像は正規 `{p}`-群なので `O_p(G ⧸ O_{p'}(G)) = O_{q∉{p}}(...)` に含まれ、
引き戻すと `O_{p',p}(G)`。 -/
theorem opCore_le_oPiPrimePiCore [Finite G] (p : ℕ) [Fact p.Prime] :
    Ch01.opCore p G ≤ Ch03.oPiPrimePiCore {p} G := by
  have hmap_le : (Ch01.opCore p G).map
      (QuotientGroup.mk' (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G)) ≤
      Ch03.oPiCore {p} (G ⧸ Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) := by
    haveI : ((Ch01.opCore p G).map
        (QuotientGroup.mk' (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G))).Normal :=
      (Ch01.opCore.normal p G).map _ (QuotientGroup.mk'_surjective _)
    apply Ch03.Subgroup.IsPiGroup.le_oPiCore
    have hpg : IsPGroup p ((Ch01.opCore p G).map
        (QuotientGroup.mk' (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G))) :=
      (Ch01.opCore_isPGroup p G).map _
    intro q hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    rw [hn, Nat.mem_primeFactors] at hq
    have hqp : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq.1 Fact.out).mp (hq.1.dvd_of_dvd_pow hq.2.1)
    rw [hqp]
    exact Set.mem_singleton p
  exact Subgroup.map_le_iff_le_comap.mp hmap_le

/-- **BG Thm 6.1 (core / reduced case)** = Isaacs Thm 7.6 中間結果の奇数位数特殊化。

奇数位数 solvable `G`、`p ≠ 2`、`P ∈ Syl_p(G)` で `O_{p'}(G) = ⊥` かつ `P = C_G(Z(P))`
のとき、Thompson 部分群 `J(P)` は `O_p(G)` に含まれる。

`O_{p'}(G) = ⊥` の下では `O_{p',p}(G) = O_p(G)` なので、これは BG Thm 6.1
(`O_{p',p}(G) ⊇` S の abelian normal 部分群) の `J(P)` インスタンス (reduced case)。 -/
theorem thompsonJ_le_opCore_of_odd [Finite G]
    (hodd : Odd (Nat.card G)) [IsSolvable G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hp2 : p ≠ 2)
    (h_oPiPrime_trivial : Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
      Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
        = (P : Subgroup G)) :
    Subgroup.thompsonJ (P : Subgroup G) p ≤ Ch01.opCore p G :=
  Ch07.thompsonJ_le_opCore_of_normal_J_hypotheses P hp2 inferInstance
    (comm_of_isPGroup_two_of_odd hodd) h_oPiPrime_trivial h_centralizer_center

/-- **BG Thm 6.2 (core / reduced case)** = Isaacs Thm 7.6 (`normal_J`) の奇数位数特殊化。

奇数位数 solvable `G`、`p ≠ 2`、`P ∈ Syl_p(G)` で `O_{p'}(G) = ⊥` かつ `P = C_G(Z(P))`
のとき、`J(P) ⊴ G`。

BG Thm 6.2 (`Z(J(S))·O_{p'}(G) ⊴ G`, 任意 S) の reduced case。一般形は `O_{p'}(G)` で商を
取り本定理に簡約する (後続コミット)。 -/
theorem normalJ_normal_of_odd [Finite G]
    (hodd : Odd (Nat.card G)) [IsSolvable G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hp2 : p ≠ 2)
    (h_oPiPrime_trivial : Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
      Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
        = (P : Subgroup G)) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal :=
  Ch07.normal_J P hp2 inferInstance
    (comm_of_isPGroup_two_of_odd hodd) h_oPiPrime_trivial h_centralizer_center

/-- **BG Thm 6.1 (J(P)-instance, O_{p',p} 形)**: `thompsonJ_le_opCore_of_odd` を橋
`opCore_le_oPiPrimePiCore` で `O_{p',p}(G)` 形に持ち上げたもの。

奇数 solvable `G`、`p ≠ 2`、`P ∈ Syl_p`、`O_{p'}(G) = ⊥`、`P = C_G(Z(P))` で
`J(P) ≤ O_{p',p}(G)`。BG Thm 6.1 (任意 abelian normal 部分群 ⊆ `O_{p',p}`) の `J(P)`
特殊形 (reduced case)。一般形は別途 (notes/bg/s06_additional.md 残課題 3)。 -/
theorem thompsonJ_le_oPiPrimePiCore_of_odd [Finite G]
    (hodd : Odd (Nat.card G)) [IsSolvable G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hp2 : p ≠ 2)
    (h_oPiPrime_trivial : Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (h_centralizer_center :
      Subgroup.centralizer
        (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
        = (P : Subgroup G)) :
    Subgroup.thompsonJ (P : Subgroup G) p ≤ Ch03.oPiPrimePiCore {p} G :=
  (thompsonJ_le_opCore_of_odd hodd P hp2 h_oPiPrime_trivial h_centralizer_center).trans
    (opCore_le_oPiPrimePiCore p)

/-! ## 6.5: 可解群の N/C 分解 (pp. 64-65, mmd L2048-2088)

**Lemma 6.5**: `K, U, H ≤ G` 可解, `K ⊴ G`, `G = KU`, `H ⊆ U`, `(|H|, |K|) = 1` のとき
(a) `H ∩ G' = H ∩ U'`, (b) `N_G(H) = C_K(H)·N_U(H)`, (c) `H^g ⊆ U ⇒ g = cu`
(`c ∈ C_K(H)`, `u ∈ U`)。§8 (`N_G(P)=LC_K(P)`), §10, §13, Thm 7.4(d) で多用。
原文どおり (b) は (c) から従い, (c) が本体 (Hall π-部分群の共役)。 -/

section /- 6.5 -/

open scoped Pointwise

variable [Finite G]

omit [Finite G] in
/-- 互いに素な位数の部分群は自明な交わりを持つ (`|H ⊓ K|` は `gcd(|H|, |K|) = 1` を割る)。 -/
private theorem inf_eq_bot_of_coprime_card {H K : Subgroup G}
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) : H ⊓ K = ⊥ := by
  have h1 : Nat.card ↥(H ⊓ K) ∣ Nat.card H := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(H ⊓ K) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
  have hone : Nat.card ↥(H ⊓ K) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  exact Subgroup.card_eq_one.mp hone

omit [Finite G] in
/-- `G = KU` (`K ⊴ G`) のとき `G' ≤ K · U'`: 商 `G/K` は `U` の像で生成され,
その像は可換 (`U'` が消える) なので `G/K` の commutator は像の commutator に一致。 -/
private theorem commutator_le_sup_commutator {K U : Subgroup G} [K.Normal]
    (hKU : K ⊔ U = ⊤) : commutator G ≤ K ⊔ ⁅U, U⁆ := by
  set q := QuotientGroup.mk' K with hq
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hkerq : q.ker = K := by rw [hq, QuotientGroup.ker_mk']
  have hmapK : K.map q = ⊥ := (Subgroup.map_eq_bot_iff K).mpr hkerq.ge
  have hmapU : U.map q = ⊤ := by
    have h := congrArg (Subgroup.map q) hKU
    rwa [Subgroup.map_sup, hmapK, bot_sup_eq, Subgroup.map_top_of_surjective _ hsurj] at h
  -- 両辺の `q`-像が `⁅⊤,⊤⁆` で一致
  have hmapeq : (commutator G).map q = (K ⊔ ⁅U, U⁆).map q := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.map_sup, hmapK,
      bot_sup_eq, Subgroup.map_commutator, hmapU]
  -- `K = ker q ≤ K ⊔ ⁅U,U⁆` ゆえ comap-map で復元
  calc commutator G ≤ Subgroup.comap q ((commutator G).map q) := Subgroup.le_comap_map _ _
    _ = Subgroup.comap q ((K ⊔ ⁅U, U⁆).map q) := by rw [hmapeq]
    _ = K ⊔ ⁅U, U⁆ := Subgroup.comap_map_eq_self (by rw [hkerq]; exact le_sup_left)

/-- **BG Lemma 6.5(a)** (mmd L2054): `G` 可解, `K ⊴ G`, `G = KU`, `H ≤ U`,
`(|H|, |K|) = 1` のとき `H ∩ G' = H ∩ U'`。 -/
theorem inf_commutator_eq_of_coprime [IsSolvable G] {K U H : Subgroup G} [K.Normal]
    (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    H ⊓ commutator G = H ⊓ ⁅U, U⁆ := by
  refine le_antisymm (le_inf inf_le_left ?_)
    (inf_le_inf_left H (Subgroup.commutator_mono le_top le_top))
  -- 残: `H ⊓ G' ≤ ⁅U,U⁆`。`d ∈ H ⊓ G'` を取り `d = k·b` (k ∈ U⊓K, b ∈ U') に分解,
  -- `U/U'` での像の位数が `|H|` と `|K|` の両方を割る ⟹ 1 ⟹ `d ∈ U'`。
  intro d hd
  rw [Subgroup.mem_inf] at hd
  obtain ⟨hdH, hdC⟩ := hd
  have hdU : d ∈ U := hHU hdH
  have hdKU : d ∈ K ⊔ ⁅U, U⁆ := commutator_le_sup_commutator hKU hdC
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hdKU
  obtain ⟨k, hkK, b, hbUU, hkb⟩ := hdKU
  have hbU : b ∈ U := Subgroup.commutator_le_self U hbUU
  have hkU : k ∈ U := by
    have hk_eq : k = d * b⁻¹ := by rw [← hkb]; group
    rw [hk_eq]; exact U.mul_mem hdU (U.inv_mem hbU)
  set φ := QuotientGroup.mk' (commutator ↥U) with hφ
  have hbcomm : (⟨b, hbU⟩ : ↥U) ∈ commutator ↥U := by
    rw [← Subgroup.map_subtype_commutator U] at hbUU
    obtain ⟨x, hx, hxb⟩ := hbUU
    have hxeq : x = ⟨b, hbU⟩ := Subtype.ext hxb
    rwa [hxeq] at hx
  have hφb : φ ⟨b, hbU⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hbcomm
  have hdkb : (⟨d, hdU⟩ : ↥U) = ⟨k, hkU⟩ * ⟨b, hbU⟩ := Subtype.ext hkb.symm
  have hφd : φ ⟨d, hdU⟩ = φ ⟨k, hkU⟩ := by rw [hdkb, map_mul, hφb, mul_one]
  have hord_d : orderOf (φ ⟨d, hdU⟩) ∣ Nat.card H := by
    refine (orderOf_map_dvd φ _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact H.orderOf_dvd_natCard hdH
  have hord_k : orderOf (φ ⟨d, hdU⟩) ∣ Nat.card K := by
    rw [hφd]
    refine (orderOf_map_dvd φ _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact K.orderOf_dvd_natCard hkK
  have hone : orderOf (φ ⟨d, hdU⟩) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hord_d hord_k)
  have hdcomm : (⟨d, hdU⟩ : ↥U) ∈ commutator ↥U :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hone)
  rw [← Subgroup.map_subtype_commutator U]
  exact ⟨⟨d, hdU⟩, hdcomm, rfl⟩

/-- **BG Lemma 6.5(c)** (mmd L2056): 上記仮定で, `g ∈ G` が `H^g ≤ U` を満たすなら
`g = c·u` (`c ∈ C_K(H)`, `u ∈ U`) と分解できる。 -/
theorem exists_mem_centralizerK_mul_of_conj_le [IsSolvable G] {K U H : Subgroup G} [K.Normal]
    (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    {g : G} (hg : H.map (MulAut.conj g).toMonoidHom ≤ U) :
    ∃ c ∈ Subgroup.centralizer (H : Set G) ⊓ K, ∃ u ∈ U, g = c * u := by
  sorry

/-- **BG Lemma 6.5(b)** (mmd L2055): 上記仮定で `N_G(H) = C_K(H)·N_U(H)` (集合等式)。 -/
theorem normalizer_eq_centralizerK_mul_normalizerU [IsSolvable G] {K U H : Subgroup G}
    [K.Normal] (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    SetLike.coe (Subgroup.normalizer H)
      = SetLike.coe (Subgroup.centralizer (H : Set G) ⊓ K)
        * SetLike.coe (Subgroup.normalizer H ⊓ U) := by
  sorry

end

end OddOrder.BG.Ch1.S06
