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
import OddOrder.BG.Ch1_Preliminary.PLength
import Mathlib.Algebra.Group.Subgroup.Pointwise

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

/-- **Hall π-部分群の `↥V` 内共役** (BG Lem 6.5(c)/Thm 7.4(d) 共有 engine): `V` 可解で
`H₁, H₂ ≤ V` がともに `↥V` の `π`-Hall 部分群 (`subgroupOf` 形) なら、ある `w ∈ V` で
`w H₁ w⁻¹ = H₂` (pointwise 共役)。Isaacs Thm 3.21 (`Ch03.hall_C`, 可解群の π-Hall 共役性) を
`↥V → G` の `subtype` 像で `G` レベルへ持ち上げたもの。§7 Thm 7.4(d) と §6 Lem 6.5(c) の両方で使用。 -/
theorem exists_conj_eq_of_isHall_subgroupOf {V : Subgroup G}
    (hVsolv : IsSolvable ↥V) {π : Set ℕ} {H₁ H₂ : Subgroup G} (hH₁V : H₁ ≤ V) (hH₂V : H₂ ≤ V)
    (hH₁ : Ch03.IsHallSubgroup π (H₁.subgroupOf V))
    (hH₂ : Ch03.IsHallSubgroup π (H₂.subgroupOf V)) :
    ∃ w ∈ V, MulAut.conj w • H₁ = H₂ := by
  haveI := hVsolv
  obtain ⟨w, hw⟩ := Ch03.hall_C hH₁ hH₂
  refine ⟨(w : G), w.2, ?_⟩
  have hcomp : V.subtype.comp (MulAut.conj w).toMonoidHom
      = (MulAut.conj (w : G)).toMonoidHom.comp V.subtype := by
    ext x
    simp [MulAut.conj_apply]
  have h := congrArg (Subgroup.map V.subtype) hw
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hH₁V, Subgroup.map_subgroupOf_eq_of_le hH₂V] at h
  rw [Subgroup.pointwise_smul_def]
  exact h

omit [Finite G] in
/-- **(infra)** `x ∈ H.comap (MulAut.conj a) ↔ a*x*a⁻¹ ∈ H`. -/
private theorem mem_comap_conj {a x : G} {H : Subgroup G} :
    x ∈ H.comap (MulAut.conj a).toMonoidHom ↔ a * x * a⁻¹ ∈ H := by
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

omit [Finite G] in
/-- **(infra)** pointwise 共役 `MulAut.conj w • H` を comap 形 `H.comap (MulAut.conj w⁻¹)`
へ変換する橋。`exists_conj_eq_of_isHall_subgroupOf` の出力 (`smul`) を `comap` 計算へ載せる。 -/
private theorem conj_smul_eq_comap_conj_inv (w : G) (H : Subgroup G) :
    MulAut.conj w • H = H.comap (MulAut.conj w⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    mem_comap_conj]
  simp only [inv_inv]

omit [Finite G] in
/-- **(infra)** `H.comap (MulAut.conj (a*b)) = (H.comap (MulAut.conj a)).comap (MulAut.conj b)`. -/
private theorem comap_conj_mul (a b : G) (H : Subgroup G) :
    H.comap (MulAut.conj (a * b)).toMonoidHom
      = (H.comap (MulAut.conj a).toMonoidHom).comap (MulAut.conj b).toMonoidHom := by
  rw [Subgroup.comap_comap]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
/-- **(infra)** 共役同型による `comap` は位数を保つ: `|H.comap (conj k)| = |H|`. -/
private theorem card_comap_conj (k : G) (H : Subgroup G) :
    Nat.card (H.comap (MulAut.conj k).toMonoidHom) = Nat.card H := by
  rw [Subgroup.comap_equiv_eq_map_symm' (MulAut.conj k) H]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj k).symm.toMonoidHom)
    (MulAut.conj k).symm.injective

omit [Finite G] in
/-- **(infra)** `a ∈ H` なら `H.comap (MulAut.conj a) = H` (`H` 内元による共役は `H` を保つ). -/
private theorem comap_conj_self_of_mem {a : G} {H : Subgroup G} (ha : a ∈ H) :
    H.comap (MulAut.conj a).toMonoidHom = H := by
  have h := Subgroup.conj_smul_eq_self_of_mem (H := H) (h := a⁻¹) (H.inv_mem ha)
  rw [conj_smul_eq_comap_conj_inv, inv_inv] at h
  exact h

omit [Finite G] in
/-- **(infra)** `K ⊴ G`, `H ⊓ K = ⊥` のとき `|H ⊔ K| = |H| · |K|` (第二同型). -/
private theorem card_sup_eq_of_inf_bot {H K : Subgroup G} [K.Normal]
    (hHKbot : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  -- Lagrange for `K.subgroupOf (H⊔K)` inside `↥(H⊔K)`.
  have hlag := Subgroup.card_mul_index (K.subgroupOf (H ⊔ K))
  -- `|K.subgroupOf (H⊔K)| = |K|`.
  have hcardK : Nat.card (K.subgroupOf (H ⊔ K)) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv
  -- `(K.subgroupOf (H⊔K)).index = K.relIndex (H⊔K) = K.relIndex H`.
  have hidx : (K.subgroupOf (H ⊔ K)).index = Nat.card H := by
    have h1 : (K.subgroupOf (H ⊔ K)).index = K.relIndex (H ⊔ K) := rfl
    rw [h1, Subgroup.relIndex_sup_right]
    -- `K.relIndex H = (K.subgroupOf H).index`, and `K.subgroupOf H = ⊥`.
    have hbot : K.subgroupOf H = ⊥ :=
      Subgroup.subgroupOf_eq_bot.mpr (by rw [disjoint_iff, inf_comm]; exact hHKbot)
    change (K.subgroupOf H).index = Nat.card H
    rw [hbot, Subgroup.index_bot]
  rw [hcardK, hidx] at hlag
  -- `hlag : |K| * |H| = |H⊔K|`
  rw [← hlag, mul_comm]

/-- **(infra)** `W ≤ V := (H⊔K)⊓U` で `|W| = |H|` なら, `W.subgroupOf V` は
`π := primeFactors|H|`-Hall (内側 `↥V`)。両端 `H` と `g⁻¹Hg` をこの一本で処理する。 -/
private theorem isHall_subgroupOf_of_card_eq {K U H W : Subgroup G} [K.Normal]
    (hHKbot : H ⊓ K = ⊥) (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    (hWV : W ≤ (H ⊔ K) ⊓ U) (hWcard : Nat.card W = Nat.card H) :
    Ch03.IsHallSubgroup {p | p ∈ (Nat.card H).primeFactors}
      (W.subgroupOf ((H ⊔ K) ⊓ U)) := by
  set V : Subgroup G := (H ⊔ K) ⊓ U with hV
  have hWHK : W ≤ H ⊔ K := hWV.trans inf_le_left
  have hVHK : V ≤ H ⊔ K := inf_le_left
  -- `|W.subgroupOf V| = |W| = |H|`.
  have hcardWV : Nat.card (W.subgroupOf V) = Nat.card H := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWV).toEquiv, hWcard]
  -- `W.relIndex (H⊔K) = |K|`.
  have hWrelHK : W.relIndex (H ⊔ K) = Nat.card K := by
    have hlag := Subgroup.card_mul_index (W.subgroupOf (H ⊔ K))
    have hc : Nat.card (W.subgroupOf (H ⊔ K)) = Nat.card H := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWHK).toEquiv, hWcard]
    have hidx : (W.subgroupOf (H ⊔ K)).index = W.relIndex (H ⊔ K) := rfl
    rw [hc, hidx, card_sup_eq_of_inf_bot hHKbot] at hlag
    -- `hlag : |H| * W.relIndex (H⊔K) = |H| * |K|`
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hlag
  -- `W.relIndex V ∣ W.relIndex (H⊔K) = |K|`.
  have hdvd : W.relIndex V ∣ Nat.card K := by
    have hmul := Subgroup.relIndex_mul_relIndex W V (H ⊔ K) hWV hVHK
    rw [hWrelHK] at hmul
    exact ⟨V.relIndex (H ⊔ K), hmul.symm⟩
  refine ⟨?_, ?_⟩
  · -- cond1: primeFactors of |W.subgroupOf V| ⊆ π
    intro p hp
    rw [hcardWV] at hp
    exact hp
  · -- cond2: primeFactors of index ∉ π
    intro p hp hpπ
    have hidxV : (W.subgroupOf V).index = W.relIndex V := rfl
    rw [hidxV, Nat.mem_primeFactors] at hp
    -- `p ∣ |K|`
    have hpK : p ∣ Nat.card K := hp.2.1.trans hdvd
    -- `p ∣ |H|` from `p ∈ π`
    simp only [Set.mem_setOf_eq, Nat.mem_primeFactors] at hpπ
    have hpH : p ∣ Nat.card H := hpπ.2.1
    -- contradiction with coprimality
    have : p ∣ Nat.gcd (Nat.card H) (Nat.card K) := Nat.dvd_gcd hpH hpK
    rw [hcop.gcd_eq_one] at this
    exact hp.1.one_lt.ne' (Nat.dvd_one.mp this)

/-- **BG Lemma 6.5(c)** (mmd L2056): 上記仮定で, `g ∈ G` が `H^g = g⁻¹Hg ≤ U` を満たすなら
`g = c·u` (`c ∈ C_K(H)`, `u ∈ U`) と分解できる。`H^g` は BG 規約 `g⁻¹Hg`
(= `H.comap (MulAut.conj g)`)。 -/
theorem exists_mem_centralizerK_mul_of_conj_le [IsSolvable G] {K U H : Subgroup G} [K.Normal]
    (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    {g : G} (hg : H.comap (MulAut.conj g).toMonoidHom ≤ U) :
    ∃ c ∈ Subgroup.centralizer (H : Set G) ⊓ K, ∃ u ∈ U, g = c * u := by
  classical
  -- `H ⊓ K = ⊥` from coprimality.
  have hHKbot : H ⊓ K = ⊥ := inf_eq_bot_of_coprime_card hcop
  -- Step 1: decompose `g = k * v`, `k ∈ K`, `v ∈ U`.
  have hgmem : g ∈ K ⊔ U := by rw [hKU]; exact Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hgmem
  obtain ⟨k, hkK, v, hvU, hkv0⟩ := hgmem
  have hkv : k * v = g := hkv0
  -- abbreviation `Hk = k⁻¹Hk` (BG convention `comap (conj k)`)
  let Hk : Subgroup G := H.comap (MulAut.conj k).toMonoidHom
  have hHk : Hk = H.comap (MulAut.conj k).toMonoidHom := rfl
  -- Step 2: `Hk ≤ U`.  From `hg` with `g = k*v`: `Hk.comap (conj v) ≤ U`, then de-conjugate.
  have hgkv : H.comap (MulAut.conj g).toMonoidHom
      = Hk.comap (MulAut.conj v).toMonoidHom := by
    rw [hHk, ← comap_conj_mul, hkv]
  have hg' : Hk.comap (MulAut.conj v).toMonoidHom ≤ U := hgkv ▸ hg
  have hkU : Hk ≤ U := by
    intro z hz
    have hx : MulAut.conj v (v⁻¹ * z * v) ∈ Hk := by
      rw [MulAut.conj_apply]
      have heq : v * (v⁻¹ * z * v) * v⁻¹ = z := by group
      rwa [heq]
    have hzU' : v⁻¹ * z * v ∈ U := hg' (mem_comap_conj.mpr hx)
    have heq : z = v * (v⁻¹ * z * v) * v⁻¹ := by group
    rw [heq]; exact U.mul_mem (U.mul_mem hvU hzU') (U.inv_mem hvU)
  -- Step 3: `Hk ≤ H ⊔ K`. Each element of `Hk` is `k⁻¹ h k` with `h ∈ H ≤ H⊔K`, `k ∈ K ≤ H⊔K`.
  have hkHK : Hk ≤ H ⊔ K := by
    intro z hz
    rw [hHk, mem_comap_conj] at hz
    -- `k*z*k⁻¹ ∈ H`, so `z = k⁻¹*(k*z*k⁻¹)*k ∈ H⊔K`.
    have hzeq : z = k⁻¹ * (k * z * k⁻¹) * k := by group
    rw [hzeq]
    exact (H ⊔ K).mul_mem ((H ⊔ K).mul_mem
      ((H ⊔ K).inv_mem (Subgroup.mem_sup_right hkK)) (Subgroup.mem_sup_left hz))
      (Subgroup.mem_sup_right hkK)
  -- `H ≤ H ⊔ K`
  have hHHK : H ≤ H ⊔ K := le_sup_left
  -- Set `V := (H⊔K) ⊓ U`, and verify `H, Hk ≤ V`.
  set V : Subgroup G := (H ⊔ K) ⊓ U with hV
  have hHV : H ≤ V := le_inf hHHK hHU
  have hHkV : Hk ≤ V := le_inf hkHK hkU
  -- `|Hk| = |H|`
  have hcardHk : Nat.card Hk = Nat.card H := card_comap_conj k H
  -- Both `H` and `Hk` are π-Hall of `V`.
  have hHallH : Ch03.IsHallSubgroup {p | p ∈ (Nat.card H).primeFactors} (H.subgroupOf V) :=
    isHall_subgroupOf_of_card_eq hHKbot hcop hHV rfl
  have hHallHk : Ch03.IsHallSubgroup {p | p ∈ (Nat.card H).primeFactors} (Hk.subgroupOf V) :=
    isHall_subgroupOf_of_card_eq hHKbot hcop hHkV hcardHk
  -- Step 6: apply the conjugacy engine inside the solvable subgroup `↥V`.
  obtain ⟨w₀, hw₀V, hconj⟩ :=
    exists_conj_eq_of_isHall_subgroupOf (inferInstance : IsSolvable ↥V) hHV hHkV hHallH hHallHk
  -- `hconj : MulAut.conj w₀ • H = Hk`, i.e. in comap form `H.comap (conj w₀⁻¹) = Hk`.
  rw [conj_smul_eq_comap_conj_inv] at hconj
  -- so with `w := w₀⁻¹ ∈ V`: `H.comap (conj w) = Hk`.
  set w : G := w₀⁻¹ with hw
  have hwV : w ∈ V := V.inv_mem hw₀V
  have hconjw : H.comap (MulAut.conj w).toMonoidHom = Hk := hconj
  -- Step 8: reduce `w` to `K ⊓ U`. `↑V = ↑H * ↑(K ⊓ U)` (Dedekind), so `w = h₀ * c₀`.
  have hwmem : w ∈ (H : Set G) * (K ⊓ U : Subgroup G) := by
    have hVcoe : (V : Set G) = (H : Set G) * (K ⊓ U : Subgroup G) := by
      rw [Subgroup.mul_inf_assoc H K U hHU, ← Subgroup.mul_normal H K, hV, Subgroup.coe_inf]
    rw [← hVcoe]; exact hwV
  rw [Set.mem_mul] at hwmem
  obtain ⟨h₀, hh₀H, c₀, hc₀, hw_eq⟩ := hwmem
  rw [SetLike.mem_coe] at hh₀H hc₀
  -- `H.comap (conj c₀) = H.comap (conj w) = Hk` because `h₀ ∈ H` ⟹ `comap (conj h₀) H = H`.
  have hc₀conj : H.comap (MulAut.conj c₀).toMonoidHom = Hk := by
    rw [← hconjw, ← hw_eq, comap_conj_mul, comap_conj_self_of_mem hh₀H]
  -- `c₀ ∈ K` and `c₀ ∈ U`.
  have hc₀K : c₀ ∈ K := (Subgroup.mem_inf.mp hc₀).1
  have hc₀U : c₀ ∈ U := (Subgroup.mem_inf.mp hc₀).2
  -- Step 9: build `c := k * c₀⁻¹` and `u := c₀ * v`.
  refine ⟨k * c₀⁻¹, ?_, c₀ * v, U.mul_mem hc₀U hvU, ?_⟩
  · -- `c = k * c₀⁻¹ ∈ centralizer (H) ⊓ K`.
    rw [Subgroup.mem_inf]
    refine ⟨?_, K.mul_mem hkK (K.inv_mem hc₀K)⟩
    -- First: `c` normalizes `H`, i.e. `H.comap (conj c) = H`.
    -- `H.comap (conj k) = H.comap (conj c₀)` (= Hk), so conjugating back by `c₀⁻¹` fixes `H`.
    have hcNorm : H.comap (MulAut.conj (k * c₀⁻¹)).toMonoidHom = H := by
      have hkc₀ : H.comap (MulAut.conj k).toMonoidHom = H.comap (MulAut.conj c₀).toMonoidHom :=
        (hc₀conj.trans hHk).symm
      rw [comap_conj_mul, hkc₀, ← comap_conj_mul]
      -- now `H.comap (conj (c₀ * c₀⁻¹)) = H`
      have h1 : c₀ * c₀⁻¹ = (1 : G) := mul_inv_cancel c₀
      rw [h1]
      ext x; rw [mem_comap_conj]; simp
    -- `c⁻¹ H c = H` as well (apply `hcNorm` with `c⁻¹`).
    have hcNormInv : H.comap (MulAut.conj (k * c₀⁻¹)⁻¹).toMonoidHom = H := by
      have h2 := comap_conj_mul (k * c₀⁻¹) (k * c₀⁻¹)⁻¹ H
      rw [mul_inv_cancel, hcNorm] at h2
      -- `h2 : H.comap (conj 1) = H.comap (conj (k*c₀⁻¹)⁻¹)`
      have h3 : H.comap (MulAut.conj (1 : G)).toMonoidHom = H := by
        ext x; rw [mem_comap_conj]; simp
      rw [h3] at h2; exact h2.symm
    -- Now show centralizer membership.
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    -- `d := c⁻¹ * h * c * h⁻¹ ∈ H ⊓ K = ⊥`.
    set c : G := k * c₀⁻¹ with hc
    -- `c⁻¹ * h * c ∈ H` from `hcNormInv`.
    have hconjH : c⁻¹ * h * c ∈ H := by
      have : h ∈ H.comap (MulAut.conj c⁻¹).toMonoidHom := by rw [hcNormInv]; exact hh
      rw [mem_comap_conj] at this
      -- `this : c⁻¹ * h * (c⁻¹)⁻¹ ∈ H`
      rwa [inv_inv] at this
    have hdH : c⁻¹ * h * c * h⁻¹ ∈ H := H.mul_mem hconjH (H.inv_mem hh)
    -- `d ∈ K`: `c ∈ K`, `K` normal ⟹ `h * c * h⁻¹ ∈ K`, so `c⁻¹ * (h*c*h⁻¹) ∈ K`.
    have hcK : c ∈ K := K.mul_mem hkK (K.inv_mem hc₀K)
    have hdK : c⁻¹ * h * c * h⁻¹ ∈ K := by
      have hconjK : h * c * h⁻¹ ∈ K := by
        have := (‹K.Normal›.conj_mem c hcK h)
        simpa [mul_assoc] using this
      have heq : c⁻¹ * h * c * h⁻¹ = c⁻¹ * (h * c * h⁻¹) := by group
      rw [heq]; exact K.mul_mem (K.inv_mem hcK) hconjK
    -- `d = 1`.
    have hd1 : c⁻¹ * h * c * h⁻¹ = 1 := by
      have : c⁻¹ * h * c * h⁻¹ ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hdH, hdK⟩
      rw [hHKbot, Subgroup.mem_bot] at this
      exact this
    -- conclude `h * c = c * h`.
    have : c⁻¹ * h * c = h := by
      have := mul_eq_one_iff_eq_inv.mp hd1
      -- `this : c⁻¹ * h * c = (h⁻¹)⁻¹ = h`
      rwa [inv_inv] at this
    -- so `h * c = c * h`
    have hgoal : h * c = c * h := by
      have h4 : c * (c⁻¹ * h * c) = c * h := by rw [this]
      calc h * c = c * (c⁻¹ * h * c) := by group
        _ = c * h := by rw [this]
    exact hgoal
  · -- `g = c * u`: `(k * c₀⁻¹) * (c₀ * v) = k * v = g`.
    rw [← hkv]; group

omit [Finite G] in
/-- 集合 `H` の中心化群は `H` (部分群) の正規化群に含まれる (`c` が各 `h∈H` と可換 ⟹
`c·h·c⁻¹ = h ∈ H`)。 -/
private theorem centralizer_set_le_normalizer (H : Subgroup G) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer H := by
  intro c hc
  have hcomm : ∀ h ∈ H, h * c = c * h := fun h hh =>
    Subgroup.mem_centralizer_iff.mp hc h hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have he : c * h * c⁻¹ = h := by rw [← hcomm h hh]; group
    rw [he]; exact hh
  · intro hh
    have he : h = c * h * c⁻¹ := by
      have h2 : c * h = c * (c * h * c⁻¹) := by rw [← hcomm _ hh]; group
      exact mul_left_cancel h2
    rw [he]; exact hh

/-- **BG Lemma 6.5(b)** (mmd L2055): 上記仮定で `N_G(H) = C_K(H)·N_U(H)` (集合等式)。
原文どおり (c) から従う: `n ∈ N_G(H)` は `n⁻¹Hn = H ≤ U` で (c) を満たし `n = cu`,
`u = c⁻¹n ∈ N_G(H) ⊓ U = N_U(H)`。逆は両因子が `N_G(H)` 内ゆえ自明。 -/
theorem normalizer_eq_centralizerK_mul_normalizerU [IsSolvable G] {K U H : Subgroup G}
    [K.Normal] (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    SetLike.coe (Subgroup.normalizer H)
      = SetLike.coe (Subgroup.centralizer (H : Set G) ⊓ K)
        * SetLike.coe (Subgroup.normalizer H ⊓ U) := by
  apply Set.Subset.antisymm
  · intro n hn
    rw [SetLike.mem_coe] at hn
    have hcn : H.comap (MulAut.conj n).toMonoidHom ≤ U := by
      intro x hx
      rw [Subgroup.mem_comap] at hx
      exact hHU (((Subgroup.mem_normalizer_iff.mp hn) x).mpr hx)
    obtain ⟨c, hc, u, hu, hnu⟩ := exists_mem_centralizerK_mul_of_conj_le hKU hHU hcop hcn
    have hcN : c ∈ Subgroup.normalizer H := centralizer_set_le_normalizer H (Subgroup.mem_inf.mp hc).1
    have huN : u ∈ Subgroup.normalizer H := by
      have hue : u = c⁻¹ * n := by rw [hnu]; group
      rw [hue]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcN) hn
    rw [Set.mem_mul]
    exact ⟨c, SetLike.mem_coe.mpr hc, u,
      SetLike.mem_coe.mpr (Subgroup.mem_inf.mpr ⟨huN, hu⟩), hnu.symm⟩
  · rintro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨c, hc, u, hu, rfl⟩ := hx
    rw [SetLike.mem_coe] at hc hu ⊢
    exact Subgroup.mul_mem _ (centralizer_set_le_normalizer H (Subgroup.mem_inf.mp hc).1)
      (Subgroup.mem_inf.mp hu).1

end

/-! ## 6.6: p-length 1 characterization (pp. 65-66, mmd L2089-2128)

**Lemma 6.6** (BG p.65): `G` 可解で `p`-length 1, `S ∈ Syl_p(G)`. 書く `M = O_{p'}(G)`,
`N = O_{p',p}(G)`。`p`-length 1 ⟺ `G/N` が `p'`-群。このとき:

- **(foundation)** `N = M · S` (= `O_{p'}(G) ⊔ S`): `S` の `G/M` への像は `G/M` の `p`-Hall
  (= `O_p(G/M)` を含む正規 `p`-群と一致) ゆえ `O_p(G/M) ≤ SM/M`, 引き戻して `N ≤ MS`;
  逆は `M ≤ N` (下層) と `S ≤ N` (`G/N` が `p'` ⟹ `S` の `G/N` 像は自明)。
- **(1b)** `G = O_{p'}(G) · N_G(S)` (Frattini, `N` の中の Sylow `S` に適用 + `N = MS`)。
- **(2)** `S ≤ G' ⟹ S ≤ N_G(S)'` (Lem 6.5(a), `K = M`, `U = N_G(S)`)。
- **(3)** `Y ⊆ S`, `Y^x ⊆ S` ⟹ `x = c·g` (`c ∈ C_G(Y)`, `g ∈ N_G(S)`) (Lem 6.5(c))。
- **(4)** `Q` `p`-部分群 ⟹ `∃ x ∈ C_G(Q ⊓ S)`, `Q^x ⊆ S` (`Q ≤ N`, `N` 内 Sylow 共役)。

§8 (`N_G(P) = L·C_K(P)`), §10, §13 で `p`-length 1 の局所構造として多用。 -/

section /- 6.6 -/

open scoped Pointwise

open OddOrder.BG.Ch1 (hasPLengthOne)

variable [Finite G] [IsSolvable G] {p : ℕ} [Fact p.Prime]

omit [IsSolvable G] in
/-- `M := O_{p'}(G)` は `p'`-群: `|M|` は `p` と互いに素 (`oPiCore.isPiGroup` で
全素因子が `≠ p`)。`inf_eq_bot_of_pGroup_coprime` 等への入力。 -/
private theorem card_oPiPrimeCore_coprime_prime :
    (Nat.card (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G)).Coprime p := by
  have hpi : Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)}
      (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) := Ch03.oPiCore.isPiGroup _
  have hndvd : ¬ p ∣ Nat.card (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) := by
    intro hdvd
    have hmem : p ∈ (Nat.card (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
    exact (hpi p hmem) rfl
  exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hndvd))

omit [IsSolvable G] in
/-- `S ∈ Syl_p` と `M = O_{p'}(G)` の位数は互いに素 (`p`-群 vs `p'`-群)。 -/
private theorem sylow_card_coprime_oPiPrimeCore (S : Sylow p G) :
    Nat.Coprime (Nat.card (S : Subgroup G))
      (Nat.card (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G)) := by
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  rw [hn]
  exact (card_oPiPrimeCore_coprime_prime (p := p) (G := G)).symm.pow_left n

omit [IsSolvable G] in
/-- `S ∈ Syl_p` と `M = O_{p'}(G)` は交わらない (`S` は `p`-群, `M` は `p'`-群)。 -/
private theorem sylow_inf_oPiPrimeCore_eq_bot (S : Sylow p G) :
    (S : Subgroup G) ⊓ Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥ :=
  inf_eq_bot_of_coprime_card (sylow_card_coprime_oPiPrimeCore S)

omit [Finite G] [IsSolvable G] in
/-- 商写像 `mk' M` による像の位数は不変, ただし `T ⊓ M = ⊥` のとき: `|T.map (mk' M)| = |T|`。
`relIndex_ker` (`ker (mk' M) = M`) で `|T.map q| = M.relIndex T = (M.subgroupOf T).index`,
`T ⊓ M = ⊥ ⟹ M.subgroupOf T = ⊥` ゆえ index = `|T|`。 -/
private theorem card_map_mk'_eq_of_inf_bot {M T : Subgroup G} [M.Normal]
    (hbot : T ⊓ M = ⊥) :
    Nat.card (T.map (QuotientGroup.mk' M)) = Nat.card T := by
  have hker : (QuotientGroup.mk' M).ker = M := QuotientGroup.ker_mk' M
  have h1 : Nat.card (T.map (QuotientGroup.mk' M)) = M.relIndex T := by
    rw [← Subgroup.relIndex_ker, hker]
  have hbot' : M.subgroupOf T = ⊥ :=
    Subgroup.subgroupOf_eq_bot.mpr (by rw [disjoint_iff, inf_comm]; exact hbot)
  rw [h1]
  change (M.subgroupOf T).index = Nat.card T
  rw [hbot', Subgroup.index_bot]

omit [IsSolvable G] in
/-- `p`-length 1 のもとで, 任意の `p`-部分群は `N = O_{p',p}(G)` に含まれる。
`Q` の `G/N` への像は `p`-群かつ `|G/N|` (= `p` と互いに素, by `hpl1`) を割るので自明 ⟹
`Q ≤ ker (mk' N) = N`。`S ≤ N` (foundation/Frattini) と `Q ≤ N` (Lem 6.6(4)) で共有。 -/
private theorem pGroup_le_oPiPrimePiCore {Q : Subgroup G} (hQ : IsPGroup p Q)
    (hpl1 : hasPLengthOne p G) :
    Q ≤ Ch03.oPiPrimePiCore {p} G := by
  set N : Subgroup G := Ch03.oPiPrimePiCore {p} G with hN
  set q : G →* G ⧸ N := QuotientGroup.mk' N with hq
  -- `Q.map q` is a `p`-group whose card divides `|G/N|`, which is coprime to `p`.
  have hpg : IsPGroup p (Q.map q) := hQ.map q
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hdvd : Nat.card (Q.map q) ∣ Nat.card (G ⧸ N) :=
    Subgroup.card_subgroup_dvd_card (Q.map q)
  have hcop : Nat.Coprime (Nat.card (Q.map q)) (Nat.card (G ⧸ N)) := by
    rw [hn]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpl1).pow_left n
  have hcard1 : Nat.card (Q.map q) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  have hmapbot : Q.map q = ⊥ := Subgroup.card_eq_one.mp hcard1
  have hle : Q ≤ q.ker := (Subgroup.map_eq_bot_iff Q).mp hmapbot
  rwa [hq, QuotientGroup.ker_mk'] at hle

omit [IsSolvable G] in
/-- **BG Lemma 6.6 (foundation)**: `p`-length 1 のもとで `O_{p',p}(G) = O_{p'}(G) · S`
(= `O_{p'}(G) ⊔ S`)。

`⊇`: `O_{p'}(G) ≤ N` (下層), `S ≤ N` (`pGroup_le_oPiPrimePiCore`)。
`⊆`: `S` の `G/M` への像 (`M = O_{p'}(G)`) は `p`-Hall (= `p`-群 + index が `p` と互いに素;
後者は `|S| = |S.map q|` (∵ `S ⊓ M = ⊥`) が `|G|` の `p`-part, `p ∤ S.index`)。ゆえ
`O_p(G/M) ≤ S.map q` (`normal_le_hall`), 引き戻して `N = (O_p(G/M)).comap q ≤ S ⊔ M`. -/
theorem oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G) :
    Ch03.oPiPrimePiCore {p} G
      = Ch03.oPiCore {q | q ∉ ({p}:Set ℕ)} G ⊔ (S : Subgroup G) := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  set N : Subgroup G := Ch03.oPiPrimePiCore {p} G with hN
  set q : G →* G ⧸ M := QuotientGroup.mk' M with hq
  have hqker : q.ker = M := by rw [hq, QuotientGroup.ker_mk']
  -- `S ⊓ M = ⊥`
  have hSMbot : (S : Subgroup G) ⊓ M = ⊥ := sylow_inf_oPiPrimeCore_eq_bot S
  -- `S ≤ N` (from `p`-length 1)
  have hSN : (S : Subgroup G) ≤ N := pGroup_le_oPiPrimePiCore S.isPGroup' hpl1
  refine le_antisymm ?_ ?_
  · -- ⊆ direction: `N ≤ M ⊔ S`
    -- `S.map q` is a `p`-Hall subgroup of `G/M`.
    have hpg : IsPGroup p ((S : Subgroup G).map q) := S.isPGroup'.map q
    -- card of `S.map q` equals card S.
    have hcardSmap : Nat.card ((S : Subgroup G).map q) = Nat.card (S : Subgroup G) :=
      card_map_mk'_eq_of_inf_bot hSMbot
    -- cond1: prime factors ⊆ {p}
    have hcond1 : ∀ r ∈ (Nat.card ((S : Subgroup G).map q)).primeFactors, r ∈ ({p} : Set ℕ) := by
      intro r hr
      obtain ⟨n, hn⟩ := hpg.exists_card_eq
      rw [hn, Nat.mem_primeFactors] at hr
      have hrp : r = p :=
        (Nat.prime_dvd_prime_iff_eq hr.1 Fact.out).mp (hr.1.dvd_of_dvd_pow hr.2.1)
      rw [hrp]; exact Set.mem_singleton p
    -- cond2: `p ∤ (S.map q).index`
    have hidx_dvd : ((S : Subgroup G).map q).index ∣ (S : Subgroup G).index := by
      -- `card(S.map q) * (S.map q).index = card(G/M)`,  `card(G/M) * card M = card G`,
      -- `card S * S.index = card G`,  `card(S.map q) = card S`.
      have hA : Nat.card ((S : Subgroup G).map q) * ((S : Subgroup G).map q).index
          = Nat.card (G ⧸ M) := Subgroup.card_mul_index _
      have hB : Nat.card (G ⧸ M) * Nat.card M = Nat.card G := by
        have h := M.card_mul_index
        rw [Subgroup.index_eq_card, mul_comm] at h
        exact h
      have hC : Nat.card (S : Subgroup G) * (S : Subgroup G).index = Nat.card G :=
        Subgroup.card_mul_index _
      -- combine: `card S * ((S.map q).index * card M) = card S * S.index`
      refine ⟨Nat.card M, ?_⟩
      have hkey : Nat.card (S : Subgroup G) * (((S : Subgroup G).map q).index * Nat.card M)
          = Nat.card (S : Subgroup G) * (S : Subgroup G).index := by
        have step1 : Nat.card (S : Subgroup G) * ((S : Subgroup G).map q).index
            = Nat.card (G ⧸ M) := by rw [← hcardSmap]; exact hA
        calc Nat.card (S : Subgroup G) * (((S : Subgroup G).map q).index * Nat.card M)
            = (Nat.card (S : Subgroup G) * ((S : Subgroup G).map q).index) * Nat.card M := by
              rw [mul_assoc]
          _ = Nat.card (G ⧸ M) * Nat.card M := by rw [step1]
          _ = Nat.card G := hB
          _ = Nat.card (S : Subgroup G) * (S : Subgroup G).index := hC.symm
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hkey.symm
    have hcond2 : ∀ r ∈ ((S : Subgroup G).map q).index.primeFactors, r ∉ ({p} : Set ℕ) := by
      intro r hr hrp
      rw [Set.mem_singleton_iff] at hrp
      rw [Nat.mem_primeFactors] at hr
      have hpidxS : p ∣ (S : Subgroup G).index := (hrp ▸ hr.2.1).trans hidx_dvd
      exact S.not_dvd_index hpidxS
    have hHall : Ch03.IsHallSubgroup ({p} : Set ℕ) ((S : Subgroup G).map q) := ⟨hcond1, hcond2⟩
    -- `O_p(G/M) ≤ S.map q`
    have hOple : Ch03.oPiCore ({p} : Set ℕ) (G ⧸ M) ≤ (S : Subgroup G).map q :=
      Ch03.Subgroup.IsPiGroup.normal_le_hall (Ch03.oPiCore.isPiGroup _) hHall
    -- `N = (O_p(G/M)).comap q`
    have hNdef : N = (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ M)).comap q := rfl
    rw [hNdef]
    calc (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ M)).comap q
        ≤ ((S : Subgroup G).map q).comap q := Subgroup.comap_mono hOple
      _ = (S : Subgroup G) ⊔ q.ker := Subgroup.comap_map_eq q (S : Subgroup G)
      _ = (S : Subgroup G) ⊔ M := by rw [hqker]
      _ = M ⊔ (S : Subgroup G) := sup_comm _ _
  · -- ⊇ direction: `M ⊔ S ≤ N`
    refine sup_le ?_ hSN
    rw [hM, hN]
    exact Ch03.oPiCore_compl_le_oPiPrimePiCore {p} G

/-- **BG Lemma 6.6(1b)** (mmd L2092): `p`-length 1 で `G = O_{p'}(G) · N_G(S)`.

Frattini を `N = O_{p',p}(G)` の中の Sylow `S` に適用すると `N_G(S) · N = G`。foundation で
`N = M ⊔ S`, `S ≤ N_G(S)` ゆえ `S` は吸収され `N_G(S) ⊔ M ⊔ S = N_G(S) ⊔ M = G`。 -/
theorem top_eq_oPiPrimeCore_sup_normalizer_sylow (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G) :
    (⊤ : Subgroup G)
      = Ch03.oPiCore {q | q ∉ ({p}:Set ℕ)} G ⊔ Subgroup.normalizer (S : Subgroup G) := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  -- `S ≤ N`, so Frattini in `G` (with `N = O_{p',p}(G)` normal) applies.
  have hSN : (S : Subgroup G) ≤ Ch03.oPiPrimePiCore {p} G :=
    pGroup_le_oPiPrimePiCore S.isPGroup' hpl1
  have hFrattini : Subgroup.normalizer (S : Subgroup G) ⊔ Ch03.oPiPrimePiCore {p} G = ⊤ :=
    Sylow.normalizer_sup_eq_top' S hSN
  -- rewrite `N = M ⊔ S`
  rw [oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow S hpl1, ← hM] at hFrattini
  -- `N_G(S) ⊔ (M ⊔ S) = N_G(S) ⊔ M` because `S ≤ N_G(S)`.
  have hSnorm : (S : Subgroup G) ≤ Subgroup.normalizer (S : Subgroup G) := Subgroup.le_normalizer
  have habsorb : Subgroup.normalizer (S : Subgroup G) ⊔ (M ⊔ (S : Subgroup G))
      = Subgroup.normalizer (S : Subgroup G) ⊔ M := by
    rw [sup_comm M (S : Subgroup G), ← sup_assoc, sup_eq_left.mpr hSnorm]
  rw [habsorb] at hFrattini
  rw [← hFrattini, sup_comm]

/-- **BG Lemma 6.6(2)** (mmd L2096): `p`-length 1 で `S ≤ G' ⟹ S ≤ N_G(S)'`.

Lem 6.5(a) を `K = O_{p'}(G)`, `U = N_G(S)`, `H = S` に適用すると
`S ∩ G' = S ∩ N_G(S)'`。仮定 `S ≤ G'` で左辺 `= S` ゆえ `S ≤ N_G(S)'`。 -/
theorem sylow_le_commutator_normalizer_of_le_commutator (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G)
    (hS : (S : Subgroup G) ≤ commutator G) :
    (S : Subgroup G)
      ≤ ⁅(Subgroup.normalizer (S : Subgroup G) : Subgroup G),
          (Subgroup.normalizer (S : Subgroup G) : Subgroup G)⁆ := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  -- `M ⊔ N_G(S) = ⊤` from (1b).
  have hKU : M ⊔ Subgroup.normalizer (S : Subgroup G) = ⊤ :=
    (top_eq_oPiPrimeCore_sup_normalizer_sylow S hpl1).symm
  have hHU : (S : Subgroup G) ≤ Subgroup.normalizer (S : Subgroup G) := Subgroup.le_normalizer
  have hcop : Nat.Coprime (Nat.card (S : Subgroup G)) (Nat.card M) :=
    sylow_card_coprime_oPiPrimeCore S
  -- Lem 6.5(a): `S ⊓ G' = S ⊓ ⁅N_G(S), N_G(S)⁆`.
  have hinf := inf_commutator_eq_of_coprime (H := (S : Subgroup G)) hKU hHU hcop
  -- `S ⊓ G' = S` since `S ≤ G'`, so `S = S ⊓ ⁅N,N⁆ ≤ ⁅N,N⁆`.
  rw [inf_eq_left.mpr hS] at hinf
  exact le_of_eq hinf |>.trans inf_le_right

/-- **BG Lemma 6.6(3)** (mmd L2098): `p`-length 1, `Y ⊆ S` 非空, `Y^x ⊆ S` (= `x⁻¹Yx ⊆ S`)
ならば `x = c·g` (`c ∈ C_G(Y)`, `g ∈ N_G(S)`)。

Lem 6.5(c) を `K = O_{p'}(G)`, `U = N_G(S)`, `H = ⟨Y⟩`, `g = x` に適用。`⟨Y⟩ ≤ S ≤ N_G(S)`,
`⟨Y⟩^x = ⟨x⁻¹Yx⟩ ≤ S ≤ N_G(S)` (`hYx`)。出力 `c ∈ C_G(⟨Y⟩) ⊓ M ≤ C_G(Y)`。 -/
theorem exists_mem_centralizer_mul_normalizer_of_conj_subset_sylow (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G)
    {Y : Set G} (hYne : Y.Nonempty) (hYS : Y ⊆ (S : Subgroup G))
    {x : G} (hYx : ∀ y ∈ Y, x⁻¹ * y * x ∈ (S : Subgroup G)) :
    ∃ c ∈ Subgroup.centralizer Y, ∃ g ∈ Subgroup.normalizer (S : Subgroup G), c * g = x := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  set H : Subgroup G := Subgroup.closure Y with hH
  -- `H ≤ S`
  have hHS : H ≤ (S : Subgroup G) := Subgroup.closure_le _ |>.mpr hYS
  -- `M ⊔ N_G(S) = ⊤`
  have hKU : M ⊔ Subgroup.normalizer (S : Subgroup G) = ⊤ :=
    (top_eq_oPiPrimeCore_sup_normalizer_sylow S hpl1).symm
  -- `H ≤ N_G(S)`
  have hHU : H ≤ Subgroup.normalizer (S : Subgroup G) := hHS.trans Subgroup.le_normalizer
  -- coprimality: `H ≤ S` is a `p`-group ⟹ card is `p`-power coprime to card M.
  have hHpg : IsPGroup p H := S.isPGroup'.to_le hHS
  have hcop : Nat.Coprime (Nat.card H) (Nat.card M) := by
    obtain ⟨n, hn⟩ := hHpg.exists_card_eq
    rw [hn]
    exact (card_oPiPrimeCore_coprime_prime (p := p) (G := G)).symm.pow_left n
  -- `H.comap (conj x) ≤ N_G(S)`: in fact `≤ S`.
  have hconj : H.comap (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (S : Subgroup G) := by
    refine le_trans ?_ Subgroup.le_normalizer
    -- `H.comap (conj x) = H.map (conj x).symm = closure ((conj x).symm '' Y) ≤ S`.
    rw [hH, Subgroup.comap_equiv_eq_map_symm', MonoidHom.map_closure]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro z ⟨y, hy, rfl⟩
    -- `(conj x).symm y = x⁻¹ * y * x ∈ S`
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply]
    exact hYx y hy
  -- apply Lem 6.5(c)
  obtain ⟨c, hc, u, hu, hxcu⟩ := exists_mem_centralizerK_mul_of_conj_le hKU hHU hcop hconj
  -- `c ∈ centralizer Y` from `c ∈ centralizer (closure Y) ⊓ M`.
  have hcCent : c ∈ Subgroup.centralizer Y := by
    have hc1 : c ∈ Subgroup.centralizer (H : Set G) := (Subgroup.mem_inf.mp hc).1
    rwa [hH, Subgroup.centralizer_closure] at hc1
  exact ⟨c, hcCent, u, hu, hxcu.symm⟩

omit [IsSolvable G] in
/-- `p`-length 1 のもとで, `p`-部分群 `Q` の `S`-共役: ある `g ∈ N = O_{p',p}(G)` で
`g Q g⁻¹ ≤ S` (`MulAut.conj g • Q ≤ S`)。`Q ≤ N` (`pGroup_le_oPiPrimePiCore`), `S` は `↥N` の
Sylow `p`, `Q.subgroupOf N` を含む Sylow へ Sylow II 共役 (`MulAction.exists_smul_eq`), 戻して
`g Q g⁻¹ ≤ S`。Lem 6.6(4) の共役元供給。 -/
private theorem exists_mem_oPiPrimePiCore_conj_le_sylow (S : Sylow p G)
    (hpl1 : hasPLengthOne p G) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    ∃ g ∈ Ch03.oPiPrimePiCore {p} G, MulAut.conj g • Q ≤ (S : Subgroup G) := by
  set N : Subgroup G := Ch03.oPiPrimePiCore {p} G with hN
  -- `Q ≤ N`, `S ≤ N`.
  have hQN : Q ≤ N := pGroup_le_oPiPrimePiCore hQ hpl1
  have hSN : (S : Subgroup G) ≤ N := pGroup_le_oPiPrimePiCore S.isPGroup' hpl1
  -- `S` as a Sylow `p` of `↥N`.
  let S' : Sylow p ↥N := S.subtype hSN
  -- `Q.subgroupOf N` is a `p`-group of `↥N`, contained in some Sylow `Q'` of `↥N`.
  have hQsub_pg : IsPGroup p (Q.subgroupOf N) :=
    hQ.of_injective (Subgroup.subgroupOfEquivOfLe hQN).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQN).injective
  obtain ⟨Q', hQ'⟩ := hQsub_pg.exists_le_sylow
  -- Sylow II in `↥N`: `∃ h, h • Q' = S'`.
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (↥N) Q' S'
  refine ⟨(h : G), h.2, ?_⟩
  -- `h • (Q.subgroupOf N) ≤ h • Q' = S' = S.subgroupOf N`.
  have hstep1 : MulAut.conj h • (Q.subgroupOf N) ≤ S'.toSubgroup := by
    have hle : MulAut.conj h • (Q.subgroupOf N) ≤ MulAut.conj h • Q'.toSubgroup :=
      (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hQ'
    have heq : MulAut.conj h • Q'.toSubgroup = S'.toSubgroup := by
      have := congrArg Sylow.toSubgroup hh
      rwa [Sylow.coe_subgroup_smul] at this
    rwa [heq] at hle
  -- Translate to `G`: `(MulAut.conj ↑h • Q).subgroupOf N ≤ S.subgroupOf N`.
  have hS'eq : S'.toSubgroup = (S : Subgroup G).subgroupOf N := S.coe_subtype hSN
  rw [Subgroup.conj_smul_subgroupOf hQN, hS'eq] at hstep1
  -- Reflect `subgroupOf` order: map via `N.subtype`.
  have hmapped : (MulAut.conj (h : G) • Q) ⊓ N ≤ (S : Subgroup G) ⊓ N := by
    have h2 := Subgroup.map_mono (f := N.subtype) hstep1
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at h2
  -- `MulAut.conj ↑h • Q ≤ N` (h ∈ N, Q ≤ N), so `(conj ↑h • Q) ⊓ N = conj ↑h • Q`.
  have hconjQN : MulAut.conj (h : G) • Q ≤ N := by
    rintro - ⟨a, ha, rfl⟩
    exact N.mul_mem (N.mul_mem h.2 (hQN ha)) (N.inv_mem h.2)
  rw [inf_of_le_left hconjQN, inf_of_le_left hSN] at hmapped
  exact hmapped

/-- **BG Lemma 6.6(4)** (mmd L2103): `p`-length 1 で, `p`-部分群 `Q` に対し
`∃ x ∈ C_G(Q ⊓ S)`, `Q^x ⊆ S` (`Q.comap (conj x) ≤ S`, = `x⁻¹Qx ⊆ S`)。

`Q ≤ N = M ⊔ S`, `↑N = ↑S · ↑M`。共役 `g ∈ N` で `gQg⁻¹ ≤ S`
(`exists_mem_oPiPrimePiCore_conj_le_sylow`)。`g = s₀·m` (`s₀ ∈ S`, `m ∈ M`) ⟹
`m Q m⁻¹ ≤ s₀⁻¹ S s₀ = S`。`x := m⁻¹ ∈ M`: `Q.comap (conj x) = mQm⁻¹ ≤ S`,
かつ `m ∈ M` 正規 + `S ⊓ M = ⊥` で `x` が `Q ⊓ S` を中心化。 -/
theorem exists_mem_centralizer_inf_conj_le_sylow (S : Sylow p G)
    (hpl1 : OddOrder.BG.Ch1.hasPLengthOne p G) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    ∃ x ∈ Subgroup.centralizer ((Q ⊓ (S : Subgroup G) : Subgroup G) : Set G),
      Q.comap (MulAut.conj x).toMonoidHom ≤ (S : Subgroup G) := by
  set M : Subgroup G := Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hM
  set N : Subgroup G := Ch03.oPiPrimePiCore {p} G with hN
  -- `S ⊓ M = ⊥`, `N = M ⊔ S`.
  have hSMbot : (S : Subgroup G) ⊓ M = ⊥ := sylow_inf_oPiPrimeCore_eq_bot S
  have hNMS : N = M ⊔ (S : Subgroup G) := oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow S hpl1
  -- conjugate `g ∈ N` with `g Q g⁻¹ ≤ S`.
  obtain ⟨g, hgN, hgconj⟩ := exists_mem_oPiPrimePiCore_conj_le_sylow S hpl1 hQ
  -- decompose `g = s₀ * m`, `s₀ ∈ S`, `m ∈ M` (using `N = S ⊔ M`, `M` normal).
  have hgSM : g ∈ (S : Subgroup G) ⊔ M := by
    rw [sup_comm, ← hNMS]; exact hgN
  obtain ⟨s₀, hs₀, m, hmM, hg_eq⟩ := Subgroup.mem_sup_of_normal_right.mp hgSM
  -- `m Q m⁻¹ ≤ S`: from `g Q g⁻¹ ≤ S` and `s₀` normalizing `S`.
  have hmQ : MulAut.conj m • Q ≤ (S : Subgroup G) := by
    intro z hz
    -- `z = m q m⁻¹` with `q ∈ Q`; then `s₀ z s₀⁻¹ = g q g⁻¹ ∈ S`, and `s₀⁻¹ S s₀ = S`.
    obtain ⟨q, hq, rfl⟩ := hz
    have hgq : MulAut.conj g • Q ≤ (S : Subgroup G) := hgconj
    have hmem : (g : G) * q * (g : G)⁻¹ ∈ (S : Subgroup G) := hgq ⟨q, hq, rfl⟩
    -- `g q g⁻¹ = s₀ (m q m⁻¹) s₀⁻¹`.
    have hrw : (g : G) * q * (g : G)⁻¹
        = s₀ * (MulAut.conj m q) * s₀⁻¹ := by
      rw [MulAut.conj_apply, ← hg_eq]; group
    rw [hrw] at hmem
    -- `s₀⁻¹ (g q g⁻¹) s₀ = m q m⁻¹ ∈ S`.
    have hconjback : s₀⁻¹ * (s₀ * (MulAut.conj m q) * s₀⁻¹) * s₀ ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs₀) hmem) hs₀
    have hsimp : s₀⁻¹ * (s₀ * (MulAut.conj m q) * s₀⁻¹) * s₀ = MulAut.conj m q := by group
    rwa [hsimp] at hconjback
  -- set `x := m⁻¹ ∈ M`. `Q.comap (conj x) = m Q m⁻¹ ≤ S`.
  refine ⟨m⁻¹, ?_, ?_⟩
  · -- `x = m⁻¹ ∈ centralizer (Q ⊓ S)`.
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hz
    obtain ⟨hzQ, hzS⟩ := hz
    -- `d := (m⁻¹)⁻¹ z (m⁻¹) z⁻¹ = m z m⁻¹ z⁻¹ ∈ S ⊓ M = ⊥`.
    -- `m z m⁻¹ ∈ m Q m⁻¹ ≤ S` (since z ∈ Q), `z⁻¹ ∈ S`.
    have hmzm_S : m * z * m⁻¹ ∈ (S : Subgroup G) := by
      have hmem : m * z * m⁻¹ ∈ MulAut.conj m • Q := by
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
        have : m⁻¹ * (m * z * m⁻¹) * m = z := by group
        rw [this]; exact hzQ
      exact hmQ hmem
    have hd_S : m * z * m⁻¹ * z⁻¹ ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem hmzm_S ((S : Subgroup G).inv_mem hzS)
    -- `m z m⁻¹ z⁻¹ ∈ M` (m ∈ M normal).
    have hd_M : m * z * m⁻¹ * z⁻¹ ∈ M := by
      haveI : M.Normal := Ch03.oPiCore.normal _ _
      have hconjM : z * m⁻¹ * z⁻¹ ∈ M := by
        have := ‹M.Normal›.conj_mem m⁻¹ (M.inv_mem hmM) z
        simpa [mul_assoc] using this
      have heq : m * z * m⁻¹ * z⁻¹ = m * (z * m⁻¹ * z⁻¹) := by group
      rw [heq]; exact M.mul_mem hmM hconjM
    -- `d ∈ S ⊓ M = ⊥`, so `d = 1`, giving `m z m⁻¹ = z`, i.e. `z * m⁻¹ = m⁻¹ * z`.
    have hd1 : m * z * m⁻¹ * z⁻¹ = 1 := by
      have : m * z * m⁻¹ * z⁻¹ ∈ (S : Subgroup G) ⊓ M := Subgroup.mem_inf.mpr ⟨hd_S, hd_M⟩
      rw [hSMbot, Subgroup.mem_bot] at this
      exact this
    -- conclude `z * m⁻¹ = m⁻¹ * z`.
    have hmzm : m * z * m⁻¹ = z := by
      have := mul_eq_one_iff_eq_inv.mp hd1
      rw [inv_inv] at this; exact this
    -- `z * m⁻¹ = m⁻¹ * z`
    have : z * m⁻¹ = m⁻¹ * z := by
      have h4 : m⁻¹ * (m * z * m⁻¹) = m⁻¹ * z := by rw [hmzm]
      calc z * m⁻¹ = m⁻¹ * (m * z * m⁻¹) := by group
        _ = m⁻¹ * z := by rw [hmzm]
    exact this
  · -- `Q.comap (conj m⁻¹) = m Q m⁻¹ ≤ S`.
    intro z hz
    rw [mem_comap_conj, inv_inv] at hz
    -- `hz : m⁻¹ * z * m ∈ Q`.
    -- want `z ∈ S`. `z ∈ m Q m⁻¹ ≤ S`.
    have hzmem : z ∈ MulAut.conj m • Q := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
      exact hz
    exact hmQ hzmem

end

end OddOrder.BG.Ch1.S06
