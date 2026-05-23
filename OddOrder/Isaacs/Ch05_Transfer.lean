/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Focal
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import OddOrder.Isaacs.Ch03_SplitExtensions

open scoped commutatorElement

/-!
# OddOrder.Isaacs.Ch05 — Transfer

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 5
"Transfer" (pp. 147-180) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 5A | Transfer 定義・welldefinedness・準同型性 | 5.1 – 5.4 | mathlib + ✅ Thm 5.3 + Cor 5.4 |
| 5B | 中心への transfer = n 乗, Schur, Dietzmann | 5.5 – 5.10 | mathlib 直接 + 5.10 保留 |
| 5C | Hall transfer, Burnside, cyclic / abelian Sylow | 5.11 – 5.19 | ✅ Lem 5.11 + Lem 5.12 + Thm 5.17 + Thm 5.18 (強形+弱形) + Cor 5.19 (cyclic Sylow_2 版) |
| 5D | Focal subgroup theorem + p-transfer control | 5.20 – 5.24 | mathlib `Focal.lean` 直接 |
| 5E | Frobenius normal p-complement + 系 | 5.25 – 5.30 | docstring + 保留 (FT クリティカル) |

## 方針

mathlib カバレッジは Ch.5 中で最も厚い (`Mathlib/GroupTheory/Transfer.lean` 350 行 +
`Focal.lean` 218 行 + `Schreier.lean` + `SpecificGroups/ZGroup.lean`).
**no-wrapper policy** に従い, mathlib 直接対応の Isaacs 番号は section docstring の
対応表に記録するのみ. Isaacs 流のステートメント (引数特殊化や Isaacs 流の `H/H'` 標的)
が必要な場合のみ別途定理化する.

## Mathlib direct correspondence (no wrapper)

mathlib 既収載で本ファイルでは wrapper を書かないもの:

* `MonoidHom.transfer` (`Transfer.lean:148`) = **Thm 5.1, 5.2** (transfer welldef + 準同型).
* `MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot` (`Transfer.lean:161`) = **Thm 5.5**
  (transfer-evaluation lemma; orbital 分解).
* `MonoidHom.transfer_center_eq_pow`, `transferCenterPow` (`Transfer.lean:222, 229`)
  = **Thm 5.6** (中心 transfer = `g ↦ g^|G:Z|`).
* `Subgroup.card_commutator_le_of_finite_commutatorSet` (`Schreier.lean:208`) =
  **Thm 5.7** (Schur, bound 付き強化版).
* `MonoidHom.ker_transferSylow_isComplement'` (`Transfer.lean:275`) = **Thm 5.13 Burnside**.
* `IsCyclic.isComplement'` (`Transfer.lean:339`) = **Cor 5.14** (cyclic Sylow + smallest prime).
* `IsZGroup.isCyclic_commutator` (`ZGroup.lean:144`) = **Thm 5.16 part 1** (G' cyclic).
* `IsZGroup.isCyclic_abelianization` (`ZGroup.lean:134`) = **Thm 5.16 part 2** (G/G' cyclic).
* `IsZGroup.coprime_commutator_index` (`ZGroup.lean:280`) = **Thm 5.16 part 3** (|G'|, |G:G'| coprime).
* `isZGroup_iff_exists_mulEquiv` (`ZGroup.lean:315`) = **Thm 5.16 part 4** (semidirect product 形).
* `IsZGroup → IsSolvable` instance (`ZGroup.lean:102`) = **Cor 5.15** (Z-group solvable).
* `Subgroup.focalSubgroup`, `focalSubgroupOf`, `transferFocal` (`Focal.lean:58, 67, 151`) =
  Focal subgroup の定義 (Isaacs §5D 冒頭).
* `Subgroup.ker_restrict_transferFocal_eq_focalSubgroupOf` (`Focal.lean:191`) = **Thm 5.20**
  に相当 (ker(v) restrict 表示).
* `Subgroup.commutator_inf_eq_focalSubgroup` (`Focal.lean:208`) = **Thm 5.21 Focal Subgroup
  Theorem (D. G. Higman)** ⭐ **FT クリティカル**. BG が独自 Thm 1.17 として再述.
* `Subgroup.transferFocal_surjective` (`Focal.lean:180`) = transfer 全射性 (5.21 系).

## 下流被引用 (FT 経路)

**最重要**: **Focal Subgroup Theorem (5.21)** — BG が独自 Thm 1.17 として再述, 本文 3 箇所
(L2723, L5042, L5068) で使用. **Burnside (5.13)** = BG Thm 1.18 として再述.

Peterfalvi 本体 §4-§16 では transfer / focal を使わず. Suzuki 定理付録 (05.4) のみで
transfer-evaluation を直接利用 (1 件).

ノート: [`notes/isaacs/ch05_transfer.md`](../../notes/isaacs/ch05_transfer.md)
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5A: Transfer definition + homomorphism (pp. 147-153) -/

/-! ### Isaacs §5A (Transfer 定義)

- **Thm 5.1** (transfer welldef): mathlib `MonoidHom.transfer` 構成時点で transversal
  非依存性が組み込み済. wrapper 不要.
- **Thm 5.2** (transfer 準同型性): 同上, 構造の `map_mul'` フィールドで内包.
- **Thm 5.3** (`p ∣ |G' ∩ Z(G)|` ⇒ Sylow_p(G) は非可換): ✅
  `not_isMulCommutative_sylow_of_dvd_card_commutator_inf_center`.
- **Thm 5.4** (Schur multiplier corollary): ✅ 弱形
  `not_isMulCommutative_sylow_of_le_commutator_inf_center` — `Z ≤ Γ' ∩ Z(Γ)`, `p ∣ |Z|`
  ⇒ Sylow_p(Γ) 非可換. Schur multiplier 概念 (M(G), 中心 extension の universal) 自体は
  mathlib 未収載で full 形 (Sylow_p(Γ/Z) noncyclic) は別途. -/

/-- **Isaacs Thm 5.3**: 素数 `p` で `p ∣ |G' ∩ Z(G)|` ⇒ Sylow_p(G) は非可換.

**証明** (Isaacs p.157): `P ∈ Syl_p(G)`, `P` abelian と仮定. `P` abelian なら
`id : P →* P` で transfer `v : G →* P` が定義できる. Cauchy で `G' ∩ Z(G)` 中の
位数 `p` の元 `z` を取る. `z` 中心 ⇒ `zpowers z` 正規 (normal) かつ `p`-subgroup ⇒
任意の Sylow_p P に含まれる (Sylow II + 正規性の conjugation 不変).
transfer_eq_pow + `z` 中心 で `v(z) = z^|G:P|`. `v` hom to abelian ⇒
`G' ⊆ ker v` ⇒ `z ∈ G' ⇒ v(z) = 1` ⇒ `z^|G:P| = 1`. `orderOf z = p` だが
Sylow_p は `p ∤ |G:P|`, 矛盾. -/
theorem not_isMulCommutative_sylow_of_dvd_card_commutator_inf_center
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex]
    (h : p ∣ Nat.card ((commutator G ⊓ Subgroup.center G : Subgroup G))) :
    ¬ IsMulCommutative (P : Subgroup G) := by
  intro hPab
  -- Cauchy: z ∈ G' ∩ Z(G), orderOf z = p
  obtain ⟨z₀, hz₀⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(commutator G ⊓ Subgroup.center G)) p h
  have hz_comm : z₀.val ∈ commutator G := z₀.property.1
  have hz_cent : z₀.val ∈ Subgroup.center G := z₀.property.2
  have hz_ord : orderOf z₀.val = p := by
    rw [Subgroup.orderOf_coe]; exact hz₀
  -- ⟨z⟩ ⊴ G (z central)
  haveI : (Subgroup.zpowers z₀.val).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨n, ?_⟩
    have hzn_cent : z₀.val ^ n ∈ Subgroup.center G :=
      Subgroup.zpow_mem _ hz_cent n
    have hcomm : g * z₀.val ^ n = z₀.val ^ n * g :=
      (Subgroup.mem_center_iff.mp hzn_cent) g
    rw [hcomm]; group
  -- z ∈ P: ⟨z⟩ 正規 p-subgroup ⇒ 任意の Sylow_p P に含まれる
  have hz_inP : z₀.val ∈ P := by
    have h_zp_card : Nat.card (Subgroup.zpowers z₀.val) = p :=
      (Nat.card_zpowers z₀.val).trans hz_ord
    have h_zp_pg : IsPGroup p (Subgroup.zpowers z₀.val) :=
      IsPGroup.of_card (h_zp_card.trans (pow_one p).symm)
    obtain ⟨Q, hzQ⟩ := IsPGroup.exists_le_sylow h_zp_pg
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
    have h_zp_le_P : Subgroup.zpowers z₀.val ≤ (P : Subgroup G) := by
      calc Subgroup.zpowers z₀.val
          = MulAut.conj g • Subgroup.zpowers z₀.val :=
            (Subgroup.Normal.conj_smul_eq_self g _).symm
        _ ≤ MulAut.conj g • (Q : Subgroup G) :=
            Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hzQ
        _ = ((g • Q : Sylow p G) : Subgroup G) := Sylow.coe_subgroup_smul.symm
        _ = (P : Subgroup G) := by rw [hg]
    exact h_zp_le_P (Subgroup.mem_zpowers _)
  -- Setup transfer v : G →* ↥P (P abelian → CommGroup via priority-100 instance)
  -- mathlib transferSylow パターンと同じ @ explicit 形で typeclass diamond 回避
  let v : G →* (P : Subgroup G) :=
    @MonoidHom.transfer G _ (P : Subgroup G) (P : Subgroup G)
      (@CommGroup.ofIsMulCommutative ↥(P : Subgroup G) _ hPab)
        (MonoidHom.id (P : Subgroup G)) _
  -- transfer_eq_pow for z central: v(z) val = z^|G:P|
  have h_key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z₀.val ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * z₀.val ^ k * g₀ = z₀.val ^ k := by
    intro k g₀ _
    have hzk_cent : z₀.val ^ k ∈ Subgroup.center G :=
      Subgroup.pow_mem _ hz_cent k
    have hcomm : z₀.val ^ k * g₀ = g₀ * z₀.val ^ k :=
      (Subgroup.mem_center_iff.mp hzk_cent g₀).symm
    calc g₀⁻¹ * z₀.val ^ k * g₀
        = g₀⁻¹ * (z₀.val ^ k * g₀) := by group
      _ = g₀⁻¹ * (g₀ * z₀.val ^ k) := by rw [hcomm]
      _ = z₀.val ^ k := by group
  have hv_z_val : (v z₀.val).val = z₀.val ^ (P : Subgroup G).index := by
    show ((@MonoidHom.transfer G _ (P : Subgroup G) (P : Subgroup G)
        (@CommGroup.ofIsMulCommutative ↥(P : Subgroup G) _ hPab)
          (MonoidHom.id (P : Subgroup G)) _) z₀.val).val = _
    rw [@MonoidHom.transfer_eq_pow G _ (P : Subgroup G) (P : Subgroup G)
          (@CommGroup.ofIsMulCommutative ↥(P : Subgroup G) _ hPab)
            (MonoidHom.id (P : Subgroup G)) _ z₀.val h_key]
    rfl
  -- v hom to abelian ⇒ commutator G ≤ ker v ⇒ v(z) = 1
  have hv_z_one : v z₀.val = 1 := by
    have hker : commutator G ≤ v.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact MonoidHom.mem_ker.mp (hker hz_comm)
  -- z^|G:P| = 1 ⇒ p ∣ |G:P|, contradicting Sylow_p ⇒ p ∤ |G:P|
  have h_pow_one : z₀.val ^ (P : Subgroup G).index = 1 := by
    have hh : (v z₀.val).val = (1 : ↥(P : Subgroup G)).val := by
      rw [hv_z_one]
    rw [hv_z_val] at hh
    exact hh
  have h_p_dvd : p ∣ (P : Subgroup G).index := by
    have h := orderOf_dvd_of_pow_eq_one h_pow_one
    rwa [hz_ord] at h
  exact P.not_dvd_index h_p_dvd

/-- **Isaacs Cor 5.4** (Sylow non-abelian part, Schur multiplier 系): `Z ≤ Γ' ∩ Z(Γ)`,
`p ∣ |Z|` ⇒ Sylow_p(Γ) は非可換.

Thm 5.3 の hypothesis weakening (具体的 Z で `p ∣ |Z| → p ∣ |Γ' ∩ Z(Γ)|`).

Schur multiplier 文脈: Γ = `G` の中心拡大 (`Γ/Z ≅ G`, `Z ≤ Γ' ∩ Z(Γ)`), `Z` の取りうる最大
群が Schur multiplier `M(G)`. このとき "`p ∣ |M(G)|` ⇒ Sylow_p(`G`) noncyclic" が
得られる. ここでは前段の Sylow_p(Γ) 非可換のみ実装. (Γ/Z の Sylow noncyclic への
変換は `Cyclic.commutative_of_cyclic_center_quotient` + `P ∩ Z ≤ Z(P)` 経由で追加可.) -/
theorem not_isMulCommutative_sylow_of_le_commutator_inf_center
    [Finite G] {p : ℕ} [Fact p.Prime] {Z : Subgroup G}
    (hZ : Z ≤ commutator G ⊓ Subgroup.center G)
    (h_p_dvd : p ∣ Nat.card Z) (P : Sylow p G) [P.FiniteIndex] :
    ¬ IsMulCommutative (P : Subgroup G) :=
  not_isMulCommutative_sylow_of_dvd_card_commutator_inf_center P
    (h_p_dvd.trans (Subgroup.card_dvd_of_le hZ))

end -- 5A

section /- 5B: Central transfer, Schur, Dietzmann (pp. 153-159) -/

/-! ### Isaacs §5B (中心 transfer, Schur, Dietzmann)

- **Thm 5.6** (中心 transfer = `g ↦ g^n`): mathlib `MonoidHom.transferCenterPow` 直接.
- **Lemma 5.8, Cor 5.9** (`Z(G)` transversal commutator 構造 + `|G:Z|`-乗 = 1):
  形式化保留 (`Subgroup.LeftTransversal` projection の精緻化が要る. FT 経路で要求なし).
- **Thm 5.7 Schur** (`|G:Z(G)| < ∞ ⇒ G' 有限`): mathlib
  `Subgroup.card_commutator_le_of_finite_commutatorSet` 直接 (bound 付き強化版).
- **Thm 5.10 Dietzmann** (`X ⊆ G` 有限・共役閉・∃n, x^n=1 ⇒ `⟨X⟩` 有限):
  mathlib 未収載. Schur 5.7 の証明では mathlib `closureCommutatorRepresentatives` 経路
  で代替されているため独立 Dietzmann の必要なし. 形式化保留. -/

end -- 5B

section /- 5C: Hall transfer, Burnside, cyclic / abelian Sylow (pp. 159-167) -/

/-! ### Isaacs §5C (Hall transfer + Burnside)

- **Lemma 5.11** (Hall index transfer): `ker_transfer_sup_eq_top_of_hall` ✅.
- **Lemma 5.12** (`N_G(P)` controls `C_G(P)` fusion): `normalizer_controls_centralizer_fusion` ✅.
- **Thm 5.13 Burnside**: `MonoidHom.ker_transferSylow_isComplement'` 直接.
- **Cor 5.14**: `IsCyclic.isComplement'` 直接.
- **Cor 5.15** (Z-group solvable): mathlib `IsZGroup` instance 直接.
- **Thm 5.16** (Z-group 構造): mathlib `IsZGroup` API 直接.
- **Thm 5.17** (cyclic Sylow_p ⇒ p∤|G'| or p∤|G:G'|): ✅ `isaacs_thm_5_17`
  (axiom on Ch.4 §4D Thm 4.34 Fitting + cyclic-chain helper).
- **Cor 5.19** (Sylow_2 cyclic direct factor ⇒ 非単純): 形式化保留. -/

/-! ### Forward axioms (Ch.4 §4D dep)

Thm 5.17 は Ch.4 §4D **Thm 4.34 Fitting** に依存. 当面 axiom 化, Ch.4 §4D 完成後に
theorem 化する. -/

namespace _root_.OddOrder.Isaacs.Ch04

/-- **Isaacs Thm 4.34 (Fitting)** — axiom 形 (Ch.4 §4D forward dep).

`A` (= subgroup `K` of `G` with `K ≤ N_G(P)`) が abelian subgroup `P` に conjugation 経由で
作用. `(|P|, |K|) = 1` (coprime) ⇒ `P = C_P(K) × ⁅P, K⁆` (internal direct product, element form).

**証明戦略** (Isaacs p.142, θ trick):
* θ : ↥P → ↥P, θ(p) = ∏_{k ∈ K} k • p. P abelian なので well-def + homomorphism.
* θ(p) ∈ C_P(K) (θ は K 作用と可換).
* `p ∈ C_P(K)` で θ(p) = p^|K|; (|P|, |K|) = 1 ⇒ θ(p) = 1 ⇒ p = 1.
* ⁅P, K⁆ ⊆ ker θ (各 [p, k] が ker に入る).
* ⇒ C_P(K) ⊓ ⁅P, K⁆ = ⊥.
* p^|K| = θ(p) · h with h ∈ ⁅P, K⁆ (元素計算). Bezout で p ∈ C_P(K) · ⁅P, K⁆.

**実装スケジュール**: Ch.4 §4D 着手時 ~150 LOC. 進捗は ROADMAP / `notes/isaacs/ch04_commutators.md`. -/
axiom fitting_coprime_abelian_decomp
    {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} [IsMulCommutative ↥P]
    {K : Subgroup G} (_hK_norm : K ≤ Subgroup.normalizer P)
    (_h_coprime : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K)) :
    (Subgroup.centralizer (K : Set G) ⊓ P) ⊓ (⁅P, K⁆ : Subgroup G) = ⊥ ∧
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊔ (⁅P, K⁆ : Subgroup G) = P

/-- **Cyclic p-group inf-eq-bot** (theorem 形, 2026-05-23 axiom → theorem 化).

cyclic 有限 `p`-group の部分群 lattice は線形 (divisor lattice 同型). よって
任意 2 部分群 `H, K ≤ P` で `H ⊓ K = ⊥ ⇒ H = ⊥ ∨ K = ⊥`.

**証明戦略**:
- `H, K` 非自明と仮定 (背理法). `IsPGroup p ↥H` (`hP_pgroup.to_le hH_le_P`) + `Cauchy`
  (`exists_prime_orderOf_dvd_card'`) で `H, K` に order `p` 元 `h, k` を取る.
- `↥P` に lift: cyclic ⇒ CommGroup. mathlib `IsCyclic.card_powMonoidHom_ker` で
  `(powMonoidHom p).ker` (cyclic 内 unique order-p subgroup) の cardinality = `p`.
- `zpowers h_P` と `zpowers k_P` (両方 ↥P 内) は cardinality = p で `(powMonoidHom p).ker`
  に含まれる ⇒ `Subgroup.eq_of_le_of_card_ge` で両方 = ker.
- ゆえに `zpowers h_P = zpowers k_P`, 特に `h_P ∈ zpowers k_P`. G に戻して `h ∈ K`.
- `h ∈ H ⊓ K = ⊥` ⇒ `h = 1` だが `orderOf h = p > 1`, 矛盾. -/
theorem cyclic_pgroup_inf_eq_bot_iff
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} [hPcyc : IsCyclic ↥P] (hP_pgroup : IsPGroup p ↥P)
    {H K : Subgroup G} (hH_le_P : H ≤ P) (hK_le_P : K ≤ P) :
    H ⊓ K = ⊥ ↔ H = ⊥ ∨ K = ⊥ := by
  refine ⟨fun h_inf => ?_, fun h => h.elim
    (fun he => by rw [he, bot_inf_eq]) (fun he => by rw [he, inf_bot_eq])⟩
  by_contra h_not
  push_neg at h_not
  obtain ⟨hH_ne, hK_ne⟩ := h_not
  -- Cauchy in H: ∃ h ∈ H with orderOf h = p
  have hH_pgroup : IsPGroup p ↥H := hP_pgroup.to_le hH_le_P
  obtain ⟨nH, hnH⟩ := IsPGroup.iff_card.mp hH_pgroup
  have hnH_pos : 1 ≤ nH := by
    by_contra h
    push_neg at h
    interval_cases nH
    rw [pow_zero] at hnH
    exact hH_ne (Subgroup.eq_bot_of_card_eq H hnH)
  have h_p_dvd_H : p ∣ Nat.card ↥H :=
    hnH ▸ dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hnH_pos)
  obtain ⟨⟨h, hh_mem⟩, hh_ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥H) p h_p_dvd_H
  have hh_inP : h ∈ P := hH_le_P hh_mem
  have hh_ord_g : orderOf h = p := (Subgroup.orderOf_coe _).trans hh_ord
  -- Cauchy in K: ∃ k ∈ K with orderOf k = p
  have hK_pgroup : IsPGroup p ↥K := hP_pgroup.to_le hK_le_P
  obtain ⟨nK, hnK⟩ := IsPGroup.iff_card.mp hK_pgroup
  have hnK_pos : 1 ≤ nK := by
    by_contra h
    push_neg at h
    interval_cases nK
    rw [pow_zero] at hnK
    exact hK_ne (Subgroup.eq_bot_of_card_eq K hnK)
  have h_p_dvd_K : p ∣ Nat.card ↥K :=
    hnK ▸ dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hnK_pos)
  obtain ⟨⟨k, hk_mem⟩, hk_ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥K) p h_p_dvd_K
  have hk_inP : k ∈ P := hK_le_P hk_mem
  have hk_ord_g : orderOf k = p := (Subgroup.orderOf_coe _).trans hk_ord
  -- Lift h, k to ↥P (cyclic ⇒ IsMulCommutative auto ⇒ CommGroup auto via priority 100)
  let h_P : ↥P := ⟨h, hh_inP⟩
  let k_P : ↥P := ⟨k, hk_inP⟩
  have hh_P_ord : orderOf h_P = p := by
    show orderOf (⟨h, hh_inP⟩ : ↥P) = p
    rw [Subgroup.orderOf_mk]; exact hh_ord_g
  have hk_P_ord : orderOf k_P = p := by
    show orderOf (⟨k, hk_inP⟩ : ↥P) = p
    rw [Subgroup.orderOf_mk]; exact hk_ord_g
  -- Z := (powMonoidHom p).ker, unique order-p subgroup of ↥P
  obtain ⟨a, hP_card⟩ := IsPGroup.iff_card.mp hP_pgroup
  have ha_pos : 1 ≤ a := by
    have h_dvd : Nat.card ↥H ∣ Nat.card ↥P := Subgroup.card_dvd_of_le hH_le_P
    rw [hP_card, hnH] at h_dvd
    exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt Fact.out)).mp
      (h_dvd.trans (dvd_refl _)) |>.trans' hnH_pos
  have hZ_card : Nat.card ((@powMonoidHom ↥P _ p).ker) = p := by
    rw [IsCyclic.card_powMonoidHom_ker, hP_card,
        Nat.gcd_eq_right (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp ha_pos))]
  -- h_P, k_P ∈ Z (since h_P^p = 1)
  have hh_in_Z : h_P ∈ (@powMonoidHom ↥P _ p).ker := by
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact orderOf_dvd_iff_pow_eq_one.mp (hh_P_ord ▸ dvd_refl _)
  have hk_in_Z : k_P ∈ (@powMonoidHom ↥P _ p).ker := by
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact orderOf_dvd_iff_pow_eq_one.mp (hk_P_ord ▸ dvd_refl _)
  -- zpowers h_P = Z (same card p) ; similarly zpowers k_P = Z
  have h_zpowers_h : Subgroup.zpowers h_P = (@powMonoidHom ↥P _ p).ker := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hh_in_Z)
    rw [hZ_card, Nat.card_zpowers, hh_P_ord]
  have h_zpowers_k : Subgroup.zpowers k_P = (@powMonoidHom ↥P _ p).ker := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk_in_Z)
    rw [hZ_card, Nat.card_zpowers, hk_P_ord]
  have h_eq_zpowers : Subgroup.zpowers h_P = Subgroup.zpowers k_P := by
    rw [h_zpowers_h, h_zpowers_k]
  -- h_P ∈ zpowers k_P ⇒ h_P = k_P^n for some n ⇒ h = k^n in G
  have hh_in_zpowers_k : h_P ∈ Subgroup.zpowers k_P := by
    rw [← h_eq_zpowers]; exact Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh_in_zpowers_k
  have hh_g_eq : h = (k : G) ^ n := by
    have h1 : (h_P : G) = ((k_P ^ n : ↥P) : G) := by rw [hn]
    have h2 : ((k_P ^ n : ↥P) : G) = (k_P : G) ^ n := SubgroupClass.coe_zpow _ _
    have h3 : (h_P : G) = h := rfl
    have h4 : (k_P : G) = k := rfl
    rw [h3, h2, h4] at h1
    exact h1
  -- h ∈ K (K closed under zpow)
  have hh_in_K : h ∈ K := by
    rw [hh_g_eq]; exact K.zpow_mem hk_mem n
  -- h ∈ H ⊓ K = ⊥ ⇒ h = 1, but orderOf h = p > 1, contradiction
  have hh_inHK : h ∈ H ⊓ K := ⟨hh_mem, hh_in_K⟩
  rw [h_inf, Subgroup.mem_bot] at hh_inHK
  rw [hh_inHK, orderOf_one] at hh_ord_g
  exact (Nat.Prime.ne_one Fact.out) hh_ord_g.symm

end _root_.OddOrder.Isaacs.Ch04

/-- **Isaacs Lemma 5.11** (Hall transfer index): `H` が π-Hall 部分群 + `ϕ : H →* A`
(`A` 可換有限群, `|A| ∣ |H|`) ⇒ `ker(transfer ϕ) · H = G`.

**証明** (Isaacs p.159): `transfer ϕ : G →* A` の range ⊆ A から `|G:ker(v)| = |range|`
が `|A|` を割り切る. 仮定 `|A| ∣ |H|` から `|G:ker(v)| ∣ |H|`. Hall 性 `gcd(|H|, |G:H|) = 1`
で `gcd(|G:ker(v)|, |G:H|) = 1`. Lemma 3.16 で `ker(v) ⊔ H = ⊤`.

通常 `A := H/H'` で適用するとき `|A| = |H|/|H'| ∣ |H|` が成立. -/
theorem ker_transfer_sup_eq_top_of_hall [Finite G] {π : Set ℕ}
    {H : Subgroup G} (hHall : OddOrder.Isaacs.Ch03.IsHallSubgroup π H) [H.FiniteIndex]
    {A : Type*} [CommGroup A] [Finite A] (ϕ : H →* A)
    (hAH : Nat.card A ∣ Nat.card H) :
    (MonoidHom.transfer ϕ).ker ⊔ H = ⊤ := by
  apply OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index
  -- (transfer ϕ).ker.index ∣ |A| (1st iso + Lagrange in A)
  have h_range_card : (MonoidHom.transfer ϕ).ker.index ∣ Nat.card A := by
    have heq : Nat.card (G ⧸ (MonoidHom.transfer ϕ).ker) =
        Nat.card (MonoidHom.transfer ϕ).range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
    rw [Subgroup.index_eq_card] at *
    rw [heq]
    exact Subgroup.card_subgroup_dvd_card _
  have h_dvd_H : (MonoidHom.transfer ϕ).ker.index ∣ Nat.card H :=
    h_range_card.trans hAH
  -- gcd(ker.index, |G:H|) divides gcd(|H|, |G:H|) = 1 (Hall)
  exact Nat.Coprime.coprime_dvd_left h_dvd_H hHall.coprime_index

/-- **Isaacs Lemma 5.12** (`N_G(P)` controls `C_G(P)` fusion):
`P ∈ Syl_p(G)`, `x, y ∈ C_G(P)` が `G` で共役 (∃ g, gxg⁻¹ = y) ⇒ `N_G(P)` で共役.

**証明** (Isaacs p.161): `y = x^g` (g ∈ G). `x ∈ C_G(P)` から `q ∈ P` は `x` と可換 ⇒
`gqg⁻¹` は `gxg⁻¹ = y` と可換 ⇒ `gPg⁻¹ ⊆ C_G(y)`. 一方 `y ∈ C_G(P)` から `P ⊆ C_G(y)`.
ゆえに `P`, `gPg⁻¹` は `C_G(y)` の Sylow_p. Sylow II in `C_G(y)` で `c ∈ C_G(y)` 存在し
`c (gPg⁻¹) c⁻¹ = P`, i.e., `(cg) ∈ N_G(P)`. `(cg) x (cg)⁻¹ = c y c⁻¹ = y`. -/
theorem normalizer_controls_centralizer_fusion
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {x y g : G}
    (hx : x ∈ Subgroup.centralizer (P : Set G))
    (hy : y ∈ Subgroup.centralizer (P : Set G))
    (hgxy : g * x * g⁻¹ = y) :
    ∃ n : G, n ∈ Subgroup.normalizer (P : Subgroup G) ∧ n * x * n⁻¹ = y := by
  set K : Subgroup G := Subgroup.centralizer ({y} : Set G) with hK_def
  -- y ∈ C_G(P) ⇒ P ≤ K = C_G(y)
  have hP_le_K : (P : Subgroup G) ≤ K := by
    intro q hq z hz
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact (Subgroup.mem_centralizer_iff.mp hy q hq).symm
  -- x ∈ C_G(P) ⇒ gPg⁻¹ ≤ K (using Sylow's G-action via MulAut.conj)
  have hPg_le_K : ((g • P : Sylow p G) : Subgroup G) ≤ K := by
    rw [Sylow.coe_subgroup_smul]
    intro w hw
    -- w = g * q * g⁻¹ for some q ∈ P
    obtain ⟨q, hq_mem, hqw⟩ : ∃ q ∈ (P : Subgroup G), g * q * g⁻¹ = w := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hw
      refine ⟨(MulAut.conj g)⁻¹ w, hw, ?_⟩
      have heq : (MulAut.conj g) ((MulAut.conj g)⁻¹ w) = w :=
        MulAut.apply_inv_self G (MulAut.conj g) w
      simpa [MulAut.conj] using heq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz; subst hz
    have hxq : q * x = x * q := Subgroup.mem_centralizer_iff.mp hx q hq_mem
    -- w * y = (g q g⁻¹) * (g x g⁻¹) = g (q x) g⁻¹ = g (x q) g⁻¹ = (g x g⁻¹) * (g q g⁻¹) = y * w
    rw [← hqw, ← hgxy]
    calc (g * x * g⁻¹) * (g * q * g⁻¹)
        = g * (x * q) * g⁻¹ := by group
      _ = g * (q * x) * g⁻¹ := by rw [← hxq]
      _ = (g * q * g⁻¹) * (g * x * g⁻¹) := by group
  -- Promote to Sylow p K
  let P_K : Sylow p K := P.subtype hP_le_K
  let Pg_K : Sylow p K := (g • P).subtype hPg_le_K
  -- Sylow II in K: there exists c : K with c • Pg_K = P_K
  haveI : Finite K := inferInstance
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := K) Pg_K P_K
  -- Translate back: c • Pg_K = P_K via Sylow.smul_subtype ⇒ (c.val • (g • P)).subtype = P.subtype
  have h_subtype_eq : ((c : G) • g • P).subtype (Sylow.smul_le hPg_le_K c) = P_K := by
    rw [show ((c : G) • g • P).subtype (Sylow.smul_le hPg_le_K c) =
        c • (g • P).subtype hPg_le_K from (Sylow.smul_subtype hPg_le_K c).symm]
    exact hc
  have hcgP : (c : G) • g • P = P := Sylow.subtype_injective h_subtype_eq
  -- (c * g) • P = P, so c * g ∈ N_G(P)
  have hcgP_smul : ((c : G) * g) • P = P := by rw [mul_smul]; exact hcgP
  refine ⟨(c : G) * g, ?_, ?_⟩
  · -- (c * g) ∈ N_G(P)
    rw [← Sylow.smul_eq_iff_mem_normalizer]
    exact hcgP_smul
  · -- (cg) * x * (cg)⁻¹ = c * (g x g⁻¹) * c⁻¹ = c * y * c⁻¹ = y (c ∈ K = C_G(y))
    have hcy : y * (c : G) = (c : G) * y := by
      have hcK : (c : G) ∈ K := c.property
      exact Subgroup.mem_centralizer_iff.mp hcK y (Set.mem_singleton y)
    calc ((c : G) * g) * x * ((c : G) * g)⁻¹
        = (c : G) * (g * x * g⁻¹) * (c : G)⁻¹ := by group
      _ = (c : G) * y * (c : G)⁻¹ := by rw [hgxy]
      _ = y * (c : G) * (c : G)⁻¹ := by rw [← hcy]
      _ = y := by group

/-- mathlib `commutator_inf_eq_focalSubgroup` のリネーム (Focal Subgroup Theorem の
Isaacs 5.18 弱形). 注: Isaacs 5.18 のフル statement は次の
`eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer` (強形). -/
theorem abelian_sylow_commutator_inf_eq_focal
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex] :
    _root_.commutator G ⊓ (P : Subgroup G) = P.focalSubgroup :=
  Subgroup.commutator_inf_eq_focalSubgroup P

/-- **Isaacs Thm 5.18 (強形)**: `P` abelian Sylow_p(G) ⇒ `G' ∩ P ∩ Z(N_G(P)) = 1`.

要素形式: `x ∈ G', x ∈ P, x ∈ Z(N_G(P))` ⇒ `x = 1`.

**証明** (Isaacs p.166): transfer `v : G →* P` (P abelian, id : P →* P).
`v(x) = 1` (x ∈ G', v hom to abelian P, commutator ≤ ker).
`transfer_eq_pow` の key: `g₀⁻¹ x^k g₀ ∈ P ⇒ g₀⁻¹ x^k g₀ = x^k`.
このために (i) P abelian で x^k, g₀⁻¹ x^k g₀ ∈ C_G(P), (ii) G-conjugate (via g₀⁻¹),
(iii) **Lemma 5.12** で N_G(P)-conjugate: ∃ n ∈ N(P), n · x^k · n⁻¹ = g₀⁻¹ x^k g₀.
(iv) x ∈ Z(N(P)) ⇒ x^k ∈ Z(N(P)) ⇒ Commute n x^k ⇒ n · x^k · n⁻¹ = x^k.
ゆえに v(x).val = x^|G:P|. v(x) = 1 ⇒ x^|G:P| = 1. orderOf x は p-power (x ∈ P),
|G:P| coprime to p ⇒ orderOf x = 1 ⇒ x = 1. -/
theorem eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex]
    [hPab : IsMulCommutative (P : Subgroup G)]
    {x : G} (hx_comm : x ∈ commutator G) (hx_P : x ∈ (P : Subgroup G))
    (hx_central_N : ∀ n ∈ Subgroup.normalizer (P : Subgroup G), n * x = x * n) :
    x = 1 := by
  -- Setup transfer v : G →* ↥P (P abelian)
  let v : G →* (P : Subgroup G) :=
    @MonoidHom.transfer G _ (P : Subgroup G) (P : Subgroup G)
      (@CommGroup.ofIsMulCommutative ↥(P : Subgroup G) _ hPab)
        (MonoidHom.id (P : Subgroup G)) _
  -- P abelian ⇒ P ⊆ centralizer P
  have hP_le_centP : (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
    intro a haP
    rw [Subgroup.mem_centralizer_iff]
    intro b hbP
    have h : (⟨b, hbP⟩ : ↥(P : Subgroup G)) * ⟨a, haP⟩ = ⟨a, haP⟩ * ⟨b, hbP⟩ :=
      mul_comm _ _
    exact congrArg Subtype.val h
  -- key for transfer_eq_pow
  have h_key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * x ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * x ^ k * g₀ = x ^ k := by
    intro k g₀ hg_pow_in_P
    have hxk_in_P : x ^ k ∈ (P : Subgroup G) := Subgroup.pow_mem _ hx_P k
    have hxk_cent_P : x ^ k ∈ Subgroup.centralizer (P : Set G) := hP_le_centP hxk_in_P
    have hg_pow_cent_P : g₀⁻¹ * x ^ k * g₀ ∈ Subgroup.centralizer (P : Set G) :=
      hP_le_centP hg_pow_in_P
    -- G-conjugate via g₀⁻¹
    have h_conj : g₀⁻¹ * x ^ k * (g₀⁻¹)⁻¹ = g₀⁻¹ * x ^ k * g₀ := by group
    -- Lemma 5.12: N_G(P)-conjugate
    obtain ⟨n, hn_N, hn_eq⟩ := normalizer_controls_centralizer_fusion P
      hxk_cent_P hg_pow_cent_P h_conj
    -- x ∈ Z(N(P)) ⇒ Commute n x ⇒ Commute n (x^k)
    have hxn_comm : Commute n x := hx_central_N n hn_N
    have hxkn_comm : Commute n (x ^ k) := hxn_comm.pow_right k
    -- n * x^k * n⁻¹ = x^k
    have h_eq : n * x ^ k * n⁻¹ = x ^ k := by
      rw [hxkn_comm.eq]; group
    -- g₀⁻¹ x^k g₀ = n * x^k * n⁻¹ = x^k
    rw [← hn_eq, h_eq]
  -- v(x).val = x^|G:P|
  have hv_x_val : (v x).val = x ^ (P : Subgroup G).index := by
    show ((@MonoidHom.transfer G _ (P : Subgroup G) (P : Subgroup G)
        (@CommGroup.ofIsMulCommutative ↥(P : Subgroup G) _ hPab)
          (MonoidHom.id (P : Subgroup G)) _) x).val = _
    rw [@MonoidHom.transfer_eq_pow G _ (P : Subgroup G) (P : Subgroup G)
          (@CommGroup.ofIsMulCommutative ↥(P : Subgroup G) _ hPab)
            (MonoidHom.id (P : Subgroup G)) _ x h_key]
    rfl
  -- v(x) = 1 (x ∈ G', v hom to abelian)
  have hv_x_one : v x = 1 := by
    have hker : commutator G ≤ v.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact MonoidHom.mem_ker.mp (hker hx_comm)
  -- x^|G:P| = 1
  have h_pow_one : x ^ (P : Subgroup G).index = 1 := by
    have hh : (v x).val = (1 : ↥(P : Subgroup G)).val := by rw [hv_x_one]
    rw [hv_x_val] at hh
    exact hh
  -- orderOf x is p-power (x ∈ P p-group)
  have h_ord_ppow : ∃ n, orderOf x = p ^ n := by
    have h_eq : orderOf x = orderOf (⟨x, hx_P⟩ : ↥(P : Subgroup G)) :=
      (Subgroup.orderOf_mk x hx_P).symm
    rw [h_eq]
    exact (IsPGroup.iff_orderOf.mp P.isPGroup') _
  obtain ⟨n, hn⟩ := h_ord_ppow
  -- Coprime (orderOf x) |G:P|: orderOf x = p^n and p ∤ |G:P|
  have h_coprime : Nat.Coprime (orderOf x) (P : Subgroup G).index := by
    rw [hn]
    exact Nat.Coprime.pow_left _
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index)
  -- orderOf x ∣ |G:P| ∧ Coprime ⇒ orderOf x = 1 ⇒ x = 1
  have h_ord_dvd : orderOf x ∣ (P : Subgroup G).index :=
    orderOf_dvd_of_pow_eq_one h_pow_one
  have h_ord_eq_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes h_coprime dvd_rfl h_ord_dvd
  exact orderOf_eq_one_iff.mp h_ord_eq_one

/-- **Isaacs Thm 5.17**: `P ∈ Syl_p(G)` cyclic ⇒ `p` は `|G'|`, `|G:G'|` のたかだか
一方を割る (i.e., `¬ p ∣ |G'| ∨ ¬ p ∣ |G:G'|`).

**証明** (Isaacs p.165, Fitting 4.34 + Burnside 5.13 経由):

`N := N_G(P)`, `K` complement of `P` in `N` (Schur-Zassenhaus, `(|P|, |N:P|) = 1` since
P Sylow_p). `K ≤ N`, `(|P|, |K|) = 1`. **Thm 4.34 Fitting** (axiom): `P = C_P(K) × ⁅P,K⁆`
(internal direct, `C_P(K) ⊓ ⁅P,K⁆ = ⊥` AND `C_P(K) ⊔ ⁅P,K⁆ = P`).

`P` cyclic + axiom **cyclic_pgroup_inf_eq_bot_iff**: `C_P(K) ⊓ ⁅P,K⁆ = ⊥ ⇒
C_P(K) = ⊥ ∨ ⁅P,K⁆ = ⊥`.

* **Case 1** `⁅P,K⁆ = ⊥`: `K` centralizes `P`. `N = PK` で全要素が `P` と可換 ⇒
  `N ⊆ C_G(P)`. `N(P) ≤ C(P)` ⇒ Burnside (mathlib `ker_transferSylow_isComplement'`)
  で normal `p`-complement `M`. `G/M ≅ P` cyclic ⇒ `G/M` abelian ⇒ `G' ⊆ M`. `M`
  `p'`-group ⇒ `p ∤ |G'|`.

* **Case 2** `C_P(K) = ⊥`: 4.34 sup より `P = ⁅P,K⁆ ⊆ commutator G`. `|G:G'| = |G|/|G'|`,
  Sylow_p 全体が `G'` に入る ⇒ `|G:G'|` の `p`-成分 = 1 ⇒ `p ∤ |G:G'|`.

**FORWARD DEPENDENCY**: Thm 4.34 (Ch.4 §4D) + cyclic_pgroup_inf_eq_bot_iff (mathlib upstream
候補) を axiom 化. 完成後 unconditional 化. -/
theorem isaacs_thm_5_17
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex]
    [hPcyc : IsCyclic ↥(P : Subgroup G)] :
    ¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index := by
  -- P abelian (cyclic)
  haveI hPab : IsMulCommutative ↥(P : Subgroup G) := inferInstance
  -- N := N_G(P), P_N := P.subgroupOf N (normal in N)
  set N := Subgroup.normalizer ((P : Subgroup G) : Set G) with hN_def
  set P_N : Subgroup ↥N := (P : Subgroup G).subgroupOf N with hP_N_def
  haveI hP_N_normal : P_N.Normal := Subgroup.normal_in_normalizer
  haveI : Finite ↥N := inferInstance
  -- coprime(|P_N|, |N : P_N|): |P_N| = |P| = p^a, |N:P_N| ∣ |G:P| coprime to p
  have hP_le_N : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  have h_coprime_P_N : Nat.Coprime (Nat.card ↥P_N) P_N.index := by
    have h_card_eq : Nat.card ↥P_N = Nat.card ↥(P : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
    have h_idx_dvd : P_N.index ∣ (P : Subgroup G).index :=
      Subgroup.relIndex_dvd_index_of_le hP_le_N
    obtain ⟨a, hP_card⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [h_card_eq, hP_card]
    -- p coprime to |G:P| (Sylow); pow_left ⇒ p^a coprime to |G:P|; dvd ⇒ coprime to P_N.index
    have h_p_coprime_idx : Nat.Coprime p ((P : Subgroup G).index) :=
      (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index
    have h_pa_coprime_idx : Nat.Coprime (p^a) ((P : Subgroup G).index) :=
      h_p_coprime_idx.pow_left a
    exact h_pa_coprime_idx.coprime_dvd_right h_idx_dvd
  -- Schur-Zassenhaus: complement K' of P_N in N
  obtain ⟨K', hK'_compl⟩ := Subgroup.exists_right_complement'_of_coprime h_coprime_P_N
  -- Map K' back to G via subtype
  let K : Subgroup G := K'.map N.subtype
  -- K ≤ N
  have hK_le_N : K ≤ N := by
    intro k hk
    obtain ⟨k', _, rfl⟩ := hk
    exact k'.property
  -- |K| coprime to |P|: |K| = |K'| = P_N.index (complement), and (|P|, P_N.index) coprime
  have h_coprime_PK : Nat.Coprime (Nat.card ↥(P : Subgroup G)) (Nat.card ↥K) := by
    -- |K| = |K'|
    have h_K_card : Nat.card ↥K = Nat.card ↥K' :=
      (Nat.card_congr (Subgroup.equivMapOfInjective K' N.subtype Subtype.coe_injective).toEquiv).symm
    -- |K'| = P_N.index (complement)
    have h_K'_card : Nat.card ↥K' = P_N.index := by
      have := hK'_compl.card_right
      rwa [Nat.card_coe_set_eq] at this
    -- |P_N| = |P|
    have h_PN_card : Nat.card ↥P_N = Nat.card ↥(P : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
    rw [h_K_card, h_K'_card, ← h_PN_card]
    exact h_coprime_P_N
  -- Apply Thm 4.34 (axiom)
  obtain ⟨h_inf_bot, h_sup_top⟩ :=
    _root_.OddOrder.Isaacs.Ch04.fitting_coprime_abelian_decomp hK_le_N h_coprime_PK
  -- ⁅P, K⁆ ≤ P (since K ≤ N normalizes P, so conjugates of P-elements stay in P)
  have h_comm_le_P : (⁅(P : Subgroup G), K⁆ : Subgroup G) ≤ (P : Subgroup G) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyN : y ∈ N := hK_le_N hy
    have hyxiy : y * x⁻¹ * y⁻¹ ∈ (P : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp ((P : Subgroup G).inv_mem hx)
    have h_eq : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [show (⁅x, y⁆ : G) = x * y * x⁻¹ * y⁻¹ from rfl, h_eq]
    exact (P : Subgroup G).mul_mem hx hyxiy
  have h_cent_le_P : Subgroup.centralizer (K : Set G) ⊓ (P : Subgroup G) ≤ (P : Subgroup G) :=
    inf_le_right
  -- Cyclic axiom: C_P(K) ⊓ ⁅P,K⁆ = ⊥ ⇒ one of them is ⊥
  rcases (_root_.OddOrder.Isaacs.Ch04.cyclic_pgroup_inf_eq_bot_iff P.isPGroup'
      h_cent_le_P h_comm_le_P).mp h_inf_bot with h_cent_bot | h_comm_bot
  · -- Case 2 (h_cent_bot): C_P(K) = ⊥ ⇒ P = ⁅P,K⁆ ⊆ commutator G ⇒ p ∤ |G:G'|
    right
    -- P ≤ commutator G
    have hP_le_comm : (P : Subgroup G) ≤ commutator G := by
      rw [← h_sup_top, h_cent_bot, bot_sup_eq]
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    -- (commutator G).index ∣ (P : Subgroup G).index (P ≤ G' ⇒ |G:G'| ∣ |G:P|)
    -- p ∣ (commutator G).index ⇒ p ∣ (P : Subgroup G).index, contradicting Sylow
    intro h_dvd_idx
    have h_idx_dvd : (commutator G).index ∣ (P : Subgroup G).index :=
      Subgroup.index_dvd_of_le hP_le_comm
    exact P.not_dvd_index (h_dvd_idx.trans h_idx_dvd)
  · -- Case 1 (h_comm_bot): ⁅P,K⁆ = ⊥ ⇒ K centralizes P ⇒ N(P) ≤ C(P) ⇒ Burnside
    left
    -- K centralizes P (commutator_eq_bot_iff_le_centralizer + commutator_comm)
    have hK_cent_P : K ≤ Subgroup.centralizer (P : Subgroup G) := by
      have h_comm_KP : (⁅K, (P : Subgroup G)⁆ : Subgroup G) = ⊥ := by
        rw [Subgroup.commutator_comm]; exact h_comm_bot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h_comm_KP
    -- (P : Subgroup G) ≤ centralizer P (abelian)
    have hP_cent_P : (P : Subgroup G) ≤ Subgroup.centralizer (P : Subgroup G) := by
      intro a haP
      rw [Subgroup.mem_centralizer_iff]
      intro b hbP
      have h := mul_comm (⟨b, hbP⟩ : ↥(P : Subgroup G)) ⟨a, haP⟩
      exact congrArg Subtype.val h
    -- N = (P : Subgroup G) ⊔ K (from complement P_N ⊔ K' = ⊤ via Subgroup.map)
    have hN_eq : (P : Subgroup G) ⊔ K = N := by
      have h_sup_top_PN : P_N ⊔ K' = ⊤ := hK'_compl.sup_eq_top
      calc (P : Subgroup G) ⊔ K
          = P_N.map N.subtype ⊔ K := by
            rw [Subgroup.map_subgroupOf_eq_of_le hP_le_N]
        _ = P_N.map N.subtype ⊔ K'.map N.subtype := rfl
        _ = (P_N ⊔ K').map N.subtype := (Subgroup.map_sup _ _ _).symm
        _ = (⊤ : Subgroup ↥N).map N.subtype := by rw [h_sup_top_PN]
        _ = N := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    -- N ≤ centralizer P
    have h_NP_le_CP : N ≤ Subgroup.centralizer (P : Subgroup G) := by
      rw [← hN_eq]
      exact sup_le hP_cent_P hK_cent_P
    -- Burnside: M := ker(transferSylow P h_NP_le_CP) is normal p-complement
    -- |M| coprime to p (mathlib)
    have h_M_no_p : ¬ p ∣ Nat.card (MonoidHom.transferSylow P h_NP_le_CP).ker :=
      MonoidHom.not_dvd_card_ker_transferSylow P h_NP_le_CP
    -- commutator G ≤ M (since ↥P abelian via IsCyclic ⇒ transferSylow hom to abelian)
    have h_comm_le_M : commutator G ≤ (MonoidHom.transferSylow P h_NP_le_CP).ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
      -- ↥P abelian (IsCyclic ⇒ IsMulCommutative)
      haveI hPab : IsMulCommutative ↥(P : Subgroup G) := inferInstance
      exact mul_comm _ _
    -- p ∤ |commutator G|
    intro h_p_dvd_comm
    exact h_M_no_p (h_p_dvd_comm.trans (Subgroup.card_dvd_of_le h_comm_le_M))

/-- Helper: in any finite cyclic group, the element of order 2 is unique (if exists).
mathlib `IsCyclic.card_orderOf_eq_totient` + `Nat.totient_two = 1` + Subsingleton. -/
private lemma cyclic_finite_unique_order_two
    {P : Type*} [Group P] [Finite P] [IsCyclic P] {s t : P}
    (hs_ord : orderOf s = 2) (ht_ord : orderOf t = 2) : s = t := by
  haveI : Fintype P := Fintype.ofFinite P
  classical
  have h2_dvd : (2 : ℕ) ∣ Fintype.card P := by
    rw [← hs_ord]; exact orderOf_dvd_card
  have h_card : Fintype.card {x : P // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient h2_dvd, Nat.totient_two]
  haveI : Subsingleton {x : P // orderOf x = 2} :=
    Fintype.card_le_one_iff_subsingleton.mp h_card.le
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨s, hs_ord⟩ : {x : P // orderOf x = 2}) ⟨t, ht_ord⟩)

/-- **Isaacs Cor 5.19** (cyclic Sylow_2 版): `G` 非可換 finite + `P ∈ Syl_2(G)` cyclic
非自明 ⇒ `G` 単純でない.

Isaacs 原版は `P = A × B` with `A` cyclic strictly largest (本実装は `B = ⊥` の特殊化).
原版への一般化は同じ Thm 5.18 強形 + 適切な characteristic 部分群選択で extensible.

**証明**: `P` cyclic Sylow_2, `|P| = 2^a, a ≥ 1`. Cauchy で order-2 元 `t ∈ P` を取る.
任意 `n ∈ N_G(P)` で `n * t * n⁻¹ ∈ P` (normalizer) かつ order 2 (semiconjugate);
cyclic finite group の unique order-2 element (`cyclic_finite_unique_order_two`) で
`n * t * n⁻¹ = t`, ゆえに `t ∈ Z(N_G(P))`. Thm 5.18 強形
(`eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer`) で
`t ∈ G' ⇒ t = 1` だが `orderOf t = 2`, 矛盾 ⇒ `G' < G`. `G` simple なら
`commutator G ∈ {⊥, ⊤}`, `G' ⊊ G` ⇒ `G' = ⊥` ⇒ `G` abelian, 非可換と矛盾. -/
theorem not_isSimpleGroup_of_isCyclic_sylow_two
    [Finite G] (hG_nonab : ¬ IsMulCommutative G)
    (P : Sylow 2 G) [P.FiniteIndex]
    [hPcyc : IsCyclic ↥(P : Subgroup G)]
    (hP_nontrivial : (P : Subgroup G) ≠ ⊥) :
    ¬ IsSimpleGroup G := by
  intro hSimp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- |P| = 2^a, a ≥ 1
  obtain ⟨a, hP_card⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have ha_pos : 1 ≤ a := by
    by_contra h
    push_neg at h
    interval_cases a
    rw [pow_zero] at hP_card
    exact hP_nontrivial (Subgroup.eq_bot_of_card_eq _ hP_card)
  -- Cauchy in ↥P: ∃ t ∈ P with orderOf t = 2
  have h_2_dvd : (2 : ℕ) ∣ Nat.card ↥(P : Subgroup G) := by
    rw [hP_card]
    exact dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp ha_pos)
  obtain ⟨⟨t, ht_inP⟩, ht_ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(P : Subgroup G)) 2 h_2_dvd
  have ht_ord_g : orderOf t = 2 := (Subgroup.orderOf_coe _).trans ht_ord
  have ht_ne_one : t ≠ 1 := by
    intro h_eq; rw [h_eq, orderOf_one] at ht_ord_g; norm_num at ht_ord_g
  -- t ∈ Z(N(P)): for n ∈ N(P), n * t * n⁻¹ = t (cyclic unique order-2)
  have ht_central :
      ∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), n * t = t * n := by
    intro n hn
    have hntn_inP : n * t * n⁻¹ ∈ (P : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hn t).mp ht_inP
    have hntn_ord : orderOf (n * t * n⁻¹) = 2 := by
      have h_sb : SemiconjBy n t (n * t * n⁻¹) := by
        show n * t = (n * t * n⁻¹) * n; group
      exact (SemiconjBy.orderOf_eq n h_sb).symm.trans ht_ord_g
    -- Lift to ↥P, use cyclic_finite_unique_order_two
    have ht_P_ord : orderOf (⟨t, ht_inP⟩ : ↥(P : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact ht_ord_g
    have hntn_P_ord :
        orderOf (⟨n * t * n⁻¹, hntn_inP⟩ : ↥(P : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hntn_ord
    have h_eq_P : (⟨n * t * n⁻¹, hntn_inP⟩ : ↥(P : Subgroup G)) = ⟨t, ht_inP⟩ :=
      cyclic_finite_unique_order_two hntn_P_ord ht_P_ord
    have h_g_eq : n * t * n⁻¹ = t := congrArg Subtype.val h_eq_P
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [h_g_eq]
  -- Apply 5.18 strong: t ∉ commutator G
  haveI hPab : IsMulCommutative ↥(P : Subgroup G) := inferInstance
  have h_t_not_in_comm : t ∉ commutator G := by
    intro h_t_in
    exact ht_ne_one
      (eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer P
        h_t_in ht_inP ht_central)
  -- G simple ⇒ commutator G ∈ {⊥, ⊤}. ≠ ⊤ (else t ∈ ⊤). So = ⊥ ⇒ G abelian, 矛盾
  have h_comm_normal : (commutator G).Normal := inferInstance
  rcases hSimp.eq_bot_or_eq_top_of_normal _ h_comm_normal with h_bot | h_top
  · -- commutator G = ⊥ ⇒ G abelian (直接 commutator element 経由)
    apply hG_nonab
    refine ⟨⟨fun a b => ?_⟩⟩
    have h_comm_mem : ⁅a, b⁆ ∈ commutator G := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h_bot, Subgroup.mem_bot] at h_comm_mem
    rwa [commutatorElement_eq_one_iff_mul_comm] at h_comm_mem
  · -- commutator G = ⊤ ⇒ t ∈ commutator G, contradiction
    apply h_t_not_in_comm
    rw [h_top]; exact Subgroup.mem_top t

end -- 5C

section /- 5D: Focal Subgroup theorem (pp. 167-173) -/

/-! ### Isaacs §5D (Focal Subgroup Theorem)

mathlib `Focal.lean` で Focal Subgroup Theorem が完全実装済 (Boyang Hu, 2026):

- `Subgroup.focalSubgroup`, `focalSubgroupOf`: focal subgroup の定義 (Isaacs §5D 冒頭).
- `Subgroup.transferFocal`: `G →* H/H*` の transfer.
- **`Subgroup.commutator_inf_eq_focalSubgroup`** = **Focal Subgroup Theorem (Thm 5.21)** ⭐.

**Thm 5.20** (ker(v) = A^p(G)) = `ker_restrict_transferFocal_eq_focalSubgroupOf` で同等内容
(Isaacs 流は `A^p(G) = O^p(G) · G'` の表示だが, mathlib では `focalSubgroupOf` 表示で同値).

**Cor 5.22, 5.23** (`H controls fusion ⇒ controls p-transfer`): mathlib transferFocal +
Isaacs 流の "controls fusion" 定義の橋渡し. 形式化保留 (FT 経路で BG 直接引用なし).

**Thm 5.24** (G simple, H maximal nilpotent ⇒ H は p-group; Wielandt): BG/Peterfalvi
直接被引用無し. 保留. -/

end -- 5D

section /- 5E: Frobenius normal p-complement (pp. 173-180) -/

/-! ### Isaacs §5E (Frobenius normal p-complement)

**FT クリティカル**. mathlib 未収載で新規実装が必要.

- **Def** `HasNormalPComplement p G` — 「G は normal p-complement を持つ」.
- **Thm 5.25** (Sylow controls own fusion ⇔ normal p-comp): 形式化保留.
- **Thm 5.26 Frobenius** (3 同値条件): 形式化保留 (Lem 5.27 + Lem 5.28 + 5.25 経由).
- **Lem 5.27** (1 ⇒ 2 ⇒ 3 易方向): ✅ 完成. Part 1 (`hasNormalPComplement_of_subgroup`) +
  Part 2 (`isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement`).
- **Lem 5.28** (3 ⇒ Sylow 共役 via C_G(P ⊓ Q)): 形式化保留 (5.26 鍵).
- **Cor 5.29** (q ∤ p^e-1 ⇒ normal p-comp): 5.26 + p-group action.
- **Cor 5.30** (p odd, 全 order-p 中心 ⇒ normal p-comp): 5.26 + Ch.4 §4D Thm 4.36 待ち. -/

/-- "G has a normal p-complement" — there exists a normal subgroup `N : Subgroup G` such
that for every Sylow `p`-subgroup `P`, `(N, P)` form a complement pair (`IsComplement'`).

For finite `G`, this is equivalent to existence of normal `N` with `|N|` coprime to `p`
and `|G:N|` a `p`-power. mathlib 未収載のため新規定義. -/
def HasNormalPComplement (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧
    ∀ P : Sylow p G, Subgroup.IsComplement' N (P : Subgroup G)

/-! **Isaacs Thm 5.25** (Sylow controls own G-fusion ⇔ normal p-complement):
形式化保留. Focal Subgroup Theorem (5.21) + Sylow conjugacy.

**Isaacs Thm 5.26 Frobenius normal p-complement** ⭐ **FT クリティカル**:
`G` は normal p-complement を持つ ⇔ 任意の p-subgroup `X` で `N_G(X)/C_G(X)` が p-group.

3 同値条件のうち本 statement は (1) ⇔ (3). 5.25 経由で (1) ⇔ (2) (全 p-local 部分群
が normal p-comp) も導出.

**証明骨子** (Isaacs p.174-177):
- (1) ⇒ (2) ⇒ (3): **Lem 5.27** (本ファイル下記). 易方向.
- (3) ⇒ (1): **Lem 5.28** (Sylow conjugacy via centralizer) + 5.25.

形式化保留. -/

/-- **Isaacs Lem 5.27 part 1 (1 ⇒ 2, strong form)**: G が normal p-complement を持つなら,
任意の subgroup `H ≤ G` も normal p-complement を持つ.

`H` の p-complement は `N.subgroupOf H = N ⊓ H` viewed inside `H` (witness).

**証明** (Isaacs p.174): `N` は `G` で normal なので `N.subgroupOf H` は `H` で normal
(`Normal.subgroupOf`). Cardinality:

* 任意 Sylow `P₀ : Sylow p G` で `IsComplement' N P₀` ⇒ `N.index = |P₀| = p^v_p(|G|)`,
  `|N|` coprime to `p` (Sylow `not_dvd_index` + `IsComplement'.index_eq_card`).
* `(N.subgroupOf H).index ∣ N.index` (`relIndex_dvd_index_of_normal`) ⇒ p-power.
* `|N.subgroupOf H| = |M.map H.subtype| = |N ⊓ H| ∣ |N|` ⇒ coprime to `p`.
* 任意 Sylow `Q : Sylow p ↥H` で `|Q| = p^v_p(|H|)` (`Sylow.card_eq_multiplicity`).
* Lagrange + `Nat.factorization_mul` で `v_p(|H|) = a` (M.index = p^a の指数).
  ⇒ `|Q| = p^a = M.index`, よって `|N.subgroupOf H| * |Q| = |H|` + Coprime.
* `Subgroup.isComplement'_of_coprime` 適用. -/
theorem hasNormalPComplement_of_subgroup [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : HasNormalPComplement p G) (H : Subgroup G) :
    HasNormalPComplement p ↥H := by
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  haveI : N.Normal := hN_normal
  refine ⟨N.subgroupOf H, hN_normal.subgroupOf H, fun Q => ?_⟩
  set M : Subgroup ↥H := N.subgroupOf H with hM_def
  -- Get any Sylow P₀ in G
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p G))
  -- |P₀| = p^v_p(|G|)
  have hP₀_card : Nat.card ↥(P₀ : Subgroup G) = p ^ (Nat.card G).factorization p :=
    P₀.card_eq_multiplicity
  -- N.index = |P₀|
  have hN_idx_eq_P₀ : N.index = Nat.card ↥(P₀ : Subgroup G) :=
    (hN_compl P₀).symm.index_eq_card
  -- ¬ p ∣ |N|
  have h_p_ndvd_N : ¬ p ∣ Nat.card ↥N := by
    rw [← (hN_compl P₀).index_eq_card]; exact P₀.not_dvd_index
  -- |M| ∣ |N|: M ≃ N ⊓ H ≤ N via H.subtype
  have hM_card_dvd_N : Nat.card ↥M ∣ Nat.card ↥N := by
    have h_inj : Function.Injective (H.subtype : ↥H → G) := Subtype.coe_injective
    have h_card_eq : Nat.card ↥M = Nat.card ↥(M.map H.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective M H.subtype h_inj).toEquiv
    rw [h_card_eq, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  -- ¬ p ∣ |M|
  have h_p_ndvd_M : ¬ p ∣ Nat.card ↥M := fun h => h_p_ndvd_N (h.trans hM_card_dvd_N)
  -- M.index ∣ N.index (relIndex_dvd_index_of_normal)
  have hM_idx_dvd_Nidx : M.index ∣ N.index :=
    Subgroup.relIndex_dvd_index_of_normal N H
  -- M.index = p^a for some a ≤ v_p(|G|)
  obtain ⟨a, _, hM_idx_pow⟩ : ∃ a ≤ (Nat.card G).factorization p, M.index = p ^ a :=
    (Nat.dvd_prime_pow Fact.out).mp ((hN_idx_eq_P₀.trans hP₀_card) ▸ hM_idx_dvd_Nidx)
  -- |Q| = p^v_p(|H|)
  have hQ_card : Nat.card ↥(Q : Subgroup ↥H) = p ^ (Nat.card ↥H).factorization p :=
    Q.card_eq_multiplicity
  -- |H| = |M| * M.index (Lagrange)
  have hL_M : Nat.card ↥M * M.index = Nat.card ↥H := by
    rw [mul_comm]; exact M.index_mul_card
  -- v_p(|H|) = a (from |M| * p^a = |H|, |M| coprime to p ⇒ v_p(|M|) = 0)
  have h_va : (Nat.card ↥H).factorization p = a := by
    have h_card_eq : Nat.card ↥M * p ^ a = Nat.card ↥H := by
      rw [← hM_idx_pow]; exact hL_M
    have hp_pos : 0 < p := (Fact.out (p := p.Prime)).pos
    have hM_ne : Nat.card ↥M ≠ 0 := Nat.card_pos.ne'
    have hpa_ne : p ^ a ≠ 0 := pow_ne_zero a hp_pos.ne'
    rw [← h_card_eq, Nat.factorization_mul hM_ne hpa_ne, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd h_p_ndvd_M,
        Nat.factorization_pow_self Fact.out, zero_add]
  -- |Q| = M.index
  have hQ_card_eq : Nat.card ↥(Q : Subgroup ↥H) = M.index := by
    rw [hQ_card, h_va, ← hM_idx_pow]
  -- |M| * |Q| = |H|
  have h_mul_eq : Nat.card ↥M * Nat.card ↥(Q : Subgroup ↥H) = Nat.card ↥H := by
    rw [hQ_card_eq]; exact hL_M
  -- Coprime |M| |Q|: |M| coprime to p ⇒ Coprime |M| p ⇒ Coprime |M| p^a
  have h_coprime : Nat.Coprime (Nat.card ↥M) (Nat.card ↥(Q : Subgroup ↥H)) := by
    rw [hQ_card, h_va]
    exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_p_ndvd_M).symm).pow_right a
  exact Subgroup.isComplement'_of_coprime h_mul_eq h_coprime

/-- `(C_G(X)).subgroupOf (N_G(X))` は `N_G(X)` で normal (kernel of `normalizerMonoidHom`).
mathlib `normalizerMonoidHom_ker` 経由で機械的に得られるが、typeclass resolution が
直接行かないので明示 instance 化. -/
instance centralizer_subgroupOf_normalizer_normal (X : Subgroup G) :
    ((Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))).Normal := by
  rw [← X.normalizerMonoidHom_ker]
  infer_instance

/-- **Isaacs Lem 5.27 part 2 (2 ⇒ 3)**: 仮定「∀ 非自明 p-subgroup `X` ⊆ `G`,
`N_G(X)` が normal p-complement を持つ」 ⇒ 任意 p-subgroup `X` で
`↥N_G(X) / (C_G(X)).subgroupOf N_G(X)` は p-group.

**証明** (Isaacs p.174):
* `X = ⊥` の場合: `centralizer (⊥ : Set G) = ⊤` (1 と全 g が可換) ⇒
  `subgroupOf normalizer = ⊤` ⇒ 商 ↥(normalizer ⊥) ⧸ ⊤ は Subsingleton ⇒ p-group.
* `X ≠ ⊥` の場合: 仮定で `normalizer X` の normal p-complement `K'` を得る.
  `X.subgroupOf (normalizer X)` (`X_n`) は normal (`normal_in_normalizer`),
  `K'` も normal. `K' ⊓ X_n = ⊥` (|K'| coprime to p, |X_n| = |X| p-power,
  `inf_eq_bot_of_coprime`).
  `[K', X_n] ≤ K' ⊓ X_n = ⊥` (`commutator_le_inf` with両 normal) ⇒
  `K' ≤ centralizer X_n` (`commutator_eq_bot_iff_le_centralizer`).
  座標 ↥(normalizer X) → G で `K' ≤ (centralizer X).subgroupOf (normalizer X)` (`C_n`).
  `↥(normalizer X) ⧸ K'` は p-group (Sylow Q complement), `↥(normalizer X) ⧸ C_n` は
  その quotient (`QuotientGroup.map (id) ... K'≤C_n`) ⇒ `IsPGroup.of_surjective` で p-group. -/
theorem isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
    [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p X →
        HasNormalPComplement p ↥(Subgroup.normalizer (X : Set G)))
    (X : Subgroup G) (hXp : IsPGroup p X) :
    IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
      (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  -- 統一戦略: `C_n := (centralizer X).subgroupOf (normalizer X)` の `index` が `p` 乗
  -- であることを示し, `IsPGroup.of_card` を介して `↥N ⧸ C_n` が p-group であることを導く.
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN_def
  -- ∃ b, C_n.index = p^b を示せばよい
  suffices h_idx_pow : ∃ b, ((Subgroup.centralizer (X : Set G)).subgroupOf N).index = p ^ b by
    obtain ⟨b, hb⟩ := h_idx_pow
    refine IsPGroup.of_card (n := b) ?_
    rw [← Subgroup.index_eq_card]; exact hb
  -- 場合分け
  by_cases hX_bot : X = ⊥
  · -- X = ⊥: centralizer = ⊤ ⇒ subgroupOf = ⊤ ⇒ index = 1 = p^0
    refine ⟨0, ?_⟩
    rw [pow_zero]
    have hSubgroup_top : (Subgroup.centralizer (X : Set G)).subgroupOf N = ⊤ := by
      ext ⟨g, hg⟩
      refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro b hb
      subst hX_bot
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hb
      rw [hb, one_mul, mul_one]
    rw [hSubgroup_top, Subgroup.index_top]
  · -- X ≠ ⊥: hypothesis gives K' normal p-complement, K' ≤ C_n, C_n.index ∣ K'.index = p^a
    obtain ⟨K', hK'_normal, hK'_compl⟩ := h X hX_bot hXp
    haveI : K'.Normal := hK'_normal
    let X_n : Subgroup ↥N := X.subgroupOf N
    haveI hX_n_normal : X_n.Normal := by
      change (X.subgroupOf (Subgroup.normalizer (X : Set G))).Normal
      exact Subgroup.normal_in_normalizer
    -- Sylow Q in ↥N
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p ↥N))
    have hQ_compl : Subgroup.IsComplement' K' (Q : Subgroup ↥N) := hK'_compl Q
    -- ¬ p ∣ |K'| (Sylow not_dvd_index + IsComplement'.index_eq_card)
    have h_p_ndvd_K' : ¬ p ∣ Nat.card ↥K' := by
      rw [← hQ_compl.index_eq_card]; exact Q.not_dvd_index
    -- X_n p-group (|X_n| = |X|)
    have h_X_n_pg : IsPGroup p X_n := by
      have hX_le_N : X ≤ N := Subgroup.le_normalizer
      have h_card_eq : Nat.card ↥X_n = Nat.card ↥X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_N).toEquiv
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
      exact IsPGroup.of_card (h_card_eq.trans hk)
    -- K' ⊓ X_n = ⊥ (coprime cards)
    have h_inf_bot : K' ⊓ X_n = ⊥ := by
      apply Subgroup.inf_eq_bot_of_coprime
      obtain ⟨k, hX_n_card⟩ := IsPGroup.iff_card.mp h_X_n_pg
      rw [hX_n_card]
      exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_p_ndvd_K').symm).pow_right k
    -- [K', X_n] = ⊥ (commutator_le_inf with K', X_n both normal)
    have h_comm_bot : ⁅K', X_n⁆ = ⊥ :=
      le_bot_iff.mp (h_inf_bot ▸ Subgroup.commutator_le_inf K' X_n)
    -- K' ≤ centralizer (X_n : Set ↥N)
    have h_K'_cent : K' ≤ Subgroup.centralizer (X_n : Set ↥N) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h_comm_bot
    -- K' ≤ (centralizer X).subgroupOf N
    have h_K'_le_C_n : K' ≤ (Subgroup.centralizer (X : Set G)).subgroupOf N := by
      intro k hk
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro x hxX
      have hxN : x ∈ N := Subgroup.le_normalizer hxX
      have hx_in_Xn : (⟨x, hxN⟩ : ↥N) ∈ X_n := by
        change (⟨x, hxN⟩ : ↥N) ∈ X.subgroupOf N
        rw [Subgroup.mem_subgroupOf]; exact hxX
      have hkx_eq : (⟨x, hxN⟩ : ↥N) * k = k * (⟨x, hxN⟩ : ↥N) :=
        Subgroup.mem_centralizer_iff.mp (h_K'_cent hk) ⟨x, hxN⟩ hx_in_Xn
      exact congrArg Subtype.val hkx_eq
    -- K'.index = |Q| (IsComplement'.symm.index_eq_card)
    have hK'_idx : K'.index = Nat.card ↥(Q : Subgroup ↥N) := hQ_compl.symm.index_eq_card
    -- K'.index = p^a (Q is p-group)
    obtain ⟨a, hKa⟩ : ∃ a, K'.index = p ^ a := by
      rw [hK'_idx]; exact IsPGroup.iff_card.mp Q.isPGroup'
    -- C_n.index ∣ K'.index (K' ≤ C_n)
    have hC_n_idx_dvd : ((Subgroup.centralizer (X : Set G)).subgroupOf N).index ∣ K'.index :=
      Subgroup.index_dvd_of_le h_K'_le_C_n
    -- C_n.index = p^b for some b ≤ a
    rcases (Nat.dvd_prime_pow Fact.out).mp (hKa ▸ hC_n_idx_dvd) with ⟨b, _, hb⟩
    exact ⟨b, hb⟩

/-- **Isaacs Cor 5.30** (p odd 中心化): ⭐ **FT 経路で奇数位数仮定との親和性**.
`p` odd, 全 order-`p` 元が `Z(G)` 中心 ⇒ `G` は normal p-complement を持つ.

**証明** (Isaacs p.180): Thm 5.26 で any p-subgroup X に対し N_G(X)/C_G(X) が p-group
を示せばよい. `Q := N_G(X)/C_G(X)` 内の p'-部分 A を取り A が trivial に作用することを
**Ch.4 Thm 4.36** (p>2 + p-群 G + p'-A が order-p 元固定 ⇒ A trivial) で示す. 仮定より
order-p 元は中心で A 不変, 中心で固定 ⇒ Thm 4.36 適用条件成立.

**実装状態**: Ch.4 §4D Thm 4.36 完成待ち. -/
theorem normal_p_complement_of_order_p_central_odd
    [Finite G] {p : ℕ} [Fact p.Prime] (_hp_odd : p ≠ 2)
    (_hCent : ∀ g : G, orderOf g = p → g ∈ Subgroup.center G) :
    HasNormalPComplement p G := by
  sorry

end -- 5E

end OddOrder.Isaacs.Ch05
