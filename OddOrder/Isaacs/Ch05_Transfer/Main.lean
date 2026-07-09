/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Focal
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main

open scoped commutatorElement
open scoped IsMulCommutative -- rc2: IsMulCommutative→CommGroup/Monoid now scoped

/-!
# OddOrder.Isaacs.Ch05 — Transfer

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 5
"Transfer" (pp. 147-180) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 5A | Transfer 定義・welldefinedness・準同型性 | 5.1 – 5.4 | mathlib + ✅ Thm 5.3 + Cor 5.4 |
| 5B | 中心への transfer = n 乗, Schur, Dietzmann | 5.5 – 5.10 | ✅ 5.8 + 5.9, mathlib + 5.10 保留 |
| 5C | Hall transfer, Burnside, cyclic / abelian Sylow | 5.11 – 5.19 | ✅ Lem 5.11 + Lem 5.12 + Thm 5.17 + Thm 5.18 (強形+弱形) + Cor 5.19 (cyclic Sylow_2 版) |
| 5D | Focal subgroup theorem + p-transfer control | 5.20 – 5.24 | ✅ 5.20-5.23; 5.24 保留 |
| 5E | Frobenius normal p-complement + 系 | 5.25 – 5.30 | ✅ 5.25-5.30 |

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
      ((haveI := hPab; (inferInstance : CommGroup ↥(P : Subgroup G))))
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
        ((haveI := hPab; (inferInstance : CommGroup ↥(P : Subgroup G))))
          (MonoidHom.id (P : Subgroup G)) _) z₀.val).val = _
    rw [@MonoidHom.transfer_eq_pow G _ (P : Subgroup G) (P : Subgroup G)
          ((haveI := hPab; (inferInstance : CommGroup ↥(P : Subgroup G))))
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
  ✅ quotient `out` 代表元版 + transfer-kernel 版.
- **Thm 5.7 Schur** (`|G:Z(G)| < ∞ ⇒ G' 有限`): mathlib
  `Subgroup.card_commutator_le_of_finite_commutatorSet` 直接 (bound 付き強化版).
- **Thm 5.10 Dietzmann** (`X ⊆ G` 有限・共役閉・∃n, x^n=1 ⇒ `⟨X⟩` 有限):
  mathlib 未収載. Schur 5.7 の証明では mathlib `closureCommutatorRepresentatives` 経路
  で代替されているため独立 Dietzmann の必要なし. 形式化保留. -/

/-- A central factor on the right of the left commutator input does not change the commutator. -/
lemma commutatorElement_mul_center_left {z x y : G} (hz : z ∈ Subgroup.center G) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hzy : z * y = y * z := ((Subgroup.mem_center_iff.mp hz) y).symm
  simp [commutatorElement_def, hzy, mul_assoc]

/-- A central factor on the right of the right commutator input does not change the commutator. -/
lemma commutatorElement_mul_center_right {x z y : G} (hz : z ∈ Subgroup.center G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have hzx : z * x⁻¹ = x⁻¹ * z := ((Subgroup.mem_center_iff.mp hz) x⁻¹).symm
  simp [commutatorElement_def, hzx, mul_assoc]

/-- **Isaacs Lemma 5.8** (representative form): every commutator is obtained from the
chosen representatives of the two cosets in `G ⧸ Z(G)`.

This is the quotient-`out` version of Isaacs' right-transversal statement. It avoids introducing
a separate bridge API for transversals while retaining the useful formal content. -/
theorem commutatorElement_eq_centerQuotient_out (x y : G) :
    ⁅x, y⁆ =
      ⁅(QuotientGroup.mk' (Subgroup.center G) x).out,
        (QuotientGroup.mk' (Subgroup.center G) y).out⁆ := by
  let qx : G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G) x
  let qy : G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G) y
  have hqx :
      QuotientGroup.mk' (Subgroup.center G) qx.out =
        QuotientGroup.mk' (Subgroup.center G) x := by
    simp [qx]
  have hqy :
      QuotientGroup.mk' (Subgroup.center G) qy.out =
        QuotientGroup.mk' (Subgroup.center G) y := by
    simp [qy]
  obtain ⟨zx, hzx, hx⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center G)).mp hqx
  obtain ⟨zy, hzy, hy⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center G)).mp hqy
  calc
    ⁅x, y⁆ = ⁅qx.out * zx, y⁆ := by rw [hx]
    _ = ⁅qx.out, y⁆ := commutatorElement_mul_center_left hzx
    _ = ⁅qx.out, qy.out * zy⁆ := by rw [hy]
    _ = ⁅qx.out, qy.out⁆ := commutatorElement_mul_center_right hzy
    _ = ⁅(QuotientGroup.mk' (Subgroup.center G) x).out,
          (QuotientGroup.mk' (Subgroup.center G) y).out⁆ := rfl

/-- **Isaacs Lemma 5.8**: if `Z(G)` has finite index, then there are only finitely many
commutators in `G`. -/
theorem finite_commutatorSet_of_finiteIndex_center
    [Subgroup.FiniteIndex (Subgroup.center G)] : Finite (commutatorSet G) := by
  classical
  letI := (Subgroup.center G).fintypeQuotientOfFiniteIndex
  let f : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) → G := fun q =>
    ⁅q.1.out, q.2.out⁆
  have hsubset : commutatorSet G ⊆ Set.range f := by
    intro c hc
    rcases (mem_commutatorSet_iff.mp hc) with ⟨x, y, rfl⟩
    exact ⟨(QuotientGroup.mk' (Subgroup.center G) x,
        QuotientGroup.mk' (Subgroup.center G) y),
      (commutatorElement_eq_centerQuotient_out x y).symm⟩
  exact ((Set.finite_range f).subset hsubset).to_subtype

/-- **Isaacs Thm 5.7** (Schur): if `Z(G)` has finite index, then `G'` is finite. -/
theorem finite_commutator_of_finiteIndex_center
    [Subgroup.FiniteIndex (Subgroup.center G)] : Finite (commutator G) := by
  haveI : Finite (commutatorSet G) := finite_commutatorSet_of_finiteIndex_center (G := G)
  infer_instance

/-- **Isaacs Cor 5.9** (subgroup form): if `Z(G)` has finite index, every element of `G'`
is killed by the index `|G : Z(G)|`. -/
theorem pow_index_center_eq_one_of_mem_commutator
    [Subgroup.FiniteIndex (Subgroup.center G)] {g : G} (hg : g ∈ commutator G) :
    g ^ (Subgroup.center G).index = 1 := by
  have h := Abelianization.commutator_subset_ker (MonoidHom.transferCenterPow G) hg
  simpa only [MonoidHom.mem_ker, Subtype.ext_iff, MonoidHom.transferCenterPow_apply,
    OneMemClass.coe_one] using h

/-- **Isaacs Cor 5.9**: if `Z(G)` has finite index, every commutator has
`|G : Z(G)|`-th power equal to `1`. -/
theorem commutatorElement_pow_index_center_eq_one
    [Subgroup.FiniteIndex (Subgroup.center G)] (x y : G) :
    ⁅x, y⁆ ^ (Subgroup.center G).index = 1 := by
  apply pow_index_center_eq_one_of_mem_commutator
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

end -- 5B

/-- "G has a normal p-complement" — there exists a normal subgroup `N : Subgroup G` such
that for every Sylow `p`-subgroup `P`, `(N, P)` form a complement pair (`IsComplement'`).

For finite `G`, this is equivalent to existence of normal `N` with `|N|` coprime to `p`
and `|G:N|` a `p`-power. mathlib 未収載のため新規定義. -/
def HasNormalPComplement (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧
    ∀ P : Sylow p G, Subgroup.IsComplement' N (P : Subgroup G)

section /- 5C: Hall transfer, Burnside, cyclic / abelian Sylow (pp. 159-167) -/

/-! ### Isaacs §5C (Hall transfer + Burnside)

- **Lemma 5.11** (Hall index transfer): `ker_transfer_sup_eq_top_of_hall` ✅.
- **Lemma 5.12** (`N_G(P)` controls `C_G(P)` fusion): `normalizer_controls_centralizer_fusion` ✅.
- **Thm 5.13 Burnside**: `hasNormalPComplement_of_sylow_normalizer_le_centralizer` ✅.
- **Cor 5.14**: `IsCyclic.isComplement'` 直接.
- **Cor 5.15** (Z-group solvable): mathlib `IsZGroup` instance 直接.
- **Thm 5.16** (Z-group 構造): mathlib `IsZGroup` API 直接.
- **Thm 5.17** (cyclic Sylow_p ⇒ p∤|G'| or p∤|G:G'|): ✅ `isaacs_thm_5_17`
  (Ch.4 §4D Thm 4.28 + 4.34 Fitting + cyclic-chain helper).
- **Cor 5.19** (Sylow_2 cyclic direct factor ⇒ 非単純): 形式化保留. -/

/-! ### Ch.4 §4D adapter

Thm 5.17 は Ch.4 §4D **Thm 4.28 + 4.34 Fitting** に依存する. Ch.4 の
`fixedPointsOfMulAut` / `actionCommutator` 形式を、Ch.5 の subgroup conjugation 形式へ
ここで変換する. -/

/-- **Isaacs Thm 4.34 (Fitting)** — Ch.5 subgroup-conjugation adapter.

`A` (= subgroup `K` of `G` with `K ≤ N_G(P)`) が abelian subgroup `P` に conjugation 経由で
作用. `(|P|, |K|) = 1` (coprime) ⇒ `P = C_P(K) × ⁅P, K⁆` (internal direct product, element form).

**証明戦略** (Isaacs p.142, θ trick):
* θ : ↥P → ↥P, θ(p) = ∏_{k ∈ K} k • p. P abelian なので well-def + homomorphism.
* θ(p) ∈ C_P(K) (θ は K 作用と可換).
* `p ∈ C_P(K)` で θ(p) = p^|K|; (|P|, |K|) = 1 ⇒ θ(p) = 1 ⇒ p = 1.
* ⁅P, K⁆ ⊆ ker θ (各 [p, k] が ker に入る).
* ⇒ C_P(K) ⊓ ⁅P, K⁆ = ⊥.
* p^|K| = θ(p) · h with h ∈ ⁅P, K⁆ (元素計算). Bezout で p ∈ C_P(K) · ⁅P, K⁆.

This is the form needed by Isaacs Thm 5.17: a subgroup `K ≤ N_G(P)` acts on the
abelian subgroup `P` by conjugation. Ch.4 gives the same result for an abstract
automorphism action on the group `↥P`; this theorem translates fixed points to
`C_G(K) ∩ P` and action-commutators to `⁅P, K⁆`. -/
theorem fitting_coprime_abelian_decomp
    {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} [IsMulCommutative ↥P]
    {K : Subgroup G} (hK_norm : K ≤ Subgroup.normalizer P)
    (h_coprime : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K)) :
    (Subgroup.centralizer (K : Set G) ⊓ P) ⊓ (⁅P, K⁆ : Subgroup G) = ⊥ ∧
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊔ (⁅P, K⁆ : Subgroup G) = P := by
  classical
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let KN : Subgroup N := K.subgroupOf N
  let φ : KN →* MulAut P := MulDistribMulAction.toMulAut KN P
  have hKN_card : Nat.card KN = Nat.card K :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := N)
        (by simpa [N] using hK_norm)).toEquiv
  have hCop : Nat.Coprime (Nat.card KN) (Nat.card P) := by
    rw [hKN_card]
    exact h_coprime.symm
  have hSolv : IsSolvable KN ∨ IsSolvable P := by
    right
    infer_instance
  have h_inf_P :
      Subgroup.fixedPointsOfMulAut φ ⊓
        _root_.OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
    _root_.OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian
      φ hCop
  have h_sup_P :
      Subgroup.fixedPointsOfMulAut φ ⊔
        _root_.OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤ :=
    _root_.OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      (φ := φ) hCop hSolv
  have h_fixed_map_le : (Subgroup.fixedPointsOfMulAut φ).map P.subtype ≤
      Subgroup.centralizer (K : Set G) ⊓ P := by
    intro x hx
    rw [Subgroup.mem_inf]
    rcases hx with ⟨xp, hxp_fixed, rfl⟩
    constructor
    · rw [Subgroup.mem_centralizer_iff]
      intro y hyK
      let yN : N := ⟨y, by simpa [N] using hK_norm hyK⟩
      let yKN : KN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyK⟩
      have hfix : (φ yKN) xp = xp := hxp_fixed yKN
      have hconj : y * (xp : G) * y⁻¹ = (xp : G) := by
        exact congrArg Subtype.val hfix
      calc y * (xp : G) = (y * (xp : G) * y⁻¹) * y := by group
        _ = (xp : G) * y := by rw [hconj]
    · exact xp.property
  have h_ac_map_le :
      (_root_.OddOrder.Isaacs.Ch04.actionCommutator φ).map P.subtype ≤
        (⁅P, K⁆ : Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap,
      _root_.OddOrder.Isaacs.Ch04.actionCommutator_le_iff]
    intro a x
    rw [Subgroup.mem_comap]
    change ((a : N).val * (x : G) * (a : N).val⁻¹) * (x : G)⁻¹ ∈
      (⁅P, K⁆ : Subgroup G)
    have haK : ((a : N).val : G) ∈ K := by
      have ha := a.property
      rwa [Subgroup.mem_subgroupOf] at ha
    have hxP : (x : G) ∈ P := x.property
    have hcomm : (⁅(x : G), ((a : N).val : G)⁆ : G) ∈ (⁅P, K⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hxP haK
    convert (Subgroup.inv_mem _ hcomm) using 1
    group
  have h_comm_le_ac_map :
      (⁅P, K⁆ : Subgroup G) ≤
        (_root_.OddOrder.Isaacs.Ch04.actionCommutator φ).map P.subtype := by
    rw [Subgroup.commutator_le]
    intro x hxP y hyK
    let yN : N := ⟨y, by simpa [N] using hK_norm hyK⟩
    let yKN : KN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyK⟩
    let xP : P := ⟨x, hxP⟩
    have hgen : xP * (φ yKN) xP⁻¹ ∈
        _root_.OddOrder.Isaacs.Ch04.actionCommutator φ :=
      Subgroup.subset_closure ⟨xP, yKN, rfl⟩
    refine ⟨xP * (φ yKN) xP⁻¹, hgen, ?_⟩
    dsimp [φ, xP, yKN, yN]
    change x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹
    group
  have h_inf_bot :
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊓ (⁅P, K⁆ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases Subgroup.mem_inf.mp hx with ⟨hx_centP, hx_comm⟩
    rcases Subgroup.mem_inf.mp hx_centP with ⟨hx_cent, hxP⟩
    let xP : P := ⟨x, hxP⟩
    have hx_fixed : xP ∈ Subgroup.fixedPointsOfMulAut φ := by
      intro a
      apply Subtype.ext
      rcases a with ⟨⟨y, _hyN⟩, hyK⟩
      have hcomm : y * x = x * y := by
        rw [Subgroup.mem_centralizer_iff] at hx_cent
        exact hx_cent y hyK
      change y * x * y⁻¹ = x
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hx_ac : xP ∈ _root_.OddOrder.Isaacs.Ch04.actionCommutator φ := by
      have hx_map :
          x ∈ (_root_.OddOrder.Isaacs.Ch04.actionCommutator φ).map P.subtype :=
        h_comm_le_ac_map hx_comm
      rcases hx_map with ⟨z, hz_ac, hz_val⟩
      have hz_eq : z = xP := Subtype.ext hz_val
      rwa [hz_eq] at hz_ac
    have hxP_bot : xP ∈ (⊥ : Subgroup P) := by
      rw [← h_inf_P]
      exact ⟨hx_fixed, hx_ac⟩
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxP_bot)
  have h_sup_eq :
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊔ (⁅P, K⁆ : Subgroup G) = P := by
    apply le_antisymm
    · exact sup_le inf_le_right (by
        rw [Subgroup.commutator_le]
        intro x hxP y hyK
        have hyN : y ∈ N := by simpa [N] using hK_norm hyK
        have hyxiy : y * x⁻¹ * y⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (P.inv_mem hxP)
        have h_eq : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [show (⁅x, y⁆ : G) = x * y * x⁻¹ * y⁻¹ from rfl, h_eq]
        exact P.mul_mem hxP hyxiy)
    · intro x hxP
      have hx_map_top : x ∈ ((⊤ : Subgroup P).map P.subtype) := by
        exact ⟨⟨x, hxP⟩, Subgroup.mem_top _, rfl⟩
      rw [← h_sup_P, Subgroup.map_sup] at hx_map_top
      exact (sup_le_sup h_fixed_map_le h_ac_map_le) hx_map_top
  exact ⟨h_inf_bot, h_sup_eq⟩

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
  push Not at h_not
  obtain ⟨hH_ne, hK_ne⟩ := h_not
  -- Cauchy in H: ∃ h ∈ H with orderOf h = p
  have hH_pgroup : IsPGroup p ↥H := hP_pgroup.to_le hH_le_P
  obtain ⟨nH, hnH⟩ := IsPGroup.iff_card.mp hH_pgroup
  have hnH_pos : 1 ≤ nH := by
    by_contra h
    push Not at h
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
    push Not at h
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
    ∃ n : G, n ∈ Subgroup.normalizer (P : Set G) ∧ n * x * n⁻¹ = y := by
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

/-- **Isaacs Thm 5.13 (Burnside normal p-complement)**:
if a Sylow `p`-subgroup centralizes its normalizer, then `G` has a normal
`p`-complement.

This adapts mathlib's `MonoidHom.ker_transferSylow_isComplement'`, which gives a
complement for the chosen Sylow subgroup, to this file's `HasNormalPComplement`
predicate requiring the same normal complement for every Sylow subgroup. -/
theorem hasNormalPComplement_of_sylow_normalizer_le_centralizer
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    HasNormalPComplement p G := by
  classical
  let N : Subgroup G := (MonoidHom.transferSylow P hP).ker
  have hNP : Subgroup.IsComplement' N (P : Subgroup G) := by
    simpa [N] using MonoidHom.ker_transferSylow_isComplement' P hP
  refine ⟨N, inferInstance, ?_⟩
  intro Q
  have hdisj : Disjoint N (Q : Subgroup G) := by
    simpa [N] using MonoidHom.ker_transferSylow_disjoint P hP
      (Q : Subgroup G) Q.isPGroup'
  have hcardQ : Nat.card (Q : Subgroup G) = Nat.card (P : Subgroup G) := by
    exact Nat.card_congr (Sylow.equiv Q P).toEquiv
  have hcard : Nat.card N * Nat.card (Q : Subgroup G) = Nat.card G := by
    rw [hcardQ]
    exact hNP.card_mul
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj

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
    (hx_central_N : ∀ n ∈ Subgroup.normalizer (P : Set G), n * x = x * n) :
    x = 1 := by
  -- Setup transfer v : G →* ↥P (P abelian)
  let v : G →* (P : Subgroup G) :=
    @MonoidHom.transfer G _ (P : Subgroup G) (P : Subgroup G)
      ((haveI := hPab; (inferInstance : CommGroup ↥(P : Subgroup G))))
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
        ((haveI := hPab; (inferInstance : CommGroup ↥(P : Subgroup G))))
          (MonoidHom.id (P : Subgroup G)) _) x).val = _
    rw [@MonoidHom.transfer_eq_pow G _ (P : Subgroup G) (P : Subgroup G)
          ((haveI := hPab; (inferInstance : CommGroup ↥(P : Subgroup G))))
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
P Sylow_p). `K ≤ N`, `(|P|, |K|) = 1`. **Thm 4.34 Fitting** adapter:
`P = C_P(K) × ⁅P,K⁆`
(internal direct, `C_P(K) ⊓ ⁅P,K⁆ = ⊥` AND `C_P(K) ⊔ ⁅P,K⁆ = P`).

`P` cyclic + **cyclic_pgroup_inf_eq_bot_iff**: `C_P(K) ⊓ ⁅P,K⁆ = ⊥ ⇒
C_P(K) = ⊥ ∨ ⁅P,K⁆ = ⊥`.

* **Case 1** `⁅P,K⁆ = ⊥`: `K` centralizes `P`. `N = PK` で全要素が `P` と可換 ⇒
  `N ⊆ C_G(P)`. `N(P) ≤ C(P)` ⇒ Burnside (mathlib `ker_transferSylow_isComplement'`)
  で normal `p`-complement `M`. `G/M ≅ P` cyclic ⇒ `G/M` abelian ⇒ `G' ⊆ M`. `M`
  `p'`-group ⇒ `p ∤ |G'|`.

* **Case 2** `C_P(K) = ⊥`: 4.34 sup より `P = ⁅P,K⁆ ⊆ commutator G`. `|G:G'| = |G|/|G'|`,
  Sylow_p 全体が `G'` に入る ⇒ `|G:G'|` の `p`-成分 = 1 ⇒ `p ∤ |G:G'|`.

**実装状態**: Ch.4 §4D Thm 4.28 + 4.34 を subgroup-conjugation adapter で接続済み.
`cyclic_pgroup_inf_eq_bot_iff` も theorem 化済み. -/
theorem isaacs_thm_5_17
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex]
    [hPcyc : IsCyclic ↥(P : Subgroup G)] :
    ¬ p ∣ Nat.card (commutator G) ∨ ¬ p ∣ (commutator G).index := by
  -- P abelian (cyclic)
  haveI hPab : IsMulCommutative ↥(P : Subgroup G) := inferInstance
  -- N := N_G(P), P_N := P.subgroupOf N (normal in N)
  set N := Subgroup.normalizer (P : Set G) with hN_def
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
  -- Apply Thm 4.34 adapter.
  obtain ⟨h_inf_bot, h_sup_top⟩ :=
    fitting_coprime_abelian_decomp hK_le_N h_coprime_PK
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
  -- Cyclic p-group chain: C_P(K) ⊓ ⁅P,K⁆ = ⊥ ⇒ one of them is ⊥.
  rcases (cyclic_pgroup_inf_eq_bot_iff P.isPGroup'
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
    push Not at h
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
      ∀ n ∈ Subgroup.normalizer (P : Set G), n * t = t * n := by
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

**Cor 5.22, 5.23** (`H controls fusion ⇒ controls p-transfer`): ✅ `A^p` equality
form implemented (`A^p(H)=H∩A^p(G)`), without adding a separate transfer-control predicate.

**Thm 5.24** (G simple, H maximal nilpotent ⇒ H は p-group; Wielandt): BG/Peterfalvi
直接被引用無し. 保留. -/

/-- "`K` controls `G`-fusion in `H`": any two elements of `H` conjugate in the
ambient group `G` are already conjugate by an element of `K`.

Isaacs §5C-§5D で使う fusion-control 条件. -/
def _root_.Subgroup.ControlsFusionIn {G : Type*} [Group G] (K H : Subgroup G) : Prop :=
  ∀ ⦃x y : G⦄, x ∈ H → y ∈ H →
    (∃ g : G, g * x * g⁻¹ = y) →
    (∃ u : G, u ∈ K ∧ u * x * u⁻¹ = y)

/-- **Isaacs Cor 5.22 (focal-subgroup core)**:
if `H` controls `G`-fusion in `P`, then the focal subgroup of `P` computed inside
`H` maps to the focal subgroup of `P` computed inside `G`.

This is the substantive focal-subgroup step in the proof that `H` controls
`p`-transfer in `G`; the remaining book argument is an index/kernel comparison
via the focal subgroup theorem. -/
theorem _root_.Subgroup.focalSubgroup_subgroupOf_map_eq_of_controlsFusionIn
    {G : Type*} [Group G] {P H : Subgroup G} (hP_le_H : P ≤ H)
    (hFusion : H.ControlsFusionIn P) :
    (P.subgroupOf H).focalSubgroup.map H.subtype = P.focalSubgroup := by
  apply le_antisymm
  · rw [Subgroup.focalSubgroup_def, MonoidHom.map_closure, Subgroup.focalSubgroup_def]
    apply Subgroup.closure_mono
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨hzPH, x, hxPH, u, rfl⟩
    exact ⟨hzPH, (x : G), hxPH, (u : G), rfl⟩
  · rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgP, x, hxP, u, rfl⟩
    have hyP : u * x * u⁻¹ ∈ P := by
      have hy_eq : u * x * u⁻¹ = (⁅x, u⁆)⁻¹ * x := by
        rw [commutatorElement_def]
        group
      rw [hy_eq]
      exact P.mul_mem (P.inv_mem hgP) hxP
    obtain ⟨v, hvH, hv⟩ := hFusion hxP hyP ⟨u, rfl⟩
    have hcomm_eq : ⁅x, u⁆ = ⁅x, v⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc
        x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
        _ = x * (v * x * v⁻¹)⁻¹ := by rw [hv]
        _ = x * v * x⁻¹ * v⁻¹ := by group
    let xH : H := ⟨x, hP_le_H hxP⟩
    let vH : H := ⟨v, hvH⟩
    let gH : H := ⟨⁅x, u⁆, hP_le_H hgP⟩
    have hgH_focal : gH ∈ (P.subgroupOf H).focalSubgroup := by
      rw [Subgroup.focalSubgroup_def]
      apply Subgroup.subset_closure
      refine ⟨hgP, xH, hxP, vH, ?_⟩
      apply Subtype.ext
      exact hcomm_eq
    exact Subgroup.mem_map_of_mem H.subtype hgH_focal

/-- `OPrime p G` — the smallest normal subgroup of `G` with `p`-power index.
For finite `G`, this is the intersection of all such normal subgroups (Isaacs §5D 冒頭, 'O^p(G)').

mathlib 未収載のため新規定義. 5.25 (⇐), 5.20 等で使用. -/
def OPrime (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ N : {N : Subgroup G // N.Normal ∧ ∃ k : ℕ, N.index = p ^ k}, N.val

/-- `OPrime p G` ≤ any normal subgroup with `p`-power index. -/
lemma OPrime_le {p : ℕ} {G : Type*} [Group G] {N : Subgroup G}
    (hN_normal : N.Normal) {k : ℕ} (hN_idx : N.index = p ^ k) :
    OPrime p G ≤ N :=
  iInf_le_of_le ⟨N, hN_normal, k, hN_idx⟩ le_rfl

/-- `OPrime p G` is normal. -/
instance OPrime_normal (p : ℕ) (G : Type*) [Group G] : (OPrime p G).Normal := by
  unfold OPrime
  exact Subgroup.normal_iInf_normal (fun N => N.property.1)

/-- Per-element Normal instance for the `OPrime` indexing subtype. Needed so that
`G ⧸ N.val` (over `N` in the subtype) has a group structure during type elaboration. -/
instance OPrime_index_subtype_normal {p : ℕ} {G : Type*} [Group G]
    (N : {N : Subgroup G // N.Normal ∧ ∃ k : ℕ, N.index = p ^ k}) :
    (N.val : Subgroup G).Normal := N.property.1

/-- For finite `G`, `OPrime p G` has `p`-power index.

**証明**: `OPrime = ⨅ N : ι, N.val` over the finite indexing set `ι` of normal subgroups
with p-power index. Build the diagonal `MonoidHom G →* ∏ N : ι, G/N.val` (via
`MonoidHom.pi`); its kernel is exactly `⨅ N : ι, N.val = OPrime p G` (since `g ∈ ker`
iff `g ∈ N` for every member of the family). By the first iso theorem,
`G/OPrime ≃* range`, with range a subgroup of `∏ G/N.val`. Lagrange gives
`|range| ∣ |∏ G/N.val| = ∏ N.val.index`. Each `N.val.index = p^{k_N}` so the product
is `p^{∑ k_N}`. By `Nat.dvd_prime_pow`, `(OPrime).index = p^?`. -/
lemma OPrime_index_isPGroup (p : ℕ) (G : Type*) [Group G] [Finite G] [Fact p.Prime] :
    ∃ k : ℕ, (OPrime p G).index = p ^ k := by
  classical
  let ι : Type _ := {N : Subgroup G // N.Normal ∧ ∃ k : ℕ, N.index = p ^ k}
  haveI : Finite ι := Subtype.finite
  haveI : Fintype ι := Fintype.ofFinite ι
  -- Diagonal hom φ : G →* ∀ i : ι, G ⧸ i.val (instance found via OPrime_index_subtype_normal)
  let φ : G →* (∀ i : ι, G ⧸ (i.val : Subgroup G)) :=
    MonoidHom.pi fun i : ι => QuotientGroup.mk' i.val
  -- ker φ = OPrime p G
  have h_ker : φ.ker = OPrime p G := by
    ext g
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [OPrime, Subgroup.mem_iInf]
      intro i
      have hg_i : φ g i = (1 : G ⧸ (i.val : Subgroup G)) := by
        rw [MonoidHom.mem_ker] at h; exact congrFun h i
      simpa [φ, MonoidHom.pi_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] using hg_i
    · rw [MonoidHom.mem_ker]
      ext i
      simp only [φ, MonoidHom.pi_apply, QuotientGroup.mk'_apply, Pi.one_apply,
        QuotientGroup.eq_one_iff]
      rw [OPrime, Subgroup.mem_iInf] at h
      exact h i
  -- Lagrange: |range φ| ∣ |∀ i, G/i.val|
  haveI : Finite (∀ i : ι, G ⧸ (i.val : Subgroup G)) := Pi.finite
  have h_card_range : Nat.card φ.range ∣ Nat.card (∀ i : ι, G ⧸ (i.val : Subgroup G)) :=
    Subgroup.card_subgroup_dvd_card _
  -- |G/OPrime| = |range φ| via first iso
  have h_card_quot : Nat.card (G ⧸ OPrime p G) = Nat.card φ.range := by
    rw [← h_ker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  -- |∀ i, G/i.val| = ∏ (i.val.index)
  have h_card_pi : Nat.card (∀ i : ι, G ⧸ (i.val : Subgroup G)) = ∏ i : ι, i.val.index := by
    rw [Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Subgroup.index_eq_card]
  -- ∏ i.val.index = p ^ (∑ k_i)
  let k_fun : ι → ℕ := fun i => Classical.choose i.property.2
  have hk_fun : ∀ i : ι, i.val.index = p ^ k_fun i := fun i => Classical.choose_spec i.property.2
  have h_prod_pow : (∏ i : ι, i.val.index) = p ^ (∑ i : ι, k_fun i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => hk_fun i
  -- Combine: (OPrime).index ∣ p^∑
  have h_idx_dvd : (OPrime p G).index ∣ p ^ (∑ i : ι, k_fun i) := by
    rw [Subgroup.index_eq_card, h_card_quot]
    calc Nat.card φ.range
        ∣ Nat.card (∀ i : ι, G ⧸ (i.val : Subgroup G)) := h_card_range
      _ = ∏ i : ι, i.val.index := h_card_pi
      _ = p ^ (∑ i : ι, k_fun i) := h_prod_pow
  obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Fact.out).mp h_idx_dvd
  exact ⟨a, ha⟩

/-- `APrime p G` — the smallest normal subgroup `K ⊴ G` with `G/K` abelian and p-power index.
Equivalently, the smallest member of the family `{K ⊴ G : commutator G ≤ K ∧ [G:K] is p-power}`.

For finite `G`, this corresponds to Isaacs' `A^p(G)`. mathlib 未収載のため新規定義. -/
def APrime (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ K : {K : Subgroup G // K.Normal ∧ commutator G ≤ K ∧ ∃ k : ℕ, K.index = p ^ k}, K.val

/-- Per-element Normal instance for the `APrime` indexing subtype. -/
instance APrime_index_subtype_normal {p : ℕ} {G : Type*} [Group G]
    (K : {K : Subgroup G // K.Normal ∧ commutator G ≤ K ∧ ∃ k : ℕ, K.index = p ^ k}) :
    (K.val : Subgroup G).Normal := K.property.1

/-- `APrime p G` ≤ any normal subgroup containing `commutator G` with p-power index. -/
lemma APrime_le {p : ℕ} {G : Type*} [Group G] {K : Subgroup G}
    (hN : K.Normal) (hC : commutator G ≤ K) {k : ℕ} (hi : K.index = p ^ k) :
    APrime p G ≤ K :=
  iInf_le_of_le ⟨K, hN, hC, k, hi⟩ le_rfl

/-- `APrime p G` is normal. -/
instance APrime_normal (p : ℕ) (G : Type*) [Group G] : (APrime p G).Normal := by
  unfold APrime
  exact Subgroup.normal_iInf_normal (fun K => K.property.1)

/-- `commutator G ≤ APrime p G` (the commutator is contained in every family member). -/
lemma commutator_le_APrime (p : ℕ) (G : Type*) [Group G] : commutator G ≤ APrime p G := by
  intro x hx
  unfold APrime
  rw [Subgroup.mem_iInf]
  intro K
  exact K.property.2.1 hx

/-- For finite `G`, `APrime p G` has `p`-power index (same proof as `OPrime_index_isPGroup`,
since the family is closed under `⊓` and each member has `p`-power index). -/
lemma APrime_index_isPGroup (p : ℕ) (G : Type*) [Group G] [Finite G] [Fact p.Prime] :
    ∃ k : ℕ, (APrime p G).index = p ^ k := by
  classical
  let ι : Type _ :=
    {K : Subgroup G // K.Normal ∧ commutator G ≤ K ∧ ∃ k : ℕ, K.index = p ^ k}
  haveI : Finite ι := Subtype.finite
  haveI : Fintype ι := Fintype.ofFinite ι
  let φ : G →* (∀ i : ι, G ⧸ (i.val : Subgroup G)) :=
    MonoidHom.pi fun i : ι => QuotientGroup.mk' i.val
  have h_ker : φ.ker = APrime p G := by
    ext g
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [APrime, Subgroup.mem_iInf]
      intro i
      have hg_i : φ g i = (1 : G ⧸ (i.val : Subgroup G)) := by
        rw [MonoidHom.mem_ker] at h; exact congrFun h i
      simpa [φ, MonoidHom.pi_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] using hg_i
    · rw [MonoidHom.mem_ker]
      ext i
      simp only [φ, MonoidHom.pi_apply, QuotientGroup.mk'_apply, Pi.one_apply,
        QuotientGroup.eq_one_iff]
      rw [APrime, Subgroup.mem_iInf] at h
      exact h i
  haveI : Finite (∀ i : ι, G ⧸ (i.val : Subgroup G)) := Pi.finite
  have h_card_range : Nat.card φ.range ∣ Nat.card (∀ i : ι, G ⧸ (i.val : Subgroup G)) :=
    Subgroup.card_subgroup_dvd_card _
  have h_card_quot : Nat.card (G ⧸ APrime p G) = Nat.card φ.range := by
    rw [← h_ker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have h_card_pi : Nat.card (∀ i : ι, G ⧸ (i.val : Subgroup G)) = ∏ i : ι, i.val.index := by
    rw [Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Subgroup.index_eq_card]
  let k_fun : ι → ℕ := fun i => Classical.choose i.property.2.2
  have hk_fun : ∀ i : ι, i.val.index = p ^ k_fun i :=
    fun i => Classical.choose_spec i.property.2.2
  have h_prod_pow : (∏ i : ι, i.val.index) = p ^ (∑ i : ι, k_fun i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => hk_fun i
  have h_idx_dvd : (APrime p G).index ∣ p ^ (∑ i : ι, k_fun i) := by
    rw [Subgroup.index_eq_card, h_card_quot]
    calc Nat.card φ.range
        ∣ Nat.card (∀ i : ι, G ⧸ (i.val : Subgroup G)) := h_card_range
      _ = ∏ i : ι, i.val.index := h_card_pi
      _ = p ^ (∑ i : ι, k_fun i) := h_prod_pow
  obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Fact.out).mp h_idx_dvd
  exact ⟨a, ha⟩

/-- For finite groups, `A^p(G)` is characteristic.

This is the automorphism-invariance of Isaacs' defining family: normal subgroups containing
`G'` with p-power index are preserved by every automorphism. -/
lemma APrime_characteristic (p : ℕ) (G : Type*) [Group G] [Finite G] [Fact p.Prime] :
    (APrime p G).Characteristic := by
  classical
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ
  let K : Subgroup G := (APrime p G).comap φ.toMonoidHom
  have hK_normal : K.Normal := inferInstance
  have hK_comm : commutator G ≤ K := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxmap : φ x ∈ (commutator G).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom hx
    have hmap_comm : (commutator G).map φ.toMonoidHom = commutator G := by
      rw [_root_.map_commutator_eq,
        φ.toMonoidHom.range_eq_top_of_surjective φ.surjective,
        ← _root_.commutator_def]
    exact commutator_le_APrime p G (hmap_comm ▸ hxmap)
  obtain ⟨k, hk⟩ := APrime_index_isPGroup p G
  have hK_index : K.index = p ^ k := by
    rw [Subgroup.index_comap_of_surjective (H := APrime p G)
      (f := φ.toMonoidHom) φ.surjective, hk]
  exact APrime_le (K := K) hK_normal hK_comm hK_index

/-- The transfer-focal kernel contains `A^p(G)`.

This is the `A^p` half of Isaacs Thm 5.21 in the mathlib formulation: the quotient
`G / ker(V)` is isomorphic to the p-group `P / P*`, and `ker(V)` contains `G'`. -/
lemma APrime_le_transferFocal_ker [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : APrime p G ≤ P.transferFocal.ker := by
  classical
  have hquot : IsPGroup p (G ⧸ P.transferFocal.ker) :=
    (P.2.to_quotient P.focalSubgroupOf).of_equiv
      (Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf P).symm
  obtain ⟨k, hk⟩ := hquot.exists_card_eq
  have hker_index : P.transferFocal.ker.index = p ^ k := by
    rw [Subgroup.index_eq_card]
    exact hk
  exact APrime_le (K := P.transferFocal.ker) inferInstance
    (Abelianization.commutator_subset_ker P.transferFocal) hker_index

/-- **Isaacs Thm 5.20/5.21 bridge**: for a Sylow `p`-subgroup `P`,
`A^p(G) ∩ P` is the focal subgroup of `P`.

The forward inclusion uses `A^p(G) ≤ ker(transferFocal)`, and the reverse inclusion is
the focal subgroup theorem `G' ∩ P = Foc_G(P)` together with `G' ≤ A^p(G)`. -/
lemma APrime_inf_sylow_eq_focalSubgroup [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    APrime p G ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup := by
  apply le_antisymm
  · calc
      APrime p G ⊓ (P : Subgroup G) ≤ P.transferFocal.ker ⊓ (P : Subgroup G) :=
        inf_le_inf (APrime_le_transferFocal_ker P) le_rfl
      _ = (P : Subgroup G).focalSubgroup :=
        Subgroup.ker_transferFocal_inf_eq_focalSubgroup P
  · rw [← Subgroup.commutator_inf_eq_focalSubgroup P]
    exact inf_le_inf (commutator_le_APrime p G) le_rfl

/-- **Isaacs Thm 5.21 (Focal Subgroup Theorem)**:
for a Sylow `p`-subgroup `P`, the focal subgroup is the common intersection of
`P` with the commutator subgroup, with `A^p(G)`, and with the focal-transfer kernel.

This is the downstream-facing Ch.5 entrypoint for BG Thm 1.17. It packages mathlib's
`Subgroup.commutator_inf_eq_focalSubgroup` and
`Subgroup.ker_transferFocal_inf_eq_focalSubgroup` together with this file's
`A^p(G)` bridge. -/
theorem focalSubgroupTheorem [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    _root_.commutator G ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup ∧
      APrime p G ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup ∧
      P.transferFocal.ker ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup := by
  exact ⟨Subgroup.commutator_inf_eq_focalSubgroup P,
    APrime_inf_sylow_eq_focalSubgroup P,
    Subgroup.ker_transferFocal_inf_eq_focalSubgroup P⟩

/-- **Isaacs Thm 5.20**: the focal transfer kernel is `A^p(G)`.

This upgrades `A^p(G) ≤ ker(transferFocal)` to equality by comparing indices via a
Sylow `p`-subgroup: both normal subgroups have p-power index, both join with `P` to
give `G`, and both have the same intersection with `P`, namely the focal subgroup. -/
theorem APrime_eq_transferFocal_ker [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    APrime p G = P.transferFocal.ker := by
  classical
  let A : Subgroup G := APrime p G
  let K : Subgroup G := P.transferFocal.ker
  haveI : A.Normal := by
    dsimp [A]
    infer_instance
  haveI : K.Normal := by
    dsimp [K]
    infer_instance
  have hA_le_K : A ≤ K := by
    simpa [A, K] using APrime_le_transferFocal_ker (G := G) (p := p) P
  have hA_inf_P : A ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup := by
    simpa [A] using APrime_inf_sylow_eq_focalSubgroup (G := G) (p := p) P
  have hK_inf_P : K ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup := by
    simpa [K] using Subgroup.ker_transferFocal_inf_eq_focalSubgroup P
  have hA_index_pow : ∃ k : ℕ, A.index = p ^ k := by
    simpa [A] using APrime_index_isPGroup p G
  have hK_index_pow : ∃ k : ℕ, K.index = p ^ k := by
    have hquot : IsPGroup p (G ⧸ P.transferFocal.ker) :=
      (P.2.to_quotient P.focalSubgroupOf).of_equiv
        (Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf P).symm
    obtain ⟨k, hk⟩ := hquot.exists_card_eq
    refine ⟨k, ?_⟩
    change P.transferFocal.ker.index = p ^ k
    rw [Subgroup.index_eq_card]
    exact hk
  have hPA_top : (P : Subgroup G) ⊔ A = ⊤ := by
    obtain ⟨k, hk⟩ := hA_index_pow
    have hcop : Nat.Coprime (P : Subgroup G).index A.index := by
      rw [hk]
      exact Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out P.not_dvd_index
    exact OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hcop
  have hPK_top : (P : Subgroup G) ⊔ K = ⊤ := by
    obtain ⟨k, hk⟩ := hK_index_pow
    have hcop : Nat.Coprime (P : Subgroup G).index K.index := by
      rw [hk]
      exact Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out P.not_dvd_index
    exact OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hcop
  have h_index_eq : A.index = K.index := by
    calc
      A.index = A.relIndex (P : Subgroup G) := by
        rw [← Subgroup.relIndex_sup_right (H := (P : Subgroup G)) (K := A),
          hPA_top, Subgroup.relIndex_top_right]
      _ = (A ⊓ (P : Subgroup G)).relIndex (P : Subgroup G) := by
        rw [Subgroup.inf_relIndex_right]
      _ = (K ⊓ (P : Subgroup G)).relIndex (P : Subgroup G) := by
        rw [hA_inf_P, hK_inf_P]
      _ = K.relIndex (P : Subgroup G) := by
        rw [Subgroup.inf_relIndex_right]
      _ = K.index := by
        rw [← Subgroup.relIndex_sup_right (H := (P : Subgroup G)) (K := K),
          hPK_top, Subgroup.relIndex_top_right]
  have hrel_eq_one : A.relIndex K = 1 := by
    have hmul : A.relIndex K * K.index = 1 * K.index := by
      rw [Subgroup.relIndex_mul_index hA_le_K, one_mul, h_index_eq]
    exact Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hmul
  exact le_antisymm hA_le_K (Subgroup.relIndex_eq_one.mp hrel_eq_one)

/-- The always-available half of Isaacs Cor. 5.22:
if a subgroup `H` contains a Sylow `p`-subgroup of `G`, then
`A^p(H) ≤ H ∩ A^p(G)`.

The proof follows Isaacs' paragraph before Cor. 5.22: since `P · A^p(G)=G`, also
`H · A^p(G)=G`, so `H/(H ∩ A^p(G))` is an abelian p-group. -/
lemma APrime_le_subgroupOf_APrime_of_sylow_le [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {H : Subgroup G} (hP_le_H : (P : Subgroup G) ≤ H) :
    APrime p H ≤ (APrime p G).subgroupOf H := by
  classical
  let A : Subgroup G := APrime p G
  haveI hA_normal : A.Normal := inferInstance
  have hA_index_pow : ∃ k : ℕ, A.index = p ^ k := by
    simpa [A] using APrime_index_isPGroup p G
  have hPA_top : (P : Subgroup G) ⊔ A = ⊤ := by
    obtain ⟨k, hk⟩ := hA_index_pow
    have hcop : Nat.Coprime (P : Subgroup G).index A.index := by
      rw [hk]
      exact Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out P.not_dvd_index
    exact OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hcop
  have hHA_top : H ⊔ A = ⊤ := by
    rw [eq_top_iff, ← hPA_top]
    exact sup_le_sup hP_le_H le_rfl
  have hA_sub_H_index : ∃ k : ℕ, (A.subgroupOf H).index = p ^ k := by
    obtain ⟨k, hk⟩ := hA_index_pow
    refine ⟨k, ?_⟩
    change A.relIndex H = p ^ k
    rw [← Subgroup.relIndex_sup_right (H := H) (K := A), hHA_top,
      Subgroup.relIndex_top_right, hk]
  have hA_sub_H_normal : (A.subgroupOf H).Normal := hA_normal.subgroupOf H
  have hcommH_le : commutator H ≤ A.subgroupOf H := by
    intro x hx
    change (x : G) ∈ A
    have hxmap : (x : G) ∈ (commutator H).map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype hx
    have hmap_le : (commutator H).map H.subtype ≤ commutator G := by
      rw [Subgroup.map_subtype_commutator, _root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact commutator_le_APrime p G (hmap_le hxmap)
  obtain ⟨k, hk⟩ := hA_sub_H_index
  exact APrime_le (K := A.subgroupOf H) hA_sub_H_normal hcommH_le hk

/-- **Isaacs Cor. 5.22 (`A^p` equality form)**:
if `P ≤ H ≤ G` and `H` controls `G`-fusion in `P`, then
`A^p(H) = H ∩ A^p(G)`.

This is the transfer-control conclusion, stated without adding a separate
`ControlsPTransfer` predicate. -/
theorem APrime_eq_subgroupOf_APrime_of_controlsFusionIn [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {H : Subgroup G}
    (hP_le_H : (P : Subgroup G) ≤ H)
    (hFusion : H.ControlsFusionIn (P : Subgroup G)) :
    APrime p H = (APrime p G).subgroupOf H := by
  classical
  let A : Subgroup G := APrime p G
  let B : Subgroup H := APrime p H
  let PH_sub : Subgroup H := (P : Subgroup G).subgroupOf H
  have hB_le_AH : B ≤ A.subgroupOf H := by
    simpa [A, B] using APrime_le_subgroupOf_APrime_of_sylow_le (G := G) (p := p) P hP_le_H
  have hPH_pgroup : IsPGroup p PH_sub :=
    P.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_H).symm
  have hPH_not_dvd : ¬ p ∣ PH_sub.index := by
    intro hdiv
    exact P.not_dvd_index (hdiv.trans (Subgroup.relIndex_dvd_index_of_le hP_le_H))
  let PH : Sylow p H := hPH_pgroup.toSylow hPH_not_dvd
  have hPH_eq : (PH : Subgroup H) = PH_sub :=
    hPH_pgroup.toSylow_coe hPH_not_dvd
  have hB_inf_PH : B ⊓ PH_sub = PH_sub.focalSubgroup := by
    have h := APrime_inf_sylow_eq_focalSubgroup (G := H) (p := p) PH
    simpa [B, hPH_eq] using h
  have hAH_inf_PH : A.subgroupOf H ⊓ PH_sub = PH_sub.focalSubgroup := by
    apply (Subgroup.map_subtype_inj (H := H)).mp
    rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective,
      Subgroup.subgroupOf_map_subtype,
      Subgroup.map_subgroupOf_eq_of_le hP_le_H,
      Subgroup.focalSubgroup_subgroupOf_map_eq_of_controlsFusionIn hP_le_H hFusion,
      ← APrime_inf_sylow_eq_focalSubgroup (G := G) (p := p) P]
    rw [inf_assoc, inf_comm H (P : Subgroup G), inf_eq_left.mpr hP_le_H]
  have hB_sup_PH : B ⊔ PH_sub = ⊤ := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, B.index = p ^ k := by
      simpa [B] using APrime_index_isPGroup p H
    have hcop : Nat.Coprime B.index PH_sub.index := by
      rw [hk]
      exact (Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out hPH_not_dvd).symm
    exact OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hcop
  have hAH_index_pow : ∃ k : ℕ, (A.subgroupOf H).index = p ^ k := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, A.index = p ^ k := by
      simpa [A] using APrime_index_isPGroup p G
    have hPA_top : (P : Subgroup G) ⊔ A = ⊤ := by
      have hcop : Nat.Coprime (P : Subgroup G).index A.index := by
        rw [hk]
        exact Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out P.not_dvd_index
      exact OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hcop
    have hHA_top : H ⊔ A = ⊤ := by
      rw [eq_top_iff, ← hPA_top]
      exact sup_le_sup hP_le_H le_rfl
    refine ⟨k, ?_⟩
    change A.relIndex H = p ^ k
    rw [← Subgroup.relIndex_sup_right (H := H) (K := A), hHA_top,
      Subgroup.relIndex_top_right, hk]
  have hAH_sup_PH : A.subgroupOf H ⊔ PH_sub = ⊤ := by
    obtain ⟨k, hk⟩ := hAH_index_pow
    have hcop : Nat.Coprime (A.subgroupOf H).index PH_sub.index := by
      rw [hk]
      exact (Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out hPH_not_dvd).symm
    exact OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hcop
  have h_index_eq : B.index = (A.subgroupOf H).index := by
    calc
      B.index = B.relIndex PH_sub := by
        rw [← Subgroup.relIndex_sup_right (H := PH_sub) (K := B), sup_comm,
          hB_sup_PH, Subgroup.relIndex_top_right]
      _ = (B ⊓ PH_sub).relIndex PH_sub := by
        rw [Subgroup.inf_relIndex_right]
      _ = (A.subgroupOf H ⊓ PH_sub).relIndex PH_sub := by
        rw [hB_inf_PH, hAH_inf_PH]
      _ = (A.subgroupOf H).relIndex PH_sub := by
        rw [Subgroup.inf_relIndex_right]
      _ = (A.subgroupOf H).index := by
        rw [← Subgroup.relIndex_sup_right (H := PH_sub) (K := A.subgroupOf H),
          sup_comm, hAH_sup_PH, Subgroup.relIndex_top_right]
  have hrel_eq_one : B.relIndex (A.subgroupOf H) = 1 := by
    have hmul : B.relIndex (A.subgroupOf H) * (A.subgroupOf H).index =
        1 * (A.subgroupOf H).index := by
      rw [Subgroup.relIndex_mul_index hB_le_AH, one_mul, h_index_eq]
    exact Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hmul
  exact le_antisymm hB_le_AH (Subgroup.relIndex_eq_one.mp hrel_eq_one)

/-- **Isaacs Cor. 5.23 (`A^p` equality form)**:
if the Sylow `p`-subgroup `P` is abelian, then `N_G(P)` controls `p`-transfer,
expressed as `A^p(N_G(P)) = N_G(P) ∩ A^p(G)`.

This is Cor. 5.22 applied to Lemma 5.12, since an abelian `P` is contained in
its own centralizer. -/
theorem APrime_normalizer_eq_subgroupOf_APrime_of_isMulCommutative_sylow
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [IsMulCommutative ↥(P : Subgroup G)] :
    APrime p (Subgroup.normalizer (P : Set G)) =
      (APrime p G).subgroupOf (Subgroup.normalizer (P : Set G)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  have hP_le_N : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hFusion : N.ControlsFusionIn (P : Subgroup G) := by
    intro x y hxP hyP hxy
    obtain ⟨g, hgxy⟩ := hxy
    have hxC : x ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (congrArg Subtype.val
        (mul_comm (⟨x, hxP⟩ : ↥(P : Subgroup G)) (⟨q, hq⟩ : ↥(P : Subgroup G)))).symm
    have hyC : y ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (congrArg Subtype.val
        (mul_comm (⟨y, hyP⟩ : ↥(P : Subgroup G)) (⟨q, hq⟩ : ↥(P : Subgroup G)))).symm
    exact normalizer_controls_centralizer_fusion P hxC hyC hgxy
  simpa [N] using
    APrime_eq_subgroupOf_APrime_of_controlsFusionIn (G := G) (p := p) P hP_le_N hFusion

end -- 5D

section /- 5E: Frobenius normal p-complement (pp. 173-180) -/

/-! ### Isaacs §5E (Frobenius normal p-complement)

**FT クリティカル**. mathlib 未収載で新規実装が必要.

- **Def** `HasNormalPComplement p G` — 「G は normal p-complement を持つ」(§5C で導入済み).
- **Thm 5.25** (Sylow controls own fusion ⇔ normal p-comp): ✅ 完成.
  `controlsOwnFusion_of_hasNormalPComplement` + `hasNormalPComplement_of_controlsOwnFusion`.
- **Thm 5.26 Frobenius** (3 同値条件): ✅ 完成 (Lem 5.27 + Lem 5.28 + 5.25 経由).
- **Lem 5.27** (1 ⇒ 2 ⇒ 3 易方向): ✅ 完成. Part 1 (`hasNormalPComplement_of_subgroup`) +
  Part 2 (`isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement`).
- **Lem 5.28** (3 ⇒ Sylow 共役 via C_G(P ⊓ Q)): ✅ 完成 (sorry-free).
  helper `sylow_sup_normal_eq_top_of_quot_isPGroup` + `lt_normalizer_of_pgroup_of_lt_top`.
  main body Steps 1-11 全実装: P ⊓ N > D, Sylow S/T/R 設定, N=SC 分解,
  Sylow II in ↥N, T = yC • S, conjugation translation to G, index strict ineq,
  二回 IH chain (P, R) と (yR, Q), 結合 c = x · yC⁻¹ · z.
- **Cor 5.29** (q ∤ p^e-1 ⇒ normal p-comp): ✅ 完成 (5.26 + p-group action).
- **Cor 5.30** (p odd, 全 order-p 中心 ⇒ normal p-comp): ✅ 完成 (Ch.4 §4D Thm 4.36). -/

/-- If `A^p(G)=G`, then a Sylow p-subgroup is equal to its focal subgroup.

This packages only the standard `A^p` consequence of the focal subgroup theorem, avoiding a
separate public bridge through `G'`. -/
lemma sylow_focalSubgroup_eq_self_of_APrime_eq_top [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hA : APrime p G = ⊤) :
    P.focalSubgroup = (P : Subgroup G) := by
  have hker_top : P.transferFocal.ker = ⊤ := by
    apply eq_top_iff.mpr
    simpa [hA] using APrime_le_transferFocal_ker (G := G) (p := p) P
  rw [← Subgroup.ker_transferFocal_inf_eq_focalSubgroup P, hker_top, top_inf_eq]

/-- **Isaacs Thm 5.25 proof step**: if `N = O^p(G)`, then `A^p(N)=N`.

Isaacs p.173 uses that `A^p(N)` is characteristic in `N`, hence normal in `G`, and that
`|G:A^p(N)| = |G:N| · |N:A^p(N)|` is a p-power. Minimality of `O^p(G)` then gives
`N ≤ A^p(N).map subtype ≤ N`, so `A^p(N)=N` internally. -/
lemma APrime_eq_top_of_eq_OPrime [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : N = OPrime p G) :
    APrime p N = ⊤ := by
  classical
  let A : Subgroup N := APrime p N
  haveI hA_char : A.Characteristic := by
    simpa [A] using APrime_characteristic (p := p) (G := N)
  haveI hAmap_normal : (A.map N.subtype).Normal := inferInstance
  have hAmap_le_N : A.map N.subtype ≤ N :=
    Subgroup.map_subtype_le A
  obtain ⟨a, hN_index⟩ : ∃ a : ℕ, N.index = p ^ a := by
    rw [hN]
    exact OPrime_index_isPGroup p G
  obtain ⟨b, hA_index⟩ : ∃ b : ℕ, A.index = p ^ b := by
    simpa [A] using APrime_index_isPGroup p N
  have hAmap_index : (A.map N.subtype).index = p ^ (b + a) := by
    rw [Subgroup.index_map_subtype, hA_index, hN_index, ← pow_add]
  have hN_le_Amap : N ≤ A.map N.subtype := by
    have hO_le_Amap : OPrime p G ≤ A.map N.subtype :=
      OPrime_le hAmap_normal hAmap_index
    exact hN.symm ▸ hO_le_Amap
  have hAmap_eq_N : A.map N.subtype = N :=
    le_antisymm hAmap_le_N hN_le_Amap
  have hA_eq_top : A = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := N)).mp
    rw [hAmap_eq_N, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa [A] using hA_eq_top

/-- "Sylow `p`-subgroup `P` controls its own G-fusion": for any two elements `x, y ∈ P`
that are conjugate in `G`, they are already conjugate by some element of `P`.

Isaacs §5C-§5E で頻出. mathlib 未収載のため新規定義. -/
def _root_.Sylow.ControlsOwnFusion {p : ℕ} {G : Type*} [Group G] (P : Sylow p G) : Prop :=
  (P : Subgroup G).ControlsFusionIn (P : Subgroup G)

/-- **Isaacs Thm 5.25 (⇒)**: G has normal p-complement ⇒ any Sylow_p `P` controls own fusion.

**証明** (Isaacs p.173): 与えられた N normal p-comp で `G = N · P`, `N ⊓ P = ⊥`.
x, y ∈ P G-conjugate: ∃ g, g x g⁻¹ = y. `mem_sup_of_normal_left` で `g = n · p`
(n ∈ N, p ∈ P). z := p x p⁻¹ ∈ P. `g x g⁻¹ = n z n⁻¹ = y ∈ P`. 一方
`n z n⁻¹ · z⁻¹ = n · (z n⁻¹ z⁻¹) ∈ N` (N normal) かつ `∈ P` (= y · z⁻¹). よって
`∈ N ⊓ P = ⊥`, つまり `n z n⁻¹ = z = p x p⁻¹ = y`. `u = p` で完了. -/
theorem controlsOwnFusion_of_hasNormalPComplement [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hG : HasNormalPComplement p G) :
    P.ControlsOwnFusion := by
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  haveI : N.Normal := hN_normal
  rintro x y hx_P hy_P ⟨g, hgxy⟩
  -- g ∈ N ⊔ P = ⊤ ⇒ g = n · p (n ∈ N, p ∈ P)
  have h_sup_top : N ⊔ (P : Subgroup G) = ⊤ := (hN_compl P).sup_eq_top
  have hg_in_sup : g ∈ N ⊔ (P : Subgroup G) := h_sup_top ▸ Subgroup.mem_top g
  obtain ⟨n, hn_N, q, hq_P, hg_eq⟩ := Subgroup.mem_sup_of_normal_left.mp hg_in_sup
  -- z := q * x * q⁻¹ ∈ P
  have hz_P : q * x * q⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hq_P hx_P)
      ((P : Subgroup G).inv_mem hq_P)
  -- y = g x g⁻¹ = n · (q x q⁻¹) · n⁻¹ = n z n⁻¹
  have h_y_eq : y = n * (q * x * q⁻¹) * n⁻¹ := by
    rw [← hgxy, ← hg_eq]; group
  -- n z n⁻¹ ∈ P (= y)
  have h_nzn_in_P : n * (q * x * q⁻¹) * n⁻¹ ∈ (P : Subgroup G) := h_y_eq ▸ hy_P
  -- n z n⁻¹ · z⁻¹ ∈ N: rewrite as n · (z n⁻¹ z⁻¹) with z n⁻¹ z⁻¹ ∈ N (conj)
  have h_in_N : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ N := by
    have hzn_inv_z_inv_N : (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ N :=
      hN_normal.conj_mem n⁻¹ (N.inv_mem hn_N) (q * x * q⁻¹)
    have heq : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ =
               n * ((q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹) := by group
    rw [heq]
    exact N.mul_mem hn_N hzn_inv_z_inv_N
  -- n z n⁻¹ · z⁻¹ ∈ P
  have h_in_P : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem h_nzn_in_P ((P : Subgroup G).inv_mem hz_P)
  -- n z n⁻¹ · z⁻¹ ∈ N ⊓ P = ⊥, so equal to 1
  have h_eq_one : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ = 1 := by
    have h_in_inf : n * (q * x * q⁻¹) * n⁻¹ * (q * x * q⁻¹)⁻¹ ∈ N ⊓ (P : Subgroup G) :=
      ⟨h_in_N, h_in_P⟩
    rw [(hN_compl P).disjoint.eq_bot, Subgroup.mem_bot] at h_in_inf
    exact h_in_inf
  -- n z n⁻¹ = z, so y = z = q x q⁻¹
  rw [mul_inv_eq_one] at h_eq_one
  refine ⟨q, hq_P, ?_⟩
  rw [h_y_eq, h_eq_one]

/-- **Helper for Thm 5.25 (⇐)**: heart of the proof. Sylow_p `P` that controls its own G-fusion
satisfies `P ⊓ OPrime p G = ⊥`. The rest of Thm 5.25 (⇐) is a Sylow-conjugacy + cardinality
assembly on top of this.

**証明スケッチ** (Isaacs p.173):
* `N := OPrime p G`. `Q := (P ⊓ N).subgroupOf N` is Sylow `p` of `↥N` (cardinality argument:
  `|P ⊓ N| = |P| / [G : N · P]` and `N · P = G` from `[G:N]` being p-power dividing `|P|`).
* **APrime p ↥N = ⊤**: `APrime p ↥N` is characteristic in `↥N` (Aut(N) preserves the
  defining family) ⇒ its `.map N.subtype` is normal in `G`. It has p-power index in `G`
  (= `|G:N| · |↥N : APrime|`), so by `OPrime` minimality `N ≤ (APrime).map subtype ≤ N`,
  hence equality, hence `APrime p ↥N = ⊤` in `↥N`.
* **Focal Subgroup Theorem**: `APrime p ↥N = ⊤` and transfer-focal give
  `focalSubgroup Q = Q`. This is the `A^p(N)=N` line in Isaacs followed by Thm 5.21,
  without adding an extra public bridge through `commutator ↥N`.
* **ControlsOwnFusion lift**: every generator `⁅x, u⁆ ∈ focalSubgroup Q` (with `x ∈ Q`,
  `u ∈ ↥N` such that `[x,u] ∈ Q`) can be rewritten using ControlsOwnFusion. Set
  `y := u x u⁻¹ ∈ Q ⊆ P`; controlsOwnFusion gives `v ∈ P` with `v x v⁻¹ = y`. Then
  `[x, v⁻¹] = x⁻¹ y` is in `⁅Q.map N.subtype, (P : Subgroup G)⁆`. Hence
  `focalSubgroup Q ≤ ⁅Q.map subtype, P⁆` (viewing all in `G`).
* **Iteration**: Combine the previous two: `Q.map subtype ≤ ⁅Q.map subtype, P⁆` in `G`. By
  induction on `n`, `Q.map subtype ≤ lowerCentralSeries (P : Subgroup G) n`.
  (Base: `Q.map subtype ≤ P` since `Q ⊆ P`. Step: `Q.map subtype ≤ ⁅Q.map subtype, P⁆ ≤
  ⁅lowerCentralSeries P n, ⊤⁆ = lowerCentralSeries P (n+1)`.)
* **Termination**: `P` is a finite p-group ⇒ `IsNilpotent P` (`IsPGroup.isNilpotent`) ⇒
  `∃ n, lowerCentralSeries P n = ⊥` (`Subgroup.nilpotent_iff_lowerCentralSeries`). Hence
  `Q.map subtype = ⊥` in `G`, so `(P : Subgroup G) ⊓ N = ⊥`.

The proof below implements these steps directly. -/
lemma OPrime_meet_sylow_eq_bot_of_controlsOwnFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : P.ControlsOwnFusion) :
    (P : Subgroup G) ⊓ OPrime p G = ⊥ := by
  set N : Subgroup G := OPrime p G with hN_def
  haveI hN_normal : N.Normal := inferInstance
  set R : Subgroup G := (P : Subgroup G) ⊓ N with hR_def
  have hR_le_P : R ≤ (P : Subgroup G) := by
    rw [hR_def]
    exact inf_le_left
  -- Controls-own-fusion converts focal generators of `R` into commutators with `P`.
  have h_focal_R_le_comm : R.focalSubgroup ≤ ⁅R, (P : Subgroup G)⁆ := by
    rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgR, x, hxR, u, rfl⟩
    have hyR : u * x * u⁻¹ ∈ R := by
      have hy_eq : u * x * u⁻¹ = (⁅x, u⁆)⁻¹ * x := by
        rw [commutatorElement_def]
        group
      rw [hy_eq]
      exact R.mul_mem (R.inv_mem hgR) hxR
    obtain ⟨v, hvP, hv⟩ := hP (hR_le_P hxR) (hR_le_P hyR) ⟨u, rfl⟩
    have hcomm_eq : ⁅x, u⁆ = ⁅x, v⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc
        x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
        _ = x * (v * x * v⁻¹)⁻¹ := by rw [hv]
        _ = x * v * x⁻¹ * v⁻¹ := by group
    rw [hcomm_eq]
    exact Subgroup.commutator_mem_commutator hxR hvP
  -- **Crux**: `R ≤ ⁅R, (P : Subgroup G)⁆`.
  -- 内訳: APrime ↥N = ⊤ (char + OPrime minimality) → transfer-focal で
  -- focalSubgroup Q = Q → 各 focal generator ⁅x, u⁆ (x ∈ Q, u ∈ ↥N) を
  -- ControlsOwnFusion で ⁅Q.map subtype, P⁆ 内 commutator に変換.
  have h_R_le_comm : R ≤ ⁅R, (P : Subgroup G)⁆ := by
    have h_R_le_focal : R ≤ R.focalSubgroup := by
      have hR_le_N : R ≤ N := by
        rw [hR_def]
        exact inf_le_right
      have hR_pgroup : IsPGroup p R :=
        P.isPGroup'.to_le hR_le_P
      have hRN_pgroup : IsPGroup p (R.subgroupOf N) :=
        hR_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hR_le_N).symm
      have hRN_not_dvd : ¬ p ∣ (R.subgroupOf N).index := by
        obtain ⟨a, hN_idx_pow⟩ : ∃ a : ℕ, N.index = p ^ a := by
          rw [hN_def]
          exact OPrime_index_isPGroup p G
        have hNP_coprime : Nat.Coprime N.index (P : Subgroup G).index := by
          rw [hN_idx_pow]
          exact (Nat.Prime.coprime_pow_of_not_dvd (m := a) Fact.out P.not_dvd_index).symm
        have hNP_top : N ⊔ (P : Subgroup G) = ⊤ :=
          OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hNP_coprime
        have h_index_eq : (R.subgroupOf N).index = (P : Subgroup G).index := by
          have hR_le_N' : R ≤ N := hR_le_N
          have hR_rel_mul : R.relIndex N * N.index = R.index :=
            Subgroup.relIndex_mul_index hR_le_N'
          have hN_rel_P : N.relIndex (P : Subgroup G) = N.index := by
            rw [← Subgroup.relIndex_sup_right (H := (P : Subgroup G)) (K := N),
              sup_comm, hNP_top, Subgroup.relIndex_top_right]
          have hNP_rel_mul : N.relIndex (P : Subgroup G) * (P : Subgroup G).index =
              R.index := by
            have h := Subgroup.relIndex_inf_mul_relIndex (H := N)
              (K := (P : Subgroup G)) (L := (⊤ : Subgroup G))
            simpa [Subgroup.relIndex_top_right, hR_def, inf_comm] using h
          have hmul : R.relIndex N * N.index = (P : Subgroup G).index * N.index := by
            rw [hR_rel_mul, ← hNP_rel_mul, hN_rel_P, mul_comm N.index]
          have hrel : R.relIndex N = (P : Subgroup G).index :=
            Nat.eq_of_mul_eq_mul_right
              (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hmul
          exact hrel
        rw [h_index_eq]
        exact P.not_dvd_index
      let RN : Sylow p N := hRN_pgroup.toSylow hRN_not_dvd
      have hRN_eq : (RN : Subgroup N) = R.subgroupOf N :=
        hRN_pgroup.toSylow_coe hRN_not_dvd
      have hAPrime_top : APrime p N = ⊤ :=
        APrime_eq_top_of_eq_OPrime (G := G) (p := p) (N := N) hN_def
      have hRN_focal_eq : RN.focalSubgroup = (RN : Subgroup N) :=
        sylow_focalSubgroup_eq_self_of_APrime_eq_top RN hAPrime_top
      have hRN_le_focal : R.subgroupOf N ≤ RN.focalSubgroup := by
        intro x hx
        rw [hRN_focal_eq, hRN_eq]
        exact hx
      have hRN_focal_map_le : RN.focalSubgroup.map N.subtype ≤ R.focalSubgroup := by
        rw [Subgroup.focalSubgroup_def, MonoidHom.map_closure, Subgroup.focalSubgroup_def]
        apply Subgroup.closure_mono
        rintro y ⟨z, hz, rfl⟩
        rcases hz with ⟨hzRN, x, hxRN, u, rfl⟩
        have hzR : ((⁅x, u⁆ : N) : G) ∈ R := hzRN
        have hxR : (x : G) ∈ R := by
          have hxRN' : x ∈ R.subgroupOf N := by
            rwa [hRN_eq] at hxRN
          exact hxRN'
        exact ⟨hzR, (x : G), hxR, (u : G), rfl⟩
      intro r hr
      let x : N := ⟨r, hR_le_N hr⟩
      have hxRN : x ∈ R.subgroupOf N := hr
      have hxFocal : x ∈ RN.focalSubgroup := hRN_le_focal hxRN
      exact hRN_focal_map_le (Subgroup.mem_map_of_mem N.subtype hxFocal)
    exact h_R_le_focal.trans h_focal_R_le_comm
  -- Helper: `(⊤ : Subgroup ↥P).map P.subtype = P` (via `range_eq_map` + `range_subtype`).
  have h_top_map : ((⊤ : Subgroup ↥(P : Subgroup G))).map (P : Subgroup G).subtype =
      (P : Subgroup G) := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  -- **Step 5 (iteration)**: `∀ n, R ≤ ((⊤ : Subgroup ↥P).lowerCentralSeries n).map P.subtype`.
  -- Base: R ⊆ P = ⊤.map subtype. Step: R ≤ ⁅R, P⁆ = ⁅R, ⊤.map subtype⁆ ≤ ⁅(lcs n).map, ⊤.map⁆
  --       = (⁅lcs n, ⊤⁆).map = (lcs (n+1)).map.
  have h_R_le_lcs : ∀ n : ℕ, R ≤ Subgroup.map (P : Subgroup G).subtype
      ((⊤ : Subgroup ↥(P : Subgroup G)).lowerCentralSeries n) := by
    intro n
    induction n with
    | zero =>
      show R ≤ Subgroup.map (P : Subgroup G).subtype ⊤
      rw [h_top_map]
      exact inf_le_left
    | succ n ih =>
      change R ≤ Subgroup.map (P : Subgroup G).subtype
        ⁅(⊤ : Subgroup ↥(P : Subgroup G)).lowerCentralSeries n,
          (⊤ : Subgroup ↥(P : Subgroup G))⁆
      rw [Subgroup.map_commutator, h_top_map]
      exact h_R_le_comm.trans (Subgroup.commutator_mono ih le_rfl)
  -- **Step 6 (termination)**: `P` is a finite p-group ⇒ nilpotent ⇒ `∃ n, lcs ↥P n = ⊥`.
  haveI hP_pgroup : IsPGroup p ↥(P : Subgroup G) := P.isPGroup'
  haveI hP_nilp : Group.IsNilpotent ↥(P : Subgroup G) := hP_pgroup.isNilpotent
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hP_nilp
  have : R ≤ ⊥ := by
    have := h_R_le_lcs n
    rw [hn, Subgroup.map_bot] at this
    exact this
  exact le_bot_iff.mp this

/-- **Isaacs Thm 5.25 (⇐)**: any Sylow_p `P` controls own fusion ⇒ G has normal p-complement.

**証明** (Isaacs p.173, harder direction): `N := OPrime p G`. 主な仕事は
`(P : Subgroup G) ⊓ N = ⊥` を示すことで, これが
`OPrime_meet_sylow_eq_bot_of_controlsOwnFusion` (前置の helper). 残りは:
(B) Sylow II + N normal で任意 Sylow `R` に拡張 (`g • (P ⊓ N) = (g • P) ⊓ N`). ✅
(C) p ∤ |N| (任意 Sylow R で R ⊓ N = ⊥ + Cauchy 矛盾) → `|N| · |P'| = |G|` +
    `Nat.Coprime (|N|) (p^a)` → `Subgroup.isComplement'_of_coprime`. ✅

**実装状態 (2026-05-25)**: Step A (heart) + Steps B/C 完成 (sorry-free). -/
theorem hasNormalPComplement_of_controlsOwnFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : P.ControlsOwnFusion) :
    HasNormalPComplement p G := by
  -- Set N := OPrime p G, the normal-p-complement witness.
  set N : Subgroup G := OPrime p G with hN_def
  haveI hN_normal : N.Normal := inferInstance
  -- |G : N| is a p-power, say p^a.
  obtain ⟨a, hN_idx_pow⟩ := OPrime_index_isPGroup p G
  -- **Step A** (heart, deferred to helper): `(P : Subgroup G) ⊓ N = ⊥`.
  have h_PN_bot : (P : Subgroup G) ⊓ N = ⊥ :=
    OPrime_meet_sylow_eq_bot_of_controlsOwnFusion P hP
  -- **Step B**: Conjugation propagates Step A to every Sylow `R` (Sylow II + N normal):
  -- ∃ g, g • P = R. Then `(R ⊓ N) = (g • P) ⊓ (g • N) = g • (P ⊓ N) = g • ⊥ = ⊥`.
  have h_all_sylow : ∀ R : Sylow p G, (R : Subgroup G) ⊓ N = ⊥ := fun R => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P R
    have h_R_eq : (R : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    have h_N_eq : MulAut.conj g • N = N := Subgroup.Normal.conj_smul_eq_self g N
    calc (R : Subgroup G) ⊓ N
        = MulAut.conj g • (P : Subgroup G) ⊓ N := by rw [h_R_eq]
      _ = MulAut.conj g • (P : Subgroup G) ⊓ MulAut.conj g • N := by rw [h_N_eq]
      _ = MulAut.conj g • ((P : Subgroup G) ⊓ N) := (Subgroup.smul_inf _ _ _).symm
      _ = MulAut.conj g • (⊥ : Subgroup G) := by rw [h_PN_bot]
      _ = ⊥ := Subgroup.smul_bot _
  -- **Step C**: `p ∤ |N|` (any p-element in N would lie in some Sylow R, hence in R ⊓ N = ⊥)
  -- ⇒ `|N| · p^c = |G|` where `c = (|G|).factorization p` ⇒ `c = a` ⇒ `|N| · |P'| = |G|`
  -- + disjoint ⇒ `IsComplement' N P'`.
  refine ⟨N, hN_normal, fun P' => ?_⟩
  have h_P'N_bot : (P' : Subgroup G) ⊓ N = ⊥ := h_all_sylow P'
  -- C.1: p ∤ |N|
  have h_p_ndvd_N : ¬ p ∣ Nat.card ↥N := by
    intro hp_dvd
    obtain ⟨x, hx_order⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hp_dvd
    have hx_ne : (x : ↥N) ≠ 1 := by
      intro h; rw [h, orderOf_one] at hx_order
      exact (Fact.out : p.Prime).one_lt.ne hx_order
    -- (x : G) has the same order p (Subgroup.orderOf_coe)
    have hx_order_G : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx_order
    -- ⟨x.val⟩ as Subgroup G is a p-group (cyclic of order p)
    have hpg : IsPGroup p (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card ((Nat.card_zpowers (x : G)).trans hx_order_G |>.trans (pow_one p).symm)
    obtain ⟨Q, hQ_le⟩ := hpg.exists_le_sylow
    have hxQ : (x : G) ∈ (Q : Subgroup G) := hQ_le (Subgroup.mem_zpowers _)
    have hxN : (x : G) ∈ N := x.property
    have h_in : (x : G) ∈ (Q : Subgroup G) ⊓ N := ⟨hxQ, hxN⟩
    rw [h_all_sylow Q, Subgroup.mem_bot] at h_in
    exact hx_ne (Subtype.ext h_in)
  -- C.2: factorization of |G| at p = a
  have h_fact_a : (Nat.card G).factorization p = a := by
    have hN_card_mul : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
    have h_total : Nat.card G = Nat.card ↥N * p ^ a := by rw [← hN_card_mul, hN_idx_pow]
    rw [h_total, Nat.factorization_mul (Nat.card_pos (α := ↥N)).ne'
      (pow_pos (Fact.out : p.Prime).pos a).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h_p_ndvd_N,
      Nat.Prime.factorization_pow (Fact.out : p.Prime),
      Finsupp.single_apply]
    simp
  -- C.3: |P'| = p^a, hence |N| · |P'| = |G|
  have hP'_card : Nat.card ↥(P' : Subgroup G) = p ^ a := by
    rw [P'.card_eq_multiplicity, h_fact_a]
  have h_card_mul : Nat.card ↥N * Nat.card ↥(P' : Subgroup G) = Nat.card G := by
    rw [hP'_card, ← hN_idx_pow]; exact Subgroup.card_mul_index N
  -- C.4: Coprime |N| |P'|
  have h_coprime : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(P' : Subgroup G)) := by
    rw [hP'_card]
    exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_p_ndvd_N).symm).pow_right a
  exact Subgroup.isComplement'_of_coprime h_card_mul h_coprime

/-- **Isaacs Thm 5.25**: G has normal p-complement ⇔ Sylow_p controls own fusion. -/
theorem hasNormalPComplement_iff_controlsOwnFusion [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    HasNormalPComplement p G ↔ P.ControlsOwnFusion :=
  ⟨controlsOwnFusion_of_hasNormalPComplement P, hasNormalPComplement_of_controlsOwnFusion P⟩

/-! **Isaacs Thm 5.26 Frobenius normal p-complement** (forward declaration; theorem 化は下記)
は (1) ⇔ (3) で記述. 詳細は Lem 5.27, Lem 5.28 完成後の theorem 化を参照. -/

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
      refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
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

/-- Criterion after Isaacs Thm 5.26: to check
`N_G(X) / C_G(X)` is a p-group, it suffices to show that every q-subgroup (`q ≠ p`)
normalizing a p-subgroup `X` centralizes it.

This is the formal version of the paragraph preceding Cor 5.29. -/
theorem isPGroup_normalizerQuotientCentralizer_of_prime_subgroups_centralize
    [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      ∀ {X Q : Subgroup G}, IsPGroup p X → IsPGroup q Q →
        Q ≤ Subgroup.normalizer (X : Set G) →
        Q ≤ Subgroup.centralizer (X : Set G))
    (X : Subgroup G) (hXp : IsPGroup p X) :
    IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
      (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN_def
  set C : Subgroup N := (Subgroup.centralizer (X : Set G)).subgroupOf N with hC_def
  suffices h_idx_pow : ∃ b, C.index = p ^ b by
    obtain ⟨b, hb⟩ := h_idx_pow
    refine IsPGroup.of_card (n := b) ?_
    rw [← Subgroup.index_eq_card]
    exact hb
  have hC_index_ne_zero : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨C.index.primeFactorsList.length, ?_⟩
  rw [← List.prod_replicate, ← List.eq_replicate_of_mem ?_,
    Nat.prod_primeFactorsList hC_index_ne_zero]
  intro q hq
  obtain ⟨hq_prime, hq_dvd_C_index⟩ := (Nat.mem_primeFactorsList hC_index_ne_zero).mp hq
  haveI : Fact q.Prime := ⟨hq_prime⟩
  by_contra hq_ne_p
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow q N))
  let Q : Subgroup G := (S : Subgroup N).map N.subtype
  have hQ_q : IsPGroup q Q := S.isPGroup'.map N.subtype
  have hQ_le_N : Q ≤ Subgroup.normalizer (X : Set G) := by
    simpa [Q, hN_def] using Subgroup.map_subtype_le (H := N) (S : Subgroup N)
  have hQ_le_CG : Q ≤ Subgroup.centralizer (X : Set G) :=
    h hq_ne_p hXp hQ_q hQ_le_N
  have hS_le_C : (S : Subgroup N) ≤ C := by
    intro s hs
    rw [hC_def, Subgroup.mem_subgroupOf]
    exact hQ_le_CG (Subgroup.mem_map_of_mem N.subtype hs)
  have hC_dvd_S_index : C.index ∣ (S : Subgroup N).index :=
    Subgroup.index_dvd_of_le hS_le_C
  exact S.not_dvd_index (hq_dvd_C_index.trans hC_dvd_S_index)

/-- **N = S · C 補題**: `S : Sylow p N`, `C ⊴ N` で `N/C` が p-group ⇒
`(S : Subgroup N) ⊔ C = ⊤`.

**証明**: `mk' C : N →* N/C` 全射. `S.mapSurjective mk' surj : Sylow p (N/C)`.
`N/C` は p-group なので任意 Sylow p = ⊤ (cardinality 一致). よって
`S.map (mk' C) = ⊤`. `comap_map_eq` で `S ⊔ ker (mk' C) = S ⊔ C = ⊤`. -/
private lemma sylow_sup_normal_eq_top_of_quot_isPGroup
    {N : Type*} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    {C : Subgroup N} [C.Normal] (hQ : IsPGroup p (N ⧸ C))
    (S : Sylow p N) :
    (S : Subgroup N) ⊔ C = ⊤ := by
  have hSurj : Function.Surjective (QuotientGroup.mk' C : N →* N ⧸ C) :=
    QuotientGroup.mk'_surjective C
  let S' : Sylow p (N ⧸ C) := S.mapSurjective hSurj
  -- (S' : Subgroup (N ⧸ C)) = ⊤ via cardinality
  have h_S'_top : (S' : Subgroup (N ⧸ C)) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [S'.card_eq_multiplicity]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    rw [hk, Nat.factorization_pow_self Fact.out]
  -- Translate back: S ⊔ C = ⊤
  have h_S_map : (S : Subgroup N).map (QuotientGroup.mk' C) = ⊤ := h_S'_top
  have h := Subgroup.comap_map_eq (f := QuotientGroup.mk' C) (S : Subgroup N)
  rw [h_S_map, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
  exact h.symm

/-- **"Normalizers grow" in p-group** (mathlib `lt_normalizer_of_isNilpotent_of_lt_top` の
p-group 特殊化). `G` finite p-group, `H : Subgroup G` で `H < ⊤` ⇒
`H < Subgroup.normalizer (H : Set G)`. -/
private lemma lt_normalizer_of_pgroup_of_lt_top
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) {H : Subgroup G} (hH : H < ⊤) :
    H < Subgroup.normalizer (H : Set G) := by
  haveI : Group.IsNilpotent G := IsPGroup.isNilpotent hG
  exact OddOrder.Isaacs.Ch01.lt_normalizer_of_isNilpotent_of_lt_top hH

/-- **Isaacs Lem 5.28**: 仮定「∀ p-subgroup `X` ⊆ `G`, `N_G(X)/C_G(X)` は p-group」
⇒ 任意 `P, Q : Sylow p G` で `Q = P^c` (= `c • Q = P` in mathlib 流) を満たす
`c ∈ C_G(P ⊓ Q)` が存在. **Frobenius normal p-complement 5.26 の鍵補題**.

**証明** (Isaacs p.174-175): `D := P ⊓ Q` の cardinality に関する強帰納法 (counter-example
の最大 `|D|` を取る). `D < P, D < Q` (else `P = Q`, `c = 1`).
* `N := N_G(D)`, `C := C_G(D)`, 仮定で `N/C` は p-group.
* `P ⊓ N = N_P(D) > D` (`IsPGroup.lt_normalizer_subgroupOf`).
* `S := Sylow p N ⊇ P ⊓ N`, `T := Sylow p N ⊇ Q ⊓ N`, `R := Sylow p G ⊇ S`.
* `N = S · C` (`sylow_sup_normal_eq_top_of_quot_isPGroup`).
* Sylow II in `N`: `T = n • S`, `n = s · y`, `s ∈ S`, `y ∈ C` ⇒ `T = y • S ⊆ y • R = R^y`.
* `P ⊓ R ⊇ P ⊓ N > D` ⇒ IH on `(P, R)`: `∃ x ∈ C_G(P ⊓ R), x • R = P`. `x` centralizes `D`.
* `R^y ⊓ Q ⊇ T ⊓ Q ⊇ Q ⊓ N > D` ⇒ IH on `(R^y, Q)`: `∃ z ∈ C_G(R^y ⊓ Q), z • Q = R^y`.
  `z` centralizes `D`.
* `(x y z) • Q = x • y • z • Q = x • (y • R^y) = x • R = P`. `x, y, z` all centralize `D`,
  hence `xyz ∈ C_G(D)`. 完了.

**実装状態 (2026-05-24)**: 助補題 (sylow_sup_normal + normalizers grow) は実装済.
本体は ~250 LOC で骨格のみ. 完全形式化は別 session.

**FT クリティカル**: Frobenius 5.26 (3⇒1) 経由. -/
theorem isaacs_lem_5_28 [Finite G] {p : ℕ} [Fact p.Prime]
    (hH : ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))))
    (P Q : Sylow p G) :
    ∃ c ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G)) : Set G),
      c • Q = P := by
  -- Strong induction on `k = ((P : Subgroup G) ⊓ Q).index`. Smaller k = larger intersection.
  suffices h : ∀ k : ℕ, ∀ (P Q : Sylow p G),
      ((P : Subgroup G) ⊓ (Q : Subgroup G)).index = k →
      ∃ c ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G)) : Set G),
        c • Q = P by exact h _ P Q rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P Q hk
    -- **Case 1**: P = Q. Take c = 1.
    by_cases hPQ : P = Q
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [hPQ, one_smul]
    -- **Case 2**: P ≠ Q. Apply textbook argument.
    · -- D := P ⊓ Q. P ≠ Q + Sylow card equality ⇒ D < P, D < Q.
      set D : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G) with hD_def
      have hPQ_card_eq : Nat.card ↥(P : Subgroup G) = Nat.card ↥(Q : Subgroup G) := by
        rw [P.card_eq_multiplicity, Q.card_eq_multiplicity]
      have hD_lt_P : D < (P : Subgroup G) := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h_eq
        have hP_le_Q : (P : Subgroup G) ≤ (Q : Subgroup G) := h_eq ▸ inf_le_right
        have h_subgroup_eq : (P : Subgroup G) = (Q : Subgroup G) :=
          Subgroup.eq_of_le_of_card_ge hP_le_Q hPQ_card_eq.symm.le
        exact hPQ (Sylow.ext h_subgroup_eq)
      have hD_lt_Q : D < (Q : Subgroup G) := by
        refine lt_of_le_of_ne inf_le_right ?_
        intro h_eq
        have hQ_le_P : (Q : Subgroup G) ≤ (P : Subgroup G) := h_eq ▸ inf_le_left
        have h_subgroup_eq : (P : Subgroup G) = (Q : Subgroup G) :=
          (Subgroup.eq_of_le_of_card_ge hQ_le_P hPQ_card_eq.le).symm
        exact hPQ (Sylow.ext h_subgroup_eq)
      -- N := normalizer D, C := centralizer D
      set N : Subgroup G := Subgroup.normalizer (D : Set G) with hN_def
      set C : Subgroup G := Subgroup.centralizer (D : Set G) with hC_def
      -- D ≤ N (le_normalizer), D ≤ P (already), D ≤ Q (already), D ≤ C (D centralizes itself? NO!)
      -- D centralizes itself only if D is abelian. Skip — we don't need D ≤ C.
      have hD_le_N : D ≤ N := Subgroup.le_normalizer
      have hD_le_P : D ≤ (P : Subgroup G) := inf_le_left
      have hD_le_Q : D ≤ (Q : Subgroup G) := inf_le_right
      -- D is p-group (subgroup of P p-group)
      have hD_pgroup : IsPGroup p ↥D := P.isPGroup'.to_le inf_le_left
      -- hH applied: ↥N ⧸ C.subgroupOf N is p-group
      have h_quot_pgroup : IsPGroup p (↥N ⧸ C.subgroupOf N) := hH D hD_pgroup
      -- **Step 1**: P ⊓ N > D via "normalizers grow" in ↥P
      have hPN_gt_D : D < (P : Subgroup G) ⊓ N := by
        have hD_sub_P_lt_top : D.subgroupOf (P : Subgroup G) < ⊤ := by
          rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
          intro h_le; exact (not_le_of_gt hD_lt_P) h_le
        have h_lt_norm : D.subgroupOf (P : Subgroup G) <
            Subgroup.normalizer ((D.subgroupOf (P : Subgroup G)) : Set ↥(P : Subgroup G)) :=
          lt_normalizer_of_pgroup_of_lt_top P.isPGroup' hD_sub_P_lt_top
        have h_norm_eq : Subgroup.normalizer ((D.subgroupOf (P : Subgroup G)) :
            Set ↥(P : Subgroup G)) = N.subgroupOf (P : Subgroup G) :=
          (Subgroup.subgroupOf_normalizer_eq hD_le_P).symm
        rw [h_norm_eq] at h_lt_norm
        -- D.subgroupOf P < N.subgroupOf P (in ↥P). |·| translates to G.
        have h_card_lt : Nat.card ↥(D.subgroupOf (P : Subgroup G)) <
            Nat.card ↥(N.subgroupOf (P : Subgroup G)) := by
          have h_dvd := Subgroup.card_dvd_of_le h_lt_norm.le
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h_dvd) ?_
          intro hcardeq
          exact h_lt_norm.ne
            (Subgroup.eq_of_le_of_card_ge h_lt_norm.le hcardeq.symm.le)
        have h_card_D : Nat.card ↥(D.subgroupOf (P : Subgroup G)) = Nat.card ↥D :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_P).toEquiv
        have h_card_NP : Nat.card ↥(N.subgroupOf (P : Subgroup G)) =
            Nat.card ↥((P : Subgroup G) ⊓ N) := by
          rw [show (P : Subgroup G) ⊓ N = N ⊓ (P : Subgroup G) from inf_comm _ _,
              ← Subgroup.subgroupOf_map_subtype]
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective _ _ ((P : Subgroup G).subtype_injective)).toEquiv
        rw [h_card_D, h_card_NP] at h_card_lt
        exact lt_of_le_of_ne (le_inf hD_le_P hD_le_N)
          (fun h => Nat.lt_irrefl _ (h ▸ h_card_lt))
      -- **Step 2**: Q ⊓ N > D (symmetric)
      have hQN_gt_D : D < (Q : Subgroup G) ⊓ N := by
        have hD_sub_Q_lt_top : D.subgroupOf (Q : Subgroup G) < ⊤ := by
          rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
          intro h_le; exact (not_le_of_gt hD_lt_Q) h_le
        have h_lt_norm : D.subgroupOf (Q : Subgroup G) <
            Subgroup.normalizer ((D.subgroupOf (Q : Subgroup G)) : Set ↥(Q : Subgroup G)) :=
          lt_normalizer_of_pgroup_of_lt_top Q.isPGroup' hD_sub_Q_lt_top
        have h_norm_eq : Subgroup.normalizer ((D.subgroupOf (Q : Subgroup G)) :
            Set ↥(Q : Subgroup G)) = N.subgroupOf (Q : Subgroup G) :=
          (Subgroup.subgroupOf_normalizer_eq hD_le_Q).symm
        rw [h_norm_eq] at h_lt_norm
        have h_card_lt : Nat.card ↥(D.subgroupOf (Q : Subgroup G)) <
            Nat.card ↥(N.subgroupOf (Q : Subgroup G)) := by
          have h_dvd := Subgroup.card_dvd_of_le h_lt_norm.le
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h_dvd) ?_
          intro hcardeq
          exact h_lt_norm.ne
            (Subgroup.eq_of_le_of_card_ge h_lt_norm.le hcardeq.symm.le)
        have h_card_D : Nat.card ↥(D.subgroupOf (Q : Subgroup G)) = Nat.card ↥D :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_Q).toEquiv
        have h_card_NQ : Nat.card ↥(N.subgroupOf (Q : Subgroup G)) =
            Nat.card ↥((Q : Subgroup G) ⊓ N) := by
          rw [show (Q : Subgroup G) ⊓ N = N ⊓ (Q : Subgroup G) from inf_comm _ _,
              ← Subgroup.subgroupOf_map_subtype]
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective _ _ ((Q : Subgroup G).subtype_injective)).toEquiv
        rw [h_card_D, h_card_NQ] at h_card_lt
        exact lt_of_le_of_ne (le_inf hD_le_Q hD_le_N)
          (fun h => Nat.lt_irrefl _ (h ▸ h_card_lt))
      -- **Step 3**: Sylow p of ↥N containing (P ⊓ N).subgroupOf N, (Q ⊓ N).subgroupOf N
      have hPN_pgroup_in_N : IsPGroup p ↥(((P : Subgroup G) ⊓ N).subgroupOf N) := by
        have h_iso : ((P : Subgroup G) ⊓ N).subgroupOf N ≃* ↥((P : Subgroup G) ⊓ N) :=
          Subgroup.subgroupOfEquivOfLe inf_le_right
        exact (P.isPGroup'.to_le inf_le_left).of_equiv h_iso.symm
      have hQN_pgroup_in_N : IsPGroup p ↥(((Q : Subgroup G) ⊓ N).subgroupOf N) := by
        have h_iso : ((Q : Subgroup G) ⊓ N).subgroupOf N ≃* ↥((Q : Subgroup G) ⊓ N) :=
          Subgroup.subgroupOfEquivOfLe inf_le_right
        exact (Q.isPGroup'.to_le inf_le_left).of_equiv h_iso.symm
      obtain ⟨S, hPN_le_S⟩ := IsPGroup.exists_le_sylow hPN_pgroup_in_N
      obtain ⟨T, hQN_le_T⟩ := IsPGroup.exists_le_sylow hQN_pgroup_in_N
      -- **Step 4**: R : Sylow p G containing S.map N.subtype
      set S_in_G : Subgroup G := (S : Subgroup ↥N).map N.subtype with hS_in_G_def
      have hS_in_G_pgroup : IsPGroup p ↥S_in_G := S.isPGroup'.map _
      obtain ⟨R, hS_in_G_le_R⟩ := IsPGroup.exists_le_sylow hS_in_G_pgroup
      -- **Step 5**: S ⊔ C.subgroupOf N = ⊤ in ↥N (via helper)
      have hS_sup_C : (S : Subgroup ↥N) ⊔ C.subgroupOf N = ⊤ :=
        sylow_sup_normal_eq_top_of_quot_isPGroup h_quot_pgroup S
      -- **Step 6**: Sylow II in ↥N: ∃ n : ↥N, n • S = T
      obtain ⟨n, hn_smul⟩ := MulAction.exists_smul_eq (↥N) S T
      -- **Step 7**: Decompose n = yC * sS (yC ∈ C.subgroupOf N, sS ∈ S)
      have hC_sup_S : C.subgroupOf N ⊔ (S : Subgroup ↥N) = ⊤ := by
        rw [sup_comm]; exact hS_sup_C
      have hn_in_top : (n : ↥N) ∈ C.subgroupOf N ⊔ (S : Subgroup ↥N) := by
        rw [hC_sup_S]; exact Subgroup.mem_top _
      obtain ⟨yC, hyC_in, sS, hsS_in, hn_eq⟩ := Subgroup.mem_sup_of_normal_left.mp hn_in_top
      -- **Step 8**: T = yC • S (since (yC * sS) • S = yC • (sS • S) = yC • S)
      have h_sS_S : (sS : ↥N) • S = S := by
        rw [Sylow.smul_eq_iff_mem_normalizer]; exact Subgroup.le_normalizer hsS_in
      have h_T_eq : T = yC • S := by
        rw [← hn_smul, ← hn_eq, mul_smul, h_sS_S]
      -- **Step 10 preview**: index strict inequality for IH (works for any subgroup > D).
      -- P ⊓ R ≥ P ⊓ N (via S_in_G ≤ R and P ⊓ N ⊆ S_in_G), and P ⊓ N > D.
      have hPN_le_S_in_G : (P : Subgroup G) ⊓ N ≤ S_in_G := by
        intro x hx
        have ⟨_, hx_N⟩ := Subgroup.mem_inf.mp hx
        refine ⟨⟨x, hx_N⟩, ?_, rfl⟩
        exact hPN_le_S (by rw [Subgroup.mem_subgroupOf]; exact hx)
      have hPN_le_R : (P : Subgroup G) ⊓ N ≤ (R : Subgroup G) :=
        hPN_le_S_in_G.trans hS_in_G_le_R
      have hPR_gt_D : D < (P : Subgroup G) ⊓ R :=
        lt_of_lt_of_le hPN_gt_D (le_inf inf_le_left hPN_le_R)
      -- **Step 9**: yR := yC.val • R (Sylow in G). Q ⊓ N ≤ yR.
      set yR : Sylow p G := (yC : G) • R with hyR_def
      have hQN_le_yR : (Q : Subgroup G) ⊓ N ≤ (yR : Subgroup G) := by
        intro q hq
        obtain ⟨hq_Q, hq_N⟩ := Subgroup.mem_inf.mp hq
        let q_N : ↥N := ⟨q, hq_N⟩
        have hq_N_in_QN : q_N ∈ ((Q : Subgroup G) ⊓ N).subgroupOf N := by
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_inf.mpr ⟨hq_Q, hq_N⟩
        have hq_N_in_T : q_N ∈ (T : Subgroup ↥N) := hQN_le_T hq_N_in_QN
        have hq_in_yCS : q_N ∈ ((yC • S : Sylow p ↥N) : Subgroup ↥N) := by
          rw [← h_T_eq]; exact hq_N_in_T
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq_in_yCS
        -- hq_in_yCS : (MulAut.conj yC)⁻¹ • q_N ∈ S
        have hs_in_R : ((MulAut.conj yC)⁻¹ q_N : ↥N).val ∈ (R : Subgroup G) := by
          apply hS_in_G_le_R
          exact ⟨(MulAut.conj yC)⁻¹ q_N, hq_in_yCS, rfl⟩
        show q ∈ (((yC : G) • R : Sylow p G) : Subgroup G)
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        -- Goal: (MulAut.conj (yC : G))⁻¹ q ∈ (R : Subgroup G)
        -- Both sides equal (yC : G)⁻¹ * q * (yC : G); ((MulAut.conj yC)⁻¹ q_N).val computes same
        convert hs_in_R using 1
        simp only [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.coe_mul,
          InvMemClass.coe_inv]
        rfl
      -- **Step 10**: index strict inequalities for IH (P, R) and (yR, Q)
      have hQyR_gt_D : D < (Q : Subgroup G) ⊓ yR :=
        lt_of_lt_of_le hQN_gt_D (le_inf inf_le_left hQN_le_yR)
      -- (P ⊓ R).index < k (D.index)
      have h_PR_idx_lt : ((P : Subgroup G) ⊓ R : Subgroup G).index < k := by
        rw [← hk]
        have h_dvd : ((P : Subgroup G) ⊓ R).index ∣ D.index :=
          Subgroup.index_dvd_of_le hPR_gt_D.le
        have h_D_idx_pos : 0 < D.index :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        refine lt_of_le_of_ne (Nat.le_of_dvd h_D_idx_pos h_dvd) ?_
        intro h_eq
        have h_card_eq : Nat.card ↥D = Nat.card ↥((P : Subgroup G) ⊓ R) := by
          have h1 := Subgroup.index_mul_card D
          have h2 := Subgroup.index_mul_card ((P : Subgroup G) ⊓ R)
          rw [h_eq] at h2
          exact Nat.eq_of_mul_eq_mul_left h_D_idx_pos (h1.trans h2.symm)
        exact hPR_gt_D.ne (Subgroup.eq_of_le_of_card_ge hPR_gt_D.le h_card_eq.ge)
      -- ((Q ⊓ yR)).index < k. Note inf_comm: Q ⊓ yR = yR ⊓ Q? Use Q ⊓ yR for symmetric IH.
      have h_QyR_idx_lt : ((Q : Subgroup G) ⊓ yR : Subgroup G).index < k := by
        rw [← hk]
        have h_dvd : ((Q : Subgroup G) ⊓ yR).index ∣ D.index :=
          Subgroup.index_dvd_of_le hQyR_gt_D.le
        have h_D_idx_pos : 0 < D.index :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        refine lt_of_le_of_ne (Nat.le_of_dvd h_D_idx_pos h_dvd) ?_
        intro h_eq
        have h_card_eq : Nat.card ↥D = Nat.card ↥((Q : Subgroup G) ⊓ yR) := by
          have h1 := Subgroup.index_mul_card D
          have h2 := Subgroup.index_mul_card ((Q : Subgroup G) ⊓ yR)
          rw [h_eq] at h2
          exact Nat.eq_of_mul_eq_mul_left h_D_idx_pos (h1.trans h2.symm)
        exact hQyR_gt_D.ne (Subgroup.eq_of_le_of_card_ge hQyR_gt_D.le h_card_eq.ge)
      -- **Step 11**: IH applications + combine c = x · yC.val⁻¹ · z
      -- IH on (P, R): (P : Subgroup G) ⊓ R as intersection (need to match shape)
      -- The IH wants ∃ c ∈ centralizer((P' ⊓ Q' : Set G)), c • Q' = P' for any P' Q' pair with
      -- index of P' ⊓ Q' < k. Apply to (P, R) and (yR, Q).
      obtain ⟨x, hx_C, hxR⟩ := ih _ h_PR_idx_lt P R rfl
      -- hx_C : x ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (R : Subgroup G)) : Set G)
      -- hxR : x • R = P
      -- For (yR, Q): index = (yR : Subgroup G) ⊓ Q. Hmm I have Q ⊓ yR.
      have hyRQ_inf_eq : (yR : Subgroup G) ⊓ Q = (Q : Subgroup G) ⊓ yR := inf_comm _ _
      have h_yRQ_idx_lt' : ((yR : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G).index < k := by
        rw [hyRQ_inf_eq]; exact h_QyR_idx_lt
      obtain ⟨z, hz_C, hzQ⟩ := ih _ h_yRQ_idx_lt' yR Q rfl
      -- hz_C : z ∈ Subgroup.centralizer (((yR : Subgroup G) ⊓ (Q : Subgroup G)) : Set G)
      -- hzQ : z • Q = yR
      -- c := x * yC.val⁻¹ * z
      refine ⟨x * (yC : G)⁻¹ * z, ?_, ?_⟩
      · -- c ∈ centralizer D
        have hyC_cent_D : (yC : G) ∈ Subgroup.centralizer (D : Set G) := by
          have : yC.val ∈ C := by
            have := hyC_in
            rwa [Subgroup.mem_subgroupOf] at this
          exact this
        have hyC_inv_cent_D : ((yC : G))⁻¹ ∈ Subgroup.centralizer (D : Set G) :=
          (Subgroup.centralizer (D : Set G)).inv_mem hyC_cent_D
        have hx_cent_D : x ∈ Subgroup.centralizer (D : Set G) := by
          have h_D_le : (D : Set G) ⊆ (((P : Subgroup G) ⊓ R : Subgroup G) : Set G) := by
            intro a ha
            exact Subgroup.mem_inf.mpr
              ⟨hD_le_P ha, hPN_le_R (le_inf hD_le_P hD_le_N ha)⟩
          exact Subgroup.centralizer_le h_D_le hx_C
        have hz_cent_D : z ∈ Subgroup.centralizer (D : Set G) := by
          have h_D_le : (D : Set G) ⊆ (((yR : Subgroup G) ⊓ Q : Subgroup G) : Set G) := by
            intro a ha
            refine Subgroup.mem_inf.mpr ⟨?_, hD_le_Q ha⟩
            -- a ∈ yR = yC.val • R; yC centralizes D so yC⁻¹ a yC = a ∈ R
            show a ∈ (((yC : G) • R : Sylow p G) : Subgroup G)
            rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
            have h_a_in_R : a ∈ (R : Subgroup G) :=
              hPN_le_R (le_inf hD_le_P hD_le_N ha)
            have h_comm : a * (yC : G) = (yC : G) * a :=
              Subgroup.mem_centralizer_iff.mp hyC_cent_D a ha
            have h_smul_eq : (MulAut.conj (yC : G))⁻¹ • a = a := by
              show (yC : G)⁻¹ * a * (yC : G) = a
              rw [mul_assoc, h_comm, ← mul_assoc, inv_mul_cancel, one_mul]
            rw [h_smul_eq]; exact h_a_in_R
          exact Subgroup.centralizer_le h_D_le hz_C
        exact (Subgroup.centralizer (D : Set G)).mul_mem
          ((Subgroup.centralizer (D : Set G)).mul_mem hx_cent_D hyC_inv_cent_D)
          hz_cent_D
      · -- c • Q = P
        -- z • Q = yR = yC.val • R, so yC.val⁻¹ • (z • Q) = R, (yC.val⁻¹ * z) • Q = R
        -- x • R = P, so x • ((yC.val⁻¹ * z) • Q) = P, (x * yC.val⁻¹ * z) • Q = P
        rw [show (x * (yC : G)⁻¹ * z) • Q = x • ((yC : G)⁻¹ • (z • Q)) by
          rw [← mul_smul, ← mul_smul]]
        rw [hzQ, hyR_def]
        rw [show ((yC : G)⁻¹ • (yC : G) • R : Sylow p G) = R from by
          rw [← mul_smul, inv_mul_cancel, one_smul]]
        exact hxR

/-- **Isaacs Thm 5.26 Frobenius normal p-complement** ⭐ **FT クリティカル**.
`G` has normal p-complement ⇔ ∀ p-subgroup `X`, `N_G(X)/C_G(X)` is p-group.

**証明** (Isaacs p.175-177):
* (1) ⇒ (3): `hasNormalPComplement_of_subgroup` (Lem 5.27 Part 1) で
  ∀ p-subgroup X non-trivial, `normalizer X` も normal p-comp を持つ.
  `isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement`
  (Lem 5.27 Part 2) で結論. ✅
* (3) ⇒ (1): 任意 Sylow `P` で `P.ControlsOwnFusion` を示し (Lem 5.28 経由),
  `hasNormalPComplement_of_controlsOwnFusion` (Thm 5.25 ⇐) で normal p-comp. ✅ -/
theorem hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer
    [Finite G] {p : ℕ} [Fact p.Prime] :
    HasNormalPComplement p G ↔
    ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  refine ⟨fun hG X hXp => ?_, fun hH => ?_⟩
  · -- (1) ⇒ (3): via Lem 5.27 Part 1 + Part 2 (both sorry-free)
    exact isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
      (fun Y _hY_ne _hY_pg => hasNormalPComplement_of_subgroup hG
        (Subgroup.normalizer (Y : Set G)))
      X hXp
  · -- (3) ⇒ (1): Pick Sylow P, show P.ControlsOwnFusion via Lem 5.28,
    -- then apply Thm 5.25 (⇐).
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
    refine (hasNormalPComplement_iff_controlsOwnFusion P).mpr ?_
    intro x y hx_P hy_P ⟨g, hgxy⟩
    -- Apply Lem 5.28 to (P, g • P)
    set gP : Sylow p G := g • P with hgP_def
    -- y ∈ P ⊓ gP
    have hy_in_gP : y ∈ (gP : Subgroup G) := by
      show y ∈ ((g • P : Sylow p G) : Subgroup G)
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have h_smul_eq : (MulAut.conj g)⁻¹ • y = x := by
        show g⁻¹ * y * g = x
        rw [← hgxy]; group
      rw [h_smul_eq]; exact hx_P
    have hy_in_PgP : y ∈ (P : Subgroup G) ⊓ (gP : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨hy_P, hy_in_gP⟩
    -- Lem 5.28: ∃ c ∈ C(P ⊓ gP), c • gP = P
    obtain ⟨c, hc_C, hc_smul⟩ := isaacs_lem_5_28 hH P gP
    -- c centralizes y
    have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.mp hc_C y hy_in_PgP).symm
    -- cg ∈ N(P): c • gP = P ⇒ (c * g) • P = P ⇒ cg ∈ normalizer
    have hcg_in_N : c * g ∈ Subgroup.normalizer (P : Set G) := by
      rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul, ← hgP_def]
      exact hc_smul
    set N_P : Subgroup G := Subgroup.normalizer (P : Set G) with hN_P_def
    -- P ≤ N(P) (general)
    have hP_le_N : (P : Subgroup G) ≤ N_P := Subgroup.le_normalizer
    -- P as Sylow of ↥N(P)
    let P_NP : Sylow p ↥N_P := P.subtype hP_le_N
    -- hH applied to P: ↥N(P) / C(P).subgroupOf N(P) is p-group
    have h_quot_pgroup : IsPGroup p
        (↥N_P ⧸ (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P) :=
      hH P P.isPGroup'
    -- Normal instance for the centralizer subgroupOf
    haveI : ((Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P).Normal :=
      centralizer_subgroupOf_normalizer_normal (P : Subgroup G)
    -- N(P) = C(P).subgroupOf N(P) ⊔ P_NP (via helper applied to ↥N(P))
    have hSC_top : (P_NP : Subgroup ↥N_P) ⊔
        (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P = ⊤ :=
      sylow_sup_normal_eq_top_of_quot_isPGroup h_quot_pgroup P_NP
    -- cg lifted to ↥N(P)
    let cg_N : ↥N_P := ⟨c * g, hcg_in_N⟩
    have hcg_in_sup : cg_N ∈ (Subgroup.centralizer ((P : Subgroup G) : Set G)).subgroupOf N_P
        ⊔ (P_NP : Subgroup ↥N_P) := by
      rw [sup_comm]; rw [hSC_top]; exact Subgroup.mem_top _
    obtain ⟨t_N, ht_C, u_N, hu_P, htu_eq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hcg_in_sup
    -- t_N : ↥N(P), t_N ∈ centralizer.subgroupOf ⇒ t_N.val ∈ centralizer P
    -- u_N : ↥N(P), u_N ∈ P_NP ⇒ u_N.val ∈ P
    have ht_in_C : (t_N : G) ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
      have := ht_C
      rwa [Subgroup.mem_subgroupOf] at this
    have hu_in_P : (u_N : G) ∈ (P : Subgroup G) := by
      have := hu_P
      change (u_N : G) ∈ (P : Subgroup G) at this ⊢
      exact this
    -- (cg).val = t_N.val * u_N.val
    have hcg_val_eq : c * g = (t_N : G) * (u_N : G) := by
      have h := congrArg Subtype.val htu_eq
      exact h.symm
    -- y = (cg) • x = (t_N.val * u_N.val) • x = t_N.val • (u_N.val • x) = u_N.val • x (t centralizes uxu⁻¹ ∈ P)
    refine ⟨(u_N : G), hu_in_P, ?_⟩
    -- Goal: u_N.val * x * u_N.val⁻¹ = y
    -- First: y = (cg) x (cg)⁻¹. From c * y = y * c, y = c y c⁻¹ = c (g x g⁻¹) c⁻¹ = (cg) x (cg)⁻¹.
    have h_y_eq_cgx : y = (c * g) * x * (c * g)⁻¹ := by
      have h_c_y_eq : c * y * c⁻¹ = y := by
        rw [hcy]; group
      calc y = c * y * c⁻¹ := h_c_y_eq.symm
        _ = c * (g * x * g⁻¹) * c⁻¹ := by rw [hgxy]
        _ = (c * g) * x * (c * g)⁻¹ := by group
    -- (cg) x (cg)⁻¹ = (t * u) x (t * u)⁻¹. Use t centralizes uxu⁻¹ ∈ P to simplify.
    have h_uux_in_P : (u_N : G) * x * (u_N : G)⁻¹ ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem
        ((P : Subgroup G).mul_mem hu_in_P hx_P)
        ((P : Subgroup G).inv_mem hu_in_P)
    have h_t_comm : ((u_N : G) * x * (u_N : G)⁻¹) * (t_N : G) =
        (t_N : G) * ((u_N : G) * x * (u_N : G)⁻¹) :=
      Subgroup.mem_centralizer_iff.mp ht_in_C _ h_uux_in_P
    have h_t_uxu_eq : (t_N : G) * ((u_N : G) * x * (u_N : G)⁻¹) * (t_N : G)⁻¹ =
        (u_N : G) * x * (u_N : G)⁻¹ := by
      rw [← h_t_comm]; group
    calc (u_N : G) * x * (u_N : G)⁻¹
        = (t_N : G) * ((u_N : G) * x * (u_N : G)⁻¹) * (t_N : G)⁻¹ := h_t_uxu_eq.symm
      _ = ((t_N : G) * (u_N : G)) * x * ((t_N : G) * (u_N : G))⁻¹ := by group
      _ = (c * g) * x * (c * g)⁻¹ := by rw [← hcg_val_eq]
      _ = y := h_y_eq_cgx.symm

/-- Isaacs' p-local action criterion, packaged with Frobenius' normal p-complement theorem.

If every q-subgroup (`q ≠ p`) normalizing a p-subgroup centralizes it, then `G` has a
normal p-complement. This is the shared entry point for Cor 5.29 and Cor 5.30. -/
theorem hasNormalPComplement_of_prime_subgroups_centralize
    [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      ∀ {X Q : Subgroup G}, IsPGroup p X → IsPGroup q Q →
        Q ≤ Subgroup.normalizer (X : Set G) →
        Q ≤ Subgroup.centralizer (X : Set G)) :
    HasNormalPComplement p G :=
  hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer.mpr
    (fun X hXp =>
      isPGroup_normalizerQuotientCentralizer_of_prime_subgroups_centralize h X hXp)

/-- If a q-group acts on a finite set, then `q` divides the number of non-fixed points. -/
private lemma prime_dvd_card_sub_card_fixedPoints_of_pgroup_action
    {A X : Type*} [Group A] [Group X] [Finite X] [MulDistribMulAction A X]
    {q : ℕ} [Fact q.Prime] (hA : IsPGroup q A) :
    q ∣ Nat.card X - Nat.card (MulAction.fixedPoints A X) := by
  have hmod := hA.card_modEq_card_fixedPoints X
  have hle : Nat.card (MulAction.fixedPoints A X) ≤ Nat.card X :=
    Nat.card_le_card_of_injective _ (fun _ _ h => Subtype.ext h)
  exact (Nat.modEq_iff_dvd' hle).mp hmod.symm

/-- Orbit-count step in Isaacs Cor 5.29.

If a q-group acts nontrivially by automorphisms on a finite p-group `X`, and `|X| = p^k`
with `k ≤ a`, then `q ∣ p^e - 1` for some `1 ≤ e ≤ a`. -/
private lemma exists_prime_dvd_pow_sub_one_of_nontrivial_pgroup_action
    {A X : Type*} [Group A] [Group X] [Finite X] [MulDistribMulAction A X]
    {p q a : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hX : IsPGroup p X) (hA : IsPGroup q A) (hpq : q ≠ p)
    (hX_bound : ∃ k, k ≤ a ∧ Nat.card X = p ^ k)
    (hfix_ne : MulAction.fixedPoints A X ≠ Set.univ) :
    ∃ e, 1 ≤ e ∧ e ≤ a ∧ q ∣ p ^ e - 1 := by
  classical
  let F : Subgroup X := {
    carrier := MulAction.fixedPoints A X
    one_mem' := by intro g; exact smul_one g
    mul_mem' := by
      intro x y hx hy g
      rw [smul_mul', hx g, hy g]
    inv_mem' := by
      intro x hx g
      rw [smul_inv', hx g] }
  have hF_card_lt : Nat.card F < Nat.card X := by
    change Nat.card (MulAction.fixedPoints A X) < Nat.card X
    simpa [Nat.card_coe_set_eq] using Set.ncard_lt_card hfix_ne
  have hF_index_ne_one : F.index ≠ 1 := by
    intro hidx_one
    have hidx := F.index_mul_card
    rw [hidx_one, one_mul] at hidx
    exact (Nat.lt_irrefl _ (hidx ▸ hF_card_lt))
  obtain ⟨e, he_index⟩ := hX.index F
  have he_pos : 1 ≤ e := by
    cases e with
    | zero =>
        exfalso
        exact hF_index_ne_one (by simpa using he_index)
    | succ e => exact Nat.succ_le_succ (Nat.zero_le e)
  obtain ⟨k, hk_le_a, hX_card⟩ := hX_bound
  have hF_index_dvd_card : F.index ∣ Nat.card X := by
    exact ⟨Nat.card F, F.index_mul_card.symm⟩
  have he_le_k : e ≤ k := by
    have hpow_dvd : p ^ e ∣ p ^ k := by
      rw [← he_index, ← hX_card]
      exact hF_index_dvd_card
    exact (pow_dvd_pow_iff (Fact.out : p.Prime).ne_zero
      (mt Nat.isUnit_iff.mp (Fact.out : p.Prime).ne_one)).mp hpow_dvd
  have he_le_a : e ≤ a := he_le_k.trans hk_le_a
  have hdiff_dvd := prime_dvd_card_sub_card_fixedPoints_of_pgroup_action (X := X) hA
  have hcard_eq : Nat.card X = Nat.card F * p ^ e := by
    calc
      Nat.card X = F.index * Nat.card F := F.index_mul_card.symm
      _ = p ^ e * Nat.card F := by rw [he_index]
      _ = Nat.card F * p ^ e := by rw [mul_comm]
  have hdiff_eq : Nat.card X - Nat.card (MulAction.fixedPoints A X) =
      Nat.card F * (p ^ e - 1) := by
    change Nat.card X - Nat.card F = Nat.card F * (p ^ e - 1)
    rw [hcard_eq]
    simpa [mul_one] using (Nat.mul_sub_left_distrib (Nat.card F) (p ^ e) 1).symm
  have hq_dvd_mul : q ∣ Nat.card F * (p ^ e - 1) := by
    rwa [← hdiff_eq]
  obtain ⟨r, hF_card_pow⟩ := IsPGroup.iff_card.mp (hX.to_subgroup F)
  have hq_coprime_cardF : q.Coprime (Nat.card F) := by
    rw [hF_card_pow]
    exact
      ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr hpq).pow_right r
  have hq_dvd : q ∣ p ^ e - 1 := hq_coprime_cardF.dvd_of_dvd_mul_left hq_dvd_mul
  exact ⟨e, he_pos, he_le_a, hq_dvd⟩

/-- **Isaacs Cor 5.29**: If `|G| = p^a m`, `p ∤ m`, and no prime divisor `q`
of `m` divides any `p^e - 1` with `1 ≤ e ≤ a`, then `G` has a normal
p-complement.

**Proof** (Isaacs p.179): use Frobenius' p-local criterion. If a q-subgroup `Q`
normalizing a p-subgroup `X` acts nontrivially, then the fixed-point subgroup
`C_X(Q)` is proper in `X`; orbit counting gives `q ∣ |X| - |C_X(Q)|`, hence
`q ∣ p^e - 1` for `|X:C_X(Q)| = p^e`, contradiction. -/
theorem hasNormalPComplement_of_no_prime_dvd_pow_sub_one
    [Finite G] {p a m : ℕ} [Fact p.Prime]
    (hcard : Nat.card G = p ^ a * m) (hpm : ¬ p ∣ m)
    (hNo : ∀ {q e : ℕ}, q.Prime → q ∣ m → 1 ≤ e → e ≤ a →
      ¬ q ∣ p ^ e - 1) :
    HasNormalPComplement p G := by
  classical
  refine hasNormalPComplement_of_prime_subgroups_centralize
    (fun {q} _ hq_ne_p {X Q} hXp hQq hQ_le_N => ?_)
  by_contra hQ_not_le_C
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN_def
  let QN : Subgroup N := Q.subgroupOf N
  have hQN_q : IsPGroup q QN := by
    have h_iso : QN ≃* Q := Subgroup.subgroupOfEquivOfLe hQ_le_N
    exact hQq.of_equiv h_iso.symm
  have hfix_ne : MulAction.fixedPoints QN X ≠ Set.univ := by
    intro hfix_univ
    apply hQ_not_le_C
    intro y hyQ
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    let yN : N := ⟨y, by simpa [hN_def] using hQ_le_N hyQ⟩
    let yQN : QN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyQ⟩
    let xX : X := ⟨x, hxX⟩
    have hfixed : yQN • xX = xX := by
      have hx_fixed : xX ∈ MulAction.fixedPoints QN X := by
        rw [hfix_univ]
        exact Set.mem_univ xX
      exact hx_fixed yQN
    have hconj : y * x * y⁻¹ = x := by
      exact congrArg Subtype.val hfixed
    calc x * y = (y * x * y⁻¹) * y := by rw [hconj]
      _ = y * x := by group
  have hQ_ne_bot : Q ≠ ⊥ := by
    intro hQ_bot
    apply hQ_not_le_C
    intro y hyQ
    rw [Subgroup.mem_centralizer_iff]
    intro x _hxX
    have hy_one : y = 1 := by
      rw [hQ_bot, Subgroup.mem_bot] at hyQ
      exact hyQ
    rw [hy_one, one_mul, mul_one]
  have hQ_card_ne_one : Nat.card Q ≠ 1 := by
    intro hcardQ
    exact hQ_ne_bot (Subgroup.card_eq_one.mp hcardQ)
  have hQ_card_gt_one : 1 < Nat.card Q := by
    have hpos : 0 < Nat.card Q := Nat.card_pos
    omega
  haveI : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp hQ_card_gt_one
  obtain ⟨n, hn_pos, hQ_card_eq⟩ := hQq.nontrivial_iff_card.mp inferInstance
  have hq_dvd_Q : q ∣ Nat.card Q := by
    rw [hQ_card_eq]
    exact dvd_pow_self q (ne_of_gt hn_pos)
  have hq_dvd_G : q ∣ Nat.card G := by
    have hQ_dvd_top : Nat.card Q ∣ Nat.card (⊤ : Subgroup G) :=
      Subgroup.card_dvd_of_le (show Q ≤ (⊤ : Subgroup G) from le_top)
    exact hq_dvd_Q.trans (by simpa using hQ_dvd_top)
  have hq_dvd_m : q ∣ m := by
    have hq_dvd_mul : q ∣ p ^ a * m := by
      rwa [← hcard]
    rcases (Fact.out : q.Prime).dvd_mul.mp hq_dvd_mul with hq_dvd_pa | hq_dvd_m
    · have hcop_q_pa : q.Coprime (p ^ a) :=
        ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr
          hq_ne_p).pow_right a
      exact False.elim (((Fact.out : q.Prime).coprime_iff_not_dvd.mp hcop_q_pa) hq_dvd_pa)
    · exact hq_dvd_m
  have hX_bound : ∃ k, k ≤ a ∧ Nat.card X = p ^ k := by
    obtain ⟨k, hkX⟩ := IsPGroup.iff_card.mp hXp
    refine ⟨k, ?_, hkX⟩
    have hX_card_dvd_G : Nat.card X ∣ Nat.card G := by
      have hX_dvd_top : Nat.card X ∣ Nat.card (⊤ : Subgroup G) :=
        Subgroup.card_dvd_of_le (show X ≤ (⊤ : Subgroup G) from le_top)
      simpa using hX_dvd_top
    have hpk_dvd_pa_m : p ^ k ∣ p ^ a * m := by
      rw [← hcard, ← hkX]
      exact hX_card_dvd_G
    have hcop_pk_m : (p ^ k).Coprime m :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpm).pow_left k
    have hpk_dvd_pa : p ^ k ∣ p ^ a :=
      hcop_pk_m.dvd_of_dvd_mul_left (by rwa [mul_comm] at hpk_dvd_pa_m)
    exact (pow_dvd_pow_iff (Fact.out : p.Prime).ne_zero
      (mt Nat.isUnit_iff.mp (Fact.out : p.Prime).ne_one)).mp hpk_dvd_pa
  obtain ⟨e, he_pos, he_le_a, hq_dvd_pe⟩ :=
    exists_prime_dvd_pow_sub_one_of_nontrivial_pgroup_action
      (A := QN) (X := X) hXp hQN_q hq_ne_p hX_bound hfix_ne
  exact (hNo (q := q) (e := e) (Fact.out : q.Prime) hq_dvd_m he_pos he_le_a
    hq_dvd_pe).elim

/-- **Isaacs Cor 5.30** (p odd 中心化): ⭐ **FT 経路で奇数位数仮定との親和性**.
`p` odd, 全 order-`p` 元が `Z(G)` 中心 ⇒ `G` は normal p-complement を持つ.

**証明** (Isaacs p.180): Thm 5.26 で any p-subgroup X に対し N_G(X)/C_G(X) が p-group
を示せばよい. `Q := N_G(X)/C_G(X)` 内の p'-部分 A を取り A が trivial に作用することを
**Ch.4 Thm 4.36** (p>2 + p-群 G + p'-A が order-p 元固定 ⇒ A trivial) で示す. 仮定より
order-p 元は中心で A 不変, 中心で固定 ⇒ Thm 4.36 適用条件成立.

**実装状態**: Ch.4 §4D Thm 4.36 を q-subgroup action に適用して完成. -/
theorem normal_p_complement_of_order_p_central_odd
    [Finite G] {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hCent : ∀ g : G, orderOf g = p → g ∈ Subgroup.center G) :
    HasNormalPComplement p G := by
  classical
  refine hasNormalPComplement_of_prime_subgroups_centralize
    (fun {q} _ hq_ne_p {X Q} hXp hQq hQ_le_N => ?_)
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN_def
  let QN : Subgroup N := Q.subgroupOf N
  have hQN_q : IsPGroup q QN := by
    have h_iso : QN ≃* Q := Subgroup.subgroupOfEquivOfLe hQ_le_N
    exact hQq.of_equiv h_iso.symm
  let φ : QN →* MulAut X := MulDistribMulAction.toMulAut QN X
  have hQN_p' : ¬ p ∣ Nat.card QN := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQN_q
    rw [hn]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp
      (((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr
        hq_ne_p.symm).pow_right n)
  have hfix : ∀ x : X, x ^ p = 1 → ∀ a : QN, (φ a) x = x := by
    intro x hxpow a
    apply Subtype.ext
    have hxpowG : (x : G) ^ p = 1 := by
      exact congrArg Subtype.val hxpow
    have hxord_dvd : orderOf (x : G) ∣ p := orderOf_dvd_of_pow_eq_one hxpowG
    change ((a : QN) • x : X).val = x.val
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hxord_dvd with hxord1 | hxordp
    · have hx_one : (x : G) = 1 := orderOf_eq_one_iff.mp hxord1
      have hx_one_X : x = 1 := Subtype.ext hx_one
      simp [hx_one_X]
    · have hx_cent : (x : G) ∈ Subgroup.center G := hCent x hxordp
      have hcomm : (a : N).val * (x : G) = (x : G) * (a : N).val :=
        Subgroup.mem_center_iff.mp hx_cent (a : N).val
      change (a : N).val * (x : G) * (a : N).val⁻¹ = (x : G)
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hbot : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
    OddOrder.Isaacs.Ch04.isaacs_thm_4_36 hp_odd φ hXp hQN_p' hfix
  have htriv : ∀ a : QN, ∀ x : X, (φ a) x = x :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially φ).mp hbot
  intro y hyQ
  rw [Subgroup.mem_centralizer_iff]
  intro x hxX
  let yN : N := ⟨y, by simpa [hN_def] using hQ_le_N hyQ⟩
  let yQN : QN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyQ⟩
  let xX : X := ⟨x, hxX⟩
  have hfixed : (φ yQN) xX = xX := htriv yQN xX
  have hconj : y * x * y⁻¹ = x := by
    exact congrArg Subtype.val hfixed
  calc x * y = (y * x * y⁻¹) * y := by rw [hconj]
    _ = y * x := by group

end -- 5E

end OddOrder.Isaacs.Ch05
