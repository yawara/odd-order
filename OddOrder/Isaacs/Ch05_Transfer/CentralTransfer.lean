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

/-!
# Isaacs §5A-5B — Central transfer: Thm 5.3 / Cor 5.4 / Schur / Cor 5.9

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 5 "Transfer",
§5A (pp. 147-153) + §5B (pp. 153-159) の Lean 化。

`Basic.lean` (1657 行) からの prefix-split (1500 行閾値、issue 1036)。
章全体の overview・mathlib 対応表は `Basic.lean` 冒頭を参照。
Thm 5.10 (Dietzmann) は `Dietzmann.lean`。
-/

open scoped commutatorElement
open scoped IsMulCommutative -- rc2: IsMulCommutative→CommGroup/Monoid now scoped

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
    change ((@MonoidHom.transfer G _ (P : Subgroup G) (P : Subgroup G)
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
変換は `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` + `P ∩ Z ≤ Z(P)` 経由で追加可.) -/
theorem not_isMulCommutative_sylow_of_le_commutator_inf_center
    [Finite G] {p : ℕ} [Fact p.Prime] {Z : Subgroup G}
    (hZ : Z ≤ commutator G ⊓ Subgroup.center G)
    (h_p_dvd : p ∣ Nat.card Z) (P : Sylow p G) [P.FiniteIndex] :
    ¬ IsMulCommutative (P : Subgroup G) :=
  not_isMulCommutative_sylow_of_dvd_card_commutator_inf_center P
    (h_p_dvd.trans (Subgroup.card_dvd_of_le hZ))

/-- **Isaacs Cor 5.4** (商版, 書籍の結論そのもの): `Z ≤ Γ' ∩ Z(Γ)`, `p ∣ |Z|` ⇒
`Γ/Z` の Sylow `p`-部分群は**非巡回**.

Schur multiplier 文脈で `G = Γ/Z`, `Z ≤ M(G)` のとき「`p ∣ |M(G)|` ⇒ Sylow_p(G)
noncyclic」を与える形. 証明: `Syl_p(Γ/Z)` が巡回なら, `Γ` の Sylow `P` の像
(共役で一致, `Sylow.mapSurjective`) も巡回. 制限準同型 `↥P →* ↥(P の像)` の核は
`Z ∩ P ≤ Z(P)` (Z 中心的) なので
`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` で `P` 可換となり,
前段 (`not_isMulCommutative_sylow_of_le_commutator_inf_center`) と矛盾. -/
theorem not_isCyclic_sylow_quotient_of_le_commutator_inf_center
    [Finite G] {p : ℕ} [Fact p.Prime] {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ commutator G ⊓ Subgroup.center G)
    (h_p_dvd : p ∣ Nat.card Z) (Q : Sylow p (G ⧸ Z)) :
    ¬ IsCyclic ↥(Q : Subgroup (G ⧸ Z)) := by
  intro hcyc
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  set P' : Sylow p (G ⧸ Z) := P.mapSurjective (QuotientGroup.mk'_surjective Z) with hP'
  -- 巡回性を Q から P' (共役) へ移送.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ Z) P' Q
  haveI hcyc' : IsCyclic ↥(P' : Subgroup (G ⧸ Z)) := by
    have e1 : ↥(P' : Subgroup (G ⧸ Z)) ≃* ↥((g • P' : Sylow p (G ⧸ Z)) : Subgroup (G ⧸ Z)) :=
      Sylow.equivSMul P' g
    have e2 : ↥((g • P' : Sylow p (G ⧸ Z)) : Subgroup (G ⧸ Z)) ≃*
        ↥(Q : Subgroup (G ⧸ Z)) :=
      MulEquiv.subgroupCongr (congrArg _ hg)
    exact isCyclic_of_surjective _ (e1.trans e2).symm.surjective
  -- 制限準同型 ↥P →* ↥(P.map mk') の核 ≤ Z(P) → P 可換.
  haveI hcyc'' : IsCyclic ↥(P.1.map (QuotientGroup.mk' Z)) := hcyc'
  have hcomm : IsMulCommutative ↥(P : Subgroup G) := by
    refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      ((QuotientGroup.mk' Z).subgroupMap (P : Subgroup G)) ?_
    intro x hx
    have hxZ : (x : G) ∈ Z := by
      have h1 : (QuotientGroup.mk' Z).subgroupMap (P : Subgroup G) x = 1 := hx
      have h2 : QuotientGroup.mk' Z (x : G) = 1 := congrArg Subtype.val h1
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h2
    have hxC : (x : G) ∈ Subgroup.center G := (hZ.trans inf_le_right) hxZ
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxC y)
  exact not_isMulCommutative_sylow_of_le_commutator_inf_center hZ h_p_dvd P hcomm

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

end OddOrder.Isaacs.Ch05
