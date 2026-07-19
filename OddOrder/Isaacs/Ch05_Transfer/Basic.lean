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
import OddOrder.Isaacs.Ch05_Transfer.CentralTransfer

/-!
# Basic

Prefix-split from `OddOrder.Isaacs.Ch05_Transfer.Main` (2000-line limit, issue 0103 第 2 パス).
§5A-5B は `CentralTransfer.lean` へ分割済 (1500 行閾値, issue 1036).
-/

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
| 5C | Hall transfer, Burnside, cyclic / abelian Sylow | 5.11 – 5.19 | ✅ 完備 (Cor 5.19 の書籍一般形 = `SylowTwoDirectFactor.lean`) |
| 5D | Focal subgroup theorem + p-transfer control | 5.20 – 5.24 | ✅ 完備 (5.24 = `NilpotentMaximal.lean`) |
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
* `IsZGroup.coprime_commutator_index` (`ZGroup.lean:280`) = **Thm 5.16 part 3** (|G'|, |G:G'|
coprime).
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
- **Cor 5.19** (Sylow_2 cyclic direct factor ⇒ 非単純): ✅ 書籍一般形は `SylowTwoDirectFactor.lean`. -/

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
    change orderOf (⟨h, hh_inP⟩ : ↥P) = p
    rw [Subgroup.orderOf_mk]; exact hh_ord_g
  have hk_P_ord : orderOf k_P = p := by
    change orderOf (⟨k, hk_inP⟩ : ↥P) = p
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
    change ((@MonoidHom.transfer G _ (P : Subgroup G) (P : Subgroup G)
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
      (Nat.card_congr (Subgroup.equivMapOfInjective K' N.subtype
          Subtype.coe_injective).toEquiv).symm
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

Isaacs 原版は `P = A × B` with `A` cyclic strictly largest で, 本定理はその `B = ⊥` 特殊化.
**一般形は実装済** — `not_isSimpleGroup_of_sylow_two_cyclic_strict_max_factor`
(`OddOrder/Isaacs/Ch05_Transfer/SylowTwoDirectFactor.lean:73`). 本定理はその `B = ⊥` の場合
に相当するが, cyclic Sylow₂ 版として独立に有用なので残してある (一般形からの薄い
再導出ではなく別証明 — `Disjoint A B` や `P` abelian を要さない分, 仮定が素直).

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
        change n * t = (n * t * n⁻¹) * n; group
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

**Thm 5.24** (G simple, H maximal nilpotent ⇒ H は p-group): ✅
`exists_isPGroup_of_isCoatom_of_isNilpotent` (`NilpotentMaximal.lean`, 2026-07-17). -/

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

/-- **Isaacs Cor. 5.22, second conclusion**: `H ⧸ A^p(H) ≃* G ⧸ A^p(G)`.

Isaacs states 5.22 as「`H` controls `p`-transfer, and hence `A^p(H) = H ∩ A^p(G)` **and**
`G/A^p(G) ≅ H/A^p(H)`」.  `APrime_eq_subgroupOf_APrime_of_controlsFusionIn` (above) gives the
first conclusion; this gives the second — the "controls `p`-transfer" content proper.

⚠ The isomorphism is **not** derivable from the first conclusion alone: it additionally needs
`H · A^p(G) = G`, supplied here by coprimality of `|G : P|` with the `p`-power `|G : A^p(G)|`
together with `P ≤ H`.  Given that, the second isomorphism theorem
(`QuotientGroup.quotientInfEquivProdNormalQuotient`) reads
`H ⧸ A^p(G).subgroupOf H ≃* (H ⊔ A^p(G)) ⧸ … `, and `H ⊔ A^p(G) = ⊤` turns the right side into
`G ⧸ A^p(G)`. -/
theorem quotient_aPrime_mulEquiv_of_controlsFusionIn [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {H : Subgroup G}
    (hP_le_H : (P : Subgroup G) ≤ H)
    (hFusion : H.ControlsFusionIn (P : Subgroup G)) :
    Nonempty ((↥H ⧸ APrime p H) ≃* (G ⧸ APrime p G)) := by
  classical
  have hHA_top : H ⊔ APrime p G = ⊤ := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (APrime p G).index = p ^ k := by
      simpa using APrime_index_isPGroup p G
    have hPA_top : (P : Subgroup G) ⊔ APrime p G = ⊤ := by
      have hcop : Nat.Coprime (P : Subgroup G).index (APrime p G).index := by
        rw [hk]
        exact Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out P.not_dvd_index
      exact OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index hcop
    rw [eq_top_iff, ← hPA_top]
    exact sup_le_sup hP_le_H le_rfl
  have hAPH : APrime p H = (APrime p G).subgroupOf H :=
    APrime_eq_subgroupOf_APrime_of_controlsFusionIn P hP_le_H hFusion
  refine ⟨((QuotientGroup.congr (APrime p H) ((APrime p G).subgroupOf H)
      (MulEquiv.refl ↥H) (by simpa using hAPH)).trans
    (QuotientGroup.quotientInfEquivProdNormalQuotient H (APrime p G))).trans ?_⟩
  refine QuotientGroup.congr ((APrime p G).subgroupOf (H ⊔ APrime p G)) (APrime p G)
    ((MulEquiv.subgroupCongr hHA_top).trans Subgroup.topEquiv) ?_
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulEquiv.trans_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hHA_top ▸ Subgroup.mem_top x⟩, hx, rfl⟩

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

end
end OddOrder.Isaacs.Ch05
