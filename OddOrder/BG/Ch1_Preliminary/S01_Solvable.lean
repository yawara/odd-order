/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow
import OddOrder.Isaacs.Ch03_SplitExtensions
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# BG §1: Elementary Properties of Solvable Groups

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
Chapter I §1 (pp. 1-8), mmd `references/bg/local-analysis.mmd` L310-585, **22 結果** (Lemma/
Proposition/Theorem/Corollary 1.1-1.22).

## 構造 (BG §1 全 22 結果)

§1 を概念別に 7 つの sub-section に整理:

- **§1A** Solvable group basics (Lem 1.1, Prop 1.2-1.4)
- **§1B** A-invariant Hall theory (Prop 1.5, Prop 1.6) — Peterfalvi で多数引用
- **§1C** Frattini + Burnside operator (Lem 1.7, Thm 1.8, Lem 1.9, Prop 1.10)
- **§1D** p-odd action (Thm 1.11, Cor 1.12, Thm 1.13 Thompson critical)
- **§1E** Sylow lift + Hall-Higman + noncyclic auto (Lem 1.14, Prop 1.15, Prop 1.16)
- **§1F** Focal + Burnside + Maschke (Thm 1.17, Thm 1.18, Cor 1.19, Thm 1.20) — **mathlib 直接**
- **§1G** p-length one + p-group normal series (Lem 1.21, Lem 1.22)

## Isaacs FGT / mathlib 対応表

CLAUDE.md no-mathlib-wrapper policy 準拠: mathlib 直接対応がある §1F の 4 結果は
**section docstring 記載のみで個別 theorem を書かない**.

| BG | Isaacs FGT | mathlib | 本ファイル |
|---|---|---|---|
| Thm 1.8 | Thm 1.8 | (Ch.1 §1B TODO) | Phase 1 待ち |
| Thm 1.11 | Thm 4.36 | Phase 1 Ch.4 §4D | Phase 1 待ち |
| Thm 1.13 | (Thompson critical) | (Phase 1 未) | Phase 1 待ち |
| **Lem 1.14** main | — | Sylow II in T·M + `Subgroup.conj_smul_subgroupOf` + `subgroupOf_inj` | ✅ **sorry-free 完成** |
| **Lem 1.14** 易方向 | — | `Subgroup.normalizer_le_normalizer_sup_normal` + `le_normalizer` | ✅ **sorry-free 5 行** |
| **Prop 1.15(a)** | Thm 3.21 | `hall_higman_1_2_3` ✅ | ✅ **sorry-free thin wrap** (π = {p} 特殊化) |
| Thm 1.17 | Thm 5.21 | `commutator_inf_eq_focalSubgroup` ✅ | no-wrapper, docstring 参照 |
| Thm 1.18 | Thm 5.13 | `ker_transferSylow_isComplement'` ✅ | no-wrapper |
| Cor 1.19(b) | — | `IsZGroup.coprime_commutator_index` ✅ | no-wrapper, audit 発見 |
| Thm 1.20 | — | `Maschke` ✅ | no-wrapper |
| **Lem 1.22** | (Ch.1 系) | `IsPGroup.normal_inf_center_nontrivial` + Cauchy + 帰納 | ✅ **proof 完成** |

## Audit context

Phase 2a 第 1 波 audit (2026-05-23) で §1 を 4 視点で再調査済.
詳細: `notes/bg/s01_solvable.md` + `notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`.

主要 audit 発見 (§1 関連):
- Lem 1.1 "43+ 回引用" → 実測 0 in §2+
- Prop 1.2 "22 回引用" → 実測 6
- Thm 1.13 ↔ Isaacs 4.31 同一視 → 別物 (Thompson critical ≠ P×Q)
- Cor 1.19(b) → mathlib `IsZGroup.coprime_commutator_index` 直接ヒット
- 内部 hub は **Prop 1.5(d)** (6 §1 proofs)

## 実装 status (2026-05-24) — §1E 全 sorry-free 完成 ⭐

- **Skeleton** + **§1F docstring mapping** + **9 結果 全 sorry-free**:
  - **Lem 1.22** `normal_subgroup_card_pow_le_of_pGroup` ⭐ sorry-free 完成
  - **Lem 1.14 main** `normalizer_sup_eq_normalizer_sup_of_pGroup_coprime` ⭐ **sorry-free 完成**
  - **Lem 1.14 易方向** `le_normalizer_sup_of_normal` ⭐ sorry-free
  - **Prop 1.15(a)** `hall_higman_solvable_specialization` ⭐ sorry-free thin wrap
  - **`card_comap_eq_card_mul_card_ker`** helper sorry-free
  - **`inf_eq_bot_of_pGroup_coprime`** (Step 1) ⭐ sorry-free
  - **`card_sup_eq_card_mul_card_of_disjoint_normal`** (Step 2) ⭐ sorry-free
  - **`subgroupOf_sup_card_eq_and_pGroup`** (Step 3 part 1) ⭐ sorry-free
  - **`subgroupOf_sup_eq_of_pGroup_le_of_coprime`** (Step 3 part 2) ⭐ sorry-free
- Lem 1.14 hard direction proof (~115 LOC inline): TSyl + T_xSyl 構築 + `MulAction.exists_smul_eq`
  (Sylow II in ↥(T ⊔ M)) + `Subgroup.conj_smul_subgroupOf` + `subgroupOf_inj` + `inf_of_le_left`
  で `MulAut.conj y.val • T = T_x` を G で取得 + `mem_sup_of_normal_left` で `y.val = m·t'` 分解
  + `t' ∈ T` で `t' · T · t'⁻¹ = T` + `m⁻¹·x ∈ N_G(T)` で集約.
- Phase 1 完成度: Ch.1 ✅ / Ch.3 ✅ (Hall + Hall-Higman 3.21) / Ch.4 §4D 進行中 / Ch.7 §7A/§7C 着手 / Ch.5/6 進行中.
-/

namespace OddOrder.BG.Ch1.S01

open OddOrder.Isaacs.Ch01
open Pointwise

/-! ## §1A-§1B: 未実装 (Phase 1 + shared module 待ち) -/

/-! ## §1C: Frattini + Burnside operator (Lem 1.7-1.10) -/

/-- **BG Lemma 1.7(a)** (Frattini argument, finite specialization):
有限群 `G` で `H ≤ G` かつ `H ⊔ Φ(G) = ⊤` ⇒ `H = ⊤`.

mathlib `frattini_nongenerating` の有限群特殊化. `[Finite G]` から
`Finite (Subgroup G)` → `WellFoundedGT (Subgroup G)` → `IsStronglyCoatomic` →
`IsCoatomic` の instance chain で `frattini_nongenerating` に渡せる.

BG 原 statement は R p-group の文脈だが proof は finite group で成立. -/
theorem eq_top_of_sup_frattini_eq_top {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (h : H ⊔ frattini G = ⊤) : H = ⊤ :=
  frattini_nongenerating h

/-! ## §1D: 未実装 (Phase 1 Ch.4 §4D 待ち) -/

/-! ## §1E: Sylow lift + Hall-Higman + noncyclic auto -/

/-! ### Lem 1.14 helpers (Step 1-3 sorry-free, main statement 下方) -/

/-- **Helper for Lem 1.14**: T p-group + M p'-group ⇒ `T ⊓ M = ⊥`.

`T ⊓ M` は T の subgroup として p-group (`hT.of_injective Subgroup.inclusion`) かつ
|T ⊓ M| ∣ |M|. |M| が p と coprime ⇒ p^k ∣ |M| ⇒ k = 0 ⇒ |T ⊓ M| = 1 ⇒ T ⊓ M = ⊥. -/
theorem inf_eq_bot_of_pGroup_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} (hM_p' : (Nat.card M).Coprime p) :
    T ⊓ M = ⊥ := by
  have hTM_le_T : T ⊓ M ≤ T := inf_le_left
  have hTM_le_M : T ⊓ M ≤ M := inf_le_right
  have hTM_pgroup : IsPGroup p (T ⊓ M : Subgroup G) :=
    hT.of_injective (Subgroup.inclusion hTM_le_T) (Subgroup.inclusion_injective hTM_le_T)
  have hcard_dvd : Nat.card (T ⊓ M : Subgroup G) ∣ Nat.card M :=
    Subgroup.card_dvd_of_le hTM_le_M
  obtain ⟨k, hk⟩ := hTM_pgroup.exists_card_eq
  rw [hk] at hcard_dvd
  -- p^k ∣ |M| and (|M|, p) = 1 ⇒ p^k = 1
  have hcop_pow : ((p ^ k).Coprime (Nat.card M)) := (hM_p'.symm).pow_left k
  have hpow_eq_one : p ^ k = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_pow dvd_rfl hcard_dvd
  rw [hpow_eq_one] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

/-- **Helper for Lem 1.14** (Step 2, cardinality): `T ⊓ M = ⊥` + `M ⊴ G` ⇒
`|T ⊔ M| = |T| · |M|`. mathlib 第二同型 `quotientInfEquivProdNormalQuotient` +
`subgroupOfEquivOfLe` + `card_eq_card_quotient_mul_card_subgroup`. -/
theorem card_sup_eq_card_mul_card_of_disjoint_normal
    {G : Type*} [Group G] [Finite G]
    {T M : Subgroup G} [M.Normal] (h_disj : T ⊓ M = ⊥) :
    Nat.card (T ⊔ M : Subgroup G) = Nat.card T * Nat.card M := by
  -- Step A: M.subgroupOf T = ⊥ (from T ⊓ M = ⊥)
  have hMT_bot : M.subgroupOf T = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def]
    intro x hxM hxT
    have hx_inf : x ∈ T ⊓ M := Subgroup.mem_inf.mpr ⟨hxT, hxM⟩
    rwa [h_disj, Subgroup.mem_bot] at hx_inf
  -- |M.subgroupOf T| = 1
  have hMT_card_one : Nat.card (M.subgroupOf T) = 1 := by
    rw [hMT_bot]; exact Subgroup.card_bot
  -- |T| = |T ⧸ M.subgroupOf T| * |M.subgroupOf T| = |T ⧸ M.subgroupOf T|
  have hT_quot_card : Nat.card T = Nat.card (T ⧸ M.subgroupOf T) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf T)
    rw [hMT_card_one, mul_one] at this
    exact this
  -- Second iso theorem: T ⧸ M.subgroupOf T ≃* (T ⊔ M) ⧸ M.subgroupOf (T ⊔ M)
  have h_iso := QuotientGroup.quotientInfEquivProdNormalQuotient T M
  have h_eq_TM : Nat.card ((T ⊔ M : Subgroup G) ⧸ (M.subgroupOf (T ⊔ M))) = Nat.card T := by
    rw [hT_quot_card]
    exact (Nat.card_congr h_iso.toEquiv).symm
  -- |M.subgroupOf (T ⊔ M)| = |M|
  have hM_sub_TM_card : Nat.card (M.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : M ≤ T ⊔ M)).toEquiv
  -- |T ⊔ M| = |quotient| · |M.subgroupOf (T ⊔ M)| = |T| · |M|
  have h_card : Nat.card ↥(T ⊔ M : Subgroup G) =
      Nat.card ((T ⊔ M : Subgroup G) ⧸ (M.subgroupOf (T ⊔ M))) *
      Nat.card (M.subgroupOf (T ⊔ M : Subgroup G)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h_card, h_eq_TM, hM_sub_TM_card]

/-- **Helper for Lem 1.14** (Step 3 part 1): `T.subgroupOf (T ⊔ M)` is a p-group with
cardinality `|T|`. uses `Subgroup.subgroupOfEquivOfLe` (T ≤ T ⊔ M ⇒ T.subgroupOf (T⊔M) ≃* T). -/
theorem subgroupOf_sup_card_eq_and_pGroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T) (M : Subgroup G) :
    Nat.card (T.subgroupOf (T ⊔ M)) = Nat.card T ∧
      IsPGroup p (T.subgroupOf (T ⊔ M : Subgroup G)) := by
  refine ⟨?_, ?_⟩
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ M)).toEquiv
  · exact hT.of_injective (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ M)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ M)).injective

/-- **Helper for Lem 1.14** (Step 3 part 2 一般版, Sylow 性): 任意の `S ≤ T ⊔ M` で
`|S| = |T|` ⇒ `S.subgroupOf (T ⊔ M)` は ↥(T ⊔ M) の Sylow p (Q ≥ S.subgroupOf + Q p-group
⇒ Q = S.subgroupOf).

`S = T` の場合 `subgroupOf_sup_eq_of_pGroup_le_of_coprime` (corollary 下記),
`S = xTx⁻¹` (T_x) の場合 Lem 1.14 main proof 内の T_xSyl 構築で使用.

証明: |Q| = p^j ∣ |T ⊔ M| = |T| · |M| with (|M|, p) = 1 ⇒ p^j ∣ p^k = |T|.
`S.subgroupOf ≤ Q` + `|S.subgroupOf| = |S| = |T| = p^k` ⇒ k ≤ j. 両方合わせて j = k,
|Q| = |S.subgroupOf|. `Subgroup.eq_of_le_of_card_ge` で等号. -/
theorem subgroupOf_sup_eq_of_pGroup_le_of_card_eq
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [_hM_norm : M.Normal] (hM_p' : (Nat.card M).Coprime p)
    {S : Subgroup G} (hS_le : S ≤ T ⊔ M) (hS_card : Nat.card S = Nat.card T)
    {Q : Subgroup ↥(T ⊔ M : Subgroup G)} (hQ_pgroup : IsPGroup p Q)
    (hS_sub_Q : S.subgroupOf (T ⊔ M) ≤ Q) :
    Q = S.subgroupOf (T ⊔ M) := by
  have hS_sub_card : Nat.card (S.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le).toEquiv, hS_card]
  have h_disj : T ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hT hM_p'
  have h_card_sup : Nat.card (T ⊔ M : Subgroup G) = Nat.card T * Nat.card M :=
    card_sup_eq_card_mul_card_of_disjoint_normal h_disj
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  obtain ⟨j, hj⟩ := hQ_pgroup.exists_card_eq
  have hQ_dvd : Nat.card Q ∣ Nat.card ↥(T ⊔ M : Subgroup G) :=
    Subgroup.card_subgroup_dvd_card Q
  rw [h_card_sup, hk, hj] at hQ_dvd
  have hp_cop : (p ^ j).Coprime (Nat.card M) := (hM_p'.symm).pow_left j
  have hpj_dvd_pk : p ^ j ∣ p ^ k := Nat.Coprime.dvd_of_dvd_mul_right hp_cop hQ_dvd
  have hcard_le : Nat.card (S.subgroupOf (T ⊔ M : Subgroup G)) ≤ Nat.card Q :=
    Subgroup.card_le_of_le hS_sub_Q
  rw [hS_sub_card, hk, hj] at hcard_le
  have hk_le_j : k ≤ j := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard_le
  have hj_le_k : j ≤ k :=
    (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hpj_dvd_pk
  have hjk : j = k := le_antisymm hj_le_k hk_le_j
  symm
  apply Subgroup.eq_of_le_of_card_ge hS_sub_Q
  rw [hS_sub_card, hk, hj, hjk]

/-- **Helper for Lem 1.14** (Step 3 part 2, Sylow 性, S = T 特殊化):
T p-group + M ⊴ G p'-subgroup ⇒ `T.subgroupOf (T ⊔ M)` は ↥(T ⊔ M) の Sylow p.
一般版 `subgroupOf_sup_eq_of_pGroup_le_of_card_eq` (S = T の場合) の corollary. -/
theorem subgroupOf_sup_eq_of_pGroup_le_of_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [_hM_norm : M.Normal] (hM_p' : (Nat.card M).Coprime p)
    {Q : Subgroup ↥(T ⊔ M : Subgroup G)} (hQ_pgroup : IsPGroup p Q)
    (hT_sub_Q : T.subgroupOf (T ⊔ M) ≤ Q) :
    Q = T.subgroupOf (T ⊔ M) :=
  subgroupOf_sup_eq_of_pGroup_le_of_card_eq hT hM_p' le_sup_left rfl hQ_pgroup hT_sub_Q

/-- **BG Lemma 1.14 (易 direction, sorry-free)**: `N_G(T)·M ≤ N_G(T·M)`.

- `T.normalizer ≤ (T ⊔ M).normalizer`: x normalizes T ⇒ x normalizes M (M ⊴ G) ⇒ x
  normalizes T ⊔ M.
- `M ≤ (T ⊔ M).normalizer`: M ≤ T ⊔ M and subgroup self-normalizes via inner conjugation. -/
theorem le_normalizer_sup_of_normal
    {G : Type*} [Group G] (T : Subgroup G) (M : Subgroup G) [M.Normal] :
    Subgroup.normalizer T ⊔ M ≤ Subgroup.normalizer (T ⊔ M : Subgroup G) :=
  sup_le Subgroup.normalizer_le_normalizer_sup_normal
    (le_sup_right.trans Subgroup.le_normalizer)

/-- **BG Lemma 1.14 (heart, normalizer-in-G form)**: `T` p-subgroup of `G`, `M ⊴ G` p'-subgroup
(`gcd(|M|, p) = 1` を採用) ⇒ `N_G(T·M) = N_G(T)·M`.

In quotient form: with `f = QuotientGroup.mk' M`,
- `(N_{G/M}(T·M/M)).comap f = N_G(T·M)` (mathlib `comap_normalizer_eq_of_surjective`)
- `N_G(T·M) = N_G(T)·M` (this lemma)

**Proof** (BG p.5, 主要部 = hard direction):
- 易: `M ≤ T·M ≤ N_G(T·M)` (subgroup self-normalization) + `N_G(T) ≤ N_G(T·M)` (M normal
  ⇒ conjugation fixes M, T conjugation fixes T, so T·M fixed).
- 難: `x ∈ N_G(T·M)` ⇒ `xTx⁻¹ ⊆ T·M`. `T ∩ M = ⊥` (coprime orders) ⇒ `|T·M| = |T|·|M|`,
  `|T|` は `|T·M|` の p-part ⇒ `T` Sylow `p` of `T·M`. 同様に `xTx⁻¹` Sylow `p` of `T·M`.
  Sylow II in T·M: `∃ y ∈ T·M, xTx⁻¹ = yTy⁻¹`. `y = m·t` (`m ∈ M`, `t ∈ T`, possible
  since `M·T = T·M` for M normal) ⇒ `xTx⁻¹ = m·T·m⁻¹` ⇒ `m⁻¹x ∈ N_G(T)` ⇒
  `x ∈ M·N_G(T) = N_G(T)·M`.

**実装状態**: ⭐ **sorry-free 完成** (2026-05-24). TSyl + T_xSyl 構築 + Sylow II
(`MulAction.exists_smul_eq`) + `Subgroup.conj_smul_subgroupOf` + `subgroupOf_inj` で
`MulAut.conj y.val • T = T_x` を G で取得. `mem_sup_of_normal_left` で `y.val = m·t'`
分解 + `t' ∈ T ⇒ t'·T·t'⁻¹ = T` + `m⁻¹·x ∈ N_G(T)` で集約. ~115 LOC inline. -/
theorem normalizer_sup_eq_normalizer_sup_of_pGroup_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [hM_norm : M.Normal] (hM_p' : (Nat.card M).Coprime p) :
    Subgroup.normalizer (T ⊔ M : Subgroup G) = Subgroup.normalizer T ⊔ M := by
  apply le_antisymm _ (le_normalizer_sup_of_normal T M)
  intro x hx
  -- === Step 0: setup ===
  have h_disj : T ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hT hM_p'
  have h_card_sup : Nat.card (T ⊔ M : Subgroup G) = Nat.card T * Nat.card M :=
    card_sup_eq_card_mul_card_of_disjoint_normal h_disj
  have hT_le_TM : T ≤ (T ⊔ M : Subgroup G) := le_sup_left
  have hM_le_TM : M ≤ (T ⊔ M : Subgroup G) := le_sup_right
  have hx_norm : ∀ s, s ∈ (T ⊔ M : Subgroup G) ↔ x * s * x⁻¹ ∈ T ⊔ M :=
    Subgroup.mem_normalizer_iff.mp hx
  -- === Step 1: TSyl construction ===
  let TSyl : Sylow p ↥(T ⊔ M : Subgroup G) :=
    ⟨T.subgroupOf (T ⊔ M),
     (subgroupOf_sup_card_eq_and_pGroup hT M).2,
     fun {Q} hQ hle => subgroupOf_sup_eq_of_pGroup_le_of_coprime hT hM_p' hQ hle⟩
  -- === Step 2: T_x = x · T · x⁻¹ properties ===
  let T_x : Subgroup G := T.map (MulAut.conj x).toMonoidHom
  have hT_x_pg : IsPGroup p T_x :=
    hT.of_equiv (Subgroup.equivMapOfInjective T _ (MulAut.conj x).injective)
  have hT_x_card : Nat.card T_x = Nat.card T :=
    (Nat.card_congr (Subgroup.equivMapOfInjective T _ (MulAut.conj x).injective).toEquiv).symm
  have hT_x_le : T_x ≤ (T ⊔ M : Subgroup G) := by
    rintro a ⟨t, ht, hta⟩
    rw [← hta]
    change x * t * x⁻¹ ∈ T ⊔ M
    exact (hx_norm t).mp (hT_le_TM ht)
  have hT_x_sub_pg : IsPGroup p (T_x.subgroupOf (T ⊔ M : Subgroup G)) :=
    hT_x_pg.of_injective (Subgroup.subgroupOfEquivOfLe hT_x_le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hT_x_le).injective
  have hT_x_sub_card : Nat.card (T_x.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_x_le).toEquiv, hT_x_card]
  -- === Step 3: T_xSyl construction (一般 helper 使用) ===
  let T_xSyl : Sylow p ↥(T ⊔ M : Subgroup G) :=
    ⟨T_x.subgroupOf (T ⊔ M),
     hT_x_sub_pg,
     fun {Q} hQ_pg hT_x_sub_Q =>
       subgroupOf_sup_eq_of_pGroup_le_of_card_eq hT hM_p' hT_x_le hT_x_card hQ_pg hT_x_sub_Q⟩
  -- === Step 4: Sylow II — ∃ y : ↥(T ⊔ M), y • TSyl = T_xSyl ===
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (↥(T ⊔ M : Subgroup G)) TSyl T_xSyl
  -- === Step 5: extract y.val · T · y.val⁻¹ = T_x as subgroups of G ===
  have hy_carrier : (y • TSyl).toSubgroup = T_xSyl.toSubgroup := congrArg Sylow.toSubgroup hy
  have h_conj_T_eq_Tx : MulAut.conj (y : G) • T = T_x := by
    have h1 : (y • TSyl).toSubgroup = MulAut.conj y • T.subgroupOf (T ⊔ M) := rfl
    have h2 : T_xSyl.toSubgroup = T_x.subgroupOf (T ⊔ M : Subgroup G) := rfl
    have h3 : MulAut.conj y • T.subgroupOf (T ⊔ M : Subgroup G) =
        (MulAut.conj (y : G) • T).subgroupOf (T ⊔ M : Subgroup G) :=
      Subgroup.conj_smul_subgroupOf hT_le_TM y
    rw [h1, h2, h3] at hy_carrier
    -- hy_carrier : (MulAut.conj y.val • T).subgroupOf (T ⊔ M) = T_x.subgroupOf (T ⊔ M)
    have h_smul_T_le : MulAut.conj (y : G) • T ≤ (T ⊔ M : Subgroup G) := by
      rintro - ⟨t, ht, rfl⟩
      change (y : G) * t * (y : G)⁻¹ ∈ T ⊔ M
      exact (T ⊔ M).mul_mem ((T ⊔ M).mul_mem y.2 (hT_le_TM ht)) ((T ⊔ M).inv_mem y.2)
    rw [Subgroup.subgroupOf_inj] at hy_carrier
    rwa [inf_of_le_left h_smul_T_le, inf_of_le_left hT_x_le] at hy_carrier
  -- === Step 6: decompose y.val = m · t' (m ∈ M, t' ∈ T) ===
  have hy_in_MT : (y : G) ∈ (M ⊔ T : Subgroup G) := by
    rw [sup_comm]; exact y.2
  obtain ⟨m, hm_M, t', ht'_T, hmt⟩ := Subgroup.mem_sup_of_normal_left.mp hy_in_MT
  -- hmt : m * t' = y.val
  -- === Step 7: m · T · m⁻¹ = T_x (since t' normalizes T) ===
  have h_t'_norm_T : MulAut.conj t' • T = T := by
    ext s
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hu, rfl⟩
      change t' * u * t'⁻¹ ∈ T
      exact T.mul_mem (T.mul_mem ht'_T hu) (T.inv_mem ht'_T)
    · intro hs
      refine ⟨t'⁻¹ * s * t', T.mul_mem (T.mul_mem (T.inv_mem ht'_T) hs) ht'_T, ?_⟩
      change t' * (t'⁻¹ * s * t') * t'⁻¹ = s
      group
  have h_conj_y_eq_conj_m : MulAut.conj (y : G) • T = MulAut.conj m • T := by
    rw [← hmt, map_mul, mul_smul, h_t'_norm_T]
  have h_mT_eq_Tx : MulAut.conj m • T = T_x := h_conj_y_eq_conj_m.symm.trans h_conj_T_eq_Tx
  -- === Step 8: m⁻¹ * x ∈ N_G(T) ===
  have h_mx_in_NT : m⁻¹ * x ∈ Subgroup.normalizer T := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨?_, ?_⟩
    · -- Forward: t ∈ T ⇒ (m⁻¹x)t(m⁻¹x)⁻¹ ∈ T
      intro ht
      -- x·t·x⁻¹ ∈ T_x (definition unfolding)
      have hxtx_in_Tx : x * t * x⁻¹ ∈ T_x := ⟨t, ht, by simp [MulAut.conj_apply]⟩
      rw [← h_mT_eq_Tx] at hxtx_in_Tx
      -- Get s ∈ T with m * s * m⁻¹ = x * t * x⁻¹
      obtain ⟨s, hs, hms⟩ := hxtx_in_Tx
      have hms_eq : m * s * m⁻¹ = x * t * x⁻¹ := by
        rw [← MulAut.conj_apply m s]; exact hms
      -- (m⁻¹x) · t · (m⁻¹x)⁻¹ = m⁻¹ · (x*t*x⁻¹) · m = m⁻¹ · (m*s*m⁻¹) · m = s
      have h_eq : m⁻¹ * x * t * (m⁻¹ * x)⁻¹ = s := by
        have step : m⁻¹ * (x * t * x⁻¹) * m = s := by rw [← hms_eq]; group
        calc m⁻¹ * x * t * (m⁻¹ * x)⁻¹
            = m⁻¹ * (x * t * x⁻¹) * m := by group
          _ = s := step
      rw [h_eq]; exact hs
    · -- Reverse: (m⁻¹x)t(m⁻¹x)⁻¹ ∈ T ⇒ t ∈ T
      intro hut
      set u := m⁻¹ * x * t * (m⁻¹ * x)⁻¹ with hu_def
      -- u ∈ T, and m·u·m⁻¹ = x·t·x⁻¹
      have hmum_eq_xtx : m * u * m⁻¹ = x * t * x⁻¹ := by rw [hu_def]; group
      -- m·u·m⁻¹ ∈ MulAut.conj m • T = T_x
      have hmum_in_mT : m * u * m⁻¹ ∈ MulAut.conj m • T :=
        ⟨u, hut, by simp [MulAut.conj_apply]⟩
      rw [h_mT_eq_Tx, hmum_eq_xtx] at hmum_in_mT
      -- hmum_in_mT : x * t * x⁻¹ ∈ T_x
      obtain ⟨s, hs, hxs⟩ := hmum_in_mT
      have hxs_eq : x * s * x⁻¹ = x * t * x⁻¹ := by
        rw [← MulAut.conj_apply x s]; exact hxs
      have h_st : s = t := mul_left_cancel (mul_right_cancel hxs_eq)
      rw [← h_st]; exact hs
  -- === Step 9: x = m · (m⁻¹ * x) ∈ M · N_G(T) ⊆ N_G(T) ⊔ M ===
  have h_x_eq : x = m * (m⁻¹ * x) := by group
  rw [h_x_eq]
  have h_in_M_NT : m * (m⁻¹ * x) ∈ (M : Subgroup G) ⊔ Subgroup.normalizer T :=
    Subgroup.mul_mem_sup hm_M h_mx_in_NT
  rwa [sup_comm] at h_in_M_NT

/-- **BG Proposition 1.15(a) (P. Hall & G. Higman "Lemma 1.2.3", thin wrap)**: `G` 有限可解 +
`O_{p'}(G) = ⊥` ⇒ `C_G(O_p(G)) ⊆ O_p(G)`.

**形式化**: Phase 1 `OddOrder.Isaacs.Ch03.hall_higman_1_2_3` の π = {p} 特殊化.
`IsPiSeparable {p} G` は `IsSolvable G` から `isPiSeparable_of_solvable` で取得.

**BG 原 statement (`T` Sylow p of `O_{p',p}(G)` ⇒ `C_G(T) ⊆ O_{p',p}(G)`) との関係**:
G を G/O_{p'}(G) に置き換えると `T` は `O_p(G/O_{p'}(G))` に一致 (Sylow p of p-group は
全体). この特殊形が下の statement.

CLAUDE.md no-wrapper policy 例外 (仮定特殊化: `IsSolvable G` instance + π = {p}
specialization, `IsPiSeparable` hypothesis を取り除く). -/
theorem hall_higman_solvable_specialization
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [IsSolvable G]
    (hp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G : Set G) ≤
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
  OddOrder.Isaacs.Ch03.hall_higman_1_2_3 ({p} : Set ℕ)
    (OddOrder.Isaacs.Ch03.isPiSeparable_of_solvable ({p} : Set ℕ)) hp'

/-! ## §1F: Focal + Burnside + Maschke (Thm 1.17-1.20) — mathlib 直接, no-wrapper

CLAUDE.md no-mathlib-wrapper policy により 4 結果とも個別 theorem は書かない.

- **BG Thm 1.17** (Focal Subgroup): mathlib `Subgroup.commutator_inf_eq_focalSubgroup`.
  Phase 1 wrapper: `OddOrder.Isaacs.Ch05.abelian_sylow_commutator_inf_eq_focal`.
- **BG Thm 1.18** (Burnside p-complement): mathlib `MonoidHom.ker_transferSylow_isComplement'`
  (`Mathlib/GroupTheory/Transfer.lean:275`).
- **BG Cor 1.19(b)** (Z-group ⇒ G' Hall): mathlib `IsZGroup.coprime_commutator_index`
  (`Mathlib/GroupTheory/SpecificGroups/ZGroup.lean:280`).
- **BG Thm 1.20** (Maschke): mathlib `Mathlib/RepresentationTheory/Maschke.lean`. -/

/-! ## §1G: p-length one + p-group normal series (Lem 1.21, Lem 1.22)

- **Lem 1.21** (p-length one の 5 性質): BG-unique def, 別ファイル `PLength.lean` (将来).
- **Lem 1.22** (p-group normal series): 本ファイル下記.

### Lem 1.22 implementation -/

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Helper: for a surjective group hom `f : G →* H`, the cardinality of the preimage of a
subgroup `K ≤ H` equals `|K| * |ker f|`. Used in Lem 1.22 induction step. -/
private lemma card_comap_eq_card_mul_card_ker
    {G' H : Type*} [Group G'] [Group H] [Finite G'] [Finite H]
    (f : G' →* H) (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  have h1 : (K.comap f).index = K.index := K.index_comap_of_surjective hf
  have h2 : (K.comap f).index * Nat.card (K.comap f) = Nat.card G' :=
    (K.comap f).index_mul_card
  have h3 : K.index * Nat.card K = Nat.card H := K.index_mul_card
  have h4 : Nat.card G' = Nat.card H * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
    exact congrArg (· * _)
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv)
  have hidx_ne : K.index ≠ 0 := by
    rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'
  have hstep : K.index * Nat.card (K.comap f) = K.index * (Nat.card K * Nat.card f.ker) := by
    calc K.index * Nat.card (K.comap f)
        = (K.comap f).index * Nat.card (K.comap f) := by rw [h1]
      _ = Nat.card G' := h2
      _ = Nat.card H * Nat.card f.ker := h4
      _ = (K.index * Nat.card K) * Nat.card f.ker := by rw [h3]
      _ = K.index * (Nat.card K * Nat.card f.ker) := mul_assoc _ _ _
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hidx_ne) hstep

/-- **BG Lemma 1.22**: in a finite `p`-group `G`, every normal subgroup `N` contains, for each
`r` with `p^r ∣ |N|`, a normal subgroup of `G` of order `p^r`.

**Proof** (BG p.8): induction on `r`.
- Base `r = 0`: `L = ⊥`.
- Step `r → r+1`: by IH get `L₀ ⊴ G`, `L₀ ≤ N`, `|L₀| = p^r`. Work in quotient
  `G ⧸ L₀` (which is `p`-group by `IsPGroup.to_quotient`). The image `N' = N.map (mk' L₀)`
  is normal, nontrivial since `p ∣ |N'| = |N|/p^r` (by `card_comap_eq_card_mul_card_ker`).
  By Phase 1 `IsPGroup.normal_inf_center_nontrivial`, `N' ⊓ Z(G ⧸ L₀)` is nontrivial. By
  Cauchy, take `x ∈ N' ⊓ Z(G ⧸ L₀)` of order `p`. Then `⟨x⟩` is central (hence normal in
  `G ⧸ L₀`). The preimage `L = ⟨x⟩.comap (mk' L₀)` satisfies `L ⊴ G`, `L ≤ N` (since
  `(N.map f).comap f = N ⊔ ker f = N`), `|L| = p · p^r = p^(r+1)` (helper).

proof 実装は次 commit (技術的詳細: `orderOf_subtype_coe`, `Subgroup.zpowers` 中央化, など
mathlib API の精査要). -/
theorem normal_subgroup_card_pow_le_of_pGroup
    (hG : IsPGroup p G) {N : Subgroup G} [hN : N.Normal] {r : ℕ}
    (hr_dvd : p ^ r ∣ Nat.card N) :
    ∃ L : Subgroup G, L.Normal ∧ L ≤ N ∧ Nat.card L = p ^ r := by
  classical
  induction r with
  | zero =>
    exact ⟨⊥, Subgroup.normal_bot, bot_le, by rw [Subgroup.card_bot, pow_zero]⟩
  | succ r ih =>
    obtain ⟨L₀, hL₀_norm, hL₀_le_N, hL₀_card⟩ :=
      ih (dvd_trans (pow_dvd_pow p (Nat.le_succ _)) hr_dvd)
    haveI : L₀.Normal := hL₀_norm
    let f : G →* G ⧸ L₀ := QuotientGroup.mk' L₀
    have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective _
    have hf_ker : f.ker = L₀ := QuotientGroup.ker_mk' L₀
    let N' : Subgroup (G ⧸ L₀) := N.map f
    haveI hN'_normal : N'.Normal := hN.map f hf_surj
    have hG'_pgroup : IsPGroup p (G ⧸ L₀) := hG.to_quotient L₀
    have hN'_comap : (N.map f).comap f = N := by
      rw [Subgroup.comap_map_eq, hf_ker, sup_eq_left]; exact hL₀_le_N
    have hN_card_eq : Nat.card N = Nat.card N' * Nat.card L₀ := by
      have h := card_comap_eq_card_mul_card_ker f hf_surj N'
      rwa [hN'_comap, hf_ker] at h
    have hpr_pos : 0 < p ^ r := Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero)
    have hp_dvd_N' : p ∣ Nat.card N' := by
      have h1 : p ^ (r + 1) ∣ Nat.card N' * p ^ r := by
        rw [← hL₀_card, ← hN_card_eq]; exact hr_dvd
      have h2 : p * p ^ r ∣ Nat.card N' * p ^ r := by
        rw [show p * p ^ r = p ^ (r + 1) by ring]; exact h1
      exact Nat.dvd_of_mul_dvd_mul_right hpr_pos h2
    have hN'_card_gt : 1 < Nat.card N' :=
      lt_of_lt_of_le hp.out.one_lt (Nat.le_of_dvd Nat.card_pos hp_dvd_N')
    haveI hN'_nontrivial : Nontrivial N' :=
      Finite.one_lt_card_iff_nontrivial.mp hN'_card_gt
    have hinter_nontrivial :
        Nontrivial ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hG'_pgroup hN'_nontrivial
    have hinter_card_gt : 1 < Nat.card ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) :=
      Finite.one_lt_card_iff_nontrivial.mpr hinter_nontrivial
    have hinter_pgroup : IsPGroup p ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) :=
      hG'_pgroup.to_subgroup _
    have hp_dvd_inter : p ∣ Nat.card ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hinter_pgroup
      rw [hn] at hinter_card_gt ⊢
      have : 0 < n := by
        rcases n with _ | n
        · simp at hinter_card_gt
        · exact Nat.succ_pos _
      exact dvd_pow_self p this.ne'
    haveI : Fintype ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) := Fintype.ofFinite _
    have hp_dvd_fintype :
        p ∣ Fintype.card ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) := by
      rwa [← Nat.card_eq_fintype_card]
    obtain ⟨⟨xc, hxc_mem⟩, hxc_order⟩ := exists_prime_orderOf_dvd_card p hp_dvd_fintype
    set x : G ⧸ L₀ := xc with hx_def
    have hx_in_N' : x ∈ N' := (Subgroup.mem_inf.mp hxc_mem).1
    have hx_in_center : x ∈ Subgroup.center (G ⧸ L₀) := (Subgroup.mem_inf.mp hxc_mem).2
    set K : Subgroup (G ⧸ L₀) := Subgroup.zpowers x with hK_def
    have hK_le_N' : K ≤ N' := Subgroup.zpowers_le.mpr hx_in_N'
    have hx_orderOf : orderOf x = p := by
      change orderOf xc = p
      exact (Subgroup.orderOf_coe ⟨xc, hxc_mem⟩).trans hxc_order
    have hK_card : Nat.card K = p := by
      rw [Nat.card_zpowers, hx_orderOf]
    have hx_comm : ∀ g, g * x = x * g := Subgroup.mem_center_iff.mp hx_in_center
    haveI hK_normal : K.Normal := by
      refine ⟨fun a ha g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hgx : Commute g x := hx_comm g
      have hgxk : Commute g (x ^ k) := hgx.zpow_right k
      rw [show g * x ^ k * g⁻¹ = x ^ k from by rw [hgxk.eq, mul_inv_cancel_right]]
      exact zpow_mem (Subgroup.mem_zpowers x) k
    refine ⟨K.comap f, hK_normal.comap f, ?_, ?_⟩
    · intro g hg
      have hg_N' : f g ∈ N' := hK_le_N' hg
      have : g ∈ (N.map f).comap f := hg_N'
      rwa [hN'_comap] at this
    · have h := card_comap_eq_card_mul_card_ker f hf_surj K
      rw [hf_ker, hL₀_card, hK_card] at h
      rw [h, pow_succ, mul_comm]

end OddOrder.BG.Ch1.S01
