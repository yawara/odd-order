---
id: 96
slug: s10-section8-dade-support-carveout-lane-b
title: "carve-out: S10 §8 Dade-support 宣言群を lane b 所有 ((8.18.c)/route-B 前提)"
created: 2026-07-02
---

# carve-out: S10 §8 Dade-support 宣言群を lane b 所有 ((8.18.c)/route-B 前提)

## 背景 (2026-07-02 hub 裁定、ユーザー委任レビュー)

lane b (β) の残る最深 body 2 クラスタのうち Cluster B ((8.18.c) `nonconjugate_diffImage_inner_zero`
→ (12.3) → (12.14)/(12.15)/(12.16) 最終矛盾、issue 9003) と route B (issue 8022 の
FamilyHypothesis71 再構成 → `not_all_maximal_typeI` → `theorem88_caseB_holds`) は、いずれも
**Pf §8 Dade-support geometry** を前提とし、その宣言群は物理的に lane a 所有の
`S10_MinimalSimpleStructure.lean` に同居している。

- 9003 の旧指示 (「lane a の S10/S11 は編集しない、S14 に pin」) の下で b は
  `support_mutual_exclusion` を S10 で実証明してしまい自己 flag (65a2be52 / 3bbbde4c)。
  hub 検証の結果この edit は**旧 statement が false as stated (nonconjugacy 仮説欠落) の修正 +
  sorry-free/axiom-clean 実証明**で、9003 裁定にて**受理 (keep in S10)**。
- lane a の active frontier は S12 (11.8 chain) + 次いで S11 σ-tail であり、S10 §8 support 宣言との
  近接衝突リスクは低い。§8 Dade-support は β cluster (type-I Dade tower) の主題そのもの。
- 先例: carve-out 0086/0088/0090 (同型の sub-file 所有例外)。

## 裁定 = scoped carve-out (lane b)

`OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` のうち、以下の **§8 Dade-support 宣言 +
その直接 helper (新設含む)** を **lane b 所有**として扱う (line は 2026-07-02 main 時点):

- `typeII_A_sets_TI` (:490) / `typeII_A_sets_normalizer` (:500)
- `dadeSupportHypotheses_typeI` (:556, Pf 8.15) / `dadeSupportHypotheses_typeP` (:565)
- `support_mutual_exclusion` (:853, Pf 8.18.c — 65a2be52 で b が実証明済)

加えて `OddOrder/Peterfalvi/S10_BGInterface.lean` への **A₁/σ♯/M̃ bridge 補題の追加**は b 許容
(既存宣言の変更は要 hub flag)。

**追加許容 (2026-07-04 hub 裁定, ユーザー承認 — §8-support consumer の proof-only de-gate)**:
lane b が §8-support の上流 (BG Theorem B 系) を sorry-free 化したとき、その consumer である
**§8-support lane-a 宣言の証明本体を「now-sorry-free な upstream を cite する」形に差し替える
de-gate 編集**は b 許容 (逸脱としない)。**条件**: (i) signature/statement 不変、(ii) sorry/axiom
regression なし、(iii) 9003 等で self-flag。具体例 = `typeI_centralizer_le_and_unique` (:1728,
Pf 8.12.b) を B4 full-Theorem-B cite → `typeP_hall_small_subgroup_cyclic_tau2` 直接 cite に
de-gate (commit 94a34018)。**statement を変える編集は依然 out-of-scope** (下記) で要 hub flag。

**追加許容 (2026-07-04 hub 裁定 #2, ユーザー承認 — (8.12.b) faithful form の S10 landing + 注記)**:
lane b は §8-support の (8.12.b) について、以下を S10 で行ってよい (逸脱としない):
(a) **faithful sorry-free 版の新 decl 追加** (例 `typeI_or_typeII_centralizer_unique_hall` — Hall 仮説
付き完全証明・axiom-clean、commit 7f863d33)。(b) 旧 false-as-stated / overstated decl
(`typeI_or_typeII_centralizer_unique`・`escapingCentralizers_control`・`typeII_A_sets_*`) への
**docstring-only 注記** (false-as-stated/vestigial の警告 + faithful 版へのポインタ)。**条件**:
statement/proof 改変なし (旧 decl の statement と `sorry` proof は不変)、build green、sorry
regression なし。**旧 decl の実際の削除・statement 改変・proof 差し替えは要 hub flag** (9006 step 5 の
旧 `typeI_or_typeII_centralizer_unique` 削除は S11 migration 完了時に別途処理)。

**対象外 (従来通り lane a、b が statement 変更/proof 差し替え/削除したら逸脱)**: S10 のそれ以外すべて — bgTheoremE carrier
(`BGTheoremECoverData`/`bgTheoremE_cover_data` 等)、`hall_maxNilpotentNormalHall_and_mainSubgroup`、
`typeI_or_typeII_centralizer_unique`、`escapingCentralizers_control`、type-classification structural
((8.16)/(8.6.a) 系を含む Cluster A 前提 — こちらは 9003 どおり S14 に pin して cite)。
⚠ 上記 de-gate 許容は **proof body のみ**。これら宣言の statement 改変は引き続き逸脱。

**step 1.5 運用 (merge_monitor)**: lane b の S10/S10_BGInterface 編集は、hunk が上記宣言
(+新 helper) の文脈に収まる場合のみ逸脱としない。曖昧なら `git diff main...b -- …S10…` の
hunk 位置で判定 (carve-out 0086 と同じ運用)。

**lane a への通知**: 上記 5 宣言 (+b の新 helper) は編集しない (要望は notes/issue 経由)。

## やること

- [x] 裁定 + 所有マップ反映 (merge_monitor.md 🔒 マップ直下 carve-out 節)
- [ ] lane b: (8.18.c) の mixed Ã₁∩Ã support theory ((8.13.c)/(8.17)/(8.18)) を本 carve-out 範囲で
      正面から build (9003 loop⁹⁸ への回答 = これが β の最深 body、回避対象ではない)
- [ ] lane b: route B (issue 8022) の per-rep `dadeSupportHypotheses_typeI` (8.15) を同範囲で build
- [ ] 恒久解: §8 support theory が固まったら hub prefix-split で S10 から dedicated leaf
      (例 `S10_DadeSupport.lean`) に分離し、本 carve-out を解消

## 🧾 境界補足 (2026-07-02 全体レビュー)

- **`escapingCentralizers_control` (S10:482, Pf 8.13.c 系, 現 consumer 0)**: 9003 loop⁹⁸ の分析どおり
  (8.18.c) mixed 形は (8.13.c) escaping-centralizer を要しうる。**b が (8.13.c) piece に到達したら本
  carve-out に本宣言を拡張する** (hub 承認 1 行で可) — b が S14 側で helper を再導出する形は取らない
  (dup 防止)。それまでは lane a 保持のまま。
- **a 保持の S10 structural trio** (`hall_maxNilpotentNormalHall_and_mainSubgroup` (S14 4 call sites) /
  `typeI_or_typeII_centralizer_unique` / `escapingCentralizers_control`): b が必要なら **9003 pattern
  (S14 に sorried pin して cite)** が既定。a の queue 到達 (文書順 §8 は 0044→σ-tail の後) を待たない。

## 完了条件

(8.18.c)/route-B が要する §8 Dade-support 宣言が sorry-free 化し、恒久解 (dedicated leaf 分離) で
carve-out が不要になること。

## ⚠️ lane b 発見+修正 (2026-07-02, commit 5807febb) — (8.15) carrier が unfaithful pin で uninhabited だった

carve-out task「(8.15) build」の着手時精査で **`DadeSupportHypothesisData.H_eq_supportKernel` が
issue 8021 と同根の unfaithful pin** と判明: `H(a) = supportKernel M M A a = C_{M_F}(a)` (escaping
set 上) は、escaping `a ∈ A₁(M)` で `a ∈ C_{M_F}(a) ∩ C_M(a)` となり dade の (2.2.b) disjointness /
(2.2.c) coprimality と**矛盾** → escaping 元が存在する A で構造体が uninhabited (= S12/S14 の
`Hypothesis` が vacuous パラメータ化、(8.15) 2 宣言は証明不能)。Pf (8.14) の R(a) は per-x
supporting maximal `N[a]` の `C_{(N[a])_F}(a)` (Coq `FTsignalizer`/'R[x])。

**修正 (5807febb、本 carve-out 範囲)**: S10 に `ftSupportKernel M A x` (escaping で BG
`FT_signalizer x`、それ以外 ⊥) + `ftThickenedSupport` を新設し、`H_eq_ftSupportKernel` に差し替え。
`dadeSupport_eq_thickenedSupport` field は proven lemma `dadeSupport_eq_ftThickenedSupport` に変換。
`hconj` (R(x) の M-conj 不変性、Theorem D uniqueness 由来) を field 化 (S14/S12 の導出は datum 参照
1 行に)。S14 の `dadeSupport_subset_conjClassSet_maxNilpotentNormalHall_of_frobenius` は faithful 定義下で
**偽** (escaping coset factor は σ(L)′-元で L_F に共役不能) のため削除 (consumer 0)。

**cross-lane flag**: `S12_MaximalIII_IV_V_Core.lean` (lane a) に機械的追従 2 hunks
(`hconj := dadeData.hconj` + dead private `supportKernel_conj_invariant`/helper 削除)。65a2be52 受理
と同型の statement-soundness 改善で、lane a frontier (11.8/S12 char) と非衝突。full build 3898 green。

## 参照

- issue 9003 (Cluster B gate map + 本裁定の記載先) / issue 8022 (route B) / issue 0091 (受理前例)
- commit 65a2be52 (support_mutual_exclusion 実証明) / 3bbbde4c (b 自己 flag) / 5807febb ((8.15)
  carrier faithful 化)
- merge_monitor.md 🔒 マップ + carve-out 先例 0086/0088/0090

## ✅ HUB 裁定 (2026-07-03, 監視再開 tick): S12_Core 追従 2 hunks 受理

上記 cross-lane flag (`5807febb` の S12_MaximalIII_IV_V_Core 機械的追従 2 hunks) は
**ユーザー裁定 2026-07-03 で受理・合流済** (`55e46f1f`)。hub 検証: merge base 単一で誤検出
でなし / 削除補題の外部 consumer 0 / lane a の同 file hunk (@370) と非重複。
**standing carve-out ではない** (issue 0091 と同運用): 以後 lane b が S12_Core を編集したら
通常どおり逸脱 → 都度 flag + 裁定。

## ⚠ HUB 注記 (2026-07-03): issue 9004 追加発見 2 が本 carve-out の (8.15) typeP 側に波及

lane a の issue 9004「追加発見 2」: `typePA0` (GroupTheory/MaximalSubgroupType.lean:309) の
**G-共役閉包は unsound** — `S04.Hypothesis` の `subset_L` と G の単純性が矛盾し、b 所有の
`dadeSupportHypotheses_typeP` (S10:566) 第 1 成分は **statement が偽 (充足不能)**。修正
(M-共役化) は lane a が 9004 で claim 済 (shared MaximalSubgroupType + S12_Core fallout)。
b は (8.15) typeP 側に着手する前に 9004 を読み、typePA0 定義変更の自動追従を前提にすること
(typeI 側 = 232aaf18 は影響なし)。lane 間調整は 9004/本 issue への追記経由 (cross-lane-sync-via-notes)。
