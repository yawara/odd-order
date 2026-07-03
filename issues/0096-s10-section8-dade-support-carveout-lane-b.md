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

## 🔎 lane b 精査 (loop¹¹⁵) — type-P Dade engine soundness 解決: (M')# は正しい base、残 = escaping signalizer structure

loop¹⁰⁹ の「typePA=(M')# ⊋ ASet で unsound か?」を Pf (8.10)/(8.13) + Coq PFsection8 で解決:

**✅ (M')# は type-P の正しい Dade base** (Pf (8.10) mmd 04.10 L119): 「A_1(M)=A(M)=(M')# **if M is of
type III, IV or V**」。∴ type-P M (III/IV/V) では A(M)=(M')#=A_1 が定義どおり正しい。loop¹⁰⁹ の
(M')#⊋ASet 懸念は **type-II M** の話 (A(M)≠(M')#) で、**type-P engine (III/IV/V) には無関係**。
Coq: `FT_Dade_support M A` (PFsection8:78) + BGsection16「'A(M) == Peterfalvi (8.10)」で整合確認。

**✅ escaping soundness** (Pf (8.13.b) mmd L139): 「D={x∈A(M):C_G(x)⊄M} ⊂ A_1(M)」。type-P で
A_1=(M')# ゆえ escaping (M')# ⊂ (M')# (自明)、engine の base として健全。

**⚠ 残る deep piece = `escaping_typePA_signalizer_structure` (type-P (8.13.c))**: **clean な σ-sharp
還元は不可**。M'=M_F⋊U で U は (κ∪σ)'-complement ゆえ **M' ⊄ M_σ** (U-part が σ')、∴ escaping (M')#
点は一般に σ-sharp でない → type-I の `signalizer_structure_of_mem_sigmaSharp` (σ-sharp 要) を直接
使えない。type-P 固有の signalizer 構造 (Pf (8.13.c1/c2) の semidirect、BG §16 の non-σ-sharp escaping
treatment) が要る = **genuine deep BG §16、focused multi-session**。loop¹⁰⁷ の評価が正しかった。

**次手 (fresh session)**: (a) type-P (8.13.c) signalizer 構造の BG §16 原文 (mmd) + Coq FTsignalizer
精読、(b) escaping (M')# 点の R(x) 定義 (Pf 8.14 の supporting maximal N[x] 経由、σ-sharp 非依存版が
あるか)。soundness は解決済ゆえ build は confident に進められる。conj-invariance 前提 (typePA_conj_mem/
A1_conj_mem, loop¹⁰⁸) は済。

## 🚀 lane b 進捗 (loop¹¹⁶) — type-P engine build path 確定 + P1 structural bridge landed

type-P Dade engine の build path を `mainSubgroup_eq_Msigma`/`A1_eq_sigmaSharp` (共 proven, S16) を
軸に確定し、P1 の structural bridge 2 本を landed (S10、full build green)。

**確定した build path** (soundness は loop¹¹⁵ で解決済):
- **A1 M tau = sigmaSharp = M_σ# (全 tau, `A1_eq_sigmaSharp` proven)**。∴ engine の A1 成分は σ-sharp
  set への Dade data で、escaping 点は σ-sharp、`signalizer_structure_of_mem_sigmaSharp` 直接適用 = clean。
- **typePA = (M')#**: P1 (M'=M_σ, `isTypeP1_derivedInG_eq_Msigma`) では **= M_σ# = sigmaSharp** (clean、
  landed `typePA_eq_sigmaSharp_of_isTypeP1`)。P2 (M_σ⊊M', `maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2`
  は M_F(M')=M_σ を与えるのみ) では typePA⊋M_σ#。
- **escaping typePA ⊆ σ-sharp (全 type-P)**: (8.13.b) escaping⊆A_1 + A1_eq_sigmaSharp。P1 は自明
  (landed `escaping_typePA_mem_sigmaSharp_of_isTypeP1`)、P2 は type-P (8.13.b) `escaping_typePA_mem_A1` が要る
  (deep — typePA⊄ASet ゆえ type-I の ASet route 不可)。
- **typePA0 = typePA ∪ V^M**: V^M (exceptional) 成分は別途。

**残 build (fresh session、~150 行)**: (1) σ-sharp base engine `dadeSupportHypothesisData_of_subset_sigmaSharp`
(type-I engine の σ-sharp core を typeIA 非依存に一般化; escaping_sigmaSharp_signalizer_structure を
type-I `escaping_typeIA_signalizer_structure` step 2-4 から抽出)。(2) A1 + P1-typePA 成分を cite で discharge。
(3) P2-typePA の `escaping_typePA_mem_A1` (type-P 8.13.b) + typePA0 の V^M。conj-invariance 前提済 (loop¹⁰⁸)。

**landed** (loop¹¹⁶): `typePA_eq_sigmaSharp_of_isTypeP1` / `escaping_typePA_mem_sigmaSharp_of_isTypeP1` (S10)。

## 📋 lane b 精査 (loop¹¹⁷) — σ-sharp engine の coprimality core は type-specific、engine は genuine multi-session

loop¹¹⁶ の「σ-sharp base engine を type-I engine から抽出」を精査したところ、**clean な抽出は不可**:
- 抽出対象の type-I `escaping_typeIA_signalizer_structure` step 2-3 (join/disjoint/normalize) は σ-sharp
  のみ依存で抽出可能。
- **但し step 4 (coprimality c2) の core `escaping_sigma_disjoint_centralizer` (S10:899) は type-I 固有**:
  `kappa S = ∅` (type-I=type-F) を使う。type-P (kappa≠∅) では coprimality 論法が異なり、**type-P 版の
  (8.13.c2) が要る = deep**。
- 同様に `typeIA_isConj_conj_in_M` (8.13.a)・`ftSupportKernel_conj_smul` も type-P 版が要る。

**∴ type-P Dade engine は genuine multi-session build** (P1 structural bridge = loop¹¹⁶ の clean landed
piece、engine 本体は type-P 固有 (8.13.a/c2) + escaping structure の deep pieces を要す)。

**⚠ lane b 全体状態 (honest)**: ungated な lane-b own-work は **deep type-P engine のみ**。他は全て
他レーン upstream に gated: Cluster A (12.10-12) = lane a §8-§11 (8.16/8.6.a/9.7.b/10.10/11.6, 未形式化)、
Dade calc (12.14-16) = (12.3)[§16 via 8.18.c=lane c] / Cluster A、(8.18.c) = §16 lane c、S09 card_G0 =
7.9/11.8 lane a。→ lane b は type-P engine (deep) を focused に進めるか、他レーン upstream 待ち。

## 🎯 loop¹¹⁸ — 2 of 3 pins LANDED: loop¹¹⁷ の「isConj/structure も type-specific-deep」評価を revise

loop¹¹⁷ は「(8.13.a) isConj・escaping structure・(8.13.c2) coprimality すべて type-P 固有 = deep」と
評価したが、**精査で isConj と structure は σ-decomposition-generic (= wiring) と判明**。3 pin 中 2 本を
build-green で landed (S10):

1. **`sigmaSharp_isConj_conj_in_M`** (σ-sharp (8.13.a)): `a,b∈M_σ#`, `b=gag⁻¹` ⟹ M-conj。**tame
   embedding 経由でなく σ-分解から native に証明**: `M` と `g⁻¹Mg` は共に `a` の σ-maximal
   (`maximalConjugatesContaining_eq_maximalSigma`)、Thm 14.4 `exists_conj_centralizer_of_mem_maximalSigma`
   で `C_G(a)`-conj、`gc∈N_G(M)=M` (`normalizer_eq_self_of_mem_maximalSubgroups`) が M-conjugator。
   `A1_eq_sigmaSharp` (全 tau) ゆえ **A₁ の conj_in_L を全 type で discharge**、P1-typePA も
   (`typePA_eq_sigmaSharp_of_isTypeP1`)。
2. **`escaping_sigmaSharp_signalizer_structure`** (σ-generic (8.13.c1)): `a∈M_σ#` escaping ⟹
   `C_G(a)=R(a)⋊C_M(a)` (join/disjoint/normalize)。type-I `escaping_typeIA_signalizer_structure` の
   step 2-4 は **kappa=∅ を hσa 導出のみに使い、以降は σ-sharp generic** と確認 ⟹ 3-conjunct を抽出。
   **type-I 版も本 lemma を cite するよう dedup refactor** (~90 行削減、signature 不変ゆえ downstream 不変)。

### loop¹¹⁸ cont. — 3rd pin も σ-generic: type-P engine 全体が tractable (deep 評価は完全に誤り)

(8.13.c2) coprimality core `escaping_sigma_disjoint_centralizer` を精読した結果、**これも σ-generic と
判明** (loop¹¹⁷/loop¹¹⁸-前半 の「coprimality = type-specific-deep」評価も誤り):
- 中核 `non_disjoint_signalizer_frobenius` (BG Lemma 14.13(a)) は **`TypeIData` を取らず任意の maximal
  `S` に効く** (common prime ⟹ S Frobenius + τ₂(S)=∅ の implication は general)。
- type-I 固有部は **(a) `z∈M_σ#` を κ(S)=∅ から導出、(b) `w∈M_σ` を type-F Frobenius 吸収から導出**
  の 2 点のみ — σ-sharp 版では両方 **hypothesis**。
- ⟹ `escaping_sigmaSharp_disjoint_centralizer` (σ-generic, hypotheses `hσz`/`hwMσ`/`hw1`) を抽出、
  **type-I 版も back-half を本 lemma に delegate する dedup** (~68 行削減)。

**∴ 3 pin すべて σ-generic で landed (build green)**:
`sigmaSharp_isConj_conj_in_M` (8.13.a) / `escaping_sigmaSharp_signalizer_structure` (8.13.c1) /
`escaping_sigmaSharp_disjoint_centralizer` (8.13.c2)。**type-P Dade engine は deep multi-session でなく
σ-generic wiring** (loop¹¹⁷ の全評価を revise)。

**次 build path (更新²)**: σ-sharp base engine `dadeSupportHypothesisData_of_subset_sigmaSharp`
(`dadeSupportHypothesisData_of_subset` を X⊆M_σ# 用に; 3 pin + `ftSupportKernel_conj_smul` σ-版 の hconj
field を wiring) → `dadeSupportHypotheses_typeP` の **A₁ 成分 (全 tau、A1=M_σ#) + P1-typePA 成分**
(typePA=M_σ#) を discharge。残る P2-typePA + typePA0 は typePA⊋M_σ# ゆえ escaping⊆A_1 の (8.13.b)
`escaping_typePA_mem_A1` (P2) + V^M 成分が要る (別 frontier)。∴ 次 iteration =
`dadeSupportHypothesisData_of_subset_sigmaSharp` 組立 + `ftSupportKernel_conj_smul` σ-generic 化。

### loop¹¹⁹ — σ-sharp base engine LANDED + `dadeSupportHypotheses_typeP` の A₁ 成分を honest discharge

上記 build path を実行、build green:
1. **`FT_signalizer_conj_smul_of_escaping_sigmaSharp`** (σ-generic (8.14) kernel 同変性): type-I
   `FT_signalizer_conj_smul_of_escaping` の κ=∅ σ-sharp 導出を hypothesis 化 (a とその共役の σ-sharp性)。
2. **`ftSupportKernel_conj_smul_sigmaSharp`** (X⊆M_σ# 上の hconj field 用)。
3. **`dadeSupportHypothesisData_of_subset_sigmaSharp`** (σ-generic engine): 任意の M-conj-invariant
   nonempty `X⊆M_σ#` に Dade (2.2) support data。3 pin + normalizer_support_eq (既 generic) + kernel 同変性
   で組立。type-I `dadeSupportHypothesisData_of_subset` と同構造だが type-I lemma 群でなく σ-generic pin 駆動。

**`dadeSupportHypotheses_typeP` の A₁ 成分を honest 実証**: `refine ⟨?_,?_,?_⟩` で 3 分岐化、
**A₁(M)=M_σ# (全 tau、`A1_eq_sigmaSharp`) を engine で discharge** (nonempty ← `Msigma_ne_bot` +
`mainSubgroup_eq_Msigma`、hXiff ← `A1_conj_mem`)。sorry は 1→2 だが A₁ 三分の一が**本物の証明**に
(doneness = 仮説構成可能性、sorry-count でない)。残 2 sorry = **typePA0 (V^M exceptional 成分) + typePA
(P2 は escaping⊆A_1 の (8.13.b) `escaping_typePA_mem_A1`; P1 は typePA=M_σ# で engine 適用可)**。両者とも
signature 明記の genuine deep obligation。

**次 frontier**: (a) **P1-typePA を engine で discharge** (`typePA_eq_sigmaSharp_of_isTypeP1` で
typePA=M_σ#、但し `dadeSupportHypotheses_typeP` は tau 一般ゆえ P1 特化には型分岐が要る — data から P1/P2
を判定して分岐)。(b) **type-P (8.13.b) `escaping_typePA_mem_A1`** (P2-typePA/typePA0 の escaping 還元)。
(c) **typePA0 の V^M 成分**。engine が完成した今、残りは type-P 固有の support 幾何 ((8.13.b) + V^M)。

### loop¹¹⁹ cont. — P1-typePA も engine で discharge (frontier (a) 完了)

A₁ datum を `have hA1` に抽出 (A₁ bullet + P1-typePA で再利用)。**typePA の P₁ 分岐を engine で honest
discharge**: `by_cases hP1 : IsTypeP1 M` → P1 branch は `rw [typePA_eq_sigmaSharp_of_isTypeP1,
← A1_eq_sigmaSharp]` で typePA=M_σ#=A₁ に還元し `exact hA1`。`classical` で任意 Prop に by_cases 可。

**`dadeSupportHypotheses_typeP` 現状**: A₁ (全 tau) ✅ + typePA-P₁ ✅ = **honest**、残 2 sorry =
**typePA0 (V^M exceptional) + typePA-P₂ ((8.13.b) `escaping_typePA_mem_A1` の escaping 還元)**。
engine 部分は完了、残りは type-P 固有 support 幾何のみ。次 = (b) type-P (8.13.b) の実証 or (c) V^M。

### loop¹²⁰ — P2-typePA/typePA0 = genuine deep type-P structure と確定 (engine と違い wiring でない)

残 2 sorry を精査:engine の σ-generic wiring とは違い、**type-P 固有の support 幾何が要ると判明**。

**P2-typePA の障害 (precise)**: engine は escaping 点が σ-sharp (∈M_σ#) を要求。P2 は typePA=(M')#⊋M_σ# ゆえ
escaping (M')# 点が σ-sharp である必要。σ-sharp 化の唯一の route `mem_sigmaSharp_of_mem_aSet_of_escape`
(S16:6179) は **ASet/A0Set cover gated** (点が cover 内であることが前提)。cover-free の escape→σ-sharp は
**存在しない**。`typePA ⊆ A0Set M K` bridge も未存在で、要 `(M')# ⊆ hatMsigma M`
(= 全 x∈(M')# で M_σ⊓C_G(x)≠⊥) = **genuine deep type-P 構造** (case-heavy: W1# 点は `centralizer_W1`→W2⊆H⊆M_σ
で OK だが、一般 M' 元は nilpotent H=M_F への固定点論法が要り自明でない; 冪零 H への coprime 作用は
fixed-point-free 可)。**M_F ⊆ M_σ は general** (`maxNilpotentNormalHall_le_Msigma` S15:175) — 部品にはなる。

**typePA0**: typePA ∪ conjClassSetIn M (typePV M data) の **V^M exceptional 成分** (`typePV` S10-GT:305)。
別 deep obligation。

**次 iteration の第一歩 (優先度確認 + 攻略)**: (1) **downstream consumer 確認** — `dadeSupportHypotheses_typeP`
の typePA0/typePA 成分が FT critical path で実際に consume されるか grep (A₁ 成分だけで足りる下流なら
P2-typePA/typePA0 は後回し可; feedback-verify-lane-connects-to-goal)。(2) consume されるなら
**`(M')# ⊆ hatMsigma` (or escaping 版) を type-P 構造から実証** — TypePData の H⋊U 構造 + centralizer_W1
+ M_F⊆M_σ + 固定点論法。Coq `BGsection15/16` の of_typeP normedTI 'F(M)^# を併読 (PFsection8.v L141:
`normedTI 'F(M)^# G M`)。これが type-P Dade engine の最後の deep core。

### loop¹²⁰ cont. — ★ 束縛制約 = typePA0 の V^M exceptional 成分 (engine 対象外・deep) と判明

**downstream consumer 確認結果 (重要)**: `dadeSupportHypotheses_typeP` の唯一の consumer =
`S12_MaximalIII_IV_V_Core.exists_hypothesis_of_typeIIIorIVorV` (Pf **(10.1) existence**, §12 Dade tower
の入口) が **`.1` = typePA0 成分**を `S12.Hypothesis.dadeData` field に使う (S12:567)。type III/IV/V は
**全て P1** (`exists_peterfalviType`: P₁ が V/III/IV に分岐) ゆえ、**S12 の束縛制約 = typePA0(P1)**。

**私が実証した A₁/P1-typePA は束縛制約でない** (genuine だが consumer は typePA0 を要求)。engine は
typePA0 の **M_σ# 部分**を賄うが、**V^M 部分は engine 対象外**:
- `typePV = W \ (W1∪W2)`、`typePA0 = typePA ∪ conjClassSetIn M typePV`。
- V 元は W1-成分が非自明 (W=W1⊔W2、V は両成分非自明の diagonal 部) ⟹ W1⊓M'=⊥ (M_complement) ゆえ
  **V ⊄ M'、V^M ⊄ M_σ#** ⟹ **engine (X⊆M_σ# 前提) 適用不可**。
- V^M = type-P **exceptional character** の support = deep type-P Dade 幾何。

**∴ 真の frontier = typePA0(P1) の Dade data = [M_σ# 部分 = engine ✅] + [V^M 部分 = deep exceptional]**。
これが §12 type-P tower (10.1 existence) の束縛制約。P2-typePA は S12 consumer (P1) には不要
(typePA(P1)=M_σ# で足りる)。

**次 iteration**: (1) `typePA0` の `IsTISubset ... M` (S10:556 area、既 proven か確認) → TI-structure から
V^M の Dade data が出るか (normedTI 'F(M)^# route, Coq BGsection16 of_typeP)。(2) typePA0(P1) を
M_σ# ∪ V^M に分解し、M_σ# 部分は engine、V^M 部分を TI/exceptional で。engine の
`dadeSupportHypothesisData_of_subset_sigmaSharp` は M_σ# を賄うが、typePA0 全体は **union support の
Dade data 合成** (2 TI-piece の disjoint union) が要る = 新機構。

### loop¹²¹ — V^M non-escaping + (8.13.b) typePA0-P1 landed; typePA0_isConj は wireable の見込み

typePA0(P1) Dade data の**構造基礎 2 本を build-green で landed**:
1. **`centralizer_typePV_le_M`**: v∈V=W∖(W1∪W2) で C_G(v)≤M (`normalizer_V`: N_G(⟨v⟩)=W、singleton ゆえ
   =C_G(v)、W=W1⊔W2≤M)。⟹ **V^M 点は非 escaping** = Dade 構造は trivial (H(v)=⊥)。
2. **`escaping_typePA0_mem_sigmaSharp_of_isTypeP1`** ((8.13.b) for typePA0-P1): escaping A_0(M) 点は
   σ-sharp。V^M 点は非 escaping (#1) ゆえ escaping 点は typePA(P1)=M_σ# に居る。engine が **full A_0(M)**
   (A_1=M_σ# だけでなく) を P1 で賄うのに要る (8.13.b) 還元。

**残: typePA0(P1) engine の 3 piece** — (a) generalized engine (X⊆M, escaping⊆M_σ#; type-I
`dadeSupportHypothesisData_of_subset` を σ-generic pin + (8.13.b) で駆動)、(b) **typePA0_isConj**
(G-conj→M-conj)、(c) **coprimality** (b∈typePA0)。

**typePA0_isConj は wireable 見込み** (deep-from-scratch でない): S16 `theoremII` の conjunct-1 内部
(S16:6010-6030) が piece 別に conjugacy 制御 — M_σ 部=Thm D(1)、**A(M)−M_σ 部=Thm B(5)**、
**A_0−A (=V^M) 部=Thm C(9)** の `hTI_B`/`hTI_C`。∴ typePA0_isConj は (i) `typePA0 = A0Set M K` (BG A_0)
対応を示せば tame embedding conjunct-1 直用、or (ii) Thm B(5)/C(9) を抽出。**次 iteration**: typePA0 vs
BG A0Set 対応を確認 (A_0(M) 記法の BG↔Pf 一致)、なら typePA0_isConj + coprimality が tame embedding
から wire 可能で typePA0(P1) engine 完成 → `dadeSupportHypotheses_typeP` typePA0 成分 discharge →
S12 (10.1 existence) unblock。

### loop¹²² — typePData_V_ti を S10 へ upstream + V^M conjugacy landed (typePA0_isConj の V^M 半分)

typePA0_isConj (typePA0=M_σ#∪V^M の G-conj→M-conj) に向け:
- **`typePData_V_ti` を S12→S10 へ move** (upstream + dedup): V=W∖(W1∪W2) は TI-subset with
  normalizer W。self-contained (TypePData + cyclic_subgroup_eq_of_card_eq + IsTISubset) ゆえ S10 で proven、
  S12 は cite (S12 は S10 を transitive import; `S10.typePData_V_ti` に 2 cite 更新)。
- **`conjClassSetIn_typePV_isConj_conj_in_M`** (V^M half): a,b∈V^M, b=gag⁻¹ ⟹ M-conj。
  a=m1v1m1⁻¹, b=m2v2m2⁻¹ で h=m2⁻¹gm1 が v1↦v2 (V内) ⟹ typePData_V_ti で h∈W≤M ⟹
  **g=m2·h·m1⁻¹∈M 自身が M-conjugator**。

**typePA0_isConj の残 = mixed case** (a∈M_σ#, b∈V^M, G-conj): V 元は W1-成分 (κ-order) 非自明ゆえ
純 σ-元でない → M_σ#(σ-order) と非共役 (order prime-type mismatch) = **vacuous**。要 κ∩σ=∅ + W1 の
κ-order 構造。次: mixed-case vacuity → typePA0_isConj 完成 → generalized engine + coprimality →
typePA0(P1) Dade data discharge → S12 (10.1) unblock。

### loop¹²³ — typePData_typePV_not_mem_derived を S10 へ upstream (mixed-case 準備)

typePA0_isConj の mixed case (a∈M_σ#, b∈V^M は非共役) は「v∈V→v∉M'」を要する。この fact
(`typePData_typePV_not_mem_derived`, S12) を **S10 へ move** (upstream + dedup): self-contained
(TypePData の W_cyclic/W_eq/M_complement/W2_le/H_le)。S12 の 5 cite (S12_Core 3 + S12_MaximalIII_IV_V 2)
を `OddOrder.Peterfalvi.S10.` prefix に更新。両 S12 leaf build green。

**次 (mixed case 完成 → typePA0_isConj)**: a∈M_σ#→σ-elt (`isPiElement_sigma_of_mem_Msigma`)、
b=gag⁻¹→σ-elt (`isPiElement_conj`)、b∈V^M→v∈V σ-elt→v∈M_σ (`sigma_subgroup_le_Msigma_of_isHall`
+`Msigma_isHall`)=M' (P1, `isTypeP1_derivedInG_eq_Msigma`)、v∉M' (`typePData_typePV_not_mem_derived`)
で矛盾 = vacuous。⟹ typePA0_isConj (M_σ#/V^M/mixed 3-case) 完成。その後 coprimality + generalized
engine (X⊆M, escaping⊆M_σ# 版) → typePA0(P1) Dade data discharge → S12 (10.1) unblock。
