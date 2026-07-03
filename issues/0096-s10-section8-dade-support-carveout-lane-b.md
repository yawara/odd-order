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

### loop¹²³ cont. — ★ typePA0_isConj (P1) COMPLETE (mixed-case vacuity landed)

**`typePA0_isConj_conj_in_M_of_isTypeP1`** = typePA0(P1)=M_σ#∪V^M の G-conj→M-conj、**3-case 完成**:
- both M_σ#: `sigmaSharp_isConj_conj_in_M`。
- both V^M: `conjClassSetIn_typePV_isConj_conj_in_M`。
- mixed: `not_isConj_typePA_typePV_of_isTypeP1` (vacuous) — M_σ#=σ-elt、conj で σ-elt 保存、
  V^M の v は σ-elt なら M_σ=M' (P1) に入り v∉M' と矛盾。σ-chain =
  isPiElement_sigma_of_mem_Msigma / isPiElement_conj / sigma_subgroup_le_Msigma_of_isHall /
  isTypeP1_derivedInG_eq_Msigma / typePData_typePV_not_mem_derived。

**技術メモ**: mixed-case lemma が whnf timeout したが原因は `m⁻¹⁻¹` vs `m` の defeq search (heartbeat
bump 不要)。isPiElement_conj m⁻¹ の型は `m⁻¹*y*m⁻¹⁻¹` で `m` と書くと whnf 爆発。正しい形で即解決。

**typePA0(P1) Dade engine の残 (isConj 完了)**: (1) **coprimality** (escaping a, b∈typePA0 で
coprime |R(a)| |C_M(b)|; b∈M_σ#→σ-sharp coprimality、b∈V^M→C_M(b)⊆W との coprimality)、
(2) **generalized engine** (X⊆M, escaping⊆M_σ# 版; sigmaSharp engine を一般化)、(3) assembly →
dadeSupportHypotheses_typeP typePA0 成分 discharge → S12 (10.1) unblock。pins 済:
escaping_typePA0_mem_sigmaSharp (8.13.b) + centralizer_typePV_le_M (V^M 非escaping) + isConj。

### loop¹²⁴ — ★ coprimality は tractable (σ-sharp に還元) — typePA0(P1) engine 全 pin 完備

初め「V^M coprimality は deep (σ vs W structure)」と危惧したが、**σ-sharp coprimality に還元できると判明**
(過去の "deep" 危惧と同様に tractable):

**`coprime_FT_signalizer_centralizerIn_typePV`**: escaping a∈M_σ#, b∈V^M で coprime |R(a)| |C_M(b)|。
鍵: **C_M(b) は C_M(v)=W に M-共役** (v∈V: C_G(v)=N_G(⟨v⟩)=W by normalizer_V、⊇ は W abelian)、
`w∈W₂#⊆M_σ#` を取れば W≤C_M(w) (abelian) ⟹ |W| | |C_M(w)| ⟹ **σ-sharp coprimality
(`escaping_sigmaSharp_disjoint_centralizer`) を w で適用**して共通素数を殺す。card_centralizerIn_conj で
|C_M(b)|=|C_M(v)|、C_G(v)=W は normalizer_V + W abelian の antisymm。

**typePA0(P1) Dade engine の全 pin 完備**:
- isConj: `typePA0_isConj_conj_in_M_of_isTypeP1` ✓
- escaping→σ-sharp (8.13.b): `escaping_typePA0_mem_sigmaSharp_of_isTypeP1` ✓
- V^M 非escaping: `centralizer_typePV_le_M` ✓
- coprimality (V^M): `coprime_FT_signalizer_centralizerIn_typePV` ✓ (M_σ# は sigmaSharp engine)
- escaping structure: `escaping_sigmaSharp_signalizer_structure` ✓

**残 = final assembly のみ**: generalized engine (X=typePA0; sigmaSharp engine を X⊆M+escaping⊆M_σ# に
一般化、上記 pin で駆動) + ftSupportKernel_conj_smul の typePA0 版 + normalizer_eq(typePA0)。→
`dadeSupportHypotheses_typeP` typePA0 成分 discharge → S12 (10.1 existence) unblock。deep 部分は無し、
残りは mechanical assembly。

### loop¹²⁵ — general engine + full typePA0 coprimality landed (残 = set-facts + discharge のみ)

typePA0(P1) Dade engine の assembly infra を landed:
- **`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`** (general engine): sigmaSharp engine を
  X⊆M + escaping⊆M_σ# に一般化。(8.13.a) conj_in_L + (8.13.c2) coprimality を hypothesis 化、
  escaping structure は σ-generic `escaping_sigmaSharp_signalizer_structure`。
- **`ftSupportKernel_conj_smul_escaping_sigmaSharp`** (general conj_smul, hconj field 用)。
- **`coprime_FT_signalizer_centralizerIn_typePA0_of_isTypeP1`**: A_0 全体の coprimality
  (A(M)=M_σ# は σ-sharp、V^M は `coprime_FT_signalizer_centralizerIn_typePV`)。

**残 = mechanical wiring のみ**: typePA0 の set-facts (⊆M / ≠1 / nonempty / M-conj-invariant) を
組んで general engine に渡す `dadeSupportHypothesisData_typePA0_of_isTypeP1` → `dadeSupportHypotheses_typeP`
の typePA0(P1) 成分 discharge (P2 は別 sorry のまま) → S12 (10.1 existence) unblock。deep content は
全て済み、残りは typePA0=typePA∪V^M の union set-facts の組立。

### loop¹²⁶ — ★★ typePA0(P1) Dade datum CONSTRUCTED (sorry-free) — dadeSupportHypotheses_typeP typePA0(P1) discharge

**`dadeSupportHypothesisData_typePA0_of_isTypeP1`** (sorry-free): type-P1 の A_0(M)=A(M)∪V^M の
Dade (2.2) support data を general engine + 全 pin + union set-facts (⊆M/≠1/nonempty/M-conj-inv,
conjClassSetIn API 経由) で **完全構成**。doneness = carrier 構成可能性を満たす (posited でなく実構成)。

**`dadeSupportHypotheses_typeP` の typePA0 成分を P1 で discharge**: by_cases hP1 → P1 は engine helper、
P2 は sorry (deeper)。現状 dadeSupportHypotheses_typeP: A₁ ✅ + typePA-P1 ✅ + typePA0-P1 ✅、
残 2 sorry = typePA0-P2 + typePA-P2 (deeper type-P2 (M')# geometry)。

**次 = S12 unblock**: `exists_hypothesis_of_typeIIIorIVorV` (Pf 10.1 existence) は現在
`(dadeSupportHypotheses_typeP ...).1` を使うが、これは P2 sorry を transitively 含む。**sorry-free な
`dadeSupportHypothesisData_typePA0_of_isTypeP1` に切替**れば S12 の typePA0 datum が sorry-free に。
要 hP1 : IsTypeP1 M を IsTypeIII/IV/V から導出 (III/IV/V=P1)。

### loop¹²⁷ — ★★★ S12 Pf (10.1) existence が sorry-free に — type-P (III/IV/V) tower の入口 UNBLOCK

**`exists_hypothesis_of_typeIIIorIVorV` (Pf 10.1 existence) を sorry-free 化**:
- S12 の `(dadeSupportHypotheses_typeP ...).1` (typePA0-P2 sorry を transitive 依存) を、sorry-free な
  **`dadeSupportHypothesisData_typePA0_of_isTypeP1` に routing 切替**。
- hP1 : IsTypeP1 M を III/IV/V から `proposition_type_classification` 経由で導出
  (III/IV = `.2.2.1`、V = `.2.2.2.1`)。
- **`#print axioms exists_hypothesis_of_typeIIIorIVorV` = [propext, Classical.choice, Quot.sound]
  のみ (sorryAx 無し)**。⟹ §12 type-P (III/IV/V) tower の入口 (Hypothesis 構成) が sorry-free。

**session 総括 (loop¹¹⁸-¹²⁷, ~20 commits)**: lane b の type-P Dade support 機構を σ-sharp engine から
type-P1 A_0 datum の sorry-free 構成まで積み上げ、S12 (10.1) を unblock。全ての "deep multi-session"
と恐れた障害 (engine 全体 / isConj / coprimality / V^M geometry) は σ-sharp 機構に還元。残 type-P2
((M')# geometry) は dadeSupportHypotheses_typeP の 2 sorry として cleanly 分離 (S12 は P1 のみ使うゆえ
tower 入口には不要)。

### loop¹²⁷ cont. — 次 frontier survey: §12 char analysis (S12_MaximalIII_IV_V の 4 sorry)

**unblocked 10.1 の downstream consumer (FT critical path 確認)**:
- **`FeitThompson.lean:446`** (FT spine) — `exists_hypothesis_of_typeIIIorIVorV` を
  `card_kappaHall_lt_of_isTypeIIIorIV` 経由で使用。⟹ 10.1 unblock は spine に直結。
- `S12_MaximalIII_IV_V:3666` (type-V contradiction)。

**次 lane-b frontier = `S12_MaximalIII_IV_V.lean` の 4 real sorry** (§12 type-P char analysis /
Dade tower body、10.1 Hypothesis が入手可能になった今 downstream)。S12_Core は 0 sorry。
次 iteration: 4 sorry を survey → 上流優先で engage (§10 ω-grid / §5 依存の有無を確認)。

type-P Dade support (§8) の carve-out 0096 の主目的 (typePA0 datum 構成 → S12 10.1) は達成。
以降は §12/§10 char analysis (別 arc、S12 主体)。

### loop¹²⁸ — 次 arc = §12 char body (deep character theory) と characterize

carve-out 0096 (type-P Dade **support** geometry) は達成。次 arc = **§12 char analysis body**
(`S12_MaximalIII_IV_V.lean` の 4 sorry)、いずれも deep §10/§11 character theory:
- `typeII_derived_frobenius` (10.7): type-II [S,S] Frobenius 構造 (coherence 仮定下)。
- `typeII_coherence_contradiction_estimate` (10.8): 「§7 analytic heart」norm-counting estimate。
- `exists_zeta_residual_not_orthogonal` (11.8.1-6): σ-grid identities + (5.7) S(HC)-coherence +
  (5.6) coherence-union の deep 非直交計算。
- `typeV_forces_coherence` (10.10): type-V coherence。

**これは type-P Dade support (σ-generic wiring だった) と質的に異なる deep char body** = lane b の core
§12 Dade tower の最深部 (loop¹¹⁷ が "deep char" と識別した領域)。ungated own-work だが genuine deep。
一部は §9↔§10 carrier bridge に gated の注記あり (L2244)。次 iteration: 上流優先で
`typeII_derived_frobenius` (10.7) から engage (fresh context 推奨、深い char/structure 証明)。

### loop¹²⁸ cont. — lane-b frontier 全体 survey (type-P support arc 後): S14 type-I Dade tower が主

「lane b mostly blocked」の早計を訂正。lane-b sorry inventory:
- **S14_MaximalI: 11 sorry** (type-I Dade tower: rho_constant_on_H_minus_Hprime, sibleyTarget_frobI,
  witness_L_isTypeI/complement_isZGroup, intersection_complement_structure, complement_cyclic_order_dvd,
  psi_constant_on_xK, rhoM_integer_values, exists_counterexample_dade_data, exists_typeICovering×2)。
  = lane b の core 型-I char/Dade 解析、ungated own-work 多数。
- S12_MaximalIII_IV_V: 4 (type-P char body、mixed: 11.8=lane-a gated、11.9.b/§10-11 core=lane-b)。
- S10 (carve-out): 8 (type-P2 residue 含む + type-II structural 系)。

**FT-path 確認**: exists_hypothesis (10.1) ✅ + w2_lt_w1 (11.9.b, lane-b) → exists_zeta_residual
(11.8, **lane-a** gated) → card_kappaHall_lt → FT spine。typeII_derived_frobenius (10.7) は 0 consumer。

**次 = S14 type-I Dade tower** (上流優先で engage)。type-P support arc (0096 主目的) 完了後の lane-b
主 frontier。深い char 解析ゆえ fresh context 推奨。

### loop¹²⁹ — (12.5) rho_constant 精読: deep multi-session char (Dade reciprocity/inertia/coherence infra 要)

S14 type-I Dade tower の上流 (12.5) `rho_constant_on_H_minus_Hprime` を Coq
`FtypeI_invDade_ortho_constant` (PFsection12:416) で精読:
- **(12.4) coset-constancy は Lean で proven** (`orthogonal_character_constant_on_coset` S14:2360,
  sorry-free): x∈L∖H で ψ(xh)=ψ(x)。
- **(12.5) は H∖H' 上 (inside-H) の ρ(=invDade) 版で別物・deeper**。Coq 証明は
  `pair_degree_coherence` + `invDade_reciprocity` (Dade reciprocity) + Iirr-H の
  Ind[H,H']-partition (P_ i, trivIset/cover) + `cfInd_central_Inertia` (central inertia) を要す。
- Lean 未整備: Dade reciprocity (invDade)、induced-from-H' partition、central inertia。⟹ **(12.5) は
  substantial char infra build を要する multi-session effort** (S14 type-I Dade tower 全 11 sorry も同様の
  deep char)。

**honest 状況**: type-P Dade **support** arc (0096 主目的) 完了 (S12 10.1 sorry-free, FT spine 直結)。
残 lane-b frontier = **deep multi-session §14 type-I char theory** (coherence/Dade-reciprocity/inertia
infra build 込み)。type-P support の σ-generic wiring とは質的に異なる。

### loop¹³⁰ — ★ 訂正: (12.5) は lane-b own-work + 主要 infra 存在 (loop¹²⁹ の過小評価を修正)

claim-before-build 調整で loop¹²⁹「(12.5) は from-scratch multi-session char-infra 要」を**訂正**:
- **§10-12 char core は lane-b own-work** (FeitThompson:418/496/855: §10-11/§10-12 char は lane-b 所有;
  lane-a は 11.8 exists_zeta_residual のみ)。→ (12.5) は lane-b own-work、lane-a と非競合。
- **Dade reciprocity は存在** (`Hypothesis.tau_inner_eq_of_supported` S12_Core:3586、
  `tau_inner_trivial` 5776)。loop¹²⁹「invDade 無し」は grep 名違い (Lean は tau_inner_*)。
- **Rset span も存在** (`coherent_extension_constituent_mem_span_Rset` S14:1720)。coherence も (S07/S08)。

**∴ (12.5) の残 infra = induced-from-H' Iirr partition のみ** (Clifford: H'⊴H で Irr(H)=⊔ constt(Ind[H,H'] χ),
Lean 未整備)。Ind[H,H'] χ は H∖H' 上 vanish (H'⊴H) ゆえ Fourier で ρψ=const on H∖H'。o_rpsi_S 部は
tau_inner + span + horth で即。**(12.5) は 1-2 iteration の tractable build** (from-scratch でない)。

**次 = induced-from-H' Iirr partition (Clifford) を build → (12.5) 組立**。concrete target 確定。

### loop¹³¹ — ★★ territorial 訂正: lane-b frontier = S14 Type-I tower (NOT §10/§9-keystone = lane-a)

**重大訂正**: loop¹²⁵-¹³⁰ で (10.8)`typeII_coherence_contradiction_estimate` / §9-keystone(2030) /
(11.8) を lane-b frontier と分析していたが、**これらは 2026-07-02 3レーン再編で lane-a 所有**
(正本 `ft_lane_reallocation_2026_06_28.md`:48「Pf S(0[3-9]|1[0-3])* 全体 = lane a」、:108-111 で
10.7/10.8/10.10/11.8/S13 は lane-a deepest body)。cross-check: 直近 S12 commit da165ea8/5a67ee61
=「Pf 11.8.4/5」= lane-a active。**FeitThompson.lean:418/496/855「§10-§12 char owned by lane-b」は
stale (再編前)** — lane-a 所有 file ゆえ lane-b は編集せず、staleness は lane-a へ notes 通知のみ。

**lane-b の実所有 (再編後)** = `S14_MaximalI.lean` 全体 (§12 all-Type-I Dade tower) + carve-out 0096
(S10 §8 Dade-support) + coherence infra (6.5.c)。type-P Dade support arc (loop¹¹⁸-¹²⁹) は 0096 = 正しく
lane-b territory だった (S10)。誤ったのは (10.8)/§9 への pivot のみ。

**lane-b live frontier = S14 の 11 sorry** (comment-strip 実測):
| Pf | decl | 複雑さ |
|---|---|---|
| 8.17 | `exists_typeICovering` (6197) | 8022 M̃-reroute に entangled (旧 lane-d carve-out、d 退役) |
| 12.5 | `rho_constant_on_H_minus_Hprime` (2413) | orphan(0 consumer) + statement 疑義 (ψ(h)=ψ(1) vs Coq「H∖H' で const」) |
| 12.10 | `sibleyTarget_frobI` (2521) | TI-case 限定、issue 2032 |
| 12.10 | `witness_L_isTypeI` (4666) | hub 9003 Cluster A pinned (deep §8-§11 type-analysis) |
| 12.10 | `witness_L_complement_isZGroup` (4677) | hub 9003 Cluster A pinned (deep §8 minimality) |
| 12.11 | `intersection_complement_structure` (4711) | 4 consumer だが (12.10) downstream |
| 12.12 | `complement_cyclic_order_dvd` (5148) | proven `isCyclic_..._fpf_conj_elemAbelian` は ∣p²-1、p+1 は Frobenius torus 構造要 |
| 12.13 | `exists_counterexample_dade_data` (5578) | 12.16 chain |
| 12.14 | `psi_constant_on_xK` (5340) | downstream char |
| 12.15 | `rhoM_integer_values` (5349) | downstream char |

**proven 済** (deepest-body list は stale): `nonconjugate_diffImage_inner_zero` (8.18.c, loop¹⁰⁰)、
`constituent_diff_support_subset_nonescaping` (loop¹¹¹)。

**次 = S14 tower を正面 engage** (lane-b assigned deep cluster; 全 sorry deep だが territory 内)。
upstream-most cleanly-lane-b = (12.5) rho_constant (statement 解決 → induced-from-H' partition +
Dade reciprocity(tau_inner) で build) か (12.12) の Frobenius-torus p+1 refinement。

### loop¹³² — ✅ 実 landing: induce vanishing lemma + (12.5) statement 確定

**① LANDED (sorry-free, commit 4f831a66)**: `induce_apply_eq_zero_of_not_mem_normal`
(InducedCharacter.lean:310) — 一般再利用可能: H ⊴ G で g∉H ⟹ Ind_H^G θ(g)=0 (各 induceTerm が
正規性 x⁻¹gx∈H⟺g∈H で消える)。build green 3158 jobs。数 iteration ぶりの実コード landing。

**② (12.5) statement 確定 = MIS-STATED (orphan stub)**: Coq `FtypeI_invDade_ortho_constant`
(PFsection12:417-419) は `{in H:\:H' &, rho psi x = rho psi y}` = **ρψ が H∖H' 上 const**
(H∖H' 内 2 点比較、ρψ=a という特定定数、line 457)。Lean stub `ψ(h)=ψ(1)` は **1∈H' の値**と比較で
別物。DpsiH 分解 `ρψ|_H = Σ a_A·Ind_{H'}^H χ_A + a·1_H` で確定: H∖H' 上 Ind 項は上記 lemma で消え
ρψ(h)=a、だが ρψ(1)=a+Σa_A[H:H']χ_A(1)≠a。∴ **ψ(h)=ψ(1) は偽**、正 = const on H∖H'。

**③ (12.5) deep-proof path**: DpsiH 分解 (o_rpsi_S = Dade reciprocity `tau_inner_eq_of_supported` +
Irr(H) の induced-from-H' 分割) → 上記 vanishing lemma で finish。induced-from-H' 分割 (Clifford)
が残 infra。**次: (12.5) statement を const-on-H∖H' に訂正 (orphan ゆえ lane-b 裁量) + DpsiH 組立**、
または (12.14)/(12.15) downstream char へ。

### loop¹³³ — ✅ (12.5) statement 訂正 + faithful Fourier 還元 landed (commit 7fd6f34d)

(12.5) `rho_constant_on_H_minus_Hprime` を **opaque sorry → 訂正 statement + 実証明還元** に:
- statement: `ψ(h)=ψ(1)` (偽) → **const on H∖H'** (∀ h1 h2∈H∖H', ψ h1=ψ h2、Coq 準拠)。0 consumer。
- 還元 (実証明): Fourier `Res_L ψ=γ+β` ((12.4) 同型)、**γ は H 全体で const 実証明**
  (`apply_mul_eq_of_mem_characterKernel`、各 H-kernel φ で φ(h)=φ(1))。残 sorry = **hβconst**
  (β const on H∖H') の 1 本のみに isolate。build green 3871 jobs。

**残 (12.5) core = hβconst**: β (off-H-kernel ∈ ℂ[S], S=Ind_H^L θ) が H∖H' で const。
Coq o_rpsi_S (horth ψ⊥R(χ) → 等次数 ξ の係数構造) + DpsiH (induced-from-H' 分解) →
`induce_apply_eq_zero_of_not_mem_normal` (loop¹³²) で finish。次: hβconst の S-structure +
Dade reciprocity (`tau_inner_eq_of_supported`) 接続を build。

**(12.5) 進捗**: 2 iteration で opaque sorry → [訂正 statement + γ 実証明 + isolate hβconst + vanishing infra]。
FT decomposition パターン (mechanical spine 実証明 + deep core を精密 isolate)。

### loop¹³⁴ — (12.5) hβconst 精密 decomposition roadmap (deep multi-iter build、既存 infra へ mapping)

hβconst (β const on H∖H') = Coq (12.5) 本体 (PFsection12:420-475) 精読。各 piece を既存 Lean infra へ mapping:
1. **o_rpsi_S** (⟨ρψ, ξ1-ξ2⟩=0、等次数 ξ∈S): Dade reciprocity `tau_inner_eq_of_supported`
   (S12_Core:3586) + coherence `pair_degree_coherence`/`mem_coherent_sum_subseq` + ψ⊥R (horth)。
2. **induced-from-H' 分割 P_i = constt(Ind_{H'}^H χ_i)** (trivIset + cover):
   - disjoint: **直接 route** = `inner_induce_eq_zero_of_not_conj` (InducedIrreducible:151、非共役⟹⟨Ind i1,Ind i2⟩=0)
     + 「直交指標は constituent 非共有」。単一軌道機構 (RestrictionConstituentsSingleOrbit) 不要。
   - cover: 各 j∈Irr(H) は Res_{H'} j に constituent i を持つ (Clifford) + Frobenius `inner_induce_eq_inner_restrict`。
   - constt_Ind_Res は `inner_induce_eq_inner_restrict` そのもの (wrapper 不要)。
3. **cfInd_central_Inertia** (Ind χ_i = e·Σχ_j): `exists_extension_induce_eq_sum_distinct_of_inertia_inf_le`
   (CliffordDecomposition:290) + `InertiaAbelianQuotient` 系。
4. **DpsiH assembly** (ρψ|_H = Σ a_A Ind χ_A + a·1): Fourier `cfun_sum_cfdot` + 上記。
5. **H∖H' vanish**: `induce_apply_eq_zero_of_not_mem_normal` (loop¹³², LANDED)。

∴ hβconst は **既存 infra から assemblable な multi-iteration build** (from-scratch でない)。(12.5) は orphan
ゆえ FT 即効値は低いが、partition/inertia は type-I char 全般の再利用 infra。
**次: partition disjointness lemma (直接 route) を build** → cover → DpsiH → o_rpsi_S。

### loop¹³⁵ — ✅ partition trivIset core landed (commit 822d37fa)

`exists_conj_of_common_induce_constituent` (CliffordSingleOrbit.lean、sorry-free): H⊴G で θ₁ θ₂∈Irr(H)
が共通 χ を Ind constituent に持てば G-共役。= induced-from-H' 分割の **trivIset core** (非共役⟹P_i disjoint)。
Clifford 単一軌道 + Frobenius の assembly。再利用 Clifford infra。build green 3298 jobs。

**(12.5) hβconst 進捗** (4 iter): vanishing lemma (¹³²) + statement 訂正/Fourier 還元 (¹³³) + roadmap (¹³⁴)
+ trivIset core (¹³⁵)。**次 = partition cover** (∀ j∈Irr(H), ∃ i∈Irr(H'), j lies over Ind i;
= Res_{H'} j ≠ 0 の constituent 存在) → partition 組立 → DpsiH → o_rpsi_S (Dade reciprocity)。
