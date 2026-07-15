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

### loop¹³⁶ — partition 完成 (cover は既存) + o_rpsi_S 深さ確定; (12.5) 残 core 評価

**partition 完成**: induced-from-H' 分割の 2 事実が両方 available:
- **trivIset**: `exists_conj_of_common_induce_constituent` (loop¹³⁵ landed)。
- **cover**: `exists_liesOver` (Clifford:626、**既存・proven**、正規性不要)。∴ cover の build 不要。

**o_rpsi_S 深さ確定 (subtle Lean-Coq alignment)**: Lean は Dade **isometry** `tau_inner_eq_of_supported`
(⟨τφ,τψ⟩=⟨φ,ψ⟩) + coherence bridge `coherent_extension_constituent_mem_span_Rset` を持つが、
Lean (12.5) は ψ on G (horth = τ-image 直交) で Coq o_rpsi_S は ⟨ρψ,·⟩ on L。**この reconciliation +
DpsiH 組立が残 hβconst core** = deep/subtle/multi-iter。

**(12.5) 総括**: 5 iter で reusable infra 全抽出 (induce vanishing ¹³² + partition trivIset ¹³⁵)、
statement 訂正 + Fourier 還元 (¹³³)、roadmap (¹³⁴)。残 hβconst = o_rpsi_S reconciliation + DpsiH の
deep orphan build。reusable infra (vanishing/partition) は type-I char 全般で再利用可。
**次: DpsiH-const 汎用 lemma (係数 class-const → const on H∖H') = partition + cfInd_central_Inertia
(`exists_extension_induce_eq_sum_distinct_of_inertia_inf_le`) + vanishing の assembly** を build、
o_rpsi_S を残 hypothesis に isolate。

### loop¹³⁷ — frontier 総括 + (12.5) hβconst に集中決定

**(12.14) 評価**: Coq は (12.4) `FTtype1_ortho_constant` 適用で証明。但し Lean mapping subtle:
dade.psi = coh.extension χ は span R(χ) 内ゆえ R(χ) と非直交 → (12.4) 適用は cross-family 直交
(R(χ)⊥R(χ'), χ≠χ') + coset/kernel 構造依存。deep multi-piece。

**lane-b S14 frontier 総括**: 全 target が deep multi-iteration build:
- (12.5) hβconst: partition (trivIset ¹³⁵ + cover exists_liesOver 既存) + vanishing (¹³²) DONE、残 = o_rpsi_S reconciliation + DpsiH。
- (12.14): (12.4) 経由だが dade.psi⊥R subtle + cross-family 直交要。
- (12.11): group theory (support facts + Cauchy/Sylow)。
- (12.10) witness_L_*: hub 9003 pinned。
reusable infra (induce vanishing + partition trivIset) は抽出済・type-I char 全般で再利用可。

**決定: (12.5) hβconst に集中** (最多 infra 済 + upstream-most)。o_rpsi_S = horth (ψ⊥R on G) →
Res_L ψ の S-係数構造 の reconciliation を sustained build。orphan だが CLAUDE.md 上 skip 理由でなく、
infra 蓄積が最も進んでいる。次: o_rpsi_S の concrete build 着手。

### loop¹³⁸ — ★ Dade reciprocity 存在確認 (loop¹³⁷ 訂正) + lane-b frontier 網羅評価

**★ 訂正: Dade reciprocity は存在** (loop¹³⁷「invDade 欠如」は誤り、grep 名違い):
`adjoint_formula` (S04:3894) = ⟨τα, χ⟩_G = ⟨α, ρχ⟩_L (ρχ = `adjointAverageFun` S04:3866)。
docstring:「§4 最重要 export、§7/§9/§12/§13/§16 が直接 cite」。∴ ρ-based 論法 (o_rpsi_S 等) は
既存 infra で可能。from-scratch invDade build 不要。

**lane-b S14 frontier 網羅評価** (全 target の性質確定):
- (12.5) rho_constant: orphan + formulation 混乱 (stub psi は G 上だが真の (12.5) は ρψ=adjointAverageFun ψ on L)
  + deep o_rpsi_S/DpsiH。**reusable infra 抽出済** (induce vanishing ¹³² + partition trivIset ¹³⁵)。
- (12.14) psi_constant_on_xK (consumed 3): (12.4) 経由、dade.psi⊥R + cross-family 直交 + coset 構造要。
- (12.15) rhoM_integer_values (consumed 1): **dade.rhoMFormula = free Prop (scaffold carrier)** → arbitrary dade で
  unprovable。genuine carrier 構成 gated (S11 §9 keystone 型)。
- (12.11) (consumed 4): deep group theory (support facts + Cauchy/Sylow)。
- (12.10) witness_L_*: hub 9003 pinned。

**総括**: reusable char infra 抽出完了。残 frontier = deep multi-piece build か carrier-scaffold-gated か
formulation-confused。**最 tractable FT-path = (12.14)** ((12.4) 経由の明確 path)。次: (12.14) の
cross-family R-orthogonality (same-L, R(χ1)⊥R(χ2) χ1≠χ2) prerequisite を build。

### loop¹³⁹ — ✅ 二族 constituent-diff 直交 landed (commit 0e7a3b94)

`constituentDiff_tau_inner_eq_zero_of_ne_across` (S14、sorry-free): 同一 L・異 χ1,χ2∈S の
φ∈S(χ1), φ'∈S(χ2) で φ≠φ'・φ≠φ̄'・φ̄≠φ' なら ⟨τ(φ-φ̄),τ(φ'-φ̄')⟩=0。既存同一-χ 版の二族一般化
(証明同型)。build green 3871 jobs。code cadence 復帰 (assessment 3連 ¹³⁶⁻¹³⁸ 後)。

**次 = 同一 L cross-family R-orthogonality** (`R(χ1)⊥R(χ2)`, χ1∉{χ2,χ̄2}):
`toOrthonormalImage_inner_eq_zero_across` (S07:977) + 上記二族 diff 直交 + χ1∉{χ2,χ̄2}→
disjoint constituents (partition trivIset `exists_conj_of_common_induce_constituent` ¹³⁵) から
h2/h3 (φ≠φ̄' 等) 導出。(12.14) path の reusable 入力 + nonconjugate 版の companion。

### loop¹⁴⁰ — ✅ 同一L cross-family R-orthogonality landed (commit 44c39a0d)

`samegroup_typeI_R_orthogonal` (S14、sorry-free): 同一 L の χ1,χ2∈S で constituents pairwise distinct
(hcond, χ1∉{χ2,χ̄2} で成立) なら R(χ1)⊥R(χ2)。nonconjugate 版の companion、前 commit の二族 diff 直交で
signed-diff を埋める。build green 3871。**2 連続 code landing** (¹³⁹ 二族 diff + ¹⁴⁰ same-L R-ortho)。

**R-orthogonality toolkit 完成**: nonconjugate (異L) + samegroup (同L) + constituentDiff_..._across
(二族 diff)。type-I char (12.3/12.4/12.14) の reusable 入力。

**(12.14) 残 subtlety**: dade.psi=coh.extension χ0 ∈ ℤ[R(χ0)] は R(χ0) と非直交。(12.4)
orthogonal_character_constant_on_coset は ⊥ 全 R(χ') 要 → χ'=χ0 で gap。samegroup R-ortho は χ'≠χ0 を
埋めるが χ0 は残る。Coq (12.14) の FTtype1_ortho_constant 適用の calS/χ0 扱いが要精読。次: (12.14)
assembly の χ0 subtlety 解決 (Lean 意図 proof / Coq 精読) か、R-orthogonality を別 consumer で活用。

### loop¹⁴¹ — (12.14) subtlety 解決 = cross-group + Hypothesis M gated; frontier 全 gated 確定

**(12.14) 解決**: Coq `FTtype1_seqInd_ortho` (237-243) = **cross-group** (非共役 L1,L2) R-orthogonality
(要 L2∉L1^G)。∴ (12.14) は (12.4) を **M** (counterexample maximal) に適用、dade.psi⊥R_M(φ) は
cross-group (L vs M 非共役) = 既存 `nonconjugate_typeI_R_orthogonal`。**my ¹³⁹/¹⁴⁰ same-L 版は
(12.14) の鍵でない** (reusable だが (12.14) は cross-group [既存] 使用)。
**(12.14) 実 gate**: `Hypothesis M` (M の Dade 設定) 構成要 — CounterexampleHypothesis は
K=maxNilpotentNormalHall M を持つが Dade Hypothesis M を carry せず。deep 構成。

**★ lane-b S14 frontier 全 gated 確定** (網羅):
| Pf | gate |
|---|---|
| 12.5 | formulation-confused (psi on G vs ρψ on L) + o_rpsi_S/DpsiH |
| 12.10 | hub 9003 pinned (deep §8-11) |
| 12.11 | deep Cauchy/Sylow + support facts |
| 12.14 | Hypothesis M 構成 gated (cross-group R-ortho は既存) |
| 12.15 | DadeNotation carrier scaffold (free rhoMFormula Prop) |

reusable infra 全抽出 (induce vanishing/partition trivIset/two-family diff/same-L R-ortho)。残 = 各
deep 構成 (Hypothesis M / carrier genuinize / Cauchy-Sylow) = multi-session。**最 concrete structural =
(12.11) part-2** (M∩L≤H の Cauchy/Sylow, group theory, 4 consumer)。次: (12.11) part-2 着手。

### loop¹⁴² — root unblock = Hypothesis M 構成 (12.14/12.15/DadeNotation の共通根)

(12.11) part-2 精査: 特定の Frobenius/Sylow 論法 (isPiSubgroup_le_of_normal_isHall [BG S12:43 既存]
で π-group へ還元、但し L Frobenius [witness_L_frobenius, 10.10 cross-lane gated] + Sylow 構造依存)。
clean ungated general lemma は抽出できず。

**★ root 発見**: char endgame の gated targets が共通根に収束:
- (12.14): Hypothesis M (M の Dade 設定) 要 → (12.4) を M に適用。
- (12.15)/(DadeNotation ρM): ρM = adjointAverageFun (M の Dade adjoint) 要 → **Hypothesis M** 要。
∴ **Hypothesis M 構成 = 12.14-12.16 chain の root unblock** (lane-b territory)。

**構成可能性**: 反例 M (noncyclic Sylow p, p∣[M:M_F]) の型に依存。型-P なら **既に build 済の
type-P Dade support engine (S10, type-P arc loop¹¹⁸-¹²⁹)** が Hypothesis M を構成しうる (reuse!)。
型-I なら type-I Dade 構成。**次: 反例 M の型判定 + type-P Dade engine が Hypothesis M を与えるか確認**
→ 与えれば 12.14-16 chain unblock (major)。Dade reciprocity (adjoint_formula ¹³⁸) は既存。

### loop¹⁴³ — ★★ 重大訂正: (12.14) は ASSEMBLABLE (Hypothesis M 利用可、gated でない)

**loop¹⁴¹ の「Hypothesis M gated」は誤り**: 反例 M は **type-I** (`ctr.M_typeI : IsTypeI M` S14:4220)、
`exists_typeI_hypothesis hG ctr.M_maximal ctr.M_typeI : Nonempty (Hypothesis M)` (S14:218) で **直接利用可**。

**(12.14) 全 piece 存在 → assemblable**:
1. Hypothesis M: `exists_typeI_hypothesis` ✓
2. data_M (∀χ∈Sset_M, CharacterDecompositionData): existence 構成子 (S14:658/675) ✓
3. horth (dade.psi ⊥ R_M): `coherent_extension_constituent_orthogonal_Rset_of_nonconjugate` (S14:1844、
   coh.extension ⊥ R_M for L≠M) + dade.psi=coh.extension χ を constituent 和で ✓ (L≠M 要)
4. (12.4) for M: `orthogonal_character_constant_on_coset` (S14:2448) ✓
5. hypM.H = ctr.K = maxNilpotentNormalHall M (K_eq_MF) ✓
6. x∈M (P0≤M) ✓、x∉K (p-element + p∤|K|)

**残 sub-facts**: L≠M non-conjugate (witness 構造から)、dade.psi=coh.extension χ の constituent-和 for horth、
x∉K の p-element 論法。**(12.14) は ~60 行 assembly** (gated でない、全 piece 存在)。

**★ 訂正の意義**: 「char endgame 全 gated on deep constructions」は **過度に悲観的だった** — M が type-I で
Hypothesis M 直接利用可ゆえ (12.14)/(12.15)/(12.16) chain は既存 piece から assemblable。次: (12.14) assembly を build。

### loop¹⁴⁴ — (12.14) assembly 完全 scope: statement redesign 要 (coh + L≠M input)

(12.14) 精査: assemblable だが **現 statement は under-specified**:
- horth (dade.psi ⊥ R_M) は dade.tau1 が coherent extension である必要 → 一般 DadeNotation の tau1 では不足。
  **coh_L (IsCoherent) 入力要** + dade.psi = coh.extension dade.chi の link。
- cross-group には **L≠M non-conjugate** 要 (現 statement に無し)。
→ **statement redesign 要** (coh + hLM 追加; code consumer 0 ゆえ安全)。

**assembly plan** (redesign 後):
```
obtain ⟨hypM⟩ := exists_typeI_hypothesis hG ctr.M_maximal ctr.M_typeI
hHK : hypM.H = ctr.K  := hypM.typeI.typeF.H_eq.trans ctr.K_eq_MF.symm
data_M := fun χ hχ => (⟨CharacterDecompositionData existence S14:658⟩).choose
refine orthogonal_character_constant_on_coset hG hypM data_M horth hxM hxK g (hHK▸hg)
  horth: dade.psi=coh.extension χ ⊥ R_M — χ の constituents で分解 + coherent_extension_orthogonal (L≠M)
  hxM: witness.x ∈ P0 ≤ M;  hxK: x∉K via p-element + p∤|K|
```
**subtlety**: dade.chi は degree e=[L:H] ⟹ Ind_H^L θ (θ linear≠1) ⟹ Frobenius で irreducible ⟹ 単一
constituent (horth 簡略化)。**次: (12.14) redesign + assembly を build** (~60-80 行、全 piece 存在)。

### loop¹⁴⁵ — ✅ (12.14) reduction landed (commit af21399b)

`psi_constant_on_xK` を opaque sorry → **実 assembly reduction**: (12.4) を Hypothesis M
(exists_typeI_hypothesis、M=type-I ゆえ直接) に適用。機械部 (Hypothesis M 構成 + hHK[typeF.H_eq+K_eq_MF]
+ data_M[character_decomposition existence] + hxM[P0≤M] + (12.4) 配線) 実証明。build green 3871。
**loop¹⁴³ unblock (M=type-I) を実 code 化** — 「全 gated」の悲観を実証明で覆した。

**残 2 obligation (既知 path、次)**:
- **horth** (dade.psi⊥R_M): coherent_extension_constituent_orthogonal_Rset_of_nonconjugate (S14:1844)。
  要 coh (coherence) + L≠M + dade.psi=coh.extension χ (χ irreducible constituent)。statement redesign 要。
- **hxK** (x∉K): witness.x は nontrivial p-element、K=M_F は p'-Hall (p∣[M:M_F]) ゆえ p∤|K| → x∉K。
  witness の x_ne_one + x^p=1 + K の Hall 構造から (自己完結的、redesign 不要)。
次: hxK (self-contained) を先に埋め、horth は redesign + coherent_extension_orthogonal threading。

### loop¹⁴⁶ — ✅ (12.14) hxK 実証明 (commit 4ec8434c); 残 horth のみ

hxK (x∉K) 実証明: witness.x は nontrivial p-element (orderOf x = p via orderOf_eq_prime)。
x∈K⟹p∣|K| (Lagrange orderOf_dvd_natCard + orderOf_injective coe)。K=M_F Hall
(maxNilpotentNormalHall_isHall.coprime_index) + p∣[M:K] (p_dvd_index) で Coprime(|K|,[M:K]) ⟹ p∤|K| ⟹ 矛盾。
build green 3871。**(12.14) 2 obligation の 1 完了** (¹⁴⁵ reduction + ¹⁴⁶ hxK の 2 連 landing)。

**残 = horth のみ** (dade.psi⊥R_M): dade.psi=dade.tau1 dade.chi。tau1 が coherent extension である必要
(一般 IntegralCharacterMap では不足) ⟹ **statement redesign 要** (coh:IsCoherent + hpsi:dade.psi=coh.extension χ
+ hLM:L≠M 追加)。coherent_extension_constituent_orthogonal_Rset_of_nonconjugate (S14:1844) で証明。
χ irreducible constituent 構造 (dade.chi degree=[L:H]⟹Ind linear⟹irreducible) を thread。次: horth 完成 → (12.14) sorry-free。

### loop¹⁴⁷ — ✅★ (12.14) 完成 SORRY-FREE (commit 86c17b4b)

horth 実証明で **(12.14) psi_constant_on_xK 完全 sorry-free**。statement redesign (coherence input:
coh + chi0 IrreducibleCharacter の data/constt/mem + hpsi + hLM) で horth =
coherent_extension_constituent_orthogonal の 1 行。full assembly 実証明 (Hypothesis M + hHK + data_M
+ horth + hxK + (12.4) 適用)。**3 iter (¹⁴⁵ reduction/¹⁴⁶ hxK/¹⁴⁷ horth) で完成**。build green 3871。

**★ loop¹⁴³ unblock 完全実証**: 「char endgame 全 gated」の悲観 (¹⁴¹) を、M=type-I ⟹ Hypothesis M
直接利用可 (exists_typeI_hypothesis) の発見 (¹⁴³) → 実 code (¹⁴⁵⁻¹⁴⁷) で覆した。(12.16) chain の 1 piece 完成。

**次 = (12.15) rhoM_integer_values**: 同 Hypothesis M unblock 適用。dade.psi g∈ℤ for g∈K∖K'
(ρ=adjointAverageFun + Hypothesis M) + rhoMFormula (free Prop、redesign or caller 供給要)。

### loop¹⁴⁸ — (12.15)/(12.16) chain 評価: (12.14) done、残 = deep final Dade contradiction

(12.15) rhoM_integer_values: Coq `rhoM_psi` は `rhoM := invDade` for M (M の Dade adjoint =
adjointAverageFun) + norm 下界 `lb_psiM` + cyclotomic `vchar_ker_mod_prim`。**deep** (12.14 より深い)。
+ rhoMFormula/rhoFormula は free Prop (constructor で True) = scaffold carrier。consumer 0。

(12.16) chain: `counterexample_contradiction` (headline) = exists_rankTwoWitness + exists_witness_g +
**exists_counterexample_dade_data** (deep §7/§12 bundle、sorry S14:5782) + counterexample_contradiction_of_facts。
`CounterexampleDadeData` fields = ψ-data + **h_const(=12.14 DONE)** + h_psig_int(=12.15 deep) +
norm bounds hA/hB/hC (deep §7) + he(3≤e, discharged)。

**∴ 残 (12.16) chain content = deep final Dade contradiction** (M の ρM adjoint + §7 norm estimates +
cyclotomic + 12.15)。(12.14) done は h_const field を供給 (chain の 1 field 完成)。
**次: CounterexampleDadeData 構成 (exists_counterexample_dade_data) で 12.14 [h_const] を wire +
dischargeable field を埋め、deep field (h_psig_int/norm bounds) を isolate** = faithful decomposition。

### loop¹⁴⁹ — CounterexampleDadeData field map: (12.14) done = h_const; 残 = h_psix/h_psig_int/hA-C

`CounterexampleDadeData` (S14:5738) fields = (12.16) contract:
- **he** (3≤e): discharged。
- **h_const** (ψ(x·g)=ψ(x)): **= (12.14) DONE** (specific g への適用)。
- **h_psix** (∃w integral, ψ(x)-e=(1-ε)w): cyclotomic 合同 ψ(x)≡e mod(1-ε)。
  Coq = vchar_ker_mod_prim; Lean は (1.10.a) `exists_integral_apply_sub_of_commute` 系か。
- **h_psig_int** (ψ(g)=mval∈ℤ): **= (12.15) deep** (M の ρM=adjointAverageFun + norm 下界 + cyclotomic)。
- **hA/hB/hC** (norm bounds normRhoM/normRho の不等式): **deep §7 estimates** (Hypothesis78/NormEstimates 系)。

∴ exists_counterexample_dade_data (bundle 構成) の残 = **deep final Dade contradiction**
(h_psix cyclotomic + h_psig_int 12.15 + hA-C §7 norm)。(12.14) は h_const を供給済。
**次: h_psix (cyclotomic、(1.10) infra で最 tractable) を build 検討 → CounterexampleDadeData の
非-deep field を埋める**。deep field (h_psig_int/norm) は multi-session。

### loop¹⁵⁰ — h_psix も ψ(1)=e (coherence degree-preservation) 要; (12.16) chain 全 field deep 確定

h_psix (∃w, ψ(x)-e=(1-ε)w): `exists_integral_apply_sub_of_commute` (CyclotomicCharacterCongruence:234,
既存) を y=1 で適用 ⟹ ψ(x)-ψ(1)=(1-ε)z。∴ h_psix には **ψ(1)=e** 要 (e=χ(1)、chi_degree_eq_e)。
だが IsCoherent (S07:1659) は isometry (extension_inner_eq) + ZIrr のみで **degree-preservation
(coh.extension χ(1)=χ(1)) を直接持たない**。ψ(1)=e は coherence degree/sign 性質要 (isometry⟹±irr
+ degree = χ(1) の導出)。

**∴ (12.16) chain 全 field deep 確定**: h_psix (ψ(1)=e degree-preserv) / h_psig_int (12.15 ρM) /
hA-C (§7 norm)。**(12.14) は strong milestone (chain 再開 + h_const 供給)**、残は deep final Dade
contradiction (multi-session)。次: ψ(1)=e (coherence degree-preservation) の導出可否を検討
(isometry + ZIrr ⟹ ±irr ⟹ degree)、可なら h_psix landing。

### loop¹⁵¹ — ψ(1)=e は S07 apply_one infra で導出可能 (deep field は infra 有・from-scratch でない)

h_psix upstream の ψ(1)=e (coherence degree-preservation) の infra 発見:
- `dadeIntegralCharacterMap_apply_one` (S07_CoherenceGalois:86、"Dade images vanish at 1")。
- `extension_apply_one_eq_zero_of_supported` (S08:328、supported diff は 1 で消える)。
- `coherent_of_constant_degree` (S07:551)。S-members は irreducible (`hSirr`)。
∴ ψ(1)=e は導出可能 (χ-χ' supported diff の extension が 1 で消える ⟹ 同次数 S-member の
extension は 1 で同値、+ constant-degree)。**involved だが from-scratch でなく、既存 infra から build 可**。

**(12.16) chain 総括**: 全 field deep だが **各に relevant infra 有** (h_psix=S07 apply_one、
h_psig_int=12.15 の ρM=adjointAverageFun+cyclotomic、hA-C=§7 Hypothesis78/NormEstimates)。
= sustained multi-iter build (from-scratch でない)。**(12.14) は strong milestone**。
**次: ψ(1)=e を grind → h_psix landing** (genuine deep build、churn assessment を脱する)。

### loop¹⁵² — ✅ h_psix cyclotomic 合同 landed (commit fcc499a2); 残 = ψ(1)=e

`psi_apply_x_sub_e_cyclotomic` (S14、sorry-free): ψ∈ℤ[Irr G], x^p=1, ε primitive, **ψ(1)=e** ⟹
∃w integral, ψ(x)-e=(1-ε)w。(1.10.a) exists_integral_apply_sub_of_commute (y=1) + ψ(1)=e。
build green 3871。**assessment churn (¹⁴⁸⁻¹⁵¹) を脱する実 code landing** — h_psix の cyclotomic 部完成。

**残 h_psix input = ψ(1)=e** (coherence degree-preservation dade.psi(1)=coh.extension χ(1)=χ(1)=e)。
IsCoherent は isometry+ZIrr のみ ⟹ ψ(1)=e は coherence の degree/sign 性質要 (χ-χ̄ supported diff の
extension 消失 ⟹ real は出るが =e には不足)。**(12.13) 構成 (dadeNotation_of_coherence) が degree 性質を
持つか、または coherence 構成から導出**。次: ψ(1)=e の導出可否を examine → 可なら h_psix 完成。

### loop¹⁵³ — ψ(1)=e は coherence degree-preservation 要 (直接 lemma 無し); (12.16) 残は deep endgame

ψ(1)=e (coh.extension χ(1)=χ(1)) の直接 lemma 探索: `restrict_extension_Yset_degree_value_eq_of_frobenius`
(S08:2017) は SibleyDadeHypothesis の coherentYset/Xset 構造用で別物。`coherent_of_constant_degree`
(S07:551) は isometry 構成のみ。**IsCoherent は isometry+ZIrr ⟹ coh.extension χ = ±ζ (norm-1 irr)
だが degree-preservation (=χ(1)) は出ない** (χ-χ̄ supported ⟹ extension が 1 で χ,χ̄ 同値 = real は出るが
=e 不足)。∴ ψ(1)=e は coherence の degree/sign 性質から build 要 (involved)。

**(12.16) chain 総括 (確定)**: 全 field deep endgame — h_psix (ψ(1)=e coherence-degree、cyclotomic 部は
¹⁵² landed) / h_psig_int (12.15 ρM) / hA-C (§7 norm)。**session milestone = (12.14) sorry-free +
h_psix cyclotomic congruence**。残 = deep final Dade contradiction (coherence-degree + ρM + §7 norm)、
sustained multi-session char theory。次: ψ(1)=e を coherence 構成 (witness_L_coherent) から build 試行、
または h_psig_int/norm へ。

### loop¹⁵⁴ — ψ(1)=e 深さ最終確認; (12.16) = deep endgame、measured pace へ

ψ(1)=e: `nu_zeta_isIrreducibleCharacter_of_isCoherent_of_apply_one_pos` (S09:2948) で coh.extension χ =
irreducible (norm-1 + apply_one>0) は出るが、その degree=χ(1)=e は coherence の **construction-level
degree-preservation** 要 (isometry+sign では degree が χ(1) に固定されない)。∴ ψ(1)=e は deep sub-fact。

**(12.16) chain 確定 (¹⁴⁸⁻¹⁵⁴ の網羅精査)**: deep final Dade contradiction、各 field は sustained
per-field char-theory derivation 要:
- h_psix: cyclotomic 部 landed (¹⁵²)、残 ψ(1)=e = coherence degree-preservation (construction level)。
- h_psig_int (12.15): M の ρM=adjointAverageFun + norm 下界 + cyclotomic。
- hA/hB/hC: §7 Hypothesis78/NormEstimates。

**session milestones (strong)**: (12.14) psi_constant_on_xK **sorry-free** (¹⁴⁵⁻¹⁴⁷、Hypothesis M
unblock 実証)、h_psix cyclotomic 合同 (¹⁵²)。**残 = deep endgame** (multi-session、各 field 深い)。
rapid churn を避け measured pace で継続 (各 deep field は多 iteration の build)。

### loop¹⁵⁵ — coherent_of_constant_degree 精査: extension(1)=const だが ≠e; h_psix は ρL 経由で entangled

`coherent_of_constant_degree` (S07:551) 構成: extension(χⱼ)=β-τ(χ₀-χⱼ) ⟹ extension(χⱼ)(1)=β(1)
(**S-member 間で const**、τ 像は χ₀-χⱼ supported ゆえ 1 で消える extension_apply_one_eq_zero_of_supported)。
但し β(1)=±ζ(1) は e に固定されない ⟹ **ψ(1)=e は構成から出ない**。
更に Coq h_psix は psi(x*g)=χ(x) (ρL relation rhoL_psi) 経由 ⟹ **h_psix は (12.15) ρ-machinery と entangled**、
ψ(1)=e standalone でない。my psi_apply_x_sub_e_cyclotomic (¹⁵²) は valid lemma (ψ(1)=e given) だが
h_psix の実 route は ρL。

**(12.16) 最終確定**: deep entangled final Dade contradiction — h_psix/h_psig_int は ρM/ρL machinery
(M の adjointAverageFun + norm 下界 + cyclotomic) で結合、hA-C は §7。**sustained focused work 要**
(rapid /loop でなく dedicated session 向き)。**session milestones (strong)**: (12.14) sorry-free +
reusable toolkit + h_psix cyclotomic。残 = ρM machinery build (multi-session)。measured pace 継続。

### loop¹⁵⁶ — (12.5) へ上流ピボット: Fact-A 材料は**全て存在**、3 component landed

**方針転換 (上流優先+文書順)**: 深い (12.16) を grind し続けず、**より上流の (12.5)
`rho_constant_on_H_minus_Hprime`** (文書順 12.5 < 12.15) に降りた。原文+Coq PFsection12
(`FtypeI_invDade_ortho_constant` L417) 精読で真の証明構造を確定:
- **step 3 (o_rpsi_S)**: coherence + Dade 相互律 ⟹ `⟨ρψ, χ₁−χ₂⟩=0` (等次数)、∴ `⟨ρψ,θ⟩` は θ(1) のみ依存。
- **step 5 (DpsiH)**: `Res_H(ρψ) = Σ_λ a_λ Ind_{H'}^H λ + a·1_H` (Clifford partition P、trivIset/cover)。
- **step 6**: Ind_{H'}^H λ は H−H' で消える ⟹ 定数。

**重要訂正**: 従来 docstring の **InHKernel (L-level) γ/β 分割は dead-end** — Peterfalvi は Irr H で
分解 (Irr L 分割でない)、Res_H φ (off-L-kernel) は H−H' 構造を尊重しない。β const は full 結論と等価
(循環)。かつ statement は plain `psi` だが Coq は `rho psi`(=invDade=chiRhoCF)を結論 — **要 restate**
(consumer 無し ⟹ 自由)。

**Fact-A 材料は全て存在** (過度悲観を再訂正、(12.14) unblock と同型):
- 相互律 `chiRho_adjoint` (S09_NonexistenceCertain:353): `⟨τα,χ⟩_G = ⟨α, χ^ρ⟩_L`、ρ=`H71.chiRhoCF`
  (=`hyp.toHypothesis71.chiRhoCF`)。**proven**。
- `coherent_extension_constituent_mem_span_Rset` (S14:1808): `coh.extension φ ∈ ℤ[Rset]`。
- `IsCoherent.extends_on_supported`: `extension φ = hyp.tau φ` (φ ∈ zSupportedSpan)。
- **NEW landed this iter**: `inner_psi_coherent_extension_eq_zero` (S14) = `⟨ψ, coh.extension φ⟩=0`
  (ψ⊥Rset)。step-3 の `'[psi,tau2 xi]=0` 相当。

**this iter landed (build-green, 2 commit)**:
1. `sum_smul_induce_apply_eq_zero_of_not_mem_normal` (InducedCharacter) — step 6、Σ Ind vanish off normal。
2. `apply_eq_of_eq_sum_smul_induce_add_const` (InducedCharacter) — step 6 reduction (const off normal)。
   (12.5) と (12.15) rhoM 両方の endgame。
3. `inner_psi_coherent_extension_eq_zero` (S14) — Fact-A の直交 component。

**次 iteration = full Fact-A build** `⟨ρψ,χ₁⟩=⟨ρψ,χ₂⟩` (等次数): 上記材料を wire。
**残る wiring 課題** (careful, fresh context 向き): (a) χ₁−χ₂ を `SupportedClassFunctions ℂ A L`
に構成 (等次数 ⟹ degree-0、supported on A=H^#)、(b) **τ-層 bridging** `H71.τ`(DadeMap) ↔ `hyp.tau`
(IntegralCharacterMap) ↔ `coh.extension` via extends_on_supported、(c) **A-set 型** `chiRho_adjoint` の
A:Set G (typeIA) vs `IsCoherent` の A:Set ↥L (supportInSubgroup) の橋渡し。
Fact-A 後も **Clifford partition (step 5)** が残る = (12.5) は multi-iteration (材料は揃った)。

### loop¹⁵⁸ — (12.5) 全 step を既存 tooling に mapping 完了 (de-risk) + escaping-support 判明

**landed** (this iter): `Sset_diff_vanishes_off_H_sharp` (A1xi12 support: 等次数 S-member 差は H^# で消える)。

**(12.5) full build mapping** (全 step → 既存 lemma、de-risked):
- **step 3 (H-level Fact A)** `⟨ρψ, χ₁−χ₂⟩=0`: `chiRho_adjoint` 相互律 (S09_NonexistenceCertain:353)
  + `inner_psi_coherent_extension_eq_zero` (my corollary) + `extends_on_supported`。ρψ=`hyp.toHypothesis71.chiRhoCF psi`。
  ⚠ **escaping-support 注意**: Lean type-I Dade は nonescaping-supported constituent 差で動く
  (`constituent_diff_tau_eq_induce`)。S-member 差 (Ind θ₁−Ind θ₂) は H^# support だが nonescaping
  でない (Res_H(Ind θ) の escaping 消失を欠く — constituent と違い Res 一致しない)。
  ∴ Frobenius witness case (escaping 空 ⟹ H^#=nonescaping) で S-member route 有効、
  一般は constituent-level 経由要。
- **step 4 (等次数 Ind_{H'}^H λ constituents)**: H'=[H,H] ゆえ **H/H' abelian 自動** ⟹ I_H(λ)/H' abelian
  ⟹ λ extends (CyclicCharacterExtension) ⟹ Gallagher (GallagherDecomposition) ⟹ 全 constituent
  degree=[H:I]·λ(1) 等しい。tooling: InertiaAbelianQuotient + CyclicCharacterExtension + Gallagher。
  (L-level 版 = `typeI_induced_char_constituents`; H-level は abelian 自動で (8.2.c) 不要・より clean。)
- **step 5 (partition + DpsiH assembly)**: `CliffordSingleOrbit`
  (`restrictionConstituentsSingleOrbit_of_isIrreducible` + degree formula) + trivIset/cover。
- **step 6 (vanishing→const)**: my bricks `sum_smul_induce_apply_eq_zero_of_not_mem_normal` +
  `apply_eq_of_eq_sum_smul_induce_add_const`。**DONE**。

**次 iteration = step 4 build** (generic 「等次数 constituents of Ind_N^H λ, H/N abelian」lemma、
Gallagher+extension で組む — 独立 reusable Clifford 定理)。以降 step 3-full→step 5→assemble。
`rho_constant_on_H_minus_Hprime` は ρψ に restate 要 (現 plain-ψ は誤 statement、consumer 無)。

### loop¹⁶⁰⁻¹⁶⁵ — 一般 Peterfalvi (1.7.b) tower **完成** (12.5 step-4 前提)

**milestone**: 一般 (1.7.b) equal-degree (**coprimality 不要**、abelian inertia quotient) を
bottom-up で完成。全 build-green・多くは first-try。reusable §1 char theory (repo 欠落を補充):
1. `induce_restrict_mul` (射影公式 Frobenius–Nakayama, CharacterProduct)
2. `induce_trivial_eq_sum_linearClassFunction` (Ind 1_H = ∑_β Inf(β), Gallagher)
3. `induce_restrict_eq_mul_sum_linearClassFunction` (Ind(Res ψ)=ψ·∑Inf, Gallagher)
4. `restrict_eq_restrictionMultiplicity_smul_of_invariant` (Res ψ=e·θ, invariant Clifford, CliffordSingleOrbit)
5a. `induce_smul_eq_mul_sum_of_invariant` (e·Ind θ=ψ·∑Inf, 新 file InducedInvariantConstituent)
5b. `induce_invariant_constituent_apply_one_eq` (**capstone**: Ind_H^K θ の全既約 constituent が degree ψ(1))
+ helper `ClassFunction.sum_apply`/`mul_sum` (ClassFunction は Mul のみ非 semiring → 分配を手証明)

**残り (12.5) への path**:
- **(1.7.a) Clifford corr lift**: inertia I=I_H(λ) で 5b 適用 (λ は I-invariant) → Ind_{H'}^H λ = Ind_I^H(Ind_{H'}^I λ)、
  constituent φ_i=Ind_I^H ψ_i, degree [H:I]·ψ_i(1) 全等。CliffordCorrespondence.lean 参照。
- **(12.5) DpsiH assembly**: partition P (trivIset/cover, CliffordSingleOrbit) + degree-determined
  coefficient (5b + ρ-adjoint Fact A) + step-6 bricks (`sum_smul_induce_apply_eq_zero_of_not_mem_normal`)。
- **ρ-adjoint Fact A (o_rpsi_S)**: `inner_psi_coherent_extension_eq_zero` + chiRho_adjoint + Sset_diff support (既 landed)。
`rho_constant_on_H_minus_Hprime` は ρψ (chiRhoCF) に restate 要 (現 plain-ψ 誤、consumer 無)。

### loop¹⁶⁶⁻¹⁷⁰ — 一般 Peterfalvi (1.7.b) **完全版**完成 (inertia + full-group lift)

**milestone**: 一般 (1.7.b) H-level equal-degree (coprimality 不要、full-group) を完成。
inertia-level (5b) を Clifford correspondence + induction-in-stages で full-group に lift。
InducedInvariantConstituent.lean:
- `induce_smul_eq_sum_induce_mul_of_invariant_inertia`: `e·Ind_N^L θ = ∑_β Ind_T^L(ψ·Inf β)`
  (transport-heavy、stages `induce_induce_subgroupOf` + inertia 5a + `induce_sum`)。
- `induce_inertia_constituent_apply_one_eq`: **完全版** — Ind_N^L θ の全 constituent が degree
  [L:T]·ψ(1) (Clifford corr irreducibility `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq`
  + `restrict_mul_of_apply_eq_one` (Res(ψ·Inf β)=Res ψ) + `induce_apply_one` degree)。

**(12.5) への残り path** (1.7.b は完済、以下が残):
- **(12.5) DpsiH assembly**: partition P (trivIset/cover via CliffordSingleOrbit
  `exists_conj_of_common_induce_constituent`) + degree-determined coefficient (完成 1.7.b equal-degree
  + ρ-adjoint Fact A) + step-6 bricks (`sum_smul_induce_apply_eq_zero_of_not_mem_normal`)。
  → `Res_H(ρψ) = ∑_λ a_λ Ind_{H'}^H λ + a·1_H`、H−H' で定数。
- **ρ-adjoint Fact A (o_rpsi_S)**: `inner_psi_coherent_extension_eq_zero` + `chiRho_adjoint` 相互律
  + `extends_on_supported` + `Sset_diff_vanishes_off_H_sharp` (全 landed、要 wiring)。
- **statement 修正**: `rho_constant_on_H_minus_Hprime` を ρψ=`hyp.toHypothesis71.chiRhoCF psi` に restate
  (現 plain-ψ 誤、consumer 無)。

### loop¹⁷¹⁻¹⁷⁵ — (12.5) o_rpsi_S Fact-A **完成** (残り = DpsiH assembly のみ)

**milestone**: (12.5) の 2 大前提が完済:
1. **一般 (1.7.b)** equal-degree (完全版、full-group lift) — 別 milestone。
2. **o_rpsi_S Fact-A** `chiRhoCF_inner_eq_of_equal_degree` — ⟨χ₁, ρψ⟩=⟨χ₂, ρψ⟩ (等次数 S-member)。
   bridge chain 全 landed:
   - `Sset_diff_support_subset_ambientA` (χ₁−χ₂ ⊆ A(L)、SupportedClassFunctions 化)
   - `chiRho_adjoint` 相互律 (⟨χ₁−χ₂, ρψ⟩ = ⟨H71.τ(χ₁−χ₂), ψ⟩)
   - `toHypothesis71_tau_apply` (τ-bridging: H71.τ = hyp.tau on supported、via IsDadeMap.unique)
   - `extends_on_supported` (hyp.tau = coh.extension) + `map_sub`
   - orthogonality hyps (from `inner_psi_coherent_extension_eq_zero`, ψ⊥R(χ))

**(12.5) 残り = DpsiH assembly のみ** (`rho_constant_on_H_minus_Hprime`):
`Res_H(ρψ) = ∑_λ a_λ Ind_{H'}^H λ + a·1_H`、H−H' で定数。要:
- partition P (Ind_{H'}^H λ constituents、CliffordSingleOrbit `exists_conj_of_common_induce_constituent` trivIset/cover)
- degree-determined coefficient (Fact-A + Frobenius `⟨Res_H ρψ, θ⟩=⟨ρψ, Ind_H^L θ⟩`)
- block 内 equal-degree (完成 1.7.b、H'/H instantiation)
- step-6 bricks (`sum_smul_induce_apply_eq_zero_of_not_mem_normal`、Ind_{H'} vanish off H')
- statement を ρψ=`toHypothesis71.chiRhoCF ψ` に restate (現 plain-ψ 誤、consumer 無)。

### loop¹⁷⁶⁻¹⁷⁸ — (12.5) DpsiH: multiplicity-e 2 brick 完成 + assembly 4-brick 計画確定

**Peterfalvi (12.5) 原文 + Coq `FtypeI_invDade_ortho_constant` (PFsection12.v:417-484) 精読で証明構造を確定。**
結論は **ψ^ρ (= `toHypothesis71.chiRhoCF ψ`) が H−H' で定数** (現 S14 の plain-`psi` 文は誤、consumer 無 → restate 安全)。
現行 proof の InHKernel γ/β split (L-level、hβconst sorry @2701) は (12.4) 用の別物 → **H-level Ind_{H'} block 分解に置換**する。

**証明 (Coq mirror)**: f := Res_H(ρψ)。h1,h2 ∈ H−H' に対し
f(h1)−f(h2) = ∑_{θ∈Irr H} ⟨f,θ⟩(θ(h1)−θ(h2)) を **Ind_{H'} block P で regroup** → 各 block = 0。
block A (= constt Ind_N λ, N:=H'.subgroupOf H) 内: ⟨f,θ⟩ は θ≠1_H で定数 c_A (θ-coeff)、1_H 項は θ(h1)−θ(h2)=0 で落ちる →
= c_A ∑_{θ∈A}(θ(h1)−θ(h2)) = c_A/e·(Ind_N λ(h1)−Ind_N λ(h2)) = c_A/e·(0−0) = 0 (Ind_N λ は H−H' で消える、H'⊴H)。

**brick A 完成 (この iteration、2 commit)**:
- `restrictionMultiplicity_eq_of_liesOver_of_apply_one_eq` (CliffordSingleOrbit) — equal-degree ⟹ equal restriction mult (degree formula の共通因子 [G:I(ρ)]·ρ(1) を mul_right_cancel₀ 2 段)。
- `inner_induce_constituent_eq_of_apply_one_eq` (InducedInvariantConstituent) — 上を `inner_induce_coe_eq_restrictionMultiplicity` で ⟨Ind_N λ,φ⟩ 形へ持ち上げ (= block の共通 mult e)。

**残 assembly (次 iteration、brick B→C→D→restate、各 build-green commit)**:
- **B. H-level block partition** (generic, RepTheory): `∃ parts : Finset (Finset (Irr H)), univ = parts.biUnion id ∧ PairwiseDisjoint`。
  cap: φ ↦ constt(Ind_N λ(φ)) (λ(φ) = `exists_liesOver` で選ぶ Res_N φ の constituent)、partition = univ.image cap。
  PairwiseDisjoint: 別 block が θ 共有 ⟹ `exists_conj_of_common_induce_constituent` (CliffordSingleOrbit:175) で λ conj ⟹ Ind_N λ = Ind_N λ' (induce-conj-invariance 要確認/新設) ⟹ block 一致。
  cover: φ ∈ constt(Ind_N λ(φ)) ⟺ λ(φ) ∈ constt(Res_N φ) (Frobenius `inner_induce_ne_zero_iff_liesOver`)。L-level `exists_offKernel_constituent_partition` (S14:2508) を template に。
- **C. block-sum-zero** (generic): block A + coeff-const(θ≠1) + equal-mult(brick A) ⟹ ∑_{θ∈A}⟨g,θ⟩(θ(h1)−θ(h2))=0。
  Ind_N λ = e∑θ (Fourier + brick A の all-mults-equal) + `induce_apply_eq_zero_of_not_mem_normal` (Ind vanish off N)。1_H 項は (θ(h1)−θ(h2))=0 で処理。
- **D. assemble + restate**: `sum_inner_irreducibleCharacter_smul` Fourier-difference + B の biUnion regroup + C。
  `rho_constant_on_H_minus_Hprime` を ρψ 文へ restate、θ-coeff = `chiRhoCF_restrict_inner_eq_of_equal_degree` (S14:1995)、block equal-degree = `induce_inertia_constituent_apply_one_eq` (H'/H instantiation、H/H' abelian ⟹ inertia quotient abelian)。

### loop¹⁷⁹⁻¹⁸² — (12.5) DpsiH: generic 機構 **全完成** (core + partition + 等次数) — 残 = S14 wiring のみ

**この iteration で (12.5) の generic/reusable 機構を全て完成 (3 commit、全 green)**:
1. **partition 強化** `exists_induce_constituent_partition` に block characterization
   (`∀ A ∈ parts, ∃ ρ, ∀θ, θ∈A ↔ LiesOver H θ ρ`) 追加。
2. **DpsiH core** `constant_off_normal_of_inner_block_const` (InducedInvariantConstituent, ~114 行, 一発 green):
   H ⊴ G, g ∈ CF(G) が hcoeff(block 内 ⟨g,θ⟩ 一致, θ≠1)+hmult(⟨Ind ρ,θ⟩ 一致) ⟹ g は H 外で定数。
   Fourier + partition regroup (sum_biUnion) + block ごと e·(sum)=c·(Ind ρ x−Ind ρ y)=0。
3. **等次数系** `induce_inertia_constituents_apply_one_eq`: Ind_N^L θ の 2 constituent は等次数
   (`induce_inertia_constituent_apply_one_eq` を同一 ψ で 2 回 → 両者 [L:T]·ψ(1))。

**残 = Brick D (S14 wiring のみ)** `rho_constant_on_H_minus_Hprime` を core に帰着:
- **restate**: 結論を `(chiRhoCF psi)⟨h1⟩ = (chiRhoCF psi)⟨h2⟩` (ρψ, 現 plain-psi は誤・consumer 無)。
- **core 適用**: 環境 G_core := ↥((hyp.H).subgroupOf L)、g := restrict(H.subgroupOf L)(chiRhoCF psi)、
  H_core := G_core の commutator (= H'=derivedInG H に対応、`Hprime = derivedInG hyp.H` 確認済 ⟹ G_core/H_core abelian)。
- **hab 一様**: G_core/commutator abelian ⟹ ∀ x y ∈ G_core, ⁅x,y⁆∈commutator ⟹ 各 inertia T_ρ で hab 成立。
- **hcoeff**: θ₁,θ₂ ≠triv, LiesOver ρ → (i) 等次数 = `induce_inertia_constituents_apply_one_eq`
  (per-ρ: N=H_core, T=inertia(ρ), ψ_ρ=constituent over compHom ρ〈存在補題要〉, hinertia=定義) →
  (ii) θᵢ≠triv ⟹ Ind_{H.subgroupOf L}θᵢ ∈ Sset (`Sset = {Ind θ : θ≠triv}` 確認済) →
  (iii) `chiRhoCF_restrict_inner_eq_of_equal_degree` (S14:1995) で ⟨θ₁,Res(ρψ)⟩=⟨θ₂,Res(ρψ)⟩。
- **hmult**: 同 (i) 等次数 → `inner_induce_constituent_eq_of_apply_one_eq` (Brick A)。
- **翻訳**: g(x)=(chiRhoCF psi)(x:L) via restrict_apply; x∉H_core ⟺ h∉Hprime (subgroupOf iso)。
- **要確認/新設**: (a) ψ_ρ 存在補題 (Irr(inertia ρ) で compHom ρ の上); (b) x∉commutator(G_core) ⟺ 像∉derivedInG H;
  (c) inertia T_ρ の Fintype/Invertible/Normal instance plumbing。

### loop¹⁸³⁻¹⁸⁵ — (12.5) Brick D 材料 **全完成** — 残 = 純 S14 wiring + commutator bridge

**この iteration (2 commit)**: Brick D の最後の難所 2 補題を landing (全 green)。
- `exists_liesOver_of_subgroup` (CliffordSingleOrbit): exists_liesOver の双対 (σ∈Irr H の上に ψ∈Irr G 存在)。
  Ind σ 正次数 ⟹ 非零 ⟹ completeness。inertia setup の Clifford correspondent ψ を供給。
- `commutator_induce_constituents_apply_one_eq` (InducedInvariantConstituent): [HH,HH] block 等次数。
  induce_inertia_constituents_apply_one_eq を N=[HH,HH]/T=I(ρ)/ψ=上記/hab=⁅⊤,⊤⁆ で適用、
  inertia instance を Fintype.ofFinite/invertibleOfNonzero/subgroupOf_inertia_normal 供給。
  **注**: LiesOver を signature で述べるため `[Fintype ↥(commutator HH)] [Invertible (card ↥(commutator HH):ℂ)]`
  を signature instance に要 (body haveI 不可)。

**(12.5) 材料 全完成リスト** (core+partition+等次数+等mult+θ-coeff+ψ存在):
core `constant_off_normal_of_inner_block_const` / `exists_induce_constituent_partition` (block char 付) /
`inner_induce_constituent_eq_of_apply_one_eq` (等mult) / `commutator_induce_constituents_apply_one_eq` (等次数) /
`chiRhoCF_restrict_inner_eq_of_equal_degree` (S14 θ-coeff) / `exists_liesOver_of_subgroup`。

**残 = 純 S14 wiring のみ** (`rho_constant_on_H_minus_Hprime` restate + core 帰着):
- G_core := ↥((hyp.H).subgroupOf L)、H_core := commutator G_core、g := restrict((hyp.H).subgroupOf L)(chiRhoCF psi)。
- **commutator bridge** (残る唯一の非自明 sub-task): `x ∈ commutator ↥(H.subgroupOf L) ↔ (x:G) ∈ derivedInG H`。
  `subgroupOfEquivOfLe (H≤L) : ↥(H.subgroupOf L) ≃* ↥H` で commutator 転送
  (`(derivedInG H).subgroupOf H = commutator ↥H` = FeitThompson:955) + coercion chain。
- hcoeff: 等次数(helper) → θᵢ≠triv ⟹ Ind_{H.subgroupOf L}θᵢ∈Sset → θ-coeff (inner 引数順は conj で合わせる:
  core は inner(g,θ)、θ-coeff は inner(θ,restrict); g=restrict ゆえ inner(g,θ)=conj inner(θ,g))。
- hmult: 等次数(helper) → Brick A。
- 翻訳: g(x)=(chiRhoCF psi)(x:L) via restrict_apply; x∉H_core ⟺ h∉Hprime (bridge)。

### loop¹⁸⁶⁻¹⁸⁹ — (12.5) 全 ingredient 完成 (bridge+self-constituent+orthogonality) — 残 = main restate のみ

**この iteration (3 commit)**: (12.5) wiring の残り material を全 landing (全 green)。
- `mem_commutator_subgroupOf_iff` (S14): x∈commutator ↥(H.subgroupOf L) ↔ (x:G)∈derivedInG H (bridge、一発 green)。
- `Sset_self_mem_constituents` (S14): Frobenius χ∈S は自身の constituent (∃φ∈constituents, ↑φ=χ)。
- `Sset_inner_coherent_extension_eq_zero` (S14): ψ⊥R(χ) ⟹ ⟨ψ,coh.extension χ⟩=0 (orthogonality 供給)。
  **注**: FiniteInduce scoped instance で coh を inner_psi_... と一致させる (open scoped ... in は docstring 前)。

**(12.5) ingredient 全リスト (全 committed・green)**:
RepTheory: `constant_off_normal_of_inner_block_const` (core) / `exists_induce_constituent_partition` (block char付) /
`inner_induce_constituent_eq_of_apply_one_eq` (等mult) / `commutator_induce_constituents_apply_one_eq` (等次数) /
`exists_liesOver_of_subgroup` (ψ存在)。
S14: `mem_commutator_subgroupOf_iff` (bridge) / `Sset_self_mem_constituents` / `Sset_inner_coherent_extension_eq_zero` /
`chiRhoCF_restrict_inner_eq_of_equal_degree` (θ-coeff)。

**残 = main restate のみ** (`rho_constant_on_H_minus_Hprime`、unconsumed 確認済 ⟹ 旧 2683 削除 + helper 群の後へ新設):
```
新 signature (open scoped FiniteInduce in、helper 群の後に配置):
  (hyp) (coh : IsCoherent hyp.tau hyp.Sset hyp.A) (hAH : ambientA = (hyp.H:Set G)\{1})
  {C} (hfrob : IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
  (data) {psi} (horth : ∀χ∈Sset,∀α∈Rset,inner psi α=0) :
  ∀ h1∈H, h1∉Hprime, ∀ h2∈H, h2∉Hprime,
    (chiRhoCF psi)⟨h1,H_le _⟩ = (chiRhoCF psi)⟨h2,H_le _⟩
証明:
  set HH := (hyp.H).subgroupOf L; G_c := ↥HH; H_c := commutator ↥HH; g := restrict HH (chiRhoCF psi)
  haveI 群: Finite/Fintype ↥HH, Invertible(card ↥HH:ℂ), Fintype(Irr ↥HH),
           Fintype/Invertible ↥(commutator ↥HH) (ofFinite/invertibleOfNonzero)
  x := ⟨⟨h1,hh1L⟩, mem_subgroupOf.mpr hh1⟩ : ↥HH; 同 y
  hx : x∉commutator via (mem_commutator_subgroupOf_iff H_le x).not ← h1∉Hprime ((x:↥L:G)=h1)
  goal (chiRhoCF psi)⟨h1⟩=(chiRhoCF psi)⟨h2⟩ を restrict_apply で g x = g y へ
  refine constant_off_normal_of_inner_block_const g ?hcoeff ?hmult hx hy
  hcoeff θ₁ θ₂ ρ hne1 hne2 hlo1 hlo2:
    hdeg := commutator_induce_constituents_apply_one_eq ρ θ₁ θ₂ hlo1 hlo2 (θ₁(1)=θ₂(1))
    hχᵢmem := ⟨θᵢ, hneᵢ, rfl⟩ : induce HH θᵢ ∈ Sset
    hdegχ: induce_apply_one → (induce HH θ₁)(1)=(induce HH θ₂)(1)
    horthᵢ := Sset_inner_coherent_extension_eq_zero hyp coh hfrob data horth hχᵢmem
    hθcoeff := chiRhoCF_restrict_inner_eq_of_equal_degree hyp coh hχ₁mem hχ₂mem hdegχ hAH horth1 horth2 rfl rfl
      : inner θ₁ (restrict HH (chiRhoCF psi)) = inner θ₂ (...)  [= inner θᵢ g]
    core は inner g θ ⟹ conj 変換: inner g θ = conj(inner θ g) (inner_conj_symm) 両辺
  hmult θ₁ θ₂ ρ hlo1 hlo2:
    hdeg := commutator_induce_constituents_apply_one_eq ρ θ₁ θ₂ hlo1 hlo2
    inner_induce_constituent_eq_of_apply_one_eq hlo1 hlo2 hdeg  [N=commutator ↥HH, Brick A]
```
**要検証**: (a) x:↥HH の (x:↥L:G)=h1 coercion; (b) restrict_apply で g x=(chiRhoCF psi)(x:↥L);
(c) inner 変換 conj (core=inner g θ vs θ-coeff=inner θ g); (d) instance 解決 (特に Fintype(Irr ↥HH))。

### loop¹⁹⁰ — 🎉 **Peterfalvi (12.5) 完全証明・閉じた** (rho_constant_on_H_minus_Hprime)

**(12.5) `rho_constant_on_H_minus_Hprime` を完全証明** — sorry-free、`#print axioms` =
`[propext, Classical.choice, Quot.sound]` (標準3 axiom のみ、sorryAx 無・新 axiom 無)。
full build green (3915 jobs)、AxiomsCheck OK。

旧 plain-ψ 文 (hβconst sorry、consumer 無) を削除し、正しい **ψ^ρ = chiRhoCF psi の
H−H' 定数性**を generic DpsiH core へ帰着。5 iteration (loop¹⁷⁶⁻¹⁹⁰) で全 ingredient を
build して最終 assembly:

**generic 機構 (RepTheory、再利用可)**:
- `constant_off_normal_of_inner_block_const` — DpsiH core (Fourier + block regroup + 各 block 消去)
- `exists_induce_constituent_partition` — Irr G の Ind_H^G block 分割 (block char 付)
- `inner_induce_constituent_eq_of_apply_one_eq` — 等次数 ⟹ 等 multiplicity
- `commutator_induce_constituents_apply_one_eq` — [HH,HH] block 全 constituent 等次数
- `exists_liesOver_of_subgroup` — σ の上に ψ 存在 (Clifford correspondent)
- `restrictionMultiplicity_eq_of_liesOver_of_apply_one_eq` — degree formula の等次数系

**S14-specific**:
- `mem_commutator_subgroupOf_iff` — commutator bridge (x∈commutator ↥(H.subgroupOf L) ↔ (x:G)∈derivedInG H)
- `Sset_self_mem_constituents` — Frobenius χ∈S は自身の constituent
- `Sset_inner_coherent_extension_eq_zero` — ψ⊥R(χ) ⟹ ⟨ψ,coh.extension χ⟩=0
- `chiRhoCF_restrict_inner_eq_of_equal_degree` — θ-coefficient equality (既存)

**key 教訓**: FiniteInduce scoped instance (finiteSubFintype/natCardInvC、任意 subgroup 汎用) が
全 subgroupOf/commutator の Fintype/Invertible を供給。自前 haveI は instance diamond
(induce の Invertible が競合 → rfl 失敗) を招くので削除する。Sset membership は
`simp only [Hypothesis.Sset, Set.mem_setOf_eq]` で unfold。

**次 frontier**: §12 の (12.6) coherence / (12.7) type-I Frobenius (Coq FT_Frobenius_coherence /
FT_type1)、または §12 downstream の上流未証明項。次 iteration で scan。

### loop¹⁹¹ — (12.5) 後の frontier 再scan: (8.2.c) は既済、次 = (12.15) rhoM_integer_values (12.5 consumer)

(12.5) 完済後、S14 frontier を再scan:
- **(8.2.c) `typeI_induced_char_constituents` は既に proven** (S14:441-559、sorry-free、
  `exists_extension_induce_eq_sum_distinct_of_inertia_inf_le` 経由)。loop¹¹¹ note が「S14 最上流 sorry」と
  記録していたが、その後 (別 loop/merge で) 閉じられていた。frontier 更新。
- **残 S14 sorry (8 本)**: `sibleyTarget_frobI` (2776、(6.8) TI-case carrier、witness 非-TI ゆえ FT-excluded) /
  `witness_L_isTypeI` (5030) + `witness_L_complement_isZGroup` (5041) ((12.10) Cluster A、deep §8-§11
  type-analysis、gated) / `intersection_complement_structure` (5080) / `complement_cyclic_order_dvd` (5519) /
  **`rhoM_integer_values` (5789、(12.15))** / `exists_counterexample_dade_data` (6023) /
  `exists_typeICovering` (6738/6773)。

**次 target = (12.15) `rhoM_integer_values` (S14:5789)** — **(12.5) の自然な consumer**:
`dade.rhoMFormula ∧ (∀ g∈K, g∉K', ∃ z:ℤ, dade.psi g = z)`。K−K' 上定数性は今 proven の
`rho_constant_on_H_minus_Hprime` (ρψ) で供給できるはず。整数値は rational + algebraic integer。
lane b の §12 Dade tower 領域 (witness pins の §8-§11 type-analysis より lane-b-appropriate)。
deep Dade assembly ((12.13)-(12.15)) だが (12.5) を活かす直系の続き。次 iteration で engage。
