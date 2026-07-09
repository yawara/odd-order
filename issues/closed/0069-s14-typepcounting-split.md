---
id: 69
slug: s14-typepcounting-split
title: "S14_TypePCounting.lean 分割 (1848行>1500, size watch)"
created: 2026-06-15
---

# S14_TypePCounting.lean 分割 (1848行>1500, size watch)

## 背景

`OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean` が **1848 行**に到達し、粒度規約の
1,500 行上限を超過(merge monitor size watch で検出、2026-06-15)。Lane H が Prop 14.2
(case-τ₃ COMPLETE → case-τ₁ 進行中)を本ファイルで active に証明中。

分割 owner = **hub**(merge_monitor.md 規約: lane の frontier と衝突しない凍結境界で prefix-split)。

## トリガー条件(いつ実行するか)

**今すぐは実行しない** — H が S14 に毎 tick コミット中で、今 prefix-split すると H の次マージと
確実に conflict する(凍結窓が無い)。以下のいずれかで実行:

- [ ] H が **Prop 14.2 を完全 landing**(case-τ₁ 全 conjunct + funnel 14.3-14.13 着地)して
      S14 frontier が一段落、または
- [ ] H が明示的に idle/pause、または
- [ ] H 自身が次の主結果(14.3 等)で新 leaf を切る(lane 側デフォルト)で自然に縮む

## やること(prefix-split 案)

凍結している先頭部(定義 + 基本補題)を上流 leaf へ切り出し、Prop 14.2 本体(H の active frontier)を
`S14_TypePCounting` に残す:

- [ ] 候補 leaf `S14_TypePDefs.lean`(または同等)= `piSet`/`sigmaComplementPrimes`/`kappa`/
      `IsTypeP`/`IsTypeP1`/`IsTypeP2`/`IsTypeF` の定義 + 基本 dichotomy 定理群 +
      `maximalTypePFamily` 系 + `SigmaDecompositionData` 構造体(= 行 66〜~360 の凍結部分)。
- [ ] `S14_TypePCounting` は上流 leaf を import し、Prop 14.2 (`typeP_structure`) 以降を残す。
- [ ] 新 leaf を `OddOrder.lean` + `AxiomsCheck.lean` 両方に import(root closure)。
- [ ] full build green + AxiomsCheck OK + sorry 不変を確認。
- [ ] 切る境界は H の最新 frontier を見て決定(前方参照不可ゆえ任意の宣言境界で安全)。

## 完了条件

- S14_TypePCounting.lean が 1,500 行以下、または topic-coherent に分割完了。
- build green / AxiomsCheck OK / sorry 不変。

## 参照

- 規約: `notes/meta/merge_monitor.md`「サイズ watch」、CLAUDE.md「分割の owner と trigger」
- 関連: H LAUNCH(S14 所有)、[[feedback-record-deferred-hub-tasks-as-issues]]

## 🧾 注記 (2026-07-02 hub 全体レビュー): hold 失効 — hygiene-only

- 旧 hold 条件「H が S14 に active commit 中」は**失効**: lane H は退役済 (3 レーン体制
  a/b/c、正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`)、BG 側 frontier は凍結。
- 行数 refresh: `S14_TypePCounting.lean` = **12098 行** (2026-07-02)。
- 優先度 = **hygiene-only** (BG 凍結クラスタの粒度整理であり FT 経路の実質的証明では
  ない)。hub batch の余力枠で実施。

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - Basics.lean (1657 行)
  - GlobalCounting.lean (2052 行)
  - LocalStructure.lean (2197 行)
  - SigmaLengthOne.lean (2403 行)
  - TypePDuality.lean (4073 行)
