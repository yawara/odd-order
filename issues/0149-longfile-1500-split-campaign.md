---
id: 149
slug: longfile-1500-split-campaign
title: "longFile 1500 移行 + 分割 campaign (58 file の stamp 除去)"
created: 2026-07-24
---

# longFile 1500 移行 + 分割 campaign

## 背景 (ユーザー裁定 2026-07-24「ファイル分割を mathlib の基準に合わせたうえで進めよう」)

従来の本リポ上限 2000 行 (2026-07-09 裁定、lakefile で `longFile=2000` + defValue ハック) を廃し、
**mathlib 素の基準 = `linter.style.longFile 1500`** に切替えた。超過 58 file は mathlib 自身の
per-file 例外機構 `set_option linter.style.longFile N` で grandfather 済み (N は linter が許容する
candidate/candidate−100 のみ; 過大値は「bound 過大」警告になる)。

この stamp は **ratchet として機能する**: 超過 file はこれ以上伸ばせず (伸ばすには stamp の明示
bump が必要 = diff に出る)、分割が済んだ file から stamp を除去して純減させる。lint gate は
`--strict` (issue 0138 closed) なので stamp 漏れ・過大 stamp は CI で赤になる。

## 方針 (CLAUDE.md「ファイル粒度」準拠)

- 目安 1 file ≈ 300–1500 行 / 1 トピック。**分割はディレクトリ化第一** (`<節名>.lean` を pure
  re-export hub 化、実体は `<節名>/<Topic>.lean`) — module 名不変で下流 import 無変更。
- 凍結境界での flat prefix-split (先頭クラスタ → sibling、元 file が import) も可。
- 命名は記述的英語 (`Part1` 等は不可)。**新 leaf は同 commit で `OddOrder.lean` に配線**
  (orphan-leaf 素通し防止)。分割後 stamp を除去して full build + `--strict` で検証。
- owner: active-lane file は owner lane の frontier 通過時 / frozen file は hub の quiet window。
- 順序: hard 級 (2000 近傍・issue 起票済) から文書順。具体的には
  [0141](0141-feitsibley-theorem-split.md) FeitSibley (1882) → S04g_Thm418 (1963) →
  S03f_Thm36 (3822, 最難・単一定理クラスタの helper 層切出し) → 残りを文書順。
  旧 watch issue 0124 (S01_Solvable / TypeP1Criteria / TheoremsAE) と 0129 (CNGroupStructure)
  は本 campaign に統合して close。

## worklist (stamp 除去 = 完了の定義; 2026-07-24 時点 58 file)

| file (OddOrder/ 配下) | 行数 (stamp 時点) |
|---|---|
| `AxiomsCheck.lean` | 12635 |
| `BG/Ch1_Preliminary/S03f_Thm36.lean` | 3822 |
| `BG/Ch1_Preliminary/S04g_Thm418.lean` | 1965 |
| `Peterfalvi/S10_MinimalSimpleBasic.lean` | 1888 |
| `Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean` | 1883 |
| `Isaacs/Ch06_FrobeniusActions/FrobeniusActionTI.lean` | 1875 |
| `BG/AppC_FrobeniusClassSum.lean` | 1870 |
| `BG/AppC_NormSet.lean` | 1841 |
| `Peterfalvi/S05_SignedTripleGrid.lean` | 1832 |
| `Peterfalvi/S11_MaximalII_III_IV/CuS0.lean` | 1822 |
| `BG/Ch4_FamilyOfMaximal/S16_MainResults/TheoremsAE.lean` | 1812 |
| `Peterfalvi/S14_MaximalI/FrobeniusStructure.lean` | 1800 |
| `Isaacs/Ch06_FrobeniusActions/DQSDRecognition.lean` | 1783 |
| `BG/Ch1_Preliminary/S04_SmallRankBasic.lean` | 1779 |
| `BG/Ch4_FamilyOfMaximal/S15_MF/SetupLemma151.lean` | 1744 |
| `Isaacs/Ch03_SplitExtensions/Basic.lean` | 1740 |
| `Peterfalvi/S11_MaximalII_III_IV/InnerCompHom.lean` | 1733 |
| `Peterfalvi/S07_Coherence/CoherenceUnion.lean` | 1729 |
| `BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean` | 1729 |
| `BG/Ch1_Preliminary/S03e_Thm35.lean` | 1724 |
| `Peterfalvi/Appendices/FeitSibleyEndgame.lean` | 1723 |
| `Peterfalvi/S15_BridgeCharacter.lean` | 1707 |
| `Peterfalvi/S12_MaximalIII_IV_V.lean` | 1701 |
| `Peterfalvi/S04_DadeIsometryBasic.lean` | 1687 |
| `BG/Ch4_FamilyOfMaximal/S14_TypePCounting/Basics.lean` | 1683 |
| `BG/Ch1_Preliminary/S06_Additional.lean` | 1676 |
| `BG/AppE_FurtherResults.lean` | 1674 |
| `Peterfalvi/S11_MaximalII_III_IV/ChiefFactorCore.lean` | 1671 |
| `Peterfalvi/S16_NonExistenceG/ComparingLM.lean` | 1654 |
| `BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeP1Criteria.lean` | 1651 |
| `Peterfalvi/S07_Coherence/FamilyBundleDade.lean` | 1643 |
| `BG/Ch1_Preliminary/S04f_Blackburn.lean` | 1633 |
| `Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean` | 1627 |
| `BG/Ch1_Preliminary/S01_Solvable.lean` | 1621 |
| `BG/Ch4_FamilyOfMaximal/S15_MF/Theorem152Helpers.lean` | 1615 |
| `Peterfalvi/S09_CertificateDischarge.lean` | 1611 |
| `BG/Ch1_Preliminary/S02_RepresentationsBasic.lean` | 1611 |
| `Peterfalvi/S16_CoreSetup.lean` | 1606 |
| `BG/Ch2_Uniqueness/S08_FittingOfMaximal.lean` | 1606 |
| `BG/Ch1_Preliminary/S04f_Omega1.lean` | 1606 |
| `GroupTheory/RepresentationTheory/ClassSumCongruence.lean` | 1601 |
| `BG/Ch2_Uniqueness/S08_CenterFittingOpcore.lean` | 1601 |
| `BG/Ch2_Uniqueness/S08_SCNFitting.lean` | 1596 |
| `GroupTheory/CNGroupStructure.lean` | 1587 |
| `Peterfalvi/S12_TypeIICrossIsometryPair.lean` | 1577 |
| `BG/Ch1_Preliminary/S02_Representations.lean` | 1577 |
| `Isaacs/Ch04_Commutators/Main/BaerTrick.lean` | 1572 |
| `BG/Ch1_Preliminary/S01_FrattiniBurnside.lean` | 1572 |
| `BG/Ch1_Preliminary/S02_FixedSubmodules.lean` | 1553 |
| `Peterfalvi/S14_MaximalI/WitnessSylowCyclic.lean` | 1541 |
| `BG/Ch4_FamilyOfMaximal/S16_MainResults/TaxonomyOutput.lean` | 1528 |
| `Peterfalvi/S08_CaseBAnchoredSeed.lean` | 1526 |
| `Peterfalvi/S11_NineElevenCoherence.lean` | 1518 |
| `Peterfalvi/S11_MaximalII_III_IV/WielandtSetup.lean` | 1516 |
| `Peterfalvi/S08_RestrictExtensionDvd.lean` | 1515 |
| `Peterfalvi/S08_CoherenceBasic.lean` | 1507 |
| `Peterfalvi/S08_CoherenceCore.lean` | 1506 |
### 消化記録

- ✅ `Peterfalvi/Appendices/FeitSibleyTheorem.lean` (1884) — 2026-07-24 prefix-split:
  `FeitSibleySsetCoherence.lean` (892) + 残 1022、両方 stamp 不要化 (issue 0141 close)。
- ➕ `Higman/Suzuki2Groups/HigmanLowerCentralSpectrum.lean` (1501) を worklist 追加 —
  wc 1499 (lastLine 1500) は linter 境界仕様で unstamped だと警告になるため stamp 1600 を付与。

(AxiomsCheck.lean 12635 は機械列挙 file の意図的例外 — stamp 恒久維持、分割対象外。)

## 完了条件

AxiomsCheck 以外の全 stamp が除去され (= 全 file ≤ 1500)、lakefile の 1500 gate が
per-file 例外なしで green。CLAUDE.md「ファイル粒度」の実測値を更新。

## 参照

- CLAUDE.md「ファイル粒度」(2026-07-24 改訂) / issue 0103 (機械分割の道具) /
  closed/0138 (--strict gate) / 0141 (FeitSibley 分割計画)
