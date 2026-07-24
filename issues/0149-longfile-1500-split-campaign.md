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

- ✅ Isaacs 帯 3 file — 2026-07-24 文書順 sweep (いずれも section/topic 境界の
  prefix-split、下流 import 無変更、stamp 除去):
  - `Ch03_SplitExtensions/Basic.lean` 1740 → 1367 (+ `SemidirectAut.lean` 413: §3A)
  - `Ch04_Commutators/Main/BaerTrick.lean` 1572 → 1143 (+ `BaerMulGroup.lean` 456:
    Baer trick 構成層)
  - `Ch06_FrobeniusActions/FrobeniusActionTI.lean` 1875 → 1447
    (+ `FrobeniusActionBasics.lean` 471: §6A basics)
- ✅ Isaacs 帯 残り 3 file — 2026-07-25 (**Isaacs 帯 6/6 完了**):
  - `Ch06_FrobeniusActions/DQSDRecognition.lean` 1783 → 1050
    (+ `InvolutionRecognition.lean` 349 + `SelfCentralizingEnlargement.lean` 439)
  - `Ch07_ThompsonSubgroup/S7B1_NormalJ.lean` 1627 → 730
    (+ `S7B1_NormalJ_Setup.lean` 929; private 横断ゼロの Step-6 境界で切断)
  - `Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean` 1883 → 458
    (+ `S7B2_NormalJClose.lean` 1454: normal-J close; import 連鎖差替えのみ)
- ✅ BG Ch1 帯 5 file — 2026-07-25 前半 (いずれも prefix-split・下流 import 無変更・stamp 除去):
  - `S01_Solvable.lean` 1621 → 1165 (+ `S01_BurnsideOperator.lean` 482: §1C)
  - `S01_FrattiniBurnside.lean` 1572 → 1211 (+ `S01_SolvableBasics.lean` 400: §1A)
  - `S02_RepresentationsBasic.lean` 1612 → 1372 (+ `S02_RepresentationPropositions.lean` 287: §2A–§2E)
  - `S03e_Thm35.lean` 1725 → 374 (+ `S03e_Thm35Prelim.lean` 1386: step 機構全部)
  - (S03f_Thm36 は上記 ✅✅ 参照)

- ✅ BG §4 帯 3 file — 2026-07-25 (prefix-split・下流 import 無変更・stamp 除去):
  - `S04_SmallRankBasic.lean` 1780 → 964 (+ `S04_CommutatorCollection.lean` 857: §4A
    collection 公式 + Ω₁ exponent)
  - `S04_PGroupsSmallRank.lean` 1730 → 1259 (+ `S04_ExtraspecialCommutator.lean` 492:
    Lem 4.15; import 差替え)
  - `S04f_Omega1.lean` 1607 → 1226 (+ `S04f_AutOrderConstraints.lean` 412: Lem 4.13/4.14)
- chip 由来 merge (2026-07-25): `S7B1_NormalJ_Setup.lean` の dead private 8 件削除 (−138 行)。
- ✅ BG Ch2 S08 帯 3 file — 2026-07-25 (prefix-split・import 連鎖差替え・stamp 除去、
  gate は帯 push 直前に集約する新規律の初適用):
  - `S08_FittingOfMaximal.lean` 1607 → 1305 (+ `S08_SCN3Map.lean` 328)
  - `S08_CenterFittingOpcore.lean` 1602 → 1321 (+ `S08_FittingInGBasic.lean` 318)
  - `S08_SCNFitting.lean` 1597 → 1156 (+ `S08_PiCoreCentralizers.lean` 467)
  - ⚠ 教訓: 宣言境界 cut は必ず docstring 開始行まで walk-up してから切る
    (泣き別れ parse error が 3 file 中 3 回発生 → gen script に walk-up を組み込み済)。
  - 🚨 教訓 (2026-07-25, AppE で実害): **新 leaf 名は書く前に `git ls-files` で存在確認**。
    `AppE_RegularOperator.lean` が既存 module (E.3 の 928 行, issue 3021) と衝突し、生成 script が
    上書き → 1 commit に破壊が入った (importer の AppE_ExponentP/AxiomsCheck は leaf build 範囲外で
    未検出)。復旧 = 旧内容 restore + 新 leaf は `AppE_CentralizerDecomposition.lean` に改名。
    walk-up と合わせ、prefix 一致の宣言ターゲットも不可 (`isTypeII_of_isTypeP2` が
    `…_of_derived_typeF` を掴んだ) — 完全一致行で指定する。

- ✅ BG Ch4 帯 6 file — 2026-07-25 (S14 Basics 1684→1193 + TypeClassification 523 /
  S15 SetupLemma151 1745→1273 + AutAbelianCore 499 / S15 Theorem152Helpers 1616→1200 +
  TypeP1Forcing 439 / S16 TheoremsAE 1813→1294 + TheoremAB 541 / S16 TypeP1Criteria
  1652→212 + TypeDataBridges 1464 (唯一の private-clean 点 L1467) / S16 TaxonomyOutput
  1529→543 + LocalTaxonomy 1008)。
- ✅ BG App + GroupTheory 帯 4 file — 2026-07-25 (AppC_NormSet 1842→919 + NormSetBasic 961 /
  AppC_FrobeniusClassSum 1871→1351 + NormOneInduce 556 / AppE_FurtherResults 1675→1042 +
  RegularOperator 670 (section RegularOperator を main 側で再オープン) / CNGroupStructure
  1588→1179 + CNGroupFrobeniusSteps 442)。

- ✅ Pf 帯 4 file — 2026-07-25 (S04_DadeIsometryBasic 1688→1398 + S04_DadeHypothesisCore 332
  (namespace Hypothesis 再オープン + open 復元) / S05_SignedTripleGrid 1833→1345 +
  S05_NormThreeCharacters 511 / S07 CoherenceUnion 1730→706 + CoherenceExtensionTau2 1042 /
  S07 FamilyBundleDade 1644→1367 + FamilyBundleBasic 294)。
  ⚠ 親の namespace 再オープン時は原本の **open 行 (OddOrder.RepresentationTheory /
  scoped Pointwise) を必ず複製** — 3 file で instance/identifier 解決が落ちた。

### ✅ Pf S08 帯 + S09 — 2026-07-25 (再試行で完了)

- `S08_CoherenceBasic` 1508→797 (+ `S08_SibleyHypothesisBasic` 743) /
  `S08_CoherenceCore` 1507→793 (+ `S08_SibleyCoherenceLemmas` 744) /
  `S08_RestrictExtensionDvd` 1516→767 (+ `S08_SibleyRestrictionLemmas` 779) /
  `S08_CaseBAnchoredSeed` 1527→882 (+ `S08_CaseBSeedSetup` 673) /
  `S09_CertificateDischarge` 1612→894 (+ `S09_CertificateBasic` 742)。
- gen script の教訓 2 件 (初回試行は revert 済み):
  1. **import 挿入位置は「連続 import run の直後」**で判定 — module docstring 内の
     「`import chain head: …`」という行頭 `import` の doc 行に `^import` 検出が騙され、
     挿入 import がコメント内部に落ちて無効化していた。
  2. **walk-up は fixpoint まで** — docstring 開始まで戻った後、その上の
     `open scoped Classical in` 等の modifier 行をもう一度戻る (modifier → docstring →
     modifier の交互適用)。

- ✅ Pf S11 帯 5 file — 2026-07-25 (`CuS0` 1823→1166 + `CuS0Basic` 684 /
  `InnerCompHom` 1734→1022 + `InnerCompHomBasic` 741 / `ChiefFactorCore` 1672→1061 +
  `ChiefFactorBasic` 637 / `S11_NineElevenCoherence` 1519→893 + `S11_NineElevenSetup` 654
  (先頭 named section が preamble 複製に混入 → main 側で section 行と scoped variable を除去) /
  `WielandtSetup` 1517→842 + `WielandtSetupBasic` 712)。
  ⚠ scan 修正: primed 名 (`foo'`) の使用検出は `\b` 境界では失敗する — 前後 lookaround で判定。

- ✅ Pf 残り帯 + Higman + 表外 1 — 2026-07-25 (**第一パス完遂**):
  - `S12_MaximalIII_IV_V` 1702→1109 (+ `S12_MaximalTypesSetup` 619) /
    `S12_TypeIICrossIsometryPair` 1578→1000 (+ `S12_CrossIsometrySetup` 606)
  - `S14_MaximalI/FrobeniusStructure` 1801→1130 (+ `FrobeniusStructureBasic` 692) /
    `S14_MaximalI/WitnessSylowCyclic` 1542→988 (+ `WitnessSylowBasic` 577)
  - `S15_BridgeCharacter` 1708→1050 (+ `S15_BridgeCharacterBasic` 684)
  - `S16_CoreSetup` 1607→859 (+ `S16_CoreSetupBasic` 782; section Step4 +
    namespace FieldNormalizerData を跨ぐため main で再オープン、local instance は
    `factPPrimeStep4Split` に改名再宣言) /
    `S16_NonExistenceG/ComparingLM` 1655→1066 (+ `ComparingLMBasic` 615)
  - `Appendices/FeitSibleyEndgame` 1724→1136+4 (+ `FeitSibleyEndgameSetup` 613;
    namespace Hypothesis を main で再オープン)
  - `Higman/…/HigmanLowerCentralSpectrum` 1502→1009 (+ `HigmanSpectrumBilinear` 541;
    universe 宣言の main 側複製が必要だった)
  - 表外: `BG/Ch4_FamilyOfMaximal/S15_MF/OpicoreCentralizer` 1502→976
    (+ `OpicoreCentralizerBasic` 550; 0a6a849aa で stamp されたが worklist 表から漏れていた)

**⟹ 第一パス完遂 (2026-07-25)**: 残 stamp = `AxiomsCheck.lean` (恒久例外) + 下記第二パス 6 件のみ。

### ⚠ 第二パス行き (private 網が全域を覆い、clean な宣言境界 cut が存在しない)
- `Peterfalvi/S10_MinimalSimpleBasic.lean` (1889) — private 網 (622→1534, 674→1534;
  primed 名 `Msigma_conj_smul'` 含む) で clean cut なし

prefix-split では割れない — 対応には crossing private の public 化 (namespace 付与) という
設計判断が要るため、campaign 第一巡から除外して後続パスで扱う:

- `BG/Ch1_Preliminary/S02_Representations.lean` (1577) — odd_two_dim 帰納網
  (private 54→1438 等が全域交差)
- `BG/Ch1_Preliminary/S02_FixedSubmodules.lean` (1553) — fixedOnSubmoduleAndQuotient 網
  (private 22→1366 等)
- `BG/Ch1_Preliminary/S04f_Blackburn.lean` (1634) — private 29→1152 等が全域交差
  (clean cut = L25 のみで無意味)
- `BG/Ch1_Preliminary/S06_Additional.lean` (1677) — clean cut ゼロ (private 508→1495 等)
- `GroupTheory/RepresentationTheory/ClassSumCongruence.lean` (1602) — named section 網
  (ClassSum/StructureCoeff/…) と private (227→410, 315→1511) の交差で section 境界 cut が全滅

- ✅✅ `BG/Ch1_Preliminary/S03f_Thm36.lean` (3822) — 2026-07-24 **完了、stamp 除去**:
  単一巨大宣言 `thm36_aux` の IH-free セグメント 3 つを段階的に切出し、
  3822 → **1301 行** (stamp 4000 → 2600 → 1900 → 除去)。
  - `S03f_Endgame.lean` (1402): (3.29)–(3.38)、opaque binder + 定義等式渡し (仮説 41)。
  - `S03f_R0Action.lean` (802): Phase C (3.17)–(3.21)。VG/KG/S₁/φ は lemma 内部で同一
    `set` 再構成 → verbatim 移植 (パッチ 2 箇所のみ)、caller が re-`set` で fold。
  - `S03f_ComplementK.lean` (646): Phase B (3.12)–(3.16)、`∃ K P` package (15 conjuncts)。
  - 残りは IH を消費する Phase A (3.6)–(3.11) + Phase D (3.22)–(3.28) で分割不能の本体。
    副産物: thm36_aux の elaboration 50s → 17s。
- ✅ `Peterfalvi/Appendices/FeitSibleyTheorem.lean` (1884) — 2026-07-24 prefix-split:
  `FeitSibleySsetCoherence.lean` (892) + 残 1022、両方 stamp 不要化 (issue 0141 close)。
- ✅ `BG/Ch1_Preliminary/S04g_Thm418.lean` (1965) — 2026-07-24 prefix-split:
  `S04g_Thm418Core.lean` (958、Thm 4.18 本体+rank 系) + 残 1008 (p-complement 転送 +
  CharacteristicSylow series 層)、両方 stamp 不要化・下流 import 無変更。
- ➕ `Higman/Suzuki2Groups/HigmanLowerCentralSpectrum.lean` (1501) を worklist 追加 —
  wc 1499 (lastLine 1500) は linter 境界仕様で unstamped だと警告になるため stamp 1600 を付与。

(AxiomsCheck.lean 12635 は機械列挙 file の意図的例外 — stamp 恒久維持、分割対象外。)

## 完了条件

AxiomsCheck 以外の全 stamp が除去され (= 全 file ≤ 1500)、lakefile の 1500 gate が
per-file 例外なしで green。CLAUDE.md「ファイル粒度」の実測値を更新。

## 参照

- CLAUDE.md「ファイル粒度」(2026-07-24 改訂) / issue 0103 (機械分割の道具) /
  closed/0138 (--strict gate) / 0141 (FeitSibley 分割計画)
