# Odd Order Theorem 形式化ロードマップ

## ゴール

有限群論の **Feit-Thompson 定理**「位数が奇数の有限群はすべて可解である」の **Lean 4 による完全形式化**。AI エージェント駆動の長期プロジェクト。

## スコープ: 3 冊を全部形式化する

| 略称 | 書名 | 役割 |
|------|------|------|
| **Isaacs** | I. M. Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) | 有限群論の前提一式 (Fitting, Hall, Frobenius, ZJ, transfer, 一般化 Fitting `F*`) |
| **BG** | H. Bender & G. Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994) | Feit-Thompson 1963 原論文 Ch.IV (局所解析) + Ch.VI (最終矛盾; App.C は Peterfalvi 1984 paper の改訂版) |
| **Peterfalvi** | T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000) | Feit-Thompson 1963 原論文 Ch.V (指標理論) |

## 方針

- **すべてローカルに書く** (mathlib への PR は将来課題、当面はこのリポジトリ内)
- **mathlib 互換を可能な限り維持** (将来の upstream を見据えて命名・スタイル・namespace を mathlib に寄せる)
- **blueprint は使わない** (教科書 PDF → Lean 直接)
- **教科書として Isaacs を採用 (Gorenstein 1968 は使わない)** — BG が "**G**" として引く Gorenstein _Finite Groups_ (1968) は古典で、BG/Peterfalvi の前提知識を提供する標準文献だが、本プロジェクトでは現代記法で同等内容を扱う **Isaacs FGT を一次参照に採用**するという明示的な選択。BG 中の "G, Thm X.Y.Z" 引用は Isaacs の対応定理に読み替えて Phase 1 で形式化する
- mathlib 既存資産 (Sylow, p-群, 可解, 冪零, Frattini, Transfer, Focal subgroup, Schur-Zassenhaus, 基本表現論/指標, Maschke, 既約表現, 直交関係, 誘導表現) は再利用
- 命名: `OddOrder.Isaacs.Subgroup.fitting` のように、将来 `Subgroup.fitting` へリネームしやすい形を取る

## フェーズ

| Phase | 内容 | 状態 |
|---|---|---|
| 0 | Lean プロジェクト初期化 (Lean 4.29.1 + mathlib v4.29.1) | ✅ 2026-05-21 |
| 1 | **Isaacs** Ch.1–10 + Appendix の Lean 化 | ⏳ |
| 2a | **BG** Ch.I–IV + 補助 Appendices の Lean 化 | ⏳ |
| 2b | **Peterfalvi** 主章 + 補章 の Lean 化 | ⏳ |
| 3 | 最終矛盾の結合 (BG App.C ≅ Peterfalvi の対応物) | ⏳ |
| 4 | `FeitThompson` メイン定理ステートメント & 完全結合 | ⏳ |

Phase 2a と 2b は Phase 1 が概ね終わった後、独立に並行進行可。

## 依存グラフ

```
                  mathlib
                     │
                     ↓
            [Phase 1] Isaacs
   (Fitting, Hall, Frobenius, ZJ, F*)
                     │
         ┌───────────┴───────────┐
         ↓                       ↓
   [Phase 2a] BG          [Phase 2b] Peterfalvi
   (局所解析)             (指標理論)
         └───────────┬───────────┘
                     ↓
             [Phase 3] 最終矛盾
                     ↓
             [Phase 4] FeitThompson
```

## Lean モジュール構成 (提案)

```
OddOrder.lean                            # entry module — 章ファイルを順次 import
OddOrder/
├── Isaacs/                              # Phase 1
│   ├── Ch01_Sylow.lean
│   ├── Ch02_Subnormality.lean
│   ├── Ch03_SplitExtensions.lean        # Hall, Schur-Zassenhaus
│   ├── Ch04_Commutators.lean
│   ├── Ch05_Transfer.lean
│   ├── Ch06_FrobeniusActions.lean
│   ├── Ch07_ThompsonSubgroup.lean       # J(P), ZJ
│   ├── Ch08_PermutationGroups.lean
│   ├── Ch09_MoreSubnormality.lean       # F*(G)
│   ├── Ch10_MoreTransfer.lean
│   └── AppA_Basics.lean
├── BG/                                  # Phase 2a
│   ├── Ch1_Preliminary/
│   │   ├── S01_Solvable.lean
│   │   ├── S02_Representations.lean
│   │   ├── S03_FrobeniusActions.lean
│   │   ├── S04_PGroupsSmallRank.lean
│   │   ├── S05_NarrowPGroups.lean
│   │   └── S06_Additional.lean
│   ├── Ch2_Uniqueness/
│   │   ├── S07_Transitivity.lean
│   │   ├── S08_FittingOfMaximal.lean
│   │   └── S09_Uniqueness.lean
│   ├── Ch3_MaximalSubgroups/
│   │   ├── S10_MalphaMsigma.lean
│   │   ├── S11_ExceptionalMaximal.lean
│   │   ├── S12_E.lean
│   │   └── S13_PrimeAction.lean
│   ├── Ch4_FamilyOfMaximal/
│   │   ├── S14_TypePCounting.lean
│   │   ├── S15_MF.lean
│   │   └── S16_MainResults.lean
│   ├── AppA_Prerequisites.lean
│   ├── AppB_Puig.lean
│   ├── AppC_FinalContradiction.lean     # Peterfalvi (1984 paper) 改訂版
│   ├── AppD_CNGroups.lean
│   └── AppE_FeitThompson.lean
├── Peterfalvi/                          # Phase 2b
│   ├── S01_Introduction.lean
│   ├── S02_Notation.lean
│   ├── S03_PreliminaryCharacter.lean
│   ├── S04_DadeIsometry.lean
│   ├── S05_TICyclic.lean
│   ├── S06_DadeIsometryCertain.lean
│   ├── S07_Coherence.lean
│   ├── S08_CoherenceTheorems.lean
│   ├── S09_NonExistenceCertainGroup.lean
│   ├── S10_MinimalSimpleStructure.lean
│   ├── S11_MaximalII_III_IV.lean
│   ├── S12_MaximalIII_IV_V.lean
│   ├── S13_MaximalIII_IV.lean
│   ├── S14_MaximalI.lean
│   ├── S15_SAndT.lean
│   ├── S16_NonExistenceG.lean
│   └── Appendices/
│       ├── Suzuki.lean
│       ├── Huppert.lean
│       ├── NearFields.lean
│       ├── Suzuki2Groups.lean
│       └── FeitSibley.lean
├── FeitThompson.lean                    # Phase 4: メイン定理
└── Basic.lean                           # 一時ダミー (削除予定)
```

Namespace 階層: `OddOrder.Isaacs.Ch01`, `OddOrder.BG.Ch1.S03`, `OddOrder.Peterfalvi.S04` 等。

## ファイル粒度とトレーサビリティ

各 Lean ファイルは「文献のどこの形式化か」を一目で追える状態を保つ。

### 初期粒度

| 本 | 1 ファイル単位 | 理由 |
|---|---|---|
| Isaacs | 1 章 | 章は 20-48 ページ、Lean 500-2000 行に収まる見込み |
| BG | 1 節 (§) | 節が 3-16 ページと小さく、節境界が明確 |
| Peterfalvi | 1 節 (§) | 同上 (1-12 ページ) |

### 育ってから分割

1 ファイルが概ね **1500-2000 行** を超えた段階で、subsection 単位でディレクトリに昇格:

```
OddOrder/Isaacs/Ch01_Sylow.lean
        ↓
OddOrder/Isaacs/Ch01_Sylow/
                ├── A_Existence.lean
                ├── B_Normalizer.lean
                └── ...
```

先回りで全部 subsection 分割するのは避ける (本によって subsection 区切りが緩いところがあり、無駄な分割になりやすい)。

### トレーサビリティ慣習 (3 層)

```lean
/-!
# OddOrder.Isaacs.Ch01 — Sylow Theory

Isaacs, *Finite Group Theory*, Chapter 1 (pp. 1-44) の Lean 化。
-/
namespace OddOrder.Isaacs.Ch01

section /- 1A: Sylow's Theorems (pp. 1-10) -/

/-- **Isaacs Thm 1.4** (Sylow's existence). 任意の素数 `p` について ... -/
theorem sylowExistence ... := ...

/-- **Isaacs Thm 1.7** (Sylow's conjugacy). ... -/
theorem sylowConjugacy ... := ...

end -- 1A

section /- 1B: Counting and the index theorem (pp. 11-20) -/
...
end -- 1B
```

- **ファイル冒頭の `/-! ... -/`**: 本のどの章節か、ページ範囲、簡単な内容
- **`section /- ラベル (ページ範囲) -/ ... end`**: 本の subsection 構造をミラー (VSCode で折り畳み可、grep で位置特定可)
- **theorem の docstring 冒頭の `**Book名 Thm N.M**`**: 本での番号 + 慣用名

定理名 (`theorem` の Lean 識別子) には番号 (`thm_1_4` 等) を入れない — mathlib 互換のため命名は記述的 (`sylowExistence`, `sylowConjugacy`) に保つ。本での番号は docstring 内に。

## 進捗ログ

- **2026-05-21** Phase 0 完了 (Lean プロジェクト初期化、mathlib カバレッジ調査、3 冊スコープ確定、本ロードマップ作成)
- **2026-05-21** Phase 1 章間依存を Isaacs mmd から集計、下記の依存図を追加
- **2026-05-22** Phase 2 全体構造の調査ノート完了: [`notes/bg/_overview.md`](notes/bg/_overview.md) (BG 138 結果集計 + FT 経路 + Phase 2a 着手順), [`notes/peterfalvi/_overview.md`](notes/peterfalvi/_overview.md) (Peterfalvi 140 結果集計 + FT 経路 + Phase 2b 着手順), [`notes/meta/phase2_cross_refs.md`](notes/meta/phase2_cross_refs.md) (3 冊間クロス参照マップ + Phase 1 Isaacs ↔ Phase 2 対応表)

## Phase 1 内の章間依存 (Isaacs)

Isaacs FGT 本文中で `Theorem|Lemma|Corollary|Proposition N.M` 形式の章間参照を `references/isaacs/finite-group-theory.mmd` から集計した実依存:

```
Ch.1 (Sylow) ──┬─→ Ch.2 (Subnormality) ──→ Ch.9 (F*)
               │     │
               │     ↓
               ├─→ Ch.3 (Hall, S-Z) ─→ Ch.4 (Commutators) ─→ Ch.5 (Transfer)
               │                                                  │
               │                                                  ↓
               │                                             Ch.6 (Frobenius)
               │                                                  │
               │                                       ┌──────────┤
               │                                       ↓          ↓
               │                                 Ch.10 (More)  Ch.7 (Thompson, ZJ)
               │
               └─→ Ch.8 (Permutation, 実質独立)

Appendix: 前提なし
```

並列着手の指針:

- **第 1 波 (前提なし、mathlib 既存資産で薄く):** Ch.1, Ch.8, Appendix
- **第 2 波 (Ch.1 完了後):** Ch.2
- **第 3 波 (Ch.2 完了後、並列可):** Ch.3, Ch.9 (F\* は Ch.2 直後に着手可)
- **第 4 波:** Ch.4 → Ch.5 → Ch.6 のシーケンス (Transfer は mathlib 既存で速い)
- **第 5 波 (Ch.6 完了後、並列可):** Ch.7 (Thompson J(P), ZJ), Ch.10 (More Transfer)

クリティカルパスは Ch.6 → Ch.7 (Frobenius 群と Thompson subgroup の新規実装が Phase 1 の山場)。Ch.9 (F\*) は意外に Ch.6/Ch.7 を待たずに並行できる。

集計再現手順 (mathlib や Isaacs 改訂で章番号が変わった場合に再実行):

```bash
mmd=references/isaacs/finite-group-theory.mmd
# 章境界: grep -n "^## Chapter " "$mmd" で取得 (Ch.3 は MISSING_PAGE_EMPTY で欠落するので前後章から推定)
# 各章本文範囲を awk で切り出し、Theorem/Lemma/Corollary/Proposition N.M の N を grep -oE で抽出
awk -v s=START -v e=END 'NR>=s && NR<e' "$mmd" \
  | grep -oE "(Theorem|Lemma|Corollary|Proposition) [0-9]+\.[0-9]+" \
  | grep -oE "[0-9]+\.[0-9]+" | awk -F. '{print "Ch."$1}' \
  | sort | uniq -c | sort -rn
```

## チャプター進捗チェックリスト

### Phase 1 — Isaacs

- [ ] Ch.1 Sylow Theory (p.1) — *前提なし*
- [ ] Ch.2 Subnormality (p.45) — *前提: Ch.1*
- [ ] Ch.3 Split Extensions (p.65) — Hall, Schur-Zassenhaus; *前提: Ch.1, Ch.2*
- [ ] Ch.4 Commutators (p.113) — *前提: Ch.3 (Ch.1, Ch.2 軽)*
- [ ] Ch.5 Transfer (p.147) — *前提: Ch.3, Ch.4*
- [ ] Ch.6 Frobenius Actions (p.177) — *前提: Ch.3, Ch.4, Ch.5*
- [ ] Ch.7 The Thompson Subgroup (p.201) — J(P), ZJ; *前提: Ch.6 (Ch.1-5 横断)*
- [ ] Ch.8 Permutation Groups (p.223) — *前提: Ch.1 (実質独立)*
- [ ] Ch.9 More on Subnormality (p.271) — F*(G); *前提: Ch.2 (Ch.1 軽)*
- [ ] Ch.10 More Transfer Theory (p.295) — *前提: Ch.4, Ch.5, Ch.6*
- [ ] Appendix: The Basics (p.325) — *前提なし (基礎集合)*

### Phase 2a — Bender-Glauberman

**Overview**: [`notes/bg/_overview.md`](notes/bg/_overview.md) — 全 138 結果 (本文 121 + Appendix 17). 3 冊間クロス参照: [`notes/meta/phase2_cross_refs.md`](notes/meta/phase2_cross_refs.md). FT クリティカル経路: §1-§5 → **§6 Thm 6.2 (= Isaacs Thm 7.6 normal-J)** → §7-§9 Uniqueness → §10-§13 Maximal → §14-§16 Main → App.C. App.A "p-Stability" は §6-§16 全体に暗黙の前提.

**Chapter I. Preliminary Results** (62 結果)
- [ ] §1 Elementary Properties of Solvable Groups (p.1) — 22 結果. **Prop 1.5-1.6 が Peterfalvi で多用**. A-invariant Hall + p-length + solvable basic. *前提: Isaacs Ch.1, Ch.3, Ch.4* — [調査メモ](notes/bg/s01_solvable.md): A-invariant Hall (Prop 1.5 = 28+ 引用, Lemma 1.1 = 43+ 引用), Prop 1.15 = Isaacs 3.21 Hall-Higman 1.2.3, 9/22 が mathlib 直接, 8/22 が Isaacs 再引用, 5/22 が新規定義/構造
- [ ] §2 General Results on Representations (p.9) — 6 結果. Operator group の表現、Fong-Swan 系. 本文使用 1-2 箇所. *前提: Isaacs Ch.6 軽*
- [ ] §3 Actions of Frobenius Groups (p.17) — 10 結果. Frobenius kernel nilpotent + 表現論的 Frobenius action. **Isaacs Ch.6 全面前提**. *前提: Isaacs Ch.6 完成*
- [ ] §4 p-Groups of Small Rank (p.33) — 10 結果. Rank ≤ 2 p-群構造定理 (Blackburn). *前提: Isaacs Ch.4*
- [ ] §5 Narrow p-Groups (p.44) — 7 結果. Narrow p-群族, Sylow 形状制限. *前提: Isaacs Ch.4*
- [ ] §6 Additional Results (p.49) — 7 結果 (Thm 6.1, 6.2, 6.3, 6.4, 6.7 + Lem 6.5, 6.6). solvable + p-length 1 + Frobenius factorization. **§7-§16 で多用される道具袋**. mmd L1957-2128 (§6 ヘッダ Nougat 抽出ミスあり、`**6.**` インライン). *前提: Isaacs Ch.5, Ch.7* — [調査メモ](notes/bg/s06_additional.md): **Thm 6.2 (normal-J) ≡ Isaacs Thm 7.6** odd-order 等価, §8 (3 箇所) §9 (2 箇所) App.A (Thm A.4(b) で再述) App.B App.C で 7+ 引用. 形式化方針: Isaacs 7.6 import 推奨 (1-2 日) vs BG App.A 経由再証明 (4-5 日). MISSING_PAGE:67 は §6 末で論理影響無し

**Chapter II. The Uniqueness Theorem** (10 結果)
- [ ] §7 The Transitivity Theorem (p.55) — 3 結果. **Hypothesis 7.1 で最小反例 G を固定** (mmd L2133). *前提: Isaacs Ch.7 (J(P))*
- [ ] §8 The Fitting Subgroup of a Maximal Subgroup (p.61) — 1 結果. **Thm 6.2 を 5+ 箇所引用**. *前提: §6, §7, Isaacs Ch.7 Thm 7.6*
- [ ] §9 The Uniqueness Theorem (p.64) — 6 結果. central structure + maximal subgroup 一意性. **Thm 6.2 を 4+ 箇所引用**. *前提: §8, Isaacs Ch.7 Thm 7.6*

**Chapter III. Maximal Subgroups** (32 結果)
- [ ] §10 The Subgroups M_α and M_σ (p.69) — 6 結果. maximal subgroup の族の定義・性質. *前提: §9*
- [ ] §11 Exceptional Maximal Subgroups (p.80) — 4 結果. 例外 maximal subgroup 分類. *前提: §10*
- [ ] §12 The Subgroup E (p.83) — 15 結果 (大規模, §12 が小章相当). 部分群 E の構造と共役性. *前提: §10-§11, Isaacs Ch.7*
- [ ] §13 Prime Action (p.97) — 7 結果. derived series, Thompson 風作用. *前提: §12*

**Chapter IV. The Family of All Maximal Subgroups of G** (17 結果)
- [ ] §14 Maximal Subgroups of Type 𝒫 and Counting (p.105) — 7 結果. counting argument; type-𝒫 構造. *前提: §10-§13 統合*
- [ ] §15 The Subgroup M_F (p.117) — 9 結果. Fitting 関連 maximal. *前提: §14*
- [ ] §16 The Main Results (p.123) — 1 結果 (Theorem B). FT 局所部の最終. App.C / Peterfalvi へ橋渡し. *前提: §1-§15 全統合*

**Appendices** (17 結果)
- [ ] App.A Prerequisites and p-Stability (p.135) — 5 結果 (Thm A.1-A.5). **Thm A.4(b) ≡ Isaacs Thm 7.6 odd-order 版**. §6 Thm 6.2 の証明前提. *前提: Isaacs Ch.7 全面* — [調査メモ](notes/bg/appA_pstability.md): p-stability 概念の正式定義 (Glauberman 1968 [11] origin), Isaacs Ch.7 全体の odd-order 再構築. A.5 が App.B Puig L(S) の中核前提. 実装量 ~530 行 / 9-11 日. mathlib ~10%, Phase 1 Ch.7 import ~50%, 新規 ~40%
- [ ] App.B The Puig Subgroup L(S) (p.139) — 3 結果. J(S) の代替 Puig 不変部分群. App.A 補強の独立証明枝. *前提: App.A*
- [ ] App.C The Final Contradiction (p.145) — 3 結果 (Theorem C, Lem C.1, C.2). **Peterfalvi 1984 paper [22] の Carlip-Wheeler 編集再録**. **Phase 2b §9 と統合形式化**. mmd L4763 `## Appendix D Main Theorem` は Nougat 抽出ミスで App.C 本文の続き.
- [ ] App.D CN-Groups of Odd Order (p.153) — 2 結果. Feit-Hall-Thompson 1960 短縮ルート. FT 本筋外 (△).
- [ ] App.E Further Results of Feit and Thompson (p.157) — 5 結果. 発展結果. Phase 2a 完了後の発展材料、または Phase 4 メイン結合時に. △.

### Phase 2b — Peterfalvi 本体 (Character Theory for the Odd Order Theorem)

**Overview**: [`notes/peterfalvi/_overview.md`](notes/peterfalvi/_overview.md) — 本文 113 結果 ((N.M) 形式) + 付録 27 結果 (140 結果). FT クリティカル: §3-§8 (指標論コア) → §9 (= BG App.C) → §10-§15 (型分析、BG Ch.3-Ch.4 出力依存) → §16 (G 非存在). 全節 ☆ (FT 必須). 付録は △.

- [ ] §1 Introduction (pp.1-2) — 0 結果. FT 証明戦略 + BG 依存明示. *前提なし*
- [ ] §2 Notation (pp.3-4) — 0 結果. 指標論・加群記号. *前提なし*
- [ ] §3 Preliminary Results from Character Theory (pp.5-9) — 10 結果 ((1.1)-(1.10)). Isaacs [Is] 表現論 + Peterfalvi 補強. mathlib `Character.lean` API 橋渡し. *前提: Phase 1 完成, mathlib `RepresentationTheory.Character`* — [調査メモ](notes/peterfalvi/s03_preliminary_character.md): (1.4) tau isometry が §4 Dade の準備 (☆☆☆), (1.3) Fourier 展開も新規. (1.1), (1.5)-(1.8) は Isaacs [Is] Thm 6.32, 6.5, 6.11, Cor 6.28, Cor 2.30 の odd-order 再述. 実装量 ~400 行
- [ ] §4 The Dade Isometry (pp.10-14) — 6 結果 ((2.1)-(2.6)). **TI-subset 上の virtual character isometry**. **新規概念**. *前提: §3* — [調査メモ](notes/peterfalvi/s04_dade_isometry.md): **Phase 2b の山場**, mathlib 完全新規 (~70% 新規実装). 主定理 (2.6) は (a) isometry + (b) virtual character preservation. 形式化方針: **predicate-based (候補 3 推奨)** で `IsDadeIsometry τ hyp` + existence theorem. §5-§8 Coherence の前提. 実装量 ~400-450 行 / 16-18 時間
- [ ] §5 TI-Subsets with Cyclic Normalizers (pp.15-20) — 5 結果 ((3.1)-(3.5)). cyclic normalizer 特殊化. *前提: §4*
- [ ] §6 The Dade Isometry for a Certain Type of Subgroup (pp.21-24) — 5 結果 ((4.1)-(4.5)). Dade 拡張. *前提: §4-§5*
- [ ] §7 Coherence (pp.25-29) — 6 結果 ((5.1)-(5.6)). **Coherence 定義 + 基本性質**. Dade 後の isometry 整合条件. **新規概念**. *前提: §4*
- [ ] §8 Some Coherence Theorems (pp.30-37) — 4 結果 ((6.1)-(6.4)). Coherence 応用定理. Sibley/Reynolds 系含む. *前提: §7*
- [ ] §9 Non-existence of a Certain Type of Group of Odd Order (pp.38-43) — 6 結果 ((7.1)-(7.6)). **≡ BG App.C Theorem C**. Frobenius family の非存在. *前提: §3-§8 + BG §3* — [調査メモ](notes/peterfalvi/s09_nonexistence_certain.md): BG App.C と内容重複 (BG L4759-5005). 形式化方針: **Peterfalvi §9 を一次, BG App.C は section docstring + reference**. Phase 3 で equivalence lemma `OddOrder.BG.AppC.TheoremC ≅ OddOrder.Peterfalvi.S09.TheoremC`. 有限体 F_{p^q} + norm-1 部分群 U + Frobenius H = PU の Lean 形式化設計含む
- [ ] §10 Structure of a Minimal Simple Group of Odd Order (pp.44-49) — 6 結果 ((8.1)-(8.6)). **G の Type I-V 分類定義**. BG Theorem A-E 翻訳. *前提: **BG §10-§16 全面***
- [ ] §11 Maximal Subgroups of G of Types II, III and IV (pp.50-57) — 9 結果 ((9.1)-(9.9)). (9.1) Wielandt 作用, (9.2) Frobenius kernel cohomology. *前提: §10 + BG §11-§13*
- [ ] §12 Maximal Subgroups of Types III, IV and V (pp.58-63) — 7 結果 ((10.1)-(10.7)). (10.7) [S,S] が Frobenius. *前提: §11*
- [ ] §13 Maximal Subgroups of Types III and IV (pp.64-68) — 8 結果 ((11.1)-(11.8)). *前提: §12*
- [ ] §14 Maximal Subgroups of Type I (pp.69-74) — 13 結果 ((12.1)-(12.13)). 型 I は最複雑. *前提: §13 + BG §12 (E)*
- [ ] §15 The Subgroups S and T (pp.75-86) — 17 結果 ((13.1)-(13.17)). **本文最大規模 (365 行)**. S, T の位数・正規化群・指標. §16 直前の最終仕込み. *前提: §14 + BG §15 (M_F)*
- [ ] §16 Non-existence of G (pp.87-92) — 11 結果 ((14.1)-(14.11)). **FT 完了 = G の非存在**. 指標論計算が中心. *前提: §3-§15 + BG §16*

**Peterfalvi 補章** (27 結果, 全 △ = FT 経路外)
- [ ] App: A Theorem of Suzuki (pp.97-134) — 21 結果 (Prop 1-16 in 05.3 + Lemmas in 05.0-05.6). Suzuki 1962: PSL(2,q), Sz(q), PSU(3,q) の二重推移群特性化
- [ ] App: A Special Case of a Theorem of Huppert (pp.135-136) — 1 結果. Huppert 1957 定理の Peterfalvi 流再証明
- [ ] App: On Near-Fields (pp.137-138) — 2 結果. Near-field (Wedderburn 系) の基本
- [ ] App: On Suzuki 2-Groups (pp.139-143) — 4 結果. Higman 分類 Suzuki 2-群
- [ ] App: The Feit-Sibley Theorem (pp.144-150) — 2 結果. Feit-Sibley 1976 定理

### Phase 3-4

- [ ] Phase 3: 最終矛盾の結合 — BG App.C と Peterfalvi §16 の整合・統合
- [ ] Phase 4: `FeitThompson` メイン定理ステートメントと完全証明結合

## ノート・小ロードマップの管理

章節単位のミニロードマップ・調査結果・設計決定は `notes/` 配下に置く:

```
notes/
├── isaacs/
│   ├── ch01_sylow.md          # Isaacs Ch.1 用ミニロードマップ + 調査
│   ├── ch03_split.md
│   └── ...
├── bg/
│   ├── s08_fitting.md         # BG §8 用
│   └── ...
├── peterfalvi/
│   └── ...
└── meta/                       # 章節に紐づかない横断調査・設計決定
    ├── 2026-05-21-namespace-strategy.md
    └── ...
```

各 `.md` には「調査」「計画」「未解決の疑問」を見出しで混在させてよい。本 ROADMAP のチェックリストから対応する `notes/` へリンクして掘り下げる運用。

## 補足ドキュメント

- mathlib カバレッジ詳細 (どの mathlib 資産が使えるか、何が欠けているか): [`notes/meta/mathlib_coverage.md`](notes/meta/mathlib_coverage.md)
- プロジェクトセットアップ状態: メモリ `project_setup_state.md` 参照
