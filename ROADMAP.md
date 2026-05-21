# Odd Order Theorem 形式化ロードマップ

## ゴール

有限群論の **Feit-Thompson 定理**「位数が奇数の有限群はすべて可解である」の **Lean 4 による完全形式化**。AI エージェント駆動の長期プロジェクト。

## スコープ: 3 冊を全部形式化する

| 略称 | 書名 | 役割 |
|------|------|------|
| **Isaacs** | I. M. Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) | 有限群論の前提一式 (Fitting, Hall, Frobenius, ZJ, transfer, 一般化 Fitting `F*`) |
| **BG** | H. Bender & G. Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994) | FT 原論文 Ch.IV (局所解析) + Ch.VI (最終矛盾、App.C で Peterfalvi 改訂版) |
| **Peterfalvi** | T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000) | FT 原論文 Ch.V (指標理論) |

## 方針

- **すべてローカルに書く** (mathlib への PR は将来課題、当面はこのリポジトリ内)
- **mathlib 互換を可能な限り維持** (将来の upstream を見据えて命名・スタイル・namespace を mathlib に寄せる)
- **blueprint は使わない** (教科書 PDF → Lean 直接)
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
│   ├── AppC_FinalContradiction.lean     # Peterfalvi Ch.VI 改訂版
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

Namespace 階層: `OddOrder.Isaacs.Ch1`, `OddOrder.BG.Ch1.S03`, `OddOrder.Peterfalvi.S04` 等。

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

## チャプター進捗チェックリスト

### Phase 1 — Isaacs

- [ ] Ch.1 Sylow Theory (p.1)
- [ ] Ch.2 Subnormality (p.45)
- [ ] Ch.3 Split Extensions (p.65) — Hall, Schur-Zassenhaus
- [ ] Ch.4 Commutators (p.113)
- [ ] Ch.5 Transfer (p.147)
- [ ] Ch.6 Frobenius Actions (p.177)
- [ ] Ch.7 The Thompson Subgroup (p.201) — J(P), ZJ
- [ ] Ch.8 Permutation Groups (p.223)
- [ ] Ch.9 More on Subnormality (p.271) — F*(G)
- [ ] Ch.10 More Transfer Theory (p.295)
- [ ] Appendix: The Basics (p.325)

### Phase 2a — Bender-Glauberman

**Chapter I. Preliminary Results**
- [ ] §1 Elementary Properties of Solvable Groups (p.1)
- [ ] §2 General Results on Representations (p.9)
- [ ] §3 Actions of Frobenius Groups (p.17)
- [ ] §4 p-Groups of Small Rank (p.33)
- [ ] §5 Narrow p-Groups (p.44)
- [ ] §6 Additional Results (p.49)

**Chapter II. The Uniqueness Theorem**
- [ ] §7 The Transitivity Theorem (p.55)
- [ ] §8 The Fitting Subgroup of a Maximal Subgroup (p.61)
- [ ] §9 The Uniqueness Theorem (p.64)

**Chapter III. Maximal Subgroups**
- [ ] §10 The Subgroups M_α and M_σ (p.69)
- [ ] §11 Exceptional Maximal Subgroups (p.80)
- [ ] §12 The Subgroup E (p.83)
- [ ] §13 Prime Action (p.97)

**Chapter IV. The Family of All Maximal Subgroups of G**
- [ ] §14 Maximal Subgroups of Type 𝒫 and Counting (p.105)
- [ ] §15 The Subgroup M_F (p.117)
- [ ] §16 The Main Results (p.123)

**Appendices**
- [ ] App.A Prerequisites and p-Stability (p.135)
- [ ] App.B The Puig Subgroup (p.139)
- [ ] App.C The Final Contradiction (p.145) — Peterfalvi 改訂版
- [ ] App.D CN-Groups of Odd Order (p.153)
- [ ] App.E Further Results of Feit and Thompson (p.157)

### Phase 2b — Peterfalvi 本体 (Character Theory for the Odd Order Theorem)

- [ ] §1 Introduction (pp.1-2)
- [ ] §2 Notation (pp.3-4)
- [ ] §3 Preliminary Results from Character Theory (pp.5-9)
- [ ] §4 The Dade Isometry (pp.10-14)
- [ ] §5 TI-Subsets with Cyclic Normalizers (pp.15-20)
- [ ] §6 The Dade Isometry for a Certain Type of Subgroup (pp.21-24)
- [ ] §7 Coherence (pp.25-29)
- [ ] §8 Some Coherence Theorems (pp.30-37)
- [ ] §9 Non-existence of a Certain Type of Group of Odd Order (pp.38-43)
- [ ] §10 Structure of a Minimal Simple Group of Odd Order (pp.44-49)
- [ ] §11 Maximal Subgroups of G of Types II, III and IV (pp.50-57)
- [ ] §12 Maximal Subgroups of Types III, IV and V (pp.58-63)
- [ ] §13 Maximal Subgroups of Types III and IV (pp.64-68)
- [ ] §14 Maximal Subgroups of Type I (pp.69-74)
- [ ] §15 The Subgroups S and T (pp.75-86)
- [ ] §16 Non-existence of G (pp.87-92)

**Peterfalvi 補章**
- [ ] App: A Theorem of Suzuki (pp.97-134)
- [ ] App: A Special Case of a Theorem of Huppert (pp.135-136)
- [ ] App: On Near-Fields (pp.137-138)
- [ ] App: On Suzuki 2-Groups (pp.139-143)
- [ ] App: The Feit-Sibley Theorem (pp.144-150)

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

- mathlib カバレッジ詳細 (どの mathlib 資産が使えるか、何が欠けているか): メモリ `mathlib_coverage_feit_thompson.md` 参照
- プロジェクトセットアップ状態: メモリ `project_setup_state.md` 参照
