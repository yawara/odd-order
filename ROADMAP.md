# Odd Order Theorem 形式化ロードマップ

## ゴール

有限群論の **Feit-Thompson 定理**「位数が奇数の有限群はすべて可解である」の **Lean 4 による完全形式化**。AI エージェント駆動の長期プロジェクト。

> **FT theorem milestone (2026-07-15)**: `OddOrder.feitThompson` は end-to-end の
> authoritative axiom trace と permanent `AxiomsCheck` の双方で
> `[propext, Classical.choice, Quot.sound]` の標準3公理のみに依存する。これは FT 経路の
> honest carrier / proof spine が完成したことを意味する。3冊の経路外章節・補章まで含む
> 全文形式化は引き続き長期スコープであり、この milestone と区別する。

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
- **教科書として Isaacs を一次参照に採用 (Gorenstein 1968 は「全形式化はしない」)** — BG が "**G**" として引く Gorenstein _Finite Groups_ (1968) の引用は、まず **Isaacs FGT の対応定理に読み替える**。Isaacs が欠く場合 (典型: ZJ / p-stability = **G** Ch.3 §8 / Ch.6 §5 / Ch.8 §2、BG App.A A.2–A.4) のみ Gorenstein 原文 (`references/gorenstein/`) を**行間補完として参照**し Lean に書き起こす (独立の章節形式化はしない)。正本 = CLAUDE.md「やらないこと」(2026-05-28 refinement)
- mathlib 既存資産 (Sylow, p-群, 可解, 冪零, Frattini, Transfer, Focal subgroup, Schur-Zassenhaus, 基本表現論/指標, Maschke, 既約表現, 直交関係, 誘導表現) は再利用
- 命名: `OddOrder.Isaacs.Subgroup.fitting` のように、将来 `Subgroup.fitting` へリネームしやすい形を取る

## フェーズ

| Phase | 内容 | 状態 |
|---|---|---|
| 0 | Lean プロジェクト初期化 (Lean 4.29.1 + mathlib v4.29.1) | ✅ 2026-05-21 |
| 1 | **Isaacs** Ch.1–10 + Appendix の Lean 化 | 🔄 Ch.1–7 sorry-free 完成 (Thm 7.6/7.8 含む 168 flagship axiom-clean)。**Ch.8–10 も 2026-07-17 に実装済・実 sorry 0** (Ch08_PermutationGroups 14 leaf / Ch09_MoreSubnormality 18 leaf / Ch10_MoreTransfer 6 leaf)。旧「FT 経路外で保留」は 2026-07-16 のフェーズ移行で失効 |
| 2a | **BG** Ch.I–IV + 補助 Appendices の Lean 化 | 🔄 **FT が必要とする部分は sorry-free・axiom-clean** (§1–§16 spine + App.A/B/C、spine 消費 = Prop 16.1 のみ)。forward axiom **0 本**。⚠ 旧「FROZEN-COMPLETE (2026-07-02) / BG に active frontier は無い」は**失効** — 2026-07-03 以降 BG に 169 commit が入り、2026-07-19 現在も lane c の active frontier (Thm 6.4 系、issue 0126/9132/9133)。**残 sorry は 11 で内訳も旧記載と異なる**: S14/S15/S16 は 0、AppD_CNGroups 2 / AppE_FurtherResults 9 (2026-07-19 comment-strip census) |
| 2b | **Peterfalvi** 主章 + 補章 の Lean 化 | 🔄 **FT 経路 §§3–§16 完成 (2026-07-15)** — §13 character-degree Core、§14 structure、§15–§16 endgame を実供給へ接続し、FT consumer まで axiom-clean。経路外の補章・historical mis-encoding は長期の全文形式化フェーズに残る。 |
| 3 | 最終矛盾の結合 (BG App.C ≅ Peterfalvi の対応物) | ✅ **App.C 完全形式化** — `theoremC` / `final_contradiction` は sorry-free かつ標準3公理のみ。Pf §16 の `nonexistence_of_G` から実配線済み。 |
| 4 | `FeitThompson` メイン定理ステートメント & 完全結合 | ✅ **2026-07-15 完成** — `nonexistence_of_G` → `BG.AppC.final_contradiction` → `noMinimalSimpleOdd` → `feitThompson_of_noMinimalSimpleOdd` → `feitThompson` の全段を authoritative trace + permanent `AxiomsCheck` で検証。依存は標準3公理のみ。 |

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

> ⚠ 簡略図。実 import spine は Phase 3 以前から交差する: Pf S08/S10/S11/S16 が `OddOrder.BG.Ch4.*` を
> import (BG §16 出力の bridge 消費)、BG `AppC_FinalContradiction` が `Peterfalvi.S16_NonExistenceG` を
> import。「独立に並行進行可」は signature contract 前提の作業並列性を指す (ゲートではない)。

## Lean モジュール構成 (提案 — 2026-05 初期案の記録)

> ⚠ 実レイアウトは大きく成長済 (2026-07-19 実測: `OddOrder/Peterfalvi/` 339 files、BG appendices 11 files。
> hub/leaf 分割規則で増殖)。**現況はディスク (`OddOrder/`) と merge_monitor 冒頭の所有 regex が正**
> (本文中の 🔒 所有マップは FT endgame の履歴)。以下は当初提案の温存。

```
OddOrder.lean                            # entry module — 章 Main を順次 import
OddOrder/
├── Isaacs/                              # Phase 1
│   ├── Ch01_Sylow/
│   │   └── Main.lean
│   ├── Ch02_Subnormality/
│   │   └── Main.lean
│   ├── Ch03_SplitExtensions/            # Hall, Schur-Zassenhaus
│   │   └── Main.lean
│   ├── Ch04_Commutators/
│   │   ├── ForwardFromCh02.lean
│   │   ├── ForwardFromCh03.lean
│   │   └── Main.lean
│   ├── Ch05_Transfer/
│   │   └── Main.lean
│   ├── Ch06_FrobeniusActions/
│   │   └── Main.lean
│   ├── Ch07_ThompsonSubgroup/           # J(P), ZJ
│   │   ├── ForwardFromCh03.lean
│   │   └── Main.lean
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
```

Namespace 階層: `OddOrder.Isaacs.Ch01`, `OddOrder.BG.Ch1.S03`, `OddOrder.Peterfalvi.S04` 等。

## ファイル粒度とトレーサビリティ

各 Lean ファイルは「文献のどこの形式化か」を一目で追える状態を保つ。

### 初期粒度

| 本 | 1 ファイル単位 | 理由 |
|---|---|---|
| Isaacs | 1 章ディレクトリ、入口は `Main.lean` | 章は 20-48 ページ。Forward 系や将来の subsection 分割を章配下に集約する |
| BG | 1 節 (§) | 節が 3-16 ページと小さく、節境界が明確 |
| Peterfalvi | 1 節 (§) | 同上 (1-12 ページ) |

### 育ってから分割 (編集局所性 + レイテンシ基準, 2026-05-27 改訂 — ⚠ SUPERSEDED)

> **正本は CLAUDE.md「ファイル粒度」節 (2026-06-11 メカニズム化)**: trigger = 1,500 行超で ⚠ flag +
> 分割 issue 起票、**実施 owner = hub** (凍結境界 prefix-split、lane は継続)、新主結果 = 新 leaf が
> デフォルト、細分化下限 ~300 行。以下の旧基準 (>4000 行 / <800-1000 行 / レイテンシ唯一基準) は
> 履歴。レイテンシ観点の分析自体は有効な背景資料として温存。

分割の良し悪しを決めるのは **行数ではなく 1 edit-cycle の再ビルドレイテンシ**。`lake build` は
olean = ファイル単位なので、1 行直すとそのファイル全体 + 下流 importer が再 elaboration される
(コスト ≈ 5s 固定 + ~2ms/行、証明密度で大きく変動)。エージェント駆動は edit-build を多数回すので、
この **サイクルレイテンシが唯一の本質的な分割理由**。LLM の可読性は律速ではない (6000 行でも
ページング Read + 文字列マッチ Edit で扱える)。

**いつ割るか**: 「**今まさに伸ばしている章** かつ **leaf 再ビルドが痛い**」とき。目安は >~4000 行
または rebuild >~12-15s。**休眠中の巨大ファイル (編集していない完成章) は行数だけでは割らない** —
キャッシュされて無害で、今割るのは「先回り分割」。行数は粗い代理指標で、重い `simp`/`omega`/
typeclass 探索の多いファイルは行数あたりコストが高い点に注意。

**どう割るか**: import トポロジが効く。線形チェーンだと上流ファイルの編集が下流全部を再ビルドし、
固定 5s × N で **単一ファイルより遅くなりうる**。したがって **active frontier を小さな leaf
`Main.lean` (章内で他から import されない側) に残し、完成・凍結した subsection を上流へ押し出す**:

```
OddOrder/Isaacs/Ch01_Sylow/
                ├── A_Existence.lean    (凍結 subsection, build 1 回でキャッシュ)
                ├── B_Normalizer.lean   (凍結 subsection)
                └── Main.lean           (A,B を import; active frontier = leaf, ここを伸ばす)
```

細分化しすぎ (<~800-1000 行が乱立) は固定 5s/ファイルが効いて逆効果。mathlib upstream 観点でも
focused なファイルは好まれる (soft な副次理由、明確な行数上限は無い)。前例: Ch06/Ch07 分割
([issues/closed/0038](issues/closed/0038-build-perf-bottleneck.md)) — active §7D を Ch07 leaf
`Main` に置き、leaf-edit を ~20s → ~7-9s に短縮。

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
- **2026-05-22** Phase 2 per-section ノート 全節完了: BG 全 16 §1-§16 + App.A-E (22 ファイル), Peterfalvi 全 16 §1-§16 (§1+§2 統合) + App.A Suzuki + App.B-E 統合 (18 ファイル). 各節について TL;DR / 結果表 / Isaacs/BG 対応 / mathlib カバレッジ / Phase 2 形式化着手順 / 未解決 TODO を整理. 合計約 16200 行の調査ドキュメント
- **2026-05-22** Isaacs §2A Thm 2.2 完成 (`le_fitting_iff_isNilpotent_and_isSubnormal` + Ch.1 `opCore.characteristic`/`fitting.characteristic` instance 追加 + `|G|`-induction 補助 `le_fitting_aux`)
- **2026-05-22** Isaacs §2A Thm 2.8 完成 (`isSubnormal_of_permutable_with_conjugates`: permutability ⇒ subnormality, |G|-induction + Zipper Lemma + normal closure + `Subgroup.conj_smul_subgroupOf` 経由の H への permutability transfer)
- **2026-05-22** Isaacs §2A Thm 2.11 (Wielandt abelian-in-F(G)): sorry stub. §2B Thm 2.12 Baer 順方向 (`baer_sup_conj_isNilpotent_of_le_fitting`) 完成, 逆方向は 2.11 依存で stub
- **2026-05-22** Isaacs Ch.3 構造完成: §3A 3.3/3.4 stub, §3B mathlib 対応表 + `IsElementaryAbelian` 定義 + Thm 3.11 stub, §3C `IsHallSubgroup` 定義 + Lemma 3.16 完成 + `IsHallSubgroup.coprime_index` 完成 + Thm 3.13-3.17 stubs, §3D `IsPiSeparable` 定義 + Thm 3.18-3.22 stubs, §3E/§3F docstrings
- **2026-05-22** Isaacs §2B 完成: Thm 2.12 Baer (順方向 + 逆方向 + iff) — Zipper Lemma + Thm 2.2 経由の `|G|`-induction で逆方向を構成. Lemma 2.14 essence (`inv_by_two_involutions`) + structural (`mem_zpowers_or_mul_t_mem`) — closure induction で 4 mul cases + 2 inv cases. Thm 2.13 Matsuyama (`t ∉ O_2(G)` ⇒ 奇素数位数 inversion `x^t = x⁻¹`) — Baer iff + Cauchy + Lemma 2.14. Helpers: `mem_opCore_of_le_fitting_of_isPGroup` (Sylow `p` of F(G) = O_p(G)), `exists_odd_prime_dvd_of_not_pow_two` (Nat 強 induction)
- **2026-05-22** Isaacs §2D axiom 化: Thm 2.18 Zenkov (`zenkov_minimal_le_fitting`), Cor 2.19 (`inf_fitting_ne_bot_of_abelian_card_ge_index`), Thm 2.20 Lucchini (`lucchini_index_normalCore_lt_index`) を statement のみ axiom 化. 各 docstring に Isaacs p.61-63 の完全証明戦略 (|G|-induction + Baer + 計算) を記載. Lucchini が Ch.3 Horosevskii の必須前提
- **2026-05-22** Isaacs Ch.3 §3A Thm 3.3 Horosevskii 完成: `horosevskii_aut_order_lt` (`orderOf σ < Nat.card G`). Lucchini axiom + 半直積 `G ⋊[A.subtype] A` + `inl_range_isComplement_inr_range` (Thm 3.2) + Lemma 2.7 + `inl_aut` + `MonoidHom.map_zpowers` で完全証明 (~120 行)
- **2026-05-22** Isaacs Ch.4-7 dependency 再 audit 完了: [`notes/meta/ch04_07_audit_2026_05_22.md`](notes/meta/ch04_07_audit_2026_05_22.md) — 4 章 (Commutators / Transfer / Frobenius / Thompson) を 4 視点 (forward dep / 章内依存 / mathlib status 含む証明内 API / 先行章依存) で並列再調査. 主結果: (i) Ch.6 ↔ Ch.7 双方向依存は 6.23 一本のみ (axiom 化 clean), (ii) `IsElementaryAbelian` / `Subgroup.thompsonJ` / `IsPStable` を `OddOrder/GroupTheory/` 配下 shared module 化推奨 (BG App.A が再利用), (iii) Cor 3.28 が Ch.4 §4C-§4D 多数定理 (4.26, 4.28-30, 4.34-36, 4.38) の transitive 前提, (iv) Ch.6 6.11 は 6.12 の corollary (実装順序訂正), (v) Ch.5 大部分は Ch.4 完成を待たず実装可 (Ch.4 dep は 5.17 と 5.30 のみ), (vi) Ch.6 本文は Hall-Higman 3.21 不使用. 既存 ch04/ch06 ノートの事実誤認 4 件訂正済
- **2026-05-23** Isaacs Ch.1 (Sylow Theory) §1G Chermak-Delgado 省略判断 re-audit: [`notes/meta/ch01_audit_2026_05_23.md`](notes/meta/ch01_audit_2026_05_23.md) — fresh grep で BG/Peterfalvi/Ch.2-10 下流引用 0 件再確認, **§1G 省略を維持**. ただし tactical refinement: §1G 実装が要求する 2 helper (H1 `card_HK·card_inf=card_H·card_K`, H2 `le_centralizer_centralizer`) は mathlib v4.29.1 不在で独立に upstream 価値高 ⇒ Ch.2+ で必要時 standalone 追加方針. §1G 本体は (1) `m_G(H)` 記法の下流出現, (2) H1/H2 累積実装, (3) Phase 1 完成後の upstream pivot のいずれかでトリガー. §1G stub docstring 更新済
- **2026-05-23** (同日) §1G Chermak-Delgado **実装方針に決定変更**: ユーザ判断により mathlib upstream のため Thm 1.41-1.46 を実装する. 実装計画 [`notes/meta/ch01_chermak_delgado_plan.md`](notes/meta/ch01_chermak_delgado_plan.md) — `OddOrder/Mathlib/Subgroup.lean` (H1, H2, H3, `centralizer_sup` helper) + `OddOrder/GroupTheory/ChermakDelgado.lean` (`chermakDelgadoMeasure`, `chermakDelgadoLattice`, `chermakDelgadoSubgroup` + Thm 1.41-1.46) ~200 LOC / ~2 日. 確認済新情報: Galois connection `Subgroup.le_centralizer_iff` (Centralizer.lean:54) のおかげで H2 は **2 行 proof** (`le_centralizer_iff.mpr le_rfl`); `Sublattice` 構造体 mathlib に既存 (Order/Sublattice.lean); `Subalgebra.centralizer_sup` あり / Subgroup 版なし
- **2026-05-23** Isaacs Ch.3 (Split Extensions) 4 視点 audit 完了: [`notes/meta/ch03_audit_2026_05_23.md`](notes/meta/ch03_audit_2026_05_23.md) — mmd 欠落 (MISSING_PAGE) のため PDF (pp.78-125) 直読 + 既存 `ch03_split.md` + Ch03_SplitExtensions/Main.lean (1029 行) で §3A-§3B / §3C-§3D / §3E-§3F の 3 並列 audit. 主結果: (i) **Cor 3.28 コスト訂正 ~1-2 週 Tier 1** (旧 audit "8-12 週" 悲観すぎ): Lem 3.24 + Thm 3.27 のみ依存, **Ch.4 §4A-§4B と並列着手可**, (ii) **`Ch06_FrobeniusActions/ForwardFromCh03.lean` (3.21 Hall-Higman) 配置ミス**: Ch.6 は 3.21 を全く使わず, 下流引用は Ch.4 4.33 + Ch.7 7.5/7.6 のみ ⇒ Ch.7 dir 移動推奨 (docstring に flag 追加済), (iii) `IsElementaryAbelian` (Ch.3 L455) を Ch.6/Ch.7 着手前に `OddOrder/GroupTheory/` 配下 shared 化推奨 (subgroup-based form), (iv) Thm 3.4 は ✅ 完成済 (既存ノートの stale TODO 訂正), (v) `isSolvable_def` (auto-gen `@[mk_iff]`) が 3.9 exact match, `derivedSeries_eq_bot_iff` 等の想定名は mathlib v4.29.1 不在, (vi) §3F (3.35, 3.36) は FT 経路完全不要, 現 weak `cyclic_quotient_lift` で恒久充分, (vii) 3.31 Hartley-Turull は BG/Peterfalvi 名前引用 0 件で Phase 4 までも skip 可. 既存 ch03 ノート 4 件 + Ch.4/Ch.6 forward placeholder docstring 2 件訂正済
- **2026-05-23** Isaacs Ch.1 §1G **Chermak-Delgado 全実装完了** (Thm 1.41-1.46, 全 6 結果). 配置: [`OddOrder/Mathlib/Subgroup.lean`](OddOrder/Mathlib/Subgroup.lean) (helper: `card_HK_mul_card_inf_eq_card_mul_card`, `le_centralizer_centralizer`, `centralizer_centralizer_centralizer`, `centralizer_sup`) + [`OddOrder/GroupTheory/ChermakDelgado.lean`](OddOrder/GroupTheory/ChermakDelgado.lean) (定義 `chermakDelgadoMeasure` / `chermakDelgadoLattice` / `chermakDelgadoSubgroup` + Lemma 1.42-1.43 + Thm 1.44 (a)(b)(c) + Cor 1.45 全 4 性質 (M ∈ L, abelian, Z(G) ≤ M, characteristic) + Thm 1.41 主定理 + Cor 1.46). [`OddOrder/Isaacs/Ch01_Sylow/Main.lean`](OddOrder/Isaacs/Ch01_Sylow/Main.lean) §1G section は import + export 形に変更. mathlib upstream 視野の shared module 化. **Isaacs Ch.1 全 46/46 結果完成**
- **2026-05-23** (同日) **Isaacs Ch.5 Transfer ファイル作成完了**: [`OddOrder/Isaacs/Ch05_Transfer/Main.lean`](OddOrder/Isaacs/Ch05_Transfer/Main.lean) 新規 (~175 行). mathlib カバレッジが Ch.5 中最厚 (~40-50%) のため no-wrapper policy 適用 — section docstring 内 mapping table で Isaacs 番号 ↔ mathlib API 対応を記録. Wrapper 実装: `abelian_sylow_commutator_inf_eq_focal` (5.18 = `commutator_inf_eq_focalSubgroup` 特殊化) のみ. mathlib 直接: 5.1/5.2 (`MonoidHom.transfer`), 5.5 (`transfer_eq_prod_quotient_*`), 5.6 (`transferCenterPow`), 5.7 (`card_commutator_le_*`), 5.13 Burnside (`ker_transferSylow_isComplement'`), 5.14 (`IsCyclic.isComplement'`), 5.15-5.17 Z-group (`IsZGroup` API), 5.20-5.21 Focal Subgroup Theorem ⭐ (`commutator_inf_eq_focalSubgroup`). §5E Frobenius (5.25-5.30) は docstring 保留 (Ch.4 §4D 4.36 依存)
- **2026-05-23** (同日) **Isaacs Ch.4 §4A Commutator basics 7 結果完成 + §4B Cor 4.10 完成**: [`OddOrder/Isaacs/Ch04_Commutators/Main.lean`](OddOrder/Isaacs/Ch04_Commutators/Main.lean) (~245 行). 完成: (i) `subgroup_le_normalizer_commutator_self` (Lem 4.1 左) — H ≤ N(⁅H,K⁆), H/K 正規性仮定なし版. Identity `g·⁅a,b⁆·g⁻¹ = ⁅ga,b⁆·⁅b,g⁆` (private `conj_commutator_split`) + `Subgroup.closure_induction` で証明, (ii) `subgroup_le_normalizer_commutator_self_right` (Lem 4.1 右) — `commutator_comm` 経由, (iii) `le_normalizer_of_commutator_le` / `commutator_le_of_le_normalizer` / `commutator_le_iff_le_normalizer` (Lem 4.3 三方向) — element identity `k·x·k⁻¹ = ⁅k,x⁆·x` + normalizer 性質, (iv) `commutator_commutator_le_of_rotate` (Cor 4.10 = Three-subgroups mod N) — 商写像 G→G/N で push し mathlib `commutator_commutator_eq_bot_of_rotate` 適用. `open scoped commutatorElement` 必須 (Bracket scoped instance). §4B-§4D 残 (Lem 4.6 chapter ハブ 5 引用, Thm 4.11 lcs additivity, 4.28-4.36 FT クリティカル) は docstring scaffolding
- **2026-05-23** (同日) **Isaacs Ch.3 §3D Thm 3.21 Hall-Higman 1.2.3 statement 確定** (proof sorry): `hall_higman_1_2_3` — G π-separable + oPiCore π' = ⊥ ⇒ centralizer(oPiCore π) ≤ oPiCore π. 5 段階証明戦略 (B = C ⊓ O_π(G) 設定 → B π-group + C 正規 → C/B 非自明 characteristic K/B が π or π'-group → 各 case で矛盾) を docstring 詳細記載. 実装規模 ~150-200 LOC 推定. **下流被引用**: Ch.4 Thm 4.33 + Ch.7 Thm 7.5/7.6 の 3 箇所. proof は Step 1-5 を補題分解する次セッションで完成予定
- **2026-05-23** (同日) **Isaacs Ch.4 Lem 4.6 (G' = ⁅A,⊤⁆) 完全証明完成** ⭐ (sorry 消去): `commutator_eq_commutator_of_normal_abelian_cyclic_quotient`. A ⊴ G abelian + G/A cyclic ⇒ commutator G = ⁅A, ⊤⁆. **章内 5 引用 + Ch.5/7/10 で多用の章内ハブ**. proof: mathlib `commutative_of_cyclic_center_quotient` (`Cyclic.lean:180`) 経由 5-step: (1) ⁅A,⊤⁆ ≤ A (commutator_top_left_le_iff + commutator_comm), (2) lift Q := G/⁅A,⊤⁆ → G/A (QuotientGroup.lift), (3) f.ker ⊆ Z(Q) (∵ y ∈ A, g ∈ G ⇒ ⁅g,y⁆ ∈ ⁅A,⊤⁆ ⇒ Q で gy = yg; QuotientGroup.eq_iff_div_mem 利用), (4) Q commutative (Cyclic.lean lemma 適用), (5) commutator G ⊆ ker(mk' ⁅A,⊤⁆) = ⁅A,⊤⁆. 後半 G' ≅ A/(A∩Z(G)) は別途
- **2026-05-23** (同日) **Isaacs Ch.4 §4B Thm 4.11 (lcs additivity) + Cor 4.13 (derived ⊆ lcs exponential) 完全証明完成** ⭐: (i) `commutator_lowerCentralSeries_le` — `⁅lcs i, lcs j⁆ ≤ lcs (i+j+1)` (mathlib indexing で Isaacs `⁅G^i, G^j⁆ ≤ G^{i+j}`). 証明: `j`-induction (`i` free), step は Cor 4.10 `commutator_commutator_le_of_rotate` を `H₁ = lcs j, H₂ = ⊤, H₃ = lcs i, N = lcs (i+j+2)` で適用 (h1: `⁅⊤, lcs i⁆ = lcs (i+1)` 経由で IH at (i+1); h2: IH + commutator_mono + lcs_succ 定義). mathlib `Characteristic (lcs n)` instance が `[N.Normal]` 自動提供. ~30 LOC. (ii) `derivedSeries_le_lowerCentralSeries_two_pow_sub_one` — `derivedSeries G r ≤ lcs G (2^r - 1)`. mathlib 既存 `derived_le_lower_central` (`derived r ≤ lcs r`) より strictly stronger (r ≥ 2 で). 証明: `r`-induction + commutator_mono + **Thm 4.11** + 算術 (`pow_succ` + omega + `Nat.one_le_two_pow`). ~10 LOC. **下流**: Thm 4.11 は Lucchini K=⊥ aux 解消経路 (Ch.2 §2D Z(F(G)) absorbs G-minimal 補題)
- **2026-05-23** (同日) **Isaacs Ch.4 §4B Cor 4.12 + 量的境界 + iterCommutator インフラ完備** ⭐ **§4B コア完成**: (i) **Cor 4.12** `iterLeftCommutator_mem_lowerCentralSeries` — `iterLeftCommutator g [g₁..gₙ] ∈ lcs G n` (重み n+1 左結合交換子). `List.foldl ⁅·, ·⁆` 定義 + accumulator-depth 汎用補題. (ii) **derived 長量的境界** `derivedSeries_eq_bot_of_lowerCentralSeries_eq_bot` — `lcs G m = ⊥ ⇒ derivedSeries G (Nat.log 2 m + 1) = ⊥`. mathlib qualitative `IsNilpotent → IsSolvable` から explicit upper bound `1 + ⌊log₂ m⌋` へ. (iii) **iterCommutator インフラ** — Lucchini K=⊥ 「Z(F(G)) absorbs G-minimal normal」補題の前哨基地: `iterCommutator E F : ℕ → Subgroup G` (= `⁅...⁅E, F⁆, F⁆..., F⁆`) 定義 + `iterCommutator_le_lowerCentralSeries_map` (`E ≤ F ⇒ iter E F n ≤ (lcs ↥F n).map F.subtype`) + `iterCommutator_normal` + `iterCommutator_succ_le_self` (antitone) + `iterCommutator_eq_bot_of_isNilpotent` (`F` 冪零 ⇒ ∃n, iter = ⊥). §4B (Cor 4.10, Thm 4.11, Cor 4.12, Cor 4.13, 量的境界) **コア完成**. Mann 4.14-4.19 は Phase 1 skip 可 (audit 確認済). 次は Lucchini K=⊥ 本体 + Hall-Higman 3.21 sorry 消去 + §4C/§4D 着手
- **2026-05-23** (同日) **Isaacs Ch.4 Z(F(G)) absorbs G-minimal normal 補題完成** ⭐ (Lucchini K=⊥ aux 核補題): `le_centralizer_of_isMinimalNormal` — E ⊴ G minimal normal + E ≤ F + F ⊴ G + F 冪零 ⇒ E ≤ centralizer F. 証明: iterCommutator 降下列 + smallest-k descent + minimality (~30 LOC). 補助 `iterCommutator_le_self` も追加. **下流**: Ch.2 §2D Lucchini K=⊥ aux の axiom 解消への核. Cor 2.19 + AE 構造解析 + IH on G/E と組み合わせて `lucchini_K_bot_aux` を theorem 化予定. Isaacs PDF p.62-63 の Lucchini Thm 2.20 proof 確認済
- **2026-05-23** (同日) **Isaacs Ch.3 §3D oPiCore.isPiGroup ⭐** (Hall-Higman 3.21 critical bottleneck 解消): 有限 G で `Subgroup.IsPiGroup π (oPiCore π G)`. 証明: `Finset.sup_induction` を predicate `H ↦ H.Normal ∧ IsPiGroup π H` で適用; closure step は前 helper `Subgroup.IsPiGroup.sup_of_normal` (H₁, H₂ ⊴ G + π ⇒ H₁ ⊔ H₂ ⊴ G + π, `card_HK_mul_card_inf_eq_card_mul_card` 経由) を使用. ~30 LOC. これで Hall-Higman 3.21 の `B := C ⊓ O is π-group` 仮定が成立. **残**: K = preimage of K/B (correspondence) + Schur-Zassenhaus complement (mathlib `exists_right_complement'_of_coprime`) + O_π'(K) characteristic in K (↥K の自分 oPiCore に同 instance 適用). 並行で Lucchini K=⊥ prereq 完備 + Hall-Higman structural prereq 完備
- **2026-05-23** (同日) **Isaacs Ch.1 §1D + Mathlib.Subgroup: Lucchini K=⊥ prereq 2 件追加**: (i) `fitting_map_subtype_le_fitting` (Ch.1 §1D) — `M ⊴ G ⇒ (fitting ↥M).map M.subtype ≤ fitting G`. `fitting.isNilpotent` + `equivMapOfInjective` + `nilpotent_of_mulEquiv` + `nilpotent_normal_le_fitting` で ~7 LOC. (ii) `inf_sup_eq_sup_inf_of_normal_of_le` (Mathlib.Subgroup) — **Dedekind modular law** `E ⊴ G, E ≤ M ⇒ M ⊓ (E ⊔ A) = E ⊔ (M ⊓ A)`. mathlib v4.29.1 `IsModularLattice (Subgroup G)` instance は `[CommGroup G]` 限定で非可換版不在. `Subgroup.mem_sup_of_normal_left` で element-level 計算 ~15 LOC. **Lucchini K=⊥ aux 解消で残: M abelian/non-abelian の 2 case 分析** (各 ~50-80 LOC)
- **2026-05-23** (同日) **Isaacs Ch.4 Lucchini K=⊥ 1st step composition 完成**: `exists_isMinimalNormal_le_fitting_le_centralizer_fitting` — G 非自明有限 + A abelian + `|A| ≥ |G:A|` ⇒ ∃ E ⊴ G minimal normal で `E ≤ F(G) ∧ E ≤ centralizer F(G)`. 既存の Cor 2.19 + exists_isMinimalNormal_le + Z(F(G)) absorbs 補題を ~10 LOC で連結. 書籍 p.62 Lucchini proof の最初の 3 ステップに対応. **残**: (i) E elem abelian p-群 結論 (E ≤ F(G) nilpotent + minimal normal 経由, ~30-50 LOC), (ii) M abelian case (φ(m)=m^p homo + B ≤ p + M=B 矛盾, ~50-80 LOC), (iii) M non-abelian case (Z(M) cyclic + B ∩ F(M) ⊆ Z(M) characteristic, ~50-80 LOC), (iv) glue together with IH on G/E (~30 LOC). **`ForwardFromCh02.lean` への移行は import structure 整理が必要** (現状 Ch03 が ForwardFromCh02 を import するため Main.lean からの逆参照不可)
- **2026-05-23** (同日) **Isaacs Ch.4 Thm 3.11 全体の nilpotent 部分群版 + Lucchini 1st step 拡張**: 3 補題追加で Lucchini K=⊥ aux **前提完全完成**: (i) `commutator_lt_self_of_isNilpotent_subtype` — `↥E` 冪零 + 非自明 ⇒ `⁅E, E⁆ < E` (mathlib `IsSolvable.commutator_lt_of_ne_bot` の冪零部分群版). (ii) `isCommutative_of_isMinimalNormal_of_isNilpotent_subtype` — Thm 3.11 part 1 (minimal normal + abelian) の nilpotent 版. (iii) `isElementaryAbelian_of_isMinimalNormal_of_isNilpotent_subtype` — Thm 3.11 全体 (minimal normal + elem abelian p-group) の nilpotent 版 (~60 LOC, Ch.3 既存 proof structure を copy + abelian step を (ii) に置換). `exists_isMinimalNormal_le_fitting_le_centralizer_fitting` も拡張: `Group.IsNilpotent ↥E` を `subgroupOfEquivOfLe` 経由で取得し elem abelian p-group 結論を出力に追加. **Lucchini K=⊥ aux 前提**: Cor 2.19 ✅ + minimal normal exists ✅ + Z(F(G)) absorbs ✅ + E nilpotent ✅ + E elem abelian ✅ + F(M) ⊆ F(G) ✅ + Dedekind law ✅. 残: body の M abelian/non-abelian 2 case 統合
- **2026-05-23** (同日) **Isaacs Ch.3 §3D + OddOrder.Mathlib.Subgroup: Hall-Higman 3.21 prereq + helper 群完備** (ralph-loop session 累計): `oPiCore.characteristic` instance + `exists_oPiCore_ne_bot_or_oPi'Core_ne_bot` + `oPiCore.isPiGroup` ⭐ (critical bottleneck 解消, `Finset.sup_induction` 経由) + `Subgroup.IsPiGroup.{le_oPiCore, sup_of_normal, subgroupOf, bot, le, map_equiv}` + `IsPiGroup.of_normal_quotient` (extension) + `hall_higman_case_pi_K_le_B` (case π core 1-liner) + `hall_higman_case_pi_contradiction` (case π full closure) + `eq_bot_of_isPiGroup_of_oPiCore_eq_bot` (case π' closure helper) + `Nat.coprime_of_isPiGroup_of_isPiGroup_compl` (case π' Schur-Zassenhaus coprime). Mathlib.Subgroup: `eq_bot_of_le_of_normal_of_normalCore_eq_bot`, `powMonoidHom_range_characteristic`, `inf_sup_eq_sup_inf_of_normal_of_le` + `eq_sup_inf_of_le_sup_of_normal_of_le` (Dedekind modular law 両形式), `nontrivial_quotient_of_ne_top`. **Hall-Higman 3.21 prereq 完全完成**: case π closure 自動化, case π' は Schur-Zassenhaus (mathlib `exists_right_complement'_of_coprime`) 適用後の H ⊴ K + O_π'(K) characteristic chain で完結予定. 残: body assembly (K = preimage of K' via correspondence theorem, ~50 LOC case π + ~80 LOC case π') は multi-iteration. 並行で Lucchini K=⊥ aux も完全 prereq + body multi-iteration 状態.
- **2026-05-23** (同日) **Isaacs Ch.3 Thm 3.21 Hall-Higman 1.2.3 ⭐⭐ sorry-free 完成** (FT クリティカル, AxiomsCheck flagship 入り): `hall_higman_1_2_3` — G π-separable + `oPiCore π' G = ⊥` ⇒ `centralizer(oPiCore π G) ≤ oPiCore π G`. 主定理は ~25 LOC で `by_contra` + `B := C ⊓ O < C` + `CB := C.map (mk' B) ≠ ⊥` + `exists_oPiCore_ne_bot_or_oPi'Core_ne_bot (G := ↥CB) π` で `oPiCore π CB ≠ ⊥ ∨ oPiCore {p ∉ π} CB ≠ ⊥` 場合分け + `hall_higman_case_pi_body` / `hall_higman_case_pi'_body` で各 case False. case π body (~60 LOC): K = preimage of `oPiCore π CB.map CB.subtype` 経由で `K ≤ C ∧ B < K ∧ K/B π-group` ⇒ `K ≤ O ∧ K ≤ C` で `K ≤ B` 矛盾. case π' body (~130 LOC): 同様に K 構築 + `B.subgroupOf K` π-group + index π'-group ⇒ Schur-Zassenhaus complement H' + `normal_complement_of_commute` (B ⊆ O かつ H' ⊆ C ⇒ B と H' 可換) で H' ⊴ K + H' π'-group ⇒ `H' ≤ oPiCore {p ∉ π} K` ⇒ G に lift して `oPiCore {p ∉ π} G = ⊥` から H' = ⊥ だが `|H'| > 1` で矛盾. 全 LOC ~350 (helpers 200 + cases 130 + main 25). **下流被引用**: Ch.4 Thm 4.33 + Ch.7 Thm 7.5/7.6 の 3 箇所. AxiomsCheck.lean に flagship 追加: 3 標準公理のみで unconditional.
- **2026-05-23** (同日) **Isaacs Ch.5 Lemma 5.12 (N_G(P) controls C_G(P) fusion) 完成**: `normalizer_controls_centralizer_fusion` — P Sylow_p(G), x, y ∈ C_G(P) が G で共役 ⇒ N_G(P) で共役. 証明: K = C_G(y) を構築し P ≤ K と gPg⁻¹ ≤ K を示す (centralizer のメンバシップを直接計算). 両方を Sylow p ↥K に `Sylow.subtype` で promote, Sylow II in K (`MulAction.exists_smul_eq` via `Sylow.isPretransitive_of_finite`) で `c ∈ K, c • Pg_K = P_K`. `Sylow.smul_subtype` + `Sylow.subtype_injective` で G に戻すと `c • g • P = P`. `mul_smul` で `(c*g) • P = P` ⇒ `c*g ∈ N_G(P)` (`Sylow.smul_eq_iff_mem_normalizer`). `(cg) x (cg)⁻¹ = c y c⁻¹ = y` (c ∈ K = C_G(y)) で完了. ~50 LOC. **下流**: Thm 5.13 Burnside (mathlib 既収載) の本質的補題, Cor 5.23 (abelian Sylow ⇒ N controls p-transfer) で再利用.
- **2026-05-23** (同日) **BG GroupTheory: IsMetacyclic shared module 新規** (Phase 2a 第1波 audit で確定した 16 shared modules の 1 件目): [`OddOrder/GroupTheory/IsMetacyclic.lean`](OddOrder/GroupTheory/IsMetacyclic.lean). `IsMetacyclic G := ∃ N ⊴ G, IsCyclic N ∧ IsCyclic (G ⧸ N)` def + `of_isCyclic` (N = ⊥, `↥⊥` Unique で trivially cyclic + `isCyclic_of_surjective (mk' ⊥)` で `G ⧸ ⊥` transfer) + `isSolvable` (cyclic-by-cyclic extension, `IsCyclic.commGroup` + `CommGroup.isSolvable` + `solvable_of_ker_le_range N.subtype (mk' N)`). mathlib v4.29.1 に IsMetacyclic 不在確認済 (0 hits). BG §4 Lem 4.10 / Prop 4.11 (Huppert) / Thm 4.12 で必須. 86 LOC, 部分群閉包 (非自明) と商閉包 (trivial) は後の補強で.
- **2026-05-23** (同日) **BG Phase 2a 第 1 波 6 節 4 視点 audit 完了**: [`notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`](notes/meta/bg_phase2a_wave1_audit_2026_05_23.md) — §1 / §2 / §4 / §5 / App.A / App.B を 4 視点 (forward / internal hub-spoke / mathlib proof-internal / preceding per-target) で 6 並列 sub-agent + synthesis. 統合観点 5 件: (i) **App.B + Thm A.5 を Phase 2a で完全スキップ可** (~570 行 / 10-13 日節約) — App.B は FT-orphan (§1-§16 + App.C/E + Peterfalvi 全 0 cite, 唯一の本文使用は §6 advertisement + App.D parenthetical), overview L95「App.B は App.A 不要で独立」は誤り (B.3+B.4 が Thm A.5 cite), 既存「Lem B.1-B.5」は B.5 不在で計 4 結果のみ; (ii) **App.A は §6 の上流** (既存「下流」方向逆), 着手順は BG §1+§2 → App.A → §6, さらに **BG §1 Prop 1.8/1.15(b) + BG §2 Thm 2.6 完成必須** (既存ノート未捕捉); (iii) **§2 は FT 中核** (既存「§9 1-2 cite skip」完全に逆), 実測 §3×5 + §4 + §15 + App.A = 8+ cites, Thm 2.5/2.6 が §3 Thm 3.4 + App.A Thm A.1 入力, Lem 2.3 (Fong-Swan) のみ forward=0 で defer 可; (iv) **A.4(b) ≠ Isaacs 7.6 (corollary, 同値ではない)** — 7.6 ⇒ A.4(b) trivial, 逆方向は J(P) ⊴ G の追加要; (v) **`OddOrder/GroupTheory/` 新規 shared module 16 件**が真の Phase 2a 前提条件 (Ch.4-7 audit 拡張): `OpResidual` (O_p/O_{p'}/O_{p',p}, mathlib 0 hit) ~150-250 LOC, `InvariantSubgroup` (A-invariant Sylow/Hall), `ChiefSeries` (mathlib 不在), `OmegaSubgroup`, `PRank` (mathlib `Group.rank` は min-generators で BG `m(A)` 不適), `FrattiniPGroup` (1.7(b)(d)), `MinimalNormal`, `Thompson` (Ch.7), `PStable`, `IsExtraspecial`, `IsMetacyclic`, `SCN`, `AutElementaryAbelian` + 表現論側 `Clifford`, `AbsolutelyIrreducible`, `EigenspaceUnderCyclicAction`, `PGroupFixedVector`. 既存 per-section ノート 6 件 + `_overview.md` + `phase2_cross_refs.md` に audit log/inline 訂正済 (Lem 1.1 "43+"→0, Prop 1.2 "22"→6, Thm 1.13≠Isaacs 4.31, "Jacobson Density 未実装"→`SimpleModule/Basic.lean:582`, "narrow def r(R)≤2"→§1 L354 verbatim, "§4-§5 独立"→6 cites, "Lem B.1-B.5"→B.1-B.3+Thm B.4, "Isaacs Thm 3.8.1/3.8.3"→Isaacs 不在 (Gorenstein 番号系) 等 6 ノート × 5-8 件).
- **2026-05-23** (同日) **Isaacs Ch.5 Lemma 5.11 (Hall transfer index) 完成**: `ker_transfer_sup_eq_top_of_hall` — H π-Hall + ϕ : H →* A (可換有限, |A| ∣ |H|) ⇒ `ker(transfer ϕ) · H = G`. ~10 LOC. 1st iso (`quotientKerEquivRange`) + Lagrange (`card_subgroup_dvd_card`) で `(transfer ϕ).ker.index ∣ |A|`. 仮定 `|A| ∣ |H|` + Hall coprime + `Nat.Coprime.coprime_dvd_left` で `Coprime ker.index H.index`. Lemma 3.16 (`sup_eq_top_of_coprime_index`) で sup = ⊤. **下流**: Thm 5.13 Burnside (mathlib 既収載) の本質的補題. 通常 A := H/H' で適用するとき |A| ∣ |H| が自然成立.
- **2026-05-25** **Isaacs Ch.5 FT-critical transfer surface 整備**: [`OddOrder/Isaacs/Ch05_Transfer/Main.lean`](OddOrder/Isaacs/Ch05_Transfer/Main.lean) に BG/Peterfalvi 下流向け入口 `focalSubgroupTheorem` (Isaacs 5.21 / BG 1.17; `G'∩P`, `A^p(G)∩P`, `ker(transferFocal)∩P` の focal subgroup 等式を package) と `hasNormalPComplement_of_sylow_normalizer_le_centralizer` (Isaacs 5.13 / BG 1.18) を公開. 既存 §5E chain `hasNormalPComplement_iff_controlsOwnFusion` (5.25), `hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer` (5.26), `hasNormalPComplement_of_no_prime_dvd_pow_sub_one` (5.29), `normal_p_complement_of_order_p_central_odd` (5.30) を AxiomsCheck 対象に追加. Ch.5 は FT クリティカル公開面が sorry-free; 5.24 は BG/Peterfalvi 直接被引用無しで後回し.
- **2026-05-23** (同日) **Isaacs Ch.3 §3E IsAInvariant 完備 + Ch.4 Lem 4.32 完成** ⭐ (ralph-loop session 累計 §4D 初の theorem): IsAInvariant suite を ~20 lemmas に拡張 (`{top, bot, inf, sup, iInf, iSup, of_characteristic, derivedSeries, lcs, center, commutator, normalizer, centralizer, normalCore, smul_mem, inv_smul_mem, restrict, subgroupOf}`). OddOrder.Mathlib に `SemidirectProduct.{finite, IsPGroup.semidirectProduct, IsNilpotent.semidirectProduct_of_pGroup}` + `Subgroup.{fixedPointsOfMulAut, map_centralizer_eq_of_bijective}` 追加. Ch.4 Main に `iterCommutator_{le_lowerCentralSeries, eq_bot_of_isNilpotent_ambient}` (E ≤ F 不要の一般版) + `commutator_lt_self_of_isNilpotent_ambient` (strict 降下) を追加. **Lem 4.32 両半完成** (前半: `commutator_inl_inr_lt_inl_of_pgroup_action` = P p-群 on G p-群 ⇒ ⁅inl(G), inr(P)⁆ < inl(G) in Γ = G ⋊ P; 後半: `fixedPoints_ne_bot_of_pgroup_action_pgroup` = C_G(P) > 1 via mathlib `IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point`). +Hall-Higman 3.21 系 `centralizer_oPiCore_eq_center`.
- **2026-05-23** (同日) **BG GroupTheory: IsExtraspecial + SCN shared modules 新規** (Phase 2a 第1波 audit で確定した 16 shared modules の 2/3 件目): (i) [`OddOrder/GroupTheory/IsExtraspecial.lean`](OddOrder/GroupTheory/IsExtraspecial.lean) (~85 LOC). BG §2 Thm 2.5 + §4 Lem 4.15 + Isaacs Ch.6 §6 で必要. mathlib 不在確認済 (RootSystem の同名語別概念). 教科書 (Isaacs Defn 6.6 / Aschbacher §23) 標準定義 `Z(G) = [G,G] = Φ(G) ∧ |Z(G)| = p` を 4 field structure 化 (`isPGroup` / `commutator_eq_center` / `frattini_eq_center` / `center_card`) + 派生補題 `commutator_eq_frattini` / `commutator_card` / `frattini_card`. **mathlib namespace 注**: `frattini` は `_root_` (`Subgroup.frattini` ではない). (ii) [`OddOrder/GroupTheory/SCN.lean`](OddOrder/GroupTheory/SCN.lean) (~70 LOC). BG §4 Prop 4.4 + §4 Lem 4.7 + §5 Lem 5.1 + Isaacs Ch.7 で必要. mathlib 不在確認済. 教科書定義 `A ⊴ G ∧ A abelian ∧ centralizer A = A` を 3 field structure 化 (`isNormal` / `isMulCommutative` / `selfCentralizing`) + `le_centralizer` / `centralizer_le` 補題. **`SCN_n` (rank ≥ n) は `PRank.lean` 完成後に追加** (audit で分離決定). Build 1931/1931 OK.
- **2026-05-23** (同日) **BG GroupTheory: OmegaSubgroup shared module 新規** (Phase 2a 第1波 audit で確定した 16 shared modules の 4 件目): [`OddOrder/GroupTheory/OmegaSubgroup.lean`](OddOrder/GroupTheory/OmegaSubgroup.lean) (~80 LOC). BG §1 Thm 1.11/Cor 1.12/Thm 1.13 + §4 全節 + §5 全節 + Isaacs Ch.4 §4D Thm 4.36 で必要. mathlib v4.29.1 不在確認済 (`Omega1`/`Omega`/`omega1`/`omegaSubgroup` 0 hits in `Mathlib/GroupTheory/`). 定義 `Omega p n G := Subgroup.closure {g : G | g^(p^n) = 1}` (一般 G, abelian 仮定なし). 補題 2 件: `mem_of_pow_eq_one` (生成元の membership) + `mono` (`m ≤ n ⇒ Omega p m G ≤ Omega p n G`, 生成元 inclusion 経由). **mathlib name gotcha**: `Nat.pow_add` (Lean core protected) を使う (`pow_add` は monoid 一般版で型推論失敗、`rewrite` がパターン unify 失敗). 将来補強: characteristic/normal, abelian 同値, `Omega_zero = ⊥`. Build 1932/1932 OK.
- **2026-05-23** (同日) **BG GroupTheory: PRank shared module 新規 (軽量版)** (Phase 2a 第1波 audit で確定した 16 shared modules の 5 件目): [`OddOrder/GroupTheory/PRank.lean`](OddOrder/GroupTheory/PRank.lean) (~55 LOC). BG §4 全節 (Blackburn rank theory) + §5 で必要. mathlib `Group.rank` は **min generators 数** (Rank.lean) で BG `r_p(G)` (= max log_p of elementary abelian p-subgroup) と別概念 ⇒ 命名衝突回避のため `pRank` 採用. 定義 `pRank G p := ⨆ A : {A : Subgroup G // A.IsElementaryAbelian p}, Nat.log p (Nat.card A.val)` (noncomputable, iSup based). `[Finite G]` 下でのみ意味ある値. 性質補題は **future work** (BddAbove 仮定下の `le_ciSup` 適用要). 教科書 `m(A) = log_p |Ω₁(A)|` for abelian は後の補強で. Build 1933/1933 OK.
- **2026-05-23** (同日) **Isaacs Ch.3 §3F Thm 3.35 強版 (uniqueness) 完成**: [`OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`](OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean) `cyclic_quotient_extension_unique` (~20 LOC). N ⊴ G + gN が G/N 生成元 + θ θ' : G →* G₀ が N 上一致 + g → g₀ ⇒ θ = θ'. u = x * g^i (x ∈ N) zpowers 分解 + map_mul + map_zpow. Thm 3.36 existence (Sym(Ω) realization) は次セッション. Phase 3 (§3F) 部分完成.
- **2026-05-24** **Isaacs Ch.3 §3F Thm 3.36 (cyclic extension existence) 完成 — §3F 全 sorry-free 達成** 🎉 (AxiomsCheck flagship 入り): [`OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`](OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean) `cyclic_extension_exists` (~170 LOC). 構成: **Sym(Ω) realization は不採用 → `N ⋊_σ ℤ` を `K := ⟨(a⁻¹, m)⟩` で quotient** (mathlib SemidirectProduct API 活用度高). 5 sub-properties: (1) **h_inj** (inl_to_G 単射): (a⁻¹, m)^j の right component = ofAdd(j*m) を経由, m > 0 ⇒ j = 0. (2) **hN₀_norm**: range_inl = ker rightHom 正規, mk' surjective で transfer. (3) **zpowers ⟦g⟧ = ⊤** in G/N₀: preG lift y を inl·inr 分解, inl 成分は N₀ で消え, inr 成分は g^(right.toAdd). (4) **g^m = ι a**: (inr(ofAdd m))⁻¹ * inl a = (a, ofAdd(-m)) = cExt⁻¹ ∈ K (σ a = a ⇒ σ^k a = a ∀ k). (5) **Conjugation**: `SemidirectProduct.inl_aut: inl (φ g n) = inr g * inl n * inr g⁻¹` を活用, cyclicExtPhi σ (ofAdd 1) = σ. これで Phase 4 (Isaacs Thm 3.36) は完全完成. AxiomsCheck.lean に flagship 追加 (3 標準公理のみで unconditional).
- **2026-05-23** (同日) **SchurZassenhausConj (Isaacs Thm 3.12) ralph-loop で大幅 progress** (12 iter, 14 commit): [`OddOrder/Mathlib/SchurZassenhausConj.lean`](OddOrder/Mathlib/SchurZassenhausConj.lean). 完成 sorry-free (13 items): Helper A (Restriction `subgroupOf_of_le`) + Helper B (Quotient `map_mk'`) + solvability transfer 2 instances (subgroup + quotient via second iso) + Step 1 `step_restriction` (proper U で IH 呼び出し + lifting via map_subtype_conj_subgroupOf) + Step 2 `step_factor` (factor group reduction + mk'_comp_conj_eq + map_eq_map_iff) + `card_quotient_lt_of_ne_bot` + `exists_minimal_normal_le` (Set.Finite.exists_minimal) + **Isaacs Lem 3.11 自前** `minimal_normal_isCommutative_of_solvable` (~30 LOC, [L,L]=⊥/L 議論 + derivedSeries solvable contradiction) + step_caseA 全 structure (trivial N=⊥ + main flow + hK_g_compl + cardinality argument L=N) + step_caseB trivial N=⊤ + `main_aux` 強誘導 + 公開 `IsComplement'.exists_conj_of_coprime` (skeleton). 残 sorry (2 件, ~230 LOC, multi-session): (1) `abelian_sz_conjugacy` final transition (mathlib `Subgroup.exists_smul_eq` の QuotientDiff form → subgroup conjugation form, 直接 lemma 無し確認済), (2) `step_caseB` main body (Sylow C + minimal normal in quotient + N_G(L) argument).
- **2026-05-23** (同日) **BG §1 (Elementary Properties of Solvable Groups) 着手 — BG 形式化の最初のファイル**: [`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean) 新規 (~140 LOC). Section docstring に **BG §1 全 22 結果 + Isaacs FGT / mathlib 対応表** + §1A-§1G sub-section 構造. **§1F mathlib 直接対応 4 結果 (Thm 1.17 Focal / Thm 1.18 Burnside p-comp / Cor 1.19(b) Z-group / Thm 1.20 Maschke)** は CLAUDE.md no-mathlib-wrapper policy 準拠で section docstring のみ (Cor 1.19(b) → mathlib `IsZGroup.coprime_commutator_index` 直接ヒット, audit 発見). **§1G Lem 1.22** (p-group N ⊴ G, |N|=p^k ⇒ ∀ r ≤ k, ∃ L ⊴ G, L ≤ N, |L|=p^r) statement 確定, proof は次 commit で実装 (sorry; 方針: strong induction + Phase 1 `IsPGroup.normal_inf_center_nontrivial` + Cauchy + quotient correspondence). 残 §1A-§1E は Phase 1 + shared module (`MinimalNormal`, `InvariantSubgroup`, `ChiefSeries`, `FrattiniPGroup`) 待ち. S01_Solvable single-file build 1640/1640 OK.
- **2026-05-24** **BG §1 ralph-loop 夜間 iter 4-5**: (iter 4 `c64c4c7`) **Lem 1.1 (部分)** `isMinimalNormal_le_fitting_and_isElementaryAbelian` ⭐ sorry-free: 有限可解群の minimal normal M ⇒ M ≤ F(G) ∧ ∃ p, M.IsElementaryAbelian p. Ch.3 `solvable_minimal_normal_isElementaryAbelian` + x^p=1 から `IsPGroup p ↥M` 構築 (k=1) + `IsPGroup.isNilpotent` + Ch.1 `nilpotent_normal_le_fitting` の合成. BG 原 statement の "M ⊆ Z(F(G))" 部分は Ch.4 `le_centralizer_of_isMinimalNormal` 依存だが現状 Ch.4 parse error で import 不可, 完全形は将来. (iter 5 `1f1170f`) S01 docstring mapping table と実装 status 更新 (9→11 結果 sorry-free).

- **2026-05-24** **BG §1 ralph-loop 夜間 iter 1-2**: (i) iter 1 (`0227102`) `subgroupOf_sup_eq_of_pGroup_le_of_card_eq` 一般版 helper 抽出 (任意 `S ≤ T ⊔ M` で `|S| = |T|` ⇒ S.subgroupOf (T ⊔ M) は ↥(T ⊔ M) の Sylow p), 既存 `subgroupOf_sup_eq_of_pGroup_le_of_coprime` を 2 行 corollary に縮小 + Lem 1.14 main proof body の T_xSyl 構築 inline maximality argument (~18 LOC) を一般 helper 呼び出し (1 行) に置換 → 主証明 ~50 LOC 短縮; (ii) iter 2 (`0aa73e8`) **BG §1C Lem 1.7(a)** (`eq_top_of_sup_frattini_eq_top`): 有限群 G で `H ⊔ Φ(G) = ⊤` ⇒ `H = ⊤`, ⭐ sorry-free. mathlib `frattini_nongenerating` の `[Finite G]` 特殊化 (instance chain `Finite → WellFoundedGT → IsStronglyCoatomic → IsCoatomic`). CLAUDE.md no-wrapper 例外 (仮定特殊化). S01 ファイルに §1C section + §1A-§1B / §1D placeholder section markers 追加.

- **2026-05-24** **BG §1 Lem 1.14 hard direction ⭐ sorry-free 完成 — §1E 全 sorry-free 達成! 🎉** (`c3ff18a`): [`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean) `normalizer_sup_eq_normalizer_sup_of_pGroup_coprime` proof body (~115 LOC inline) 完成. **証明構造**: (0) Setup (h_disj + h_card_sup), (1) TSyl 構築 (前 commit の helpers から組立), (2) T_x := xTx⁻¹ = `T.map (MulAut.conj x).toMonoidHom` の p-group/cardinality/`≤ T ⊔ M` properties, (3) T_xSyl 構築 (Step 3 part 2 maximality argument を T_x 用に inline 再現), (4) `MulAction.exists_smul_eq (↥(T ⊔ M)) TSyl T_xSyl` で `∃ y, y • TSyl = T_xSyl`, (5) `Subgroup.conj_smul_subgroupOf` + `Subgroup.subgroupOf_inj` + `inf_of_le_left` で `MulAut.conj y.val • T = T_x` in G に翻訳, (6) `mem_sup_of_normal_left` (sup_comm 経由 M ⊔ T へ) で `y.val = m·t'` 分解, (7) `t' ∈ T ⇒ MulAut.conj t' • T = T` (手作り ext + group) で `MulAut.conj m • T = T_x`, (8) `m⁻¹·x ∈ N_G(T)` 両方向 (forward: hxtx_in_Tx + m·s·m⁻¹ = x·t·x⁻¹ calc; reverse: mul_left_cancel + mul_right_cancel), (9) `Subgroup.mul_mem_sup` + `sup_comm` で `x ∈ N_G(T) ⊔ M` 集約. **重要 mathlib API**: `Subgroup.conj_smul_subgroupOf` (`MulAut.conj h • P.subgroupOf K = (MulAut.conj h.val • P).subgroupOf K`), `Subgroup.subgroupOf_inj` (`S₁.subgroupOf K = S₂.subgroupOf K ↔ S₁ ⊓ K = S₂ ⊓ K`), `MulAction.exists_smul_eq` (= IsPretransitive). **Lessons learned**: (i) `MulAut.conj m • T` (pointwise smul, `open Pointwise` 必須) と `T.map (MulAut.conj m).toMonoidHom` (map form) は defeq だが `((MulDistribMulAction.toMonoidEnd ...) (MulAut.conj m))` まで elaborate されることがあり `rw` で pattern mismatch ⇒ `rw [← MulAut.conj_apply m s]; exact hms` の direction reversal で整合; (ii) `rwa [sup_comm] at h` は `h : x ∈ T ⊔ M` の `x` の型が `↥(T ⊔ M)` (subtype) なら motive type error ⇒ goal 側 `rw [sup_comm]; exact h` の pattern; (iii) `mul_left_cancel` / `mul_right_cancel` の引数指定 (`(a := x)` 等) は不要, 直接 chain 可 (`mul_left_cancel (mul_right_cancel hxs_eq)`). **§1E (Sylow lift + Hall-Higman + Lem 1.16 noncyclic auto) のうち Lem 1.14 + Prop 1.15(a) が完成. 残 Lem 1.16 (Prop 1.15(b) D. Goldschmidt + Lem 1.16 noncyclic auto) は Phase 1 待ち.

- **2026-05-24** (Lem 1.14 易 + Prop 1.15(a) 同日, 後続 commit) **BG §1 Lem 1.14 hard direction Step 1-3 helpers 段階完成** (`1a0fdef` / `9f24d6a` / `dc88434` の 3 commit + race-merged `2b5f7d1` の Step 3 part 1): [`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean) に 3 helper を逐次 sorry-free 追加.
    1. **Step 1** `inf_eq_bot_of_pGroup_coprime` (~18 LOC): `T` p-group + `(Nat.card M).Coprime p` ⇒ `T ⊓ M = ⊥`. `IsPGroup.of_injective` で T ⊓ M を p-group transfer → `|T ⊓ M| = p^k`. `Nat.eq_one_of_dvd_coprimes` で k = 0.
    2. **Step 2** `card_sup_eq_card_mul_card_of_disjoint_normal` (~30 LOC): `T ⊓ M = ⊥` + `M ⊴ G` ⇒ `|T ⊔ M| = |T|·|M|`. mathlib 第二同型 `QuotientGroup.quotientInfEquivProdNormalQuotient` + `subgroupOf_eq_bot` + `subgroupOfEquivOfLe` (M.subgroupOf (T ⊔ M) ≃ M) + `card_eq_card_quotient_mul_card_subgroup` chain.
    3. **Step 3 part 1** `subgroupOf_sup_card_eq_and_pGroup` (~10 LOC): `T.subgroupOf (T ⊔ M)` は ↥(T ⊔ M) で p-group + cardinality = |T|. `Subgroup.subgroupOfEquivOfLe (T ≤ T ⊔ M)` で T と同型.
    4. **Step 3 part 2** `subgroupOf_sup_eq_of_pGroup_le_of_coprime` (~35 LOC): `T.subgroupOf (T ⊔ M)` の **Sylow 性 (maximality)**. `Q : Subgroup ↥(T ⊔ M)` で `IsPGroup p Q` + `T.subgroupOf ≤ Q` ⇒ `Q = T.subgroupOf`. 証明: |Q| = p^j ∣ |T ⊔ M| = |T|·|M| = p^k · |M|, `(p^j, |M|) = 1` (`pow_left` で `Coprime` 持ち上げ) ⇒ `p^j ∣ p^k` ⇒ j ≤ k; `T.subgroupOf ≤ Q` で逆向き k ≤ j; `Nat.pow_le_pow_iff_right` + `Nat.pow_dvd_pow_iff_le_right` を `Fact.out : p.Prime` で適用; `Subgroup.eq_of_le_of_card_ge` (with `symm`) で等号.
  これで **T を ↥(T ⊔ M) の Sylow p object として `Sylow.mk` で構築可能** (isPGroup' + is_maximal' 両方の証明手段が揃った). 残: Step 4 (Sylow II via `Sylow.isPretransitive_of_finite` + `MulAction.exists_smul_eq` で `∃ y ∈ ↥(T ⊔ M), y • TSyl = (xTx⁻¹)Syl`), Step 5 (element decomposition `y.val = m·t'` + conjugation `yTy⁻¹ = mTm⁻¹` + 集約) — ~55 LOC 規模で次セッション.

- **2026-05-24** (Lem 1.22 同日, 後続 commit) **BG §1 Lem 1.14 (易方向) + Prop 1.15(a) sorry-free 完成 + Lem 1.14 main statement 確定**: [`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean) (commit `e8f6d1e` に巻き込み committed — ralph-loop concurrent run の `git commit -a` が staged 変更を取り込んだ race, 内容は健全). True placeholder 2 件 → 3 結果に展開:
    1. `normalizer_sup_eq_normalizer_sup_of_pGroup_coprime` (Lem 1.14 main): `N_G(T ⊔ M) = N_G(T) ⊔ M` (T p-group + M ⊴ G p'-group, `(Nat.card M).Coprime p` 仮定). proof は **sorry** (Sylow II in T·M + element decomposition + cardinality argument, ~100 LOC 規模 次 commit 予定). True から meaningful statement に格上げ.
    2. `le_normalizer_sup_of_normal` (Lem 1.14 易方向): `N_G(T) ⊔ M ≤ N_G(T ⊔ M)` ⭐ **sorry-free 5 行**. mathlib `Subgroup.normalizer_le_normalizer_sup_normal` (M.Normal で N(T) ≤ N(T ⊔ M)) + `Subgroup.le_normalizer.trans le_sup_right` (M ≤ T ⊔ M ≤ N(T ⊔ M)) の `sup_le`. proof body 5 行で完結.
    3. `hall_higman_solvable_specialization` (Prop 1.15(a)): `G` finite solvable + `O_{p'}(G) = ⊥` ⇒ `C_G(O_p(G)) ⊆ O_p(G)` ⭐ **sorry-free thin wrap**. Phase 1 `OddOrder.Isaacs.Ch03.hall_higman_1_2_3` の π = {p} 特殊化, `IsPiSeparable {p} G` を `isPiSeparable_of_solvable {p}` で `[IsSolvable G]` instance から取得して直接適用. CLAUDE.md no-wrapper 例外 (仮定特殊化: `IsSolvable G` instance + π = {p}, `IsPiSeparable` 仮定を取り除く). BG 原 statement (T Sylow p of O_{p',p}(G) ⇒ C_G(T) ⊆ O_{p',p}(G)) との関係: G を G/O_{p'}(G) に置き換えると T は O_p(G/O_{p'}(G)) に一致するため, 本 statement が「quotient で reduced された BG 1.15(a)」に該当. 完全 statement への昇格は Lem 1.14 hard direction 完成と並行.
  S01_Solvable single-file build OK (sorry 1 個: Lem 1.14 main only). 全体 build は ralph-loop 並走で一時 Ch04 broken だが S01 自体は健全.
- **2026-05-24** (同日) **Isaacs Ch.4 ForwardFromCh03 着手 — Glauberman 3.24(a) 完成** ⭐: [`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean`](OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean) (~340 LOC). 基盤 (`IsCompatibleMulAction` + `SemidirectProduct.lift` 経由の SDP 作用構築 + `inl/inr_smul` 簡略補題) + Glauberman 3.24(a) `glauberman_fixed_point_exists` 完成. 7 ステップ: (1) U ⊔ inlG = ⊤ via G transitive. (2) inlG.relIndex U = |A| via second iso (`relIndex_sup_right` + `relIndex_top_right`). (3) SZ existence in U (`exists_right_complement'_of_coprime`). (4) H := H_in_U.map U.subtype は inlG の Γ 内 complement (`isComplement'_iff_card_mul_and_disjoint`). (5) inrA も complement (Ch.3 `inl_range_isComplement_inr_range`). (6) SZ conjugacy (`exists_conj_of_coprime`) で `inrA.map (conj n) = H` を導く. (7) g⁻¹ • α₀ が A-fixed (algebraic 計算: inr(a) * y = y * h with h ∈ H ⊆ U). Tier 1 の **中核** が確立. 残 Tier 1: 3.24(b), 3.23(a/b), 3.25, 3.27, 3.28, 3.29, 3.30.

- **2026-05-24** **BG §1 Lemma 1.22 ⭐ sorry-free 完成 — BG 形式化の最初の theorem**: [`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`](OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean) `normal_subgroup_card_pow_le_of_pGroup` (~70 LOC + 18 LOC helper). 主張: `IsPGroup p G` finite + `N ⊴ G` + `p^r ∣ |N|` ⇒ `∃ L ⊴ G, L ≤ N, |L| = p^r`. 証明: r 帰納法. Base r=0: L=⊥. Step r→r+1: IH で L₀ 取得, 商群 G/L₀ で作業 — `IsPGroup.to_quotient` で p-群 transfer + helper `card_comap_eq_card_mul_card_ker` (本 commit 新規 sorry-free, `index_comap_of_surjective` + `quotientKerEquivOfSurjective` + `card_eq_card_quotient_mul_card_subgroup` chain) で `|N'| = |N|/|L₀|` 計算, `Nat.dvd_of_mul_dvd_mul_right` で `p ∣ |N'|`, `Finite.one_lt_card_iff_nontrivial` で `N'` 非自明, **Phase 1 `OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial`** で `N' ⊓ Z(G⧸L₀)` 非自明, **Cauchy** (`exists_prime_orderOf_dvd_card`) で order p の x, `Subgroup.zpowers x = K` で `Nat.card_zpowers + Subgroup.orderOf_coe` で `|K|=p`, `x ∈ Z` ⇒ `Commute g x.zpow_right` で K.Normal in G⧸L₀, `L = K.comap (mk' L₀)` で `K.Normal.comap` + helper で `|L| = p · p^r = p^(r+1)`. **mathlib gotchas**: `K.index_comap_of_surjective hf` dot notation 必須; `Nat.card_zpowers` root namespace; `Subgroup.orderOf_coe ⟨xc, hxc_mem⟩` 引数明示要; `Commute` は defeq `a*b=b*a`. **Lem 1.14 (quotient Sylow lift) + Prop 1.15(a) (Hall-Higman thin wrap)** は placeholder (True + 詳細 docstring 内 proof 方針) — 次 commit で本格実装. Build 1651/1651 OK.
- **2026-05-23** (同日) **Peterfalvi Phase 2b 第 1 波 §3-§8 (character theory core) 4 視点 audit 完了**: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md) — §3 Preliminary / §4 Dade / §5 TI Cyclic / §6 Dade Certain / §7 Coherence / §8 Coherence Thm を 4 視点 (forward / internal hub-spoke / mathlib proof-internal / preceding [BG]/[Is]/[H]/[HB] cites) で 6 並列 sub-agent + synthesis. 統合観点 6 件: (i) **5/6 節で結果数 systematic 誤認** (§3 のみ正確): §4 (6→**11**), §5 (5→**9**), §6 (5→**10**), §7 (6→**9**), §8 (4→**8**); overview `^**(N.M)**` grep が top-bolded label のみ拾い (2.7)-(2.11), (3.6)-(3.9), (4.6)-(4.10), (5.7)-(5.9), (6.5)-(6.8) 漏らす; 欠落結果は実は下流最多 cite hub ((3.8) NC = 8 cites, (5.5) = 11, (5.7) = 10, (6.8) Sibley = §9/§12/§14 dispatch); (ii) **mathlib character theory は遥かに薄い** (既存 note "mid/30%" 等は誤り): `ClassFunction G` 型不在, classical induced character formula 不在 (only categorical `IndV` coinvariants), `ZIrr` 不在, Brauer permutation lemma ([Is] Thm 6.32) 不在, character-level Frobenius reciprocity (numerical) 不在, `IsTISubset` 不在 (`MulAction.IsBlock` ≠ TI), inertia subgroup 不在, Clifford theorem 不在; (iii) **§8 で重大な fabrication 2 件**: "Sibley 1984 Contemp. Math. 47" → 捏造 (実は **Sibley 1976 *Illinois J. Math.* 20**; (6.4)-(6.5) は [FT] §11 で Sibley 無関係, (6.8) のみ Sibley), "Reynolds 1965 Duke Math. J." → **完全捏造** (Reynolds は Peterfalvi 参考文献に存在せず); (iv) **Coherence (5.1) 定義に rider 混入** (§7): "τ̃(χ - 1) virtual character difference" は (5.1) に含まれない (実は (5.9.b) 結論), L62 `χ - 1` → `χ - χ̄`; (v) **`OddOrder/RepresentationTheory/` 新規 shared modules 11 件** (~1100 LOC) が真の Phase 2b 前提: `ClassFunction`, `InducedCharacter`, `ZIrr`, `SecondOrthogonality`, `IsReal`, `Clifford` (**BG §2 共有**), `Inertia`, `SchurCenterBound`, `BrauerPermutation`, `IsometryDifferencePair`, + `OddOrder/GroupTheory/TISubset.lean`. (6.7) 専用 `ClassSumAlgebraHom` + `AlgInt.cong` 別途; (vi) **§3-§8 [BG] 依存ゼロ** (全節 proof body + prose 双方; 既存 "[BG] §1 軽" / "[BG] §3 dep" 等 overstated or false). §3-§8 character theory core は **BG 完全独立で並行着手可**, BG 依存は §9 (= App.C) 以降に集中. per-section LOC 見積 revision: 既存暗黙 ~2000 → 実 **~4600 LOC** (含 Wave 1a infra). 既存 per-section ノート 6 件 + `_overview.md` に audit log section + inline 訂正タグ追加.
- **2026-05-23** (同日) **Isaacs Ch.8-10 dependency 再 audit 完了**: [`notes/meta/ch08_10_audit_2026_05_23.md`](notes/meta/ch08_10_audit_2026_05_23.md) — 3 章 (Permutation Groups / More on Subnormality / More Transfer Theory) を 4 視点 (forward dep / 章内依存 / mathlib status 含む証明内 API / 先行章依存) で並列再調査. 主結果: (i) **Ch.10 §10A wreath product コスト評価訂正**: mathlib `Mathlib/GroupTheory/RegularWreathProduct.lean` (260 行, 2025) 既存, `Sylow.mulEquivIteratedWreathProduct` (`:242`) が 10.4 認識の直接道具 ⇒ Yoshida 10.1 setup コスト「大 → 中」, ad-hoc Cp ≀ Cp 手作り不要 (Suzuki/Sz(q) Phase 2b にも恩恵), (ii) **3 章とも BG/Peterfalvi 直接被引用 0 件 validated**: Bender/Wielandt aut tower/Schenkman/Bartels/Bochert/Jordan/Iwasawa/Yoshida/Mackey/Furtwängler/Alperin-Kuo すべて 0 件, 表層 hits (`Wielandt` 12 / `component` 25 / `metacyclic` 12) は全 false positive ⇒ **3 章とも Phase 1 skip 推奨を維持** (§1G Chermak-Delgado と同列), (iii) **先行章依存さらに軽量**: Ch.8 は Thm 1.4 のみ (mmd 全 819 行で Ch.1-7 cite 1 件), **Ch.9 は Ch.1+Ch.2 のみで Ch.3 Hall-Higman は prose のみ・proof body cite なし**, Ch.10 は Ch.4 (4.6 ✅, 4.7/4.8 未) + Ch.5 (5.5/5.12/5.22 ✅, 5.6 mathlib 直接) + Ch.6 Thm 6.11 (§10B gating), (iv) **章内依存補正 1 件**: Bochert 8.26 の依存は 8.19 + 8.25 のみ (既存ノートが 8.24 を併記していたが proof L4467-L4513 で引かない; 8.24 は 8.23 の道具), (v) **shared module 配置提案 10-11 ファイル**: Quasisimple/Component/Layer/FittingStar/Socle/NilpotentResidual (Ch.9) + Metacyclic/AugmentationIdeal/MaschkeGroupAction/TransferMackey (Ch.10) + Orbital + A_n general simple (Ch.8), いずれも `OddOrder/GroupTheory/` 配下が clean, (vi) **mathlib upstream 価値 ranking**: `AugmentationIdeal` (Δ(G), Thm 10.20 G^{ab} ≅ Δ/Δ²) が最高価値 (class field theory + group cohomology 両方からの需要), 次点 Yoshida 10.1, Quasisimple/Layer, mathlib TODO A_n simple (`Alternating.lean:56`), (vii) **IwasawaStructure 仮定注意**: `IsQuasiPreprimitive` 要求 (primitive のみではない) ⇒ wrapper `IsPreprimitive.isQuasipreprimitive` 必要, (viii) **Lem 9.31 mathlib 状況確定**: 不在 (`Sylow.exists_comap_eq` は別ステートメント), ~10 行 induction で新規. 既存 ch08/ch09/ch10 ノート 5 件の audit 訂正タグ + ROADMAP entry 追加.
- **2026-05-25** **Isaacs Ch.7 Lem 7.3 GL(2,p) 補題 sorry-free 完成**: [`OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean`](OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean) `gl2_pSubgroup_centralizes_of_normalizes`. `|L|`-strong induction (`lem73_aux`) で P-invariant Sylow q-subgroupを Ch.4 `exists_aInvariant_sylow` から取得し, proper commutator branch は Ch.4 action-commutator/coprime actionで閉じる. `[L,P]=L` branch は det 経由で `L ≤ SL(2,p)`, `q=2` は Lem 7.4 の unique involution + finite abelian 2-group cyclicity (`isCyclic_of_comm_two_group_unique_order_two`) + `Aut(cyclic 2-group)` 2-group性で P 作用 trivial, `q` odd は `|SL(2,p)| = p(p-1)(p+1)` と orbit lower boundで矛盾. Build: `lake build OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main` OK; Ch07 の proof-level `sorry` warning は消滅. 次 frontier は **Thm 7.5 normal-P theorem** (Aut(E)≅GL(2,p) bridge + Hall-Higman 3.21 + Ch.6 6.11).
- **2026-05-24** **Isaacs Ch.7 着手 — Phase 1 山場のクリティカル経路頂点に進出**: 先行章 (Ch.3 §3D 一部除き未完, Ch.4 §4D 未, Ch.5 §5E 未, Ch.6 全般) が未完成だが Ch.7 内で先行不要な 3 候補 (Thm 7.2 / Lem 7.4 / Lem 7.7) を **全て完成**: (i) [`OddOrder/GroupTheory/ThompsonSubgroup.lean`](OddOrder/GroupTheory/ThompsonSubgroup.lean) 新規 shared module (~150 LOC). `Subgroup.maxElemAbelianIn P p` (Isaacs L3727 `E(P)`) + `Subgroup.thompsonJ P p = ⨆ E ∈ E(P), E` (Thompson subgroup J(P), Isaacs/Aschbacher max-order 版) def + **Thm 7.2** `thompsonJ_eq_of_le_of_le` (J(P) ≤ Q ≤ P ⇒ J(Q) = J(P)) sorry-free 完成. auxiliary: `bot_isElementaryAbelian`, `instFiniteSubgroupOfFinite` (mathlib v4.29.1 不在の `[Finite G] ⇒ Finite (Subgroup G)`), `maxElemAbelianIn_nonempty` (`Set.exists_max_image` 経由). BG §6/§8/§9 (Uniqueness) + App.A (Thm A.4(b)) + App.B (Puig L(S)) 共用視野. (ii) [`OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean`](OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean) 新規 (~210 LOC). 章 entry doc + 4 section (§7A-§7D) skeleton + 全 8 結果の TODO docstring + Thm 7.2 Ch.7 namespace re-export + **Lem 7.4 SL(2,F) 唯一 involution = -I sorry-free 完成** ⭐ (~100 LOC inline §7A). `F` field + `(2 : F) ≠ 0` ⇒ `t ∈ SL(2,F), t² = 1, t ≠ 1 ⇒ t = -1`. proof: `M := t.val`, `M*M = I`, `det M = 1` から 4 entries `a, b, c, d` の方程式 (`Matrix.det_fin_two` + `Matrix.mul_apply` + `Fin.sum_univ_two`); `M²` の (0,1)/(1,0) で `b(a+d) = c(a+d) = 0`; `a + d = 0` 仮定 ⇒ `det + (0,0)entry` 和で `2 = 0` 矛盾, よって `b = c = 0`; `a·d = 1, a² = 1 ⇒ a = ±1`, `t ≠ 1` から `a = -1`. `linear_combination` 中心 + `!![±1, 0; 0, ±1]` 中間形 + `Subtype.ext.trans` で完成. `Fact (Even (Fintype.card (Fin 2)))` private instance 補強 (`Neg (SL(2,F))` のため). Isaacs 原本 "`q` odd" を `char F ≠ 2` で一般化. **下流**: Lem 7.3 GL(2,p) 補題 + Thm 7.5 normal-P theorem で利用予定. (iii) **Lem 7.7 (b)** `centralizer_map_of_coprime_kernel` sorry-free (~115 LOC §7C inline): `N ⊴ G` で `p ∤ |N|`, `P` 非自明 `p`-部分群 ⇒ `C_Ḡ(P̄) = (C_G(P)).map (mk' N)`. 書籍 p.215-216 の "Lem 2.17 short extension" proof: Lem 2.17 (a) (Ch.2 既完) + correspondence theorem (`X := N_G(P) ⊓ Cbar.comap f`, `X.map f = Cbar`) + `Subgroup.map_commutator` + `commutator_eq_bot_iff_le_centralizer`. `⁅X, P⁆ ≤ N` (commutator が ker f に落ちる) + `⁅X, P⁆ ≤ P` (X ≤ N_G(P)) で `⁅X, P⁆ ≤ P ⊓ N = ⊥` (coprime), 即ち `X ≤ C_G(P)`. Helper `centralizer_le_normalizer` (private, mathlib v4.29.1 直接 lemma 無し) も同時追加 (`mem_normalizer_iff` 両方向 + `mul_right_cancel`). **下流**: Thm 7.1 Thompson normal p-complement の三本柱 (Ch.5 §5E 5.26 + Thm 7.6 + Lem 7.7) の 1 つ. (iv) 残 Ch.7 4 結果 (7.1/7.5/7.6/7.8) は def 系前提 (`HasNormalPComplement`, `Aut(E) ≅ GL(n,p)` 橋渡し) または先行章完成待ち, docstring TODO で skeleton 保持.
- **2026-05-24** **BG §2 (Representations) skeleton 完成**: [`OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`](OddOrder/BG/Ch1_Preliminary/S02_Representations.lean) 新規 (~330 行 docstring 中心). 6 sub-section (§2A Prop 2.1 / §2B Prop 2.2 / §2C Lem 2.3 / §2D Prop 2.4 / §2E Thm 2.5 / §2F Thm 2.6) に BG 本文 statement (mmd L598-793) + 形式化方針 + mathlib カバレッジ + 下流引用 (audit 実測) + Lean signature 案 を整理. **statement stub 全 6 結果未配置** — 依存 shared module (`RepresentationTheory/AbsolutelyIrreducible`, `EnvelopingAlgebra`, `Clifford`, `EigenspaceUnderCyclicAction`, `AutElementaryAbelian`, `PGroupFixedVector`) 未作成 + Prop 2.2 は **Isaacs Ch.6 §6F Clifford 未完成 blocker**. Audit 訂正反映 ([`bg_phase2a_wave1_audit_2026_05_23.md`](notes/meta/bg_phase2a_wave1_audit_2026_05_23.md)): 旧ノート "§9 1-2 cite, skip 推奨" → 実測 **8+ cites** (§3 ×5, §4 Lem 4.17, §15 Thm 15.7, **App.A Thm A.1 proof L4464**), **Phase 2a 第 1 波必須**. 着手順: Thm 2.6 → Prop 2.4 → Prop 2.1 → Thm 2.5 → Prop 2.2 (Ch.6 待ち); Lem 2.3 (forward use 0) defer.
- **2026-05-24** (同日, 後続 commit) **BG §2 skeleton: Gorenstein G 引用 mapping rule 徹底訂正** (commit `bbb7701`): 初回 skeleton で 7 個の G 引用 (Clifford G 3.4.1, Schur G 3.5.2, Jacobson G 3.6.2, 既約⟺Hom=F G 3.5.7, Lem 2.6.3 fixed vec, extraspecial repr G 5.5.4-5, Wedderburn) を素通ししていた CLAUDE.md L20 違反を訂正. 冒頭 mapping section + 6 箇所 inline 注記 + [`phase2_cross_refs.md`](notes/meta/phase2_cross_refs.md) §5 連動訂正. **重要確認**: Isaacs FGT (群論本) mmd で `Clifford` `Jacobson` 0 hit, representation/character theory 章なし (10 章一覧は Sylow / Subnormality / Split Extensions / Commutators / Transfer / Frobenius Actions / Thompson / Permutation / More Subnormality / More Transfer) ⇒ BG §2 の G 引用は全部 Isaacs FGT 対応なし ⇒ mathlib + 新規 `OddOrder/GroupTheory/RepresentationTheory/*` shared module で再構築方針を明示. feedback memory `feedback-bg-g-isaacs-mathlib-mapping` に永続化 (BG/Peterfalvi 各節 skeleton 冒頭に mapping section 必須ルール).
- **2026-05-24** (同日, 後続 commit) **§2F Thm 2.6 着手 — `PGroupFixedVector` shared module skeleton + Thm 2.6 (a)(b) Lean stub 配置**: (i) [`OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean`](OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean) 新規 (~95 行). mathlib `IsPGroup` namespace を直接拡張 (既存 `ChermakDelgado.lean` / `ElementaryAbelian.lean` の `Subgroup` 拡張流儀踏襲). 主 statement: `IsPGroup.invariants_ne_bot` (`Representation F G V` で `IsPGroup p G` + `[CharP F p]` + `V ≠ ⊥` ⇒ `ρ.invariants ≠ ⊥`) + corollary `IsPGroup.exists_fixed_vector_ne_zero` (corollary は sorry-free, 主 stmt が sorry). Proof strategy docstring: |G| 帰納 + p-群 center 非自明 (`IsPGroup.center_nontrivial`) + `(ρ z - 1)^{p^k} = 0` (Frobenius binomial / `add_pow_char`) ⇒ z-fixed subspace `W ≠ ⊥`, `W` は G-invariant (z ∈ Z(G)), `G/⟨z⟩` p-群で |G/⟨z⟩| < |G|, 帰納で fixed vector. (ii) [`OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`](OddOrder/BG/Ch1_Preliminary/S02_Representations.lean) `import` 追加 + §2F に **Thm 2.6 (a) `odd_two_dim_abelian`** + **(b) `odd_two_dim_sylow_abelian`** sorry stub 配置 (BG §1 流儀: 一部 stub + 他 sub-section docstring のみ). 残: (i) `invariants_ne_bot` proof, (ii) Thm 2.6 帰納本体 + GL(2,F) + MISSING_PAGE:29 補完, (iii) `CharP F p` 型整合 微調整.
- **2026-05-24** (同日, 後続 commit) **Peterfalvi 着手 — Phase 2b 最初の Lean ファイル 3 件配置** ⭐: (i) [`OddOrder/GroupTheory/TISubset.lean`](OddOrder/GroupTheory/TISubset.lean) 新規 (~120 LOC) — Wave 1a 共有 infra 最初の 1 件. `OddOrder.GroupTheory.IsTISubset A L : Prop` 定義 (`∀ g, (∃ a ∈ A, g·a·g⁻¹ ∈ A) → g ∈ L`) + 基本 API 4 件 (`disjoint_conj_of_not_mem`, `of_disjoint_conj`, `mono`, `subset`) + `Subgroup.IsTI H` convenience def (`A = H \ {1}`, `L = N_G(H)` 特殊化). audit 訂正 (mathlib v4.29.1 `MulAction.IsBlock.IsTrivialBlock` は **別概念**) 反映. Peterfalvi §4 (2.3), §5 (3.1), §6 (4.3.a), §8 (6.7), (6.8) 全節 + §11-§16 で多用予定. `Subgroup.normalizer` が `Set G → Subgroup G` 型 (mathlib v4.29.1) のため `(H : Set G)` 経由で呼び出し. Build OK (~2s). (ii) [`OddOrder/Peterfalvi/S01_Introduction.lean`](OddOrder/Peterfalvi/S01_Introduction.lean) 新規 (~110 行 docstring 中心). `OddOrder/Peterfalvi/` ディレクトリ開設. FT 戦略宣言 + 二部構成 (BG/Peterfalvi) + 前提知識 [Is] (Isaacs *Character Theory* 1976; 本プロジェクト Isaacs FGT 2008 とは **別書** 注意) Ch.1-7 + 他参照文献 ([HB]/[H]/[FT]/[Si1] 1976 (audit 訂正で Sibley 1984 → 1976)/[Su]/[L]). 0 結果. (iii) [`OddOrder/Peterfalvi/S02_Notation.lean`](OddOrder/Peterfalvi/S02_Notation.lean) 新規 (~140 行 docstring 中心). 記号対応表 (Peterfalvi ↔ mathlib v4.29.1 ↔ Wave 1a) — `Irr(G)`, `CF(G)`, `CF(G, A)`, `(α, β)_G`, `‖α‖²`, `Z[Irr G]`, `Ind/Res`, `I_G(θ)`, Frobenius, Fitting, TI-subset, Dade, Coherence の各記号. ⚠️ audit 訂正反映: `ClassFunction G` 型 / classical induced character formula / `ZIrr` / Brauer permutation / character-level Frobenius reciprocity 等 mathlib **完全不在**, Wave 1a 11 modules ~1100 LOC が真の前提. notation alias は Wave 1a 完成後に再着手予定 (現状最小). 0 結果. **意義**: Phase 2b の Lean 実装が始動. 並列 agent の BG §2 Wave 1a (`PGroupFixedVector.lean`) と相互独立に進行可.
- **2026-05-24** **Peterfalvi per-section ノート 6 件 + _overview に Phase 2b 第 1 波 audit 訂正タグ inline 反映**: [`notes/peterfalvi/s03_preliminary_character.md`](notes/peterfalvi/s03_preliminary_character.md), [`s04_dade_isometry.md`](notes/peterfalvi/s04_dade_isometry.md), [`s05_ti_cyclic_normalizer.md`](notes/peterfalvi/s05_ti_cyclic_normalizer.md), [`s06_dade_certain_subgroup.md`](notes/peterfalvi/s06_dade_certain_subgroup.md), [`s07_coherence.md`](notes/peterfalvi/s07_coherence.md), [`s08_coherence_theorems.md`](notes/peterfalvi/s08_coherence_theorems.md), [`_overview.md`](notes/peterfalvi/_overview.md) (+121 -102 行). 2026-05-23 audit ([`peterfalvi_phase2b_wave1_audit_2026_05_23.md`](notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md)) 結果を per-section 本文の table / TL;DR / scope に ⚠️ マーク付きで反映 — 旧 audit log section (file 冒頭) だけでは body の table/prose が古いまま残っていたのを補正. 訂正の中身: (i) スコープ訂正 §4 6→11, §5 5→9, §6 5→10, §7 6→9, §8 4→8 を各 file L1-3 + 表 header + 表 row に展開 ((2.7)-(2.11), (3.6)-(3.9), (4.6)-(4.10), (5.7)-(5.9), (6.5)-(6.8) 行追加 + 下流 cite 数記入); (ii) §7 Coherence (5.1) 定義 rider 削除 (「τ̃(χ-1) virtual character 差で書ける」は (5.1) ではなく (5.9.b) 結論; 旧 TL;DR + コード snippet 2 箇所訂正); §7 全体扱う差 `χ - 1` → `χ - χ̄` (複素共役) 訂正; (iii) §8 fabrication 訂正 — 「Sibley 1984 Contemp. Math. 47」を [Si1] Sibley 1976 *Illinois J. Math.* 20:434-442 に置換、(6.3)/(6.5) は [FT] §11 由来で Sibley 無関係 + (6.8) のみ Sibley 寄与 と明示、「Reynolds 1965 Duke Math. J.」関連 section + TODO 全削除 ((6.7) は無名 internal lemma); (iv) §6 (4.2.a) "K の Hall" → "L の Hall" 修正 (mmd L9 verbatim); (v) mathlib カバレッジ overstate 全削除 — §3-§8 全節 (c) bucket dominant, Wave 1a 11 modules ~1100 LOC が真の前提を明示; (vi) Phase 1 dep overstate 全削除 — §4-§5 で Ch.6 (Frobenius) 不要 + §6 (4.5.b) Brauer permutation は mathlib 不在で新規 `BrauerPermutation.lean` 要; (vii) [BG] dep 0 を per-section + _overview 表で明示 — §3-§8 character theory core は **BG 完全独立で並行着手可** (= **Isaacs 未完でも Peterfalvi 第 1 波着手可能**); (viii) _overview 本体合計 113 → 134 程度に再集計 (per-section 漏れ加算); LOC 推定全節更新 (§3 400→1000-1200, §5 400→700-850, §8 30 days → 35-45 days 等). ROADMAP Phase 2b 着手前必読リスト更新済 (audit doc + per-section corrections 完了).
- **2026-05-24** (同日, 後続 commit) **BG §2F PGroupFixedVector iter 2 — Frobenius/nilpotent/ker helper 3 件 sorry-free + step case 中段 sorry-free 化**: [`OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean`](OddOrder/GroupTheory/RepresentationTheory/PGroupFixedVector.lean) (~95 → ~190 行). 新 helper (全 sorry-free): (i) `charP_End_of_field` — `[Nontrivial V]` 下で `CharP (Module.End F V) p` instance を `charP_of_injective_algebraMap` 経由導出 (algebraMap injectivity を `Algebra.algebraMap_eq_smul_one` + `Module.End.one_apply` + `smul_left_injective F (v ≠ 0)` で示す). (ii) `exists_pow_sub_one_eq_zero` — p-群 + [CharP F p] + [Nontrivial V] で `∃ k, ((ρ g) - 1)^(p^k) = 0`. `sub_pow_char_pow_of_commute` ([`Mathlib/Algebra/CharP/Lemmas.lean:226`]) + `Commute.one_right` 経由 (`Module.End F V` 非可換のため `_of_commute` 版が必須). (iii) `ker_ne_bot_of_pow_eq_zero` — `f^N = 0` + [Nontrivial V] ⇒ `LinearMap.ker f ≠ ⊥`. proof: `ker = ⊥ ⇒ Function.Injective (⇑(f^N))` を `Module.End.mul_apply` ベース induction で示し, `f^N v = 0` + `v ≠ 0` で矛盾. (iv) main `invariants_ne_bot` step case で `Nontrivial V` instance (from `hV` via `Submodule.exists_mem_ne_zero_of_ne_bot`) → `exists_ne (1 : Subgroup.center G)` で非自明 z 取得 → helper 3 件適用で `ker ((ρ z) - 1) ≠ ⊥` **まで sorry-free**. 残 sorry: (a) ker は G-invariant (z ∈ Z(G) で全 g と可換), (b) `G/⟨z⟩` on ker の representation 構築 + |G/⟨z⟩| < |G| + 帰納仮定適用. Build OK (2272 jobs).
- **2026-05-24** (同日) **Isaacs Ch.4 ForwardFromCh03 §3E Tier 1 全 9 件 sorry-free 完成 — Cor 3.25 で fin** ⭐⭐⭐ (commit 917f573, ff3fdc1): [`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean`](OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean) `aInvariant_pSubgroup_le_aInvariant_sylow` (~110 LOC). A-不変 p-部分群 P ⊆ G で A,G coprime + (A or G) solvable ⇒ ∃ S Sylow A-不変 で P ≤ S. **証明 6 step**: (1) 極大 A-不変 p-部分群 Q ⊇ P を `Finite.exists_le_maximal` で取得. (2) N := N_G(Q) は A-不変 (`IsAInvariant.normalizer`); 制限作用 (`hN_inv.restrict : A →* MulAut ↥N`) に **Thm 3.23(a)** (`exists_aInvariant_sylow`) を適用し A-不変 Sylow R_in_N : Sylow p ↥N を得る. (3) R := R_in_N.map N.subtype は A-不変 p-部分群 of G (R_in_N の A-不変性は `isAInvariant_iff_smul_mem` + `hN_inv.restrict.smul_mem` で element-wise lift). (4) R ≤ N(Q) なので `IsPGroup.to_sup_of_normal_left'` で Q ⊔ R は p-群. 極大性で Q ⊔ R = Q ⇒ R ≤ Q. (5) Sylow 極大性 `R_in_N.3` で Q.subgroupOf N = R_in_N, `Subgroup.map_subgroupOf_eq_of_le` で Q = R. つまり Q は N 内 Sylow. (6) **Normalizer-grow argument**: 任意 p-部分群 T ⊇ Q で T = Q を示すため `by_contra` + `IsPGroup.isNilpotent` + `normalizerCondition_of_isNilpotent`. `Q.subgroupOf T < ⊤` ⇒ `Q.subgroupOf T < normalizer = N.subgroupOf T` (`Subgroup.subgroupOf_normalizer_eq` 経由), 翻訳して Q < N ⊓ T. N ⊓ T は N 内 p-部分群 ⊇ Q で `R_in_N.3` 極大性に矛盾. Sylow structural constructor で Q を Sylow オブジェクト化. **§3E Tier 1 全 9 件** (3.24a/b + 3.23a/b + 3.25 + 3.27 + 3.28 + 3.29 + 3.30) **全 unconditional flagship 化完了**. これで Hall-Higman + Glauberman 系統で要求される A-不変 Sylow 構造論が完備, **Ch.4 §4C-§4D 本格着手の最終 prerequisite 解消**. Tier 2 (Thm 3.31-3.34 軌道理論 / Three-Subgroup Lemma) は本来 Ch.4 §4C-§4D 依存のため別 phase. AxiomsCheck.lean に flagship 追加 (3 標準公理のみ).

- **2026-05-27** **状態同期 + mathlib rc2 bump + BG S02 修復**: (i) **mathlib `v4.29.1` → `v4.30.0-rc2`** bump (full build green; パターンは [`notes/meta/mathlib_rc2_migration.md`](notes/meta/mathlib_rc2_migration.md))。(ii) **トランクが実質 sorry-free + axiom-free に到達** (05-25→05-27 の進捗をここで集約記録): **Isaacs Ch.1–7 全章 sorry-free** (168 flagship が AxiomsCheck で axiom-clean — Thm 7.6 `normal_J` / 7.8 Burnside p^a q^b 含む)、**BG §1–§3 sorry-free 完成**、**Peterfalvi §1–§6 着手** (残 sorry は `RepresentationTheory/IsometryDifferencePair` の Dade isometry 1 件のみ)。`OddOrder/` に `axiom` 宣言 0。(iii) **BG S02 Representations の rc2 移行漏れを修復 + OddOrder 配線** (commit `8f06ca2`): S02 は root が import せず "full build green" 網から漏れていた。4 error は全て documented rc2 pattern (`⟨CommMagma.to_isCommutative⟩` over-wrap → `inferInstance` + `open scoped IsMulCommutative in`; `normalizer` Set 引数化 → `normal_subgroupOf_of_le_normalizer` + 明示 `map_subgroupOf_eq_of_le`)。§2 (Thm 2.5/2.6) がビルド入りし §3/§4/App.A の前提充足。(iv) **notes/memory を現状同期**: memory 3 件 (sorry/axiom discipline, setup state, MEMORY.md 索引) + CLAUDE.md toolchain + 本 ROADMAP phase 表 + `notes/bg/_overview.md` + `notes/meta/{phase2_cross_refs,mathlib_coverage}.md`。**⚠️ grep の罠**: `grep -c '\bsorry\b'` は "sorry-**free**" prose を拾い大幅過大計上 (旧 memory が S01 を「37 sorry」と誤記; 実際 0)。正確な計数は `lake build` warning か `:= sorry`/`by sorry`/行頭単独にマッチする regex で。per-section ノート (BG s01-s16, Peterfalvi s03-s16) の inline status は未個別更新 (canonical な現状は本 entry + `_overview` + memory)。

- **2026-05-28** **BG §6 → App.A+B(Puig)で Gorenstein 依存を捨てる経路を確定 (設計決定)**: [`notes/meta/bg_s6_appAB_route_2026_05_28.md`](notes/meta/bg_s6_appAB_route_2026_05_28.md)。3 冊精読で判明: **Thm 6.1=Hall-Higman(G 6.5.2)、6.2=Glauberman Z(J)(G 6.5.1+8.2.11)はBG本文が証明を書かず**、かつ **Isaacs FGT は Z(J)-定理を明示的に省く**(p.217)⇒「G→Isaacs 読み替え」方針が 6.2 で破綻。解決 = **BG App.A+B(Puig L(S))の自己完結ルート**(B.4 は Isaacs 本人の未公刊証明、L4691「serves as a substitute for Theorem 6.2」)。依存閉包精査: **App.B(B.1-B.4)は完全な証明が BG にあり実質依存は A.5 のみ**、A.1/A.5 も完備、**真のゲートは A.4(b)(=Thm 6.1, §7/§8 が独立引用)+ A.4(c)(A.5/B.4 用)の 2 つ**(ともに Gorenstein §6.5 special case で BG 未記述)。**最深部 SL(2,p)(Dickson 2.8.4/G 3.8.1)は repo 既証** `Isaacs.Ch07.gl2_pSubgroup_centralizes_of_normalizes`(Lem 7.3)⇒ A.4(b)/(c) は 7.3 を核とする bounded reduction(A.4(c) は Isaacs 7.5 の系ではなく兄弟定理、共通核が 7.3)、A.2/A.3/A.4(a) は迂回可。**J→L(S) 大域置換は §8/§9 精査で健全性確認**(M は J 非定義=導出的「N_G(Z(J(P)))=M」、§8/§9 が使う J 性質 Z(J)⊴M/char/≠1/J(P)=J(Q) は App.B の B.4/B.1/B.1(f)/B.2 が設計通りミラー、BG が L5014 で sanction)。副産物: **2026-05-23 wave1 監査の「App.B + Thm A.5 スキップ推奨」を撤回**(no-Gorenstein 方針下で App.B は 6.2 代替の本線・必須)。per-section ノート (s06/appA/appB) + wave1 監査 + cross-refs に訂正タグ反映済。次の実装: A.4(b)/(c) reduction(7.3 核)→ Prop 1.15(b)/L(S) char S 小補題 → A.5 → App.B → §8-§16 を L(S) 化。
- **2026-05-31** **(catch-up: 05-29→05-31 の集約記録)** BG ローカル解析と Peterfalvi が大きく前進。**正確な live 状況は memory `ft-master-roadmap` + `notes/meta/ft_master_roadmap_2026_05_29.md`(冒頭 05-31 訂正ヘッダ付き) + 各 `notes/` が正本**、本エントリは要約:
    - **BG App.A 完結**: A.4(a)/(b)/(c) PSTAB + A.5 が sorry-free・axiom-clean (issue 0047/0049 close)。**App.B Puig L(S)** B.1/B.2/B.3/B.4(b) (issue 2000/2001) + **BG Thm 6.2 一般形** `Z(L(S))·O_{p'}(G)⊴G` (`OddOrder/BG/AppB_Thm62.lean`, issue 2002) = Glauberman Z(J) 自己完結代替の完成形 (§7–§16 の normal-J ハブ)。
    - **BG §1 Thm 1.13** Thompson critical subgroup (`OddOrder/GroupTheory/CriticalSubgroup.lean` + `thompson_critical_omega`, issue 0016 close; Gorenstein 5.3.11/5.3.13 直参照)。
    - **BG §4 Blackburn 大半完成**: Thm 4.12(a)(b)(c) / Prop 4.3(a)(b) / Prop 4.8(a)(b) / **Prop 4.11 (Huppert)** / Lem 4.9 / Lem 4.15 / GL(n,p) 橋 / Gorenstein Lem 4.12–4.14 が sorry-free。**残 = Gorenstein Thm 4.15(i) precursor (SCN₃=∅⇒pRank≤2) → BG Lem 4.13 → Thm 4.16 apex (未 statement)**。tracker = issue 0051。
    - **Peterfalvi worktree を main へ merge** (先行 f5bcb14 + 2026-05-31 834b76c)。§7 coherence / §8 / §9 / Dade isometry / Clifford / ZIrr / `InflationCharacter.lean` 配線済。worktree も main に ff 同期、`lake build OddOrder` green **3372 jobs**。
    - **実 `sorry` は全リポジトリで 2 個** (`Peterfalvi/S08_CoherenceTheorems.lean` `sibleySetup_is_coherent`=issue 0046 / `Peterfalvi/S09_NonexistenceCertain.lean` `card_G0_lower_bound`=issue 0044)、`axiom`/`admit` 0。

- **2026-06-20** **(catch-up: 06-01→06-20 の集約記録)** BG 局所解析 spine と Peterfalvi が大きく前進し FT 経路は終盤へ。**正確な live 状況は [`notes/meta/ft_master_roadmap_2026_05_29.md`](notes/meta/ft_master_roadmap_2026_05_29.md) 冒頭「2026-06-20 現状更新ヘッダ」+ memory `ft-master-roadmap`/`ft-endgame-two-poles` が正本**、本エントリは要約:
    - **BG spine 完成域**: §9 Uniqueness (9.1-9.6) + §10 Thm 10.1 (fusion control) + §11 全 7 結果 + §12 大半 + §13 endgame (13.7-13.13) + Thm 3.4/3.5/3.6 (任意体) + App.C 完全形式化 — すべて sorry-free・axiom-clean。forward axiom 残 **0 本**。
    - **BG §14-16 + Pf §6-§16 が active frontier に昇格**: 最上位 `feitThompson` は配線済 (還元 sorry-free)。FT 層の実 obligation = **2 POLE** = POLE-1 `sectionSixteenHypothesis_of_isMinimalSimpleOdd` (→ `Peterfalvi.S16.Hypothesis`、`Section16Inputs` 3 producer) + POLE-2 `field_normalizer_structure` (Pf 14.2)。
    - **2026-06-20 セッションの frontier 前進** (3 レーン B/F/H 並行): **BG Thm 15.2 (M_F 構造) を step-1〜(c)/(d)/3 まで sorry-free 構築** (残 wrapper gate `Q0⊴M`) / **Pf (6.8) case-A coherence producer COMPLETE** + case-B `|Y|=2` 数学解決 + cY-rewiring foundation / **Pf (14.12) M_F automorphism-equivariance reduction** + (13.17) を Phase 0-2 構造プログラム化 (実 assembly + 4 gate 隔離)。
    - **進捗の測り方を成文化** (CLAUDE.md「進捗の測り方」節新設): 目的 = honest な FT 証明の積み上げ。`sorry` 数は進捗指標でない (両方向で誤る)。doneness は carrier・仮説の構成可能性で判定。"FT-orphaned"・"閉じても sorry 減らない" の言い回しは使わない。
    - 実 `sorry` = **137** (`bin/count-sorry`、transitive scaffold 数; AxiomsCheck-guard 島の「2 個」= issue 0046/0044 とは別指標)。build green **3869 jobs** / `axiom` 宣言 0 / origin push 済。

- **2026-06-22** **(レーン統合 tick — 4 レーン B/F/H/C を main へ合流)** 06-20→06-22 の 2 日間で 4 レーンが並行前進、全量 main 合流 (clean working tree, `git log main..<lane>` 空)。build green **3881 jobs** / AxiomsCheck OK (forward axiom 3 本のみ allowlist) / 新 `axiom` 0。**FT 経路 scaffold sorry = 131** (`bin/count-sorry`; 06-20 の 137 から純減)。正本は memory `ft-endgame-two-poles`/`ft-master-roadmap` + [`notes/meta/merge_monitor.md`](notes/meta/merge_monitor.md) (4 レーン体制 = F:BG §14-16 構造 / B:Pf §10/§12/§13 Dade char / H:Pf §11 Wielandt §9 + §14-15 / C:Pf §16 endpoint + POLE-2)。本 tick の主着地:
    - **lane-f (BG §14-16)**: Thm 15.7(c) type-F を faithful `M'≤F(M)` に修正 (MathComp 交差検証で印刷版 `M'=F(M)` を overstatement と確定) / BG Thm 15.2 完全 close / Theorem C 9-12 conjunct + TypePData 矛盾修正 (issue 7008) / **BG Lemma 14.11 phase 1** (Q⊄F(E) ⟹ q∈τ₁(M) ∧ C_{M_σ}(Q)=1)。
    - **lane-b (Pf §10/§12/§13)**: (10.5) ζ^τ₁ vanishes on V (a=0 計算完遂, axiom-clean) / issue 1007 grid hoist DONE (S06→S05_GridTrichotomy) → endgame de-risked。
    - **lane-h (Pf §11/§14-15)**: **(9.1) Wielandt `wielandt_fixedPoint_frobenius` 完全 unconditional** (issue 2014 closed) → (9.3)/(9.4) driving; (9.4) seed `exists_chiefFactor_seed` (群論的内容 complete) / Huppert V.8.18 b)。
    - **lane-c (Pf §16)**: 基盤 char-infra ((14.11.2) arithmetic + (3.9)/(14.11.3) parity cores) へピボット (§16 全 sorry が上流 gate と確認後)。
    - 旧「現フロンティア §7」「残 sorry 2 件 = (6.8)+(7.10)」(Phase 表) を本 tick で **stale 解消**。

- **2026-07-02** **(catch-up: 06-23→07-02 + 3 レーン再編 + hub 全体レビュー)**:
    - **06-28 全面再配分**: 依存ゲート方式を廃し **signature contract 方式** (ゲートは幻・sorried cite で
      前進) の 4 レーン a/b/c/d へ (正本 [`notes/meta/ft_lane_reallocation_2026_06_28.md`](notes/meta/ft_lane_reallocation_2026_06_28.md))。
    - **07-02 3 レーン再編**: char endgame は密結合パイプラインと判明し **lane d 退役** — BG/** は
      **FROZEN-COMPLETE** (spine 消費 = Prop 16.1 sorry-free のみ、残 15 sorry 全 off-spine)、σ-theory
      generic engine (TypePGaloisUBound 等) sorry-free 凍結、FeitThompson carrier は a に fold。現行 =
      **a (Pf §10–13 + σ-tail) / b (S14 Dade tower + coherence infra + S10 §8 carve-out 0096) /
      c (S15/S16 chain + 構成的 Clifford 9002)**。
    - **FT 層配線完了**: `FeitThompson.lean` 実 sorry **0**。唯一の bare spine sorry =
      `S12.exists_zeta_residual_not_orthogonal` (Pf 11.8、lane a が 11.8.2/11.8.3/11.8.5 を集中攻略中)。
      (12.6) coherence tower / `theorem88_caseB_holds` / (6.8) Sibley / S03–S08 帯は sorry-free。
    - **hub 全体レビュー (07-02)**: lane-role review + docs/plan review (計 12 並列 agent) → 裁定 4 件
      (S10 `support_mutual_exclusion` false-statement 修正の受理 / §8 Dade-support carve-out 0096 /
      `card_G0_lower_bound` = **on-spine** と確定し lane a へ (issue 0044) / `sibleyTarget_H0C` = lane a +
      soundness 監査必須 (issue 7001))。S12 を prefix-split (Core 6146 + active leaf 2768、issue 0076)。
      issue 30+ 件 close、stale docs 一掃。sorry: `bin/count-sorry` **115** / comment-strip 実数 **103**
      (lane 所有 74 + BG 凍結 15 + Pf Appendices 凍結 15)。build green **3898 jobs** / AxiomsCheck OK。

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

> ⚠ **このチェックリストは「節ごとの初期調査メモ + 実装見積り index」であり live な進捗トラッカではない。**
> 各 `[ ]` は「節を一次調査した」時点のスナップショットで、その後の部分形式化 (§1–§13 spine の sorry-free
> 化、§14–§16・Pf §10–§16 の進行) は反映していない。**節ごとの live 状況の正本 (2026-07-02 更新)**:
> git log + `issues/` (一次情報) + [`notes/meta/lane_reallocation_2026_07_16.md`](notes/meta/lane_reallocation_2026_07_16.md)
> (レーン配分の正本。旧 `ft_lane_reallocation_2026_06_28.md` は 2026-07-16 に SUPERSEDED) + [`notes/meta/merge_monitor.md`](notes/meta/merge_monitor.md) (合流手順 + 現状メモ)
> + memory `MEMORY.md`/`ft-four-fronts-w1-w4`。〔旧 pointer (memory `ft-master-roadmap`/`ft-endgame-two-poles`、
> `ft_master_roadmap_2026_05_29.md` ヘッダ) は consolidate/凍結済で無効〕。チェックボックスは敢えて触らず、
> 調査メモ link 集として温存する。

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
- [ ] §2 General Results on Representations (p.9) — 6 結果. Operator group 表現, Schur + abs.irred., Clifford 系, Fong-Swan, extraspecial p-群 + cyclic action, 奇数 2-dim. *前提: Isaacs Ch.6 §6F Clifford (Prop 2.2)* — [調査メモ](notes/bg/s02_representations.md): **Skeleton 完成 (2026-05-24, [S02_Representations.lean](OddOrder/BG/Ch1_Preliminary/S02_Representations.lean))**. audit 訂正 (2026-05-23): 旧 "§9 1-2 箇所 optional, skip 推奨" → 実測 **8+ cites** (§3 ×5, §4 Lem 4.17, §15 Thm 15.7, **App.A Thm A.1**), **Phase 2a 第 1 波必須**. 着手順: Thm 2.6 → Prop 2.4 → Prop 2.1 → Thm 2.5 → Prop 2.2 (Ch.6 §6F 待ち); Lem 2.3 Fong-Swan (forward use 0) defer
- [ ] §3 Actions of Frobenius Groups (p.17) — 10 結果. Frobenius kernel nilpotent + 表現論的 Frobenius action. **Isaacs Ch.6 全面前提**. *前提: Isaacs Ch.6 完成* — [調査メモ](notes/bg/s03_frobenius_actions.md): Lem 3.2 = Isaacs 6.2 (quotient Frobenius), L825 Note = Isaacs 6.24 (kernel nilpotent), Thm 3.6 Z-group centralizer (244 行 13 step proof), Peterfalvi 04.11 (9.1) Wielandt 引用. mathlib `FrobeniusGroup` 完全未収載, 90% 新規
- [ ] §4 p-Groups of Small Rank (p.33) — 10 結果. Rank ≤ 2 p-群構造定理 (Blackburn). *前提: Isaacs Ch.4* — [調査メモ](notes/bg/s04_pgroups_small_rank.md): **Thm 4.16 (Blackburn) が中核**. m_p(G), r_p(G) rank 概念で §10 の α(M) = {p : r_p(M) ≥ 3} を定義. mathlib カバレッジ 30-40%, 新規 60-70%, 25-35 日推定
- [ ] §5 Narrow p-Groups (p.44) — 7 結果. Narrow p-群族, Sylow 形状制限. *前提: Isaacs Ch.4* — [調査メモ](notes/bg/s05_narrow_pgroups.md): Thm 5.3 narrow characterization (r(R) ≤ 2 自動 narrow, r ≥ 3 は elementary abelian maximal で characterize). §4 (Small Rank) を統一概念に. mathlib 100% 新規
- [ ] §6 Additional Results (p.49) — 7 結果 (Thm 6.1, 6.2, 6.3, 6.4, 6.7 + Lem 6.5, 6.6). solvable + p-length 1 + Frobenius factorization. **§7-§16 で多用される道具袋**. mmd L1957-2128 (§6 ヘッダ Nougat 抽出ミスあり、`**6.**` インライン). *前提: Isaacs Ch.5, Ch.7* — [調査メモ](notes/bg/s06_additional.md): **Thm 6.2 (normal-J) ≡ Isaacs Thm 7.6** odd-order 等価, §8 (3 箇所) §9 (2 箇所) App.A (Thm A.4(b) で再述) App.B App.C で 7+ 引用. 形式化方針: Isaacs 7.6 import 推奨 (1-2 日) vs BG App.A 経由再証明 (4-5 日). MISSING_PAGE:67 は §6 末で論理影響無し

**Chapter II. The Uniqueness Theorem** (10 結果)
- [ ] §7 The Transitivity Theorem (p.55) — 3 結果. **Hypothesis 7.1 で最小反例 G を固定** (mmd L2133). *前提: Isaacs Ch.7 (J(P))* — [調査メモ](notes/bg/s07_transitivity.md): Hypothesis 7.1 (G, ℳ, 𝒰, SCN_3(p), ℋ_H(A;π) 記法), Thm 7.4 propagation theorem, Thm 7.6 Thompson Transitivity. §8-§16 暗黙前提. 実装 11-15 日
- [ ] §8 The Fitting Subgroup of a Maximal Subgroup (p.61) — 1 結果. **Thm 6.2 を 5+ 箇所引用**. *前提: §6, §7, Isaacs Ch.7 Thm 7.6* — [調査メモ](notes/bg/s08_fitting_max.md): Theorem 8.1 + 番号付き式 (8.1)-(8.13). Case (a) F(M) not p-group / Case (b) F(M) = p-group の分岐証明. Thm 6.2 引用 L2456/L2478/L2482 の精密文脈. §9 Uniqueness の直接前提
- [ ] §9 The Uniqueness Theorem (p.64) — 6 結果. central structure + maximal subgroup 一意性. **Thm 6.2 を 4+ 箇所引用**. *前提: §8, Isaacs Ch.7 Thm 7.6* — [調査メモ](notes/bg/s09_uniqueness.md): Thm 9.6 主結果 (r(K) ≥ 2 ⇒ K ∈ 𝒰), Lemma 9.5 pivotal (SCN₃(p) ∈ 𝒰, 67 行最複雑証明), §10-§16 + App.C で連鎖被引用. 実装 7-10 日

**Chapter III. Maximal Subgroups** (32 結果)
- [ ] §10 The Subgroups M_α and M_σ (p.69) — 6 結果. maximal subgroup の族の定義・性質. *前提: §9* — [調査メモ](notes/bg/s10_malpha_msigma.md): α(M) = {p : r_p(M) ≥ 3}, σ(M) = {p : N_G(P) ⊆ M}, β(M) ideal primes. Thm 10.2 Hall M_α/M_σ 主定理, Cor 10.7 Sylow structure (5 部). Lem 6.5/6.6 多用 (L2795-L2801)
- [ ] §11 Exceptional Maximal Subgroups (p.80) — 4 結果. 例外 maximal subgroup 分類. *前提: §10* — [調査メモ](notes/bg/s11_exceptional_maximal.md): Hypothesis 11.1 + Thm 11.3/11.5/11.7 のチェーン (nilpotency → abelianity → normality M_σA ⊴ M). §10 から 13 引用箇所継承
- [ ] §12 The Subgroup E (p.83) — 15 結果 (大規模, §12 が小章相当). 部分群 E の構造と共役性. *前提: §10-§11, Isaacs Ch.7* — [調査メモ](notes/bg/s12_subgroup_e.md): τ₁/τ₂/τ₃(M) partition + Hall E₁/E₂/E₃. Group A (12.1-12.4) E 基本, Group B (12.5-12.12) τ₂(M)≠∅ 局所解析最複雑, Group C (12.13-12.19) σ(M) embedding. **2000+ 行 Lean 予想, 3 ファイル分割推奨**
- [ ] §13 Prime Action (p.97) — 7 結果. derived series, Thompson 風作用. *前提: §12* — [調査メモ](notes/bg/s13_prime_action.md): Thm 13.4 中核 (Thompson 風, derived series 制御, 33 行証明), Lem 13.7 E₁E₃ 同時作用 conditional. §12 から 13+ 引用. 800-1100 行 Lean

**Chapter IV. The Family of All Maximal Subgroups of G** (17 結果)
- [ ] §14 Maximal Subgroups of Type 𝒫 and Counting (p.105) — 7 結果. counting argument; type-𝒫 構造. *前提: §10-§13 統合* — [調査メモ](notes/bg/s14_type_p_counting.md): Thm 14.7 中核 (Type 𝒫 family duality + Z cyclicity + TI-set), Cor 14.10 **ℓ_σ(g) ≤ 2** が framework 頂点. σ-分解 + κ(M) で Type 𝒫₁/𝒫₂ 分類
- [ ] §15 The Subgroup M_F (p.117) — 9 結果. Fitting 関連 maximal. *前提: §14* — [調査メモ](notes/bg/s15_m_f.md): Theorem 15.2 (M_F ≠ M_σ ⇒ type 𝒫₁), Type ℱ/𝒫₁/𝒫₂ 分類. §16 への橋渡し. 800-1200 行 Lean, 6-12 週推定
- [ ] §16 The Main Results (p.123) — 1 結果 (Theorem B). FT 局所部の最終. App.C / Peterfalvi へ橋渡し. *前提: §1-§15 全統合* — [調査メモ](notes/bg/s16_main_results.md): **Theorem A-E** statement (Type I-V 分類確定). Peterfalvi §10 (8.11-8.13) 入力. Phase 3 結合の前提. 18-25 日独立, 10-12 日 Peterfalvi 並行

**Appendices** (17 結果)
- [x] App.A Prerequisites and p-Stability (p.135) — 5 結果 (Thm A.1-A.5). **✅ 完成 (2026-05-29, sorry-free・axiom-clean; issue #0041/#0047/#0049 全 close)** = `OddOrder/BG/AppA_PStability.lean`。A.2 = Gorenstein 3.8.1 次元縮約は eigenvector approach で形式化済 (`quadratic_two_generated_irreducible_finrank_eq_two`)、A.3/A.4(a)(b)(c)/A.5 もすべて proved (`thmA1`–`thmA5_part2`, AxiomsCheck 登録)。A.5 が App.B Puig L(S) の中核前提。〔監査 2026-06-03: 旧「[ ] A.2 がゲート未形式化」は **stale**, 全完了済。〕
- [ ] App.B The Puig Subgroup L(S) (p.139) — 3 結果. J(S) の代替 Puig 不変部分群. *前提: App.A* — [調査メモ](notes/bg/appB_puig.md): Lem B.1-B.3 + Thm B.4 (= Thm 6.2 substitute). **⚠️ 2026-05-28 訂正 ([設計ノート §0](notes/meta/bg_s6_appAB_route_2026_05_28.md))**: 旧「J(S) path で完結、App.B は optional」は誤り。Isaacs が Z(J) を省くため **App.B Thm B.4 が Thm 6.2 の唯一の自己完結代替で必須**(B.4 ⟸ A.5 ⟸ A.4(c) ⟸ … ⟸ A.2=issue #0041)。
- [ ] App.C The Final Contradiction (p.145) — 3 結果 (Theorem C, Lem C.1, C.2). **Peterfalvi 1984 paper [22] の Carlip-Wheeler 編集再録**. **Phase 2b §9 と統合形式化**. mmd L4763 `## Appendix D Main Theorem` は Nougat 抽出ミスで App.C 本文の続き. — [調査メモ](notes/bg/appC_final_contradiction.md): 指標論 (Peterfalvi) vs 有限体代数 (BG) の対応マップ. Theorem C + Lem C.1-C.3 + 11 個 Preliminary (I)-(XI). Phase 3 で統合
- [ ] App.D CN-Groups of Odd Order (p.153) — 2 結果. Feit-Hall-Thompson 1960 短縮ルート. FT 本筋外 (△). — [調査メモ](notes/bg/appD_cn_groups.md): Lem D.1 (Sylow TI for min simple CN) + Lem D.2 (P ⊆ N'). Thm 6.2 + Focal Subgroup Theorem を CN-theorem に応用. **Phase 2 完全 skip 推奨**, Phase 4 後の発展材料
- [ ] App.E Further Results of Feit and Thompson (p.157) — 5 結果. 発展結果. Phase 2a 完了後の発展材料、または Phase 4 メイン結合時に. △. — [調査メモ](notes/bg/appE_further_results.md): Thm E.1 (Philip Hall lower central) + Prop E.2 (φ(x)=x^p homo) + Thm E.3 (Feit-Thompson 1991 regular operator), BG 本書での被引用 0. Phase 4 後の発展材料 (~1000 行 Lean, 13-18 日)

### Phase 2b — Peterfalvi 本体 (Character Theory for the Odd Order Theorem)

**Overview**: [`notes/peterfalvi/_overview.md`](notes/peterfalvi/_overview.md) — 本文 113 結果 ((N.M) 形式) + 付録 27 結果 (140 結果). FT クリティカル: §3-§8 (指標論コア) → §9 (= BG App.C) → §10-§15 (型分析、BG Ch.3-Ch.4 出力依存) → §16 (G 非存在). 全節 ☆ (FT 必須). 付録は △.

- [ ] §1 Introduction (pp.1-2) — 0 結果. FT 証明戦略 + BG 依存明示. *前提なし* — [調査メモ (§1+§2 合体)](notes/peterfalvi/s01s02_intro_notation.md): FT 二部構成 (局所/指標) + [BG]/[Is]/[HB]/[H] 文献依存
- [ ] §2 Notation (pp.3-4) — 0 結果. 指標論・加群記号. *前提なし* — [調査メモ (§1+§2 合体)](notes/peterfalvi/s01s02_intro_notation.md): Irr(G), CF(G), Z[Irr G], Res/Ind, I_G(θ), F(G), O_p(G) 等 40+ 記号 → mathlib 対応表
- [ ] §3 Preliminary Results from Character Theory (pp.5-9) — 10 結果 ((1.1)-(1.10)). Isaacs [Is] 表現論 + Peterfalvi 補強. mathlib `Character.lean` API 橋渡し. *前提: Phase 1 完成, mathlib `RepresentationTheory.Character`* — [調査メモ](notes/peterfalvi/s03_preliminary_character.md): (1.4) tau isometry が §4 Dade の準備 (☆☆☆), (1.3) Fourier 展開も新規. (1.1), (1.5)-(1.8) は Isaacs [Is] Thm 6.32, 6.5, 6.11, Cor 6.28, Cor 2.30 の odd-order 再述. 実装量 ~400 行
- [ ] §4 The Dade Isometry (pp.10-14) — 6 結果 ((2.1)-(2.6)). **TI-subset 上の virtual character isometry**. **新規概念**. *前提: §3* — [調査メモ](notes/peterfalvi/s04_dade_isometry.md): **Phase 2b の山場**, mathlib 完全新規 (~70% 新規実装). 主定理 (2.6) は (a) isometry + (b) virtual character preservation. 形式化方針: **predicate-based (候補 3 推奨)** で `IsDadeIsometry τ hyp` + existence theorem. §5-§8 Coherence の前提. 実装量 ~400-450 行 / 16-18 時間
- [ ] §5 TI-Subsets with Cyclic Normalizers (pp.15-20) — 5 結果 ((3.1)-(3.5)). cyclic normalizer 特殊化. *前提: §4* — [調査メモ](notes/peterfalvi/s05_ti_cyclic_normalizer.md): (3.1) Hypothesis W = W₁×W₂ cyclic + V TI-subset, (3.2) σ Dade isometry の 4 性質, (3.5) **orthonormal (χ_{ij}) 族と分解公式** (最重要, Case I/II 矛盾排除, 計算の山場). 実装 23-31 時間
- [ ] §6 The Dade Isometry for a Certain Type of Subgroup (pp.21-24) — 5 結果 ((4.1)-(4.5)). Dade 拡張. *前提: §4-§5* — [調査メモ](notes/peterfalvi/s06_dade_certain_subgroup.md): (4.2) Hypothesis L = K ⋊ W₁ + cyclic Hall + C_K(x) = W₂, (4.3) TI-subset (W - W₂) + Induced character decomposition μ_ij, (4.5) χ_j i-independence + Irr(L) 完全性. 13-16 時間
- [ ] §7 Coherence (pp.25-29) — 6 結果 ((5.1)-(5.6)). **Coherence 定義 + 基本性質**. Dade 後の isometry 整合条件. **新規概念**. *前提: §4* — [調査メモ](notes/peterfalvi/s07_coherence.md): (5.1) Coherence の正式定義 (Z[S] への τ 拡張 + virtual character の差での expression). 形式化候補: **predicate-based (IsCoherent τ̃)** が §4 設計と整合, coherent triple (τ₁,τ₂,τ₃) 比較が自然. 14-18 時間
- [ ] §8 Some Coherence Theorems (pp.30-37) — 4 結果 ((6.1)-(6.4)). Coherence 応用定理. Sibley/Reynolds 系含む. *前提: §7* — [調査メモ](notes/peterfalvi/s08_coherence_theorems.md): Sibley 1984 (6.4)-(6.6) p-group determination bound, Reynolds 1965 (6.7) character mod \|P\|, (6.8) main theorem Frobenius family 統合 (最複雑, 7-10 日). 30 日推定
- [ ] §9 Non-existence of a Certain Type of Group of Odd Order (pp.38-43) — 6 結果 ((7.1)-(7.6)). **≡ BG App.C Theorem C**. Frobenius family の非存在. *前提: §3-§8 + BG §3* — [調査メモ](notes/peterfalvi/s09_nonexistence_certain.md): BG App.C と内容重複 (BG L4759-5005). 形式化方針: **Peterfalvi §9 を一次, BG App.C は section docstring + reference**. Phase 3 で equivalence lemma `OddOrder.BG.AppC.TheoremC ≅ OddOrder.Peterfalvi.S09.TheoremC`. 有限体 F_{p^q} + norm-1 部分群 U + Frobenius H = PU の Lean 形式化設計含む
- [ ] §10 Structure of a Minimal Simple Group of Odd Order (pp.44-49) — 6 結果 ((8.1)-(8.6)). **G の Type I-V 分類定義**. BG Theorem A-E 翻訳. *前提: **BG §10-§16 全面*** — 調査メモ (調査メモ削除済): (8.11)→BG Thm A, (8.12)/(8.13)→Thm B/D, (8.8)-(8.9)→Thm C. Type 𝓕/𝓟 基礎層 + Type I-V 精密 5 分類. `inductive PeterfalviType` Lean 設計. 20-25 日
- [ ] §11 Maximal Subgroups of G of Types II, III and IV (pp.50-57) — 9 結果 ((9.1)-(9.9)). (9.1) Wielandt 作用, (9.2) Frobenius kernel cohomology. *前提: §10 + BG §11-§13* — 調査メモ (調査メモ削除済): (9.7) Clifford 分岐 (Case (a) 分散的 H̄ vs Case (b) F = 𝔽_{p^q} 既約), (9.10) Frobenius 実現化, (9.11) Coherence 完全性証明 (8 sub-lemma, 最大規模)
- [ ] §12 Maximal Subgroups of Types III, IV and V (pp.58-63) — 7 結果 ((10.1)-(10.7)). (10.7) [S,S] が Frobenius. *前提: §11* — 調査メモ (調査メモ削除済): (10.7) [S,S] Frobenius §16 最終矛盾の重要段階, (10.8) ℐ non-coherent 背理法 (numerical chain). 680-850 行 Lean, 9-11 日
- [ ] §13 Maximal Subgroups of Types III and IV (pp.64-68) — 8 結果 ((11.1)-(11.8)). *前提: §12* — 調査メモ (調査メモ削除済): (11.3)-(11.5) commutator 階層 M''=HC, (11.6)-(11.7) 核構造 (p-group, H₀=H', C=U'), (11.8) character orthogonality (5 段階 sub-lemma 最技巧), (11.9) Type III 確定
- [ ] §14 Maximal Subgroups of Type I (pp.69-74) — 13 結果 ((12.1)-(12.13)). 型 I は最複雑. *前提: §13 + BG §12 (E)* — 調査メモ (調査メモ削除済): (12.7) **Main Theorem: Type I ⇒ Frobenius group**, (12.12) complement order e は (p±1) の約数, (12.16) Sylow non-cyclic 反例排除, (12.17) Case (b) [S,T 存在] 強制. 1000-1500 行 Lean / 4-5 週
- [ ] §15 The Subgroups S and T (pp.75-86) — 17 結果 ((13.1)-(13.17)). **本文最大規模 (365 行)**. S, T の位数・正規化群・指標. §16 直前の最終仕込み. *前提: §14 + BG §15 (M_F)* — [調査メモ](notes/peterfalvi/s15_s_and_t.md): Phase A setup + B character + C 位数 c=1 + D 外部構造の 4 フェーズ. (13.12) c=1 numeric exhaustion, (13.15) u 決定, (13.19.c) §16 dichotomy 入力. **1500-1800 行 Lean / 6-7 週, 4 ファイル分割推奨**
- [ ] §16 Non-existence of G (pp.87-92) — 11 結果 ((14.1)-(14.11)). **FT 完了 = G の非存在**. 指標論計算が中心. *前提: §3-§15 + BG §16* — 調査メモ (調査メモ削除済): (14.11) 主結果に 4 sub-propositions, (14.11.4) norm inequality cascade で最終矛盾, BG App.C との合体方針 (Phase 3). Phase 4 FeitThompson メイン定理の statement 設計. **1000-1200 行 Lean / 5 週**

**Peterfalvi 補章** (27 結果, 全 △ = FT 経路外)
- [ ] App: A Theorem of Suzuki (pp.97-134) — 21 結果 (Prop 1-16 in 05.3 + Lemmas in 05.0-05.6). Suzuki 1962: PSL(2,q), Sz(q), PSU(3,q) の二重推移群特性化 — 調査メモ (調査メモ削除済): mathlib PSL(2,q) 既存, Sz(q)/PSU(3,q) 完全新規. Phase 1 Ch.8 (Permutation Groups) 依存. 本筋外 (△). 1500-2500 行 Lean
- [ ] App: A Special Case of a Theorem of Huppert (pp.135-136) — 1 結果. Huppert 1957 定理の Peterfalvi 流再証明 — 調査メモ (B-E 合体) (調査メモ削除済)
- [ ] App: On Near-Fields (pp.137-138) — 2 結果. Near-field (Wedderburn 系) の基本 — 調査メモ (B-E 合体) (調査メモ削除済)
- [ ] App: On Suzuki 2-Groups (pp.139-143) — 4 結果. Higman 分類 Suzuki 2-群 — 調査メモ (B-E 合体) (調査メモ削除済)
- [ ] App: The Feit-Sibley Theorem (pp.144-150) — 2 結果. Feit-Sibley 1976 定理 — 調査メモ (B-E 合体) (調査メモ削除済)

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

- **全 3 冊完全形式化フェーズ (2026-07-16 開始) のギャップ調査**: [`notes/meta/three_books_full_survey_2026_07_16.md`](notes/meta/three_books_full_survey_2026_07_16.md) — feitThompson axiom-clean 達成 (2026-07-15) 後の全 815 結果インベントリ (実作業ギャップ 214 件) + 推奨順序。⚠ **2026-07-19 の hub 裁定 9154 で「正本」から降格** — 未/部分ラベルが実体と食い違う実績があるため、**scope の一次情報にしない** (正本 = git log + `issues/` + 実測 grep)。着手前に必ず実測で再確認する
- mathlib カバレッジ詳細 (どの mathlib 資産が使えるか、何が欠けているか): [`notes/meta/mathlib_coverage.md`](notes/meta/mathlib_coverage.md)
- プロジェクトセットアップ状態: メモリ `project_setup_state.md` 参照
