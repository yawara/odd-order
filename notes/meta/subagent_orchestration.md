# サブエージェント運用方針

**スコープ**: `odd-order` プロジェクト (Feit-Thompson 形式化, AI エージェント駆動) における
サブエージェント並列実行の判断基準・プロンプト品質・トラブル時の挙動。

**初版**: 2026-05-21 (Ch.1 §1A/§1C/§1D に並列エージェントを投入したセッション後の反省を元に)。

## 1. 使うとき (proactively delegate)

### 1.1 独立並列タスク

ファイル境界・節境界が明確で、互いに干渉しない仕事。

- ✅ **複数節の同時実装**: 例 `§1A 残り` + `§1C` を別ワークツリーで並列。同じファイルでも違う section block を編集するだけなら整合可能。
- ✅ **`isolation: "worktree"` 指定**: 並列性能を出すなら必須。main worktree のファイル状態と分離されるので、戻り時に diff を読んで統合できる。

### 1.2 mathlib 大規模偵察 (Explore エージェント、read-only)

「何が既にあって、何が無いか」の悉皆 grep。

- ✅ **長い候補リストに対する一括 grep**: 「`opCore` 相当 / `iSupIndep_of_coprime_card` / `isNilpotent_iff_sylow_normal` / ...」を一気に確認。逐次 grep は私のコンテキストを浪費する。
- ✅ **設計に大きく効く発見**: Explore の出力が「step 7, 8 は `isNilpotent_of_finite_tfae` で吸収可能」のような *設計を簡略化する* 種類なら投資対効果が高い。

### 1.3 20-50 行クラスの集中的な証明

`Sylow.coe_subgroup_smul` ↔ `mem_pointwise_smul_iff_inv_smul_mem` ↔ `MulAut.apply_inv_self` のような
rewrite チェーンを試行錯誤する作業。

- ✅ **数学的方針が固まっていて Lean tactic レベルのトライアンドエラーが本体**: 集中して詰めるエージェント向け。
- ✅ **私のメインコンテキストを節約したい**: 試行錯誤の中間プロセスをエージェント内に閉じ込められる。

## 2. 使わないとき

### 2.1 アーキテクチャ判断

名前空間設計、ファイル分割粒度、依存方向の選択。

- ❌ **会話のコンテキストが本質**: 「これは `Subgroup.fitting` か `OddOrder.fitting` か」「ファイルを今割るか先延ばすか」など、これまでの議論・規約に依存する判断は私が下す。
- ❌ **ブリーフィングコストが利得を上回る**: 30 分の前提共有が必要なら自分でやる方が速い。

### 2.2 複数ファイルにまたがる軽い follow-up

「`Cor 1.3` の hn1 を整理」「import を 1 行追加」レベル。

- ❌ **タスク 1 つあたりが 5 分以下**: エージェント起動コストとプロンプト書きが重い。

### 2.3 検証コストが委譲利得を上回る場合

エージェントが "completed" を返しても build red の可能性がある (今日 Agent D が実例)。

- ❌ **出力を 1 行ずつ verify 必須な案件**: 結局 build を回して fix する必要があるなら、最初から自分で書くほうがトータル速い。
- ⚠️ **緩和策**: プロンプトに「`lake build OddOrder` を green まで通すこと」「green になったら何 jobs か報告」を必須化することで自己検証を強める。

### 2.4 既存の作業中エージェントと同じ範囲を触る

- ❌ **同一節を 2 エージェントが編集**: 統合時のコンフリクト解決コストが大きい。並列に投げる場合は **節境界 (1A vs 1C vs 1D) で完全分離**する。

## 3. プロンプト品質チェックリスト

今日の Agent D (`opCore.normal` 証明) で「数学的方針は正しいが Lean tactic で詰まった」事例から:

```
[必須]
- 教科書のステートメント (Isaacs 原文を貼る)
- 形式化のターゲット (`instance opCore.normal ...` のシグネチャ)
- 使う mathlib lemma 候補 (具体名 + 行番号レベルで; 例: `Sylow.coe_subgroup_smul @ Sylow.lean:244`)
- 既存の §XY との整合 (docstring 形式 `**Isaacs ...**`, 識別子の規約)
- 検証要件 (`lake build OddOrder` green)
- 禁止事項 (commit しない, push しない)

[品質を上げるオプション]
- "つまずきそうな所" を先回りで列挙 (今日の Agent D 案件で「`map_inv` の向き」「`MulAut.apply_inv_self` の存在」を事前に仕込むべきだった)
- 代替アプローチを 1 つ提示 ("詰まったらこちらを試せ")
- 期待される戻り値の形式 (200 語以内の Markdown レポート、TODO に残したものの理由を 1 行ずつ)
```

## 4. トラブル時の挙動

エージェントの提出が build を壊す / 詰まる場合の対処順:

1. **最小修正で green に**: 今日の `← map_inv` → `rw` 順入れ替えのような明らかな direction 違いなら私が直す。
2. **TODO 化して先へ**: 30 分以上格闘しそうなら、エージェントの試行を残しつつ `-- TODO ...` コメントに置き換えて build を unblock。これは「失敗を埋葬する」ではなく「進捗を優先する設計判断」。
3. **専用エージェントを再投入**: 完全新規のフレッシュなコンテキストで 1 つの証明だけに集中させる (今日 `opCore.normal` を Agent D に再投入した例)。

## 5. 今日 (2026-05-21) のセッションの実データ

エージェント並列構成と結果:

| エージェント | 役割 | model | 結果 | 統合 |
|---|---|---|---|---|
| A | §1A 残り (Cor 1.2, 1.3, 1.5, 1.6) | sonnet (worktree) | Cor 1.2, 1.3 ✅ / 1.5, 1.6 build red | 1.2, 1.3 採用; 1.5, 1.6 は TODO 化、後にユーザ手動で完成 |
| B | §1C (Thm 1.11–1.18) | sonnet (worktree) | 7/8 ✅ / 1.18 で `inf_of_le_right` ↔ `_left` の向き誤り | 私が `_left` に直して採用 |
| C | §1D mathlib 偵察 | sonnet (Explore, read-only) | 完璧 — `isNilpotent_of_finite_tfae` 発見で steps 7-8 不要化 | 設計ノート更新 |
| D | `opCore.normal` + `normal_pgroup_le_opCore` | sonnet (worktree) | 近かったが build red (`map_inv` 向き) | 私が向きを直して採用 |

**得られた進捗**: §1A (6 件), §1B (4 件), §1C (7/8), §1D opCore + Problem 1B.2 + Thm 1.26 + fitting + fitting.normal, §1E Lemma 1.34, Thm 1.35 — 1 セッションで 20+ 件のステートメント。
**所要時間**: ~ 3 commit batches。並列なしの逐次なら推定 2-3 倍。
**反省**: もっと早く並列に振るべきだった (最初の §1A は逐次でやり始めた)。

## 6. 関連メモリ・規約

- [`CLAUDE.md`](../../CLAUDE.md) — プロジェクト規約 (ファイル粒度・トレーサビリティ 3 層・mathlib 互換命名)
- [`ROADMAP.md`](../../ROADMAP.md) — Phase 計画 + 章節チェックリスト
- オートメモリ `feedback_subagent_orchestration.md` — このファイルへのポインタ (自動ロード用)

このファイルは知見の蓄積場所として進化させていく。新しい知見が出たら追記、古くなった項目は更新 (削除より追記+理由併記が望ましい)。
