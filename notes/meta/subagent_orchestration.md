# サブエージェント運用方針

**スコープ**: `odd-order` プロジェクト (Feit-Thompson 形式化, AI エージェント駆動) における
サブエージェント並列実行の判断基準・プロンプト品質・トラブル時の挙動。

**初版**: 2026-05-21 (Ch.1 §1A/§1C/§1D に並列エージェントを投入したセッション後の反省を元に)。
**改訂**: 2026-05-21 後半 (Ch.1 §1E 長大証明での 2 連敗を受けて TL;DR を追加)。

## TL;DR — 改訂 heuristics

**デフォルトは手動**。次のいずれかを満たすときだけ agent を起動する:

1. **独立並列タスクが同時に来ている** — 並列にしないと時短にならない場合。
2. **read-only の悉皆調査** — Explore agent で mathlib grep / ファイル横断調査。
3. **30 分以上手動でかかる、かつ入出力が明確な単一タスク** — 概ね 50-150 行の中規模補題で
   API 名がすでに分かっているもの。

**投げない**:
- **長大証明 (200+ 行) 単独委譲**: Wave 5 で 2 連敗 (Thm 1.32, Thm 1.36)。
  API 名一致が 20+ 箇所必要になり、トークン予算が尽きる前に決着しない。
  どうしても agent を使うならハイブリッド (§ 6.3) — 骨格を取り出して手で splice。
- **アーキテクチャ判断 / 名前空間設計**: 会話コンテキストが本質。
- **5 分以下の軽い follow-up**: 起動コストが利得を上回る。

詳細な議論・データ・サイズ別 heuristics 表は § 6 (Wave 4-6 で見えた失敗パターン) を参照。

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

## 6. Wave 4-6 で見えた長大証明での失敗パターン (2026-05-21 後半)

§1E Thm 1.32 / 1.33 / 1.36 (200-300 行クラスの長い証明) を agent に投げた経験から、
**「短い独立補題は速いが、長い証明は agent 単独で完走しない」** ことが明確に出た。

### 6.1 戦績データ

| Wave | 対象 | 結果 | コスト | 採用 |
|---|---|---|---|---|
| 4-A | Thm 1.36 (~250 行) | breadcrumb のみ (proof 未完) | 標準 | 不採用 |
| 4-B | Thm 1.31 一般 (~100 行) | ✅ build green | 標準 | 採用 |
| 4-C | Thm 1.16 (~190 行) | ✅ build green | 標準 | 採用 |
| 4-D | Thm 1.32 弱形 | 仮定追加で signature 違い | 標準 | 不採用 |
| 5-X | Thm 1.36 (~940 行で再挑戦) | build red 22 件で力尽き | 1087s / 104 tool calls | 不採用 |
| 5-Y | Thm 1.32 完全 + Thm 1.33 | 4 sorry, k=3 ケース未完 | 1391s / 114 tool calls | 部分構造のみ手動で salvage |

### 6.2 観察された失敗様式

1. **API name death spiral**: 長い証明 (250+ 行) では mathlib API 名一致が 20-30 ヶ所必要になり、
   各 fix で 1-2 ツールコール消費 → トークン予算が尽きる前に決着がつかない。
   `Subgroup.card_dvd_card_of_le` (実際は `Subgroup.card_dvd_of_le`)、
   `Nat.Coprime.pow_right_iff` (実際は `Nat.Coprime.pow_right`)、
   `Nat.dvd_prime_pow (n := 3)` (実際は `(m := 3)`)、
   `Subgroup.card_lt_card` (存在しない)、
   `Subgroup.card_mul_eq_card_mul_div` (存在しない) など。
2. **Stale base 問題**: `isolation: "worktree"` で agent を切ると、main の最新 commit 以前から
   分岐するため、**直前の wave で main に取り込んだ補題が agent からは見えない**。
   Wave 5-X は Wave 4-C の Thm 1.16 を使うつもりで投げたが、worktree の base は
   c8cfd41 (Thm 1.16 取り込み前) で、結局 Thm 1.16 を使わない別アプローチに走った。
3. **部分結果の信頼性**: `agent_result.success = true` でも sorry が混入していたり、
   theorem signature が当初仕様と違っていたりする。**必ず手で確認**。

### 6.3 ハイブリッド方式 — 速かったのはコレ

Thm 1.32 のケース:
- Wave 5-Y agent: 4 sorry + 5 API mismatch を残して停止 (1391 秒)
- 手動 salvage: agent の骨格を main に splice → ビルド → 5 エラーを 5 回の build cycle で fix
- **所要時間**: 約 10 分 (Edit + build × 5)

→ **agent が提示した structural skeleton を 100% 信頼するのではなく、
  「設計図」として受け取って手で完成させる**ハイブリッドが、純粋 agent 委譲より速い。

### 6.4 更新された heuristics

| サイズ | 推奨アプローチ |
|---|---|
| ~20 行 | 手動 (agent 起動コスト > 利得) |
| 20-80 行, mathlib 直系 | agent 単独で worktree |
| 80-200 行, 中規模新証明 | agent 単独, ただしプロンプトで具体 API 名を 5-10 個明示 |
| 200-400 行, 複雑な structure | **ハイブリッド**: agent で骨格 → 手で splice + 細部修正 |
| 400+ 行, 長大複合証明 | 補題分割を先にやってから個別 agent |

### 6.5 並列 wave の依存関係に注意

Wave 4-B (Thm 1.31 一般) と Wave 4-C (Thm 1.16) は **独立** に走らせたが、
**Thm 1.36 は Thm 1.16 に依存する** ため Wave 4-A は本来 Wave 4-C 後に走らせるべきだった。
並列発注時は依存グラフを 1 度書き出す。次回からは:
1. 依存無しグループを 1 batch
2. それを main に取り込んでから依存ありグループを別 batch

## 7. 関連メモリ・規約

- [`CLAUDE.md`](../../CLAUDE.md) — プロジェクト規約 (ファイル粒度・トレーサビリティ 3 層・mathlib 互換命名)
- [`ROADMAP.md`](../../ROADMAP.md) — Phase 計画 + 章節チェックリスト
- [`lean_formalization_tips.md`](lean_formalization_tips.md) — mathlib API gotcha 集 (§ 6 で言及した API 名の正解一覧はここ)
- オートメモリ `feedback_subagent_orchestration.md` — このファイルへのポインタ (自動ロード用)

このファイルは知見の蓄積場所として進化させていく。新しい知見が出たら追記、古くなった項目は更新 (削除より追記+理由併記が望ましい)。
