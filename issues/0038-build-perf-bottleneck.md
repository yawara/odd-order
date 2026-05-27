---
id: 38
slug: build-perf-bottleneck
title: "フリートのビルド速度ボトルネック調査と巨大 Main.lean 分割"
created: 2026-05-27
---

# フリートのビルド速度ボトルネック調査と巨大 Main.lean 分割

## 背景

複数エージェント並行体制でフリートの velocity が頭打ちな疑い。「Lean コンパイルがボトルネックでは」という仮説を 2026-05-27 に実測で検証した (10 コア / 32GB マシン)。

**性能モデル (1 ファイル dirty, deps キャッシュ済み):**

```
wall ≈ 5s (固定費) + ~2ms/行
```

| 操作 | wall | 備考 |
|---|---|---|
| 真の no-op (`lake build OddOrder`, 全キャッシュ) | ~2s | 54 ファイルの hash 照合は安い。tax ではない |
| 小ファイル再コンパイル (34 行) | 5.2s | ほぼ全部が固定費 |
| 中ファイル (550 行) | 6.1s | |
| 巨大 `Main.lean` (Ch06, 7603 行) | **20.9s** | user 52s → Lean4 async elaboration で内部 ~2.5 コア使用 |

固定費 5s の正体 = mathlib olean の transitive ロード (lean プロセス起動ごとに毎回払う)。

**診断: 「Lean が遅い」一般論ではなく、犯人は具体的に 2 つ。**

1. **モノリシックな `Main.lean`** (最大の効き目)
   - `Ch06_FrobeniusActions/Main.lean` = 7603 行, `Ch07_ThompsonSubgroup/Main.lean` = 7153 行。
   - CLAUDE.md / ROADMAP の「1500-2000 行を超えたら subsection 単位で分割」ルールに対し **4〜5 倍**。
   - エージェントがこの中の 1 行を直すたび毎サイクル ~20s 払う。1500-2000 行に割れば ~8s/サイクルで **inner loop が約 3 倍速**。
   - 代償はクリーンビルドが遅くなる点だけ (固定費 5s × ファイル数)。試行錯誤ループはクリーンビルドをしないので実質ノーコスト。
   - **注意: 依存チェーンに沿って割る** (編集対象が leaf 側に来るように)。さもないと下流が連鎖再ビルドする。`ForwardFromCh02` / `ForwardFromCh03` の既存分割パターンが手本。
   - **過分割もしない**: ~1000 行を切ると固定費 5s が支配的になり総コストが悪化。狙いは 1500-2000 行ピース。

2. **worktree の並列オーバーサブスクリプション**
   - 巨大ファイル 1 本のビルドが既に ~2.5 コア要求。10 コアで 9 agent worktree が同時ビルドすると 9×2.5≈22 コア要求 → 約 2 倍の輻輳 + 9 プロセスが各々 mathlib をメモリにロードし RAM 競合。
   - ① の分割はビルドあたりのワーキングセットを縮めるのでここにも効く。同時ビルド数の上限や 1 エージェントあたりの `-j` を検討する余地。

**問題ではないと判明したもの:**
- **import 依存は浅い** (最大 reverse-dep fan-out = 6)。「base ファイル変更で大量連鎖再ビルド」型ではない。
- whole-lib の hash 照合 (~2s) は tax ではない。inner loop でのビルドコマンド選択 (whole-lib vs targeted) は副次的。

**留保:** コンパイル時間は精密に測れたが、1 サイクルの「LLM が考えてる時間 : ビルド待ち時間」比率はマシンからは測れない。真の split を知るにはエージェントの transcript / タイミングが要る。ただし上の数値は今すぐ確実に潰せる部分。

## やること

- [ ] `Ch06_FrobeniusActions/Main.lean` (7603 行) を依存に沿って 1500-2000 行ピースに分割
- [ ] `Ch07_ThompsonSubgroup/Main.lean` (7153 行) を同様に分割 (※ 別エージェントが編集中・破損状態なら合流後に着手)
- [ ] 分割後に inner-loop レイテンシを再測定し、想定どおり ~20s → ~8s に下がるか確認
- [ ] (任意) 同時ビルド数 / 1 エージェントあたり `-j` の上限ポリシーを検討し worktree 運用ノートに記録
- [ ] (任意) 他の 1500-2000 行超ファイル (Ch04 6073 行, BG S02 4695 行 等) の分割要否を棚卸し

## 完了条件

- Ch06 / Ch07 の `Main.lean` がいずれも 1500-2000 行レンジの複数ファイルに分割され、`lake build OddOrder` が通る。
- 分割が依存チェーンに沿っており、1 ピース編集時に下流が連鎖再ビルドしない (fan-out で確認)。
- inner-loop 再測定で巨大ファイルの ~20s/サイクルが解消されたことを数値で確認。

## 参照

- メモリ: `project_build_perf_bottleneck.md` (性能モデルと診断)
- CLAUDE.md「ファイル粒度」§ / ROADMAP「ファイル粒度とトレーサビリティ」(1500-2000 行分割ルール)
- `notes/meta/worktree_setup.md` (並行作業の worktree 運用)
- 既存分割の手本: `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean`, `.../ForwardFromCh03.lean`
- 対象ファイル: `OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean`, `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean`
