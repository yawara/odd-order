---
id: 97
slug: isaacs-ch04-commutators-split
title: "Isaacs Ch04_Commutators/Main.lean 分割 (6636 行, size-watch)"
created: 2026-07-07
---

# Isaacs Ch04_Commutators/Main.lean 分割 (6636 行, size-watch)

## 背景

merge_monitor step 4 サイズ watch で検出。`OddOrder/Isaacs/Ch04_Commutators/Main.lean`
が **6636 行** (2026-07-07 lane d merge `2826cac1` で +350、9061-9067 の commutator/
Fitting/Frattini action 補題群を追記)。粒度規約の 1,500 行閾値を大幅超過。

**性質**: Isaacs Ch04 基盤 finite-group-theory ライブラリ (shared foundation、全 lane 加算可)。
active frontier ではないが、**lane d (codex shared-infra) が継続的に追記**しているため、
分割すれば d の今後の追記 churn と merge conflict リスクが下がる。優先度は中 (build は green、
active spine には無関係) だが、size watch protocol どおり起票。

## やること

- [ ] Main.lean の宣言クラスタを主題別に確認 (commutator API / Fitting self-centralizing・
      fixed-point action / Hall action / Frattini power-closure・elementary-abelian 等)
- [ ] 凍結境界 (lane d の active frontier と衝突しない末尾) で hub prefix-split
      — 先頭 K 宣言を topic leaf へ、残りが import
- [ ] 分割後も root closure 到達可能 (OddOrder.lean import) を維持
- [ ] full build green 確認

## 完了条件

Main.lean が topic-coherent な複数ファイルに分割され、各ファイルが概ね 1,500 行以下。
full build green + AxiomsCheck OK。

## 参照

- 分割 owner = hub (merge_monitor.md step 4)
- 同型の既存 split issue: 0068-0079, 0084, 0085, 0094, 0095 (Pf/BG frontier 側)
- 直近追記 commit: 2826cac1 (Merge 'd', 9061-9067)

## 完了 (2026-07-09)

Main.lean を dir 化分割 (commit 57309d7f)。CommutatorBasics/ThreeSubgroupsCoprime/BaerTrick/ChainNilpotent の 4 leaves。
