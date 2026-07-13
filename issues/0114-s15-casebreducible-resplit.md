---
id: 114
slug: s15-casebreducible-resplit
title: "S15_CaseBReducibleCoherence 再分割 (0113 後に 1829 行へ再成長)"
created: 2026-07-13
---

# S15_CaseBReducibleCoherence 再分割 (0113 後に 1829 行へ再成長)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 状況

- 2026-07-13 朝: issue 0113 で 1926 行 → prefix-split (S15_SSetMemberRFamily 739 行切り出し、本体 1389 行) — closed
- 同日 tick (merge 688c0922): b の 1017 #50-51 ((9.11) S-instance 4 commits) で **1389 → 1829 行 (+440)**、⚠ 1500 閾値を再超過
- 2000 hard limit まで残 ~170 行 — b の (9.11) 残 residual (`nineElevenAlphaSupportS` / `nineElevenNormBoundS` / `sSet_caseA_nineElevenRefutation` / `sSet_coherent_dade_caseB`) の証明作業でさらに成長見込み

## 方針 (merge_monitor 手順 4 / CLAUDE.md ファイル粒度)

- 分割 owner = hub。b の active frontier ((9.11) residual 群) と衝突しない**凍結境界で prefix-split**
- 候補境界: 0113 と同様、ファイル前半の landed sorry-free クラスタ (S3-coherence `sSet_sThree_coherent_dade` 系や norm-inputs bundle が凍結したタイミングで切り出し)
- trigger: 次に 2000 行に接近した時点、または b の (9.11) 系 landing の節目。b が自主分割してもよい (0113 先例)
