---
id: 116
slug: s15-normestimates-relayer
title: "HUB: S15 NormEstimates/CountingLayer の layer-inversion relayer (2035 #29 恒久解、hub architecture)"
created: 2026-07-14
---

# HUB: S15 NormEstimates/CountingLayer の layer-inversion relayer (2035 #29 恒久解、hub architecture)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 問題

S15_SAndT_Setup/{NormEstimates (2), CountingLayer (2)} + S15_SAndTBasic (1) の実 sorry 5 本は、
それぞれの honest producer (本日 landing 分含む: tSide_theta_package_of_not_caseB_core、
(13.2.b) card_Q_eq_qp、dadeHypT 等) が **import DAG 下流** (CaseACoherence → hub →
NormEstimates の層順) にあり、in-place 証明は不可能 (2035 #29 で b が確定済み、
2026-07-14 hub 監査 wf_525303b8 で再確認)。

## 恒久解 (hub architecture task)

S15↔S16 の layer inversion: 下流に落ちた producer 層 (TSideDegrees / CharacterDegreeSupply の
該当宣言) を NormEstimates より上流の位置へ再配置するか、sorry site 側を hypothesis-parameterize
して obtain-site を producer の下流へ移す (2035 #29 option A)。spine-file 再層化は
[[relayer-verify-with-build-not-bfs]] に従い edge ごとに build 検証 (BFS だけで判定しない)。

## トリガー

b の 2035 T-side campaign が (13.4)/(13.3) cluster を close した節目で hub が実施
(campaign 中の再層化は b の hottest file を動かすため衝突大)。

## 参照
- issue 2035 #29 / 0115 裁定 2 註 / merge_monitor tick 41
