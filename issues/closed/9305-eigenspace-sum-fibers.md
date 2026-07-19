---
id: 9305
slug: eigenspace-sum-fibers
title: "有限固有ベクトル和を固有値 fiber ごとに分離する"
created: 2026-07-20
---

# 有限固有ベクトル和を固有値 fiber ごとに分離する

## 背景

Higman Lemma 6 (p. 86) の triple-bracket sum を weight 成分ごとに分離するには、
各項が固有ベクトル方程式を満たし全和がゼロなら、指定固有値を持つ項だけの和も
ゼロになる汎用補題が必要である。固有空間族の独立性だけに依存するため、Higman
固有の補題にせず representation-theory infra として実装する。

## やること

- [x] `Module.End.eigenspaces_iSupIndep` から有限和の weight fiber 分離を証明する
- [x] 公開定理を axiom audit に登録する

## 完了条件

- 新規 `sorry` / `axiom` なし
- `OddOrder.GroupTheory.RepresentationTheory.EigenspaceUnderCyclicAction` が build-green
- issue を `issues/closed/` へ移す

## 参照

- `issues/2048-pf-suzuki-lemma5.md`
- `OddOrder/GroupTheory/RepresentationTheory/EigenspaceUnderCyclicAction.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanLemmaSix.lean`
