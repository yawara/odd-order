---
id: 9309
slug: central-elementary-extension-classification
title: "Classify central elementary extensions by the square map"
created: 2026-07-20
---

# Classify central elementary extensions by the square map

## 背景

Higman, *Suzuki 2-groups*, Lemma 11 (pp. 88--89) は、中心的な
elementary-abelian 核と商を持つ class-two 群について、平方写像の有限体座標を
`a ↦ a * θ(a)` と同定した後、その群を具体的な `A(n, θ)` と同型化する。
既存の `QuadraticExtensions.lean` は quadratic map から中心拡大を構成する向きだけを
持ち、actual group の平方写像からその concrete model への `MulEquiv` を構成する
逆向きの分類定理がない。

この bridge は Higman Lemma 11 と Peterfalvi Appendix III の双方で再利用されるため
shared infra として claim する。依存方向は `Higman → Peterfalvi` にせず、generic な
中心拡大の normal-form / uniqueness を `OddOrder/GroupTheory/**` に置き、
Peterfalvi の `TypeAModel` 側は adapter とする。

## やること

- [x] 既存の `GroupExtension` / section / cocycle API を調査し、重複実装を避ける
- [x] elementary-abelian 中心核と商、および ordered quotient basis から actual group の
      一意な normal form を構成する
- [x] 平方写像の polarization が commutator pairing を決定することを証明する
- [ ] 同じ平方 quadratic map を持つ actual extension と concrete twisted product の
      `MulEquiv` を構成する
- [ ] Peterfalvi `QuadraticExtension` / `TypeAModel` への adapter を接続する

## 進捗 (2026-07-20)

shared generic 層を `OddOrder/GroupTheory/CentralElementaryExtension.lean` に実装した。
公開 API `GroupExtension.equivOfCommonSquareMap` は、共通の平方座標を持つ二つの
actual central elementary extension から `S.Equiv T` を構成する。順序付き基底の
collected word、kernel coordinate、一意な multiplication law は実構成であり、
factor set や multiplication law を仮定として受け取らない。

- `lake build OddOrder.GroupTheory.CentralElementaryExtension`
  - `Build completed successfully (1777 jobs).`
- 800 行、警告なし、新規 `sorry` / `axiom` なし
- 残りは `QuadraticExtension` の canonical `GroupExtension` 表現を取り出す adapter と、
  Higman Lemma 11 で得る square-map formula の接続

## 完了条件

- 新しい theorem が free carrier / posited multiplication law を要求せず、actual group と
  actual kernel / quotient から同型を構成する
- 新規 `sorry` / `axiom` なし
- shared leaf と Peterfalvi adapter の target build が通る
- Higman Lemma 11 が square-map normal form から `TypeAData` を構成する際に利用できる

## 参照

- `issues/2048-pf-suzuki-lemma5.md`
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/QuadraticExtensions.lean`
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/Types.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanFiniteFieldTrace.lean`
- `references/higman/pages/suzuki-2-groups-p089.png`
