---
id: 2050
slug: appendix-iii-type-models
title: "Peterfalvi Appendix III Definitions 2-3: concrete type models"
created: 2026-07-18
---

# Peterfalvi Appendix III Definitions 2-3: concrete type models

## 背景

Peterfalvi Appendix III Definitions 2--3 (p. 140) の `A(n,φ)` と
`B(n,φ,ε)` を、任意 `Prop` の分類ラベルではなく、Lemma 1(b) の
quadratic central extension への実際の群同値として定義する。

## やること

- [x] characteristic two の有限体自己同型を `F₂`-linear map にする
- [x] type-A quadratic map `a ↦ a φ(a)` を構成する
- [x] type-B quadratic map
      `(a,b) ↦ a φ(a) + ε a φ(b) + b φ(b)` を構成する
- [x] 原文の `ε` 条件から quadratic map の anisotropy を証明する
- [x] finite-field data と quadratic extension への群同値を持つ
      `TypeAData` / `TypeBData` を定義する
- [x] hub と `AxiomsCheck` に配線する

## 完了条件

- Definitions 2--3 の全パラメータと仮定が原文どおり明示される
- type A/B が具体的な群モデルへの同値を持つ
- 新規 `sorry` / `axiom` / opaque-Prop carrier がない
- 対象 leaf と `OddOrder` が build-green

## 参照

- `references/peterfalvi/08.0_pp_139_143_On_Suzuki_2-Groups.mmd`
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/Types.lean`
- issue 2048
