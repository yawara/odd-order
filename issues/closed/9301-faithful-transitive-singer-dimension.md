---
id: 9301
slug: faithful-transitive-singer-dimension
title: "Faithful transitive Singer action dimension equality"
created: 2026-07-19
---

# Faithful transitive Singer action dimension equality

## 背景

Higman Lemma 6 (p. 85) の第一段落で layer action の kernel を比較した後、
`L₁` の faithful irreducible action と `L₂#` 上の faithful transitive action から
`finrank L₁ = finrank L₂` を導く必要がある。これは Higman 固有の commutator
議論ではなく Singer field の一般帰結である。

既存の actor cardinality / generator order / equivariant faithfulness transfer は
`HigmanLowerCentralSpectrum.lean` に置かれているが source-neutral なので、
新しい小粒 leaf は切らず既存 `FrobeniusCoordinates.lean` の Singer cluster へ移す。

## やること

- [x] open 9000 番台 claim を検索し、重複がないことを確認する
- [x] 既存の generic actor API 3件を `OddOrder.RepresentationTheory` へ移す
- [x] faithful irreducible / faithful transitive action の finrank equality を証明する
- [x] Higman consumer を targeted build し、issue 2048 の frontier を更新する

## 完了条件

- source-neutral theorem が `FrobeniusCoordinates.lean` に存在する
- Higman Lemma 6 が `finrank L₁ = finrank L₂` を仮定せず導出できる
- 新規 `sorry` / `axiom` なし、変更 leaf の targeted build が green

## 参照

- `issues/2048-pf-suzuki-lemma5.md`
- `OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanLowerCentralSpectrum.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanLemmaSix.lean`
