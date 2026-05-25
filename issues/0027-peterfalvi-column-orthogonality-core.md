---
id: 27
slug: peterfalvi-column-orthogonality-core
title: "Peterfalvi Part I: column orthogonality cases の proof core を証明する"
created: 2026-05-26
---

# Peterfalvi Part I: column orthogonality cases の proof core を証明する

## 背景

`issues/0021-peterfalvi-second-orthogonality.md` から分割した proof core。
public API の `column_orthogonality_diag`, `column_orthogonality_conj`,
`column_orthogonality_not_conj` は `column_orthogonality_cases` から導く形に整理済み。

残る hard proof は、character table の invertibility / matrix algebra から
`column_orthogonality_cases` を証明する部分。
これは Brauer permutation lemma と Peterfalvi §3 (1.2) の共通依存になる。

## やること

- [ ] `IrreducibleCharacter G` と `ConjClasses G` の finite cardinal/indexing をそろえる。
- [ ] first orthogonality から character-table matrix の row orthogonality を statement 化する。
- [ ] square/invertible matrix argument で column orthogonality を導く。
- [ ] conjugate/non-conjugate cases を `column_orthogonality_cases` に戻して `sorry` を消す。

## 完了条件

- `OddOrder.RepresentationTheory.column_orthogonality_cases` から `sorry` が消える。
- `lake build OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0021-peterfalvi-second-orthogonality.md`
- downstream: `issues/0022-peterfalvi-brauer-permutation.md`
- `OddOrder/GroupTheory/RepresentationTheory/IrrIndexing.lean`
- `OddOrder/GroupTheory/RepresentationTheory/SecondOrthogonality.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
