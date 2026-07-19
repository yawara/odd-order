---
id: 9162
slug: basechange-irreducible-intertwiner
title: "Base change: descend an irreducible intertwiner coordinate"
created: 2026-07-19
---

# Base change: descend an irreducible intertwiner coordinate

## 背景

Higman, *Suzuki 2-groups* (1963), Lemma 4 直後の Corollary は、任意の
体拡大 `K/F` について、非同型な既約表現 `V`, `W` の間では
`V` が `K ⊗[F] W` の ground-field-linear invariant subspace として現れない、
という source-neutral な base-change 事実を使う。

既存の `OddOrder.GroupTheory.RepresentationTheory.BaseChange` が忠実性・不変部分空間・
次元の base-change API を所有しているため、Higman 固有の結論から分離してここに置く。
着手前検索では他の open 9000 issue に同 API の claim は無かった。

## やること

- [x] 任意の拡大体の ground-field basis coordinate が base-changed action と可換することを示す
- [x] scalar extension への injective intertwiner から元の既約表現間の同値を構成する
- [x] Higman の source-facing Corollary をこの API と既存 Lemma 4 から導く

## 完了条件

- public な source-neutral theorem は `GroupTheory/RepresentationTheory/BaseChange.lean`、
  文献番号付きの結論は `HigmanLowerCentralSpectrum.lean` に置く
- 任意の `K/F` のまま証明し、`Finite K` / `FiniteDimensional F K` を仮定しない
- 変更した leaves の targeted build が warning-free、new `sorry` / `axiom` / `opaque` なし

## 参照

- `issues/2048-pf-suzuki-lemma5.md`
- `references/higman/pages/suzuki-2-groups-p085.png`
- `references/higman/p84_85_lemmas_3_6.layout.txt`
- `OddOrder/GroupTheory/RepresentationTheory/BaseChange.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanLowerCentralSpectrum.lean`
