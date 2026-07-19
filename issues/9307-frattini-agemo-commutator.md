---
id: 9307
slug: frattini-agemo-commutator
title: "finite 2-group Frattini/Agemo commutator bridge"
created: 2026-07-20
---

# finite 2-group Frattini/Agemo commutator bridge

## 背景

Higman, *Suzuki 2-groups*, Lemma 9 (p. 87) の後半で、
`[P,A] ≤ A²` から `[Φ(P),A] ≤ A⁴` を導く。平方元に対する交換子計算と
Agemo の生成閉包への延長は Higman 固有でないため、既存の汎用 power-layer
propagation とともに `OddOrder/GroupTheory/OmegaSubgroup.lean` に置く。

有限 `2`-group の `Φ(P) = Agemo P 2 1` は BG 層の既存定理に依存するため、
この shared leaf へ逆 import せず Higman consumer 側で接続する。

## やること

- [ ] 既存の汎用 `commutator_agemo_one_map_le_agemo_two_map` を GroupTheory へ移す
- [ ] 平方元および `Agemo P 2 1` に対する交換子評価を追加する
- [ ] Higman Lemma 9 consumer を新 API に接続する

## 完了条件

- 新規 `sorry` / `axiom` なし
- GroupTheory leaf と Higman consumer の対象 build が green
- GroupTheory から BG/Higman への逆依存なし

## 参照

- `issues/2048-pf-suzuki-lemma5.md`
- `issues/closed/9306-commutator-le-agemo-two-one.md`
- `references/higman/pages/suzuki-2-groups-p087.png`
