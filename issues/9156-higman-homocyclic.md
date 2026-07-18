---
id: 9156
slug: higman-homocyclic
title: "CLAIM: Higman homocyclic and invariant power-layer theorem"
created: 2026-07-19
---

# CLAIM: Higman homocyclic and invariant power-layer theorem

## 背景

Higman, *Suzuki 2-groups*, Lemma 1 (p. 83) の genuine gap。有限可換
`2`-group `A` の involution 上で automorphism group が推移的に作用するとき、
`A` は同じ位数の cyclic groups の直積であり、invariant subgroups は power
filtration `A^(2^s)` の項に限る。Peterfalvi Appendix III Higman theorem (a),
(d)--(e) の中心・Frattini・two-summand 構成に必要。

着手前検索では有限可換群の ZMod 分解、`Omega` / `Agemo`、最下層の
transitivity-to-irreducibility は既存。一方、involution height から cyclic
factor の指数を揃える bridge と全 invariant subgroup の分類は未実装。
可換群で `Agemo = powMonoidHom.range` の定理は BG §12 の downstream leaf に
局所配置されているため shared leaf へ移設して再利用する。

**shared-infra claim owner: lane B (2026-07-19)**

## やること

- [x] 可換群で `Agemo H p n = (powMonoidHom (p^n)).range` と membership API を
      `OddOrder/GroupTheory/OmegaSubgroup.lean` に移設し、旧 BG consumer を再配線する
- [ ] actor の推移性が power-map range membership (= involution height) を保存する
      ことを定式化する
- [ ] 有限可換 `2`-group の ZMod 分解で全 cyclic factor が同じ位数 `2^e` を
      持つことを証明する
- [ ] successive power layers の irreducibility から、全 invariant subgroup が
      `Agemo A 2 s` に一致することを証明する
- [ ] Peterfalvi Appendix III leaf に Higman Lemma 1 の source-facing theorem を接続する

## 完了条件

Higman Lemma 1 の homogeneous decomposition と invariant-subgroup classification
が新規 `sorry` / `axiom` / opaque carrier なしで証明され、変更した shared leaf と
Peterfalvi leaf が build-green。root / AxiomsCheck の統合 gate は main / hub 側で実行する。

## 参照

- `references/higman/suzuki-2-groups.pdftotext.txt` lines 218--229
- `references/higman/suzuki-2-groups.pdf` pp. 83--84
- `OddOrder/GroupTheory/OmegaSubgroup.lean`
- `OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1212b.lean`
- `OddOrder/GroupTheory/ElementaryAbelian.lean`
- `Mathlib/GroupTheory/FiniteAbelian/Basic.lean`
