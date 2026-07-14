---
id: 9098
slug: casea-block-scalar-divisibility
title: "SHARED: block-scalar ratio embedding cardinal divisibility for Peterfalvi (13.13)"
created: 2026-07-14
---

# SHARED: block-scalar ratio embedding cardinal divisibility for Peterfalvi (13.13)

## 背景

Peterfalvi (13.13) の case (9.7.a) は、block-scalar ratio embedding から
`u ∣ ((p - 1) / 2)^(q - 1)` を得て解析的不等式と組み合わせる。既存の issue 9000
engine `card_le_pow_of_block_scalars` は同じ injective ratio map を構成済みだが、公開結論は
cardinality の `≤` のみで、odd part へ降ろすために必要な有限群位数の divisibility を失っている。

**CLAIM (lane a, 2026-07-14)**: ratio map を group homomorphism として束ね、injectivity と
Lagrange から cardinal divisibility を公開する。他レーンは同じ ratio embedding を再構築しない。

## やること

- [ ] `SemilinearImprimitiveBound` に `card_dvd_pow_of_block_scalars` を追加する。
- [ ] `S11_ImprimitiveUBound` で `caseA.u ∣ (p - 1)^(q - 1)` を構成する。
- [ ] odd-order hypothesis により 2-primary factor を除き、
      `u ∣ ((p - 1) / 2)^(q - 1)` を公開する。
- [ ] `OrderDetermination.caseA_parameters` を honest `CliffordCaseAData` から証明する。

## 完了条件

上記 API と (13.13) が sorry-free で target build / AxiomsCheck / full build を通り、
opaque `caseA_for_S : Prop` carrier が実 certificate に置換されること。

## 参照

- `issues/0115-lane-redesign-2026-07-14.md`
- `coq/theories/PFsection13.v`, `FTtypeP_Ind_Fitting_nonGalois_facts`
