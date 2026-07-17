---
id: 9112
slug: prime-complement-residual
title: "Prime-complement residual and Sylow normal-closure API"
created: 2026-07-18
---

# Prime-complement residual and Sylow normal-closure API

## 背景

Peterfalvi Part II Ch. I §3 Lemma 1 の `O^{p′}(G)` は、有限群の Sylow `p`-部分群の
全共役が生成する最小正規部分群。§2 Prop 3 完了 (`149b0e5a`) 後の文書順 frontier。

着手前検索で、`Isaacs.Ch05.OPrime` は `O^p` (p-power index)、
`Subgroup.opPi`/`Isaacs.Ch03.oPiCore` は `O_π` (largest normal π-subgroup) であり別物と確認。
共役 join = normal closure の汎用証明は `Isaacs/Ch09_MoreSubnormality/SubnormalSocle.lean`
に局所配置されているため、再構築せず shared leaf へ移設して consumer を再配線する。

**shared-infra claim owner: lane B (2026-07-18)**

## やること

- [ ] `OddOrder/GroupTheory/PrimeComplementResidual.lean` に共役 join/normal closure の汎用 API を移設する。
- [ ] `primeComplementResidual p G := ⨆ P : Sylow p G, (P : Subgroup G)` を定義し Normal instance を構成する。
- [ ] 任意の `P : Sylow p G` について residual = `normalClosure P`、および正規 p′-index subgroup への最小性を証明する。
- [ ] Peterfalvi §3 Lemma 1 の conditional core から residual と `⟨Q^x⟩` を同定する。

## 完了条件

上記 API が sorry/axiom-free、旧 Ch09 consumer が shared theorem に再配線済み、
Suzuki §3 Lemma 1 conditional core と `OddOrder.AxiomsCheck` が build-green。

## 参照

- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd` lines 159–165
- `notes/peterfalvi/suzuki_ch1.md` item 8
- `OddOrder/Isaacs/Ch09_MoreSubnormality/SubnormalSocle.lean`
- `OddOrder/Isaacs/Ch05_Transfer/Basic.lean` (`OPrime`, semantically distinct)
