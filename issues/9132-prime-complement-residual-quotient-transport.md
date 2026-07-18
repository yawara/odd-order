---
id: 9132
slug: prime-complement-residual-quotient-transport
title: "claim: PrimeComplementResidual — surjective map and quotient transport (Peterfalvi II.I §3 Prop 1(c), lane B)"
created: 2026-07-18
---

# claim: PrimeComplementResidual — surjective map and quotient transport (Peterfalvi II.I §3 Prop 1(c), lane B)

## 背景

Peterfalvi Part II, Ch. I §3 Proposition 1(c) は、`L = C_G(X)` と
`𝒩(L)` に対して
`O^{2′}(L) / Z(O^{2′}(L)) ≃ O^{2′}(L / 𝒩(L))` を使う。
closed issue 9112 で `primeComplementResidual` と Sylow の normal closure は
実装済みだが、全射 hom による map と quotient transport API は未実装。
既存 API と open 9000 claim を着手前検索し、重複が無いことを確認済み。

**shared-infra claim owner: lane B (2026-07-18)**

Target leaf: `OddOrder/GroupTheory/PrimeComplementResidual.lean`.
Consumer: `OddOrder/Peterfalvi/Appendices/Suzuki/CentralizerResidual.lean`.

## やること

- [x] 全射 `f : G →* H` に対し
      `(primeComplementResidual p G).map f = primeComplementResidual p H`
      を証明する。
- [x] `N.subgroupOf (primeComplementResidual p G) = center ...` から
      residual の center quotient と `primeComplementResidual p (G ⧸ N)` の
      `MulEquiv` を構成する。
- [ ] Prop. 1(c) consumer と `OddOrder.AxiomsCheck` を配線する。

## 完了条件

上記 API が `sorry` / 新 `axiom` なしで証明され、shared leaf、Suzuki hub、
`OddOrder.AxiomsCheck` が build-green。

## 参照

- `issues/closed/9112-prime-complement-residual.md`
- `issues/2043-centralizer-trichotomy-c.md`
- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`
- `OddOrder/GroupTheory/PrimeComplementResidual.lean`
