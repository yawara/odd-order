---
id: 9101
slug: casea-sylow-noncyclic
title: "shared-infra claim (lane a): full odd block-scalar embedding forces noncyclic Sylow subgroups"
created: 2026-07-14
---

# shared-infra claim (lane a): full odd block-scalar embedding forces noncyclic Sylow subgroups

## 背景

Peterfalvi (14.6) の case (9.7.a) 排除では、(13.13) の極限値
`q = 3`, `|U| = ((p - 1) / 2)^2` と、(9.7.a) の忠実な 2 座標 block-scalar
ratio 埋め込みから、`r ∣ (p - 1) / 2` に対する Sylow `r`-部分群が非巡回であることを
取り出す。既存の `caseA_exists_blockScalarRatioEmbedding` は埋め込みを保持しているが、
この Sylow bridge は未実装。BG Prop 1.16 の共役作用特殊化は既に実装済みなので再構築しない。

9078 の semilinear field-model (case (9.7.b)) とは別の case-(a) structural consumer。
shared representation-theory leaf に一般補題として置き、S 側 (14.6) が instantiate する。

## やること

- [x] 奇数位数の有限群 `U` が `Fin 2 → (ZMod p)ˣ` へ忠実に埋め込まれ、
      `|U| = ((p - 1) / 2)^2` なら、全元の `((p - 1) / 2)` 乗が 1 であることを証明する。
- [x] `r ∣ (p - 1) / 2` に対する任意の `Sylow r U` が非巡回であることを証明する。
- [x] leaf build / AxiomsCheck / full build を通し、新 axiom・sorry が無いことを確認する。

## 実施結果

- 新 leaf `BlockScalarSylow.lean` に sharp-square 一般定理と odd block-scalar 特殊化を実装。
- leaf build 2144 jobs、AxiomsCheck 4204 jobs、full build 4219 jobs green。
- 2 定理とも allowlist 3 公理のみ。新 `axiom`・新 `sorry` なし。

## 完了条件

上記 2 定理が `OddOrder/GroupTheory/RepresentationTheory/SemilinearImprimitiveBound.lean`
（または topic-coherent sibling）に sorry-free で入り、Peterfalvi (14.6) から Sylow witness を
直接 cite できる。AxiomsCheck と full build が green。

## 参照

- Peterfalvi §14, (14.6); `references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd`
- Coq `coq/theories/PFsection14.v`, `galS` (`FTtypeP_nonGalois_facts` 以降)
- `OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean`
- `OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean` (`caseA_parameters`)
- `OddOrder/BG/Ch2_Uniqueness/S07_Theorem74.lean`
- issues 0115, 9077, 9078
