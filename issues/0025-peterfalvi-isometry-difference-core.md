---
id: 25
slug: peterfalvi-isometry-difference-core
title: "Peterfalvi Part I: isometry difference-pair の combinatorial core を証明する"
created: 2026-05-25
---

# Peterfalvi Part I: isometry difference-pair の combinatorial core を証明する

## 背景

`issues/0024-peterfalvi-isometry-difference-pair.md` から分割した proof core。
`isometry_difference_pair_structure` の statement と §7 coherence 側 interface は
整ったが、証明本体は以下の 2 層をまだ必要とする。

1. `IrreducibleCharacter G` を finite orthonormal index として使い、second
   orthogonality から class-function basis coefficient を取り出す層。
2. `τ (χ_i - χ_0)` の integer coefficients と norm/inner-product constraints
   だけを使って、全ての差分が同じ符号 `ε • (μ_i - μ_0)` になることを示す
   finite combinatorial induction 層。

この issue は後者の core を独立させ、前者の character-theory API と混ぜずに
証明できる形へ切る。

## やること

- [x] integer coefficient vector 用の小さな structure / predicate を決める。
- [ ] `n = 2` の norm `2` case を証明する。
- [ ] `n = 3` の common component 共有 case を証明する。
- [ ] induction step で uniform sign が崩れる `e₂ + e₃` case を degree 条件で排除する。
- [ ] core lemma を `isometry_difference_pair_structure` に戻して `sorry` を消す。

## 2026-05-26 update

- `SignedIrreducibleDifferenceFamily G n` を追加し、結論側の
  `μ : Fin n → Irr(G)` と uniform sign `ε = ±1` を structure 化した。
- `isometry_difference_pair_structure` の input/output を raw `ClassFunction`
  tuple から `IrreducibleCharacter` index と `SignedIrreducibleDifferenceFamily`
  に揃えた。
- `SignedIrreducibleDifferenceFamily.classFunction_injective`,
  `classFunction_ne`, `classFunction_irreducible` を追加した。
- §7 の `CharacterDifferenceImage` も `mu`, `nu` を raw `ClassFunction` ではなく
  `IrreducibleCharacter G` として持つ形に揃えた。
- `SignedIrreducibleDifferenceFamily.difference` と `signedDifference` を追加し、
  基準成分 `μ_i - μ_0`、符号付き差分、`difference_ne_zero`,
  `sign_ne_zero`, `sign_mul_self` を名前付き API にした。
- proof core は引き続き `n = 2`, `n = 3`, induction step の finite
  combinatorial argument。

## 完了条件

- `OddOrder.RepresentationTheory.isometry_difference_pair_structure` の proof core が
  独立 lemma として statement 化される、または同 theorem から `sorry` が消える。
- `lake build OddOrder.GroupTheory.RepresentationTheory.IsometryDifferencePair` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0024-peterfalvi-isometry-difference-pair.md`
- depends on: `issues/closed/0021-peterfalvi-second-orthogonality.md`
- depends on: `issues/0027-peterfalvi-column-orthogonality-core.md`
- `OddOrder/GroupTheory/RepresentationTheory/IsometryDifferencePair.lean`
- `OddOrder/GroupTheory/RepresentationTheory/IrrIndexing.lean`
- `OddOrder/GroupTheory/RepresentationTheory/SecondOrthogonality.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
- `notes/peterfalvi/s07_coherence.md`
