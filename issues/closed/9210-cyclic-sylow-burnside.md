# 9210 — 巡回 Sylow の Burnside 前提を最小素数条件から一般化

**claim**: lane a (9200 band) / **状態**: landing 済 (2026-07-26)

## 目的

`OddOrder/GroupTheory/CyclicSylowBurnside.lean` (新 leaf, `OddOrder.lean` 配線済):

* `normalizer_le_centralizer_of_coprime_totient` — `P` が巡回 Sylow `p`-部分群で
  `gcd(|G|, φ(|P|)) = 1` なら `N_G(P) ≤ C_G(P)`
* `exists_normal_complement_of_isCyclic_sylow` — 上に Burnside を適用した正規 `p`-補群
  (`|K| · |P| = |G|`, `p ∤ |K|`, `K ⊴ G`)

## 既存との関係 (着手前検索の結果)

mathlib `Mathlib/GroupTheory/Transfer.lean` の `IsCyclic.normalizer_le_centralizer` は
**`p` が `|G|` の最小素因数** (`(Nat.card G).minFac = p`) を要求する。実際に効いているのは
`N_G(P)/C_G(P) ↪ Aut(P)` から出る「`|N_G(P) : C_G(P)|` が `φ(|P|)` と `|G|` の両方を割る」
だけなので、そこを直接仮定にした一般形を置いた。

**どちらも他方の特殊化ではない**: 最小素数の場合は `φ(p^k) = p^{k-1}(p-1)` の `p`-部分を
別扱いする必要がある (mathlib 版はそれを `relIndex` の `p`-可除性でやっている) ので、
`gcd(|G|, φ(|P|)) = 1` は成り立たない。逆に本 leaf の形は `p` が最小でなくても使える。

## 消費点

Isaacs Problem 5C.7 (issue 1055): `|G| = 3^a · 5 · 11` ⇒ Sylow-3 が正規。
`p = 5` (`φ(5) = 4`) と `p = 11` (`φ(11) = 10`) の 2 段で使う。どちらも最小素因数ではない
(最小は 3) ので mathlib 版は使えない。
