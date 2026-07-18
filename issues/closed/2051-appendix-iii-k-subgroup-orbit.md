---
id: 2051
slug: appendix-iii-k-subgroup-orbit
title: "Peterfalvi I.3 Lemma 5: fixed-coset free action"
created: 2026-07-18
---

# Peterfalvi I.3 Lemma 5: fixed-coset free action

## 背景

Peterfalvi Part II, Ch. I §3 Lemma 5 (p. 107) の、`W` が位数 `q²` の
`K`-subgroup を自由に置換するための固定点排除を形式化する。原文の
「square fiber が q 個」だけでは一般の置換作用に固定点は従わないため、
実際に必要な invariant `Q₀`-coset と coprime fixed-point lifting を明示する。

## やること

- [x] 非自明元が一点を固定したとき cyclic subgroup 全体へ制限する
- [x] odd order と `|Q₀| = 2^n` から coprimality を証明する
- [x] invariant normal coset から固定代表元を持ち上げる
- [x] `C_Q(w) ≤ Q₀` と代表元が `Q₀` 外であることから矛盾を得る
- [x] 自由作用から作用群の位数整除を導く
- [x] hub と `AxiomsCheck` に配線する

## 完了条件

- 原文の省略を hidden cardinality argument なしで補完する
- 一般補題が新規 `sorry` / `axiom` / opaque carrier なしで成立する
- 対象 leaf と `OddOrder.AxiomsCheck` が build-green

## 参照

- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/KSubgroupOrbit.lean`
- issue 2048
