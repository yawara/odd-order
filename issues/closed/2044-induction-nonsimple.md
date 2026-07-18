---
id: 2044
slug: induction-nonsimple
title: "Peterfalvi I.3 Proposition 2 non-simple induction"
created: 2026-07-18
---

# Peterfalvi I.3 Proposition 2 non-simple induction

## 背景

Peterfalvi Part II, Ch. I §3 Proposition 2 の非単純群帰納を形式化する。
原文どおり、任意の非自明正規部分群が全 involution を含むことから
`L = ⟨I⟩` を構成し、`Q ≤ L`、`G = LD`、`[G : L]` が奇数であることを経て
`L` への帰納仮定を持ち上げる。

## やること

- [x] `O_{2′}(G) = 1` と Cauchy を用いて全 involution が非自明正規部分群に入ることを示す
- [x] 非単純性から `L = ⟨I⟩` が非自明な proper normal subgroup であることを示す
- [x] 原文の `k = t(tk)` と `C_Q(k) = 1` により `Q ≤ L` を示す
- [x] `L` 上に仮説を制限し、2-transitivity と A1--A3 を検証する
- [x] `G = LD` と `[G : L]` の奇数性を示す
- [x] `L` への帰納結果を `G` の Theorem A conclusion へ持ち上げる
- [x] `AxiomsCheck` と全体ビルドを通す

## 完了条件

Proposition 2 と同じ仮定から `Nonempty (TheoremAConclusion G Omega)` を
新しい axiom・opaque carrier・sorry なしで証明し、`lake build OddOrder` が成功すること。

## 参照

- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`
- `notes/peterfalvi/suzuki_ch1.md`
- `OddOrder/Peterfalvi/Appendices/Suzuki/InductionNonSimple.lean`
