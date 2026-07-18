---
id: 2047
slug: order-three-psl-subgroup
title: "Peterfalvi I.3 Lemma 4 order-three PSL subgroup"
created: 2026-07-19
---

# Peterfalvi I.3 Lemma 4 order-three PSL subgroup

## 背景

Peterfalvi Part II, Ch. I §3 Lemma 4 (p. 107) を原文強度で形式化する。
`orderOf (s * t) = 3` と `V ≠ 1` から、`Q₀`, `K`, `t` が生成する
部分群の Bruhat 分解を構成し、Theorem A の帰納仮説を適用して
`PSL(2, q)` と同型であることを示す。

原著の `tQ₀t ⊂ Q₀KtQ₀` には sharp が脱落している。`1 ∈ Q₀` では
左辺に `1` が入るため literal には偽であり、直前の計算が扱うのも
`Q₀# = s^K` だけである。Lean では非単位元を大セルへ、単位元を
小セルへ送り、正しい包含 `tQ₀t ⊆ Q₀K ∪ Q₀KtQ₀` を証明する。

## やること

- [x] 位数 3 から braid relation `tst = sts` を導く
- [x] `tQ₀#t ⊆ Q₀KtQ₀` と単位元を含む二セル包含を証明する
- [x] `⟨Q₀,K,t⟩` の carrier が `Q₀K ∪ Q₀KtQ₀` であることを証明する
- [x] 生成部分群の軌道上に (A1)–(A3) の `Hypothesis` を実構成する
- [x] `V ≠ 1` から生成部分群が真部分群であることを示す
- [x] Theorem A の帰納結果を生成部分群全体へ持ち上げる
- [x] Suzuki / PSU 分岐を `Q₀` の可換性で除外し、PSL 同型を得る
- [x] hub / AxiomsCheck / survey / handoff を更新する

## 完了条件

- [x] Lemma 4 の結論が有限体を existential にした `PSL(2,q)` 同型として証明済み
- [x] 原著の sharp 脱落を docstring に明記し、偽の literal statement を導入していない
- [x] 新 `sorry` / `axiom` / `opaque` なし
- [x] leaf / Suzuki hub / AxiomsCheck / `lake build OddOrder` が green

## 完了記録 (2026-07-19)

- 実装は `OrderThreePSL.lean` と `OrderThreePSLInduction.lean` の 2 leaf。
  前者が braid relation、Bruhat 二セルの閉性、生成部分群の carrier 等式を
  証明し、後者が軌道上の faithful doubly transitive action と (A1)--(A3) を
  実構成して Theorem A の帰納分類を適用する。
- 独立原文監査で p. 107 の計算・部分群化・真部分群性・誘導作用・帰納適用を
  突合した。原著の `tQ₀t ⊂ Q₀KtQ₀` は sharp 脱落であり、Lean は正しい
  `tQ₀#t ⊆ Q₀KtQ₀` と単位元を小セルへ送る包含を証明している。他の不整合はない。
- 生成部分群の作用の faithfulness は仮定していない。kernel 元を `K` に落とし、
  distinguished-involution の軌道点を固定することから `s ∈ Q₀` を中心化させ、
  非自明な `k ∈ K` に対する `Q ∩ C_G(k) = 1` で消す。`Q₀` の regularity
  から二重推移性を得た。
- `V ≠ 1` から生成部分群が真であることを証明し、帰納結果の Suzuki / PSU
  分岐を `Q₀` の可換性で除外。有限標数 2 体 `F`、`|F| = |Q₀|`、および
  `⟨Q₀,K,t⟩ ≃ PSL(2,F)` を得た。
- 単一の pre-commit `main` 同期後、`lake build OddOrder` は 4453 jobs で
  exit 0。`OrderThreePSL`、`OrderThreePSLInduction`、Suzuki hub、
  `OddOrder.AxiomsCheck`、`OddOrder` がすべて build され、axiom checks も OK。

## 参照

- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`
- `notes/peterfalvi/suzuki_ch1.md`
- `OddOrder/Peterfalvi/Appendices/Suzuki/InductionNonSimple.lean`
- `OddOrder/Peterfalvi/Appendices/Suzuki/CentralizerInductionBridge.lean`
