---
id: 1035
slug: case-a-sylow-center
title: "Peterfalvi (14.6): trap the ambient Sylow center in R₀"
created: 2026-07-15
---

# Peterfalvi (14.6): trap the ambient Sylow center in R₀

## 背景

Peterfalvi (14.6) case (9.7.a) の中心 argument を形式化する。issue 1034 / commit
`93b737f5` までで、非巡回 `R₀ ∈ Syl_r(U)`、BG Prop. 1.16 の witness
`x ∈ R₀#` with `P ∩ C_G(x) ≠ 1`、および `R₀ ≤ R ∈ Syl_r(K)` の実構成は完了した。
次は原文どおり、(13.2.e) の TI 性から `C_G(x) ≤ S` を得て、`R₀` が `S` の
Sylow `r`-subgroupであることと合わせて `C_R(x) = R₀`、従って `Z(R) ≤ R₀` を示す。

`OrderDetermination.lean` は 1433 行に達したため、1500 行 trigger に従い新しい topic leaf
`S15_CaseASylowCenter.lean` に置く（Hall API が setup 後の `S15_SAndTDefs` にあるため）。

## やること

- [x] `|U|` と `[S:U]` の coprimality を既存の complement/Frobenius data から公開する
- [x] `honestTypeP2ASet` の TI 性を centralizer witness に適用して `C_G(x) ≤ S` を得る
- [x] Sylow 最大性で `C_R(x) = R₀`、従って ambient image の `Z(R) ≤ R₀` を証明する
- [x] case-(9.7.a) certificate から ambient Sylow と中心包含をまとめて構成する
- [x] leaf / AxiomsCheck / full build と axiom audit を通す

## 完了条件

上記 theorem が `sorry` なしで成立し、標準 allowlist 三公理だけに依存すること。

## 実装

`OddOrder/Peterfalvi/S15_CaseASylowCenter.lean` に次を追加した。

- `coprime_card_U_index_S`: `[S : U] = |P| |W₁|` と既存の Frobenius/complement
  coprimality から `Coprime |U| [S : U]`
- `sylow_center_le_U_sylow_of_centralizer_witness`: TI centralizer 包含と Sylow
  最大性を組み合わせ、ambient Sylow image の中心を `R₀` に trap
- `exists_sylow_over_U_with_trapped_center_of_not_isCyclic`: issue 1034 の witness と
  ambient Sylow 構成を上の中心包含まで一括して返す

新 leaf は 197 行で、`sorry` / 新 `axiom` はない。

## 検証

- `lake build OddOrder.Peterfalvi.S15_CaseASylowCenter` — 4130 jobs、成功
- `lake build OddOrder.AxiomsCheck` — 4205 jobs、成功
- `lake build OddOrder` — 4220 jobs、成功
- 三 theorem の依存公理は `propext`, `Classical.choice`, `Quot.sound` の標準三公理のみ
- `git diff --check` — 成功

## 参照

- Peterfalvi (14.6), `references/peterfalvi/*.mmd`
- Coq `coq/theories/PFsection14.v`, `galS` の `sZR_R0`
- issues/0115, 1034, 9087
