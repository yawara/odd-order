---
id: 9157
slug: fitting-quotient-nilpotent-heredity
title: "shared infra: 「X/F(X) 冪零」の部分群・商への遺伝 (BG Thm 6.4 の transport に必要)"
created: 2026-07-19
---

# shared infra: 「X/F(X) 冪零」の部分群・商への遺伝 (BG Thm 6.4 の transport に必要)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## claim (lane c, 2026-07-19)

**着手前 scan 済**: open 9000 issue (9109/9111/9130/9132/9133/9156) に該当なし。
`grep` で「`X/F(X)` 冪零」の部分群・商遺伝に相当する既存定理は見つからず。

## 何が要るか

BG Thm 6.4 (issue 3026) の帰納法は、仮説
「`G₀/F(G₀)` と `(G/G₀)/F(G/G₀)` が冪零」を **部分群 `L ⊔ H`** と **商 `G ⧸ N`** の両方へ
transport する。そのために要る 2 つの汎用 Fitting 補題:

1. **部分群遺伝**: `X/F(X)` 冪零 かつ `Y ≤ X` ⟹ `Y/F(Y)` 冪零。
2. **商遺伝**: `X/F(X)` 冪零 かつ `N ⊴ X` ⟹ `(X/N)/F(X/N)` 冪零。

いずれも §6 に閉じない汎用事実で、**repo に home が無い**。BG Thm 6.4 以外にも再利用が見込める
(Fitting 商の冪零性は局所解析で頻出) ため、shared infra として claim する。

## 調査の出発点 (着手者へ)

- **`X/F(X)` 冪零 ⟺ nilpotent residual `X^∞ ≤ F(X)`** なので、既存の
  `OddOrder/Isaacs/Ch09_MoreSubnormality/NilpotentResidual.lean` の機構が使える可能性が高い。
  **まず同 file を通読**すること (grep でなく Read; CLAUDE.md の mathlib API 探索方針 layer 2)。
  `fitting_le_normalizer_nilpotentResidual` (:302) など既存 API の確認から。
- `Ch01.fitting` (`Isaacs/Ch01_Sylow/Basic.lean:764`) が subtype-level の Fitting。
  `Ch01.nilpotent_normal_le_fitting` (:963) が「冪零 normal ⊆ F」。
- ⚠ `fittingInAmbient` は Ch4/S15 レベルの**別概念**で §6 では層が違う (issue 3026 の
  Step-0 inventory 参照)。取り違えないこと。
- ⚠ 部分群遺伝は一般には**自明でない** (`F(Y) ⊉ F(X) ⊓ Y` が起こりうる)。着手時に
  まず**数学的に正しいか**を確認し、必要なら追加仮説 (subnormal? normal?) を洗い出すこと。
  BG Thm 6.4 の証明が実際に要求する形 (mmd L2015 以降) に合わせるのが正解。

## 消費側

- issue 3026 (BG Thm 6.4) — 残り ~2,100-3,100 行のうち transport 2 行 (~1,000-1,400 行) がこれ。
