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

- ~~`X/F(X)` 冪零 ⟺ nilpotent residual `X^∞ ≤ F(X)` なので `NilpotentResidual.lean` の機構が
  使える可能性が高い。まず同 file を通読すること。~~
  ⚠ **不要な回り道だった (2026-07-19)**。nilpotent residual は使わず、Fitting 極大性からの
  直接論法で 1 補題あたり ~15 行。将来の読者がここから始めないよう降格。
- `Ch01.fitting` (`Isaacs/Ch01_Sylow/Basic.lean:764`) が subtype-level の Fitting。
  `Ch01.nilpotent_normal_le_fitting` (:963) が「冪零 normal ⊆ F」。
- ⚠ `fittingInAmbient` は Ch4/S15 レベルの**別概念**で §6 では層が違う (issue 3026 の
  Step-0 inventory 参照)。取り違えないこと。
- ~~⚠ 部分群遺伝は一般には**自明でない** (`F(Y) ⊉ F(X) ⊓ Y` が起こりうる)。追加仮説
  (subnormal? normal?) を洗い出すこと。~~
  ⚠ **この警告は誤りだった (2026-07-19 訂正、起票者の誤り)**。`F(X) ⊓ Y ≤ F(Y)` は
  **常に成り立つ** — `F(X) ⊴ X` ゆえ `F(X) ⊓ Y ⊴ Y`、かつ `F(X)` の部分群として冪零なので、
  Fitting の極大性 (`Ch01.nilpotent_normal_le_fitting`) が直接効く。一般に成り立たないのは
  **逆包含** `F(Y) ≤ F(X)` の方だが、そちらは不要。⟹ **追加仮説は一切不要**で、
  任意の部分群・任意の商について成立する (実際そう証明された)。

## 消費側

- issue 3026 (BG Thm 6.4) — 残り ~2,100-3,100 行のうち transport 2 行 (~1,000-1,400 行) がこれ。

---

## 完了 (2026-07-19)

`OddOrder/GroupTheory/FittingHeredity.lean` (新規 155 行)。6 定理すべて sorry-free・axiom-clean。

| 定理 | 内容 |
|---|---|
| `isNilpotent_quotient_fitting_of_isNilpotent_quotient` | 共通の最終段 (冪零 normal `K` があれば `X/F(X)` 冪零) — 第三同型 |
| `isNilpotent_quotient_fitting_of_injective` | 単射準同型に沿った遺伝 (一般形) |
| `isNilpotent_quotient_fitting_of_surjective` | 全射準同型に沿った遺伝 (一般形) |
| `isNilpotent_quotient_fitting_subgroup` | `H : Subgroup X` 版 |
| `isNilpotent_quotient_fitting_of_le` | `H ≤ K` (共通 ambient) 版 — **BG §6 が使う形** |
| `isNilpotent_quotient_fitting_quotient` | `N ⊴ X` 版 |

### 設計判断: **型レベル + 準同型に沿う**形を主とした

`Y ≤ X` の部分群レベルでなく `f : Y →* X` (単射) / `f : X →* Y` (全射) を主形にした理由:
BG Thm 6.4 の帰納法が要求する 4 つの transport は、いずれも
「同型 + 包含/射影」の合成であって literal な部分群・商ではない:
- `G₀ ⊓ S` を `↥S` の中で見る = `↥(G₀.subgroupOf S)` — `↥G₀` の部分群と**同型**なだけ
- `↥S/(G₀.subgroupOf S)` — `G ⧸ G₀` の部分群と同型
- `G₀N/N` — `↥G₀` の商と同型
- `(G/N)/(G₀N/N) ≅ G/G₀N` — `G ⧸ G₀` の商

部分群レベルの形だと消費側が `fitting` を各 `MulEquiv` 越しに手で運ぶ羽目になる。
準同型形ならそれを吸収でき、同型の場合は `_of_injective e.toMonoidHom e.injective` で済む。
issue 本文が挙げた 3 形は corollary として提供した。

### 供給した証明からの調整 3 点 (いずれも簡略化)

- **Lemma A は第二同型でなく第一同型で足りる**。合成 `φ : Y →* X →* X/F(X)` の
  `ker φ = f⁻¹(F(X))` (包含なら `F(X) ⊓ Y`)、`range φ = YF(X)/F(X)` なので
  `quotientKerEquivRange` 一発で「`Y/(F(X) ⊓ Y)` 冪零」が出る。
- 両補題の共通末尾を `isNilpotent_quotient_fitting_of_isNilpotent_quotient` に括り出した
  (`Ch01.nilpotent_normal_le_fitting` を呼ぶのはここ 1 箇所のみ)。
- `Finite Y` は仮説にせず `Finite.of_injective` / `Finite.of_surjective` で導出。仮説は `[Finite X]` のみ。

### ⟹ issue 3026 (BG Thm 6.4) の見積を下方修正

transport 2 行を 500-700 行ずつと見積もっていたが、実際は**汎用補題として合計 155 行**で、
消費側は cite するだけ。3026 の残り見積を修正すること。
