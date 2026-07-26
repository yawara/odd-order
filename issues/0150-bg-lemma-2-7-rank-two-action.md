---
id: 150
slug: bg-lemma-2-7-rank-two-action
title: "BG Lemma 2.7: (Z/q)² が (Z/p)² に忠実作用 ⟹ q ∣ p−1 かつ冪写像 α が在る"
created: 2026-07-26
---

# BG Lemma 2.7 — rank-2 elementary abelian が rank-2 elementary abelian に忠実作用

## 位置づけ

**3 冊スコープで残る「真に未形式化の数学」のうち、文書順で最も上流の項目** (2026-07-26 の
全数再実測の結論; 正本 = `notes/meta/three_books_full_survey_2026_07_16.md` の
「BG の突き合わせ」「Pf 特殊化債務リストの再実測」節)。Isaacs は完済、BG の残りは本項 +
§16 tame-embedding (issue 8005 で意図的 defer) + App.C Rem (II)/(V)、Pf の残りは
(6.2)-(6.6) の h56 oracle + packaging のみ。

## 主張 (BG p.31, Lemma 2.7)

`p ≠ q` を素数、`P ≅ (ℤ/p)²`、`Q ≅ (ℤ/q)²` とし、`Q ≤ Aut(P)` (忠実作用) とする。このとき

- **(a)** `q ∣ p − 1`;
- **(b)** ある `α ∈ Q^#` が冪写像として作用する: `∀ x ∈ P, α x = x^r` で
  `r^q ≡ 1 (mod p)` かつ `r ≢ 1 (mod p)`。

## 実測状況 (2026-07-26)

**未形式化** (07-16 調査の "VERIFIED missing (refutation attempted and failed)" を再確認)。
repo 内の `2.7` ラベルは全て Isaacs Lem 2.7 / Peterfalvi (2.7) / BG Thm 12.7 / 表示式 (12.7)。

Coq 対応物 `regular_abelem2_on_abelem2` (`BGsection2.v:1048`) は Coq 側でも FT 証明本体から
未使用 — **純粋な書籍完備性項目**で、下流を unblock しない (だが CLAUDE.md の方針どおり
「payoff の遠さ」は着手判断の基準にしない)。

## 証明ルート (BG 原文 + 既存インフラ)

`P` を 2 次元 `𝔽_p`-ベクトル空間と見る。

1. **既約でない**: `Q` は可換だが非巡回。`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`
   (`OddOrder/GroupTheory/RepresentationTheory/SingerField.lean:494`) の対偶 —
   忠実かつ既約なら `Q` は巡回。⟹ `Q`-部分加群として真の直線 `L₁` が在る。
2. **完全可約**: `|Q| = q²` と `|P| = p²` は互いに素なので Maschke で補空間 `L₂` が取れる
   (`P = L₁ ⊕ L₂`、両方 1 次元)。
3. **スカラー指標**: `Q` は各直線に `𝔽_p^×` のスカラーで作用 ⟹ 指標
   `χ₁, χ₂ : Q →* 𝔽_p^×`。`Q` の指数は `q` なので `χ_i^q = 1`。
4. **忠実性**: `(χ₁, χ₂) : Q ↪ μ_q × μ_q` が単射。`|Q| = q²` ゆえ全単射で、特に
   `μ_q ⊆ 𝔽_p^×` は位数 `q` ⟹ **`q ∣ p − 1`** = (a)。
5. **(b)**: 4 の全射性から `χ₁(α) = χ₂(α) = ζ` (原始 `q` 乗根) となる `α` が取れる。
   この `α` は `P` 全体で `x ↦ x^r` (`r = ζ` の代表) として作用し、`r^q ≡ 1`、`r ≢ 1`。

## 既存インフラ

| 部品 | 所在 |
|---|---|
| Singer 順序限界 (忠実+既約+可換 ⟹ 巡回・位数 ∣ `|M|−1`) | `RepresentationTheory/SingerField.lean:494` |
| `q ∣ p²−1` (rank ≤ 2 への素数位数自己同型) — **本項より弱い** | `GroupTheory/PRank.lean` `prime_dvd_prime_sq_sub_one_of_orderOf_mulAut` |
| Singer field data / `μ : C →* Kˣ` | 同 `SingerField.lean` (`nonempty_singerFieldData`) |

### 2026-07-26 追調査 — Lean 側の橋渡し経路

- **モジュール構造**: `SingerField` 系の定理は `[Module (MonoidAlgebra (ZMod p) C) M]` を
  **instance 仮説として取る**(自分では作らない)。よって `φ : Q →* MulAut P` から作る必要がある。
  経路は mathlib 標準の **`Representation.asModule`** で、本 repo 内に使用実績あり:
  - `BG/Ch1_Preliminary/S02_RepresentationsBasic.lean:776` (Maschke + `Representation.asModule` 橋)
  - `BG/Ch1_Preliminary/S03d_Thm34.lean:339,353` (`Representation.asModuleEquiv_map_smul` /
    `asAlgebraHom_single_one` の実使用)
- **elementary abelian → ZMod p 加群**: `IsElementaryAbelian.zmodModule`
  (`GroupTheory/PRank.lean:87`) が `Module (ZMod p) (Additive E)` を与える。次元は
  `hE.card_eq_pow_finrank` で `|E| = p^n`。**setup の書き方の手本は
  `PRank.prime_dvd_prime_sq_sub_one_of_orderOf_mulAut` (:354)** — 同じ「rank ≤ 2 の
  elementary abelian に素数位数自己同型」設定を `letI := hE.zmodModule` で回している。
- **(a) は 1 本の非自明指標だけで出る**: `χ₁, χ₂` の像は `𝔽_p^×` の `q`-捩れなので位数 1 か `q`。
  両方自明なら `Q` が自明作用 ⟹ 忠実性に反する。よって少なくとも一方が位数 `q` ⟹ `q ∣ p − 1`。
- **(b) の核勘定**: `χ₂` が自明なら `ker χ₁ ∩ ker χ₂ = ker χ₁ = 1` ⟹ `χ₁` 単射 ⟹ `Q ↪ μ_q` 巡回で
  `Q ≅ (ℤ/q)²` に矛盾。よって**両方非自明**で `|ker χᵢ| = q`、かつ `(χ₁,χ₂) : Q → μ_q × μ_q` は
  位数 `q²` 同士の単射 ⟹ 同型。よって `(ζ, ζ)` の逆像 `α` が両直線に同一スカラー `ζ` で作用 =
  `x ↦ x^r`。

⚠ **Maschke の適用形** (`|Q| = q²` と `p` が互いに素 ⟹ 完全可約) が repo のどの補題で出るかは
未確定。`S02_RepresentationsBasic.lean` の Maschke 節をまず読むこと。

## 完了条件

- (a)(b) を書籍強度の単一定理 (または 2 定理) として sorry-free で landing。
- `AxiomsCheck.lean` に登録して axiom-clean を確認。
- ⚠ **sorried statement を先に置かない** (現在 repo の実 sorry は Q₈ Brauer-Suzuki の 1 件のみ。
  非退行を守る)。
