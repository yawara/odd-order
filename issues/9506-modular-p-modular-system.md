---
id: 9506
slug: modular-p-modular-system
title: "modular 表現論の底: p-modular system と Brauer 指標 (0147 の bottom-up 第 1 段, hub claim)"
created: 2026-08-03
---

# modular 表現論の底: p-modular system と Brauer 指標

**claim**: hub / main session (9500 band) / **状態**: 着手 (2026-08-03)

## 位置づけ

[issue 0147](0147-q8-modular-char-theory-frozen.md) (Q₈ Brauer–Suzuki, spine = Navarro 1998
Ch.1–7 / Z\*-定理) の **bottom-up 第 1 段**。project spec =
`notes/meta/q8_modular_char_theory_frozen_project.md` §3 の (1)(2)。

3 冊 (Isaacs / BG / Peterfalvi) の残り唯一の実 `sorry` が
`Peterfalvi/Appendices/RankOneAffineModel.lean` の `brauerSuzuki_quaternionSylow_q8` であり、
その根には mathlib にも本リポジトリにも**一切存在しない** modular 表現論がある (下記実測)。

## 着手前検索の結果 (2026-08-03 実測)

* **mathlib に無い**: `BrauerCharacter` / `decompositionMatrix` / block 論 / `defectGroup` は
  0 件 (`CartanMatrix` はルート系のもので別物)。mathlib の表現論は char 0 の ordinary のみ。
* **本リポジトリにも無い**: `OddOrder/GroupTheory/RepresentationTheory/` は 114 leaf あるが
  すべて ordinary。`pRegular` / `IsPRegular` / `IsDiscreteValuationRing` / `ResidueField` の
  grep はいずれも 0 件。
* 使える土台: mathlib の `IsDiscreteValuationRing` / `IsLocalRing.ResidueField` /
  `IsAdicComplete`、および本リポジトリの ordinary 指標一式
  (`ClassFunction` / `IrreducibleCharacter` / 誘導指標 / 直交関係)。

## 設計方針 (この issue で決める分岐)

Brauer 指標の定義には 2 つの流儀がある:

1. **p-modular system 経由** (Navarro Ch.1–2 の流儀): 完備 DVR `𝒪` (剰余体 `k` が char `p`,
   商体 `K` が char 0) を固定し、`p'`-位数の 1 の冪根の群 `U ⊆ K^×` と `k^×` の間の同型を通す。
2. **代数閉体 `k` だけで定義**: `k^×` の `p'`-部分と `ℂ^×` の `p'`-部分の間の単射を固定する。

**採用 = 1 (p-modular system)**。理由: block 論 (Brauer 対応・defect group、Navarro Ch.3–6) が
`𝒪` 上の冪等元の持ち上げを本質的に使うので後段で必ず必要になる。2 から始めると block 論の
段で作り直しになる。

⚠ **carrier の構成可能性 (CLAUDE.md「進捗の測り方」)**: `IsPModularSystem` を仮説クラスとして
置くだけでは doneness にならない。任意の `p` と `n` に対して「`n` 乗根を含む分裂 p-modular
system」を**実際に構成する**ところまでを本 issue のスコープに含める
(`ℤ[ζ_n]` の `p` 上の極大イデアルでの局所化 → 完備化)。これが無いと最終定理が空虚になる。

## やること (bottom-up)

- [ ] `OddOrder/GroupTheory/RepresentationTheory/Modular/PModularSystem.lean` —
      `𝒪` (完備 DVR, char 0) / `K = Frac 𝒪` / `k = 𝒪/J(𝒪)` (char `p`) の束ね、
      還元射 `𝒪 → k`
- [ ] `p'`-根の一致: `U = μ_{p'}(K)` と `k^×` の `p'`-部分の同型
- [ ] 分裂条件 (`|G|` 乗根を含む) と、**具体構成による instance**
- [ ] `p`-regular 元 / `p`-regular 類の API (`IsPRegular g ↔ p ∤ orderOf g`)
- [ ] Brauer 指標 `IBr`: `k G`-加群の `p`-regular 元でのトレースを `U` 経由で char 0 へ持ち上げ
- [ ] `|IBr G| = p`-regular 類の個数

以降 (別 issue に分割予定): 分解行列 `D` / Cartan 行列 `C = DᵀD` / block / Brauer 対応 /
2nd・3rd main theorem / Z\*-定理 → Q₈ bridge。

## PDF gate について

0147 の pickup 手順 step 1「Navarro Ch.5–7 を精読して Ch.1–4 の slice を絞る」は **PDF 待ち**
(ユーザー購入手配中)。ただし step 2 の**最初の段 (p-modular system / Brauer 指標) は
標準的な内容で slice 絞りに依存しない**ので、そこから着手する。
PDF が入り次第 Ch.5–7 を読んで以降の段の範囲を確定する。

## 完了条件

上記チェックボックスが全て埋まり、**具体構成による instance が存在**し、
build green + AxiomsCheck 登録 + sorry 非退行。

## 参照

- 親: [0147](0147-q8-modular-char-theory-frozen.md)
- spec: `notes/meta/q8_modular_char_theory_frozen_project.md`
- 前提調査: `notes/peterfalvi/appendixC_prop1_q8_brauer_suzuki.md`
