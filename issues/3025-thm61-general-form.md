---
id: 3025
slug: thm61-general-form
title: "BG Thm 6.1 一般形: O_{p',p}(G) は S の任意の abelian normal 部分群を含む (thmA5_part2 経由)"
created: 2026-07-19
---

# BG Thm 6.1 一般形: O_{p',p}(G) は S の任意の abelian normal 部分群を含む (thmA5_part2 経由)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

issue 3017 (BG Thm 6.2 の literal `J(S)` 一般形) の調査 (2026-07-19) 中に発見した、
**隣接する tractable な特殊化債務**。3017/3024 とは違い **Glauberman ZJ に blocked されない**。

**BG Thm 6.1**: `O_{p',p}(G)` は `S ∈ Syl_p(G)` の任意の abelian normal 部分群を含む。

現状:
- 一般形は**未**。repo にあるのは reduced な `J(P)`-instance =
  `BG.Ch1.S06.thompsonJ_le_oPiPrimePiCore_of_odd` (`S06_Additional.lean:152`) で、
  `C_G(Z(P)) = P` に gated。
- `notes/bg/s06_additional.md` の残課題 3 に一般形が挙がっている。
- ⚠ なお BG Thm 6.1 自体は `AppA_PStability.lean` の `thmA4b` として在る (book が Thm 6.1 =
  Thm A.4(b) と同一視しているため; survey L476)。**本 issue が求めるのは「`O_{p',p}(G)` が
  `S` の abelian normal 部分群を含む」という形の一般形**で、これが reduced instance しか
  無い、という債務。着手時にまず両者の関係を実測で確認すること。

## 想定経路 (未検証、着手時に要確認)

既証明の **`thmA5_part2`** (`AppA_PStability.lean:1501`) が使えそう:
`Ḡ = G/O_{p'}(G)` で `P := O_p(Ḡ)` と取ると、
- `thmA5_part2` の仮説 `hCP` (`C_G(P) ⊓ O_p(G) ≤ P`) は `… ⊓ P ≤ P` に退化して自明に真、
- 仮説 `hX` は、`A ⊴ S̄` abelian なら `O_p(Ḡ) ≤ S̄` に正規化されるので満たされる。

`O_{p'}` reduction 自体は repo 内に既に 2 回 mirror されている
(`AppB_Thm62.zCenter_lOdd_sup_oPiCore_normal` と `S06` 側)。

⚠ 上記は調査 subagent の見立てであって**未検証**。着手時に `thmA5_part2` の実署名を読み、
仮説の退化が本当に起きるかを確かめること (本 session は stale label / 名前一致の罠を
3 回踏みかけている)。

## 参照

- issue 3017 (pending, ZJ に blocked) / issue 3024 (Gorenstein Ch.8 §2)。
- `notes/bg/s06_additional.md` 残課題 3。
- survey `notes/meta/three_books_full_survey_2026_07_16.md` L476 (BG §6 概況)。
