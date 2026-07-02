---
id: 18
slug: bg-s01-prop-1-16-noncyclic-auto
title: "BG §1 Prop 1.16 noncyclic abelian p-automorphisms を形式化する"
created: 2026-05-25
---

# BG §1 Prop 1.16 noncyclic abelian p-automorphisms を形式化する

## 背景

BG Prop 1.16 は noncyclic abelian p-automorphism group が p'-group `G` に作用する場合、
`G` が非自明元や cyclic quotient kernel の centralizer で生成されることを述べる。
Peterfalvi 04.11/04.14 でも参照される。

Isaacs Ch.3 の coprime action machinery から再引用・特殊化できる可能性があるが、
`A^#` や `A/Y cyclic` の Lean 表現は整理が必要。

## やること

- [ ] BG Prop 1.16 の 2 つの生成 statement を mmd で確認する。
- [ ] noncyclic abelian p-group の仮定を Lean でどう表すか決める。
- [ ] `A^#` と `A/Y cyclic` の index/generator set を定義またはローカルに表現する。
- [ ] centralizer generated statement を実装する。

## 完了条件

- BG Prop 1.16 の生成 theorem が sorry-free、または再利用可能な既存 theorem への対応が明示済み。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- `notes/bg/s01_solvable.md`
- `references/bg/local-analysis.mmd` L501-L505 付近
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

専用 leaf `OddOrder/BG/Ch1_Preliminary/S01b_Prop116.lean` が comment-strip で実 sorry 0、S09 (uniqueness) 側で消費済
(検証 2026-07-02)。
