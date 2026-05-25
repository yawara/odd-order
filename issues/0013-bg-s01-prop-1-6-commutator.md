---
id: 13
slug: bg-s01-prop-1-6-commutator
title: "BG §1 Prop 1.6 coprime action commutator theorem を形式化する"
created: 2026-05-25
---

# BG §1 Prop 1.6 coprime action commutator theorem を形式化する

## 背景

BG Prop 1.6 は coprime action の commutator theorem。`G = C_G(A)[G,A]`、
`[G,A,A] = [G,A]`、triviality criterion、abelian case の direct product decomposition
などを含む。Peterfalvi 04.3/04.11 で Prop 1.6(d) が使われるため、§1B の主要依存。

Prop 1.5(d) と Ch.4 の commutator/coprime action API に依存する。

## やること

- [ ] BG Prop 1.6(a)-(e) の statement を mmd で確認し、Lean で扱いやすい形に分ける。
- [ ] `[G,A]` の既存表現 (`actionCommutator` など) との対応を決める。
- [ ] Prop 1.6(a)-(c) を実装する。
- [ ] abelian case の direct product decomposition (d)(e) を実装する。
- [ ] Prop 1.5 との依存関係を issue 0012 に明記する。

## 完了条件

- BG Prop 1.6(a)-(e) が sorry-free theorem または明示的な no-wrapper/doc-only 判断として整理済み。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- issue 0012
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`
- `references/bg/local-analysis.mmd` L416-L424 付近
