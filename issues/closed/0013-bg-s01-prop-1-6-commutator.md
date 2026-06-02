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

- [x] BG Prop 1.6(a)-(e) の statement を mmd で確認し、Lean で扱いやすい形に分ける。
- [x] `[G,A]` の既存表現 (`actionCommutator` など) との対応を決める。
- [x] Prop 1.6(a)-(c) を実装する。
- [x] abelian case の direct product decomposition (d)(e) を実装する。
- [x] Prop 1.5 との依存関係を issue 0012 に明記する。

## 進捗 (2026-05-30, bg-parallel-frontier workflow + 本人確認)

§1B docstring (S01_Solvable.lean:482-501) の mapping table で現状確定:

- **(a) `G = C_G(A)[G,A]`** → `Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top` ✅ sorry-free (no-wrapper)
- **(b) `[G,A,A]=[G,A]`** → `Isaacs.Ch04.iterCommutator_inl_inr_two_eq_one` ✅ sorry-free
- **(e) abelian p群 + p'作用** → `Isaacs.Ch04` §4D ✅ sorry-free
- **(c) `[G,A,A]=1 ⇒ [G,A]=1`** → `iterCommutator_inl_inr_one_eq_bot_of_two_eq_bot` ✅ sorry-free; Ch04 Lem 4.29 の Γ-form equality から導出。
- **(d) abelian 直積 `G = C_G(A) × [G,A]`** → `fixedPoints_isComplement_actionCommutator_of_abelian` ✅ sorry-free; Ch04 Lem 4.28 の sup と Thm 4.34 の trivial intersection を `Subgroup.IsComplement'` として package。

→ **Prop 1.6(a)-(e) resolved**。Public BG-facing declarations are present for (c)(d); (a)(b)(e) remain no-wrapper/direct Ch04 references as recorded in the S01 table.

## 完了条件

- BG Prop 1.6(a)-(e) が sorry-free theorem または明示的な no-wrapper/doc-only 判断として整理済み。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- issue 0012
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`
- `references/bg/local-analysis.mmd` L416-L424 付近
