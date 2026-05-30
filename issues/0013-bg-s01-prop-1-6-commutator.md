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

## 進捗 (2026-05-30, bg-parallel-frontier workflow + 本人確認)

§1B docstring (S01_Solvable.lean:482-501) の mapping table で現状確定:

- **(a) `G = C_G(A)[G,A]`** → `Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top` ✅ sorry-free (no-wrapper)
- **(b) `[G,A,A]=[G,A]`** → `Isaacs.Ch04.iterCommutator_inl_inr_two_eq_one` ✅ sorry-free
- **(e) abelian p群 + p'作用** → `Isaacs.Ch04` §4D ✅ sorry-free
- **(c) `[G,A,A]=1 ⇒ [G,A]=1`** → docstring「未実装」。(b) の系として 1 行で従う見込みだが明示 decl 無し。
- **(d) abelian 直積 `G = C_G(A) × [G,A]`** → docstring「存在予定」。(a) + `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` (Ch04:3396) から構成可能と見込まれる。

→ **(a)(b)(e) done, (c)(d) 未確定**。本 issue は **open 維持** (workflow の verify は `Main:3396/3442` を見て「全部 done」と早合点したが docstring が否定)。(c)(d) の decl 化 or doc-only 判断は §1B (Prop 1.5 = issue 0012) 本格着手時にまとめて行う。FT クリティカル経路上、§1B が gate するのは §7 (Prop 1.5 経由) であって Prop 1.6 単独ではない。

## 完了条件

- BG Prop 1.6(a)-(e) が sorry-free theorem または明示的な no-wrapper/doc-only 判断として整理済み。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- issue 0012
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`
- `references/bg/local-analysis.mmd` L416-L424 付近
