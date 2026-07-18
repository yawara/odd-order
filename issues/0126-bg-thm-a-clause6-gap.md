---
id: 126
slug: bg-thm-a-clause6-gap
title: "BG Thm A(6) の未形式化条項 (M_F ≠ 1 / M' ⊊ M / M'/M_F nilpotent) + 15.7 docstring の stale 記述"
created: 2026-07-19
owner: lane c (BG)
---

# BG Thm A(6) の未形式化条項 + 15.7 docstring の stale 記述

issue 9154 §2 の BG/Peterfalvi 実測監査 (hub, 2026-07-19) で発見。
**survey は Thm A を「済 (book A(1)-(8) 全)」と記録していたが、実測では 部分**。
これは「未形式化を未形式化と記録し損ねる」stale (量は多いが無害) ではなく、
**完了していないものを完了と記録していた逆方向のズレ**で、こちらが危険。

## (1) Thm A(6) — 本質的な欠落

`theoremA_maximal_structure_faithful` (`S16_MainResults/TypeBridges.lean:950`) を
mmd L4363-4371 と逐条照合した結果:

| 条項 | 状態 |
|---|---|
| A(1)(2)(4)(5)(8) | ✅ verbatim |
| A(3) | ⚠ `M = K ⊔ U ⊔ M_σ` と `M ≤ N(U M_σ)` はあるが、book の **`U ⊴ UK`** が無い |
| A(6) | ❌ **本質的な欠落** (下記) |
| A(7) | ⚠ `M'' ≤ F(M)` のみ。`F(M) = C_M(M_F) M_F` と `K ≠ 1 → F(M) ⊆ M'` を運んでいない (実体は `fitting_decomposition` 側にあるので packaging の問題) |

**A(6)**: book は `1 ⊂ M_F ⊆ M_σ ⊆ M' ⊂ M` **かつ `M'/M_F is nilpotent`** と印字するが、
Lean の結論は `M_F ≤ M_σ` と `M_σ ≤ M'` **のみ**。すなわち以下が欠けている:

- `M_F ≠ ⊥` — ⚠ **リポジトリ全体を grep しても主張する宣言が無い**
  (`MF M ≠ ⊥` / `Nontrivial ↥(MF …)` / `mf_ne_bot` いずれもヒット 0)。型別には導出可能に
  見えるが surface されていない。
- `M' ⊊ M` (真の包含)
- `M'/M_F is nilpotent` — type-F 版 `isNilpotent_complement_of_isTypeF`
  (`TypeP1Criteria.lean:470`) は landing 済。**全 M に対する一般形が残る**。

⚠ survey の Thm A 行はこの capstone を「book 外の repo 内 packaging follow-on (book gap でない、
低優先)」と分類しているが、**§16 引用ブロックの散文は同じものを "genuine residual gap" と
書いており矛盾**する。**正しいのは散文側** — book A(6) / Cor 15.5(c) に印字されている条項。

## (2) リポジトリ側の stale docstring (BG 15.7)

`S15_MF/OpicoreCentralizer.lean:410-413` の `fitting_not_ti_cases` docstring が今も

> **Still owed to the book (issue 3022):** conjunct (d) … and the genuine (e) trichotomy …
> Do **not** read this theorem as a complete formalization of 15.7.

と書いているが、**(d) と (e) は別宣言として landing 済** (issue 3022 は close):

- (d) = `sigmaComplement_structure_of_not_fittingIsTI` (同ファイル:286) + `quotientE2MulEquivE1` (:335)
- (e) = `fitting_not_ti_structure_e` (`S16_MainResults/FittingNonTITrichotomy.lean:123`、AxiomsCheck:9264 登録済)

⟹ docstring を現状に追随させる (issue 0125 と同型の「repo が自分の到達度を誤記している」問題)。

## やること

- [ ] A(6) の 3 条項 (`M_F ≠ ⊥` / `M' ⊊ M` / `M'/M_F nilpotent` 一般形) を形式化し、
      `theoremA_maximal_structure_faithful` の結論に組み込む
- [ ] A(3) の `U ⊴ UK`、A(7) の 2 条項を packaging に追加 (実体は既存ゆえ配線のみ)
- [ ] `fitting_not_ti_cases` の docstring から stale な "Still owed" 段落を除去
- [ ] survey の Thm A 行を「済」→「部分」に訂正し、§16 散文との矛盾を解消

## 完了条件

`theoremA_maximal_structure_faithful` が book A(1)-(8) を逐条で運び、15.7 の docstring が
実体と一致している。

## 参照

- issue 9154 §2 (BG/Pf 実測監査、本 issue の出所) / issue 3022 (15.7、close 済)
- 監査 workflow: `wf_27b12223-fd5`
