---
id: 3019
slug: s16-thm2-tamely-imbedded
title: "BG §16 Thm II (Tii) packaging + tamely-imbedded 定義 — 残 §16 ギャップ"
created: 2026-07-18
---

# BG §16 Thm II (Tii) packaging + tamely-imbedded 定義 — 残 §16 ギャップ

## 背景

lane c frontier (lane_reallocation_2026_07_16.md §2) の BG §16 は本 session (2026-07-18) で
Thm C(9) 完全恒等式 (`a0_minus_a_eq_conj_zTilde`) + Thm A type-F nilpotent
(`isNilpotent_complement_of_isTypeF`) を landing。残 §16 ギャップ = **Thm II (Tii)(a)-(e) packaging**
+ **tamely-imbedded 定義** (Remark after Thm II)。scoping 済 (subagent a23ed354、read-only)。

## 現状 map (mmd = references/bg/local-analysis.mmd)

- **Def tamely-imbedded / system of supporting subgroups** (mmd:4575、Remark after Thm II):
  repo に完全欠落 (grep `Tame*`/`SupportingSubgroups` = 0)。raw 部品は存在
  (`GroupTheory/MaximalSubgroupType.lean`: `escapingCentralizerSet`=D:54 / `supportKernel`=R(x):64 /
  `thickenedSupport`:74; `Notation.lean`: `ASet`/`A0Set`/`RData`/`tildeM`)。**定義 bundle 不在**。
- **Thm II** = `theoremII_tame_embedding` (`TaxonomyOutput.lean:1452`、sorry-free、AxiomsCheck:8276)。
  現状 3 conjunct = (Ti) G-conj⟹M-conj / D⊆A(M) / ∃! type-I|II maximal overgroup。
  **(Tii)(a)-(e) の supporting-subgroups package + (Tiii) は未 stated**。

## やること (推奨順、subagent 提案)

- [ ] **Gap 1: 定義** `SystemOfSupportingSubgroups` + `TamelyImbedded` structure を新 leaf
  (`S16_MainResults/TamelyImbedded.lean`) に。既存 object のみ使用・**新数学なし**。faithful に
  (Ti)-(Tiii) を mmd:4555-4575 からミラー。⚠ 定義は load-bearing ゆえ book と精密照合してから commit。
  FT Def 9.1(ii) の一般形との差 (BG (Tii)(d)) を docstring 注記。
- [ ] **Gap 2a: Lemma 14.13(b)** (mmd L4135) を `S16_Lemma1413.lean` に追加 (14.13(a)=`:292` の sibling)。
  「x∈D に対し M で選んだ共役 y∈D + C_G(y)=C_{H_i}(y)C_M(y)⊆M_i」。Thm 14.4 の ~5 行帰結 (effort S)
  だが **新 math** (Lean/Coq 双方に不在)。これが (Tii)(e)/(Tiii) の crux。
- [ ] **Gap 2b: packaging** `theoremII_tii_system_of_supporting`: `theoremII_tame_embedding` +
  Thm D(4) (`TaxonomyOutput.lean:948` complement/escape) + Thm B(5)/C(9) TI (at M_i) +
  `sigma_reps_pairwise_disjoint` (`TheoremsAE.lean:1551`、(a) 用) + Lemma 14.13(b) から
  `SystemOfSupportingSubgroups M X` を構成。(a)(b)(d) は engine 済で組立 bookkeeping、(c) は
  σ-disjoint から要導出、(e)/(Tiii) は 14.13(b) 依存。

## 完了条件

各 sub-clause を book strength・sorry-free・axiom-clean。tamely-imbedded 定義が faithful。
Thm II が (Ti)+(Tii)(a)-(e)+(Tiii) を stated + proved。AxiomsCheck 登録 (load-bearing)。survey §16 更新。
⚠ math-comp Coq は (Tii)(a) を drop し proof-relevant slice のみ (BGsection16.v:1245 per survey) —
本 repo は full book scope ゆえ (a)-(e) 全部を目指す (Coq を超えるのは想定内)。14.13(b) が真に
intractable と判明したら honest issue-defer (恒久除外せず)、それ以外は自律継続。

## 参照

- scoping report = subagent a23ed354 (本 session)、mmd:4431/4555/4575/L4135、survey §16 (md:376-)。
- 既存: `theoremII_tame_embedding` (TaxonomyOutput.lean:1452)、`non_disjoint_signalizer_frobenius`
  (=14.13(a), S16_Lemma1413.lean:292)、`theoremD_msigma_conjugacy_and_centralizers` (TaxonomyOutput.lean:948)。
- ⚠ coq/ は本 worktree で空 (submodule 未 init; `git submodule update --init coq` で取得)。
