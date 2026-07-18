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

- [x] **Gap 1: 定義** ✅ 2026-07-18 完了 (`S16_MainResults/TamelyImbedded.lean`):
  `TamelyImbedded` + `SystemOfSupportingSubgroups` + `FrobeniusTypeIWithNonTIFitting`。
  mmd:4555-4575 に faithful、(Ti)-(Tiii)+(a)-(e)、既存 object のみ (新数学なし)、build green。
  ⚠ **faithfulness fix**: D は `escapingSharpSet` (x≠1 込み、book 忠実) を新設して使用 —
  subagent の初版は `escapingCentralizerSet` (x≠1 欠、1∈A(M) ゆえ D 常に非空になる誤り) だった
  ので hub 検証で訂正。FT Def 9.1(ii)(e) 差を docstring 注記。root import 済。
- [x] **Gap 2a: Lemma 14.13(b)** ✅ 2026-07-18 完了 (`S16_Lemma1413.lean`、14.13(a) sibling):
  `signalizer_neighbour_conjugator_in_M` (∃ m∈M, N(y)^m=N)。axiom-clean、AxiomsCheck 登録。
  proof = x/y 両側 Thm D(4) complement を Schur-Zass 共役 (`IsComplement'.exists_conj_of_coprime`)
  → 𝓜_σ(x) sharp transitivity + N_G(M)=M。Thm 14.4 infra は全て在庫 (blocker 無)。
- [ ] **Gap 2b: packaging** `theoremII_tii_system_of_supporting`: `theoremII_tame_embedding` +
  Thm D(4) (`TaxonomyOutput.lean:948` complement/escape) + Thm B(5)/C(9) TI (at M_i) +
  `sigma_reps_pairwise_disjoint` (`TheoremsAE.lean:1551`、(a) 用) + Lemma 14.13(b) から
  `SystemOfSupportingSubgroups M X` を構成し、A(M) が `TamelyImbedded M (A(M))` を証明。
  (a)(b)(d) は engine 済で組立 bookkeeping、(c) は σ-disjoint から要導出、(e)/(Tiii) は 14.13(b) 依存。
  **← 次の frontier (残 §16 最終項目)**。

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
