---
id: 2035
slug: char-degree-analysis-producer
title: "(13.3) character_degree_analysis producer — S11 (9.x) + (9.11)/(6.8) coherence + (5.8) formula の組立 campaign"
created: 2026-07-05
---

# (13.3) character_degree_analysis producer — S11 (9.x) + (9.11)/(6.8) coherence + (5.8) formula の組立 campaign

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 目標

`character_degree_analysis` (S15_SAndT_Setup:654, sorried) — CharacterDegreeData の honest 構成。
2034 で materialize した fields (λ = Ind_{PC}(linear) P-non-kernel / τ₁ 4 fields) を実供給する。

## 設計 map (07-05 it.46 調査)

Pf (13.3) proof の引用 ↔ repo 在庫:

| Pf | 内容 | repo 状態 |
|---|---|---|
| (13.3.a) | μⱼ = Ind_{PC}(linear), μⱼ(1) = uq | S11 `caseB_character_counts` (6252, **sorried**) — SOf 機械・Clifford case 分析は大部分 proven |
| (13.3.b) | λ の存在 (WLOG 分岐) | μ₁ を λ に採用 (13.3.a 経由) |
| (13.3.c) δ=1 | (4.3.d)+(4.4) + u≡1 mod q | S06 CertainTypeConjugation の (4.9)(a)-bridges + UW₁ Frobenius (basic_structure) |
| (13.3.c) formula | (4.9) or (5.8): μⱼ^{τ₁} = Σᵢ ηᵢⱼ | S05_SigmaTrichotomy `(5.8) full-column endgame` (:318) — **core proven** |
| τ₁ 存在 | (13.2.d) 𝒮 coherent ⇐ (9.11) | S11 `coherent_H0C_commutator` — **(6.8) wired 済**、残 gap = `sibleyTarget_H0C` (:6304, sorried, §14-gated 構造 witness) |
| (9.11) の (6.8) | Sibley coherence | `S08.sibleySetup_is_coherent` **proven** (cascade notes 2026-07-02: 旧「lane B 供給待ち」framing は obsolete) |

## 実装順 (upstream-first)

1. [ ] **S15 ↔ S11 instantiation bridge**: hyp.S (type II) に対する
   `TypesIIIIIIVSetup`/`ChiefFactorData`/`Section11CharacterData` の構成。
   **precheck 済 (it.47)**: S12 に `toTypesIIIIIIVSetup` (III/IV 用 — type II 分岐
   Or.inl は未使用だが構造は II を受容) + `mkSection11CharacterData` が既存。
   **⚠ 重大 caveat: S12 の mk は `H0CprimeSupport := ∅` + `tau := hyp.tau` の
   count-専用 placeholder** (docstring 明記「used only by the (9.11) coherence, not by
   the degree fact」) — (9.11)-coherence 用途には **∅-support で IsCoherent が
   偽/空虚化する Sset := ∅ 型の罠**。本 campaign は honest 版
   (実 H0CprimeSupport = (H₀C')^#-support + 実 Dade tau) を新規構成する:
   - TypesIIIIIIVSetup: maximal := S_maximal / typeP := hyp.Sdata /
     nontrivial := TypePNontrivialCore (basic_structure の hSdataUne 系から) /
     type_alt := Or.inl (isTypeII_of_isTypeP2)
   - ChiefFactorData: S11.exists_chiefFactorData
   - Section11CharacterData: u は S12-mk と同型 (rfl-pin)、tau := (S, (H₀C')^#) の
     honest Dade map (H_sharp_dadeHypothesis の H₀C'-版)、H0CprimeSupport := 実 support
2. [ ] `sibleyTarget_H0C` (§14 structural witness) — S14 の SibleyTarget 供給
   (S14_MaximalI 機械 or type-II 側の直接構成; §14-gated の実態を precheck)
3. [ ] (13.3.a): S11 `caseB_character_counts` の残 sorry (6252/6277) を閉じる or 迂回
4. [ ] τ₁-fields 導出: `coherent_H0C_commutator` の IsCoherent (extension_agrees /
   inner_eq_on_supported) から 2034 の 4 fields (extends-Ind は τ=Ind (H_sharp_tau_eq_induce
   の M-版) 経由; ⊥η は (5.3.b)-系)
5. [ ] (5.8)-formula → mu_tau1 Props の materialize + δ=1
6. [ ] assembly: `character_degree_analysis` 本体

## 備考

- S-side τ₁ だが hub 裁定 2026-07-02 §2 と整合: atoms は W-side restate 済 (2034)、
  producer の coherence 構成は Pf-cite の本物 (13.2.d)⇐(9.11) 経路 — placeholder Sset 非依存。
- tau1T (T-side dual) も同型の構成 (T = type II dual, K = QD)。
- 関連: issues/2034 (fields 設計、残 checklist), closed/2033。

## route 候補 B (it.47 発見、要 precheck — 候補 A = (9.11)/H₀C′ より短い可能性)

**(6.8) Sibley を (G, L := hyp.S, H := hyp.H = PC) に直接適用**:
- `SibleyTarget` (S10_CoherenceWiring:96) = H ⊴ L + `S08.SibleyDadeHypothesis (G,L,H)` +
  τ/family/A₀ 一致 3 等式。`coherent_of_sibleyTarget` (sorry-free) で IsCoherent。
- (13.5)-family 𝒮₁ = {Ind_{PC}^S θ} は Sibley の base family そのもの;
  A₀ = (PC)^#-support、τ = H_sharp Dade (= Ind、13.2.e proven)。
- H = PC = F(S) ⊴ S ✓ / H^# TI + normalizer S ✓ (proven) — 残 = (6.8)(a)/(b)/(c) の
  正確な条件を S08.SibleyDadeHypothesis の fields で確認し (13.2)-carrier から充足するか。
- これが通れば S11-chars の honest 再構成 (route A step 1-2) を丸ごと skip し、
  IsCoherent → τ₁ + 4 fields 導出 (extension_agrees/inner_eq_on_supported) に直行。
- 次 iteration: S08.SibleyDadeHypothesis の fields 精読 + (S, PC)-充足性判定。
