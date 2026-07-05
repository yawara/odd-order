---
id: 9014
slug: prime-ti-reducible-coherence
title: "HUB/shared: prime-TI-reducible coherence 基盤 (Coq §3/§4) — a(10.7)+b(13.3) 共有 gate、重複防止 claim"
created: 2026-07-06
kind: shared-infra
lanes: [a, b]
---

# HUB/shared: prime-TI-reducible coherence 基盤 (Coq §3/§4)

**種別**: shared-infra claim (claim-before-build、重複防止)。**owner = lane a** (Peterfalvi §3/§4 = a の
S03/S04 territory)。**consumer = a (10.7/10.8) + b (13.3)**。**判断者**: hub / ユーザー。

## 背景 (2026-07-06 hub 検出、a・b 独立診断の収束)

a と b が**独立に同じ prime-TI-reducible coherence 機構の欠落**に到達 (repo 未形式化と code-level 確認):
- **lane a (issue 1017 RE-DIAGNOSIS)**: (10.8) char capstone の真の blocker = (10.7) `typeII_derived_frobenius`
  (S12:47/54)。その Coq 証明 `Frob_der1_type2` (PFsection10.v:549-658) が **`primeTIred` /
  `FTtypeP_coherent_TIred` / `cyclicTIiso` / `uniform_prTIred_coherent` (Coq §3/§4)** に依存、repo grep 0 refs。
- **lane b (issue 2035 GENUINE GAP #1)**: (13.3) `character_degree_analysis` の family-membership gap
  `sS1S` (Coq PFsection13:428 `sS1S : {subset calS1 <= 'Z[calS]}`) = prime-TI Clifford dichotomy
  (`FTseqInd_TIred` / `cfInd_prTIres`、μⱼ = Ind of S′-restriction) に依存、repo 未形式化。

⟹ **同一の prime-TI-reducible 基盤 (Coq PFsection3/4)** が a の (10.7)/(10.8) と b の (13.3) を**両方 gate**。
両レーンが独立構築すると重複 (anti-duplication doctrine 違反)。**本 claim で owner を a に固定**し、b は cite。

## やること (owner = lane a、Pf §3/§4 = a territory)

- [ ] **prime-TI-reducible の core** を新規 leaf (`Peterfalvi/S03_*` or `S04_*`、a territory) に形式化:
  `primeTIred` (μ_j = prime-TI reducible constituent) + `cyclicTIiso` (cyclic-TI isometry) +
  `FTseqInd_TIred` (μ_j ∈ calS) + `cfInd_prTIres` (Ind of S′-restriction 構成的性質)。Coq PFsection3/4 mirror。
- [ ] a の consumer: (10.7) `typeII_derived_frobenius` (Coq `Frob_der1_type2` mirror) → (10.8) estimate。
- [ ] b の consumer: (13.3) `sS1S` family membership (Coq `S1cases` prime-TI Clifford dichotomy) → step 5a
  `induce_H_mem_zSpan_S` (issue 2035)。

## 完了条件

prime-TI-reducible core が a territory の新 leaf に sorry-free 形式化され、a の (10.7) と b の (13.3) が
両方 signature-contract で cite (待たない、a landing 前は sorried-cite)。

## 分業 / 待たない原則

- **a が本基盤を build** (owner)。並行して a は (10.8) の Lean-light path (S09 infra + |U|≥7) も探索中 (issue 1017)、
  どちらが先に (10.8) を閉じるかは a 自律。
- **b は待たない**: b は (13.3) の prime-TI 非依存部分 (τ₁ helpers = 2035 step 5b/c、tau1S_* assemble) を並行
  build、`sS1S` は a landing まで sorried-cite。b は本基盤を**構築しない** (重複回避)。
- **⟹ hub 監視**: a/b の新規 shared-infra leaf 追加を各 tick で dup 検出 (merge_monitor 1.6)。b が prime-TI
  core を新設したら重複 flag。

## 参照
- issue 1017 (§5 coherence / (10.8) — a re-diagnosis、prime-TI が真 blocker)
- issue 2035 (character_degree_analysis / sS1S GENUINE GAP #1 — b)
- Coq: PFsection3.v / PFsection4.v (prime-TI-reducible)、PFsection10.v:549-658 (Frob_der1_type2)、
  PFsection13.v:428 (sS1S) / S1cases
