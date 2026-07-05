---
id: 9014
slug: primeti-residue-api
title: "shared-infra claim: prime-TI residue API (primeTIred/prTIres_irr_cases) — §13 μ_j machinery + (13.3) sS1S の共通基盤"
created: 2026-07-06
---

# shared-infra claim: prime-TI residue API (primeTIred/prTIres_irr_cases) — §13 μ_j machinery + (13.3) sS1S の共通基盤

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## claim (shared infra, lane b, 2026-07-06)

**mathcomp prime-TI residue theory の port** — repo 未形式化と精密確認 (issue 2035 #7)。§13 の
μ_j machinery + (13.3) `induce_H_mem_zSpan_S` (sS1S / Pf (1.5.a)) の共通基盤。全レーンは着手前に本 issue を scan。

## 対象 API (mathcomp character library / Coq PFsection*)

- **`primeTIred`** (`mu_ : Fin p → ClassFunction S ℂ`): prime-TI subgroup `W`(≤ S) の residue reducible
  characters。`cfInd_prTIres` (誘導公式)。
- **`prTIres_irr_cases`**: prime-TI residue の constituent 分類 (各 `Ind_{PU}^S`-constituent は
  `mu_`-type か `𝒮 ∩ Irr S` か)。
- Coq 出典: `coq/theories/PFsection13.v:401-428` (`S1cases`) + mathcomp `character`/`PsGroup` の
  `primeTIhypothesis`/`primeTIres` 系。

## 建設順 (issue 2035 #7)

1. prime-TI setup + `primeTIred` core + reducibility + `prTIres_irr_cases` [substantial、~2-3 session]。
2. forward `FTseqInd_TIred` (mu_j ∈ 𝒮) [~0.5]。
3. `S1cases` dichotomy assembly [~1]。
4. `sS1S` wrapper (S15 の induce_H_mem_zSpan_S を close) [~1h]。

## 配置

新 shared leaf `OddOrder/GroupTheory/RepresentationTheory/PrimeTIResidue.lean` (consumer が他レーンでも
in-scope、territorial なのは所有 file のみ)。

## 完了条件

`induce_H_mem_zSpan_S` (S15:629) が本 API から honest に close され、§13 μ_j machinery も cite 可能に。

## 🧭 HUB 統合注記 (2026-07-06, 9014 番号衝突の consolidation)

hub も独立に同基盤の claim (旧 `9014-prime-ti-reducible-coherence.md`) を起票していたが、**本 issue
(b 版) を canonical として統合・旧 hub 版は削除**。b 版が (i) 配置 = RepTheory shared leaf として正確
(prime-TI residue = mathcomp character port ゆえ汎用 RepTheory; hub 旧案の Pf §3/§4 より適切)、(ii)
owner = lane b (ユーザー 2026-07-06 が CLAUDE.md 例として prime-TI port を挙げ b が claim = 承認済)、
(iii) build 計画が具体的、ゆえ。

**⟹ consumer 追記 (hub)**: 本 API の consumer は **b (13.3 `sS1S`/§13 μ_j) だけでなく a も** —
lane a の issue 1017 RE-DIAGNOSIS で **(10.7) `typeII_derived_frobenius` (Coq `Frob_der1_type2`,
PFsection10.v:549-658) が同じ prime-TI 機構 (`primeTIred`/`cyclicTIiso`/`uniform_prTIred_coherent`) に
gated** と確定済。⟹ **a は本 leaf を cite** (10.7)→(10.8) char capstone に、prime-TI core を**再構築しない**
(重複回避)。owner=b が build、a は sorried-cite で並行。hub は a/b の prime-TI leaf 重複を各 tick で監視。
