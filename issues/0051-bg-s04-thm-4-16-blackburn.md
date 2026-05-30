---
id: 51
slug: bg-s04-thm-4-16-blackburn
title: "BG §4 Thm 4.16 Blackburn rank≤2 分類を形式化 (D)"
created: 2026-05-30
---

# BG §4 Thm 4.16 Blackburn rank≤2 分類を形式化 (D)

## 背景

BG §4 の頂点定理 = **Theorem 4.16 (Blackburn)**。p 奇, R 非自明 p-群, A p′-自己同型群, `r(R)≤2`, `[R,A]=R`, `|A|` odd ⇒ **p>3** かつ R は (1) abelian or (2) `R₁∘R₂` (R₁ exp-p extraspecial 位数 p³, R₂ cyclic, `Ω₁(R₂)=R₁'`)。

**Blackburn フル分類は Gorenstein/Isaacs に無く、BG が §4 内で完全自前展開** (`bg-s04-design` workflow wf_39c356b8-eb2 で確定)。形式化対象 = BG §4 補題チェーン (Prop 4.3→4.5→4.8→4.11 Huppert→4.12→4.13-15→4.16)。

§4 v1 (2026-05-30, `bg-s04-v1-impl` workflow) で **PRank 性質補強 / SCN₃ / Prop 4.4(a) / Lem 4.7⇒ / Lem 4.2 / Lem 4.5(a) 部分 / GL(2,p) 分岐エンジン** が sorry-free 完成。本 issue はその上に Thm 4.16 を載せる。

**詳細な cold-start 着手手順 = [`notes/bg/s04_thm416_handoff.md`](../notes/bg/s04_thm416_handoff.md)** (self-contained)。全体計画 = `notes/bg/s04_implementation_plan_2026_05_30.md`。

## やること

handoff §6 の sub-issue ロードマップに従う (各々別 issue 化推奨):

- [ ] 新規 API: `OddOrder/GroupTheory/CentralProduct.lean` + exp-p extraspecial + agemo `℧`
- [ ] Prop 4.3(a) cl≤3 分岐 + Lem 4.5 general/4.5(b)(c) (Gorenstein 5.4.10/5.4.3 行間)
- [ ] Prop 4.8 + Prop 4.11 Huppert + Thm 4.12 (§4 第2の山, 設計先行)
- [ ] Lem 4.13/4.14/4.15 (aut order + extraspecial commutator)
- [ ] Thm 4.16 本体 (Case A metacyclic / Case B-1 central product / Case B-2 GL(2,p) 矛盾)

## 完了条件

- BG Thm 4.16 が sorry-free / axiom-clean で `OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean` に着地。
- `lake build OddOrder` + `lake build OddOrder.AxiomsCheck` green。
- ⚠ **scaffold trap 厳守** (handoff §1): hard content を未充足仮説に hoist しない、`/goal` 単発不可、設計先行 + sub-issue 分割。

## 参照

- **handoff (cold-start 手順)**: `notes/bg/s04_thm416_handoff.md`
- 全体計画: `notes/bg/s04_implementation_plan_2026_05_30.md`
- BG 原典: `references/bg/local-analysis.mmd` L1636-1704 (Thm 4.16 本体)
- 既存: `OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean`, `OddOrder/GroupTheory/{PRank,SCN,CriticalSubgroup,IsMetacyclic,IsExtraspecial}.lean`
- 設計 workflow: `bg-s04-design` wf_39c356b8-eb2 / 実装 v1: `bg-s04-v1-impl` wf_ec23ca53-2a1
