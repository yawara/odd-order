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

- [x] 新規 API: `OddOrder/GroupTheory/CentralProduct.lean` + exp-p extraspecial + agemo `℧` ✅ **2026-05-30 完了** (workflow `bg-s04-thm416-api-bundle`, commits 4656738/560312b/4d0269a, sorry-free/axiom-clean/build green 3352 jobs)
- [ ] Prop 4.3(a) cl≤3 分岐 + Lem 4.5 general/4.5(b)(c) (Gorenstein 5.4.10/5.4.3 行間)
- [ ] Prop 4.8 + Prop 4.11 Huppert + Thm 4.12 (§4 第2の山, 設計先行)
- [ ] Lem 4.13/4.14/4.15 (aut order + extraspecial commutator)
- [ ] Thm 4.16 本体 (Case A metacyclic / Case B-1 central product / Case B-2 GL(2,p) 矛盾)

## 進捗 (2026-05-30)

**issue 1 (新規 API 束) 完了** — workflow `bg-s04-thm416-api-bundle` (10 agent, design→implement→verify, anti-scaffold gated):

- `OddOrder/GroupTheory/CentralProduct.lean` 新規 — `IsCentralProduct R R₁ R₂ := R = R₁⊔R₂ ∧ ⁅R₁,R₂⁆=⊥`。overlap `R₁⊓R₂ ≤ Z(R)` は導出補題 (anti-hoist)。+ `of_le_centralizer` (Case B-1 producer)。
- `IsExtraspecial.lean` — `IsExpPExtraspecial p G := IsExtraspecial p G ∧ Monoid.exponent G = p` + `pow_eq_one`。
- `OmegaSubgroup.lean` — `Agemo p n G` (BG 𝒰ⁿ, Omega 双対) + `anti`/`characteristic`。
- 全て sorry-free / axiom-clean (`[propext, Classical.choice, Quot.sound]`)、`lake build OddOrder` green (3352 jobs)。

**設計書** `notes/bg/s04_prop411_thm416_design.md` (Prop 4.11/Thm 4.12/Thm 4.16, scaffold-trap audit + sub-issue I-0a..I-5)。次の着手 = handoff §6 issue 2 (Prop 4.3(a) cl≤3 + Lem 4.5 general)。**最深 gate = N-4 (A の R/S 商作用 + Maschke)** を設計書が指摘。

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
