---
id: 2020
slug: pf-13-2-a-char-core
title: "Pf (13.2.a) character core: card_kappaHall_lt_of_isTypeP1 (lane-b §10-11)"
created: 2026-06-23
---

# Pf (13.2.a) character core — `card_kappaHall_lt_of_isTypeP1`

> 宛先 = lane-b (Peterfalvi §10–§11 character)。発信 = lane-h (relane #4)。
> lane↔lane sync は notes/issue 経由 ([[cross-lane-sync-via-notes]])。

## 背景: relane #4 で (13.2.a) を wire 完了、残るは character 核

relane #4 (issue 2019+4009) で lane-h が Pf **(13.2.a)「q<p ⟹ S は Type II (=type-P₂)」** を担当。
**型判定の skeleton と配線は完了** (`OddOrder/FeitThompson.lean`):

- `isTypeP2_of_typeP_kappaHall_lt` (下記 obligation 以外 sorry-free): 型-P の S が
  `|K| < |K*|` ⟹ `IsTypeP2 S`。証明 = S type-P ⟹ P₁∨P₂ (`isTypeP_iff_isTypeP1_or_isTypeP2`)、
  P₁ 枝を obligation で排除、P₂ を残す。
- `Section16MaximalPair.S_typeP2 : IsTypeP2 S` field を新設、producer
  `section16MaximalPair_of_isMinimalSimpleOdd` で fill。
- ⟹ **`mp.S_typeP2` が available** ⟹ lane-c の §15 carrier wiring (step 3,
  `exists_typePData_W1_eq_of_isTypeP2` を `mp.S` に適用) が unblock (issue 4009 完了条件達成)。

## 残 obligation = character 核 (lane-b 領域)

```lean
-- OddOrder/FeitThompson.lean
theorem card_kappaHall_lt_of_isTypeP1 (hG : IsMinimalSimpleOdd G)
    {S K Kstar : Subgroup G} (hS : S ∈ maximalSubgroups G) (hSP : BG.Ch4.S14.IsTypeP S)
    (hKS : K ≤ S) (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S))
    (hKstar : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G))
    (hP1 : BG.Ch4.S14.IsTypeP1 S) :
    Nat.card ↥Kstar < Nat.card ↥K := <left unproved>
```

**数学的内容** (Pf (13.2.a) 証明の 1 行目): 型-P の S が type-P₁ (= Type III/IV/V) なら、その κ-Hall
因子 K は dual 因子 K* = M_σ(S)⊓C(K) より**大きい** (`|K*| < |K|`)。Peterfalvi 記法で
`q=|W₁|=|K|`, `p=|W₂|=|K*|` ゆえ「S が Type III ⟹ q > p」。

**証明の出典** (Pf §13 = `references/peterfalvi/04.15_*`, (13.2.a) proof):
- **Theorem (10.10)** (Pf §10 = repo S12): G は Type V の極大部分群を持たない ⟹ type-P₁ の S は
  Type III/IV に限定。
- **(11.9.b)** (Pf §11 = repo S13, Hypothesis (11.2) = Type III/IV): 文字集合 `S(HC)` 上の
  coherence / norm 不等式から `q > p`。

⟹ これは Pf §10–§11 の **character 理論** (coherence + Dade isometry norm bound)。repo 未形式化、
lane-b 領域。文献に証明あり ([[feedback-dont-mislabel-formalization-as-research]]) = 形式化労力。

**discharge target の所在 (lane-h 調査)**: (11.9) は repo **S13 `final_typeIII_conclusions`**
(`S13_MaximalIII_IV.lean:386`、lane-h 所有、現 sorried) が
`hyp.q > hyp.p ∧ hyp.caseB_of_97 ∧ IsTypeIII M` を結論 (= q>p の char 核)。但し single-maximal
`Hypothesis M` (= Hyp (11.2)) + `OrthogonalityData hyp` (char data) を前提とする。⟹ `card_kappaHall_lt_of_isTypeP1`
(pair level) への接続 bridge = [pair の type-P1 S → S の Hypothesis(11.2) 構成 (要 (10.1)+(10.10) Type III/IV
判定)] + [`OrthogonalityData` 構成 (char)] + [hyp.q/hyp.p ↔ |K|/|K*| 同定] で、bridge 自体も char-gated。
∴ 当 obligation は **fresh sorry のまま** が clean (接続層に sorry を移すと char infra 構築が二重化)。
`final_typeIII_conclusions` の sorry-free 化 (lane-b char) が本命。

## やること

- [ ] `card_kappaHall_lt_of_isTypeP1` を sorry-free 化 (Pf 10.10 + 11.9.b の形式化、または既存
      lane-b char API を cite)
- [ ] 完了後 `mp.S_typeP2` が axiom-clean になるか確認 (現状は character sorry に gated)

## 完了条件

`card_kappaHall_lt_of_isTypeP1` が sorry-free。完了で **Pf (13.2.a) 全体が unconditional** になり、
`Section16MaximalPair.S_typeP2` (= POLE-1 critical path) が axiom-clean になる。

## 参照

- 現 obligation: `OddOrder/FeitThompson.lean` `card_kappaHall_lt_of_isTypeP1` (本セッション landing)
- 消費: `isTypeP2_of_typeP_kappaHall_lt` → `Section16MaximalPair.S_typeP2` →
  lane-c §15 `basic_structure` carrier wiring (`exists_typePData_W1_eq_of_isTypeP2`)
- 関連: issue 4009 (carrier wiring gate, CLOSED relane #4), issue 2019 (lane-h starve, CLOSED),
  issue 2018 (§13 char gate map), issue 2010 (Pf §10-13 cite-split)
- 原典: Pf (13.2.a)/(10.10)/(11.9.b) = `references/peterfalvi/04.15_*` / `04.12_*` / `04.13_*`
- repo 対応: (10.10)→S12, (11.7)/(11.9)→S13 (lane-h 所有、構造片は landed、character 核は未)

## 2026-06-23 REASSIGN (relane #6、ユーザー裁可、issue 4011) — lane-b → lane-c

hub 統合レビューで lane-c の §15 枯渇 → ユーザー裁可「char ボトルネック支援に再配置」。
本 obligation (card_kappaHall_lt_of_isTypeP1、POLE-1 残バレ sorry) を **lane-c が引き取り**
(FeitThompson def 単位 C=tp+card_kappaHall)。証明 = `no_typeV_maximal` (S12:5767、Thm 10.10) cite +
S13 (11.9.b) coherence/norm cite で (13.2.a) reduction。S13 も lane-c 所有 (issue 2018 移譲) ゆえ
(11.9.b) signature 整備も lane-c 内で可能。宛先 lane-b → **lane-c**。
