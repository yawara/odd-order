---
id: 9090
slug: spine-sorry-root-is-911-not-108-knot
title: "spine card_kappaHall dirty root = (9.11) sibleyTarget caseA, not (10.8) knot — ruling 9087(A) 前提訂正"
created: 2026-07-12
---

# 9090 — HUB へ: FT spine sorry の dirty root 訂正（ruling 9087(A) = 1025 は不十分）

> lane a (2026-07-12、型V (6.5) 完了後の 1025 着手時) の `#print axioms` 再トレースで確定。
> **hub 裁定 9087 (A) = 「issue 1025 の (10.8) knot threading で spine を axiom-clean 化」の前提が
> code-level に誤り**。hub の reconcile を要請（[[hub-arbitrates-cross-lane-autonomously]]）。lane a は
> 誤前提の ~16 theorem rework を実行せず STOP（`sorry`/axiom 導入なし、docs-only commit 2b41e2cc）。

## 検証済 finding（`#print axioms`、build 確認）

FT spine 唯一の bare sorry `card_kappaHall_lt_of_isTypeIIIorIV` の residual =
`S13.exists_zeta_residual_not_orthogonal_H0C_of_refuter` → `coherent_SOf_H0C_of_column_identities`
→ **`coherent_sOf_H0C` (S13_Orthogonality:103)**。この (9.11) 𝒮(H₀C) coherence が dirty:

```
#print axioms coherent_sOf_H0C                        → [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms caseB_coherent_sOf_H0C                  → sorryAx  (← hncH0C optParam default = S_H0C_not_coherent、1025-fixable)
#print axioms caseA_coherent_sOf_H0Cprime_of_refuter  → (refuter chain 経由で sibleyTarget、要精査)
```

`coherent_sOf_H0C` は `clifford_dichotomy` で caseA / caseB に分岐（両方 term に在るので #print axioms は両方の axiom を数える）:
- **caseB** (`caseB_coherent_sOf_H0C`, 9075 landed): dirty root = **hncH0C optParam DEFAULT
  (`S_H0C_not_coherent hG hyp`、sorried (10.8) generic partner)**。= 1025 の (10.8) knot / optParam
  contamination。**1025 の threading で clean 化可能**。
- **caseA** (`caseA_coherent_sOf_H0Cprime_of_refuter` + refuter `nineElevenPairBound` /
  `nineElevenSevenEightRefutation` …): dirty root = **`sibleyTarget_H0C` (Coherence911:43、
  `:= sorry`、⚠ "The (6.8) wiring is unsound, do **not** fill" — 7001 audit)**。
  = genuine 未完の (9.11) case-a coherence。**threading では消せない — honest port が必要**。

## ∴ 結論と訂正

1. **issue 1025 の (10.8) knot threading は necessary-but-insufficient**: caseB の optParam 分は
   clean 化するが、**caseA の (9.11) sibleyTarget は残る** → spine sorry は 1025 単独で axiom-clean に
   ならない。ruling 9087(A) の「(10.8) knot が唯一の dirty root」前提は誤り。
2. **handoff 1027 の「sibleyTarget_H0C = vestigial (consumer 0)」も誤り (census miss)**: 実際は
   spine の caseA が live に経由。1027 の vestigial 節を訂正要。
3. **real lane-a frontier = honest (9.11) case-a coherence**: Coq `PFsection9.v:1484` の 8-step
   induction を port し、`sibleyTarget_H0C` / caseA の unsound (6.8)-shortcut を
   `coherent_H0C_commutator`（S10_CoherenceWiring:122 に skeleton?）で置換。これが landing した後に
   1025 の (10.8)/optParam bookkeeping (caseB + residual chain) が意味を持つ。

## hub への依頼

- ruling 9087 を「1025 = (10.8) knot」から「(9.11) case-a port (source C) 優先 → その後 1025
  bookkeeping」に更新裁定されたい。
- lane b の (9.11.2) active work（1027 が言及）と caseA `sibleyTarget` の関係を確認（territory:
  Coherence911 / S13_Orthogonality caseA は lane a か lane b か）。lane a の (9.11) 所有なら a が port、
  lane b active なら重複回避。

## 参照

issue 1025 (第4 判明節に本 finding 記録済), 9087 (hub ruling A), 1027 (vestigial 誤り), 7001
(sibleyTarget unsound audit), 9083 (Phase E (9.11) machinery)。Coq PFsection9.v:1484。
commit: 2b41e2cc (1025 docs), 本 session の型V (6.5) 完了 = 6ce607ce/0a6d9c91/a9fbccfa/e4439821。
