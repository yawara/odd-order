---
id: 1020
slug: s12-108-relayering-102circle
title: "(10.8) hB の配線設計 — pair-route (10.7)' の (13.2.a) 循環発見 + 書籍 DAG 復元 3 phase 計画"
created: 2026-07-11
---

# (10.8) hB の配線設計 — (13.2.a) 循環の発見と 3 phase 計画

**lane a 設計記録 (2026-07-11 /loop)。⚠ 本 issue の循環発見は (10.8)/(11.8) 系 sorry を
埋める全員に関係 — hB を pair-(10.7)' cite で埋めるのは論理循環で不可。**

## 状況 ((10.8) の残り = hB 1 点)

`typeII_coherence_contradiction_estimate` (S12_MaximalBasic:828, sorry :876) は
hA (line-83 + (7.8.b) `chiRhoNormSq_zeta_ge_line78`) と hS/hu (partner 分解 +
`exists_typeII_partner_card_U_ge_seven`) が**証明済**。残 = **hB**
`g1g ≤ (|S_F|−1)/|S| + (w₁w₂−w₁−w₂+1)/(w₁w₂)`:
- 数学 (Pf p.60 lines 89-91): x ∈ G₁ → a := w₁-素数冪 part (prime order, x ∈ C(a))
  → (8.11)[**今日 6b08f22d で閉鎖**] H Hall → a ~ H# 元 → (8.6.a) C_G(a) ⊆ S →
  x ∈ C_S(a) → x ∈ HU なら **(10.7)** Frobenius kernel property で x ∈ H /
  x ∈ S−HU なら (2.1) で x ~ V 元 ⟹ **G₁ ⊆ (H#)^G ∪ V^G** → union-bound 計数
  (TI 不要、≤ 方向は N_G(H)=S / N_G(V) ⊇ W の軌道数上界で足りる) → ℚ 算術。
- 部品状況: V^G 側 ncard = `typePData_conjClassSet_typePV_ncard` (S12_Core:772、済)。
  (8.6.a)/(2.1)/Hall-共役/covering 本体 = 未 (Phase 2)。

## ⚠⚠ 発見: pair-route (10.7)' cite は論理循環

import 位相: MaximalBasic は pair leaf (`S12_TypeIICrossIsometryPair`) の**上流**
(FTS ← S13_CoreStructure ← S12_MaximalIII_IV_V ← … ← MaximalBasic) → cite 不能。
さらに taint 追跡で**論理循環**を確認:

```
(10.8) hB → [cite したい] (10.7)' typeII_HU_frobenius_of_coherent'
  → exists_reconciled_conj_typePData_S → isTypeP2_of_typeP_kappaHall_lt (13.2.a, FTS:703)
    ├→ card_kappaHall_lt_of_isTypeP1 (FTS:684) → no_typeV_maximal (10.10) → S_not_coherent (10.8) → hB ← 循環!
    └→ card_kappaHall_lt_of_isTypeIIIorIV (11.9.b, FTS:624) → (11.8) route → …残 sorry に (10.8) を含む ← 循環!
```

現在の acyclicity は hB ほか sorry が cut point になっているだけ。**書籍では循環しない**:
book-(10.7) は (13.2.a) を使わず §8/§9/§5 のみ ((13.2.a) は §13 で (10.10) の後)。
循環の根 = repo pair-route が M-seed relabel に (13.2.a) を使ったこと (9079 P3/P4 の
「既知 taint 継承」の正体)。

## 復元計画 (書籍 DAG: (8.8)ThmC → (10.7) → (10.8) → (10.10) → (11.x) → (13.2.a))

**Phase 1 — pair route の de-taint (a 所有、着手可)**: M-seeded pair producer 群
(exists_section16MaximalPair_data_around/_around + S_typeP2 pin) の
`isTypeP2_of_typeP_kappaHall_lt` 使用を **`theoremC_paired_structure` の P₂-disjunction
`(IsTypeP2 M ∨ IsTypeP2 Mstar)` (TheoremsAE:967、axiom-clean 実測済!) +
`not_isTypeP2_of_isTypeIII_or_IV_or_V` (clean、landed)** に置換。
⟹ (10.7)' が真に axiom-clean 化 (現 taint は 13.2.a 経由のみ)。

**Phase 2 — hB cover-bound engine (a 所有、Phase 1 と独立に着手可)**: MaximalBasic に
hypothesis-parameterized 版
`typeII_partner_G1_cover_bound (hfrob : IsFrobeniusGroup (derivedInG S) …) : g1g ≤ …`
を実証明 (covering + 計数 + 算術の本物の数学は全部ここ)。estimate は
`hfrob`-parameterized 版 `…_of_partner_frobenius` を並設 (現行 statement は不変のまま
sorried 維持、consumer 移行後に deprecate)。

**Phase 3 — relayering (hub 調整含む、Phase 1-2 後)**: 新 leaf `S12_Noncoherence.lean`
(pair leaf import) に無条件 estimate + S_not_coherent + no_typeV_maximal を移設。
FTS の (13.2.a) trio (card_kappaHall_lt_of_isTypeP1 / isTypeP2_of_typeP_kappaHall_lt /
card_kappaHall_lt_of_isTypeIIIorIV) は Phase 1 後の残消費を調査の上、§13 層下流へ移設
(S15/S16 = lane b/c の消費があれば repoint、hub flag)。FTS は char-free packaging
(ThmC ベース) に純化。

## 参照
- 9079 (pair route、(10.7)' landed) / 9080 ((8.17) mis-layering、同型の発見)
- notes/peterfalvi/s12_10_8_noncoherence.md 2026-07-06 audit (prime-TI 必要説は
  pair route で supersede 済; 本 issue が現行正)
- 6b08f22d ((8.11) 閉鎖 = hB の入力)
