---
id: 1021
slug: typev-forces-coherence
title: "typeV_forces_coherence 実装 — (10.10.1)-(10.10.4) の §6-route (v2 方式で S12_Noncoherence に)"
created: 2026-07-11
---

# typeV_forces_coherence 実装 ((10.10) の残 genuine math)

**背景**: (10.10) 無条件版 (`no_typeV_maximal_unconditional`、S12_Noncoherence) の唯一の
sorryAx 残渣 = `typeV_forces_coherence` (S12_MaximalIII_IV_V:~1650、bare sorry)。
book (10.10) の「type V なら 𝒮 coherent」((10.8) との矛盾用)。

## 設計 findings (2026-07-11 tick¹⁵ survey)

- **(8.7)-trichotomy は TypeVData.alternative field に忠実に在る**
  (MaximalSubgroupType:287-296): (a) H# TI / (b) ∃p: w₁|p−1 + O_{p'}(H) cyclic /
  (c) |O_p(H)| = p³ + w₁|p+1 + O_{p'}(H) cyclic。
- **H は data-独立** (H_eq = maxNilpotentNormalHall) なので dV↔hyp.typeP の
  trichotomy 転送は card/H-invariance で clean。type V は U = ⊥ → M' = H。
- **book の場合分け**: (a) → (6.8) で coherent / (b) → (6.5.c) で coherent /
  (c) → (10.10.1)-(10.10.4) + (10.9) で **False** (exfalso → coherent)。
- ⚠ **S14-(12.6) template は Frobenius-特化** (`nonempty_coherent_SOf_bot_of_index_dvd`
  は hF : IsFrobeniusGroup ↥L H C を要求) — type V の M = H⋊W₁ は Frobenius で
  ない (C_H(w) = W₂ ≠ 1)。book は **Hypothesis (6.4)** route ((8.15): (6.4) holds for
  (L,K,M) := (M, M', 1))。⟹ S08 の (6.4)-side engine ((6.5.b)/(6.5.c) の
  Hypothesis-(6.4) 版) を survey して使う (次 tick)。
- **配置 = S12_Noncoherence** (v2 方式): 原 sorry の home (S12_MaximalIII_IV_V) は
  (11.x)/(6.x) 消費機構の上流 (S13_Lemmas113To115 は下流) — 同じ mis-layering。
  原 sorry には superseded 警告を付け、v2 が消費する。
- (c)-refutation は (10.9) (`S12_Prop109` 系?) + μ-算術 — 最深部、別 sub-issue 可。

## 手順
1. S08 の (6.4)-Hypothesis side engines survey ((6.5.b)/(6.5.c)/(6.8) interfaces)。
2. S12_Noncoherence に typeV branch (a)/(b) 実装。
3. (c)-refutation ((10.10.1)-(10.10.4)、(10.9) 消費)。
4. no_typeV_maximal_unconditional を新版に配線 → sorryAx-free 化。
