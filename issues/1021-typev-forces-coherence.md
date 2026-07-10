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

## 2026-07-11 tick¹⁶ — 部品 survey 完了 + transfer lemma landed

- `TypeVData.alternative_transfer` landed (MaximalBasic、axiom-clean 見込み) —
  (8.7)-trichotomy を hyp.typeP へ転送。
- **case-(a) 設計確定**: SibleyDadeHypothesis は **H#-TI が field** → (a) 専用。
  組立部品: split = M_complement (U=⊥ で M' = H)、dade = S04.Hypothesis.of_isTISubset
  (S09_FrobeniusSibley の sibleyDadeHypothesis_of_frobenius が producer template、
  ただし cases-branch は Frobenius でなく **h46-certain-type** 側 —
  certainTypeHypothesis_of_typeP_kappaHall (FTS:1160) で構成)。
  出力の transport: 家族差分は (M')# = H#-supported (type V) なので
  `isCoherent_of_supportedSpan_le` (S13_Lemmas113To115:318) で A₀ 版へ。
  tau-agreement は S04.restrict 系。
- **case (b)**: (6.4)-general の (6.5.c) — SibleyDade (TI) 外。候補 =
  (11.4)/(11.5) filtration route (S13_Lemmas113To115、type II/III/IV 向けに proven —
  type V 適用可否の確認が次) or S08_SixTwoGeneral の非-TI 形。
- **case (c)**: (10.10.1)-(10.10.4) + (10.9) refutation — 最深、最後。

## 2026-07-11 tick¹⁷ — case-(a) 供給連鎖の完全 map (残る設計点 1 つ)

- **h46 producer 発見**: `Hypothesis.toHypothesis46` (S12_Core:1057、hyp 自身の完全 (4.6)!)。
  type V では typePA = ⋃_{x∈H#}C_{M'}(x)# = **H#** (M' = H) なので A-param も一致。
  side conditions: W₂ prime = w2_prime ✓ / W₂ ≤ [H,H] = W2_le (≤ secondDerived) ✓ /
  coprime = hall ✓。K = H ✓ (M' = H)。
- **SibleyDade 組立部品**: split = M_complement (U=⊥) / dade = S04.of_isTISubset
  ((a)-TI から、H a = ⊥ ✓ dade_H_eq_bot) / S_eq = inducedFamily 同定 /
  cases = Or.inr ⟨toHypothesis46, …⟩。
- **⚠ 残る設計点**: `h46.dade = dade` field — toHypothesis46.dade は A₀-Dade の
  restrict (H(a) = 継承 signalizer、⊥ とは限らない) vs TI-構成 dade (H ≡ ⊥)。
  同定には dadeHypothesis_eq_of_forall_H_eq_bot (9079 part 1、両側 H≡⊥ 要) —
  つまり **hyp.dadeData の H(a) が type-V-case-(a) で ⊥ かは data 依存**。
  解決候補: (i) hyp.dadeData 構築 (exists_hypothesis_of_typeIIIorIVorV、axiom-clean!)
  の H(a)-fields を実測 — (8.15)-構成が type V/case-(a) で ⊥ を選んでいれば同定可;
  (ii) さもなくば Sibley 側を h46.dade ベースで組む (dade_H_eq_bot を h46 側から) —
  case-(a) の TI が R(a) = 1 を強制する事実 ((2.3)-route) を経由。
- 出力 transport: isCoherent_of_supportedSpan_le + S_eq→inducedFamily ✓ (前 tick 済)。
