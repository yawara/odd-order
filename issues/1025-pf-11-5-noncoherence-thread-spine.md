---
id: 1025
slug: pf-11-5-noncoherence-thread-spine
title: "Pf (11.5)/(11.6) chain を (11.3) 非coherence で hypothesis 化 → spine residual axiom-clean"
created: 2026-07-12
---

# Pf (11.5)/(11.6) chain を (11.3) 非coherence で hypothesis 化 → spine residual axiom-clean

## 背景 (2026-07-12 lane-a 再開時、1024 完遂後の frontier トレースで確定)

FT spine (`feitThompson`) の**唯一の bare sorry** = `card_kappaHall_lt_of_isTypeIIIorIV`
(AxiomsCheck:7150)。その residual = **`exists_zeta_residual_not_orthogonal_H0C_of_refuter`**
(S13_Orthogonality:1010、Pf (11.8) refuter core)。

`#print axioms` トレースで判明した residual の dirty root は **(10.8) import-DAG knot のみ**:

- `secondDerived_eq_HC` (11.5、S13_Lemmas113To115:908) が dirty。root =
  `HC_le_secondDerived` (11.5 reverse) → `coherent_quotient_bound` (11.4) →
  `S_H0C_not_coherent` (11.3) → **`S12.S_not_coherent` (10.8、S12_MaximalBasic:1386、
  do-not-fill generic partner 経由で sorried)**。
- ⚠ **honest heir は既に存在**: `S12.S_not_coherent_unconditional` (S12_Noncoherence、axiom-clean)。
  だが **S12_Noncoherence は S13_Lemmas113To115 を import (downstream)** ゆえ、上流の
  `coherent_quotient_bound` は cite 不可 (cycle)。= 純粋な import-DAG 由来 sorry (issue 1020 圏)。
- residual の他の入力は **CLEAN**: `coherent_SOf_HC` (§14 Sibley S(HC) coherence) /
  `coherent_SOf_H0C_of_glued` (world-bridge engine) 双方 axiom-clean。

∴ **(10.8) knot を解けば residual が axiom-clean → `card_kappaHall_lt_of_isTypeIIIorIV`
(spine 唯一 bare sorry) が閉じる**。

## 鍵: spine は既に clean な (11.3) を供給している

`exists_zeta_residual_not_orthogonal_H0C_of_refuter` は **`hrefute` パラメータ**
(= (11.3) 非coherence `∀ s13hyp, ¬ Nonempty (IsCoherent … (SOf H0C) …)`) を既に取る。
spine consumer `w2_lt_w1_of_hypothesis_H0C_unconditional` (S13_TypeDetermination:62) は
`hrefute := S_H0C_not_coherent_unconditional` (**axiom-clean**) を供給。

だが residual は内部で `secondDerived_eq_HC` (line 1068) と
`coherent_SOf_H0C_of_column_identities` (line 1087) を使い、これらが `hrefute` を経由せず
sorried `S_H0C_not_coherent` に落ちている。⟹ **内部 chain を hrefute 経由に付け替えれば clean**。

## やること (additive・非破壊・proof 複製なし、import bottom-up)

各 theorem X を `X_of_noncoherent (hnc : ¬ Nonempty (IsCoherent … (SOf H0C) …)) := [本体、
内部 (11.3)-cite を hnc に置換]` に factor し、legacy 版 `X := X_of_noncoherent
(S_H0C_not_coherent _hG hyp)` を wrapper で残す。既存 consumer は wrapper を呼ぶので**無変更**。

**S13_Lemmas113To115** (最上流):
- [ ] `coherent_quotient_bound` (11.4) — 内部 `S_H0C_not_coherent` (line 191、hBncoh) を hnc に
- [ ] `HC_le_secondDerived` (11.5r) — `coherent_quotient_bound` cite を `_of_noncoherent hnc` に
- [ ] `secondDerived_eq_HC` (11.5) — `le_antisymm _ (HC_le_secondDerived_of_noncoherent hnc)`

**S13_CoreStructure**:
- [ ] `H0_eq_Hprime` (11.6) — `secondDerived_eq_HC` cite (line 936) を `_of_noncoherent hnc` に
- [ ] `chief_H0_eq_bot` (11.7) — `H0_eq_Hprime` cite (line 1163) を
- [ ] `chief_N_eq_bot` — `chief_H0_eq_bot` cite (line 1212) を
- [ ] `C_eq_cSub` — `chief_N_eq_bot` cite (line 1234) を
- [ ] `columnSum_muColumnChar_mem_sOf_H0C` — `C_eq_cSub` cite (line 1424) を

**S13_Orthogonality** (downstream):
- [ ] `coherent_sOf_H0C` — caseA branch の `columnSum…`/`C_eq_cSub` を
- [ ] `coherent_SOf_H0C_of_column_identities` — 内部 `coherent_sOf_H0C` を
- [ ] `exists_zeta_residual_not_orthogonal_H0C_of_refuter` — line 1068 (`secondDerived_eq_HC`) +
      line 1087 (`coherent_SOf_H0C_of_column_identities`) を `_of_noncoherent … (hrefute s13hyp)` に

## 完了条件

- 各 file build green。最終 `#print axioms exists_zeta_residual_not_orthogonal_H0C_of_refuter`
  が sorryAx-free (propext/Classical.choice/Quot.sound のみ)。
- `card_kappaHall_lt_of_isTypeIIIorIV` / spine を再 assert (AxiomsCheck 登録)。
- ⚠ feitThompson が完全 axiom-clean になるとは限らない (§14/§15/§16 cross-lane の推移 sorry が
  別途残る可能性)。本 issue は **lane-A の spine 貢献 (= 11.5/11.6 chain の 10.8-knot) を閉じる**。

## 参照

- issue 1020 (partner/unconditional 移行)、1024 (typeP_Galois W2)、9083 (9.11 Phase E)
- `S12.S_not_coherent_unconditional` (S12_Noncoherence)、`S_H0C_not_coherent_unconditional`
  (S13_TypeDetermination)、`w2_lt_w1_of_hypothesis_H0C_unconditional`

## 注記

- hnc の型 = `¬ Nonempty (IsCoherent hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)`
  (= `S_H0C_not_coherent _hG hyp` / `hrefute s13hyp` 双方の型)。
- legacy wrapper が sorried のまま残るのは意図どおり (他の legacy consumer 用)。spine path のみ clean 化。
- CLAUDE.md「sorry-free 化の着地を目的にしない」に留意しつつ: 本件は **honest math (unconditional 10.8)
  が存在するのに import-DAG で spine が cite できず bare sorry が残る**状況の解消 = spine の honest 化。
