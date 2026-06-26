---
id: 2027
slug: lane-h-w1-reverse-bridge-carrier
title: "lane-h W1 carrier: reverse-bridge rank-1 carrier (π(W₁)⊆κ(M)) を file-disjoint 生産"
created: 2026-06-26
---

# lane-h W1 carrier: reverse-bridge rank-1 carrier (π(W₁)⊆κ(M)) を file-disjoint 生産

## 背景

**relane #11 (2026-06-26, ユーザー裁可 AskUserQuestion = 「W1 に火力集中」)**: 6 エージェント並列監査
(workflow `wf_1cb6284d-bb2`) で relane #10 を再点検 → 構造は健全だが **4 レーン中 3 つ (b/c/h) が
ungated 作業ほぼ 0 で starve**、唯一 lane-f の W1 群論だけが ungated frontier と判明。特に lane-h の
W2 (S14_MaximalI) は lane-b char に完全従属で独立価値が低かった (W4 char 飽和から逃げて W2 char 飽和に
着地)。ユーザー裁可で **lane-h を lane-f の W1 reverse-bridge carrier 生産に振り替え** (火力集中)。

監査で reverse bridge の crux 構造が確定:
- Prop 16.1 の reverse 3 bridge `hIIP2` / `hIIIIVP1` / `hVP1` (S16_MainResults `proposition_type_classification_of_inputs`)
  は全て **carrier 事実 `π(W₁) ⊆ κ(M)`** に bottom out。
- これは `typePData_kappa_nonempty_of_rank1` (S16_MainResults:~2148/2169) が消費し、その crux は
  **rank-1 条件 `∀ p ∈ π(W₁), pRank_M p = 1`** (issue 8015 §「2026-06-20 kappa bridge 精密分解」条件 3 =
  「carrier-gated・真の残 crux」)。σ-complement 半分 `typePData_W1_prime_not_mem_sigma` は済 (2d59f42d)。

## やること

- [ ] **rank-1 carrier `∀ p ∈ π(W₁), pRank_M p = 1` を生産** (= reverse bridge の真の残 crux)。
      issue 8015 の精密分解 (条件 1 σ-complement[済] / 条件 2 / 条件 3 rank-1) を読み、rank-1 を埋める。
      carrier = `Section16MaximalPair` / `Section16TypePStructure` (FeitThompson.lean、def-unit 共有)
      の type-P データから rank-1 を導く群論。
- [ ] **file-disjoint 厳守**: lane-f は `S16_MainResults.lean` (reverse bridge 本体 + forward pair) を
      active 編集中。lane-h は **carrier 補題を別ファイル** (`S16_PairIntersection.lean` [227 行/0 sorry、
      格好の host] or 新 BG leaf) に隔離生産し、lane-f が cite する。S16_MainResults / FeitThompson carrier
      を直接編集する必要が出たら **def-granularity で lane-f と調整** (notes/issue、co-edit 回避)。
- [ ] 自分のスコーピング survey を先に回し (lane-h が W2 で issue 0081 にやったように)、rank-1 の正確な
      ステートメント・host ファイル・cite 点を確定してから着手。

## 完了条件

`typePData_kappa_nonempty_of_rank1` が要求する rank-1 carrier が sorry-free + axiom-clean で landing し、
lane-f の reverse 3 bridge (hIIP2/hIIIIVP1/hVP1) の cross-lane gate が外れる (= Prop 16.1 の reverse 完成に前進)。

## ⚠ 2026-06-26 lane-h survey: **本 issue の前提 (rank-1 carrier) は STALE** — hub 再判断要請

issue 2027 が指示する通り着手前に scoping survey を実施 (Explore ×2 + #print axioms 検証)。結果、
**「rank-1 が carrier-gated な残 crux」という前提 (issue 8015 2026-06-20 の DAG 分析) は lane-f が
既に supersede 済**と判明:

**rank-1 は carrier 不要・sorry-free で完成済** (#print axioms で 4 本とも 3-axiom allowlist 確認):
- `isTypeP_of_typePData_of_card_W1_prime` (S16_MainResults:2314, **axiom-clean**): bare `TypePData M` +
  `|W₁| 素数` ⟹ `IsTypeP M`。rank-1 を **carrier 不要**で導出 — `q∤|M'|` (← `q∤|W₂|` cyclic-W 論法
  `typePData_not_dvd_card_W2_of_card_W1_prime` + centralizer count `prime_dvd_card_inf_centralizer_of_mem_normalizer`)
  → `typePData_pRank_eq_one_of_not_dvd_card_derived` (2149) で `r_q(M)=1` → `typePData_kappa_nonempty_of_rank1` (2054)。
- `isTypeP_of_isTypeV` (2171, axiom-clean): 型 V (U=⊥ ⟹ M'=M_F Hall coprime) ⟹ IsTypeP。
- `typePData_kappa_nonempty_of_rank1` (2054, axiom-clean) / `kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot`
  (332, axiom-clean, U=⊥⟹κ=σ') も完成済。型 II/III/IV/V の **IsTypeP 半分は全て sorry-free** (`isTypeP_of_isTypeII/III/IV` 2347/2352/2358)。

⟹ **「W₁=κ-Hall を carrier から供給」(issue 8015 の懸念 [[typep-w1-kappa-carrier-not-derivable]]) は不要だった** —
素数 |W₁| (型 II/III/IV は (8.6.a) `caseB_typeP_prime_W1`、型 V は U=⊥) から rank-1 が直接出る。
**循環 (issue 8015 DAG「carrier も Prop 16.1 から作られる」) は回避され、本 issue の file-disjoint rank-1
carrier 生産タスクは moot。**

**reverse bridges の真の残ギャップ = P1/P2 型判定** (`hIIP2`/`hIIIIVP1`/`hVP1` @S16:2905-2910、コメントは
stale な「carrier W₁=κ-Hall, issue 8015」のまま):
- `hIIP2`: 型 II ⟹ IsTypeP**2** (=IsTypeP ∧ **κ≠σ'**)。IsTypeP 済、残 = **κ≠σ' を型 II 構造から** (N_G(U)⊄M)。
- `hIIIIVP1`: 型 III/IV ⟹ IsTypeP**1** (κ=σ') ∧ MF≠Mσ。IsTypeP/MF≠Mσ 済、残 = **κ=σ' を型 III/IV から** (N_G(U)≤M)。
- `hVP1`: 型 V ⟹ IsTypeP1 ∧ MF=Mσ。IsTypeP/MF=Mσ (`mf_eq_msigma_of_typePData_U_eq_bot`) 済、残 = κ=σ' (U=⊥、
  `kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot` 既存 ⟹ ほぼ wiring)。
- ⚠ U≠⊥ は P1/P2 を一意に決めない (型 II=P2 も III/IV=P1 も U≠⊥)。判定は N_G(U)≤M 等の **deep BG 分類** =
  `isTypeP2_of_hall_subgroupOf_ne_bot` (872) 等の (κ∪σ)ᶜ-Hall U に依存し、**全て S16_MainResults (lane-f 所有) 内**。

**⟹ file-disjoint な lane-h ピースは存在しない**。残作業 (型 II κ≠σ' / III-IV κ=σ' の分類 wiring) は lane-f の
S16_MainResults 分類機械と不可分。憶測的な重複 rank-1 carrier ([[scaffold-sorry-free-not-done]] = 何も消費しない
scaffold) は作らない方針。

### 要請 (hub 判断)
- [ ] 本 issue (file-disjoint rank-1 carrier) を **stale-premise で close** し、lane-h を再配置。選択肢:
  (A) lane-h ⟶ lane-f と co-edit 調整して reverse bridges の P1/P2 wiring を直接担当 (S16_MainResults co-edit、
  def-granularity 分割)。(B) lane-h ⟶ 別の ungated セグメント (W2 で示した通り (12.17) 系に ungated group-theory
  が残存する可能性: `exists_typeICovering` の §8 covering は char/§8 gated だが、他に未抽出の群論があるか hub 査定)。
  (C) lane-h stand-by + 自己復帰モニター。
- 補足: lane-h は本セッションで **旧 W2 `theorem88_caseB_holds` (12.17) を honest reduction 化** (commit `503d2bd1`、
  normalizer bridge axiom-clean) — relane #11 の「W2=char 従属で独立価値低」評価に反し ungated group-theory 核が
  実在した。issue 0081 参照。

## 参照

- 親 issue: 8015 (Prop 16.1 type-classification, lane-f 所有。本 issue は reverse carrier 半分を lane-h が担当)
- 監査: workflow `wf_1cb6284d-bb2` (relane #10 soundness, verdict=minor-adjust)、merge_monitor 現状メモ (relane #11)
- carrier: `Section16MaximalPair`/`Section16TypePStructure` (FeitThompson.lean)、[[typep-w1-kappa-carrier-not-derivable]]
- consumer: `typePData_kappa_nonempty_of_rank1` (S16_MainResults:~2148)、reverse bridges @2541-2544
- 旧 W2 (theorem88_caseB_holds, S14_MaximalI) は lane-h 離脱で driver/await に降格 (char-gated、issue 0081)
