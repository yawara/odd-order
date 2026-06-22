---
id: 4001
slug: s16-lane-c-frontier
title: "Pf §16 non-existence: lane-c frontier + Lane B gate map"
created: 2026-06-22
---

# Pf §16 non-existence: lane-c frontier + Lane B gate map

## 背景

4-lane 再編 (2026-06-21) で lane-c = Pf §16 (`S16_NonExistenceG.lean` 編集 tail + POLE-2
`field_normalizer_structure`)。`field_normalizer_structure` の dispatch tree は sorry-free
(lane-h 成果)。残 13 sorry はすべて dispatch が cite する named obligation で、ほぼ Lane B
(Pf §13 char/Dade、issue 1004 section16CharacterData) に bottom-out する。
正本 = `notes/peterfalvi/s16_nonexistence_gate_map.md`、POLE-2 = issue 2009。

## 2026-06-22 再開: 基盤 char-infra ピボット (ユーザー裁可)

全数 audit で S16 内に ungated 証明仕事が無いと再確認 (lane-b 0 commits 先行、η-grid free field、
(7.5)/(3.9) absent)。ユーザー選択「基盤 char インフラ構築」に従い、§14-16 endgame を gate する
foundational arithmetic backbone を構築 (η free-field に非依存、signature 先行整備):

- [x] `one_le_norm_signed_paired_sum` — (3.9)/(14.11.3) parity core (commit `2d517956`)。
- [x] `all_pm_one_and_card_of_odd_sq_sum_le` — (14.11.2) sum-of-squares core (commit `9f17b010`)。
- 真の long pole = **S15 η-grid carrier の honest 化 (lane-h)**。詳細 + lane-h への精密 ask =
  `notes/peterfalvi/s16_nonexistence_gate_map.md` 冒頭セクション + issue 4003。

## やること (lane-c 単独で進められる部分)

- [x] (kickoff) `key_inequality` (14.8) 実証明 + `main_size_bounds` conjunct 3 実証明 +
      `MHypothesis_kernel_cyclic` を (14.11)`K_eq_V_index_pq` + `V_cyclic` へ wire (commit ff2338a5)。
- [x] `K_eq_V_index_pq` の `e=pq` 枝 — `MHypothesis` を `complement_card_eq_pq` field で enrich
      (lane-c 所有 carrier、`LHypothesis.typeI_complement_card_eq_pq` と対称)。**DONE commit `aff0bc2a`**。
- [x] `caseB_for_S` (14.6) — `caseB_for_T` の opaque-Prop scaffold を mirror、`S15.caseB_order_u_data`
      (13.15) を cite。**DONE commit `aff0bc2a`** (文書順で最上流の lane-c 着地点)。
- [ ] `exists_MHypothesis` (14.10) の構造 skeleton — **blocked**: `typeII_overNormalizer_frobenius`
      が S/U-side ハードコード (S15:1712)。V-side 構築には **T/V-side dual** が要る = lane-h ask
      (gate map「精密 gate 特定」+ 新 issue)。dual 着地後は `exists_LHypothesis` の機械的 dual で
      構造部 sorry-free 化可。
- [ ] 残り (A norm-cascade char / B §13 cyclic / C 直交 dichotomy) は Lane B/H の §13 Dade
      producer + η-carrier (issue 4003) 着地後に cite で実証明化。

## 2026-06-22 resume の結論: §16 残 11 sorry は全て lane-h gated (原文レベル検証済)

文書順で lane-c が忠実に閉じられる sorry は上記 2 本で尽きた (caseB_for_S 211 / K_eq_V e=pq 2012)。
残 11 (`T_side_caseB_facts` 136 / `T_typeII` / `main_size_bounds_structural` / `betaM_expansion` /
`generic_character_bound` / `normCascadeBound_of_charData` / `U_cyclic_and_Q_elemAbelian` /
`V_cyclic` / `caseB_character_contradiction` / `orthogonality_switch` / `exists_MHypothesis`) は
全て lane-h の §13/§14 char/構造理論に bottom-out (T-side dual / η-carrier / Dade)。
正本 = `notes/peterfalvi/s16_nonexistence_gate_map.md`「更新 (2026-06-22, resume session)」。

## Lane B / hub への ask (signature-first, 正しければ sorried 可)

`section16CharacterData` producer (issue 1004) の landing 時に以下を faithful signature export:

- S-side case-(9.7.b) 判定 (`caseB_for_S`) — `character_degree_analysis` の dichotomy 出力
- `U_cyclic` / `Q_elementaryAbelian` / `V_cyclic` (13.2.a/b)
- (14.11.2)(14.11.3) β_M η-expansion + generic bound、(14.11.4) norm 不等式 ((7.5) Frobenius 内積)
- (14.14) 直交 dichotomy、(14.16) β_L^τ η-expansion contradiction、`T_typeII` (14.9)

## 完了条件

`S16_NonExistenceG.lean` の 13 sorry が解消 (lane-c 単独部 + Lane B producer cite)。
`field_normalizer_structure` / `nonexistence_of_G` が unconditional。`lake build OddOrder
OddOrder.AxiomsCheck` 緑。

## 参照

- `notes/peterfalvi/s16_nonexistence_gate_map.md` (正本・13 sorry の gate 詳細)
- issue 2009 (POLE-2 `field_normalizer_structure`)、issue 1004 (section16CharacterData, Lane B)
- commit ff2338a5 (kickoff: (14.8)/(14.11.1)/(14.11) wiring)
