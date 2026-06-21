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

## やること (lane-c 単独で進められる部分)

- [x] (kickoff) `key_inequality` (14.8) 実証明 + `main_size_bounds` conjunct 3 実証明 +
      `MHypothesis_kernel_cyclic` を (14.11)`K_eq_V_index_pq` + `V_cyclic` へ wire (commit ff2338a5)。
- [ ] `K_eq_V_index_pq` の `e=pq` 枝 — `MHypothesis` を `complement_card_eq_pq` field で enrich
      (lane-c 所有 carrier、`LHypothesis.typeI_complement_card_eq_pq` と対称)。
- [ ] `exists_MHypothesis` (14.10) の構造 skeleton — `T_typeII` (14.9) +
      `typeII_overNormalizer_frobenius` を T/V 側に適用、Dade fields を named obligation に isolate。
- [ ] 残り (A norm-cascade char / B §13 cyclic / C 直交 dichotomy) は Lane B の §13 Dade
      producer 着地後に cite で実証明化。

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
