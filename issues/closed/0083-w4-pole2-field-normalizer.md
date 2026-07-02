---
id: 83
slug: w4-pole2-field-normalizer
title: "W4 (lane-h): POLE-2 field_normalizer §14–16 char cascade + §15 S&T"
created: 2026-06-25
---

# W4 (lane-h): POLE-2 field_normalizer §14–16 char cascade + §15 S&T

## 背景

FT フロンティア再設計 (2026-06-25 relane #9、正本 `notes/meta/ft_frontier_remap_2026_06_25.md`)
の **フロント W4** = lane-h 担当。**Arm B (最終矛盾の独立アーム)** — `field_normalizer_structure`
(Pf 14.2, POLE-2) を構成し App.C Theorem C が消費して p≤q を出す。W1 と upstream gate を共有しない
完全独立フロント (検証 CLAIM B)。

## やること

- [ ] `field_normalizer_structure` の §14–16 char cascade (`OddOrder/Peterfalvi/S16_NonExistenceG.lean`):
      `exists_MHypothesis` (3338)、`betaM_expansion` (1878)、`generic_character_bound` (1970)、
      `main_size_bounds_structural` (1797)、`T_side_caseB_facts` (133)、`U_cyclic` (2361)、
      `V_cyclic` (2441)、`orthogonality_switch`、`exists_LHypothesis`。
- [ ] §15 setup (`S15_SAndT_Setup.lean`): `basic_structure_gated` (283)、`c_eq_one` (612, 13.12)、
      `caseB_order_u` (779, 13.15)。
- [ ] §15 S&T 構造 (`S15_SAndT.lean`): `normalizer_W1` (140, 13.16)、`card_Q_eq` (426)、
      `tConjugate_fitting_data` (443)、`card_LF_coprime_pq` (463)、`complement_inf_Q_structure` (892, 13.17)。
      §13.17 構造コアは Frobenius/Hall/centralizer 群論で一部 sorry-free 済
      (`notes/peterfalvi/s13_17_structural_program.md`)。

## 完了条件

`field_normalizer_structure` が Nonempty を sorry-free に返し、`nonexistence_of_G` →
`final_contradiction` が POLE-2 経由で False を出す (Arm B 完了)。

## 参照

- 正本: `notes/meta/ft_frontier_remap_2026_06_25.md` §2 (W4)
- 主所有: `OddOrder/Peterfalvi/{S15_SAndT, S15_SAndT_Setup, S16_NonExistenceG}.lean`
- 関連: `notes/peterfalvi/s13_17_structural_program.md`、旧 issue 2009 (POLE-2、stale pointer、要再 scope)

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

W4 charter superseded: lane h は不在 (worktree = a/b/c、lane d は 2026-07-02 退役)。§15–16 は lane c 所有;
live pointer = issues/pending/2009 + issues/4001。canonical = notes/meta/ft_lane_reallocation_2026_06_28.md
(検証 2026-07-02: git worktree list = main/a/b/c)。
