---
id: 92
slug: hub-reallocate-lane-d-to-s15-setup
title: "HUB: lane d 再配分 — γ 上流 S15_SAndT_Setup へ (BG §14–16 deliverable 完成)"
created: 2026-07-01
---

# HUB: lane d 再配分 — γ 上流 S15_SAndT_Setup へ (BG §14–16 deliverable 完成)

## 経緯 (2026-07-01, ユーザー裁定)

hub 監査で lane d の旧クラスタ δ (BG §14–16 → Peterfalvi interface) の **FT deliverable が実質完成**と確定:

- Peterfalvi spine + `FeitThompson.lean` が cite する BG §14–16 endpoint は**全て sorry-free で消費済**:
  `BG.Ch4.S14.{kappa, IsTypeP, IsTypeP1, IsTypeP2, IsTypeF, zTilde, Mtilde, typeP_duality,
  genuineSigmaDecomposition, typeP_derivedInG_isComplement_kappaHall, card_kappaHall_ne_one,
  exists_kappaHall_invariant_complement_to_MF}` / `BG.Ch4.S15.maxNilpotentNormalHall_*` (M_F 機構) /
  `BG.Ch4.S16.{proposition_type_classification, not_isTypeI_of_isTypeNonI, isTypeII_of_isTypeP2,
  mainSubgroup_eq_Msigma, exists_peterfalviType, typePData_of_inputs, typeP_pair_W_structure}` /
  `bgTheoremE_cover_data` (8.17) / `theoremD_*` / `theoremE_*` / `FT_signalizer`。
- lane d の残 owned sorry (7 §14–16 + 8 AppD/AppE) は marginal FT value 低: Thm A/B monolith
  (`theoremA_maximal_structure`/`theoremB_U_and_A_tame`) は faithful axiom-clean variant
  (`theoremA_maximal_structure_faithful` 等) が spine を既に served ゆえ honest need-path 外 /
  `tau2_transfer_constraint` (15.8) は docstring 消費のみ / `aSets_support_slice` ・
  `nonidentity_covered_by_sigma_pieces` ・ `sigmaLength_one_frobenius_type` は unconsumed /
  AppD/AppE は off-path。

## 裁定 = γ 上流 S15_SAndT_Setup を lane d へ

深い char 終盤 backlog は γ (lane c, 37 sorry) と α (lane a, 27 sorry) に集中。**binding pole = γ**。
γ の import chain は **`S15_SAndT_Setup → S15_SAndT → S16_NonExistenceG`** (線型・上流→下流)。

- **lane d の新・主焦点 = `OddOrder/Peterfalvi/S15_SAndT_Setup.lean`** (16 sorry、γ import-最上流)。
  中身 = §15 S&T setup: `basic_structure_gated` (13.1.d/e)・`character_degree_analysis`・
  `lambda_forces_T_caseB` 等。lane d は **upstream-first** で self-contained に埋める。
- **lane c は下流を保持** = `S15_SAndT.lean` (12 sorry, 13.16/13.17) + `S16_NonExistenceG.lean`
  (9 sorry, orthogonality_switch 14.14 / exists_MHypothesis 14.10 / betaM_expansion 14.11.2 /
  T_typeII 14.9)。lane c は S15_SAndT_Setup の (sorried でよい) signature を cite = signature contract。
- lane d は **BG/** 所有を dormant 保持** (必要時のみ; 残 §14–16 endpoint は当面 deprioritize)。

## lane c への指示

- **S15_SAndT_Setup.lean の編集を停止**。未コミット WIP があれば commit/stash して lane d に引き継ぐ
  (working-tree に残すと lane d との衝突源)。以後 S15_SAndT_Setup は lane d 所有 = lane c が編集したら逸脱。
- 下流 (S15_SAndT / S16_NonExistenceG) を継続。S15_SAndT_Setup の endpoint は sorried のまま cite してよい
  (signature contract、body 完成を待たない)。

## lane d への指示

- 起動時 `git merge main` で本 issue + 更新後の所有マップを取り込む。
- 主焦点を `S15_SAndT_Setup.lean` に切替。upstream-first で最上流 sorry から honest に埋める。
- BG/** は dormant (触るのは genuine に必要なときのみ)。S15_SAndT / S16_NonExistenceG は編集しない (lane c 所有)。
- ODD_ISSUE_BASE=4000 は不変。

## 状態

- [x] ユーザー裁定 = γ 上流 S15_SAndT_Setup へ
- [x] 所有マップ更新 (`ft_lane_reallocation_2026_06_28.md` / `merge_monitor.md` / cron / memory)
- [ ] lane c が S15_SAndT_Setup を停止・引き継ぎ (次 sync 時)
- [ ] lane d が S15_SAndT_Setup へ切替 (次 sync 時)
