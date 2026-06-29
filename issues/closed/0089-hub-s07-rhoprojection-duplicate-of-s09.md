---
id: 89
slug: hub-s07-rhoprojection-duplicate-of-s09
title: "HUB: S07_RhoProjection は S09 chiRho の完全重複 — 削除可否 (carve-out 0087 reversal)"
created: 2026-06-30
---

# HUB: S07_RhoProjection は S09 chiRho の完全重複 — 削除可否 (carve-out 0087 reversal)

## 発見 (lane b, 2026-06-30 loop³⁸ で 🛑 STOP+報告)

lane b が「**`S07_RhoProjection.lean` の (7.1)-(7.3) は `S09_NonexistenceCertain.lean` の `chiRho`
機構の完全重複**」と判明して STOP。**`S09` = 教科書 §7** (S番号=§番号+2)。§7 ρ machinery は `chiRho`
名で (7.1)-(7.8) 既に完備。

### hub 検証 (✅ b の主張は正しい)
- **S09 に chiRho 機構実在**: `Hypothesis71` / `chiRho` / `chiRho_dadeImage_eq` / `chiRhoCF` /
  `chiRhoCF_eq_adjointAverageFun` / `chiRho_adjoint` / `chiRho_norm_sq_le` /
  `chiRho_integral_inequality` / `FamilyHypothesis71` / `Hypothesis76` / `Hypothesis78` /
  `NormEstimates` — (7.1)-(7.8) 全部 (lane γ が (14.11.4) で常用)。
- **S07_RhoProjection の consumer = AxiomsCheck のみ** (他に cite ゼロ、grep 確認)。
- **footprint**: `S07_RhoProjection.lean` (286 行) は AxiomsCheck からのみ import される孤立 leaf
  (他の S07_* = coherence 系は無関係)。削除対象 = この 1 ファイル + AxiomsCheck の `rho*` ガード
  11 本 (6725/6726/6881/6887-6889/6894/6895/6934/6935/6941) + import 1 行。

### S07 ↔ S09 重複対応 (b 報告)
| S07 (冗長) | S09 既存 |
|---|---|
| `rhoValue`/`rhoClassFun`/`rho` | `chiRho`/`chiRhoCF` |
| `rho_dadeMap` (7.2.a) | `chiRhoCF_dadeImage_eq` |
| `rhoValue_eq_adjointAverageFun` | `chiRhoCF_eq_adjointAverageFun` |
| `rho_adjoint` (2.7) | `chiRho_adjoint` |
| `rho_normSq_le` (7.2.b) | `chiRho_norm_sq_le` |
| `rho_normSq_le_restrict` (7.3) | `chiRho_integral_inequality` |

原因: 旧 note 前提「S09 chiRho は family 特化、一般 ρ 不在」が誤り (`Hypothesis71` は general
single-L の (7.1) そのもの)。正本 memory `s09-is-section7-chirho-complete`、
[[verify-port-state-by-number-not-coq-name]]。

## ✅ 裁定 + 実施 (2026-06-30, ユーザー = 判断 D 削除)

ユーザー裁定 = **判断 D (削除)**。hub が main で実施済:
- `OddOrder/Peterfalvi/S07_RhoProjection.lean` 削除 (`git rm`)
- AxiomsCheck.lean の rho* ガード 11 本 + import 1 行削除
- carve-out 0087 撤回 (merge_monitor.md / ft_lane_reallocation_2026_06_28.md 更新、HOLD 解除)
- build green (3888 jobs、S07 削除で −1) / AxiomsCheck OK / sorry 124 不変 / 残存参照ゼロ

lane b は今後 (12.16) path を S09 `chiRho`/`Hypothesis78`/`NormEstimates` cite で構成 (新規 ρ を作らない)。
lane b の branch に残る S07 commit は次 sync の modify/delete conflict で削除側を採用 (b 自身が削除推奨ゆえ整合)。
本 issue は closed。

## 判断待ち (裁定済 = D)

- **判断 D (削除, b 推奨 + hub 推奨)**: `S07_RhoProjection.lean` 削除 + AxiomsCheck の rho* ガード
  11 本 + import 削除 + carve-out 0087 撤回。(12.16) path は S09 `chiRho`/`Hypothesis78`/`NormEstimates`
  を cite。CLAUDE.md no-duplicate 方針に合致。lane b は S09 cite に redirect。
- **判断 K (保持)**: S07 を独立 §7 形式化として残す (consumer ゼロ・S09 と二重維持の負担を受け入れる)。

## 現状
- lane b の S07 (7.3) 新規 + STOP 報告 commit は **未マージ (hold)**。判断後に処理:
  - D → b の S07 work は破棄、S07_RhoProjection 削除を hub が main で実施。
  - K → b の S07 (7.3) を通常合流。
- 既に main 入りの S07 (7.1)-(7.2.b) (前 ticks 合流済) も D なら削除対象。

## 参照
- carve-out 0087 (S07_RhoProjection を lane b 所有化、2026-06-29 ユーザー裁可) ← 本 issue で reversal 検討
- lane b STOP 報告: branch b commit `91a4f83d` + `notes/peterfalvi/s14_maximalI.md` loop³⁸
- S09: `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`
