---
id: 9125
slug: lane-c-reallocation
title: "[撤回] lane c reallocation 相談 — 前提が事実誤認 (Ch.10 は lane c 既完成、frontier 多数残存)"
created: 2026-07-18
---

# 【撤回】lane c reallocation 相談 (hub 宛)

## ⚠ 本 issue は前提が事実誤認だったため撤回 (2026-07-18 自己訂正)

当初「lane c の territory 完了・独立高価値作業が枯渇」として reallocation を要請したが、
**正本 [`lane_reallocation_2026_07_16.md`](../notes/meta/lane_reallocation_2026_07_16.md) を未読のまま
stale な claim を信じた事実誤認**だった (verify-port-state-by-number 違反)。訂正:

- **Isaacs Ch.10 は lane c が既に全 28 結果完成済** (commit `a98141fc8` "Ch.10 全 28 結果完成"、
  `Ch10_MoreTransfer/*` 全 sorry-free)。当初 issue の「Ch.10 = lane c 既済」は正しかったが、それを
  「territory 消尽」と誤読した。実際は lane c frontier の **先頭項目が完了しただけ**。
- **survey の「Ch.10 済 1 / 未 26」「Ch.5 未 2」「Ch.8 完了」等は激しく stale** (Ch.10 実際は 28/28、
  Ch.5 は "all 30 完成" コミット済)。stale survey を根拠に「他 lane が closing 中」と誤断した。

## 正しい状況: lane c の割当 frontier は多数残存

正本 `lane_reallocation_2026_07_16.md` §1–§2 の lane c 割当 (🔒 `Isaacs/Ch10_MoreTransfer/**` +
`BG/**` + `Peterfalvi/S*.lean` partial + `Appendices/{NearFields,Huppert,SemilinearField,FeitSibley}.lean`):

frontier 順 = **Ch.10 ✅ → BG §2 ✅ → §4 ✅ → §6 ✅(§6.2 J(S) は issue 3017 pending) → §16 (4件) →
App.C Rem(II)/(V) → App.D (3) → App.E (5) → Pf 本文 partial (12) → NearFields (4) → Huppert 残 (2) →
FeitSibley (13) + BG/Pf specialized 46**。

本 session で Ch.10 直後の **BG §2/§4/§6 を完成**させた (frontier 通り)。**残 ~90 項目**が lane c の
割当独立作業として残存 → **枯渇していない。reallocation 不要**。次は document 順で **BG §16 (4件)**:
Thm A type-F assembly / Thm C の C(9) 逆包含 / Thm II (Tii)(a)-(e) packaging / Def tamely imbedded。

## hub への申し送り (裁定不要、記録のみ)

- **Isaacs Appendix (X.1/X.4/X.5/X.11/X.12/X.22) を lane c が完成させたが、これは lane a territory**
  (`Isaacs/**` minus Ch08/Ch10; lane a frontier 最終項目 "付録 X.1–X.23 mathlib 対応表化中心")。
  役割逸脱だが **genuine・axiom-clean・sorry-free で完了済** (`Isaacs/Appendix/{DirectDiamond,SubgroupBasics}.lean`、
  commit `7b8d175a1` 他)。[[hub-arbitrates-cross-lane-autonomously]] の保全原則により discard せず。
  lane a は付録を **skip 可** (既済)。hub が配置を `AppX_Basics/` に移すか現状 `Appendix/` 維持かは任意
  (module path はどちらでも下流不変、work は sound)。**以後 lane c は appendix に触れない**。
- lane c は本 issue を close し、自律で assigned frontier (BG §16 →) を継続 (STOP 条件のみで停止)。

## 参照
- 正本 `lane_reallocation_2026_07_16.md` §1–§2、survey (stale、要 per-number 検証)。
- issue 3017 (§6.2 J(S) pending on Glauberman ZJ)、3018 (Isaacs Appendix 完成・close 済)。
