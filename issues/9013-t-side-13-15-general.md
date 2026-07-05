---
id: 9013
slug: t-side-13-15-general
title: "HUB: T-side (13.15) v-value + frobenius-kernel exact-values — generalize lane-b §13 estimates for both sides"
created: 2026-07-06
---

# HUB: T-side (13.15) v-value + frobenius-kernel exact-values — generalize lane-b §13 estimates for both sides

**起票者**: lane c (/loop). **判断者**: hub / lane b. **種別**: cross-lane coordination (non-duplication)。

## 背景 (2026-07-06 確定, lane c 精査)

C の S16 (`S16_NonExistenceG.lean`) は **top-level `nonexistence_of_G` まで assembly 完了**。残 8 sorry は
**全て lane-b の §13/§15 char cascade body** に gated (lane-d は 2026-07-02 退役ゆえ無関係; 9000 σ-theory
divisibility/upper-bound は完成・frozen)。内訳:

- **v-value** (`T_side_caseB_facts:179`) = `v = (q^p−1)/(q−1)` = **T-side (13.15)**。`key_ratio_inequality_of_caseB_data`
  が `Tdata.v_eq` (exact) を要する (v は不等式の大側 → **lower bound** 必須。9000 は upper bound のみ)。
- **s/t_side_frobenius_kernel** (:2594/:2607) = field-model carrier (exact u/v 値要)。
- **carrier fields** (m_row/m_col/grid_mem :5294/5297/5315) + **1_G+Δ η-grid** (:6317) = S15 grid fields (issue 3002) + η-grid。

**exact u-value は C 内で proven** (`u_final_value`, (14.15) fpf-congruence route — (13.15) 非経由・ungated)。
だが **T-side には (14.15) 相当の route が無い** (v は (14.4) case-(9.7.b) = (13.15)-dual 直行)。

## やること (非重複の判断 = claim-before-build)

lane-b が §13 S-side estimate ((13.10)/(13.11)/(13.12) `c_eq_one`) を **active に building** (commit a1dc3748,
2026-07-05)。だが lane-b の版は **S-side hardcoded** (`hyp.c` 等)。T-side (13.15) v-value を閉じるには:

- [ ] **(案 A, 推奨) lane-b が §13 estimate ((13.10)/(13.11)/(13.14)/(13.15)) を generic type-II maximal
  subgroup 版に generalize** → C が S/T 両側で instantiate (cite)。非重複・signature-contract 準拠。
- [ ] (案 B) C が T-side dual を自 file で re-derive → **lane-b S-side と重複** (anti-doctrine, 非推奨)。
- [ ] (案 C) C は landing 待ちで別 ungated work へ (但し C 自クラスタは assembly 完了ゆえ別 work 不在)。

## 完了条件

lane-b/hub が案を裁定。案 A なら generic §13 lemma export 後、C が v-value + frobenius_kernel exact-value を
cite で close (sorry 8→5 目安)。

## 参照

- `notes/peterfalvi/s16_w4_char_cascade.md` cont.⁷⁰/⁷¹
- lane-b commit a1dc3748 (Pf 13.12 c_eq_one, (13.10)+(13.11) 組立)
- `S16_NonExistenceG.lean`: `u_final_value:5874` (proven exact-u, (14.15) route), `key_ratio_inequality_of_caseB_data:1565`
