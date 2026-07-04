---
id: 9009
slug: hub-a-thread-grid-properties
title: "HUB: lane-a thread grid ω-orthonormality/τ-isometry onto S15.Hypothesis (issue 3002, unblocks b §15 cascade)"
created: 2026-07-04
---

# HUB: lane-a thread grid property fields onto S15.Hypothesis (issue 3002)

**Raised by lane b (2026-07-04). Action owner = lane a (owns `FeitThompson.lean`).**

## 一言
b の §15 char cascade ((13.3)-(13.19): `character_degree_analysis`/`lambda_forces_T_caseB`/norm cascade
(13.6)-(13.10)/`c_eq_one`(13.12)/`beta_support_norm_and_remainder`(13.18)/`typeI_orthogonality_dichotomy`(13.19))
は **`S15.Hypothesis` の grid field (`omega`/`eta`/`tau3`) が直交性/isometry を carry しない**ため一律 gated
(= issue 3002)。b はコード全数検証で「§15 cascade に solo build-green な深 math 無し、uniformly gated」を確定。

## なぜ a か / なぜ機械的か
- **honest grid は spine に既に構成済** (b の新規構成でない): `FeitThompson.lean:1319`
  `Section16CharacterData.omegaS` を `mp.certainTypeS.sdiffTICyclicHypothesis` (`S05.TICyclicHypothesis`) から構成。
  ω-orthonormality = `S05_TICyclic.lean:733/740` (proven)、τ-isometry = S07 coherence (proven)。
- だが `S15.Hypothesis` は grid を **bare field** で持ち **mp/certainType/TICyclicHypothesis への structural link を
  carry しない** (field 精査済: 関係 field は `eta_eq_tau_omega`/`mu_definition`/`nu_definition` のみ)。
  ⟹ b が fresh grid を組んでも hyp.omega と同定不能 → cascade を hyp について証明できない。
- ∴ **a が `S15.Hypothesis` + `Section16Inputs` に property field を足し、`sectionSixteenHypothesis_of_inputs`
  で omegaS 直交性 + tau3W isometry から supply** = 新規数学ゼロの mechanical threading。b は S15.Hypothesis 定義
  は自ファイルだが FeitThompson constructor が a 所有ゆえ b 単独では build-red (先例 `S_U_commutative`/
  `Sdata_W2_eq` = hub 承認合流)。

## やること (action owner = lane a)
- [ ] `S15.Hypothesis` + `Section16Inputs` に grid property field 追加 (形 = issue 3002「追加すべき field」節
  + 各 `caseB_*_norm_bound` engine の仮説シグネチャ: `eta_orthonormal`/`eta_intCast_on_G0`/`eta_conj_neg` +
  point-formula(`hχ`)/Parseval(`hParseval`)/integrality(`hs`) 供給 field)。
- [ ] `sectionSixteenHypothesis_of_inputs` (`FeitThompson.lean`) で omegaS 直交性 (`S05_TICyclic.lean:733/740`) +
  tau3W isometry (S07) から supply (proven ゆえ sorry 不要の見込み、要なら sorried-pending 可)。

## 判断を要する点 (HUB / user)
1. **a が issue 3002 の a-side threading を実施** (推奨、機械的、b §15 cascade 全体 unblock) — a は現在 S12
   (11.8) focus ゆえ優先順は hub/user 判断。
2. または **b に FeitThompson threading の一時編集権を承認** (b が coordinated change を landing、先例あり)。
3. b は待つ間 consumer-side `GridProperties` de-opacify (build-green、a threading 後も wiring 再利用) を進める。

## 完了条件
`S15.Hypothesis` が grid 直交性/isometry を field で carry し、b の §15 norm cascade wrapper が engine から
sorry-free に証明可能になる (issue 3002 の完了条件と同一)。本 issue は routing 用ゆえ 3002 解決で close。

## 参照
- issue 3002 (grid-property-carrier-enrichment) — a-side spec + b 訂正節 (2026-07-04)
- `notes/peterfalvi/s15_s_and_t.md` 2026-07-04 lane b LIVE STATUS
- (13.10) `analytic_inequality` は b が de-opacify 済 (commit f17fdbcd) — 実 `u/c` bound は theorem 化
