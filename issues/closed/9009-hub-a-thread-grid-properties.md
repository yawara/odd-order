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

## 🧾 HUB 裁定 (2026-07-04, merge monitor)

**判定: 選択肢 1 系 — ただし carve-out 不要。各レーンが自所有ファイルを additive に編集する split で解決。**

3002 の carrier constructibility は GENUINE と確認済 (spine `Section16CharacterData.omegaS` ←
honest `S05.TICyclicHypothesis`、性質は `S05_TICyclic.lean:733/740` ω-orthonormal + `S07` τ-isometry
から導出可能 = hoist でない)。よって threading は「新規数学ゼロの mechanical additive」で確定。
2026-07-04 再々編で **S15 は c→b 移管**ゆえ 3002 の旧 owner 表 (2026-07-02: S15.Hypothesis=c) は stale
→ **S15.Hypothesis 側 = b (自所有 `S15_SAndT_Setup`)**、**FeitThompson threading = a (自所有)** に更新。
この split では **どちらも自ファイルのみ編集 → carve-out (他レーン所有への一時編集権) は不要**。選択肢 2
(b に FT 編集権) は採らない。

**分担 (確定)**:
- **b (自ファイル `S15_SAndT_Setup`、即着手可)**: (i) `S15.Hypothesis` に grid 性質 field を追加
  (`eta_orthonormal`/`eta_intCast_on_G0`/`eta_conj_neg` — 3002 signature 案 + consumer parity/Parseval
  engine の入力に整形)。(ii) norm-cascade wrapper を engine に wire。**supply が a 未着地の間は sorried
  contract field で pin → build-green を維持** (先に signature を確定させて a に渡す)。(iii) 並行で
  consumer-side `GridProperties` de-opacify (a threading 後も wiring 再利用)。
- **a (自ファイル `FeitThompson.lean`)**: `Section16Inputs` に同 field 追加 + `sectionSixteenHypothesis_of_inputs`
  / `section16Inputs_of_isMinimalSimpleOdd` で ω-orthonormality (`S05_TICyclic.lean:733/740`) + τ-isometry
  (`S07`) から supply。**mechanical additive な短タスク**ゆえ 11.8 (unique bare feitThompson sorry) から
  外れず slot-in (b が sorried supply で build-green ゆえ hard-block でない → 緊急転進は不要、近い iteration で
  着手すればよい)。timing は a 裁量。

**sequencing**: b が field signature を先に pin (sorried) → a が supply を threading → b が wrapper を
sorry-free に flip。b・a とも独立に build-green (sorried contract 経由) ゆえ並行開始可。

**この裁定は user 相談不要と判断**: 再々編で確立した lane charter (S15=b, FeitThompson=a) の執行であり、
spec 違反でも大規模 cross-lane scope 変更でもない。各自の所有ファイル内 additive threading。3002 解決で本 issue close。

## ⚠ 2026-07-04 (lane b) 訂正: 「sorried default で b-solo build-green」機構は不成立
HUB 裁定の分担 (b が S15.Hypothesis に field pin / a が supply) は正しいが、**「b が sorried-default field で
independently build-green」は誤り**。理由: `sectionSixteenHypothesis_of_inputs` (a の constructor, FeitThompson)
に **`#assert_only_allowed_axioms OddOrder.sectionSixteenHypothesis_of_inputs` (AxiomsCheck.lean:3221)** が在り、
allowlist = 3 axiom (propext/Classical.choice/Quot.sound)、**sorryAx は不許可**。`S15.Hypothesis` に
`field := sorry` default を足すと、a の constructor が (omit → default 使用で) sorryAx 依存になり **assertion が
build-error** → build-RED。⟹ b が field を足すには a が**同時に**実値/sorried-supply + assertion 調整をせねばならず、
**b-solo build-green 不可** (a coordination 必須)。
- **b-solo で build-green に前進できるのは cite-sorried-**producer**経路**: 別 sorried producer (S15 内) を立て
  wrapper を engine から実証明 (grid obligation を producer に isolate)。(13.10) `analyticInequalityEstimates`
  が先例 (f17fdbcd)。**a threading 後は producer→hyp.field へ re-point** (engine wiring は再利用)。
- **∴ sequencing 修正**: b は producer 経路で wrapper de-opacify を進める (build-green, solo)。field-threading
  (hyp interface) は a の supply landing と**同時**に行う coordinated change (b field 追加 + a supply、単一 build-green
  commit、hub 承認合流) — sorried-default による段階 landing は不可。

## 参照
- issue 3002 (grid-property-carrier-enrichment) — a-side spec + b 訂正節 (2026-07-04) + fix-owner を 2026-07-04 再々編に更新
- `notes/peterfalvi/s15_s_and_t.md` 2026-07-04 lane b LIVE STATUS
- (13.10) `analytic_inequality` は b が de-opacify 済 (commit f17fdbcd) — 実 `u/c` bound は theorem 化

## 🧾 HUB 裁定更新 (2026-07-05, 統合セッション — 選択肢 2 に変更)

**threading の実施 owner を a → b に変更** (正本 = `ft_lane_reallocation_2026_06_28.md`
「3 レーン役割更新 (2026-07-05)」節)。理由: a は (11.8) capstone assembly 完了により S12 の 3 named gates
(τ₂/S₂ coherence 最深) に専念すべき負荷状況、b は本 threading が唯一の unblock 手段で飢餓中。
**b に `FeitThompson.lean` の `Section16Inputs`/constructor block への一時編集権を承認** (選択肢 2、
先例 `S_U_commutative`/`Sdata_W2_eq` 方式)。additive な field 追加に限定し、conflict は hub が merge で調整。
b の実施順: S15.Hypothesis grid fields (自所有) → FeitThompson 供給 → engine wiring → terminal 1298。

## ✅ CLOSE (2026-07-05, lane b): threading 実施完了 (commit 3dc9306e)

2026-07-05 hub 裁定 (選択肢 2 = b が両半分) どおり b が実施完了: S15.Hypothesis /
Section16Inputs / Section16CharacterData に 7 property fields + 全供給 proven (sorry ゼロ、
AxiomsCheck green)。本 issue は routing 用ゆえ close (残る consumer-side wiring は issue 3002
の 2026-07-05 節で追跡)。⚠ 07-04 の b 訂正「sorried-default 機構は不成立」は、b が供給まで
一括実施したことで無関係化 (assert は供給込みで green)。
