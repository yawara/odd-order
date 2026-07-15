---
id: 118
slug: lane-redesign-2026-07-15-endgame
title: "HUB: 3 レーン再設計 2026-07-15 — FT endgame 3 workstream 化 (0116 flip 実行=a 移譲 / ν-carrier / S16 de-bridging)"
created: 2026-07-15
---

# HUB: 3 レーン再設計 2026-07-15 — FT endgame 3 workstream 化

## 背景

ユーザー発議 (2026-07-15): 「Aレーンが終わったようです。あらためて3レーンを設計し直しても良い気がします」。
lane a は 9087 FINAL で割当 frontier 完遂 (S03–S13 + FeitThompson.lean の実 sorry 0)。
hub 3-agent 監査 (wf_54ad9ca3: authoritative #print axioms probe / on-path sorry census /
lane 実装状況) に基づく裁定。

## 確定した全体像 (監査結果、2026-07-15)

comment-strip 実 sorry = 全体 35。off-path (Pf Appendices 15 + BG AppD/E 8) を除く **FT 経路 12 本**の
うち、**`feitThompson` に実際に流入する dirty root は 7 本** (全て #print axioms + edge-probe で trace 済):

| # | root | 所在 | 性質 |
|---|---|---|---|
| 1 | `exists_muT_index` | NormEstimates:253 | legacy atom — proven `_core` twin (Engines:83) 未配線 |
| 2 | `exists_etaT_alphaFun_one_int` | NormEstimates:264 | legacy atom — proven `_core` twin (Engines:830) 未配線 |
| 3 | `character_degree_analysis` | Machinery135:345 | 9094 deprecated・unprovable-as-stated。残 consumer = NormEstimates 5 obtain-site |
| 4 | `Hypothesis.nuGridSupply` | HypothesisSwap:134 | carrier gate。**canonical producer `sectionSixteenNuGridSupplyData_of_inputs` は FeitThompson.lean:1583 に PROVEN 済** — 残 = carrier threading (9096) |
| 5 | `V_inf_centralizer_Q_eq_bot` | S15_SAndTBasic:841 | genuine math gap ((13.12) d=1 T-side dual)。in-place 証明は DAG-blocked (0116 Finding 0) — flip の discharge leaf で充填 |
| 6 | `caseB_order_u_data` | CaseBOrder:397 | (14.6) 用 compatibility bridge。honest `caseB_order_u` は同 file で proven。consumer = SubgroupL:200 / TTypeII:924 (両方 `caseB_for_S := True`) |
| 7 | `T_isTypeP2_gate` + `tSide_theta_package_of_not_caseB` (legacy) | CDS:37 / CountingLayer:870 | layer-inversion gate + legacy pair (heir `_core` は proven、残 sorryAx = #4 のみ) |

**spine 外 (consumer-0 vestigial、FT root でない)**: `sibleyTarget_S` (HypothesisBasics:1309、
do-not-complete 裁定済) / BG `sigmaLength_one_frobenius_type` (8020 mis-encoding、faithful 版
`non_disjoint_signalizer_frobenius` landed) / BG `nonidentity_covered_by_sigma_pieces`
(false-relative-to-BG surface) / BG `theoremA_maximal_structure` (overstatement、faithful heir
`theoremA_maximal_structure_faithful` proven・real caller 3、monolith 側 caller 0 = retire 候補)。

**クリーン確認済の主要部品** (probe 実測): `proposition_type_classification` /
`exists_chiefFactorData` / `no_typeV_maximal_unconditional` / `Q_elementaryAbelian_T` /
`delta_eq_one_S` / `tau1S_ofHonest_muColumn_formula` / 両 `_core` twins / caseB norm-bound
producer 3 本 / `typeI_caseC_bound_c1`/`_c2` / `gap_coefficients_nonzero_of_delta_parity` (nzT1_Ga)。

⟹ **root 7 本は下記 3 workstream で全てカバーされ、完了すれば `feitThompson` の axiom-clean 化
(= FT 完全形式化の headline 完成) が視野に入る**。ただし doneness は sorry 数でない
([[scaffold-sorry-free-not-done]]) — 各 workstream は hoist でなく実証明/実配線であることが本質で、
完了時に c-4 で全 root の再 trace 検証を行う。

## 裁定: 新レーン割当 (workstream 単位)

### lane a — WS2 ν-carrier → WS1 0116 full flip 実行

1. **(a-1) 9096 ν-carrier threading (先行、文書順上流)**: `Hypothesis.nuGridSupply` の discharge。
   canonical producer (FeitThompson.lean:1583、proven) を 9081 pattern の coordinated carrier
   threading で FT-layer から供給する (carrier field 追加 + constructor supply、a-owned
   FeitThompson{,Setup}.lean)。generic `hyp` では row-translation gap で証明不能 (9096 audit 確定)
   ゆえ、HypothesisSwap:133 の generic 宣言自体は「carrier 入力を explicit param に取る形」への
   restate + Supply 層 consumer (~8 sites、b-owned) の切替が必要 — **a = carrier/producer 側、
   b = consumer 切替 (b-5)** の分担で 9096 に記録・通知しながら進める。
2. **(a-2) 0116 full flip — 実行 owner を hub→a に移譲** (設計正本は 0116 のまま、scope 不変):
   NormEstimates 5 obtain-site の core/lam + (hD,hv) param 化 (additive + legacy wrapper) →
   討伐済 atom の cite 置換 (root #1/#2 → `_core` twins) → 新 discharge leaf
   (`S15_CaseBEndgameSupply.lean` 予定、CDS import、`T_caseB_facts_unconditional` cite で一括
   discharge) → OrderDetermination 3 obtain-site の param 版移行 (a-owned) → legacy retire
   (root #3 `character_degree_analysis` + root #7 CountingLayer legacy pair 削除)。
   - **carve-out**: flip scope 限定で `S15_SAndT_Setup/{NormEstimates,CountingLayer,Machinery135}.lean`
     (b-owned) の編集権を a に付与。b の同 file hold は継続 (相手が hub→a に変わるのみ)。
   - **hQcomm 裁量条項も a に委譲**: `Q_elementaryAbelian_T` は proven (probe 確認) ゆえ
     hTTypeII thread が自然だが、threading param 追加 vs S16 hoist は実装時判断。
   - **順序条件**: flip の Core-typed param 化は **b の δ′ restate-drop (b-1) landing 後**に始める
     (Core の field 構成が変わるため二度手間回避)。(a-1) は independent なので即着手可。
3. (a-3) flip 後: AxiomsCheck で `c_eq_one` / `caseA_parameters` / `analytic_inequality` /
   `s_side_field_repr` chain の clean 化を assert 登録・検証。

### lane b — Core/Supply 層整備 (即着手可の直列 4 件 + flip 後 sweep)

1. **(b-1) δ′ restate-drop 実装** (2035 #92 裁定済・未実装と監査確定): `CharacterDegreeCore.delta_eq_one`
   から δ′ conjunct を除去 (Machinery135:304) + EnginesSSide:566 constructor 調整 +
   `characterDegreeCore_nonempty` の AxiomsCheck assert 追加 (これで nuGridSupply を待たず即
   axiom-clean 化、#92 実測済)。**最優先** (a-2 の順序条件)。
2. **(b-2) `T_isTypeP2_gate` (root #7 前半) の resolution**: consumer = CDS:148/174 (b-owned
   swap-instance 構成)。hT2 弱化済み供給 chain (#82-86) に照らして gate 依存を除去するか、
   hTTypeII explicit param 化で layer-inversion を解消 (0116 Finding 2 の「T_isTypeP2 cite は
   証明循環」制約に注意 — cite でなく param 化が正)。
3. (b-3) `sibleyTarget_S` + `S_coherent` の W-side restate-or-retire (2026-07-02 hub 裁定の執行、
   HypothesisBasics、consumer-0 確認済)。
4. **(b-4) ✅ 再設計前に landing 済**: `6546bc02` で
   `S15_CharacterDegreeSupply` → `S15_CharacterDegreeEngines` を prefix-split 済み。
   その後 `f2c3b831` で Engines の S-side 層も分離され、現行 3 files は
   1286 / 841 / 1052 行で全て上限内。新たな分割は不要。
5. (b-5) a-1 landing 後: Supply 層 ~8 consumer を threaded ν-supply へ切替、generic sorried
   `Hypothesis.nuGridSupply` を retire (9096 完結)。
- **hold 継続**: `S15_SAndT_Setup/{NormEstimates,CountingLayer}.lean` は a の flip landing まで touch 禁止。

**lane b status (2026-07-15)**: b-1 `fa6fd706` 完了。b-2 は Phase 1 `a524da36` を landing、
field 削除本体は a flip + c-owned sites の追従待ち。b-3 は consumer-zero S-side placeholder を
`2dcab177` で retire。b-4 は上記の通り既完了。b-5 は Phase A `c87438fc` 完了、Phase B は
issue 9096 記載の c-owned S16 call-site rewire 待ち。

### lane c — WS3 S16 de-bridging + endgame 検証 (即着手 2 件 + flip 後 2 件)

1. **(c-1) `caseB_order_u_data` bridge retire (root #6、即着手可)**: SubgroupL:200 / TTypeII:924
   (両方 c-owned) の `caseB_for_S := True` 消費を proven `caseB_order_u` + 実 `CliffordCaseBData`
   certificate 消費へ rewire → bridge (`caseB_order_u_data` + `CaseBOrderUData`) 削除。
   **carve-out**: CaseBOrder.lean (b-owned) の bridge 2 宣言の削除権を c に付与 (条件: consumer
   rewire 先行・honest `caseB_order_u` の signature 非接触・単独 commit + self-flag)。
   これで `S16.T_isTypeP2` の直接 dirt が消える。
2. **(c-2) BG vestigial 整理 (即着手可、軽)**: `theoremA_maximal_structure` monolith retire
   (caller 0 確認済・faithful heir が正)、S14 の 2 本 (`sigmaLength_one_frobenius_type` /
   `nonidentity_covered_by_sigma_pieces`) への frozen/do-not-prove 注記整備、stale docstring 修正
   (TypePDuality:1306 / GlobalCounting:815 — 監査で検出)。削除は consumer-0 の再確認を commit 内で
   証跡化すること。
3. (c-3) a-2 landing 後 (hub が flag): **V_inf (root #5) の discharge-leaf proof 充填**
   (9077 carve-out の re-scope 済み内容) + S16 spine の param 版供給への追従 rewire。
4. (c-4) 全 workstream 完了後: `nonexistence_of_G` → `noMinimalSimpleOdd` → `feitThompson` の
   **最終 axiom trace** (#print axioms authoritative、未 trace 領域の残 root 有無を検証) +
   AxiomsCheck assert 追加 = **FT axiom-clean 判定の総仕上げ**。

### hub

- 監視 tick 継続 (Fable 30 分 `13,43`)。landing flags: (a-1 → b-5 kickoff) / (b-1 → a-2 kickoff) /
  (a-2 → c-3 re-engage)。0116 の設計 authority は hub 保持 (実行のみ a)。
- `hub0116` worktree/branch は撤収 (commit 0 のまま; flip 実行は a worktree で行う)。
- 2035 の b 宛 anti-collision 文言を「hub flip」→「a flip」に読み替え周知 (本 issue で足りる)。

## 根拠 (規約からの推論)

- **a への flip 移譲**: a は free かつ、flip の作業内容 (explicit-param + legacy wrapper threading /
  consumer cascade rewire / AxiomsCheck 検証) は a が card_kappaHall (1025)・legacy-rewire
  (9087 RULING #3)・OrderDetermination 移管 (0115) で 3 連続実証した同型パターン。lane cadence
  (60s /loop) は hub tick (30 分) より速く、bottleneck を最速で解消する。hub 実行に固執する理由は
  「hub が claim した」以外に無く、レーンは等価 ([[lanes-are-equivalent-no-specialty]])。
- **ν 先行 (a-1 < a-2)**: 上流優先 + 文書順 ((4.3)-(4.9)/(13.3) 供給 < (13.4)-(13.10) chain)、
  かつ ν landing で flip の discharge leaf cite (`tSide_theta_package_core` 系) がその場で clean 化。
- **c の即着手 2 件**: c は 9077 で gated-endpoint hold だったが、(c-1)/(c-2) は監査で ungated と
  確定 (consumer 全 c-owned / consumer-0 cleanup)。idle lane を busywork でなく genuine root 除去に
  充てる。
- 3 workstream は互いに file 非交差 (a: NormEstimates/CountingLayer/Machinery135/FeitThompson* /
  b: Machinery135(δ′ のみ先行)+EnginesSSide+CDS+HypothesisBasics / c: S16_NonExistenceG/**+CaseBOrder
  (bridge 削除のみ)+BG S14/S16)。唯一の交差 = Machinery135 (b-1 の δ′ drop vs a-2 の retire) は
  順序条件 (b-1 → a-2) で解消。

## 完了条件

- [ ] a-1/a-2/a-3、b-1〜b-5、c-1〜c-4 の全項目 landing
- [ ] `feitThompson` の #print axioms が標準 3 公理のみ (c-4 で判定)
- [ ] 0116 / 9096 / 9077 / 2035 の各 issue を対応する landing で close

## 参照

- 監査 = workflow wf_54ad9ca3 (3 agent: axiom probe / census / lane status、2026-07-15)
- issues/0115 (前回再設計)、0116 (flip 設計正本)、9096 (ν-carrier)、9077 (c hold)、
  2035 (b campaign)、closed/9087 (lane a 完遂)
- notes/meta/ft_lane_reallocation_2026_06_28.md「3 レーン再設計 (2026-07-15)」節

## 🧭 HUB 中間裁定 (2026-07-15 tick #8, Opus hub) — B/C block 精査 + 役割補正

ユーザー「B, C がブロックされています。役割は？HUB 裁定が必要なものを」を受け、hub 4 並列監査
(b-frontier / c-frontier / a-flip / pending-rulings) で全レーンの gating 実態を確認・裁定した。

### 結論: B/C の block は**設計どおりで正当** (idle-wait は busywork でない)

- **a**: 0116 full flip を**継続中・近接だが未 landing**。honest 置換 chain (S15_CaseBEndgameSupply/ +
  `_core` twins + OrderDetermination param split + `c_eq_one_of_lambda_dichotomy`) は全て sorry-free
  で構築済。残り = mid-layer consumer への c=1 threading (数 tick) + **cut-over + legacy-retire の 1
  assembly commit** (これが flip root #1/#2/#3/#7-half を一括除去)。数学的ブロッカーなし・機械的配線のみ。
- **b**: 3 owned FT-path sorry (`T_isTypeP2_gate` #7 / `V_inf` #5=c-3 carve-out / `nuGridSupply` #4) は
  **全て a flip または c-site に gated**。upstream の genuine math は 2035 #82-#91 で**完全に discharge 済**
  (hT2 sweep / core twins / QD_sharp / δ′)。**新規 ungated skeleton は残っていない** → idle-wait が正当。
- **c**: **c 所有 file の実 sorry = ゼロ** (c-1/c-2 完了、S16 の sorry token は全て docstring)。唯一の
  c-assignable FT sorry = #5 V_inf (b-owned SAndTBasic の c carve-out) は a flip に gated。V_inf の
  skeleton-ahead は技術的に可能だが (i) producer `T_side_D_eq_bot` が pre-flip で sorryAx-dirty、
  (ii) 除去に SAndTBasic normalizer_W1 chain の threading = a flip と衝突、ゆえ **dirty churn で非推奨**。
- **FT endgame は a の serial flip に収束**しており、flip は分割すると signature churn を招く (0118 の
  a 単独割当理由) ため parallelize 不可。∴ b/c の gated 状態は「上流枯渇の自然な収束」であって
  mis-assignment でない。

### 是正 1: c-2.5 挿入 (0118 coordination gap) — root #4 の c-owned rewrite

**b-5 Phase B の c 所有 6-site rewrite が c task 一覧から漏れていた** (9096 に記録あるが 0118 c-1..c-4
に非掲載)。これは ungated on-path work (a-1 honest carrier landed) → **c-2.5 として c の即時タスクに挿入**。
詳細・6 site・検証要件 = issue 9096「HUB RULING (tick #8)」。landing で b-5 Phase B (b が default+generic
削除) → **root #4 除去**。c-frontier 監査はこれを surface しなかった (c 所有 sorry 削減に scope 限定;
本 work は b 所有 sorry #4 を削減、work は c files) — hub が cross-lane 視点で拾った。

### 是正 2: c の flip 待ち中の productive option = c-4 diagnostic prep

c-2.5 landing 後も flip landing まで idle になるため、**c-4 の diagnostic 前倒し** (現 main の
`#print axioms feitThompson`/`nonexistence_of_G`/`noMinimalSimpleOdd` の authoritative edge-probe で
どの root が流入中かを列挙) を許可。これは verification bookkeeping (sorry 削減でない) だが flip 後の
c-4 総仕上げの土台になり、閉じ残し root の早期検出に効く。busywork でなく endgame 検証の前倒し。

### 是正 3: 9103 Phase 2 を landing-flag chain に組込 (b からの hub flag 受理)

issue 9103 (S_typeP2 field removal) Phase 2 は a-flip + c-owned sites 交差ゆえ b-2 と同 gated。
0118 の landing-flag 運用に **Phase 2 kickoff を追加**: **a flip cut-over landing → (b-2 body = S_typeP2
field 削除 + T_isTypeP2_gate 削除) + (9103 Phase 2)** を同時 kickoff。root #4 (9096) は本 campaign と独立
(swap の pins 入力)。

### landing-flag 更新版 (hub 追跡)

- **a-1 (ν-carrier) landed** → c-2.5 (9096 6-site rewrite) kickoff = **今** (本裁定で発火)。
- **c-2.5 landed** → b-5 Phase B (b が default+generic 削除) kickoff → root #4 除去。
- **a-2 (0116 flip cut-over+retire) landed** → c-3 (V_inf discharge) + b-2 body + 9103 Phase 2 kickoff。
- **全 WS 完了** → c-4 最終 axiom trace (diagnostic 前倒し分を本番化)。
