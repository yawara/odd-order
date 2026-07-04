---
id: 3002
slug: grid-property-carrier-enrichment
title: "§15/§16 cascade wrappers need Hypothesis grid τ-isometry/orthogonality fields (toolkit ready)"
created: 2026-06-29
---

# §15/§16 cascade wrappers need Hypothesis grid τ-isometry/orthogonality fields (toolkit ready)

**Lane:** c (γ §15/§16 POLE-2) raising; fix = **cross-lane**。
🧾 fix-owner **更新 (2026-07-04 hub, 3 レーン再々編 — 正本 `notes/meta/ft_lane_reallocation_2026_06_28.md` + issue 9009 裁定)**:
**S15 grid 性質 fields (`S15.Hypothesis`/`S15_SAndT_Setup` 変更) = lane b** (S15 は 2026-07-04 に c→b 移管) /
**FeitThompson.lean threading (`Section16Inputs`/constructor 供給) = lane a**。各自の自所有ファイル内 additive ゆえ
carve-out 不要 (9009 裁定)。旧 fix-owner 表 (2026-07-02: S15.Hypothesis=c / grid producers=b) は S15 移管で stale。
検証 (2026-07-02): `tau3_isometry` / `omega_orthonormal` / `eta_orthogonality` / `mu_degree` は
`OddOrder/**.lean` に **0 hits** — field 追加は未実施で本 issue は live。

## 背景

§15/§16 の Dade norm-cascade wrapper 定理 ((13.5)-(13.10)、(14.11)-(14.12)、norm cascade) は
`∃ data : NormCascadeData hyp, data.<opaqueProp>` 形で、`NormCascadeData`/`CharacterDegreeData` は
`Hypothesis` の **opaque grid** (`omega`/`eta`/`mu`/`nu` + `tauS`/`tauT`/`tau3`) に依存。これらが
**τ-isometry / η-直交性 / 指標次数** を *property* として carry していないため、wrapper は faithful 化
できず carrier-gated のまま (`scaffold_opaque_prop_convention`)。

lane c は 2026-06-29 に **carrier-free な norm-cascade arithmetic toolkit を完成** (S15_SAndT_Setup.lean):
`sum_normSq_erase_one_ge_of_const_on_subgroup` (13.5.c)・`innerSum_self_eq_sum_normSq`+
`sum_normSq_eq_card_mul_inner` (Parseval)・`caseB_quadratic_nonneg` (13.6/13.8)・`caseB_eta_norm_core`
(13.7)・`caseB_u_bound_arith` (13.2.c)。**残るのは grid 性質を Hypothesis に carry させること**だけ
— それが入れば各 wrapper を toolkit から faithful に組める。

## やること

- [ ] `S15.Hypothesis` に grid 性質 field 追加 (consumer-side で先に sorried contract として pin 可):
  - `tau3_isometry` (τ₃ が Dade isometry = `FullDadeIsometryData`、§5 `S05_IntegralSigma` の σ-isometry)
  - `omega_orthonormal` / `eta_orthogonality` ((3.2)/(5.3.b) の grid 直交性、§5 `S05_*Grid` producer)
  - `mu_degree` / `Sset_nonempty` (μ_j(1)=uq、Sset が誘導指標族 = (9.8)/(9.9))
- [ ] FeitThompson の 2 constructor (`sectionSixteenHypothesis_of_inputs` 他) + `Section16Inputs` /
  §16 carrier に thread (lanes B=grids `cd` / D=carrier; FT spine は prefix-split 共有)。producer は
  no-gates 方針で sorry 可。
- [ ] grid 性質が入ったら lane c が faithful wrapper を toolkit から組む (13.6/13.7/13.8 → 13.10 assembly)。

## 完了条件

§15/§16 の norm-cascade wrapper が opaque-Prop でなく実 inequality を述べ、lane-c toolkit + carried grid
性質から sorry-free に証明される。

## 🔎 2026-07-03 (lane c) 精査確定: char frontier 全体が本 issue に収束 + cross-lane 分担の詳細

再開時の §13/§16 全数精査で、**lane-c char frontier 全体が本 grid carrier に gated** と確定:
- **norm cascade (13.6-13.10)**: `NormCascadeData.{lambda,eta10,eta01}_norm_lower` は opaque `Prop`
  scaffold。parameterized 算術 engine (`caseB_lambda_norm_core`/`caseB_eta_norm_core`/
  `caseB_quadratic_nonneg`/`analytic_inequality` の (13.10) 算術核) は**完備・sorry-free**。残は
  grid 性質を carry して wrapper を engine に wire するだけ。
- **`c_eq_one` (13.12, S16 が 14× cite)**: 構造部 proven、残 sorry は (13.10) analytic 経由 = grid gated。
- **`exists_MHypothesis` の `betaGrid` field** ((13.1.d)/(3.9) `1_G+Δ=Σε_ij η_ij`): honest η-grid 要求。

**構成可能性 = GENUINE 確認 (hoist でない)**: spine (`FeitThompson.lean:1727+`) は
`omega := Section16CharacterData.omegaS` = honest な `S05.TICyclicHypothesis.omegaProdChar` から構成。
∴ 性質は `S05_TICyclic.lean:733/740` (ω orthonormal) + `S07_CoherenceGalois` (τ isometry
`extension_inner_eq`) から**導出可能**。placeholder でない。

**cross-lane 分担 (確定)**: `S15.Hypothesis` (S15_SAndT_Setup:81) と `Section16Inputs`
(`FeitThompson.lean:96`) は共に `omega`/`tau3` を **bare field** で持ち性質を carry せず。
- **lane c**: `S15.Hypothesis` に grid 性質 field 追加 (下記) + wire で norm cascade wrapper を honest 化。
- **lane a**: `Section16Inputs` に同 field 追加 + `sectionSixteenHypothesis_of_inputs` で S15 へ渡す +
  `section16Inputs_of_isMinimalSimpleOdd` で `omegaS` orthonormal / `tau3W` isometry から supply (sorried 可)。
- ∴ **lane c 単独で build-green 不可** (field 追加が spine を壊す、lane a threading 必須)。

**追加すべき field (signature 案、S15.Hypothesis)**:
- `eta_orthonormal : ∀ i j k l, ClassFunction.inner (eta i j) (eta k l) = if (i,j)=(k,l) then 1 else 0`
  (τ₃ isometry + ω orthonormal から導出; parity/expansion core が消費)。
- `eta_intCast_on_G0 : ∀ (g) (hg : g ∈ G0-型), ∃ n : ℤ, eta i j g = (n:ℂ)` ((3.9.c) 整数値; parity core の `n`)。
- `eta_conj_neg : eta (-i) (-j) g = conj (eta i j g)` ((3.9.a) 共役ペア involution; parity core の `hpair`)。
- (13.19.c betaM 側 odd parity は betaM_expansion 側で別途)。

正確な形は consumer (parity core `one_le_norm_signed_paired_sum` / sum-of-squares core
`all_pm_one_and_card_of_odd_sq_sum_le`, issue 4001) の入力に合わせる。

## 参照

- `OddOrder/Peterfalvi/S15_SAndT_Setup.lean` — carrier-free toolkit (上記) + `induce_one_apply`
- `notes/peterfalvi/s15_s_and_t.md` — LIVE STATUS (2026-06-29、toolkit + 2 work-streams)
- `notes/peterfalvi/s16_w4_char_cascade.md` cont.⁴⁶ (2026-07-03 frontier 収束の記録)
- `OddOrder/FeitThompson.lean:1861` — `sectionSixteenHypothesis_of_inputs` (constructor) / `:96` `Section16Inputs`
- issue 3001 (Sdata.W2 reconciliation、同系の carrier 不足)、issue 4003 (η-値性質、統合対象)

## ✅ 2026-07-04 (lane c) 検証: norm-cascade engine は完備 — 残は cross-lane threading のみ

再開時の再検証 (main sync 後、grid-property field は現 main で **0 hits** = 依然 live) で、
**character-level engine が既に完備・sorry-free** と確定 (前記「算術 engine 完備」を engine 層まで拡張):

- **算術核** (sorry-free): `caseB_lambda_norm_core` (S15_SAndT_Setup:808)・`caseB_eta_norm_core` (:868)・
  `caseB_eta01_norm_core` (:934)・`caseB_quadratic_nonneg` (:787)・`analytic_inequality_arith` (:1316)。
- **character-level engine** (sorry-free、grid 性質を**明示仮説**として取り real norm bound を産む):
  `caseB_lambda_norm_bound` (:839、hvanish/hinner/hχ/hParseval/hInflation を仮説に |S|−λ(1)² ≤ Σ_{H#}|χ|²)・
  `caseB_eta_norm_bound` (:910、hχ 点公式/hs 整数性/hParseval/hInflation で |H|−1 ≤ Σ_A|χ|²)。

⟹ **norm-cascade の solo build-green work は完全に枯渇**。残るのは本 issue の cross-lane threading のみ:
1. `S15.Hypothesis` に grid 性質 field 追加 (lane c) — ただし engine の仮説に合わせた形が要る
   (`eta_orthonormal` だけでなく、engine が消費する **点公式 (hχ)・Parseval (hParseval)・整数性 (hs)・
   inflation (hInflation)** を供給する field 群。正確な形 = 各 `caseB_*_norm_bound` の仮説シグネチャ)。
2. `sectionSixteenHypothesis_of_inputs` (FeitThompson.lean:1861、`base := { … }` where-block) で
   sorried supply → **小 bridge** (数行、`eta_orthonormal := sorry` 等)。**FeitThompson = lane a 所有ゆえ
   hub/issue 経由承認合流** (CLAUDE.md/reallocation §2「carrier field 追加は hub 経由」)。
3. `NormCascadeData`/`CharacterDegreeData` の opaque `Prop` field を real inequality に de-opacify し、
   wrapper (`lambda_norm_lower`/`eta10_norm_lower`/… + `analytic_inequality` assembly) を engine に wire (lane c)。

**∴ lane c 単独では build-green で本 issue を前進できない** (field 追加が FeitThompson constructor を破る、
threading = lane a 承認要)。engine 完備を確認した以上、次の実質前進には **lane a の Section16Inputs/constructor
threading** が先決。lane c は本 issue の lane-c 部 (field 形の確定 + wrapper wiring) を threading 合流と同時に実施可能。

## ✅ 2026-07-04 (lane c) 併行: keystone `reconciled_typePData_T` の `H_noncyclic` を実証明化 (13/20)

norm-cascade が cross-lane threading 待ちの間、solo build-green な keystone 進捗として
`reconciled_typePData_T` (S15_SAndT) の `H_noncyclic` free-field sorry を実証明に置換 (12/20 → 13/20):
`H := Q = maxNilpotentNormalHall T` は intrinsic (choice-independent) ゆえ、§13-level producer
`typePData_of_isTypeNonI hyp.T_nonI` の `H_noncyclic` を同一 subgroup `Q` に transport ((14.9) `T_typeII`
不要 = clean §13)。残 7 axiom (`W2_le`/`M_complement`/`U_nilpotent`/`derived_complement`/`secondDerived_le_fitting`/
`fitting_eq`/`centralizer_W1`) は complement 一致 (V=type-P U) の reconciliation crux に gated
(§13 では `T_typeII` が import 下流 S16:87 ゆえ使えず、genuine に §13/§14 σ-structure 要 = 正しく sorried)。

## ✅ 2026-07-04 (lane **b** 再開) — S15 が c→b 移管。b-side status + 迂回 route 発見

07-04 reallocation で S15_SAndT_Setup + S15_SAndT が c→b。b が frontier 全数をコード検証:
- **(13.10) `analytic_inequality` 出力を de-opacify 済** (commit `f17fdbcd`): 実 `u/c` bound が real theorem 化。
- **⚠ 訂正 (同 07-04 loop): 「honest W-grid で迂回可能」は誤り**。**spine (`FeitThompson.lean:1319` `omegaS`) が
  既に honest grid を `mp.certainTypeS.sdiffTICyclicHypothesis` から構成済**。だが `S15.Hypothesis` は grid を
  bare field で持ち **mp/certainType/TICyclicHypothesis への structural link を carry しない** (field 精査済)。
  ⟹ b が fresh grid を組んでも **hyp.omega と同定不能**、cascade は hyp の λ/(13.5) machinery に tie ゆえ
  fresh grid では (13.10)-about-hyp 不可。**∴ η-side 含め §15 cascade 全体が本 issue に uniformly gated**。
- **✅ a-side threading は機械的** (grid は spine に proven 済、新規構成不要): S15.Hypothesis + Section16Inputs に
  下記 property field を足し、`sectionSixteenHypothesis_of_inputs` で **`omegaS` の直交性 (`S05_TICyclic.lean:733/740`)
  + `tau3W` isometry (S07 `extension_inner_eq`)** から supply。field 形 = 各 `caseB_*_norm_bound` engine 仮説
  (`hvanish`/`hinner`/`hχ`点公式/`hParseval`/`hs`整数性/`hInflation` + ω-orthonormal/τ-isometry)。
- **b-side (build-green solo)**: `GridProperties (hyp)` carrier + sorried producer で cascade wrapper を engine から
  実証明 (wiring は a threading 後も再利用、producer sorry のみ hyp 新 field で discharge)。a threading と pair。
- 詳細 = `notes/peterfalvi/s15_s_and_t.md` の 2026-07-04 lane b LIVE STATUS (訂正済)。

## 🧾 fix-owner 再更新 (2026-07-05 hub)

**threading 両半分とも lane b が実施** (S15.Hypothesis fields = 自所有 + `FeitThompson.lean`
`Section16Inputs`/constructor = 一時編集権、9009 裁定更新参照)。a は S12 (11.8) 3 named gates に専念。
正本 = `ft_lane_reallocation_2026_06_28.md`「3 レーン役割更新 (2026-07-05)」。

## ✅ 2026-07-05 (lane b): threading 両半分 LANDED (commit 3dc9306e)

hub 裁定 (9009 選択肢 2) どおり b が両半分を実施、full build 3917 green + AxiomsCheck green:
- **7 property fields** を `S15.Hypothesis` / `Section16Inputs` / `Section16CharacterData` に追加:
  `tau3_isometry` / `tau3_trivial` / `tau3_apply_of_regular` ((3.2.c) regular-set identity) /
  `tau3_mem_ZIrr` / `omega_orthonormal` / `omega_apply_one` / `omega_mem_ZIrr`。
- **供給は全 chain (cd producer → inputs assembly → constructor base) で sorry ゼロ**:
  tau3W を tiCyclicW/tiCyclicWDadeApp に抽出refactor → S05 σ-isometry package を直読み。
  omegaS_inner = S05 `omega_inner` (新設) + `ClassFunction.inner_compHom_mulEquiv` (新設 shared
  infra) + enumeration injectivity。`sectionSixteenHypothesis_of_inputs` の sorryAx-不許可
  assert が供給込み green = **「a が同時に supply しないと build-red」の障害は解消済**。
- 旧 signature 案の `eta_orthonormal`/`eta_intCast_on_G0`/`eta_conj_neg` は **hyp field にせず
  導出定理へ変更** (η = τ₃∘ω ゆえ tau3_isometry + omega_orthonormal から S15 内で導出可;
  primitive を carry する方が supply が機械的)。
- **残 (consumer-side, lane b)**: cascade wrapper wiring — (13.5) machinery + hyp の carried
  properties から `analyticInequalityEstimates` (S15_SAndT_Setup:1298) の 4 estimates を実証明。
  hu (2u≤|P|-1) は issue 9000 producer を sorried-cite。
- **✅ 2026-07-05 後半 (lane b): consumer wiring 第 2 段完了** — 4 producer 全て実 assembly 化
  (commits `a39ca309`〜`09b1ad39`)。(13.9.a) は完全実証明 (TI counting = issue 9011 +
  counting layer)。(13.6)/(13.7+8)/(13.9.b) は Parseval/Galois/counting 側が全 real、残 sorry は
  教科書番号どおりの 5 producer (13.6/13.7/13.8-T sharp bounds + 13.9.a dichotomy + λτ₁
  coherence facts) に isolate。η-side norm-one facts は本 issue の grid fields から**実導出済**
  (`eta10_mem_ZIrr`/`eta10_inner_self_one`) = threading の payoff 実証。詳細 =
  notes/peterfalvi/s15_s_and_t.md LIVE STATUS (2026-07-05 後半)。

## 🧾 ユーザー裁定 (2026-07-05 監視 tick): S05 `omega_inner` 受理 + 供給編集権明文化

b の供給 chain の一部 `S05_TICyclic.lean` `omega_inner` (+11、lane a 所有ファイルへの追加、
self-flag 済) を step 1.5 逸脱として保留 → **ユーザー裁定 = 受理 + 明文化**: 3002 供給 chain に
必要な lane-a 所有ファイルへの **additive helper 追加** (純 additive・proven・self-flag 必須) を
b の一時編集権に含める。**3002 供給完了で失効**。正本 = `notes/meta/merge_monitor.md` の
carve-out (3002 供給編集権) ブロック。threading 両半分 (3dc9306e) + (13.10) atom 分解 (a39ca309)
は 2026-07-05 監視 tick で main 合流済 (merge 88a3bdd1)。

## 📋 c-side consumer spec (2026-07-05, lane c — S16 の η-grid 需要の精密形)

(14.14) `orthogonality_switch_pairing_bounds` 実証明化 (60b9b6b6) 後の S16 残 sorry のうち
3 本が本 issue の導出定理待ち。b が「S15 内で導出」を実装する際の consumer 形 (S16 が cite する
正確な statement) を先に固定しておく:

1. **S16:2599 `eta_grid_facts_on_G0`** (hyp : Hypothesis, Mdata : MHypothesis) — 3 成分:
   - `eta_int` : ∀ g ∈ Mdata.G0, ∀ i j, ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ) — (3.9.c)。
     G0 → order prime to pq は Mdata.G0_orbit_cover 経由 (c が接続可)。**b 供給の核 =
     「g の order が pq と素 → η_ij(g) ∈ ℤ」形の S15 導出定理** (σ-Galois: S05 の
     `exists_intCast_sigma_omega_apply` (3.9.c) を cd の tau3W=σ witness で instantiate し、
     S15.Hypothesis レベルの statement に落とす)。
   - `eta_pair` : η_{−i,−j}(g) = η_ij(g) on G0 — (3.9.a) 共役対称。同様に S05
     `sigma_mapRingEquiv_comm` 系から。
   - `eta_principal` : η₀₀(g) = 1 on G0 — ω₀₀ = 1_W (grid の trivial 位置) + tau3_trivial。
     **ω₀₀ = trivialClassFunction の identification が carried fields に無い** — 供給要
     (omega_apply_one は値 1 のみで ω₀₀ の同定はしない)。
   - 注: 4 成分目 betaM_vanish は c が実証明済 (`eta_generic_data`)。
2. **S16:5415 `exists_MHypothesis` の betaGrid** : 1_G + Δ = Σ ε_ij η_ij ((13.1.d)/(14.11.2)
   K=V 側)。(13.19.a/b/c) 相当の grid orthogonality/counting が要る (b の cascade 供給圏)。
3. **S16:4604 `caseB_contradiction_data`** ((14.16)): β_L^τ の signed η 展開 + η_ij ⊥ ψ^{τ₁}
   ((5.3.b)/(5.5) 系) + χ_L 直交 — (14.11.2) の L-side dual。同上。

c 側はこれら 3 cite の組立 (G0→order-prime 接続、(14.11.2) dual の assembly) を supply 着き次第
実施する。form が上と乖離する場合は本節を更新してから landing を (コンフリクト回避)。
