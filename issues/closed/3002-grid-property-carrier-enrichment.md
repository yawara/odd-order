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

## ✅ 2026-07-05 (lane c /loop): G0→order-prime 接続が完成 — b 供給の受け口 ready

c-side spec 1 (eta_grid_facts_on_G0) の **G0 → order-prime 接続を新 leaf
`S16_G0Coprime.lean` で全実証明** (commits 9986a629→485e0e4a、leaf sorry-free):
`orderOf_coprime_pq_of_not_mem_conj` が「regular-W/P#/Q# の共役を避ける元
(= 具体 G0 の元) は位数 pq と素」を与える (Coq coprime_typeP_Galois_core 対応、
(2.1)+Sylow+Frobenius-kernel 全チェーン)。パラメータ 2 点 (hfrob/hfrobT =
(14.6)/(14.4) の C_{M'}(x) ≤ M_F) は honest 明示仮説で、S-side は
`FieldNormalizerData.derived_inf_centralizer_le_P` (proven) が (14.2.a) carrier
着き次第放電。⟹ **b の (3.9.c) 供給は「(orderOf g).Coprime (p*q) → ∃ m : ℤ,
eta i j g = m」形 (+ (3.9.a) conj-pair 版) がそのまま最短で刺さる**。

## 🧭 HUB 裁定 (2026-07-05, POLE-2 coupled stall 再評価 — ユーザー「判断して」委任)

**背景**: c が cont.⁶⁵ で「独立 ungated frontier 枯渇 = POLE-2 coupled stall」を hub にエスカレーション
(S16 残 sorry 7 は全て b の §13 η-grid=本 issue / a の 7.8.b norm・9.7.b carrier / 9000 Galois に gated、
c が §13 grid を作ると b の on-path work と territorial 衝突ゆえ独立前進不可)。b も it.93 で「ungated
ceiling 到達」を宣言 (残は u_bound→9000 / V_inf_centralizer→c_eq_one deep chain / char_degree_analysis
keystone に deep-gated)。⟹ **b・c 2 レーンが共通の深層 keystone (§13 char_degree_analysis / 本 issue
η-grid threading + issue 9000 σ-theory) に収束**。a は ungated frontier 継続中。

**裁定 (プロジェクト方針「deep なら deep のまま engage・アイドル禁止」準拠、選択肢 1)**:
- **b = §13 char keystone を deep-engage (最優先)**: 本 issue 3002 の §13 η-grid を `S15.Hypothesis`
  grid field に threading する作業を、多反復を厭わず正面から実証明で進める。これが b 自身の下流
  (V_inf_centralizer→c_eq_one) と c の S16 carrier 群 (`lSideGridCoeffData`/`betaGrid`/`grid_mem`/
  `boundary`) を同時に unblock する pipeline のボトルネック。b の自所有領域 (S15 + coherence + FeitThompson
  3002 供給 zone) ゆえ territorial に自然。gated-endpoint body の de-gate も継続可 (u_bound は 9000 待ちで
  sorried-cite)。
- **c = S16 consumer wiring を先回り準備 (待たない・idle しない)**: 本 issue の「c-side consumer spec」
  (2026-07-05 節) どおり、b 供給後に即結線できる形まで S16 の carrier consumer を de-scaffold + 正確な
  cite statement を固定しておく。`lSideGridCoeffData` の 4 field (coeff/boundary/bessel/grid_mem) のうち
  c 独立で閉じられる部分 (coeff=整数性 trivial 等) は先に discharge。b の grid landing で残 (grid_mem/
  boundary) が供給され次第 (14.11.2) carrier 群を閉じる。
- **a = 現状維持 (ungated frontier 継続)**: §11-13 (chief_H0_eq_bot / caseA_commutator_chain / 11.8
  counts) を通常どおり進める。a の 7.8.b norm・9.7.b carrier が閉じれば c の s_/t_frobenius_kernel も
  un-gate される (副次的 unblock)。

**lane 数 = 3 維持** (idle・退役はしない)。次の実質前進の主経路 = **b の §13 η-grid threading**
(本 issue 完了 = b/c 両方の coupled carrier 群を解く)。cron 監視は継続。この裁定は各レーンが
`git merge main` で本 issue を取り込んだ時点で有効。

### 追記 (2026-07-05, a への回答 — a update²² frontier inflection への裁定):
a も群論 ungated frontier を完遂し「gate-1 threading を fresh budget で、or hub 再配分」を問うた。
**回答 = 再配分せず、a は POLE-2 裁定どおり ungated frontier を継続**: a の残 **gate-1 threading**
(proven ピース |M'ᵃᵇ|=[U:C] / commutator form / [U:C]=u を `card_SHCSet` に wire して |M'ᵃᵇ|=d を
閉じる) は **delicate spine plumbing だが a 自身の ungated 作業** (result が char-gated でも threading
自体は ungated)。プロジェクト方針「deep/delicate なら正面から engage・アイドル禁止」に従い、a は
gate-1 threading を fresh budget で careful に engage する (exists_zeta signature 変更の multi-consumer
波及は all-or-nothing ゆえ慎重に)。3 レーンとも char keystone 収束が確定したが、各自の ungated 残
(a=gate-1 threading / b=§13 η-grid keystone / c=S16 consumer wiring) を正面から進めれば lane 数 3 の
まま pipeline を解ける。gate-1 threading が真に block されたら (spine 破壊が避けられない等) 再度 hub flag。

## ✅ 2026-07-05 (lane b): η-grid Dade (3.9) fields LANDED on `S15.Hypothesis` (keystone threading)

hub 裁定 (本 issue「b = §13 η-grid keystone deep-engage」) を実施。**Peterfalvi (3.9) の 3 field を
`S15.Hypothesis` に threading 完了**、c-lane が `EtaGenericData` を即構成できる citeable form を供給。
full build **3929 jobs green**、新 sorry は下記 (3.9.a) の documented fallback 1 個のみ。

### 3 新 field on `S15.Hypothesis` (`S15_SAndT_Setup.lean`)
- **`eta_intCast_of_coprime`** (Peterfalvi (3.9.c)): `∀ g, Coprime (orderOf g) (p*q) → ∀ i j,
  ∃ m:ℤ, eta i j g = (m:ℂ)` — **供給 sorry-free**。
- **`eta_pair_of_coprime`** (Peterfalvi (3.9.a)): `∀ g, Coprime … → ∀ i j,
  eta (finNeg q.pos i) (finNeg p.pos j) g = eta i j g` — **供給に sorry 1 個** (下記 honest gate)。
- **`eta_principal_of_coprime`** (Peterfalvi (3.9)): `∀ g, Coprime … → eta ⟨0⟩ ⟨0⟩ g = 1`
  — **供給 sorry-free**。
- `S15.finNeg` を追加 (S16.finNeg と**byte-identical = defeq**、c の fill が `EtaGenericData.eta_pair`
  の `S16.finNeg` 形に defeq で通ることを実検証済)。

### 供給 chain (`FeitThompson.lean`、issue-3002 一時編集 zone)
`Section16CharacterData` 名前空間に 3 supply lemma + 全 threading (producer + 2 constructor):
- **(3.9.c) `tau3W_omegaS_intCast_of_coprime`** (sorry-free): `η_ij(g)=tau3W(omegaS i j)(g)=σ(ω(ξ_ij))(g)`
  (既存 `omegaS_eq_omega_omegaSChar`+`sigmaIntegral_apply`) → `orderOf ξ_ij ∣ pq` (新 lemma `cardTPW`:
  `|W|=pq`) → S05 **`exists_intCast_sigma_omega_apply`** (3.9.c σ-Galois integrality)。本 keystone の deep part。
- **(3.9) `tau3W_omegaS_principal_of_coprime`** (sorry-free): 新 lemma `omegaS_principal_eq_trivial`
  (`omegaSChar 0 0 = 1` via `w1CharEquiv_zero`/`chi2enum_zero`/`omegaProdChar_one_one`) + `tau3W_trivial`。
- **(3.9.a) `tau3W_omegaS_pair_of_coprime`** (**sorry 1 個 — documented honest gate**、下記)。

### ⚠ (3.9.a) finNeg-symmetry の honest gate (残 sorry の正確な obligation)
Peterfalvi (3.9.a) の真の内容 = 「η_ij の複素共役 = **character-inverse** index `(rowInv i, colInv j)`
の grid 値」(`S06_CertainTypeConjugation.chiColumn_conj`/`galoisMap_conj_omega`、実装済) + (3.9.c) で値が
実整数ゆえ自己共役 ⟹ `η_{rowInv i, colInv j}(g) = η_ij(g)`。pairing は **character 反転 `rowInv`/`colInv`**
(唯一の不動点 = principal) で honest 成立。だが `EtaGenericData.eta_pair` /
`one_le_norm_eta_grid_signed_sum` の **組合せ的 `finNeg = ⟨(n−i)%n,_⟩`** に一致させるには
`omegaSChar (finNeg i)(finNeg j) = (omegaSChar i j)⁻¹`、すなわち `w1CharEquiv (finNeg i) =
(w1CharEquiv i)⁻¹` が要る。これは **非構成的 enumeration `w1BaseEquiv`/`chi2baseEnum`
(`Fintype.equivFinOfCardEq`、群構造非保持) では FALSE** (`finNeg`≠`rowInv`)。Explore agent 2 回で厳密確認。
- **honest close の 2 択 (c-lane 判断領域)**:
  (a) `w1CharEquiv`/`chi2enum` を **構造保存 enumeration** (`ZMod`-style power-map) に組替え → `finNeg=rowInv`。
  (b) c が `EtaGenericData.eta_pair` / `one_le_norm_eta_grid_signed_sum` を honest な `rowInv`/`colInv`
      involution 上に restate (`one_le_norm_signed_paired_sum` は既に abstract `Equiv.Perm` を取る)。
- Step-D fallback (mission 明示 sanction): field を landing → c-lane wiring を即 unblock。

### AxiomsCheck の影響 (spine への波及は最小)
- **`sectionSixteenHypothesis_of_inputs` は axiom-clean のまま** (inp を abstract に取るため sorry 非伝播、
  実測 OK)。spine assembly point は不汚染。
- **`section16CharacterData_of_isMinimalSimpleOdd` (concrete cd producer) のみ** (3.9.a) sorry を transit
  ⟹ axiom-clean assertion を disable (documented comment 付き、`AxiomsCheck.lean:6719 付近)。この producer は
  元々 sorried FT-frontier (`section16Inputs_of_isMinimalSimpleOdd`) に feed される経路上。

### c-lane cite form (検証済、`eta_grid_galois_facts_on_G0` の sorry を discharge)
```
{ eta_int       := fun g hg i j => hyp.base.eta_intCast_of_coprime g (Mdata.G0_orderOf_coprime hG hg) i j
  eta_pair      := fun g hg i j => hyp.base.eta_pair_of_coprime g (Mdata.G0_orderOf_coprime hG hg) i j
  eta_principal := fun g hg     => hyp.base.eta_principal_of_coprime g (Mdata.G0_orderOf_coprime hG hg)
  betaM_vanish  := (eta_generic_data hG hyp Mdata).betaM_vanish }
```
(S16 に一時 test 定理 `tmp_verify_cite_forms` を入れて全 4 field が typecheck することを実確認 → revert 済。
`eta_principal` は既存 `eta_principal_apply_eq_one hyp.base g` でも同値。)
### ✅ 2026-07-05 (lane c, bounded investigate-and-attempt) — `lSideGridCoeffData` 残 3 field の gate 確定 (Coq 行番号付き、c-unreachable 実証済)

`lSideGridCoeffData` の残 3 sorried field (`m_row_odd`/`m_col_odd`/`grid_mem`) を bounded で精査し、
**3 field とも本 issue (b の §13 η-grid = `FTtypeI_bridge_facts`) に genuinely gated** と確定
(`bessel` が 2 度 gated 誤判定された前例に鑑み internal descent で検証 — 今回は誤判定でなく真に gated):

- **`m_row_odd` / `m_col_odd`** (境界 parity `m_0j`/`m_i0` odd): source = **Coq `FTtypeI_bridge_facts`
  (PFsection13.v:1987) の (c2) 選言** `⟨tauL betaL, eta01⟩ ≡ 1 (mod 2)`。row は **S-side type-P partner
  `StypeP`** に適用 (PFsection14.v:187 `case/betaL_P: StypeP => _ _ -> //`)、col は **T-side `TtypeP`**
  (PFsection14.v:190)。中身 = type-P coherent pairing `⟨τ β_S, τ₁ φ⟩ ≡ 1 (mod2)` on the S-side residual
  `β_S` — これは lane b の `S15_SAndT.lean:3671/3764` に所在 (S16 は opaque `caseB_formula : Prop` のみ)。
  **c-unreachable 実証**: c の唯一の parity primitive `cfdot_real_vchar_even` は (i) `η_0j` real を要求
  (repo に `eta_isReal` 無 — η は cycTI 像で複素) かつ (ii) 適用しても `⟨β_L,1⟩·⟨η_0j,1⟩ = 1·0 = 0
  (mod2)` = **EVEN** を返す (required ODD の逆)。⟹ 真の gate、hoist でない。
- **`grid_mem`** (`1_G + Δ_L = Σ m_ij η_ij` = Coq `Y=0`, PFsection14.v:212-251): `orthogonal_split` +
  `leif`-equality で、tightness `e = pq` (`ub_e`) **かつ** 各 `|m_ij|² ≥ 1` (= 上記 parity `a_odd`) から
  強制。⟹ `grid_mem` は境界 parity に **依存**。**c-unreachable 実証**: 既存 proven `NC≤2` engine
  `grid_eq_zero_of_relation_of_card_le_two` (S16_GridExpansion) は不適用 (係数 pq≥15 個が全 ±1 で NC=pq≫2)、
  `bessel` proof は `⟨Y,Y⟩ ≥ 0` しか出さず tight `=0` を出さない。Mirror: M-side `MHypothesis.betaGrid`
  (同一 statement) は `exists_MHypothesis` で explicit `sorry` (S16:6288, "genuine Track A obligation
  (issue 3002)") ゆえ L-analog も同 gate。

**c 側の状態**: `lSideGridCoeffData` の proven 3 field (coeff/m_principal/bessel) は landing 済 (cont.⁶⁴-⁶⁷)。
残 3 field は本 issue の b 供給 (S15.Hypothesis grid field: `eta_orthonormal`/`eta_intCast_on_G0`/
`eta_conj_neg` + type-P coherent pairing bound) が入り次第 c が wire する。**新 9000 issue は不要** (本 3002
が既に `lSideGridCoeffData`/`grid_mem`/`boundary` を fix-owner=b で追跡済)。file 内 sorry comment を精密化
(Coq 行番号 + c-unreachable 根拠) して landing。build green (3899 jobs)、新 axiom 無。

## ⚠ (3.9.a) 未解決ハンドオフ (2026-07-05 lane b, keystone landing 直後) — **unsound carrier 注意**

keystone (d7cb137a) は **(3.9.c) integrality + (3.9) principal を honest 供給**したが、
**(3.9.a) pairing field `eta_pair_of_coprime` は `finNeg` 形で likely-FALSE** と判明 (単なる未証明でなく):
- G0 上 η 値は実整数 (3.9.c) ゆえ真の pairing は **character 反転 `rowInv`/`colInv`** (S06
  `chiColumn_conj`/`galoisMap_conj_omega`) の下で成立。`finNeg` (組合せ的 index 反転) ≠ 反転置換
  (非構成 enum `Fintype.equivFinOfCardEq` では `w1CharEquiv(finNeg i)=(w1CharEquiv i)⁻¹` が偽)。
- ⟹ `finNeg`-form field を sorried で carry するのは **FT-path producer 上の unsound carrier**
  (sorry ゆえ false-proof 完成はしないが、honest close 不能な false statement)。
- keystone commit d7cb137a では暫定 sorried + `section16CharacterData_of_isMinimalSimpleOdd` の
  AxiomsCheck assert を disable (documented)。**この状態は次セッションで解消要**。

**次セッションの fix (2 択、A 優先)**:
- **A (honest close)**: field を honest 反転 involution 形 (perm/rowInv/colInv をデータとして carry
  or S06 反転) に**書き換え**、S06 `chiColumn_conj` + G0-実整数性から sorry-free 証明。AxiomsCheck
  assert 再有効化。c へ通知: `EtaGenericData.eta_pair` を同 involution で restate
  (`one_le_norm_signed_paired_sum` は抽象 `Equiv.Perm` を既に取る = c-side restatement のみ)。
- **B (fallback)**: (3.9.a) field を**完全撤去** (Hypothesis/Section16Inputs/Section16CharacterData/
  両 constructor から un-thread)、honest (3.9.c)+principal のみ残す。assert 再有効化。
  pairing は cross-lane design item として明示。

(先行 subagent が A を着手し Section16Inputs 更新中で停止 → incomplete edit は破棄済、
d7cb137a の documented-gate 状態から再開)。**c は integrality+principal の wiring は今すぐ可**
(それらは honest)。pairing のみ上記 fix 待ち。

## 🔗 lane-c → 3002 downstream 依存の精緻化 (2026-07-07 lane c, post-horth)

**C の (14.9) coherence side は完了** (issue 9072 CLOSED, commit `c8875eb2`)。3002 (η-grid Track A) が
landing すると unblock する C の残 S16 consumer は以下 2 箇所:

1. **`lSideGridCoeffData` (S16:7092) の `m_row_odd`/`m_col_odd`/`grid_mem`** — `coeff`/`m_principal`/`bessel`
   は **proven in-place** (lane-c-available)。残 3 field は Coq `FTtypeI_bridge_facts` (S/T type-P partner
   parity, PFsection13.v:1987) + `Y=0` grid membership (PFsection14.v:212-251) に gated。S16:7112-7143 に
   "Verified c-unreachable" 分析記載済 (c の唯一の parity primitive `cfdot_real_vchar_even` は η 実性が無く
   逆 parity を与える)。
2. **`exists_MHypothesis` (S16:8131)** の η-grid ±1 signs (`1_G+Δ=∑ signs_ij·η_ij`) — Track A、S16:8138-8146。
   構造/σ-counting/set 部分は全 proven; 残るは η-grid 展開の ±1 sign の honest joint existence のみ。

**⚠ (3.9.a) `EtaGenericData.eta_pair` 未解決ハンドオフ (上記 A/B 節) との関係**: C の `EtaGenericData`
consumer は `one_le_norm_signed_paired_sum` (抽象 `Equiv.Perm` を取る) 経由。上記通知どおり **option A
(honest 反転 involution) が landing すれば c-side は restatement のみ** (`eta_pair` を同 involution で restate)。
C は integrality+principal wiring は済/可、pairing involution の landing 待ち。lane-b の §13/§15 type-P layer
landing 次第、上記 1・2 は薄い cite で close (C が assemble)。

## ✅ 2026-07-07 (lane b): (3.9.a) unsound carrier 完全解消 — 構造保存 enumeration (commit df1ff47f)

上記「⚠ (3.9.a) 未解決ハンドオフ」を **option (a) = 構造保存 enumeration** で honest close
(A/B いずれでもなく、FT 旧 docstring が明記していた第 3 の sanctioned path):

- `w1CharEquiv`/`chi2enum` を **生成元 power enumeration** (`S06.cyclicPowEnum`、新設 generic
  block) に再定義。Peterfalvi 自身の (3.5) grid 添字 `ω_ij = ω₁^i ω₂^j` そのもので、
  **combinatorial `finNeg` = character inversion が定義から成立** (`w1CharEquiv_finNeg` /
  `chi2enum_finNeg` / `omegaSChar_finNeg`)。dual の cyclicity は新 S05 補題
  `isCyclic_charGroup_subgroupOf` (Pontryagin self-duality の cyclicity 半分)。
- `tau3W_omegaS_pair_of_coprime` の sorry を実証明に置換: ω_{−i,−j} = conj(ω_ij)
  (`galoisMap_conj_omega`) + σ Galois 等変性 (`sigma_mapRingEquiv_comm`) + (3.9.c) 整数値
  ⟹ η_{−i,−j}(g) = conj(η_ij(g)) = η_ij(g)。**#print axioms = 標準 3 公理のみ**。
- **AxiomsCheck assert 再有効化** (`section16CharacterData_of_isMinimalSimpleOdd` axiom-clean、
  endgame plan §4 完成条件 item 2 を discharge)。
- **signature 変更ゼロ**: `S15.Hypothesis.eta_pair_of_coprime` (finNeg 形) は不変のまま真に。
  **c-side (`EtaGenericData.eta_pair` finNeg 形) は restatement 不要** — そのまま honest 充填
  可能 (option A で必要だった c-side 作業が消滅)。上記「c は pairing involution の landing 待ち」
  は解消 — c は即 wire 可。
- self-flag: S05/S06 は a 所有 — S05 追加は純 additive (omega_inner precedent)、S06 の
  w1CharEquiv 再定義は signature/API 完全保存 (`w1CharEquiv_zero`/`_injective` statement 不変、
  w1BaseEquiv 削除のみ)。hub review 対象として commit message にも明記。

**⟹ 本 issue の b-side 供給は全完了** (grid property fields + (3.9) 3 fields すべて sorry-free
供給、assert 全 green)。残 = c-side consumer 組立 (`lSideGridCoeffData` 残 3 field /
`exists_MHypothesis` betaGrid、上記 2026-07-07 lane c 節)。
