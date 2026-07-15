---
id: 9077
slug: lane-c-frontier-exhausted-reallocation
title: "HUB 裁定要請: lane-c 独立 frontier 枯渇 — reallocation/方向 (2026-07-08 再確認)"
created: 2026-07-08
---

# HUB 裁定要請: lane-c 独立 frontier 枯渇 — reallocation/方向 (2026-07-08 再確認)

**起票者**: lane c (/loop、2026-07-08)。**判断者**: hub。**種別**: cross-lane reallocation 裁定。
**ユーザー指示**: 「ハブに聞くべき」(方向は hub が cross-lane 視点で裁定、lane は user でなく hub に問う)。

## 背景 — 2026-07-06 DORMANT 裁定の再確認要請

hub は 2026-07-06 夕に lane-c を **DORMANT cite-sink** 化した (merge_monitor 🧭、wf_00a0db07:
「S16 の 10 bare sorry は全て true carrier gate、ungated 行き先も無し」)。その後ユーザーが 07-08 に
`/loop Cレーンを進めます` で C を再起動。lane-c は 4 iteration 走り、**ungated な genuine 成果を追加産出**
した上で、**独立 frontier 枯渇を全数検証で再確定**した。**2026-07-06 の DORMANT 前提 (ungated 行き先無し)
は依然正しい**が、その後の C の追加 build により状況が更新されたので、hub の方向裁定を再要請する。

## 2026-07-08 lane-c 産出 (全 build-green・AxiomsCheck OK・新 axiom/新 sorry 無)

- `8a8ad379` — (13.18) 3 pin の gate を **単一 b-side mu-grounding field** (`hyp.mu = residueS.mu2`)
  に精密化 + `mu_row0_ne` の diagonal/logic を実証明し sorry を crisp 化。
- `6945ba5f` — **`hyp46S` = type-P2 `Hypothesis46`-for-S を sorry-free 構成** (ungated, `hypothesis46OfTypePData`
  instantiate、subH=M_σ の 4 obligation 実証明)。pin-2/3 が route する §6 certain-type infra を完成。
- `4cc9ad28` — **correctness 発見**: pin 2 (`tauS_mu_row0_diff_support`) は `∀ j` だが **j=0 で偽**
  (trivial column の degree mismatch)。consumer は `_hj:(j:ℕ)≠0` を持つ。fix = pin に `j≠0` 追加 + b が
  `_hj` pass (cross-lane 2-step)。
- `85457d49` — **C cluster の definitive gate map** (`notes/peterfalvi/s16_nonexistence_gate_map.md`)。

## 全数検証結果 — C cluster の 13 live sorry は全て a/b gate

| gate class | sorry (計 13) | issue |
|---|---|---|
| **lane-a σ-theory** (typeP_Galois exact-value / field model) | `hVcomm` (S16:1896)・`T_isTypeP2` (:1963)・`tSide_caseB_v` (:2063)・`s/t_side_frobenius_kernel` (:4515/4528) = **5** | 9000/9013 |
| **lane-b η-grid/grounding** | `lSideGridCoeffData` m_row/m_col/grid_mem (:7215/7218/7236)・`exists_MHypothesis` betaGrid (:8238)・pin ×3 (μ-grounding) = **8**; 加えて `T_typeIII_ratio_le` S-side βₛ (:1750) | 3002/9076/3003 |

- **C の ungated deep math は完了**: prime-TI 基盤 (`PrimeTIResidue`/`residueS` = 100% sorry-free) +
  `hyp46S` + pin scoping。**C 内に新規 ungated な証明仕事は無い** (2026-07-06 判定を追認、精度向上)。
- **ungated *upstream* も C 単独では取れない**: frobenius kernel を解く σ-theory field model
  (`FieldNormalizerData`/`TFieldModelData` 構成) は **issue 9000 = a/d claim 済**。C が降りると
  2026-07-02 の a-vs-d Singer dup を再演するリスク (policy 8 事案)。μ-grounding の spine discharge
  (`Section16CharacterData.muS = residueS.mu2`) は FeitThompson.lean (a-territory threading) 依存。

## hub に裁定を求める点

C の cluster は a/b に完全 gated、ungated upstream は a/d claim 済。この状況で C をどう配分するか
(hub が cross-lane 視点で決める案件、lane 単独判断でない):

- **(A) C を DORMANT cite-sink 継続 (2026-07-06 裁定を維持)** — gate landing (a の typeP_Galois 9000 /
  b の grid-grounding 3002・9076) 待ち。C 成果は in-place 保全、landing で pin/betaGrid を一気に close。
  → hub が「維持」なら lane-c session は idle 化 (busywork 回避)。
- **(B) C を特定 gate の cross-lane shared-infra 建設へ再配分** — 例: σ-theory field model (9000) を
  C が claim-coordination の上で build。**要 hub dedup ruling** (a/d の 9000 現況スキャン → C 参入可否)。
  多 session の deep 投資 ([[feedback-cost-scope-not-a-criterion]] 上コストは非基準だが dup は回避)。
- **(C) C を別 FT 経路へ redirect** — hub が unclaimed で C 適合の on-spine 上流を指定。
- **(D) その他** — hub の cross-lane 判断。

## hub への依頼事項 (併せて)

1. **pin 2 の `j≠0` 修正**を b の grounding-field 作業に束ねる調整 (issue 9076 に記録済、cross-lane 2-step)。
2. C の 4 commit は既に main 合流済 (`15c49a13` 経由)。方向裁定を merge_monitor 🧭 + 本 issue に記録依頼。

## 完了条件

hub が (A)-(D) を裁定し merge_monitor + 本 issue に記録。(B) 採択時は 9000 dedup ruling 込み。

## ✅ HUB RULING (2026-07-08 合流 tick、自律裁定 🧭 + subagent 調査) — (B) c は field-model leaf を build (DORMANT でない)

**裁定: 選択肢 (B)。lane c は DORMANT にせず、σ-theory semilinear field-model package
(`SemilinearFieldModel.lean` shared leaf + T-side `TFieldModelData` producer) を build する。
これは新規判断でなく、hub が 2026-07-07 に既に carve-out 済の作業の再確認** (issue [9000] scope note
item 2 / closed [0098] item 2 = 未着手)。着手 claim = [9078](9078-semilinear-fieldmodel-leaf.md) 起票済。

**調査 (hub subagent + 自己検証、code-level)**:
- **field model は genuine 未構築 gap**: 構造体 `FieldNormalizerData`(S16Core:620)/`TFieldModelData`(G0Coprime:800)
  + 両 transport (`derived_inf_centralizer_le_P/_le_Q`) は proven sorry-free。だが **T-side producer
  (`Nonempty (TFieldModelData hyp)` を作る項) は repo に存在せず**、`SemilinearFieldModel.lean` も未存在。
- **cleanly-separable (dup でない)**: field-model realization は a の Singer を **cite** (`S15.basic_structure`
  → SingerField 経由) して distinct object (`SemidirectProduct.lift` の σ-embedding) を build。`|U|∣p^q−1`
  Singer bound を再導出しない (frozen sorry-free で既存)。∴ 2026-07-02 の a-vs-d Singer dup を再演しない。
- **a は未着手**: `git rev-list --count main..a` = 0 (a は 0 ahead)、直近 15 commit は全て (11.8) fix で
  σ-theory 活動ゼロ。9000 の live claim は実質空き (d は 2026-07-07 退役)。

**根拠 (policy)**:
1. CLAUDE.md — gated / frontier 枯渇 / cost・規模・payoff の遠さ は着手/継続/reallocation 基準でない
   ([[feedback-cost-scope-not-a-criterion]])。gated lane は ungated upstream に降りる。field model は c の
   S16 sorry 5 本 (#3/#4/#5) の直接 gate ゆえ、build は c 自身の cluster を unblock する on-path 最上流。
2. DORMANT idle (選択肢 A) は最も policy 非整合 (lane を busywork 回避名目で遊ばせる)。genuine 未着手の
   hub-sanctioned leaf が在る以上、idle は不要。
3. **gated-endpoint skeleton** ([[feedback-gated-endpoint-skeleton-pattern]]): realization は (9.7.b) char body
   下流 (σ 構成に V-abelian = a の typeP_Galois output を input 要)。∴ c は V-abelian を **hypothesis 化**した
   engine+skeleton を今 build、a の char body landing で完全 close。「今すぐ full close しない」は非着手理由でない。

**c への directive** (9078 に詳細):
- claim [9078] 起票済 → 他レーン scan 対象。c は `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean`
  (module-level generic `F_{q^p}⋊V*` 実現、両 side instantiate) + T-side `TFieldModelData` producer を build。
- **分担境界**: c=field-model realization (cite a の Singer) / a=§9 block-decomposition + (11.9) char body。
  c は Singer bound を再構築しない。interface guard = module generic only + singerAdapter パターン再利用。
- **併記依頼 1 (pin-2 j≠0)**: issue [9076] に記録済 (cross-lane 2-step、b の grounding-field 作業に束ねる)。
  hub は b/c の 9076 tick で調整継続。

**2026-07-06 DORMANT 裁定は本 RULING で superseded** (当時「ungated 行き先無し」は field-model leaf が
未 carve だった時点の判断; 0098 item 2 再活性で ungated 行き先が確定)。C 既存成果は全 in-place 保全。

## 参照

- gate map: `notes/peterfalvi/s16_nonexistence_gate_map.md` (2026-07-08 CURRENT 表)。
- gate 詳細: issue 9076 (μ-grounding + pin-2 over-claim + hyp46S)・3002 (η-grid)・9000/9013 (σ-theory)。
- 着手 claim: [9078](9078-semilinear-fieldmodel-leaf.md) (SemilinearFieldModel leaf、本 RULING で起票)。
- scope 元: [9000] HUB scope note 2026-07-07 item 2 / closed [0098] item 2。
- 2026-07-06 DORMANT 裁定 (superseded): `notes/meta/merge_monitor.md` 🧭 + `ft_lane_reallocation_2026_06_28.md`。
- commits: 8a8ad379 / 6945ba5f / 4cc9ad28 / 85457d49。

## 🔁 2026-07-09 status: HUB RULING (B) = 9078 **完遂** → C 再枯渇、次 direction 要請

**RULING (B) の 9078 は完了** (lane-c /loop 2026-07-09, commit `8e6d3e61` 他, full build green・
AxiomsCheck OK・新 axiom 無):
- `SemilinearFieldModel.lean` leaf = `hcompatLift_of_equivariant` 追加で完成 (textbook 共役同変性 →
  generic `hcompatLift` 橋渡し、両 side 再利用)。
- **T-side producer `tFieldModelData_of_repr` = sorry-free 構成** (`fieldModelEmbedding` を E=Q,C=V,r=q,s=p
  で instantiate、`Nonempty (TFieldModelData hyp)`)。
- **`t_side_frobenius_kernel` = sorry-free 化** (gated-endpoint skeleton `t_side_caseB_fieldModel` 経由、
  `hVQ` 実証明、残 sorry = (9.7.b) field-data 存在 = lane-a gated)。
- AxiomsCheck に T-side sorry-free core 4 件登録 (fieldModelEmbedding/hcompatLift_of_equivariant/
  tFieldModelData_of_repr/derived_inf_centralizer_le_Q、各 3 axiom)。

**⟹ C 独立 frontier は再び枯渇** (9000 scope items 尽き: item1=9073 closed / item2=9078 done)。
2026-07-09 /loop で **代替 ungated target を全数再探索し、全て gated と code-level 再確認**:
- (14.9) `T_typeIII_ratio_le` hcount de-bundle を調査 → **blocked** (edit 前検証): `v=|V|` は
  `V_inf_centralizer_Q_eq_bot` (S15_SAndT:1891=**sorry**、T-side d=1) を cite、その proof は T-side
  `d_eq_one` dual を要し = **T-side v-value (13.15) = lane-a gated (9013)**。S-side c=1 が proven なのは
  S-side u-value が available だから (非対称)。∴ `V_inf_centralizer_Q_eq_bot` は C 単独 tractable でない
  (初回 iteration の「dual で tractable」判断を訂正)。gate map 「C 枯渇」結論を追認・精度向上。

**hub への要請**: RULING (B) 完了ゆえ次の cross-lane direction を再裁定 (A/B/C/D、正本 = 上記選択肢)。
9000 scope items は尽きたので (B) 継続は新 carve-out 要。当面 C は gate landing (a typeP_Galois 9000 /
b μ-grounding 3002・9076) 待ちで、landing 検知で pin/betaGrid/field-data を一気に close 可 (infra 完備)。

## ✅ HUB RULING #2 (2026-07-09 合流 tick、自律裁定 🧭 + 3-probe workflow wf_52474eb0) — (A-mod) temporary-hold (gated-endpoint、lazy idle でない)

**裁定: 選択肢 (A-modified) = temporary-hold**。lane c は全 ungated non-dup on-path slice を完遂済ゆえ、
a の 9000 char body / b の (13.4) route landing まで **gated-endpoint pattern で待機**する (self-resume monitor で
landing 検知 → 一気に close)。これは 2026-07-06 の DORMANT とは**質的に別** (当時は field-model leaf が未 carve;
今は c が全 buildable slice を実構築し切り真に gate 待ち = [[feedback-gated-endpoint-skeleton-pattern]] の正常態)。

**調査 (hub 3-probe workflow + high-confidence synthesis、code-level、304k tokens)** — 全 probe が
`c_buildable_ungated_nondup = false`:
1. **9013 T-side v-value (`V_inf_centralizer_Q_eq_bot` S15_SAndT:1889)**: c-buildable でない。lane-b の
   **active (13.4) route `lambda_forces_T_caseB`** (S15_SAndT_Setup:6088、~10+ commits 2026-07-07) に gated。
   c-file で re-derive = 9013 **案 B** で **hub が既に却下** (案 A = b generalize / c cite 採用)。dup HIGH vs lane-b。
   c の 9013 上の non-dup slice は既に構築+isolate 済 (`S16_CaseBOrder` engine、`tSide_caseB_v_gated_inputs`)。
2. **他 unclaimed on-path gap**: **無し**。GroupTheory/Mathlib shared-infra ~140 leaf は **real sorry 0** (未構築 leaf
   ゼロ)。残 gap は全て a (9000 σ-theory / (10.7) coherence / 1019) or b ((9.11) 1017 / (13.3) 2035 / η-grid 3002 /
   μ-grounding 9076) の active/claimed。unclaimed stub (tauS/tauT) は off-path。
3. **dup-verify**: a は 9000 を **real-time landing 中** (直近 6 commit 全 "9000 W2"、Frobenius crux
   S11_ImprimitiveUBound:147)。c の field-data gate (`t_side_caseB_fieldModel` S16:4551) の残 sorry の carrier は
   **まさに (9.7.b)/typeP_Galois char body = 9000 = lane-a**。engine (tFieldModelData_of_repr) は proven、char-body
   carrier のみ欠。→ c が降りると policy-8 dup incident の predicate-level 再演。

**根拠 (policy)**: **no-dup / policy-8**。gatedness は本来 stop 理由でないが、**残 gate が全て他レーンの ACTIVE work で
あり、降りると dup になる**場合は、待機が唯一の policy-compliant 選択 (strict dependency は並列化不能)。c は既に
全 non-dup slice を sorried-cite endpoint 化済ゆえ、これは gated-endpoint pattern であって lazy idle でない。

**c への directive**:
- **self-resume monitor で待機** ([[lane-autonomous-loop-policy]] (C)): active /loop を止め、`ScheduleWakeup` polling で
  **(i) a の 9000 typeP_Galois char body (hconst crux / hVcomm / t_side field-data) landing**、**(ii) b の (13.4)
  `lambda_forces_T_caseB` / μ-grounding (9076 `hyp.mu=residueS.mu2`) landing** を検知。landing 発火で pin ×3 /
  betaGrid / `t_side_caseB_fieldModel` / `V_inf` cite を**一気に close** (infra 完備)。
- **やらないこと**: 9000/13.4 への descent (dup)、off-path stub (tauS/tauT) 完成、9013 案 B (却下済)。
- **⚠ 例外的に新 unclaimed non-dup on-path gap が出現したら** (a/b が新 shared-infra を明示要求 等) 即再 engage
  (hold は gate 待ちであって永久停止でない)。

**hub 側フォロー**: a の 9000 / b の (13.4) landing を合流 tick で監視し、landing した tick で 9077 に「c 再 engage 可」を
追記 (c の self-resume が検知するが hub も明示 flag)。正本 = merge_monitor 🧭 + 本 RULING #2。

## 🔧 2026-07-09 lane-c (再開 session): RULING #2 の「infra 完備」を実体化 — pin 2/3 close engine 構築

ユーザー再開指示 → gate 全数再検証 (14 sorry 全て a/b gate 継続、RULING #2 hold 前提は有効) の上で、
RULING #2 が「landing 発火で一気に close (infra 完備)」とした前提を精査 → **pin 2/3 の
「grounding 仮説 → S06 定理で close」engine が未構築**と判明 (gated-endpoint skeleton の
最終部品)。c-buildable / non-dup (b の field 供給と直交) ゆえ即構築:

- `426c3ae1` — **Engine A `residueS_mu2_diff_support`**: Coq `prDade_sub_TIirr_on` の S-side
  instance (仮定形も Coq 忠実: `(j:ℕ)≠0`/`(k:ℕ)≠0`/度数一致)。pin 2 は grounding + j≠0 fix
  landing 時に one-line cite 化。+ refactor: `residueS` の data instance を scoped FiniteInduce
  供給に統一 (instance 項不一致による columnFamily-level defeq 破壊 = whnf timeout を根治)。
- `4cff46ce` — **Engine C `residueS_mu2_diff_dade_apply_of_mem_V`**: regular set 上の
  `τ_S(μ2-diff)(v) = δ·(ω^σ-diff)(v)` (Coq prTIirr_id 系)。Dade 側は
  `dadeIntegralCharacterMap_apply_of_support` + Engine A の support で完全 discharge。
  pin 3 の残 gap = **grid grounding のみ** (`hyp.mu = residueS.mu2` + η/ω^σ 同定) に精密化。

**close 態勢 (b の grounding field landing 時)**: pin 1 = `mu2_orthonormal` transport 一行 /
pin 2 = Engine A cite (度数は §13 具体値で discharge) / pin 3 = Engine C + η-grounding。
full build green 4128 jobs、AxiomsCheck OK、新 axiom 無し。

## 🎯 2026-07-10 lane-c (wakeup iteration): frobPU 実証明 — s_side gate は u-value 1 本へ

- `c3ccd231` — **`frobenius_PU_of_u_full` (sorry-free)**: Coq PFsection14.v:111-124 の frobPU
  (typeP_Galois_P → Frobenius_semiregularP) を完全実現。field model (`exists_pu_field_repr`)
  の μ-線形化で semiregularity、carrier + subgroupOf 搬送で complement 構造。
  `s_side_frobenius_kernel` の残 sorry = **hu_full = (13.15) u-value 1 本** (b の caseB_order_u
  / basic_structure sphere)。Coq galS chain と 1:1。
- 併せて SubgroupM 2074 行 → SubgroupMCore (985, sorry 0) + SubgroupM (1116, sorry 2) に
  prefix-split (2000 上限)。
- b の新 leaf `S12_TypeIIFrobenius` (typeII_HU_frobenius_of_coherent) は **(10.8) 帰謬法内部**
  (coherence 仮定下) の中間結果ゆえ §14 の無条件 frobPU には不適合と code/Coq-level で確認 —
  u-value 経由が正道 (dup せず独立に整合)。
- gate 残: pins ×3 (μ-grounding, b) / lSideGridCoeffData ×3 + betaGrid (β_S parity, b) /
  hu_full (u-value, b) / t_side field-data + hVcomm + v-value (9000, a) / V_inf ((13.4), b)。
  次 engine-prep 候補 = M-side betaGrid mirror (gate map 2026-07-09 追記節)。

## 🎯 2026-07-12 lane-c (再開 session): (11.8) endpoint 着地 — T-side (14.9) ratio bound sorry-free

再開時に前 session の未コミット (11.8) endpoint transport (mid-flight・build-broken) を発見 →
完成させて着地 (commit `97a7a596`)。RULING #2 の gated-endpoint engine-prep 系列の一部。

- **`T_typeIII_ratio_le` を local-sorry-free 化**: 最後の local sorry `hnotZeroRowProjection`
  (Coq (11.8) `FTtype34_not_ortho_cycTIiso`) を、canonical refuter を global σ/η grid equality
  + product pointer で η grid へ transport する `member_residual_not_orthogonal_eta_of_refuter`
  (TGapGridAlignment) で discharge。詳細 = issue 3004 末尾。
- 修正内容: TGapPrimeTI (`ν₀=Ind 1` 伝播)、TGapNonorthogonality (`s12Tau…` 結論の let 除去)、
  local haveI `Fintype`/`Invertible` diamond の `Subsingleton.elim` 橋渡し。
- full build 4177 jobs green・AxiomsCheck exit 0・新 axiom/sorry regression 無。

**frontier 状態の更新**: これで T-side (14.9) の ungated endpoint-transport は完了。9077 本文の
gate 表で `T_typeIII_ratio_le` に紐づいていた S-side βₛ 参照 (:1750) は本 endpoint とは別軸で、
`T_typeIII_ratio_le` 自体は sorry-free 化。残 S16 sorry は全て a/b/9000 gate のまま
(SubgroupM `s/t_side` = (9.7.b)/9000、SubgroupMCore `exists_betaMGridData` = b、
ComparingLM `lSideGridCoeffData` = b、TTypeII `hVcomm` = (11.9.c) Type-IV)。

**hVcomm 追加所見 (hub 宛、issue 3004 にも記載)**: lane a が (11.9.c) Type-IV 排除を landing し
`hVcomm` の discharge lemma (`not_isTypeIV_of_mem_maximalSubgroups`) を明記したが、それが在る
`S13_NonGaloisExclusion` は S16 を transitively import する上流 file ゆえ TTypeII から cite すると
file-level cycle。discharge には hub 裁定 (a が低レベル (11.9.c) U-abelian 補題を S16 下の file へ
分離、または spine consumer を a の版へ redirect) を要す。

**方向**: RULING #2 の engine-prep 候補 (M-side betaGrid mirror 等) は b の grounding field 待ち。
lane-c 独立 ungated frontier は再び枯渇。hub の reallocation/方向裁定を継続要請 (本 issue の standing ask)。

## 🧭 HUB RULING #3 (2026-07-12 監視 tick, Opus hub 自律裁定) — hVcomm DAG-block: 選択肢 (A) を lane a に割当

c の hVcomm DAG-block 報告を hub が import-graph で独立検証し、**block は real と確定**。裁定 = **選択肢 (A)
(低レベル Type-IV/U-abelian 補題を S16 より下の leaf へ分離) を lane a に割当**。

**検証結果 (hub の transitive closure 計算)**:
- `S13_NonGaloisExclusion` の closure (513 mod) は **S16 全体 (TTypeII 含む) を包含** → downstream of S16。
  よって TTypeII (S16 内) から `S13_NonGaloisExclusion` を import すると file-level cycle。**c の診断は正しい**。
- cycle を起こす import は **`S13_TypeDetermination` ただ 1 つ** (S13_NonGaloisExclusion の 4 direct import
  のうち; 他の S13_TypeIIIGalois / S11_MaximalII_III_IV / NilpotentAbelianization は S16-free)。
- **(A) は原理的に可能**: S16-free な 3 import (S13_TypeIIIGalois + S11_MaximalII_III_IV +
  NilpotentAbelianization) のみを import する新 leaf の closure (419 mod) は **S16 を含まない** →
  そこへ 5 補題を置けば TTypeII が import 可能。

**割当 = lane a** (a が `S13_NonGaloisExclusion` + 5 補題 + FeitThompson spine を所有ゆえ territory 内、
cross-lane 衝突なし)。**具体タスク**:
1. `S13_NonGaloisExclusion` から低レベル Type-IV/U-abelian 補題群
   (`U_isMulCommutative_of_hypothesis` / `not_isTypeIV_of_hypothesis` /
   `isMulCommutative_typePData_U_of_typePData_U` / `U_isCyclic_of_hypothesis` /
   `not_isTypeIV_of_mem_maximalSubgroups`) を **新 leaf** (例 `S13_TypeIVExclusionCore.lean`) へ抽出。
2. 新 leaf は **`S13_TypeDetermination` を import しない** (S16-free 保持)。`S13_NonGaloisExclusion` は
   新 leaf を import して従来どおり cite (下流不変)。
3. **a が要検証**: 5 補題の proof が `S13_TypeDetermination` 固有の内容 (S16 経由でしか無い symbol) を
   使っていないか。使っていれば当該依存を先に S16 下へ hoist。使っていなければ leaf 抽出のみで完了。
   (statement が参照する `Hypothesis`/`TypePData`/`IsTypeIV` は §11 type-primitive ゆえ upstream 期待。)

**選択肢 (B) (spine consumer redirect + TTypeII local Type 判定 obsolete) は却下**: より invasive で
FT spine の Type-determination 組立に触れ、c が「TTypeII 内で consume」と報告した `T_typeII` 局所論法を
obsolete 化するリスク。(A) が最小 blast radius。

**c への unblock 経路**: a が新 leaf を landing 後、**c は TTypeII の `T_not_isTypeIV_of_isTypeP1` の
hVcomm を新 leaf の `not_isTypeIV_of_mem_maximalSubgroups` (相当) cite で discharge** (c territory 内、
S16 下 leaf ゆえ cycle なし)。これは c の TTypeII 残 local sorry を 1 本消す genuine FT-path 前進。

**c の広域 frontier 枯渇**: RULING #2 の gated-endpoint pattern を継続 (M-side betaGrid mirror 等の
engine-prep は b の grounding field 待ち)。c は上記 hVcomm unblock (a の leaf 待ち) を次の re-engage
trigger とし、それまで gated-endpoint 化した slice で待機 (lazy idle でない)。hub は a の新 leaf landing を
監視し、landing tick で本 issue に「c 再 engage 可 (hVcomm)」を flag する。

## 🧭 HUB RULING #4 (2026-07-12 監視 tick, Opus hub) — c frontier 枯渇の正式裁定 (fresh 全数 census)

RULING #3 では枯渇を RULING #2 継続と再確認しただけだったので、hub が c 所有 S16_NonExistenceG の
**残 bare sorry 7 本を全数独立に読み、gate を census**した上で正式裁定する。

**census 結果 (全 7 本 genuine gated、c-unreachable 分析付き)**:
| sorry | gate lane | 詳細 |
|---|---|---|
| SubgroupMCore:853 `exists_betaMGridData` | **b** | (13.19.b) coherence + carrier `phi_mem` の `Lset=Sset` 露出待ち |
| SubgroupM:187 `hu_full` (\|U\|-value) | **b** | (13.15) u-value = caseB_order_u/basic_structure producer |
| SubgroupM:247 T-side field-data | **a** | 9000 t_side field-model (μ compatibility) |
| ComparingLM:345 `m_row_odd` | **b** | 3002 S-side β_S parity (S15_SAndT, Coq FTtypeI_bridge_facts) |
| ComparingLM:348 `m_col_odd` | **b** | 3002 双対 T-side parity |
| ComparingLM:366 `grid_mem` (Y=0) | **b** | 3002 (parity 依存)。NC≤2 engine 不適用 (pq≥15)、bessel は ⟨Y,Y⟩≥0 止まり |
| TTypeII:883 `hVcomm` | **a** | RULING #3 抽出 leaf 待ち |

**裁定 1 — 枯渇は real**: 7 本すべて a/b の **active work** に gated (b=5, a=2)。各注記は具体的
c-unreachable 理由 (使える parity primitive が逆 parity を出す / proven engine の適用条件外 等) を
明示しており、c の自己申告は正確。**追加の ungated genuine work は無い** (RULING #2 の 3-probe
workflow 2026-07-09 結論を fresh census が追認: 残 gate は全て他レーン active territory で、降りると
policy-8 dup; GroupTheory/Mathlib shared-infra の real sorry は 0)。

**裁定 2 — posture = gated-endpoint self-resume (reallocation でない)**。理由:
(a) c の gate は **a/b が現に active に閉じつつある** (stalled でない — b は 2038/(13.19) を、a は
(11.9.c)/9000 を landing 中で、これらが c の gate 本体)。
(b) c が gate 本体に降りる = a/b の active file (S15_SAndT/9000 char) 編集 = **policy-8 dup + 退役 lane d
の失敗モード (codex dup churn)**。密結合 char/coherence に 2nd operator を入れる害。
(c) c の役割は構造的に **downstream assembler** (§14 非存在 + parity 矛盾の組立)。a/b の char/coherence
が揃うまで gated なのは misallocation でなく FT endgame の DAG 構造そのもの。

**裁定 3 — c は idle でなく engine-prep を継続**: 本 tick で c は (11.8) `T_typeIII_ratio_le` を
local-sorry-free 化 (endpoint を「真の gate のみ残す」状態に整備) = gated-endpoint pattern の正しい
実行。これを続け、各 a/b landing で該当 endpoint を re-engage。

**dated re-engage triggers (hub が監視、landing tick で本 issue に flag)**:
- a: RULING #3 S16-free leaf landing → c: TTypeII `hVcomm` discharge (−1 sorry)。
- a: 9000 t_side field-data landing → c: SubgroupM:247。
- b: (13.15) u-value landing → c: SubgroupM:187。
- b: 3002 β_S/β_T parity landing → c: ComparingLM ×3 (m_row/m_col_odd → grid_mem)。
- b: (13.19.b) coherence + carrier field 露出 → c: SubgroupMCore exists_betaMGridData。

**結論**: c は「枯渇したが gated-endpoint 化で最大限前倒し済、a/b の active landing 待ち」が正しい
状態。hub は reallocation せず、上記 trigger を毎 tick 監視して c の re-engage を driving する。

## 🎯 2026-07-12 lane-c (trigger 監視 loop, tick 1): T5 発火 — exists_betaMGridData discharge

RULING #4 の dated re-engage trigger の一つが発火。lane b が (13.19.c) を完結
(`typeIOrthogonalityGridData_of_coherent78` producer + `Lset:=typeIHyp.Sset` landing、
merge afc368a0/a2fe7a0b) → c が該当 endpoint を re-engage:

- **`exists_betaMGridData` discharge** (commit `51a39e2f`): b の landed producer を `Mdata.coherent78`
  で instantiate (`IsTypeP2 T` は `T_typeII` から供給、BetaVanishing と同一パターン) し `phi_mem`
  を projection。**SubgroupMCore は sorry-free 化**。full build 4177 jobs green、AxiomsCheck exit 0。

**census 更新 (RULING #4 の 7 → 6)**:
- ✅ SubgroupMCore `exists_betaMGridData` (旧 :853) = **discharged** (b の (13.19) landing 発火)。
- 残 6: TTypeII hVcomm (a, RULING #3 leaf 待ち) / SubgroupM hu_full (b, u-value) /
  SubgroupM t-side field (a, 9000) / ComparingLM m_row_odd/m_col_odd/grid_mem (b, parity)。

**T4 (ComparingLM parity) の再評価**: b の (13.19.c) dichotomy は landing したが、`m_row_odd` の
(c2) odd parity を得るには c1 disjunct の排除 (caseB gap) が必要。`lSideGridCoeffData` の signature
には gap が無く (`hq3`/`hp5`/`hepq` のみ)、gap は上位 consumer 供給ゆえ **T4 は未発火** (依然 b-gated、
"c-unreachable" コメントは概ね有効)。b が `FTtypeI_bridge_facts` の parity を直接 citable な形で
export するか、consumer 側で gap を threading する landing が次の T4 trigger。

## 📌 2026-07-13 lane c 一時停止 (ユーザー) — 再開判定はユーザー通知が必須

ユーザーが lane c のセッションを一時停止 (2026-07-13、hub セッションで口頭指示「C はいったん
止まっているので、再開する必要が出てきたら教えてね」)。RULING #4 の gated-endpoint self-resume
は c セッションが走っていることを前提とするため、**以後 hub は re-engage trigger の landing を
検出したら、本 issue への flag に加えて必ずユーザーへ明示通知する** (tick サマリ冒頭で
「lane c 再開推奨 + 発火 trigger + 対象 endpoint」を報告 + PushNotification)。

現行の残 trigger (RULING #4 census 残 6 対応、T5 は 2026-07-12 発火済):
- **T1**: a の S16-free Type-IV 排除 leaf landing (RULING #3 の抽出) → c: TTypeII:885 `hVcomm` discharge
- **T2**: a の 9000 t_side field-data landing → c: SubgroupM:247
- **T3**: b の (13.15) u-value landing → c: SubgroupM:187 `hu_full`
- **T4**: b の 3002 β_S/β_T parity の citable export (or caseB gap threading) → c: ComparingLM ×3
  (m_row_odd/m_col_odd → grid_mem)

いずれか 1 本の発火で通知 (全部揃うのを待たない — c は 1 endpoint 単位で re-engage 可能)。

## 🔬 2026-07-13 独立全数再検証 (ユーザー要請、workflow wf_905a48ba / 17 agents / 199万 tokens)

ユーザーが「C レーンで本当にやることが無いか」を独立検証するよう指示。main 同期 (0 behind) 後、
**6 gated sorry を各々 verify+敵対的 skeptic、加えて 4 descent probe** (shared-infra / 非S16 territory /
trigger 発火 / off-path) を並列実行。**#print axioms を fresh rebuild で直接実行**して census-based の
誤判定を潰した。**結論 = TRULY_EXHAUSTED を追認** (RULING #4 census と完全一致、精度向上)。

**6 sorry の最終 gate (全て STILL_GATED、skeptic UPHELD)**:
| sorry | gate | 検証で確定した実状態 |
|---|---|---|
| TTypeII:886 `hVcomm` | **a (RULING #3 leaf)** | ⭐ **下の nuance 参照** — deep math は done、残るは a の機械的抽出のみ |
| SubgroupM:187 `hu_full` | **b** | (13.15) `caseB_order_u` = OrderDetermination.lean:774 **raw sorry** |
| SubgroupM:247 t-side field-data | **a/b** | Singer engine proven、必須の `character_degree_analysis` (13.3) = Machinery135.lean:181 **raw sorry** (issue 2035) |
| ComparingLM:353/356 `m_row/m_col_odd` | **b** | census route は **false positive**。#print axioms で `typeI_caseC_dichotomy`/`_dual_dichotomy` が **sorryAx 保持** (`V_inf_centralizer_Q_eq_bot` 13.12 T-side v-value = 9013 lane-b) と確認 |
| ComparingLM:374 `grid_mem` | **b** | engine `etaGrid_projection_rigidity` は m_row/m_col の odd-parity を入力に要求 → parity gated ゆえ gated。閉じても新規 discharge 無 (純 sorry-count 削減) |

**4 descent probe = 全て `ungated_work_found: false`**:
- shared-infra (GroupTheory/Mathlib/Algebra ~140 leaf): **real sorry 0** (RULING #2 追認)。c の 6 gate は
  どれも「未構築 shared leaf」に帰着しない (generic 前提は全て構築済 sorry-free)。
- 非S16 territory: **Clifford 9002 完全** (全 leaf 0 sorry)、**9013 carve-out `reconciled_typePData_T` は
  sorry-free** (CountingLayer.lean:757、残 2 sorry の 1619/1740 は lane-b territory)。
- trigger 発火: **T1-T4 全て UNLANDED**。
- off-path/engine-prep: gate map の「M-side betaGrid mirror」は既に done (T5 発火時)。c-buildable な残り無し。

### ⭐ hVcomm の gate 性質が変化 (T1 refinement、hub 宛の最重要所見)

`hVcomm` (TTypeII:886) の gate は**もはや「a/b の deep active math」ではない**:
- 親定理 `T_not_isTypeIV_of_isTypeP1` が必要とするのは `¬ IsTypeIV hyp.base.T` のみ。その producer
  **`not_isTypeIV_of_mem_maximalSubgroups`** (S13_NonGaloisExclusion.lean:1007) は **今 sorry-free**
  (fresh rebuild + #print axioms = `[propext, Classical.choice, Quot.sound]`、no sorryAx)。(11.9.c) chain
  全体 (`not_isTypeIV_of_hypothesis`/`U_isCyclic_of_hypothesis`/`not_cliffordCaseA_of_hypothesis`/
  `S_H0C_not_coherent_unconditional`) も comment-strip 後 0 real sorry。
- c が閉じられない唯一の理由 = **file-level import cycle** (`S13_NonGaloisExclusion` は
  `S13_TypeDetermination` 経由で S16 を transitive import; BFS 確認)。∴ TTypeII から直接 cite 不可。
- 解消 = **RULING #3 の S16-free 抽出 leaf `S13_TypeIVExclusionCore` を lane a が作る** (未着手、
  `git log --all` で不在)。これは a territory の**機械的 refactor** で、依存する deep math は既に完了。

**⟹ T1 の blocker は「a の active math 待ち」から「a の未着手な機械的 RULING #3 抽出待ち」に降格**。
これは c の frontier を 1 sorry 縮める**最高レバレッジかつ今 unblock 済**の次手。hub は lane a に
RULING #3 抽出 (5 補題を S16-free leaf へ) を driving し、landing 後に c へ hVcomm re-engage を通知するのが
最善。他 5 sorry は依然 a/b の genuine な未証明 char/coherence/parity 待ちで c-unreachable。

**posture 変更なし**: c は idle 継続 (gated-endpoint hold) が正しい。ユーザー再開は上記 T1 (a の leaf) or
T2-T4 landing 時。検証は .lean 無変更 (docs のみ)。

---

## ✅ T1 RESOLVED (2026-07-13, lane a) — `hVcomm` 閉包・(14.9) type-III determination が axiom-clean

9077 T1 の推奨 (「lane a が S16-free 抽出 leaf を作る」) は **9093 の import inversion が先に上位解決**:
`S13_TypeDetermination` の downstream producer が `FeitThompsonPairProducer` へ移設された結果、
`S13_NonGaloisExclusion` の transitive closure から `Peterfalvi.S16_NonExistenceG.*` /
`FeitThompsonSetup` が消滅 (BFS 検証済、closure 648 modules 中 S16 系 0)。**抽出 leaf は不要になった**。

これを受け lane a が TTypeII.lean の `hVcomm` residual を機械的に閉包 (RULING #3 の consumer 追従 pattern、
c は idle 確認済・hunk 衝突なし):
- `import OddOrder.Peterfalvi.S13_NonGaloisExclusion` 追加 (acyclic BFS 確認済)。
- `T_not_isTypeIV_of_isTypeP1` の body を producer 直 cite に置換
  (`not_isTypeIV_of_mem_maximalSubgroups hG hyp.base.T_maximal` — producer docstring 記載通り)。
  bare sorry −1 (`hVcomm`)。

**検証**: full `lake build OddOrder` green (4187 jobs) + 新 AxiomsCheck asserts OK —
`T_not_isTypeIV_of_isTypeP1` / **`T_isTypeIII_of_isTypeP1` (14.9 type-III determination) が
axiom-clean** (`[propext, Classical.choice, Quot.sound]`)。

**c への通知**: T1 は landing 済。`T_typeII` はまだ dirty (残 residual = `T_isTypeP2` 系 carrier、
T2-T4 の genuine char/coherence/parity 待ちで変化なし)。c の idle posture 変更は hub 判断。

## 🔄 再発 (2026-07-14 夕、lane c → HUB): c-territory 再消化完了 — reallocation 要請 #2

本日の landing (issue 0115 全消化 + α): ⚠hu_full statement 修正 / Campaign A (parities +
honest Y=0/χ classification) / Campaign B (T-side field model discharge)。consumer-traced
census の結果:

- **c-owned S16 の local sorry = `s_side_field_repr` 1 本のみ** (a の 9000/9097 pipeline 待ち、
  0115 裁定 2 の a→c pipeline)。§16 endgame ((14.12)-(14.16) → spine → AppC) は配線完結済み。
- **FT-path 残 sorry は全て owned**: S15_SAndT_Setup 層 + S15_SAndTBasic:839
  (V_inf_centralizer_Q_eq_bot — `T_caseB_facts_unconditional`+`D_eq` で discharge 可能と
  0115 に note 済み) + S15_CharacterDegreeSupply + S14_MaximalI/FrobeniusStructure:117
  (`sibleyTarget_frobI`、docstring に証明 sketch あり: TI → dade.H=⊥ → SibleyTarget) = **b**;
  OrderDetermination 3 本 + BG TypePDuality/GlobalCounting = **a**; NormEstimates/CountingLayer
  layer-inversion = **hub 0116**; TheoremsAE:31 = 意図的 legacy scaffold (faithful 版 landed 済)。
- 教訓反映: 本 census は consumer 側 (`H_eq_U`/spine) から遡って実施 (iteration-4 の重複事故の
  再発防止)。

**HUB への要請**: c の次 assignment の裁定 (候補: (i) b 過負荷分の carve-out — 例:
`sibleyTarget_frobI` 単発 or V_inf_centralizer_Q_eq_bot discharge の実施権、(ii) a の
s_side_field_repr pipeline の一部、(iii) その他)。裁定まで c は hub tick を polling。

## 🧭 HUB RULING #3 (2026-07-14 夕、要請 #2 への裁定): 候補 (i) 採用 — b quiet file 2 宣言の carve-out を c に付与

**c の次 assignment = b-owned quiet file の個別 2 宣言 (proof-only carve-out)**:
1. `V_inf_centralizer_Q_eq_bot` (S15_SAndTBasic.lean:839) — c 自身が 0115 に discharge route を
   note 済み (`T_caseB_facts_unconditional` + `D_eq`)。b が本日 landing した (13.4) theta-package
   assembly / T_caseB 系の**消費** (assembly work) であり b の active 作業と重複しない。
2. `sibleyTarget_frobI` (S14_MaximalI/FrobeniusStructure.lean:117) — docstring に証明 sketch あり
   (TI → dade.H=⊥ → SibleyTarget)、(12.17)→(12.7) chain root (9087 注記)。単発 obligation。

**根拠**: 両 file とも b の本日 hot set (Tau1T/NuRowPin/TSetMemberRFamily/CharacterDegreeSupply/
SubcoherenceInputs/TSideDegrees) と非交差の quiet file。b は 2035 #41 step 5 続行に専念。
候補 (ii) (s_side_field_repr pipeline) は **却下** — a が 0115 実施報告で「次 frontier =
(13.15) caseB_order_u」と宣言済みで衝突する (a→c pipeline は a の landing 待ちが正)。

**条件** (9087 carve-out と同型): (1) 当該 2 宣言の proof 充填以外の編集禁止 (statement/
signature 不変; 必要な helper は c-owned or 新 shared leaf claim へ)、(2) 宣言ごと単独 commit +
message self-flag、(3) landing で失効、(4) AxiomsCheck 追従 + 結果を本 issue と 2035 に記録。

## ⚠ HUB 追記 (2026-07-14 監視再開時): RULING #3 item 1 は DAG-blocked — item 2 を先に

0116 relayer 調査 (wf_746d2ebb + hub import-path 検証) の副産物として、**RULING #3 item 1
(`V_inf_centralizer_Q_eq_bot`, S15_SAndTBasic:839) の c 自身が note した discharge route
(`T_caseB_facts_unconditional` + `D_eq`) は現 DAG で不可能**と確定:

- `T_caseB_facts_unconditional` は S15_CharacterDegreeSupply:2227 にあり、その import 閉包は
  CDS → CaseACoherence → … → TSetMemberRFamily → BridgeCharacter → … → SAndTBasic を含む =
  **CDS は SAndTBasic の strictly 下流** (T_side_caseB_facts (TTypeII:191) 経由も同様に下流)。
  SAndTBasic 内の proof-only 充填からはどちらも cite 不能 (import すると cycle)。
- D = ⊥ の honest 供給は (13.4) 系のみ (それが (13.12)-T d=1 の内容) なので、SAndTBasic 内での
  代替 in-place route も無い。

**c への指示**: item 1 は HOLD し、**item 2 (`sibleyTarget_frobI`,
S14_MaximalI/FrobeniusStructure.lean:117) から着手** (S14 層で layer-block なし、docstring に
証明 sketch あり)。item 1 の unblock は hub の 0116 Route T 実施 (obtain-site を CDS 下流の
discharge leaf へ移す) 後に「c 再 engage (V_inf)」を本 issue に flag する — その際 item 1 の
carve-out は「discharge leaf 側 obtain-site の proof 充填」に re-scope される見込み
(statement/signature は SAndTBasic 側不変のまま hub が配線)。0116 の sequencing (b の hT2 弱化
裁定 + a の OrderDetermination cluster quiet 化待ち) は 0116 参照。

## 🎯 2026-07-14 lane-c: RULING #3 item 2 (`sibleyTarget_frobI`) 実施報告 — 構成 landed、⚠ signature gap 1 点発見

hub 追記 (「item 1 DAG-blocked → item 2 先行」) と**独立に同一結論に到達した上で** item 2 を実施
(c 側でも import-BFS で CDS ⊋ SAndTBasic を確認済み — hub 検証と一致、item 1 は HOLD 了解)。

**item 2 landed (commit `237ff7fc`)**: `sibleyTarget_frobI` の (6.8)(c1) 構成を実装。
docstring sketch (TI → dade.H=⊥ → SibleyTarget) どおり + template `typeVSibleyDadeHypothesis`
(S12_TypeVSibley) 踏襲。TI bound 縮小は `normalizer_sharpSubgroup` + (8.15) `normalizer_eq`、
Dade datum は transport 3 定理 (file 冒頭、この用途に設計済み) で `hyp.tau` を exact 保存、
`S_eq := rfl` (binder→FiniteInduce instance 統一 subst)。full build 4209 jobs green /
AxiomsCheck OK / 新 axiom 無し。

**⚠ 発見 (hub/lane-b 宛): `card_L_odd` signature gap** — 残 bare sorry はこの 1 点のみ (net ±0):
- `SibleyDadeHypothesis.card_L_odd : Odd (Nat.card ↥L)` は `sibleyTarget_frobI` の現 hypotheses
  から**導出不能**。G は任意有限群 (`IsMinimalSimpleOdd`/parity 入力ゼロ; `Hypothesis`/`TypeIData`/
  `TypeFData`/`DadeSupportHypothesisData` の全 field を精査、parity 無し)。反例モデル: G=S₄,
  L=S₃ (Frobenius C₃⋊C₂、C₃^# は S₄ で TI、(8.15) data 構成可) で全 hypotheses 成立 +
  |L|=6 偶数 ⟹ goal 型が空 = **statement-level unprovable**。
- 対照: type-V producer `typeVSibleyDadeHypothesis` は `hG : IsMinimalSimpleOdd G` を取り
  `card_L_odd := hG.odd.of_dvd_nat ...` (S12_TypeVSibley:264) — 同じ供給が (c1) 側にも要る。
- **提案 fix (2 行)**: `sibleyTarget_frobI` に `(hodd : Odd (Nat.card G))` (または `hG`) を追加し、
  唯一の caller `frobenius_typeI_coherent` (同 file、`hG` 保有) で `hG.odd` を thread。
  carve-out 条件 1 (signature 不変) により c は凍結中 — hub/b の approve で c が即 1-line close。

**posture**: item 1 = HOLD (0116 Route T 待ち、hub 追記どおり)。item 2 = 上記 approve 待ち。
両 item 消化につき c は gated-endpoint hold へ復帰 (trigger: 本 flag への hub 応答 / Route T
実施後の「c 再 engage (V_inf)」flag)。

## 🧭 HUB RULING #4′ (2026-07-14 tick 49): card_L_odd signature fix を承認 — c は即実施可

c の item 2 実施報告 (`card_L_odd` signature gap、反例 G=S₄/L=S₃ で statement-level
unprovable) を受理し、**提案 fix を承認する**:

- **`sibleyTarget_frobI` への odd 仮説追加を承認** — `(hodd : Odd (Nat.card G))` を推奨
  (mathlib 流の最弱仮説; `hG : IsMinimalSimpleOdd G` でも可 = S12_TypeVSibley:264 template
  との一貫性優先なら)。どちらを採るかは c の file-idiom 判断に委ねる。
- 唯一の caller `frobenius_typeI_coherent` (同 file、hG 保有) への thread も併せて c が実施。
- **carve-out 条件 1 (signature 不変) は本宣言に限り本 RULING で解除** — これは恣意的
  signature 変更でなく **faithfulness 訂正** (unprovable statement の修正 = hu_full tick 44 /
  9017 Thm 15.8 訂正と同クラス)。教科書 (Peterfalvi) は全編 odd-order G の文脈で、S12 の
  type-V producer が hG を取るのと同じ供給が (c1) 側に欠けていただけ。
- 条件: (i) 変更は odd 仮説追加 + caller thread のみ、(ii) 単独 commit + self-flag、
  (iii) build green + AxiomsCheck 追従。b への通知は本 RULING で足りる (FrobeniusStructure
  は b の quiet file、caller まで同 file 内で外部 blast radius ゼロ)。

c の再開 trigger 成立: **item 2 の 1-line close を即実施してよい**。完了後は報告どおり
gated-endpoint hold へ (次 trigger = 0116 Route T 後の「c 再 engage (V_inf)」flag)。

## ✅ 2026-07-14 lane-c: RULING #4′ 実施完了 — item 2 完全 close (`frobenius_typeI_coherent` axiom-clean)

RULING #4′ の承認どおり実施 (commit `1da9aa29`、単独 commit + self-flag):
- `sibleyTarget_frobI` に `(hodd : Odd (Nat.card G))` 追加 (推奨の最弱仮説形を採用)、
  `card_L_odd := hodd.of_dvd_nat …` (template と同型)。residual sorry 除去。
- caller `frobenius_typeI_coherent` に `hG.odd` thread (同 file 内 1 行)。
- AxiomsCheck に `sibleyTarget_frobI` + `frobenius_typeI_coherent` の 2 assert 追加
  (longFile 8100→8300 bump 込み)、**両方 axiom-clean 認証** ([propext, Classical.choice,
  Quot.sound])。full build green (4214 jobs)。net sorry −1、FrobeniusStructure 実 sorry 0。

**milestone**: Peterfalvi **(12.6) が全 3 route ((a) TI/(6.8)・(b) abelian rank-2 (5.7)・
(c) cyclic-quotient (6.5.c)) 実証明で完結**。下流の §16 consumer (S16_PairingCoherence:901 /
ComparingLM:1322 — いずれも c cluster の coherence 供給) の sorry-root が 1 本減。

**carve-out 消化状況**: item 2 = **CLOSED** (RULING #3 条件 3 により本 item の carve-out 失効)。
item 1 (V_inf) = HOLD 継続 (0116 Route T 待ち)。c は gated-endpoint hold へ復帰 —
trigger: (α) Route T 実施後の「c 再 engage (V_inf)」flag、(β) a の 9000/9097 pipeline landing
→ `s_side_field_repr` (c-owned SubgroupM の最後の local sorry)。

## 🧭 HUB RULING #5 (2026-07-15, issue 0118 再設計) — c の hold 解除: 即着手 2 件 + 更新済み trigger

3 レーン再設計 (issue 0118) に伴い c の gated-endpoint hold を**部分解除**:

- **即着手可 (ungated と監査確定)**: (c-1) `caseB_order_u_data` bridge retire (SubgroupL:200 /
  TTypeII:924 rewire → bridge 削除、CaseBOrder への削除 carve-out 付与) / (c-2) BG vestigial 整理
  (theoremA_maximal_structure retire + S14 2 本の注記 + stale docstring 修正)。詳細 = 0118。
- **item 1 (V_inf) の trigger 更新**: 「hub の Route T」→「**lane a の 0116 full flip landing**」
  (実行 owner 移譲のため)。landing tick で hub が本 issue に「c 再 engage (V_inf)」flag を出す。
- trigger β (s_side_field_repr) は a の 0117 討伐で消化済み (moot)。

## ✅ 2026-07-15 lane-c: C-1 完了 — `caseB_order_u_data` compatibility bridge retire

issue 0118 c-1 の指示どおり、`CaseBOrderUData` / `caseB_order_u_data` を削除し、consumer 2 箇所を
honest producer へ再配線した (本節と同一の単独 feature commit):

- `caseB_for_S` は `exists_chiefFactorData` と `clifford_dichotomy` から実際の Clifford dichotomy を
  構成する。case A は `caseA_parameters` + `c_eq_one` + S-side `TypeIOverNormalizerData` による
  矛盾で排除し、case B では得られた `CliffordCaseBData` の `Nonempty` certificate と proven
  `caseB_order_u` の 2 つの位数等式を保持する。旧 `True` compatibility carrier は消滅。
- `T_isTypeP2` 側の旧 dummy bridge call は、同じ不等式を直接与える unconditional theorem
  `Hypothesis.u_le_cyclotomicQuotient` に置換。この theorem は AxiomsCheck で
  `[propext, Classical.choice, Quot.sound]` のみと認証済み。
- b-owned quiet file `S15_SAndT_Setup/CaseBOrder.lean` は RULING #5 が明示した deletion
  carve-out の範囲だけ編集し、上記 structure/theorem の削除以外は変更していない。

**検証**: main 再同期後 `lake build OddOrder` green (4225 jobs)、
`lake build OddOrder.AxiomsCheck` green (4210 jobs)、旧 2 識別子の `OddOrder/` 内参照 0、
`git diff --check` clean。

**axiom trace の限定**: `caseB_order_u` / `caseB_for_S` 自体は、既知の上流未証明 obligation
(`c_eq_one`, `numeric_bounds`, `analytic_inequality`) に由来する `sorryAx` をなお継承する。
これは今回削除した compatibility bridge とは別 root であり、本節は両 theorem の
axiom-clean を主張しない。今回 bridge の代替として T-side が直接使う
`u_le_cyclotomicQuotient` だけを permanent AxiomsCheck に追加した。

**self-flag**: c-1 は上記 b-file deletion carve-out を含む単独 commit。次 frontier は issue 0118
c-2 (BG vestigial cleanup: `theoremA_maximal_structure` retire、S14 frozen 注記、stale docstring 修正)。

## ✅ 2026-07-15 lane-c: C-2 完了 — BG vestigial surfaces 整理

issue 0118 c-2 の指示どおり、faithful successor が定着した BG Theorem A の旧 surface と、
statement-level に誤っている S14 の historical surfaces を整理した:

- bare `theoremA_maximal_structure` は `OddOrder/**/*.lean` の exact-name audit で consumer 0 を
  再確認し、宣言ごと retire。`theoremA_maximal_structure_faithful` を唯一の monolithic Theorem A
  API とし、standalone conjunct helpers / AxiomsCheck / 周辺 docstring もこの canonical route に統一。
- `nonidentity_covered_by_sigma_pieces` と `sigmaLength_one_frobenius_type` は statement が BG/Coq
  原文を表さないため、**FROZEN MIS-ENCODING — DO NOT PROVE OR REPAIR IN PLACE** と明記。term-level
  consumer は 0 (source occurrence は各 declaration と、後者を説明する S16 docstring 1 件のみ)。
  新 consumer は proved faithful APIs (`Mtilde`/`zTilde` cover と
  `S16.non_disjoint_signalizer_frobenius`) を使う。
- `sigmaLength_le_two_of_mem_zTilde_of_isTypeP` と
  `exists_sigmaDecomposition_length_le_two` の旧「残 gap / gated」説明を、既に完成している
  `mem_sup_of_normal_left` split と per-piece bound plumbing に合わせて更新。関連 S14/S16 notes も
  historical status を反映した。

**検証**: main 再同期後 `lake build OddOrder` green (4225 jobs)、S14 + S16 +
`OddOrder.AxiomsCheck` target build green (4210 jobs)、旧 Theorem A exact name 0、frozen 2 宣言の
term-level caller 0、`git diff --check` clean。新 axiom・signature 変更なし。

**self-flag**: c-2 は vestigial cleanup の単独 commit。issue 0118 の次 frontier c-3
(`V_inf_centralizer_Q_eq_bot` の下流 discharge leaf + S16 rewire) は lane a の 0116 full flip
landing 後に hub が本 issue へ出す「c 再 engage (V_inf)」flag を trigger とする。
