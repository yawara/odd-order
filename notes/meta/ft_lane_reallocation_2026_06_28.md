# FT レーン再配分 (2026-06-28, canonical) — ゲートなし・signature contract 方式

> **このファイルが「レーン配分 + 運用原則」の正本** (2026-06-28〜)。
> 旧 `ft_frontier_remap_2026_06_25.md` の **honest FT 経路の構造** (Arm A / Arm B、on-path ~27 宣言) は
> 引き続き有効。本ファイルが上書きするのは **lane↔front の対応づけと運用原則**のみ。
> `ft_path_policy.md` §5 の lane 割当表 / `merge_monitor.md` の 🔒 所有マップは本ファイルへ従属。
>
> **レーン改名 (2026-06-28)**: `lane-{b,c,f,h}` → **`a,b,c,d`** (worktree も `odd-order-{a,b,c,d}` に rename、
> `.lake/build` cache 流用)。

---

## 0. 原則 — なぜ再配分したか (ユーザー方針 2026-06-28, 強い苛立ち「毎回思う」)

**症状**: relane が #1〜#12 まで繰り返され、レーンが「char-gated だ / 上流 producer 待ちだ / starve した」と
称して停止・relane を要求し続けた。`notes/`・memory にも「gated」「starved」「閉じても sorry 減らない」
という誤った語彙が蓄積した。

**根本原因**: レーン配分を**依存ゲートのチェーン**で組んでいたこと。これが「待ち文化」を生んだ。

**正しいモデル (肝に銘じる)**:

1. **レーン間ゲートは原理的に存在しない。** signature (statement) が正しければ、下流は `sorry` を含む
   上流補題でも **cite するだけ**。上流が sorried であることは下流を証明しない理由に**ならない**
   (`feedback-cite-sorried-lemmas-if-signature-correct`)。
2. **配分は依存ゲートで組まない。** 数学的に**独立な hard-core クラスタ**ごとに割り、cross-cluster
   参照はすべて **signature contract (pin した statement を cite)** で媒介する。各クラスタは数十本の
   genuine な hard body を抱え、**枯渇しない深さ**で切ってある (= 二度と starve しない)。
3. **各レーンは自クラスタの最深 body を正面から埋め続ける。** `/loop` でも難所を回避しない
   (`feedback-no-avoiding-hard-parts`)。目標は FT への前進であり、難所を先送りしても意味がない
   (残っているのは最難の endgame そのもの)。
4. **axiom について (ユーザー確認 2026-06-28)**: 各レーンがやるのは **sorry の body を honest な証明で
   埋めるだけ**。新しい `axiom` を勝手に足さない。`sorry` は `sorryAx` 公理に展開され、`#print axioms` が
   それを出すかは「推移的依存に sorry が残っているか」だけで決まる。body を埋めれば `sorryAx` は
   **単調に減る**だけ (掃除プロセスなど無い)。下流は何もせず再チェックで自動的に allowlist 3 公理
   (`propext`/`Classical.choice`/`Quot.sound`) のみになる。新公理導入 (forward axiom 等) は **abort + 承認**
   の別管理。

**doneness は sorry 数でなく carrier/仮説の構成可能性で判定** (`scaffold-sorry-free-not-done`)。
0-consumer は off-path の根拠にしない。

---

## 1. レーン所有マップ (🔒 ownership; 2026-07-07 ⚰ lane d 退役 → a/b/c 3 レーン)

| lane | worktree | クラスタ | 主所有ファイル | ODD_ISSUE_BASE |
|---|---|---|---|---|
| **a** | `odd-order-a` | **α** Pf §10–13 中央指標核 **+ σ-theory tail/dedup** | `Peterfalvi/S(0[3-9]|1[0-3])*` 全体 (= S03–S13; 例外 = b carve-out 0090 `S09_CertificateDischarge` / 0096 S10 §8 Dade-support 宣言群 / coherence infra `S07_Coherence*`+`S08_PGroupReduction` = b) + `FeitThompson.lean` **全体** (d 退役で fold) + σ-theory tail (S11 dup 3定理 retire→generic leaf cite + assembly, issue 9000 承継)。prefix-split の `*_Core` leaf は親の owner に従う (例 S12_MaximalIII_IV_V_Core = a) | 1000 |
| **b** | `odd-order-b` | **β** §16 endgame char cascade = S15 (13.9)-(13.19) **+ S14/coherence cite-only** | `Peterfalvi/{S15_SAndT_Setup, S15_SAndT}.lean` (c→b, 2026-07-04) + `Peterfalvi/S14_MaximalI.lean` + coherence infra (`S07_Coherence*` / `S08_PGroupReduction`) + carve-out 0090/0096 | 2000 |
| **c** | `odd-order-c` | **γ** S16 非存在 = W-side (14.x) norm cascade + parity contradiction **+ Clifford** | `Peterfalvi/S16_NonExistenceG.lean` (S15 は b へ移管、c は import cite) + 構成的 Clifford (issue 9002) + `S15_SAndT_Setup.lean` の T-side `reconciled_typePData_T` carve-out (issue 9013) | 3000 |
| ~~**d**~~ | — | ⚰ **退役 (2026-07-07, ユーザー裁定)** | worktree/branch 削除済。FT frontier (Pf 72 + BG 15 実 sorry) に codex 単独 closeable な genuine・on-path・非衝突・非gated sorry 不在と確定 (詳細 = merge_monitor ⚰ 節)。再活性化トリガー: T-side dual の gate 開通 or a/b/c の helper pull-request。 | (4000) |

> **⚠⚠ 2026-07-02 3 レーン再編 (ユーザー裁定) — lane d 退役**: char endgame が「4 独立クラスタ」でなく密結合
> パイプライン (coherence→σ-theory→§10-13→§13-16→S16) と判明。ungated frontier は上流集中で下流 (c/d) が
> 反復 stall → 3 レーンに縮約。**lane d 退役**: σ-theory dichotomy は sorry-free 完成、残 tail = S11 consumer
> (lane a) に fold、δ BG/** は完了済 (共有・凍結)、carrier 群も done。**S15_SAndT_Setup は lane c へ** (§15→16
> chain を一本化、issue 0092 の decouple は 3 レーンでは不要)。carve-out 0086/0088 は file owner (a/b) に解消。
> σ-theory generic leaf は `OddOrder/GroupTheory/**` 共有ゾーンに残置、lane a が tail を完成 + S11 dedup を実施。
> **ISSUE_BASE 4000 は退役** (9000 shared-infra レンジは全レーン継続)。詳細 = 本節 + merge_monitor 現状メモ。

> **♻ 2026-07-06 lane d 復活 (4 レーン体制、ユーザー承認 + hub 6-agent 調査)**: lane d を**最軽量・codex 運用**
> で復活。クラスタ δ = **issue 9006 Hall-lemma relocation**（FeitThompson.lean の誤配置 proven 群論補題 3 本を
> shared leaf へ relocate + S11 `_hall` migrate、全 body proven・on-path・純群論で char 無）。**ISSUE_BASE 4000
> 復活**。所有 = shared `OddOrder/Mathlib/Subgroup.lean` + `OddOrder/GroupTheory/MaximalSubgroupType.lean`
> （自由追加）+ FeitThompson/S10_BGInterface/S11 は 9006 列挙の relocate のみ（9006 hub 裁定の例外）。d は
> Claude でなく codex が動かすため最軽量・checklist 完備のタスクを選定（他 light 候補 9011/9012/9015/9005 は
> 納品済 stale、9007 高衝突、9014 deep）。正本 checklist = `issues/9006-*.md`。worktree = `/home/ywr/odd-order-d`。
> **2026-07-06 lane-d audit update**: 9006 と 9007 は完了・closed。9011/9012/9015 は納品済 stale として
> closed。**⚠ 9014 は codex が誤って closed へ移したが hub が reopen (2026-07-06)** — 9014 は hub RULING で
> **KEEP+OPEN** と裁定済 (prime-TI constructor は `ofS06Hypothesis` landed も downstream = §10 coherence upgrade
> `uniform_prTIred_coherent` 等が継続、b/a の active shared 基盤)。**codex は他レーンの issue を close/編集しない**
> (issue hygiene は自クラスタ範囲に限定; 越権是正)。shared foundation 側に bare `sorry` は残っていないため、
> d は新 shared claim が立つまで待機だが、**issue/notes hygiene で busywork を作らない** (アイドルなら停止+報告)。

> **⚠ 2026-07-01 再々配分 (issue 4014 hub 裁定, 履歴) → 2026-07-02 に上記 3 レーン再編で superseded**: lane d は §15 S&T setup / δ BG §14–16 の
> **on-feitThompson-spine な ungated genuine work が枯渇** (code-level 確証)。残 on-spine 前進は全て他レーン
> 上流に gated (typeP_Galois 未実装 / lane a §11 H_elementaryAbelian sorried / §9 Singer / lane b (6.8)
> Sibley coherence)。⟹ **lane d の主焦点を generic σ-theory (semilinear/near-field) = `typeP_Galois` の土台
> 新 shared-infra leaf `OddOrder/GroupTheory/**` へ移す** (policy 5(A)/(B) = 未所有 upstream leaf は consumer が
> 他レーンでも in-scope)。**claim-first 必須** (9000 番台 issue、既存 `SingerField`/`GaloisCharacter`/
> `ExtraspecialSinger`/`SkolemNoether` を scan して dup 回避)。**lane a §11 は typeP_Galois を再実装せず cite**。
> typeP_Galois は S16 が heavy に cite する `basic_structure` (P_elementaryAbelian/u_bound) + `c_eq_one`
> (Galois 分岐, 20× cite) の structural 結論を unblock する。lane d は S15_SAndT_Setup + BG/** を dormant 保持。
> 詳細 = issue 4014「HUB 裁定」節。

> **⚠ 2026-07-01 再配分 (ユーザー裁定, issue 0092)**: lane d の旧クラスタ δ (BG §14–16 → Peterfalvi
> interface) の FT deliverable は**実質完成** (kappa/IsTypeP/M_F/Prop 16.1/typeP_duality/type-P carrier/
> bgTheoremE_cover_data/theoremD_*/theoremE_*/FT_signalizer は全 sorry-free で spine 消費済)。残 §14–16
> owned sorry (Thm A/B monolith=faithful variant で迂回済 / tau2_transfer_constraint 15.8 / unconsumed
> endpoint 3) は marginal FT value 低。⟹ **lane d の主焦点を binding pole γ の import-上流最上流
> `S15_SAndT_Setup.lean` (16 sorry) へ移す**。lane c は下流 `S15_SAndT` + `S16_NonExistenceG` (21 sorry) を
> 保持。import chain = `S15_SAndT_Setup → S15_SAndT → S16_NonExistenceG` ゆえ upstream-first + signature
> contract で clean decouple。lane d は BG/** 所有を保持 (dormant、必要時のみ)。lane c は以後
> **S15_SAndT_Setup を編集しない** (逸脱扱い)。

### carve-out (sub-file 所有例外、ユーザー裁可)

carrier 宣言とその consumer が複数レーンの所有ファイルに跨るため、以下の sub-file 例外を設ける
(step 1.5 範囲逸脱チェックの除外規則。詳細手順は [`merge_monitor.md`](merge_monitor.md) の 🔒 マップ直下):

- **issue 0086 — ❌ 解消 (2026-07-02 lane d 退役)**: `Peterfalvi/S10_MinimalSimpleStructure.lean` の
  `BGTheoremECoverData` 構造 + `BGTheoremETypeICovering`/`BGTheoremENonTypeICovering` +
  `bgTheoremE_cover_data` 定理 (BG Thm E carrier, Pf 8.17) は旧 lane d 所有だったが、
  **file owner = lane a に fold** (issues/closed/0086)。
- **issue 0087 → ❌ 撤回 (issue 0089, 2026-06-30)**: `Peterfalvi/S07_RhoProjection.lean` は lane b 所有として
  導入されたが、S09 `chiRho` 機構 (=教科書 §7、S番号=§+2) の完全重複と判明し**削除済** (ユーザー裁定 D)。
  (12.16) path は S09 `chiRho`/`Hypothesis78`/`NormEstimates` を cite。memory `s09-is-section7-chirho-complete`。
- **issue 0088 — ❌ 解消 (2026-07-02 lane d 退役)**: `Peterfalvi/S14_MaximalI.lean` の
  `exists_typeICovering` carrier-consumer 部分は旧 lane d 所有だったが、**S14_MaximalI 全体が lane b**
  に一本化 (issues/closed/0088)。今後の carrier API 変更 (S10 = lane a) は a→b の通常 cross-lane
  通知 (notes/issue) で扱う。
- **issue 0096 (hub 裁定 2026-07-02, ユーザー委任レビュー)**: `Peterfalvi/S10_MinimalSimpleStructure.lean`
  の **§8 Dade-support 宣言群** (`typeII_A_sets_TI` / `typeII_A_sets_normalizer` /
  `dadeSupportHypotheses_typeI` / `dadeSupportHypotheses_typeP` / `support_mutual_exclusion` +
  直接 helper 新設) は **lane b 所有** ((8.18.c)→(12.3)→(12.14–16) chain + issue 8022 route B の前提)。
  `S10_BGInterface.lean` への A₁/σ♯/M̃ bridge 補題追加も b 許容。詳細 = issues/0096 +
  merge_monitor 🔒 マップ直下の carve-out 節。

### 各クラスタの最深 body (2026-07-02 全面刷新 — decl 名のみ、line anchor は rot するため廃止)

- **α (lane-a)** — 実 sorry 27 (S09 1 / S10 8−0096 分 / S11 4 / S12 4 / S13 10):
  **spine**: `exists_zeta_residual_not_orthogonal` (Pf 11.8, S12, **唯一の bare FT spine sorry**、
  live plan = `s13_11_8_orthogonality.md`)・`card_G0_lower_bound` (Pf 7.10, S09 — **0044 裁定 2026-07-02:
  11.8 チェーン一段落後、σ-tail より先に queue**)。
  **§10–13 body**: `typeV_forces_coherence` (10.10)・`typeII_coherence_contradiction_estimate` (10.8)・
  `typeII_derived_frobenius` (10.7)・S13 10 本 (`core_structure`×3・`H_elementaryAbelian` (11.7、γ が
  cite 待ち)・`coherent_S_of_coherent_SH0C`・`coherent_quotient_bound`・`HC_le_secondDerived`・
  `orthogonality_setup`・`not_orthogonal_mu0_sub_zeta`・`final_typeIII_conclusions`)・S11 4 本
  (`caseA/caseB_character_counts`・`exceptional_case_frobenius_realization`・**`sibleyTarget_H0C`
  (9.11 — 7001 裁定 2026-07-02: a 所有、着工前 soundness 監査必須)**)・S10 structural
  (`hall_maxNilpotentNormalHall_and_mainSubgroup`・`typeI_or_typeII_centralizer_unique`・
  `escapingCentralizers_control`・`bgTheoremE_cover_data`)。σ-tail = issue 9000 承継分。
- **β (lane-b)** — 実 sorry 13 decls (S14) + carve-out 0096 の S10 4 宣言:
  **最深**: `nonconjugate_diffImage_inner_zero` (8.18.c、mixed Ã₁∩Ã — **0096 の §8 support theory を
  S10 側で正面 build**)・`exists_typeICovering` ×2 (8.13.c1/8.8.a、route B = 8022)・(12.10) pins
  `witness_L_isTypeI`/`witness_L_complement_isZGroup`・`intersection_complement_structure` (12.11)・
  `complement_cyclic_order_dvd` (12.12)・`exists_counterexample_dade_data` (12.16 chain)・
  `constituent_diff_support_subset_nonescaping`・`rho_constant_on_H_minus_Hprime`・`psi_constant_on_xK`・
  `rhoM_integer_values`・`sibleyTarget_frobI` (**TI-case 限定**、2032)・`typeI_induced_char_constituents`
  (9002 = c の Clifford を cite)。+ **(6.5.c) coherence producer DONE**
  (`S08.nonempty_coherent_SOf_bot_of_index_dvd` + `S14.frobenius_typeI_coherent_of_cyclicQuotient`)。
  headline `theorem88_caseB_holds`/`counterexample_contradiction` (12.16)/(12.6) tower は sorry-free。
- **γ (lane-c)** 【binding = 最長 pole】 — 実 sorry 32 (Setup 15 / S15 8 / S16 9):
  **最深**: `orthogonality_switch` (14.14)・`exists_MHypothesis` (14.10)・`eta_generic_data`・
  `T_typeII_structural_inputs` (旧 `T_typeII`/`betaM_expansion`/`normalizer_W1` は **proven**、残余は
  これら inputs 系へ移動)・S15 8 本 (`Q_elementaryAbelian_T`・`V_inf_centralizer_Q_eq_bot`・
  `reconciled_typePData_T` 等)・Setup の `c_eq_one` (**W-side/structural route 制約** = s16_w4 hub 節)・
  `character_degree_analysis` (13.3)/`lambda_forces_T_caseB` (13.4) (T_side route で on-path)・
  `basic_structure_gated` (P_elementaryAbelian は a の `H_elementaryAbelian` cite / u_bound は σ-leaf +
  a assembly)。+ **η-grid honest 化 + M 向け h78/Dade instantiation (9001 追加裁定 2026-07-02 = c 所有)**
  + Clifford (G1) extension core (9002)。⚠ `sibleyTarget_S`/`S_coherent`/13.5–13.9 S-side 形 =
  vestigial 処分 (完成させず W-side restate or retire、s16_w4 hub 節)。
- ~~**δ (lane-d)**~~ **退役 (2026-07-02)**: BG §14–16 の spine 消費 endpoint は全 sorry-free で完了・
  共有凍結。残 owned sorry (signalizer Thm D/E・Thm A/B monolith・`aSets_support_slice` 等 15 個) は
  全て off-feitThompson-path と検証済 ([[ft-settled-findings]] / issues/closed/4014)。headline
  `proposition_type_classification` は sorry-free。σ-theory generic leaf 群は共有ゾーンに sorry-free
  凍結、tail は lane a に承継 (issue 9000)。

---

## 2. signature contracts (cite するだけ・待たない)

すべて signature が既存 or consumer が先に pin 可能。**真のゲートはゼロ。**

| 消費側 | 生産側 (cite 先) | contract (pin 済み statement) |
|---|---|---|
| β (§12) | BG 共有凍結 (旧 δ、sorry-free 済) | `typeP_duality` (BG §16, 既存) |
| β (§12) | α | §10–11 char 結果 (type 判定) |
| γ (POLE-2) | α | §11 Dade-norm engine |
| γ (POLE-2) | BG 共有凍結 (旧 δ、sorry-free 済) | §16 構造 (maximal pair / type-P) |
| FT spine (`FeitThompson.lean`) | a/b/c 全 headline (旧 δ headline `proposition_type_classification` は sorry-free 済) | `Section16Inputs` 3-producer assembly (配線済) + `card_kappaHall_lt_of_isTypeIIIorIV` (proven; 残余 = 11.8 cite) + `theorem88_caseB_holds` |

**`FeitThompson.lean` (2026-07-02 更新)**: **lane a が全体所有** (
`card_kappaHall_lt_of_isTypeIIIorIV` + 旧 δ carrier 宣言群、d 退役で fold)。他レーンが carrier 宣言
(`Section16Inputs` 等) に field を追加する必要があるときは hub/issue 経由で承認合流
(先例: lane c の `S_U_commutative`/`Sdata_W2_eq` 追加 = 構成子供給付き、hub 承認)。

**未存在の cross-ref が要るとき**: consuming 側が statement を**先に書いて (sorried theorem として) pin** し、
`notes/`・issue で hub に告知。両レーンが contract に対して並行作業。**body 完成を待たない。**

---

## 3. 🛑 STOP 条件 (ユーザー 2026-06-28「想定に反する挙動を観測したらその時点で止める」)

以下を観測したら**即停止・報告** (誤った待ち文化への逆戻り):

- **(a)** レーンが「gated / 上流待ち / starve」を理由に**自クラスタの hard body を放置**、または relane を要求。
- **(b)** `/loop` が難所 core を回避して wiring/簡単ピースに流れる。
- **(c)** sorry body 充足のはずが **allowlist 外の新 axiom を導入**、または hard content を **vacuous な仮説に
  hoist** (scaffold で sorry を消すだけ)。
- **(d)** signature contract を**勝手に変更** (consumer 側で cite 先の statement を書き換える等)。

正常時の唯一の例外は forward axiom (= 承認制、"勝手に" にはなり得ない)。

---

## 4. 運用ルール (既存 worktree policy 踏襲)

- **起動時 + 定期に `git merge main`** (3-way、`--ff-only` 不可)。次の leaf 着手前・commit 前にも再同期。
  取り込み後 `git rev-list --count HEAD..main` = 0 を確認。
- 自クラスタ主所有のみ編集、他は cite。
- 各レーンは自 worktree の `.lake/build` で leaf build を回し、full build は commit 直前のみ。
- 採番衝突回避に `export ODD_ISSUE_BASE=<上表>`。
- merge 順・🔒 詳細手順は `merge_monitor.md` (本ファイルの ownership に従属)。

---

## 5. 進捗参照 (2026-06-28 評価 — ⚠ 数値は当時 snapshot。2026-07-02 現在: comment-strip 実 sorry 103
(lane 所有 74 = a 27/b 14 tokens/c 32 + BG 凍結 15 + Pf Appendices 凍結 15)、count-sorry 115。
FeitThompson.lean 実 sorry 0、唯一の bare spine sorry = Pf 11.8)

- **定理到達度 ≈ 70%** (幅 65–75%)。形式化済み数学の「量」(breadth) ≈ 88%、endgame (指標終盤) の消化 ≈ 55–60%。
- 群論 spine (Isaacs 全 7 章 + BG §1–13 + Pf §1–9) は実質完成 (sorry-free)。残るは**指標論の終盤** (Pf §10–16 + BG §14–16) = 最難・最高コスト/行。
- import closure = 285 module、on-path sorry = 92/115 (off-path appendix 23 は凍結)、honest 経路 = ~27 宣言。
- **binding constraint = γ (POLE-2 §14–16 char cascade)**。次点 = α の bare spine sorry (11.8/11.9.b)。両者は §11 Dade-norm 依存を共有。
- 詳細は評価 workflow 結果 (run `wf_388a95a3-568`) と `ft_frontier_remap_2026_06_25.md`。

---

## 3 レーン再々編 (2026-07-04, ユーザー委任「ちゃんと考えて決めて」) — on-path 集中 + off-path 退役

**契機**: 9008 で type-P2 gate が phantom (mmd OCR) と判明し lane-b frontier が枯渇。ユーザーが 3 レーン
役割のゼロベース再考を委任。2 並列 Explore 監査 + spine 検証で FT の真の構造が判明:

**判明した FT 構造** (根拠 = FeitThompson.lean:3611 / AxiomsCheck.lean:6672 / 2 Explore 報告):
1. **`feitThompson` の unique bare sorry = `S12.exists_zeta_residual_not_orthogonal` (Pf 11.8.1–11.8.6)**。
   全 prereq (coherence (5.6)/(5.7)/(6.8), Wielandt (9.1)/(9.6), 構造 (11.6)/(11.7)) proven。lane-a 所有。
   ただし section16 char grid は現状 scaffold (vestigial ∅ S/T-side) — 真の §16 非存在は下記 W-side cascade。
2. **§15-16 の 31 sorry 中 ~19 が OFF-PATH vestigial**: S-side cascade (13.5–13.10, 9 本, 2026-07-02 hub
   ruling で W-side `eta=τ₃∘ω` に routing) + T-side carrier `reconciled_typePData_T` (8 field, off-spine)。
   **c はこの off-path T-side carrier を building していた (12/20→13/20) = 要修正**。
3. **on-path endgame = §16 W-side cascade ~12-14 本**: (13.9)-(13.19) parity/構造 + (14.x) norm cascade。
   最深 terminal = `eta_generic_data`(§3/§4 Dade)・`betaGrid`(13.1.d)・`h78_zetaNuRho`(7.8.b = a の §7 norm)。
4. **a の 16 その他 sorry は off-path** (card_G0 (7.10) / §8 local / §13 downstream typeIII)。

**再配分 (file 所有 + focus)**:

| lane | focus (最高優先) | 所有 file 変更 | 退役 (触らない off-path) |
|---|---|---|---|
| **a** | **S12 `exists_zeta_residual_not_orthogonal` (11.8) = unique bare feitThompson sorry** + on-path §7 norm (7.8.b `h78_zetaNuRho` が §16 terminal に feed) | S03-S13 所有維持 (focus は S12 11.8) | card_G0 (7.10) / §8 local (S10) / §13 downstream typeIII / §12 type-specific |
| **b** | **§16 endgame char cascade を担当: `S15_SAndT_Setup` + `S15_SAndT` の ON-PATH (13.9)-(13.19)** (parity/構造/norm、b の §12 Dade+char 強みが直結) | **S15_SAndT_Setup + S15_SAndT を c→b** (S14 は finished、cite-only 保持) | S-side cascade (13.5-13.10) / T-side carrier `reconciled_typePData_T` |
| **c** | **`S16_NonExistenceG` の非存在: W-side (14.x) norm cascade + parity contradiction** (最終矛盾)、b の S15 + a の (11.8)/§7 を signature-contract で cite | S16_NonExistenceG に集約 (S15 は b へ移管、c は import cite) | T-side carrier building 停止 (off-path 確定) |

**signature-contract pipeline** (依存方向確認済: S16 imports S15 imports S15_Setup):
`a: S12 (11.8) + §7 norm` → `b: S15 char cascade (13.9-13.19)` → `c: S16 非存在 (14.x)`。各下流は上流 sorried
signature を cite (待たない)。

**原則 (不変)**: off-path/vestigial は**証明しない** (S-side cascade・T-side carrier・a の §10-13 local)。
各レーンは on-path の最深 body を正面から (feedback-no-avoiding-hard-parts)。doneness は carrier 構成可能性で判定。

## 3 レーン役割更新 (2026-07-05, ユーザー委任「役割レビュー + FT 完成までの計画」— hub 裁定)

**契機**: b が 2026-07-05 handoff で「closed-sorry solo work 枯渇」を flag (§15 cascade は engine 完備
sorry-free だが、grid 仮説の供給 = issue 3002 threading が a 側未実施のため terminal 1298 を閉じられない)。
同時に a は (11.8) を capstone assembly まで landing (bare sorry → 3 named gates に分解、大きな前進) し、
S12 深部 + §9 + threading + 9000 assembly が a に集中 = **a 過負荷 / b 飢餓の非対称**が発生。

**統合時の検証 (hub, 2026-07-05)**: a/b/c 全 merge 後 full build green (3917 jobs, 128s)。実 sorry census
(comment-strip):
- **F1 (S12 = 11.8 残 gate)**: `charParam_d_modEq_one` (d=u bridge、Coq route 特定済) /
  `card_SHCSet_filter_eq_charParam_n` (§9 count) / `coherent_Sset_of_column_identities`
  (**(11.8.6) τ₂ = S₂ coherence、最深**)。
- **F2 (供給 front)**: 3002 grid property threading (S15.Hypothesis fields + FeitThompson
  `Section16Inputs`/constructor 供給、omegaS/S05:733/740/S07 から機械的) + 9000 u-bound 残 assembly。
  これが S15 terminal `analyticInequalityEstimates:1298`・`c_eq_one` (13.12, S16 16× cite)・
  numeric q=3 を一括 unblock する。
- **F3 (S16 W-side)**: 7 sorries (`exists_MHypothesis`×2 / `T_typeII_structural_inputs` /
  `T_side_caseB_facts` / `eta_grid_facts_on_G0` / `caseB_contradiction_data` /
  `orthogonality_switch_pairing_bounds`)。c は U/V cyclic 実証明化 (Zsygmondy route) で健全に前進中。

**裁定: レーン数は 3 を維持** (独立 front が現に 3 本ある; 07-02 教訓「lane 数 = ungated frontier 供給」)。
役割の変更は **b のみ**:

| lane | focus (2026-07-05〜) | 変更点 |
|---|---|---|
| **a** | **F1 専念**: S12 (11.8) の 3 named gates — τ₂/S₂ coherence capstone (9.11/11.7 gate は S11 で自所有) + §9 count + d=u bridge | threading (9009) を **b へ移管** (a は S12 から離れない) |
| **b** | **F2 = 供給 front** (再定義): (1) **3002 threading 両半分** — S15.Hypothesis grid fields (自所有) + `FeitThompson.lean` の `Section16Inputs`/constructor block (**一時編集権を hub 承認** = 9009 選択肢 2、先例 `S_U_commutative` 方式; a との conflict は Section16Inputs 追記が additive ゆえ低リスク、merge は hub が調整) → (2) S15 cascade を engine + 供給仮説で閉じる (hu は 9000 producer を sorried-cite 可) + `c_eq_one` assembly → (3) **Wave 2 着手**: S10 §8 facts (carve-out 0096、8.16/8.6.a/8.3/12.8) → S14 witness 3 本 (all-type-I branch) | 「枯渇」の恒久解: threading 完了後も b 所有 territory (S15→S10→S14) に honest 必要 math が連続供給される |
| **c** | **F3 継続**: S16 W-side (14.x) norm cascade + parity 矛盾 (現行どおり) | 変更なし |

**Wave 2 の位置づけ (honest doneness、忘れない)**: `Section16Inputs.theorem88_caseB` (8.8 trichotomy) の
honest producer は **all-type-I case を S14 (12.16) 矛盾で殺す枝**を要する。b audit の「witness route は現
feitThompson path 外」は scaffold 測定であり honest 不要を意味しない (CLAUDE.md「進捗の測り方」)。∴ S14
witness 3 本 + missing §8 facts は **honest FT の必要部品** = b の Wave 2 (S14/S10 とも b 所有で conflict 無し)。
同様に `section16CharacterData` の vestigial grid → honest 化は 3002 threading + b/c の §15-16 完成で吸収される。

**FT 完成までの wave 構造 (hub 管理)**:
- **Wave 1 (now)**: F1 (a) + F2 (b) + F3 (c) — 上記。
- **Wave 2**: theorem88_caseB honest 化 (b: §8 facts → S14 witness)、S13 residual の on-path 分
  ((11.7)/(11.3) は proven 済、typeIII downstream は該当時のみ)、`typeV_forces_coherence` (10.10)。
- **Wave 3 (final assembly)**: scaffold carrier (mp/tp/cd) の free/vestigial field 全数 discharge →
  `sectionSixteenHypothesis_of_isMinimalSimpleOdd` 実構成 → AxiomsCheck で `feitThompson` sorry-free +
  allowlist axioms のみを確認。Pf Appendices (Suzuki 等) の残 sorry は cite された時点で on-path 編入。

旧 9009 裁定 (「a が threading」) は本節で**更新** (a 過負荷の実態に合わせ b へ)。issue 9009/3002 の
fix-owner 注記も同時更新。

## レーン分担監査 + reshape (2026-07-06 夕, ユーザー「この分担で問題ないか」→ hub 7-agent 監査 → ユーザー裁可)

**契機**: ユーザーが現 4 レーン (a/b/c/d) 分担の健全性を hub に検証依頼。hub が 7-agent workflow
(レーン別 branch-tip code 監査 + 依存構造 cross-cut → 統合裁定 → adversarial critic) を実施。

**判明した実態 (branch tip code-verified、監査正本 = 本セッション workflow `wf_7215f527-50c`)**:
- **a**: tip = main の祖先 (0 ahead / 76 behind)、非生産。11.8 は assembled 済 → gate-2 (11.8.6) が真の
  carrier gate に collapse (obligation-1 hY = §14-gated / obligation-2 = repo 不在の非直交 ν-constructor)。
  正面から進む ungated work 無し。
- **b**: 唯一の生産レーン (3 ahead)。だが 3 commit は BG §15.8/15.9 (9017) = 担当 char cascade から drift。
- **c**: 純 downstream sink (0 ahead / 22 behind)。S16 残 sorry は全て b/a の真の gate。直近 commit は docs-only
  「gate pin」(frontier-thin、#print axioms で自 route の循環を自証)。
- **d**: アイドル (0 ahead)。直近 ~5 commit が `chore: refresh checklist` = CLAUDE.md 禁止の busywork。
- **当初仮説 (prime-TI 9014 / §5 coherence 1017 が gate) は STALE**: 両者 code-verified で 0-sorry・build 済
  (PrimeTIResidue.lean `ofS06Hypothesis` constructor / S07_Subcoherent.lean (9.11) squeeze)。1017 が ~23
  iteration 後に収束した先 = **BG §15/§16 (9017)** が真の unowned bottleneck (b の Pf §13 + BG-side S16 を binding)。

**裁定 (2026-07-02 教訓「lane 数 = ungated frontier 供給」の再適用 + CLAUDE.md「genuine 未形式化 prerequisite は
規模問わず正面 build」)**: honest な ungated deep frontier は ~2 本 (BG §15/§16 + b の §13 mixed-family coherence)。
4 レーン過剰供給の是正:

| lane | 2026-07-06 夕〜の役割 | 変更 |
|---|---|---|
| **b** | **BG §15/§16 node (9017) の owner を追認** (drift 保全) + §13 mixed-family coherence G1 + S15 cascade + S14 witness | drift を正式 owner 化。Thm 15.8 signature 訂正 (unsound→Coq準拠, consumer 0) + S16→S15 hoist 承認 (9017 RULING) |
| **a** | **S07 非直交 ν/τ₃ glue-map constructor (gate-2 obligation-2) を temporary S07 carve-out で build** (issue 9016) | a の唯一 ungated head-on target。idle 回避 + b 負荷分散。当初「b へ carve」案を追認帰結で a へ変更 |
| **c** | **thin downstream cite-sink** (成果 in-place 保全)。carrier landing 後に cite-assembly で再起動 | full producing lane から除外 (fault/discard しない)。§9 block-decomposition (9000) redirect は選択肢 |
| **d** | **DORMANT** (停止+報告、busywork 禁止) | BG §15/§16 が b 追認で d の rescue にならず、他 unclaimed leaf も無し → charter どおり停止。worktree 保持 (idle 継続なら retire 検討) |

**doneness マーキング**: issue 9014 (prime-TI foundation) = build 済・frontier gate でない (KEEP+OPEN は §10
coherence upgrade のみ)。issue 1017 §5-arith = 完了・G2→9017 移管・G1=b in-cluster。**「3002 uniform gate」
framing は stale** (grid fields は S15.Hypothesis に threading 済 sorry-free、FeitThompson:2654/2659 供給)。

全て hub-arbitrable な可逆運用 reshape (ユーザー escalation 事項なし)。ユーザーは「b の drift 追認」を裁可、
残りは hub 裁定。正本 = 本節 + issues 9017/9016/9014/1017 の HUB RULING + merge_monitor 🔒 マップ。

## lane c FOLD → DORMANT cite-sink (2026-07-06 夕, ユーザー「c やることなくなった」→ hub 4-agent 調査 wf_00a0db07)

**契機**: ユーザーが c の idle を flag。hub が 4-agent 調査 (c idle 検証 + ungated 行き先スキャン + b 過負荷吸収スキャン
→ ruling) を実施、code-grounded に確定:

- **c は自領域枯渇 (0 ahead)**: S16_NonExistenceG の **10 bare sorry は全て true carrier gate** (carrier/signature
  が repo 不在)、**sorried-cite assemblable はゼロ**。T_isTypeP2 (:1154) は一見 in-file cite だが**真に循環**
  (Lean-rejected)、真の gate は v-value (:1249)。Clifford 9002 は**完了** (`typeI_induced_char_constituents`
  body sorry-free、consumer b が landed)。reconciled_typePData_T は U-side 3 field 済、残 W2_le/centralizer_W1 =
  b の §13/§16 T-side W-factor σ-structure (principled stop)。
- **ungated 行き先も無し**: (1) §9 u-bound/typeP_Galois = a の S11 territory (9000、過去に a-vs-d 衝突前科)。
  (2) gate-2 hY = a file (S12) + b active (S07_Subcoherent)。(3) shared leaf (GroupTheory/RepTheory/Algebra) =
  全 0-sorry frozen、shared-infra slot は d が占有。(4) (6.8.1) char content = a の hcol 駆動 call-site。
  b-overload も移管で re-coupling ゆえ transfer 不可。
- **⟹ ruling = FOLD c を DORMANT cite-sink** (07-02 教訓「char endgame の coupled pipeline では ungated frontier
  にレーン数を合わせる」の再適用)。active 生産レーン = **3** (a §9-13 char core + typeP_Galois 9000 / b §14+coherence+
  BG§15/§16+§13 export / d shared Isaacs Hall API) + **c DORMANT**。

**c reactivation trigger** (いずれか landing で自動再開 → S16 W-side norm cascade + parity 矛盾を assemble):
**a: typeP_Galois (9000, multi-consumer root gate — a の (10.7)/(10.8) + c の (14.9) + S/T frobenius kernel を
一括 unblock)** / **b: §13 v-value lower-bound export (9013) / §15-16 W-factor σ-structure (9017) / S-T partner
parity (3002)**。c の成果 (Clifford 9002 / reconciled U-side / S16 sorried-cite skeleton) は全 **in-place 保全**
(revert しない)。

**残る非対称 (次の判断材料)**: b は依然 **OVERLOADED** (BG §15/§16 + S15 cascade + S14 + coherence)、endgame
frontier は実質 **a の typeP_Galois 9000 + b の BG §15/§16** の 2 workstream に集中。a が 9000 を landing すれば
c/b 下流が一気に unblock されるゆえ、**最高 leverage = a の typeP_Galois 9000**。a landing 後に b→c 再配分
(v-value export 等を c へ) の余地を hub が再検討。hub-arbitrable、ユーザー escalation 事項なし。

## lane d 再活性化 (2026-07-06 夕, DORMANT 判定撤回, hub 裁定)

reshape で d を DORMANT (停止・busywork 禁止) としたが、その後 **4 tick 連続で d は genuine な shared 群論 API を
sorry-free additive に生産** (claim 9018-9031、Isaacs/GroupTheory/Mathlib): normal Hall uniqueness / mulAut
invariance / complementary Hall / subtype transfer / **MinimalInvariantNormal** / minimal invariant p-group・
commutativity・normal witness / π-group disjoint / Hall subgroup action / invariant fixed conjugation 等。

**判定**: 内容は **coprime-action / minimal-invariant subgroup / Hall / π-group = FT local analysis (BG §10-13 +
typeP_Galois 9000 の σ-theory 基盤) が実際に使う foundational 群論**で、chore-churn busywork ではない (claim 手順
遵守・全 sorry-free)。「DORMANT / idle なら停止」の前提 (= d に genuine shared frontier なし) は**経験的に偽**。
⟹ **DORMANT 判定を撤回、d = codex 運用の active shared-infra レーン**に再活性化 (所有 = GroupTheory/Mathlib/
Algebra/Isaacs へ additive shared claim、claim-before-build 継続)。

**⚠ make-work 化の歯止め (CLAUDE.md「0-consumer は off-path 根拠にしない」を尊重しつつ)**: hub は d の新 API が
FT 経路に接続するかを **定期確認** (特に typeP_Galois 9000 / BG local analysis の consumer になるか)。0-consumer
それ自体は停止理由にしないが、FT-relevance 追跡を続け、明らかに spine と無関係な generic API 量産に転じたら
再度 flag。正本 = 本節 + merge_monitor d 行/note。
