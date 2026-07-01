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

## 1. 4 クラスタ × 4 レーン (🔒 ownership)

| lane | worktree | クラスタ | 主所有ファイル | ODD_ISSUE_BASE |
|---|---|---|---|---|
| **a** | `odd-order-a` | **α** Pf §10–11–13 中央指標核 | `Peterfalvi/{S10_MinimalSimpleStructure, S11_MaximalII_III_IV, S12_MaximalIII_IV_V, S13_MaximalIII_IV}.lean` + `FeitThompson.lean:426` (`card_kappaHall_lt_of_isTypeIIIorIV`) | 1000 |
| **b** | `odd-order-b` | **β** Pf §12 all-Type-I Dade tower | `Peterfalvi/S14_MaximalI.lean` | 2000 |
| **c** | `odd-order-c` | **γ** POLE-2 §14–16 下流 (Arm B) | `Peterfalvi/{S15_SAndT, S16_NonExistenceG}.lean` | 3000 |
| **d** | `odd-order-d` | **σ-theory (typeP_Galois 土台) 新 shared-infra leaf** (2026-07-01 再々配分, issue 4014 hub 裁定) + γ §15 S&T setup / δ BG §14–16 (dormant) | `OddOrder/GroupTheory/**` σ-theory leaf (主, claim-first) + `Peterfalvi/S15_SAndT_Setup.lean` + `BG/**` + `FeitThompson.lean` carrier (dormant) | 4000/9000 |

> **⚠ 2026-07-01 再々配分 (ユーザー裁定, issue 4014 hub 裁定)**: lane d は §15 S&T setup / δ BG §14–16 の
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

- **issue 0086**: `Peterfalvi/S10_MinimalSimpleStructure.lean` の `BGTheoremECoverData` 構造 +
  `BGTheoremETypeICovering`/`BGTheoremENonTypeICovering` + `bgTheoremE_cover_data` 定理 (BG Thm E carrier,
  Pf 8.17) は原則 lane a の S10 内だが **lane d 所有** (b/c/d 共有 consumer)。
- **issue 0087 → ❌ 撤回 (issue 0089, 2026-06-30)**: `Peterfalvi/S07_RhoProjection.lean` は lane b 所有として
  導入されたが、S09 `chiRho` 機構 (=教科書 §7、S番号=§+2) の完全重複と判明し**削除済** (ユーザー裁定 D)。
  (12.16) path は S09 `chiRho`/`Hypothesis78`/`NormEstimates` を cite。memory `s09-is-section7-chirho-complete`。
- **issue 0088**: `Peterfalvi/S14_MaximalI.lean` の `exists_typeICovering` 定理 (8.17.a type-I covering) は原則
  lane b だが、上記 0086 の S10 carrier API を直接 consume するため、**carrier-consumer 部分は lane d 所有**
  (role split: b = covering math 8.13.c1/8.8.a の本体、d = carrier API 追従)。恒久解 = carrier-consumer を
  d 所有 helper に抽出し `exists_typeICovering` から cite (issue 0088 で追跡)。

### 各クラスタの最深 body (2026-06-28 監査の file:line、随時更新)

- **α (lane-a)**: `exists_zeta_residual_not_orthogonal` (Pf 11.8, `S12_MaximalIII_IV_V.lean:6762`,
  **唯一の bare FT spine sorry**)・`typeV_forces_coherence` (10.10)・`typeII_coherence_contradiction_estimate`
  (10.8)・`typeII_derived_frobenius` (10.7)・§13 coherence reduction 7 本 (`S13_MaximalIII_IV.lean`)・
  9.9.a caseA/caseB counts (`S11:3335/3417`)。
- **β (lane-b)**: `counterexample_contradiction` (12.16, `S14_MaximalI.lean:1364`)・12.2–12.6 (`S14:232/258/271/282/306`)・
  12.10–12.15 (`S14:1040/1049/1324/1348/1357`)・`exists_typeICovering` 詳細 (8.13.c1/8.8.a, `S14:1615/1660`)。
  headline `theorem88_caseB_holds` は既に sorry-free (δ の `typeP_duality` を cite)。
- **γ (lane-c)** 【binding constraint = 最長 pole】: `orthogonality_switch` (14.14, `S16_NonExistenceG.lean:3633`)・
  `exists_MHypothesis` (14.10, `S16:3709`)・`betaM_expansion` (14.11.2, `S16:1954`)・`T_typeII` (14.9, `S16:1564`)・
  §15 `basic_structure_gated` (13.1.d/e, `S15_SAndT_Setup.lean:283`)・`character_degree_analysis` (`:386`)・
  `lambda_forces_T_caseB` (`:394`)・`normalizer_W1` (13.16, `S15_SAndT.lean:140`) + 13.17 構造。
- **δ (lane-d)**: BG Thm D(3)/(4) **signalizer functor** R(x) (issue 8019/8020, `S16_MainResults.lean:1075`)・
  Thm A/B/E 残 conjunct (`166/276/1223`)・`aSets_support_slice` (`1236`)・reverse bridges (issue 8015)。
  headline `proposition_type_classification` は既に sorry-free。

---

## 2. signature contracts (cite するだけ・待たない)

すべて signature が既存 or consumer が先に pin 可能。**真のゲートはゼロ。**

| 消費側 | 生産側 (cite 先) | contract (pin 済み statement) |
|---|---|---|
| β (§12) | δ | `typeP_duality` (BG §16, 既存) |
| β (§12) | α | §10–11 char 結果 (type 判定) |
| γ (POLE-2) | α | §11 Dade-norm engine |
| γ (POLE-2) | δ | §16 構造 (maximal pair / type-P) |
| FT spine (`FeitThompson.lean`) | a/b/c/d 全 headline | `Section16Inputs` 3-producer assembly (配線済) + `card_kappaHall_lt_of_isTypeIIIorIV` (:426) + `theorem88_caseB_holds` |

**共有ファイル `FeitThompson.lean`**: α が `:426` (`card_kappaHall_lt_of_isTypeIIIorIV`)、δ が carrier 宣言群を
所有。宣言境界での prefix-split 規律で衝突回避、互いの宣言は触らない。

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

## 5. 進捗参照 (2026-06-28 評価)

- **定理到達度 ≈ 70%** (幅 65–75%)。形式化済み数学の「量」(breadth) ≈ 88%、endgame (指標終盤) の消化 ≈ 55–60%。
- 群論 spine (Isaacs 全 7 章 + BG §1–13 + Pf §1–9) は実質完成 (sorry-free)。残るは**指標論の終盤** (Pf §10–16 + BG §14–16) = 最難・最高コスト/行。
- import closure = 285 module、on-path sorry = 92/115 (off-path appendix 23 は凍結)、honest 経路 = ~27 宣言。
- **binding constraint = γ (POLE-2 §14–16 char cascade)**。次点 = α の bare spine sorry (11.8/11.9.b)。両者は §11 Dade-norm 依存を共有。
- 詳細は評価 workflow 結果 (run `wf_388a95a3-568`) と `ft_frontier_remap_2026_06_25.md`。
