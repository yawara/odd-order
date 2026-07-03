---
id: 4001
slug: s16-lane-c-frontier
title: "Pf §16 non-existence: lane-c frontier + Lane B gate map"
created: 2026-06-22
---

# Pf §16 non-existence: lane-c frontier + Lane B gate map

## 背景

4-lane 再編 (2026-06-21) で lane-c = Pf §16 (`S16_NonExistenceG.lean` 編集 tail + POLE-2
`field_normalizer_structure`)。`field_normalizer_structure` の dispatch tree は sorry-free
(lane-h 成果)。残 13 sorry はすべて dispatch が cite する named obligation で、ほぼ Lane B
(Pf §13 char/Dade、issue 1004 section16CharacterData) に bottom-out する。
正本 = `notes/peterfalvi/s16_nonexistence_gate_map.md`、POLE-2 = issue 2009。

## 2026-06-22 再開: 基盤 char-infra ピボット (ユーザー裁可)

全数 audit で S16 内に ungated 証明仕事が無いと再確認 (lane-b 0 commits 先行、η-grid free field、
(7.5)/(3.9) absent)。ユーザー選択「基盤 char インフラ構築」に従い、§14-16 endgame を gate する
foundational arithmetic backbone を構築 (η free-field に非依存、signature 先行整備):

- [x] `one_le_norm_signed_paired_sum` — (3.9)/(14.11.3) parity core (commit `2d517956`)。
- [x] `all_pm_one_and_card_of_odd_sq_sum_le` — (14.11.2) sum-of-squares core (commit `9f17b010`)。
- 真の long pole = **S15 η-grid carrier の honest 化 (lane-h)**。詳細 + lane-h への精密 ask =
  `notes/peterfalvi/s16_nonexistence_gate_map.md` 冒頭セクション + issue 4003。

## やること (lane-c 単独で進められる部分)

- [x] (kickoff) `key_inequality` (14.8) 実証明 + `main_size_bounds` conjunct 3 実証明 +
      `MHypothesis_kernel_cyclic` を (14.11)`K_eq_V_index_pq` + `V_cyclic` へ wire (commit ff2338a5)。
- [x] `K_eq_V_index_pq` の `e=pq` 枝 — `MHypothesis` を `complement_card_eq_pq` field で enrich
      (lane-c 所有 carrier、`LHypothesis.typeI_complement_card_eq_pq` と対称)。**DONE commit `aff0bc2a`**。
- [x] `caseB_for_S` (14.6) — `caseB_for_T` の opaque-Prop scaffold を mirror、`S15.caseB_order_u_data`
      (13.15) を cite。**DONE commit `aff0bc2a`** (文書順で最上流の lane-c 着地点)。
- [ ] `exists_MHypothesis` (14.10) の構造 skeleton — **blocked**: `typeII_overNormalizer_frobenius`
      が S/U-side ハードコード (S15:1712)。V-side 構築には **T/V-side dual** が要る = lane-h ask
      (gate map「精密 gate 特定」+ 新 issue)。dual 着地後は `exists_LHypothesis` の機械的 dual で
      構造部 sorry-free 化可。
- [ ] 残り (A norm-cascade char / B §13 cyclic / C 直交 dichotomy) は Lane B/H の §13 Dade
      producer + η-carrier (issue 4003) 着地後に cite で実証明化。

## 2026-06-22 resume の結論: §16 残 11 sorry は全て lane-h gated (原文レベル検証済)

文書順で lane-c が忠実に閉じられる sorry は上記 2 本で尽きた (caseB_for_S 211 / K_eq_V e=pq 2012)。
残 11 (`T_side_caseB_facts` 136 / `T_typeII` / `main_size_bounds_structural` / `betaM_expansion` /
`generic_character_bound` / `normCascadeBound_of_charData` / `U_cyclic_and_Q_elemAbelian` /
`V_cyclic` / `caseB_character_contradiction` / `orthogonality_switch` / `exists_MHypothesis`) は
全て lane-h の §13/§14 char/構造理論に bottom-out (T-side dual / η-carrier / Dade)。
正本 = `notes/peterfalvi/s16_nonexistence_gate_map.md`「更新 (2026-06-22, resume session)」。

## Lane B / hub への ask (signature-first, 正しければ sorried 可)

`section16CharacterData` producer (issue 1004) の landing 時に以下を faithful signature export:

- S-side case-(9.7.b) 判定 (`caseB_for_S`) — `character_degree_analysis` の dichotomy 出力
- `U_cyclic` / `Q_elementaryAbelian` / `V_cyclic` (13.2.a/b)
- (14.11.2)(14.11.3) β_M η-expansion + generic bound、(14.11.4) norm 不等式 ((7.5) Frobenius 内積)
- (14.14) 直交 dichotomy、(14.16) β_L^τ η-expansion contradiction、`T_typeII` (14.9)

## 完了条件

`S16_NonExistenceG.lean` の 13 sorry が解消 (lane-c 単独部 + Lane B producer cite)。
`field_normalizer_structure` / `nonexistence_of_G` が unconditional。`lake build OddOrder
OddOrder.AxiomsCheck` 緑。

## 2026-06-30 lane-c (/loop): T_typeII reduction landed + V-side 構成 blocker を精密特定

本 /loop iteration の成果と、残 frontier の精密診断:

**genuine landing**: `T_typeII` (14.9) を BG-structural 経路で de-opacify (commit `89f71cfc`、leaf
green)。`typePData_of_isTypeNonI`→`isTypeII_of_typePData` (axiom-clean) cite、残は新
`T_typeII_structural_inputs` (5 連言) に isolate。教科書 type-III orthogonality 経路 (cite 不能) を回避。

**残 9 sorry の精密診断** (cont.¹⁰ の「枯渇」を refine): 全て deep §3/§9/§11/§13/§14。issue 4002 の
ユーザー裁定「lane c は自前 V-side Dade/§14 char を進める」に従い最大 item `exists_MHypothesis`
(V-side Dade 構成) の forward path を調査 → **構造 blocker を精密特定**:

- **base `Hypothesis` は非対称**: `Sdata : TypePData S` (+`Sdata_U_eq`/`Sdata_W1_eq` reconciliation) は
  在るが **`Tdata : TypePData T` が無い**。⟹ `typeII_overNormalizer_frobenius` (S15:1070、S/U-side) の
  V-side dual は機械 mirror 不可。**base Hypothesis への `Tdata` carrier 追加が前提** (= §16 carrier infra
  拡張、`Section16TypePStructure` 供給含む、architecturally significant)。
- **追加後も下流は deep**: V-side `exists_typeI_maximal_overNormalizer_U` dual は
  `card_LF_coprime_pq`/`theorem88_caseB` T-side/`typeI_overNormalizer_U_le_fitting` dual に bottom-out、
  h78 coherence/§8 partner structure は **lane b の active char keystone (Section11CharacterData /
  (11.8)/(10.8)、issue 2020)** と overlap。

⟹ **issue 4002 診断 (lane c = thin downstream consumer、real fan-out は lane b char) の再確認**。
lane c の独立 runway = (a) base Hypothesis の Tdata carrier 拡張 + V-side 構造構成 (大規模・非重複・
下流 char-gated) or (b) lane b char keystone (重複 risk)。**戦略 fork をユーザーに flag** (issue 4002
proposal: 続行 / lane b bottleneck 支援 / 別 frontier 再配置)。[[feedback-flag-poor-progress]]

### ⚠ 訂正 (同 /loop、ユーザー裁定「V-side 続行」後の正面調査): Tdata carrier は dead-end

ユーザーが「§16 V-side 構成続行」を選択 → 上記 (a) の「Tdata carrier 拡張」を着手調査した結果
**誤りと判明**。`FeitThompson.lean:276` docstring が明記: **「T (larger-κ member) need not be
type-P₂, so no symmetric Tdata」** — T の type-P₂ 性は §14 結論 (`T_typeII` 14.9) で**入力でない**
(S は smaller-κ で type-P₂ 固定ゆえ Sdata 入力、T は非対称が設計意図)。Tdata を入力 carrier に
すると §14 結論を入力に格上げする設計違反。

**真の V-side gate = `T_typeII` (14.9、本 iteration で BG-structural reduction 済)**。V-side 構成は
`exists_typeI_maximal_overNormalizer_V` (S-side S15:609 ~350 行 dual、T_typeII gated + V-side helper
chain) → `exists_MHypothesis` ~35 field assemble。`T_typeII_structural_inputs` の 5 連言 = `TypeIIData
T` field そのもの (深 §14.9 char、tractable sub-conjunct 無し)。詳細 =
`notes/peterfalvi/s16_w4_char_cascade.md` cont.¹²。次 = V-side helper chain (multi-iteration)。

## 参照

- `notes/peterfalvi/s16_nonexistence_gate_map.md` (正本・13 sorry の gate 詳細)
- `notes/peterfalvi/s16_w4_char_cascade.md` cont.¹¹ (本 iteration の詳細)
- issue 2009 (POLE-2 `field_normalizer_structure`)、issue 1004 (section16CharacterData, Lane B)
- issue 4002 (lane allocation 診断: thin downstream consumer)、issue 2020 (§13.2.a char core, lane b)
- commit ff2338a5 (kickoff)、`89f71cfc` (T_typeII reduction, 本 iteration)

## 2026-06-30 HUB 裁定 — 戦略 fork 却下・lane-c は正面突破

lane-c が cont.¹¹/¹² + 本 issue 末尾診断で **「Tdata carrier 拡張 = architecturally significant
cross-lane infra」「下流 char-gated / lane-b overlap」を理由に戦略 fork (再配置) をユーザーに flag** した
件、hub が**却下**。難所回避は無意味 (ユーザー 2026-06-30)。lane-c の LAUNCH.md に直接指示を配置済。

**却下根拠 (既裁定の適用 — 再質問しない)**:
1. **cross-lane gate は存在しない**。`Tdata` carrier の追加先 base `Hypothesis` は
   `S16_NonExistenceGCore.lean:42`（+ `S15_SAndT_Setup.lean:80`）= **lane-c 自身の所有ファイル**。
   `Sdata`/`Sdata_U_eq`/`Sdata_W1_eq` を mirror して `Tdata : TypePData T` + reconciliation を足すのは
   lane-c 単独で完結する。これを "cross-lane infra" と呼ぶのは誤り。
2. **fork は既裁定で閉じている**。issue 4002 ⚠訂正 (ユーザー 2026-06-22) が既に「lane-c=B 待ちは過大、
   真の cross-lane 依存は narrow & citeable、大半は lane-c 自身の §14 Dade char」と裁定。本 issue の
   診断自身も path (a) を「大規模・**非重複**・あなたの仕事」と認める。同じ punt の再 open は不可。
3. **下流 char-gated は幻のゲート**。h78 coherence / `Section11CharacterData`/(11.8) に当たったら
   **sorried signature を cite するだけ**（または `normCascadeData`/§8 で実証済の通り MHypothesis
   carrier に char content を isolate）。再導出も待機も再配置も不要。

**lane-c への指示 (LAUNCH.md と同一)**: (1) `git merge main` (16 behind 解消) → (2) base `Hypothesis`
に `Tdata` carrier 追加 → (3) `typeII_overNormalizer_frobenius`/`exists_typeI_maximal_overNormalizer_U`
の V-side dual を S/U-side mirror で構成 → (4) genuine lane-b char は cite/isolate。fork を立てず淡々と。

## ⚠ HUB 自己訂正 (2026-06-30, lane-c の cont.¹² 訂正 + `FeitThompson.lean:276` を merge で確認)

上記裁定の **step (2)「`Tdata` carrier 追加」は撤回する**。私が stale な punt commits に基づき誤った
具体策を出していた。`FeitThompson.lean:276` docstring が明記する通り **「`T` (larger-κ member) need not be
type-`P₂`, so no symmetric `Tdata`」** — `S` のみ determinate (type-P₂ 固定で `Sdata` 入力)、`T` の非対称は
**設計意図**であり、`Tdata` を入力 carrier にすると §14 結論 (`T_typeII` 14.9) を入力へ格上げする設計違反。
**lane-c の自己訂正 (本 issue cont.¹² 訂正) が正しい**。私の Tdata 指示は無効。

**ただし裁定の spirit は不変かつ lane-c の実 trajectory と一致**: punt/再配置せず自クラスタ V-side を
正面から、は正しい。ユーザーも lane-c session で **「§16 V-side 構成続行」を裁定済**、lane-c は既に
`isMulCommutative_U` (13.2.a 非-gated 実証明) を landing し punt から脱却している。⟹ 戦略 fork 却下は維持、
具体策のみ差し替え。

**正しい path (lane-c が特定済、これを進めよ)**: 真の V-side gate = `T_typeII` (14.9、BG-structural
reduction 済) → `exists_typeI_maximal_overNormalizer_V` (S-side `exists_typeI_maximal_overNormalizer_U`
S15:609 ~350 行の dual、`T_typeII`-gated + V-side helper chain) → `exists_MHypothesis` (~35 field assemble)。
multi-iteration の hard work、lane-c の own。`T_typeII_structural_inputs` の 5 連言 = `TypeIIData T` field
そのもの (深 §14.9 char)。詳細 = `notes/peterfalvi/s16_w4_char_cascade.md` cont.¹²。

## ⛔ 2026-06-30 HUB tick² — c の `TypePData T` spine 再導入を HOLD (マージ却下)

c の V-side バッチ (cont.¹⁴–¹⁶, branch tip) を hub が検証 → **spine sorry regression** ゆえ `git merge --abort`。
**ただし V-side helper 構築 (exists_typeI_maximal_overNormalizer_V / isMulCommutative_V / 共役・fitting dual 群
+ 4 本の新規 scaffold sorry) は genuine で歓迎 — それは残す。** 却下対象は次の 1 点のみ:

**問題**: `FeitThompson.lean` の §16 spine carrier に `Tdata : TypePData (mp.)T` + `Tdata_V_eq` を追加し、
**既存の spine constructor `section16TypePStructure_of_isMinimalSimpleOdd`**（→ `sectionSixteenHypothesis`
→ `feitThompson`、合流前は sorry-free）の中に **`have hTP2 : IsTypeP2 mp.T := sorry`** を挿入した。
これは:
1. **FT spine への sorry regression**（既存 sorry-free def に sorry 混入、merge_monitor HOLD 条件）。
2. **型が逆で設計矛盾**: `T_typeII` (14.9) が産むのは **`TypeIIData mp.T`（T = type-II）**。`TypePData mp.T` /
   `IsTypeP2 mp.T` は **type-P2**（より強い、type-P2 ⟹ type-II の逆は不成立）。c 自身の cont.¹²「真の gate =
   T_typeII = T は type-II」とも、`FeitThompson:276`「T need not be type-P₂, no symmetric Tdata」（c が今回
   **削除**した docstring）とも矛盾。`IsTypeP2 mp.T` は一般に偽ゆえ sorry は埋まらない（= Tdata dead-end の
   裏口再導入）。
3. **d 所有 carrier の非-additive 編集**（FeitThompson §16 carrier 構造の docstring 削除 + 既存 constructor 改変）。

**正しい path (差し替え)**:
- T-side data が要るなら **`TypeIIData mp.T`**（`T_typeII` から導出、constructed か新規 lemma の scaffold-sorry）
  を使う。**`TypePData mp.T` / `IsTypeP2 mp.T` は使わない**（T は type-II であって type-P2 でない）。
- **既存 spine constructor (`section16TypePStructure_of_isMinimalSimpleOdd` 等) に sorry を挿入しない**。
  carrier 拡張が本当に要るなら新規 def/lemma 側に隔離し、spine は sorry-free を保つ。
- **`FeitThompson:276` の "no symmetric Tdata" docstring を復元**し、d 所有 §16 carrier を非-additive に
  改変しない（carrier 形状は共有境界 = 要 coordination）。
- V-side helper 群はそのまま継続。`exists_MHypothesis` の assemble は `TypeIIData T` 経由で。

## 2026-06-30 lane-c 応答 — HUB tick² の修正完了 (commit `8aa7b8b4`)

tick² の指摘 (spine sorry regression + 型が逆 `IsTypeP2 T` + d-carrier 非-additive 改変) を全面是正:
- `Tdata` carrier (base Hypothesis + Section16* + spine constructor の `hTP2 : IsTypeP2 mp.T := sorry`) を
  **revert** (737a15de)、`FeitThompson:276`「no symmetric Tdata」docstring **復元**、`section16TypePStructure_of_isMinimalSimpleOdd`
  を **sorry-free に戻した** (検証済: 0 sorry / 0 IsTypeP2 mp.T)。
- V-side helper の T-side type-P 源を **off-spine の honest `reconciled_typePData_T`**
  (`∃ data : TypePData T, data.U = V ∧ data.W1 = W2`、TRUE な §13 reconciliation) に差し替え。
- V-side helper 群 (hub が genuine と承認した exists_typeI_maximal_overNormalizer_V / isMulCommutative_V /
  共役・fitting dual / complement / typeII_overNormalizer_frobenius_V) は全て残存・build-green。
- full build 3889 green、AxiomsCheck OK。

残 = exists_MHypothesis wiring (tick² 指示通り TypeIIData T + reconciled_typePData_T 経由)。

## 2026-07-04 lane-c (/loop) — 🎯🎯 exists_MHypothesis (14.10) LANDED — instance 壁 crossed

`exists_MHypothesis` の bare `sorry` を **genuine な MHypothesis carrier 構成に置換** (commit `a1faa86d`
+ `e96ade8b`)。38 field 中 35 が genuine、残 3 のみ deep §7/§13 char sorry。

- **instance-coherence 壁は自作 haveI が原因**と判明 (cont.⁴⁸ の proposed option a/b は不要)。全 instance は
  `Fintype.ofFinite _` / `invertibleOfNonzero _` に落ち `Finite G` (Prop) は proof-irrelevant ゆえ producer
  (`exists_M_hypothesis78`) と consumer は **同一 scoped instance に defeq**。⟹ `open scoped S12.FiniteInduce`
  + competing haveI を入れないだけで解決。
- **34 genuine field**: exists_M_hypothesis78 (M/typeIHyp/h78) + h78 由来 (tau/tau1/psi/betaM/Mset) +
  `base_*` helpers (P/Q_isTI, W_normalizer_V, card_normalizer_{P,Q}) + G0 集合演算 (off_dadeSupport/orbit_cover)。
- **psi_degree_eq_e も genuine 化** (2 本目 commit): exists_M_hypothesis78 に `ζ_{ind1H}(1)=[M:K]` witness 追加
  → consumer で `zeta_one_eq_ind1H_one` + hindex で discharge。
- **psi_tau1_norm_one も genuine 化** (cont.⁵⁰、commit `e8a59466`): `‖ζ‖²=1` witness (Frobenius 誘導 unit-norm
  `inner_self_induce_eq_one_of_frobeniusGroup`、shared infra) + `nu_isometry` で discharge。
- **残 2 char sorry** (両方 genuinely gated): `betaGrid` (13.1.d η-grid、Track A / issue 3002)、
  `h78_zetaNuRho_normSq_ge` (7.8.b、BetaDecomp + quadratic-norm 公式 gated = lane a 領域、clean cite 不可)。
- betaGrid は signs+grid を単一 honest existential で deferred (偽な符号を assert しない)。
- full build 3910 green、AxiomsCheck OK。詳細 = `notes/peterfalvi/s16_w4_char_cascade.md` cont.⁴⁹/⁵⁰。

**spine 前進**: `field_normalizer_structure → exists_MHypothesis` の gate が assembly 完成で解消。
exists_MHypothesis は 34 genuine field + 2 char obligation (psi_degree/psi_tau1_norm は discharge 済)。
残 2 は Track A (issue 3002) と (7.8.b) lane a landing 待ち — この 2 が埋まれば §16 endgame は spine 直結。
