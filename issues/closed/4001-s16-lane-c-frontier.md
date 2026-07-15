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

## 2026-07-04 lane-c (再開, re-re-org 後) — 🎯 orthogonality_switch (14.14) PROVEN

re-re-org (S15→b、c は S16 W-side (14.14) cascade + parity contradiction 集約) 後の初 landing。
cont.⁵¹ の「solo work 枯渇」を訂正し (14.14) の genuine arithmetic を landing (commit `a67a4ef0`):

- **`orthogonality_switch` (14.14) の bare sorry を実証明化**。これは `H_eq_U` (14.16)→(14.15)/(14.16)
  矛盾 cascade (23-method `OrthogonalitySwitchData` namespace、既 sorry-free) を発火させる key sorry。
- **`Hypothesis.caseB_forces_q_three_and_p_five`** (sorry-free): case-(b) bound `(v-1)/pq≤pq-1` +
  v-value (14.4) + `key_inequality` (14.8.a, 既 proven) から q=3∧p=5 を導出する数論核 (`q^(p-3)<p²`
  → (14.8.a) → q=3、`3^(p-3)<p²` vs `p²≤3^(p-3)` p≥7 induction → p=5)。
- 残 char 義務は opaque bare sorry から **faithful `orthogonality_switch_pairing_bounds`** (S16:4526,
  §7/§8 = (7.9) pairing dichotomy + (8.17.c) disjoint Dade support + (7.8.b) norm bound = lane-a 領域)
  に置換。doneness↑ (carrier 構成可能性で判定)。
- full build 3916 green、AxiomsCheck OK、新 axiom なし。詳細 = `notes/peterfalvi/s16_w4_char_cascade.md` cont.⁵²。

### 併行 landing: main_size_bounds (14.11.1) k>2pv isolate (commit `f56039d7`)

`main_size_bounds_structural` の opaque `k>2pv` bare sorry を、精密 §13/§15 structural obligation
`hstruct : ∃x, k=v·x ∧ x≡1 [MOD p] ∧ x≠1` ((13.17) 分解 + W₂ fpf + K≠V) + proven arithmetic
(`two_mul_add_one_le_of_modEq_one_odd`: x≡1 mod p ∧ odd x ∧ x≠1 → x≥2p+1; k=|K| odd ⟹ x odd ⟹ k=vx>2pv)
に分解。

**c-solo W-side arithmetic 完了 (2 本 = 全て出し尽くし)**: 残 9 leaves は全て cross-lane gated と精査確定
— dichotomy `orthogonality_switch_pairing_bounds` の (7.9)=§7 coherence (b) / (7.8.b)=a / (8.17.c)=§8 (b)、
η-grid=issue 3002 (b field+a threading)、U/V cyclic・T_typeII=b §13、v-value=9000。W-side assembly は
全 proven、leaves は precise faithful obligation で pin 済 (signature-contract 成立)。前進は b/a/9000 上流供給が先決。

## 2026-07-04 lane-c (loop cont.) — U-cyclic "vestigial binder" 仮説 = 検証済 NEGATIVE

main +7 取り込み (a=11.8 §9-bridge / b=§12 witness、S15/S16 未変更 ⟹ 3002/9009 grid field **未 landing**)。
9002 (constructive Clifford) は **完了確認** (`✅ lane b 完了 loop¹¹⁴`: `typeI_induced_char_constituents`
一般ケース landed、全 RepTheory Clifford/ext leaf = 0 sorry)。⟹ c の 2 mandate (S16 assembly / 9002) は
both substantially complete。残 9 S16 leaf を policy (A)「ungated genuine math へ降りる」で正面攻略:

**U cyclic (3568) の field-repr 経由 discharge を試行 → REVERTED (genuine gate 確定)**:
- 仮説: `exists_pu_field_repr`/`_W2`/`field_normalizer_of_U_characteristic_of_inputs`/`_of_fpf` の
  `[IsCyclic ↥U]` binder は **vestigial** (body は `data.U_commutative` (abelian) + `hfaith` を使用、
  coq `PFsection14.v:574 cUU: abelian U` と一致)。μ:U↪𝔽_{p^q}^× 単射 ⟹ U cyclic は **consequence**。
- **反証**: `exists_galoisField_repr` (SingerField.lean:297) は `section Irreducibility` (190-191
  `variable [CommGroup C] [IsCyclic C] [Finite C]`) 内 ⟹ `isSimpleModule_of_isCyclic_faithful_card`
  (199) 経由で **`[IsCyclic C]` を genuine に要求** (Singer irreducibility の確立に cyclic を使う)。
  binder 除去 → build-RED (777: failed to synthesize instance)。∴ **U cyclic は field-repr で false gate でない**。
- **代替 singer-adapter 経路** (`singerAdapter_isCyclic_card_dvd` S11:3841、abelian+faithful+**irreducible**
  ⟹cyclic): U abelian ✓ / faithful ✓ だが **P U-irreducibility** が要 → norm-one 設定で循環
  (irreducibility of norm-one action は field embedding を要す)。かつ P は S=P⋊(U⋊W₁) の minimal normal ゆえ
  **U⋊W₁-irreducible であって U-irreducible とは限らない** ⟹ A=U の singer 直接適用は unsound。
- **結論**: U cyclic (と dual の V cyclic 3651) は genuine §13 type-P 構造 (chief-factor / P-irreducibility)
  に gated = **b 領域**。precise 化: 旧「§9/§11 char」→「§13: P(resp Q) の U(resp V)-irreducibility + abelian」。
  **この route は再攻略しない** (field-repr は cyclic 必須、singer は irreducibility 循環)。

**S16 全 9 leaf = cross-lane gated 再確認** (assembly は full proven、build 3880 green): T_typeII (79,§13)/
v-value (174,9000 Galois)/η-grid (2581,3002)/U cyclic (3568,§13 irred)/V cyclic (3651,§13 irred)/
caseB_contradiction (4493,§3-4 Dade+13.19)/dichotomy (4673,§7.9+8.17.c+7.8.b)/betaGrid (5171,5239,3002)。
最大 leverage = **b/a の 3002/9009 landing** (η-grid batch 一斉 unblock)。次 iter で main 再取り込み監視。

## 2026-07-04 (同 loop, 続) — ⚡ 訂正: U/V cyclic は §13-gated **でない** (Zsygmondy-lite route)

上記「§13 P-irreducibility gate」結論は **too quick で誤り** (user pushback 正当)。vestigial-binder は dead だが、
別の **c-ownable non-circular route** が在る:

**機構**: `isSimpleModule_of_isCyclic_faithful_card` (SingerField.lean:199) の証明は cyclicity を
**generator にしか使わない** (g^N が dim<q の proper constituent を固定 (μ(g)^{p^d-1}=1, (p^d-1)∣N),
N=p^{(q-1)!}−1 → g^N が M 全体を固定 → g^N=1 (faithful) → |C|∣N 矛盾)。
**abelian C へ Cauchy で一般化**: |C|=(p^q−1)/(p−1) は p^q−1 の **primitive prime divisor** r
(ord_r(p)=q; q odd prime で存在) で割れる (r∤p−1 ∵ ord=q>1) → Cauchy で order-r 元 a → **Wilson**
(q∤(q−1)!) ⟹ q=ord_r(p)∤(q−1)! ⟹ r∤N ⟹ a^N≠1、だが a^N は全 constituent 固定 (同論法) ⟹ a^N=1 矛盾。

**mathlib 在庫確認済**: `sub_one_lt_natAbs_cyclotomic_eval` (|Φ_q(p)|>p−1>q ⟹ Φ_q(p) は q の冪でない
⟹ primitive prime 存在、LTE `v_q(Φ_q(p))≤1` 併用)、`(isRoot_cyclotomic_iff.mp hroot).eq_orderOf`
(ord=q)、`ZMod.orderOf_dvd_card_sub_one`、`coprime_of_root_cyclotomic`。証明 pattern =
`Nat.exists_prime_gt_modEq_one` (PrimesCongruentOne.lean:28-59)。

**build plan (次 iter 以降、c 所有 `GroupTheory/RepresentationTheory/SingerField.lean` に additive)**:
1. `exists_primitive_prime_dvd_cyclotomic` : q prime, p≥2 ⟹ ∃ r prime, r∣(cyclotomic q ℤ).eval p ∧ orderOf (p:ZMod r)=q ∧ r≠q。
2. `isSimpleModule_of_abelian_faithful_card` : `[IsCyclic C]`→`[CommGroup C]` に弱め、generator を
   Cauchy(order-r 元)に差し替え (fix 論法は m∈s 部分そのまま再利用)。
3. `exists_galoisField_repr` / `exists_pu_field_repr` を abelian 版に re-point、`field_normalizer_of_U_characteristic_of_fpf`
   内で hu_full+U_commutative+faithful から `haveI : IsCyclic ↥U` を derive → `[IsCyclic ↥U]` binder 全除去。
   `U_cyclic_and_Q_elemAbelian` の U-cyclic sorry (3568) 消滅 (無条件版は case 9.7.a で偽ゆえ **使わず**
   full-value context で局所導出)。V cyclic (3651) は dual (|V|=(q^p−1)/(q−1)=v-value 174 landing 後)。

## 2026-07-05 (loop 継続) — ✅ U cyclic 実証明化完了 (Zsygmondy-lite 5-stage chain)

前 iter の「vestigial-binder は FALSE」negative を、**別 route (abelian Singer 既約性) で覆して U cyclic を
実際に閉じた** (S16 real sorry 9→8、full build 3917 green、AxiomsCheck OK・新 axiom なし)。5 stage:

1. `orderOf_eq_of_prime_dvd_geomSum` (PrimitivePrimeDivisor.lean, 6aaebe82): prime factor r≠q ⟹ orderOf(p:ZMod r)=q。
2. `exists_prime_orderOf_eq` (同, 61cbad1f): **Zsygmondy n=q prime 特殊ケース** — q odd prime で ∑_{i<q}p^i に
   primitive prime divisor 存在。not_sq_dvd (LTE `Nat.emultiplicity_pow_sub_pow`) + n>q + 場合分け。
3. `isSimpleModule_of_abelian_faithful_card` (SingerField.lean, 3ada6138): Singer 既約性を **cyclic→abelian(任意)**
   一般化。cyclic 版 body を任意元へ parametrize、generator の代わりに Cauchy 元 (primitive prime r)、
   a^N=1 ⟹ r∣N=p^{(q-1)!}−1 ⟹ q∣(q-1)! を Wilson で矛盾。
4. `exists_galoisField_repr` を abelian 版へ re-point (c8768402): `[IsCyclic C]` omit + `Odd q` thread。
5. S16 の `[IsCyclic ↥U]` binder 4 本除去 + `U_cyclic_and_Q_elemAbelian` U-cyclic sorry 削除 (a3107ad3):
   field model は U abelian (`basic_structure.U_commutative`, coq `cUU:abelian U` と一致) から構成、
   μ:U↪𝔽_{p^q}^× 単射は consequence。**case 9.7.a で U rank-2 非 cyclic ゆえ無条件 U-cyclic は元々不健全**、
   engine が abelian で足りるので false gate を除去。

**教訓**: 「gated」評価は route を尽くしてから (user pushback 正当)。1 つの route (vestigial binder) が dead でも
別 route (数論 infra 構築) が live。isSimpleModule_of_isCyclic_faithful_card は unused 化 (削除候補)。

**V cyclic (3077, dual)**: 同 route で閉じられる — dual field model `exists_pv_field_repr` (V acts on Q,
|V|=(q^p−1)/(q-1), p odd prime) + isSimpleModule_of_abelian_faithful_card。ただし |V|=v-value は
T_side_caseB_facts (127) の sorry (§13 Galois, 9000)。T-side は常に case-B ゆえ V cyclic は無条件真だが
v-value 構築が先決。次 stage 候補。

## 2026-07-05 (loop 継続) — ✅ V cyclic 実証明化完了 (T-side dual field model)

V_cyclic (3646) を U cyclic と同 route で closure (S16 real sorry 8→7、full build 3917 green,
AxiomsCheck OK)。commit ad7efe7f。dual helpers V_le_normalizer_Q/conj_mem_Q (dd320a73) の上に、
exists_pu_field_repr の module 構成を U→V/P→Q/char p→q/exp q→p で mirror し
exists_galoisField_repr[p:=q,q:=p] → μ:V↪(GF(q^p))ˣ 単射 → isCyclic_of_injective。
faithful=D⊥ (proven)、V abelian=S15.isMulCommutative_V、|V|=v (card_V_eq_vd+d=1)、|Q|=q^p=card_Q_eq。
落とし穴: `open scoped IsMulCommutative in` が Additive Q の AddCommGroup 供給に必須。

**U/V cyclic + kernel-cyclic 連鎖の単一残 gate = v-value** (T_side_caseB_facts 174 の
`v=(q^p-1)/(q-1)`, §13/9000 σ-theory)。S-side u-value (S15.caseB_order_u_data) も同 σ-theory gate。
両者は type-P Galois/(9.7) dichotomy foundation (issue 9000, lane a/d 領域) — c 単独 build は不可。
∴ V_cyclic closure で c の abelian-Singer machinery による S16 leaf 消化は一段落。残 S16 leaf
(T_typeII/caseB_contradiction/dichotomy/betaGrid/eta_grid) は §3-13 char/grid で other-lane gated。

## 2026-07-05 (loop 継続²) — 🎯 (14.14) orthogonality_switch_pairing_bounds 完全実証明化 → F3 残は全て cross-lane gate

**本 session の landing** (詳細 = notes cont.⁵⁴): (14.14) の bare sorry を新 leaf 2 本
(S16_PairingCoherence 1057 行 / S16_PairingBessel 584 行, 全 sorry-free) + S16 instantiation で
完全実証明化。commits 339e1f52 / d5e13a98 / a6c06957 / 60b9b6b6 / 40d2cdcc。
cont.⁵² の「(8.17.c)/(7.9) は他レーン gated」は **phantom だった** (S10/S09 に proven 済) — 
cont.⁵³ 教訓の再適用が (14.14) 全体を unlock した。S16 real sorry 7→6。

**F3 残 6 sorry の再検証結果 (全て真 gate、再攻略しない)**:
- 80 `T_typeII_structural_inputs`: b §13 T-side (base に Tdata withdrawn 確認済)。
- 175 `T_side_caseB_facts` (v-value) / 5347 `main_size_bounds`: issue 9000、a claim
  (§9 block 分解 assembly 残、2026-07-03 節)。
- 2599 `eta_grid_facts_on_G0` / 4604 `caseB_contradiction_data` / 5415 `betaGrid`:
  η-grid (3.9.a/c)。b の 3002 threading (3dc9306e, 7 primitives 供給済) の後続
  「S15 内導出定理」待ち — **c-side consumer spec を issue 3002 に追記済 (2026-07-05 節)**。
  (3.9.c) は carried 7 fields のみからは導出不可 (Galois 同変 witness が S05 σ-package 側に
  ある; ω₀₀=1_W の同定も未 carry) を確認。
- card_G0 (0044) は 2026-07-04 off-path 判定 (再攻略しない)。betaM_vanish 等の c-solo 分は
  既に実証明済。

**c の現 mode**: b (η-grid 導出 or S15 cascade) / a (9000 assembly) の main 合流を監視し、
supply 着き次第 2599→5415→4604 (文書順) を組立。それまで S16 W-side に ungated solo work なし。
