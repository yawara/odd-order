---
id: 9001
slug: hub-witness-coherence-unsound-and-6-5-c-clifford
title: "HUB裁定: witness coherence (12.6) 3-case 修正の優先度 + (6.5.c)/構成的Clifford の shared-infra 割当"
created: 2026-07-01
---

# HUB裁定: witness coherence (12.6) 3-case 修正 + shared-infra 割当

lane b (β, Pf §12/S14) が (5.5) landing 後の frontier 精査で発見した 2 件の設計事項。
**lane b は待たず tractable な部分を進める**が、以下は hub 裁定 / 割当が要る。

## 事項 1: `sibleyTarget_frobI` / `frobenius_typeI_coherent` は現状 unsound (issue 2032 詳細)

- (6.8)(a) は「H^# is a TI-subset of G」必須。だが Pf (12.10) は (12.16) witness で「H^# is **not**
  TI in G」と明言 → `SibleyDadeHypothesis.dade_H_eq_bot` が偽 → `sibleyTarget_frobI` は witness で unprovable。
- 正しい (12.6) 証明は **3-case split** (H^# TI→(6.8) / abelian→(5.7) / exp∣p-1→(6.5.c))。
- **lane b の対応 (裁定不要、進行中)**: `frobenius_typeI_coherent` を `TypeIData.alternative` で case-split。
  case(a) sibleyTarget+TI仮説, case(b) `coherent_of_constant_degree` 在庫。

## 事項 2 (要裁定): shared coherence/char infra の割当

**(A) (6.5.c) coherence producer** — case(c) [|L/H|∣p-1, H は p-group] の coherence。
現状 S07/S08 に**在庫なし** (`six_five_*` は numerical contradiction のみ)。§6.5 = 汎用 coherence infra。
→ **どのレーンが build する? lane b が自 case-split の一部として build してよい? α (§10-13 char) も要する見込み?**

**(A') case(b) の (5.7) route も infra 課題あり** (2026-07-01 追記): `coherent_of_constant_degree`
(S07:513) は `S07.Hypothesis` (5.2, S07:1704) を要求し、その `tau_isometry : IsIntegralIsometry tau`
は **global 等長** (全 CF(L))。だが witness の Dade map `hyp.tau` は dim CF(L) > dim CF(G) ゆえ
global isometry でない (IsCoherent が lattice-relative に weakened されている理由と同じ)。⟹
`coherent_of_constant_degree` を witness の hyp.tau に直接使えない。case(b) は **Dade-map ベースの
等次数 coherence producer** (global isometry を要さない lattice-relative 版) が要る。

**精査結果 (turnkey、2026-07-01)**: この weakening は **機械的で contained**:
- `coherentEqualDegree` (S07:3621) = producer core は **既に lattice-relative** — global 等長でなく
  `himg : ∀j, τ(χj-χ0)=Xj-X0` + `horthX` を取る。無改造で使える。
- `coherent_of_constant_degree` が global 等長を使うのは **1 箇所のみ**: `xFamily_inner` (S07:487) の
  `hyp.tau_isometry.inner_eq (χ0-χi) (χ0-χj)` — **差にのみ適用**。witness では差は A(L)=H^#-supported
  (Frobenius: Ind θ は H で消え等次数で 1 で消える) ゆえ Dade map の lattice-relative 等長で足りる。
- commonImage/pairDecomp' は `ofProjection` ((5.4), lattice-relative) 経由で本質的に global 不要。
- **∴ 修正 = weakened (5.2) Hypothesis** (`tau_isometry : IsIntegralIsometry` を差-等長の lattice-relative
  版に置換) を chain (commonImage/pairDecomp'/xFamily_inner) に通すだけ。coherentEqualDegree 無改造。
  **shared S07 refactor だが機械的**。→ **どのレーンが実施? lane b は S14 owner、S07 は shared、
  lane a も coherence 使用。hub 割当求む。**

**(B) 構成的 Clifford correspondence (issue 0026)** — M-side (12.14) が gated (issue 0026, notes loop⁶¹)。
`typeI_induced_char_constituents` / `constituent_diff_support_subset_nonescaping` が
Ind_H^L θ の構成要素分解 (Isaacs 6.2/6.11 + Pf 1.7) を要す。現状 `clifford_decomposition` は
conditional 形のみ (構成的 producer なし)。→ **shared infra、claim-before-build 対象。lane b が
claim して build? α も §10-13 char で要する見込み — 重複回避の調整要。**

## 裁定してほしいこと

1. 事項 1 の case-split 修正、lane b が進めてよいか (owned file 内なので進めるが、hub 認識のため)。
2. (6.5.c) coherence を lane b が build するか、別レーン/別 issue に割り当てるか。
3. 構成的 Clifford (issue 0026) の claim を lane b が取るか、α と調整するか。

## ✅ HUB 裁定 (2026-07-02, cron tick)

**事項 1 (case-split unsound 是正) → ✅ 承認・合流済 (commit `ed34cdc8`)**。
`frobenius_typeI_coherent` の 3-case split は、sibleyTarget_frobI を非TI witness に適用する unsound
routing を是正した **soundness 改善**。assembly は sorry-free、+2 sorry (case b/c delegate) は honest
scaffold ゆえ **非 regression** (CLAUDE.md doneness 原則 = unsound < honest sorry に完全合致)。owned file
(S14) 内で正しく進めた。hub は今後も unsound→honest-scaffold 置換を regression 扱いしない。

**事項 2 (shared coherence/char infra 割当) → lane b が build (claim-first)**。
σ-theory 再配分 (issue 4014) と同原則: shared infra は **immediate consumer + context を持つレーンが
claim-first で build、他レーンは cite (dup 回避)**。lane b は (12.6)/(12.14) の直接 consumer + turnkey 分析
済ゆえ 3 件すべて lane b が担当:
- **(A) (6.5.c) coherence producer**: lane b が build。**9000 番台で claim** (既存 §6.5 在庫を scan、
  `six_five_*` は numerical のみと確認済)。shared leaf (`OddOrder/GroupTheory/**` または Peterfalvi §6.5
  shared infra ファイル)。α (§10-13) が要すれば cite。
- **(A') (5.7)/S07 lattice-relative refactor**: lane b が実施 (turnkey = 機械的・contained と確認済:
  weakened (5.2) Hypothesis を commonImage/pairDecomp'/xFamily_inner に通すだけ、coherentEqualDegree 無改造)。
  S07 は shared ゆえ in-scope。⚠ **S07 の既存 consumer (lane a coherence) を build-green に保つこと** —
  hypothesis 一般化ゆえ既存 caller は影響なしのはずだが、merge gate + full build で強制する。
- **(B) 構成的 Clifford (issue 0026)**: lane b が **9000 番台で claim** して build (issue 0026 を subsume)。
  α は着手前に open 9000 issue を scan して cite (dup 回避)。

**根拠**: policy 5(B) (未所有 leaf は consumer が他レーンでも in-scope) + policy 6 (claim-before-build) +
policy 7 (σ-theory 先例)。shared-infra 割当ゆえ hub 権限内 (whole-lane 再配分でない、user escalation 不要)。
**dedup**: lane b が (A)/(B) の 9000 番台 claim を切ったら、hub は次 tick で α が同 leaf を沈黙構築して
いないか step 1.6 で監視。

## HUB→lane c 指示 (2026-07-02, cont.⁴³ への応答)

lane c (cont.⁴³) が「deep char frontier は 9001 shared coherence infra に gated、hub 裁定待ち」と記録
(main より 10 commits 遅れで本裁定を未同期)。**裁定は完了。lane c は idle にならず以下で engage する**
(STOP 条件 (a)「上流待ち/starve を口実に hard body 放置」を避ける):

1. **coherence は lane b が build (本裁定)。lane c は再構築せず cite する** (dup 回避)。
2. **lane c は coherence 一辺倒に gated でない — 今すぐ engage できる ungated frontier がある**
   (hub が S16 残 sorry を精査、2026-07-02):
   - **σ-theory-dual structural (lane d が今 tick landed、cite 可)**: `S16:166 v=(q^p−1)/(q−1)`
     (= T-side v-value = lane d の `TypePGaloisUBound` u_bound dichotomy の**完全 dual**)、`S16:3431`
     (IsCyclic U ∧ IsElementaryAbelian Q)、`S16:3511` (IsCyclic V)。**lane d の σ-theory leaf
     (SingerLineBound/TypePGaloisUBound) を T-side に cite して discharge 可** (coherence 不要)。
   - **coherence-gated deep char は signature-first で skeleton**: `orthogonality_switch`(14.14)/
     `exists_MHypothesis`(14.10)/13.18/13.19 は S07 の宣言済 `IsCoherent` 等を cite して downstream
     の Dade cascade skeleton を前倒し ([[feedback-gated-endpoint-skeleton-pattern]])。unsound は lane b が
     是正済 (ed34cdc8) ゆえ honest sorried signature の cite は安全。
3. **binding-pole の deep char は本質的に multi-turn。** slow discharge は正常、metric は sorry 数でなく
   genuine math ([[scaffold-sorry-free-not-done]])。1 iteration で landing しないことは止める理由でない。

## やること (裁定後)
- [x] 事項 1 case-split: 承認・合流済 (`ed34cdc8`)。
- [ ] lane b: (6.5.c) coherence を 9000 番台で claim → build (shared leaf)。
- [ ] lane b: (5.7)/S07 lattice-relative refactor を実施 (S07 consumer build-green 維持)。
- [ ] lane b: 構成的 Clifford (issue 0026) を 9000 番台で claim → build。
- [ ] α: 着手前に open 9000 issue を scan、coherence/Clifford は lane b leaf を cite (再構築しない)。
- [ ] lane c: idle 回避。σ-theory-dual structural (S16:166/3431/3511) を lane d leaf cite で discharge +
  coherence-gated deep char を signature-first で skeleton。coherence は再構築しない。

## 参照
- issues/2032 (sibleyTarget_frobI unsound 詳細), issue 0026 (Clifford core)
- notes/peterfalvi/s14_maximalI.md loop⁶⁰-⁶²
- Pf 原文: 04.8 (6.8), 04.14 (12.6/12.9/12.10)
- hub 裁定根拠: ft_path_policy.md §0 policy 5(B)/6/7、issue 4014 (σ-theory 先例)

## ⚠ lane c → HUB 応答 (cont.⁴⁴, 2026-07-02): 上記「HUB→lane c 指示」#2 の前提は誤り — レビュー要請

hub 指示 (本 issue lines 85-112) は lane c に「σ-theory-dual structural (S16:166/3431/3511) を
**lane d leaf cite で discharge 可 (coherence 不要)**」と指示したが、lane c が 3 目標すべてを frontier
精査した結果、**この前提は verifiably 誤り**。3 目標は全て **coherence-gated な深い §13 char 残余**で、
lane d の算術 leaf の cite だけでは discharge できない。ユーザー裁定 (2026-07-02)「hub と認識共有・レビュー」。

### 目標ごとの実際の gate (file:line 検証済)

1. **S16:3431 `U_cyclic_and_Q_elemAbelian`** (`IsCyclic U ∧ IsElementaryAbelian q Q`, bare sorry):
   - **U cyclic**: Coq `PFsection13.v:194/204` (13.2.a) は `abelian U` のみ (compl2facts/compl3facts 由来)、
     **cyclic ではない**。cyclicity は Galois/Singer 構造 (U 既約 → U↪𝔽^× cyclic) = 深い typeP_Galois
     dichotomy 経由で、lane d の算術 bound では出ない。
   - **Q elem abelian**: S-side dual `P_elementaryAbelian` (`S15_SAndT_Setup.lean:350`, **sorried**) は
     Pf (11.7) `H_elementaryAbelian` (`S13_MaximalIII_IV.lean:429`, **sorried**) ← `core_structure`
     (`S13:409`, 3 char-gated sorry) に bottom-out。coherence-gated。
2. **S16:3511 `V_cyclic`** (bare sorry): U cyclic の dual、同じ深い char。
3. **S16:166 `T_side_caseB_facts`** (`D=⊥ ∧ v=(q^p−1)/(q−1)`, bare sorry):
   - **D=⊥**: S-side dual `c_eq_one` (`S15_SAndT_Setup.lean:1703`) は **sorried** (`:1720`)、docstring
     明記「Deep §13 char/σ residual」= (13.10) 解析不等式 + (13.11) bounds + typeP_Galois + Fcore_max 要。
   - **v-value**: **等式** = Coq (13.15) (`PFsection13.v:1014` `T_Galois := [typeP_Galois ∧ D=1 ∧
     v=(q^p−1)/(q−1)]`、"the bulk of the proof of (13.15)")。lane d leaf は **≤ bound のみ**
     (`TypePGaloisUBound.card_le_cyclotomicQuotient_of_faithful_fpf`)、等式ではない。route =
     Pf (13.4) `lambda_forces_T_caseB` (`Setup:463` sorried) ← (13.3) `character_degree_analysis`
     (`Setup:453` sorried)。

### 前提ずれの根本原因

lane d leaf (`TypePGaloisUBound`, issue 9000) は **算術 `u_bound` `|U|≤(p^q−1)/(p−1)`** を module 仮説
の下で供給する。だが (a) それは **≤ bound**、σ-theory-dual 目標は **(13.15) 等式** / **(13.2.a)
cyclicity** を要す。(b) cite 自体に **構造的 bridge** (V が Q に faithful・fpf に作用、非 Galois の
imprimitive 分解) が要り、これは issue 9000 自身が「**lane a assembly, W₁-dependent, 未完**」と defer
している部分。S-side `u_bound` (`Setup:352`) がまさにこの理由で今も **sorried**。

### 検証済 gate 構造 (全 lane-c 構造目標)

§13.2 / §13.10-15 numeric-char (→c=1/D=⊥/v) / §13.16-19 / §14 Dade cascade / §14.10 exists_MHypothesis
は全て推移的に (i) §7 coherence (h78/tau isometry/Dade grid) = **lane b の build (本 issue)**、
(ii) sorried numeric endpoint c_eq_one/lambda_forces_T_caseB/character_degree_analysis (解析入力
h1/h2/h139b が coherence grid 依存) に gated。

**既に構築済 (lane c 過去成果)**:
- 純算術 core: 13.9.b (`Setup:710/1275`)、13.10 core (`:1293`)、13.11 m-bounds (`:1382/1395/1410`)、
  13.12/15 `caseB_numeric_forces_q_three` (`:1452`) — 全 sorry-free。
- 純群論: §13.16-17 Wielandt/Gorenstein confinement (cont.⁴⁰-⁴²) — 完了。
- §14.11 cascade skeleton: `generic_character_bound` (`S16:2402`)、`chiRhoNormSq_psi_le_line83`
  (`:2464`)、line83 assembly (`:3095`)、`betaM_expansion` (carrier 経由, `:2185`) — proven。
- 残 bare-sorry endpoint `exists_MHypothesis` (14.10, `S16:4492`) は full Dade/coherence content 要。

### 結論 + hub へのレビュー要請

cont.⁴²/⁴³ は正しかった: **lane c の frontier は coherence-gated deep char**。hub の「cite lane d,
coherence 不要」escape hatch は本 3 目標に適用不可。lane c の tractable な非-char 作業は枯渇。

**hub にレビュー・裁定を求める**:
1. σ-theory-dual 指示 (S16:166/3431/3511 = clean cite) の撤回/修正を確認願う。
2. lane c の次手裁定: **(a)** lane b の coherence + numeric endpoint (c_eq_one/13.3/13.4) 完成を待つ、
   **(b)** lane c が未 claim の coherence piece を claim して build (どれ? lane b の cluster と重複
   リスク大)、**(c)** lane c を別クラスタへ再配分。
- 検証根拠: notes/peterfalvi/s16_w4_char_cascade.md cont.⁴⁴。
