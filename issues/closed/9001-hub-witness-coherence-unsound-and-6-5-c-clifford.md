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
- [x] **lane b: (5.7)/S07 lattice-relative refactor を実施** (commit `d31b9763`, 2026-07-02)。
  `S07.Hypothesis.tau_isometry` (global `IsIntegralIsometry`) → **差-等長** `tau_isometry_diff`
  (`∀ a b c d ∈ S, ⟨τ(a−b),τ(c−d)⟩=⟨a−b,c−d⟩`) に weakened。helper `inner_eq_on_zSpan_pair`
  (差-等長→zSpan 双線型拡張) で `ofProjection` に供給、`pairDecomp` に `hζ` 追加、`xFamily_inner`
  を `hdiff` 版に (= S14 `xFamily_inner_dade` を subsume)、unused `tau_inner_eq` 削除。
  **`coherent_of_constant_degree` が Dade-compatible に**。full build green (3893 jobs, axioms OK)。
  S07.Hypothesis は未 construction ゆえ lane-a regression なし。
- [x] lane b: (6.5.c) coherence producer is built (D audit 2026-07-06): generic engine
  `S08.nonempty_coherent_SOf_bot_of_index_dvd` + S14 consumer
  `frobenius_typeI_coherent_of_cyclicQuotient`.  The earlier "9000 番台 claim" reminder is stale.
- ~~lane b: 構成的 Clifford~~ → **lane c に再配分済** (下記「HUB 再裁定」節、issue 9002 で lane c が claim)。
  lane b は Clifford を build しない (dup 回避)。

### 次: `frobenius_typeI_coherent_of_abelianKernel` (12.6 case b) 埋め — S14 witness の S07.Hypothesis 構成
refactor で `coherent_of_constant_degree` が witness Dade map で使えるように。残タスク = S14 witness
`Hypothesis L` から `S07.Hypothesis hyp.Sset hyp.A` を構成 + `coherent_of_constant_degree` 呼び出し:
- **在庫あり**: `tau_isometry_diff` (Dade support-isometry + equal-degree supported), `conjugate_closed`
  (`Sset_closedUnderConjugate` S14:208), `difference_image` (`dadeCharacterDifferenceImageOfDiff` S14:574),
  `difference_images_orthogonal` (`toOrthonormalImage_inner_eq_zero_across` 経由 S14:644), `Sset_vanishes_off_H`
  (S14:657 → hsuppdiff 素材)。
- **要 build (witness char body, deep)**: `no_real_characters`, `pairwise_orthogonal`, `hirr` (Ind_H^L θ
  irreducible for Frobenius abelian kernel), `hconst` (等次数 [L:H]), `hsuppdiff` (差 A(L)-supported)。
  Frobenius 群指標論 (Ind from abelian kernel = irreducible, 等次数) が中核。multi-turn 想定。
- [x] α/lane c: 着手前の open-9000 scan と再構築禁止 reminder は実施済み運用へ吸収
  (9002 claim + 9005/9013 で追跡、下記 HUB 再裁定で更新済み)。
- [x] ~~lane c: σ-theory-dual structural (S16:166/3431/3511) を lane d leaf cite で discharge~~
  — **撤回済**。lane c の file:line 検証が正しく、正しい後続は 9002 constructive Clifford と
  9013/S16 W-side assembly consume 路線。

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

## ✅ HUB 再裁定 (2026-07-02, cron tick) — σ-theory-dual guidance 撤回 + lane c に構成的 Clifford 再配分

**1. σ-theory-dual guidance を全面撤回。lane c が正しい。**
前 tick の「HUB→lane c 指示」#2 (S16:166/3431/3511 = lane d leaf cite で discharge 可、coherence 不要) は
**hub の誤り**。lane c の file:line 検証を hub が確認・支持: (a) lane d leaf は算術 **≤ bound**、目標は
(13.15) **等式** / (13.2.a) **cyclicity** で別物、(b) cite に未構築の faithful-fpf 構造 bridge (issue 9000 が
「lane a assembly 未完」と defer 済) 要、(c) cyclicity は typeP_Galois dichotomy 経由の深い char。
**根本原因 = hub が quick grep で v-value 公式を pattern-match し、算術 bound と char equality/cyclicity を
混同した** ([[verify-port-state-by-number-not-coq-name]] を両方向で = phantom "easy" も避ける、を hub 自身が
守れなかった)。cont.⁴²/⁴³「lane c frontier = coherence-gated deep char」が正しい。「idle 回避」の趣旨は
維持するが、その手段としての σ-theory-dual cite は不成立。**issue 4014 の lane d 再配分にもこの誤りを持ち込んで
いた** (S16:166 を lane c の ungated 例に挙げた) → 同様に撤回。

**2. lane c 次手 = (c) 再配分。構成的 Clifford (issue 0026) を lane b → lane c に移す。**
lane c の cluster (γ §14-16 deep char) は最下流ゆえ on-spine ungated work が枯渇 (lane d と同型の
cluster-off-spine、policy 7)。選択肢 (a) 待ちは STOP 条件 (a) 違反ゆえ不可。(b) の「lane b coherence と重複」は
policy 8 で回避すべき。⟹ **lane b の plate から構成的 Clifford (issue 0026、(B)) を lane c に移管**:
- **理由**: 構成的 Clifford (Ind_H^L θ 分解 = Isaacs 6.2/6.11 + Pf 1.7) は **coherence 非依存の generic
  char 補題** = lane c が今すぐ ungated で build 可。consumer は lane b (12.14 M-side) と lane c (deep char) の
  **両方** = genuine shared infra。lane b は (6.5.c)+(5.7)-S07 refactor に集中 (plate 過積載の是正)。
- lane c は **9000 番台で issue 0026 を claim** (subsume) → `OddOrder/GroupTheory/**` or Peterfalvi §1/§6
  shared leaf で build。lane b は cite。hub は step 1.6 で dup 監視。
- 加えて lane c は §14-16 assembly を signature-first で skeleton 前倒し可 (宣言済 signature がある範囲)。

**3. lane b への更新**: (B) 構成的 Clifford は lane c 担当に変更。lane b は (A)(A') = (6.5.c) + (5.7)-S07 に集中。

**やること 更新**:
- [x] σ-theory-dual guidance 撤回 (hub 誤り、lane c 正当)。
- [x] lane c: 構成的 Clifford を 9000 番台 claim → build (issue 9002 で claim 済、infra 進行中)。lane b は cite。
- [x] lane c: §14-16 assembly を signature-first で skeleton 前倒し済み。現在の正本は
  9013「S16 `nonexistence_of_G` top-level assembly 完了、残 8 sorry は lane-b §13/§15 gated」。
- [x] lane b: (6.5.c) + (5.7)-S07 refactor complete (Clifford は lane c へ移管)。
  (5.7)-S07 は完了済 (`d31b9763`)、(6.5.c) は
  `S08.nonempty_coherent_SOf_bot_of_index_dvd` / `S14.frobenius_typeI_coherent_of_cyclicQuotient`
  で landed。旧 "9000 番台 claim 未起票" reminder は stale。
- ~~lane c: σ-theory-dual structural (S16:166/3431/3511) を lane d leaf cite で discharge~~
  (**撤回済** — 上記「✅ HUB 再裁定」節参照。行のみ残存していたため 2026-07-02 に strike)

## ✅ HUB 追加裁定 (2026-07-02 全体レビュー) — γ (binding pole) coherence 供給の明示分担

docs/plan レビューで「lane c の記録上の gate = 『§7 coherence は lane b の build』だが、b の documented
scope は §12 向け ((6.5.c) + S07 generic) のみ」というスコープずれを検出。binding pole が誰も約束して
いない納品物を待つ構図を排除するため、供給を明示分割する:

- **lane b の納品物** = (6.5.c) coherence producer (**DONE**:
  `S08.nonempty_coherent_SOf_bot_of_index_dvd` + `S14.frobenius_typeI_coherent_of_cyclicQuotient`;
  旧 9000 番台 claim reminder は stale) + S07 generic producer 群 (lattice-relative refactor は
  完了済)。**γ cascade の M 向け char 入力は b の scope 外。**
- **lane c の担当** = 自所有 S15/S16 内の **η-grid honest 化 + M 向け `Hypothesis78`/Dade instantiation**
  (`exists_MHypothesis`/`betaM_expansion_data`/(14.11.4) norm 入力)。upstream-first でこれらを §14.11
  cascade より先に build し、b の generic producer は signature contract で cite (待たない)。旧 lane-h
  課題 (2026-06-22「真の long pole = S15 η-grid carrier の honest 化」) の後継 owner = **c**。
- 詳細・c_eq_one route 制約・S-side 処分は `notes/peterfalvi/s16_w4_char_cascade.md` の
  「✅ HUB 裁定 (2026-07-02 全体レビュー)」節 (lane c の live 正本) に転記済。


## ✅ HUB CLOSE (2026-07-08 監視 tick): 全裁定実行済

9001 HUB 裁定の全事項が実行完了:
- **事項1** ((12.6) `frobenius_typeI_coherent` の 3-case split soundness fix) = commit `ed34cdc8` で landing、case-b (abelianKernel)/case-c (cyclicQuotient) branch とも sorry-free。
- **事項2 (A/A')** coherence infra = lane b が S07 refactor + (6.5.c) producer で build、carve-out は merge_monitor 記録。
- **事項2 (B)** 構成的 Clifford = lane c へ再割当、専用 issue **9002** で完遂・closed。
- 誤 σ-theory-dual guidance = doc correction で撤回済。

近傍の唯一の残 sorry = case-(a) `sibleyTarget_frobI` ((6.8) target, S14_MaximalI:2770) は 9001 の deliverable でなく issue **2032** (closed) が tracked していた別 frontier。⟹ 9001 は pending action 無し。close。
