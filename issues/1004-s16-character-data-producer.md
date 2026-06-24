---
id: 1004
slug: s16-character-data-producer
title: "Section16Inputs: section16CharacterData producer (Pf §13, lane-b)"
created: 2026-06-18
---

# Section16Inputs: section16CharacterData producer (Pf §13, lane-b)

## 背景

2026-06-18 post-§14 監査で判明した真の long pole = `Section16Inputs` producer の分配
(skeleton commit `80f9aa39`)。本 issue は **character 側 (Peterfalvi §13 coherent Dade grid)**
担当ブロック。これが lane-b の (6.8) coherence が最終的に payoff する地点
([[ft-path-policy]] の "deferred-payoff prerequisite") = (6.8) は orphaned ではなく本 producer
の上流前提。**当面は deferred** ((6.8) capstone と Pf §10-13 char API が landing するまで埋められない)。

## やること

- [ ] `section16CharacterData_of_isMinimalSimpleOdd hG mp tp : Section16CharacterData mp tp`
      (`OddOrder/FeitThompson.lean:280`, 現 `sorry`) を実証明化する。
- [ ] 入力 = 極大対 `mp` + 型 P 構造 `tp` (lane-g/lane-f が構成)。
- [ ] 内容 = Dade 指標 grid: `Sset`/`Tset`/`A0S`/`A0T`、`tauS`/`tauT`/`tau3`
      (`IntegralCharacterMap`)、`omega`/`mu`/`nu` grid (`Fin tp.q → Fin tp.p → ClassFunction …`)、
      符号 `delta`/`deltaPrime`、誘導恒等式 `mu_definition`/`nu_definition` (Pf (13.1.d/e))。
- [ ] feeder = Peterfalvi §13 coherent set theory ← (6.8) coherence
      (`S08_CoherenceTheorems.lean:59` `sibleySetup_is_coherent`) + Pf §3-9 char API + §10-13。

## 完了条件

`section16CharacterData_of_isMinimalSimpleOdd` の `sorry` が消え、`lake build OddOrder` 緑。
(深い character theory 依存ゆえ最後発の見込み。)

## 進捗 (2026-06-23) — feasibility 確立、char 理論 in-stock (de-risk)

cd producer を精査し **feasible・全 character 理論 in-stock** と確定 (「deep, last, gated」評価は誤り)。
正本 = `notes/peterfalvi/s12_s10_character_bridge.md` 更新¹⁵。要点:

- **cd の唯一の実 obligation = (13.1.e) `mu_definition`/`nu_definition`** (Explore + 原文 04.15)。`S16.Hypothesis
  = S15.Hypothesis + (q<p)`、grid への Prop 制約は (13.1.e) + `eta_eq_tau_omega` (済) のみ。深い性質は下流
  `BasicStructureData`/`CharacterDegreeData` に defer。
- **(13.1.e) 数学 in-stock**: `S06.induce_omegaColumnDiff_mu_diff` (proven) + 本セッション landed
  `S06.induce_chiColumn_diff_mu_diff` (grid-difference 形式 `Ind_W^S(ω−ω₀)=δ(μ−μ₀)`, axiom-clean) = cd の
  `mu_definition` が literal に cite する形。
- **omega は W に intrinsic** (`linearIrreducibleCharacter χ`) ⟹ S/T 両 side が同一 omega 共有 (agreement 不要)。
- **type-II OK**: `typePData_toS06Hypothesis` は `TypePData` のみ要求 (type III/IV/V 不要)。
- **構築レシピ**: 各 L∈{S,T} で `typePData_of_isTypeNonI`→`typePData_toS06Hypothesis`→chiColumn/columnFamily で
  grid → (13.1.e) を `induce_chiColumn_diff_mu_diff` で discharge。Sset=`inducedFamily`、A0=`supportInSubgroup`。
- **残 residual = structural transport** (新 char 理論でない): ① **tp.W (=`mp.S⊓mp.T`, tp.W1=mp.K) と certain-type
  W (`data_L.W`) の cross-construction 同定** (crux、HUB/lane-f と相談候補)、② Fintype 決定性ゆえ cd は
  certain-type 級で組む (Hypothesis-level muGrid 経由は Fintype binder desync で破綻)。~300-500 行 transport。

## 参照

- skeleton commit `80f9aa39`、`OddOrder/FeitThompson.lean:259` (`structure Section16CharacterData mp tp`),
  `:567` (producer、唯一の実 sorry)
- (13.1.e): `S06.induce_chiColumn_diff_mu_diff` (NEW) / `S06.induce_omegaColumnDiff_mu_diff`
- 構築入口: `typePData_toS06Hypothesis` (`S12:660`), `typePData_of_isTypeNonI`, `Hypothesis.muGrid`/`chiColumn`
- 上流前提: (6.8) `sibleySetup_is_coherent` (DONE)
- 関連: 8014 (maximalPair✅) / 7005 (typeP_structure✅) / 2009 (POLE-2)

## 進捗 (2026-06-23, lane-b 再開²) — HUB 1011 解決 + grid=real 確定 + 完全攻略計画

正本 = `notes/peterfalvi/s12_s10_character_bridge.md` 更新¹⁷。要点:

1. **✅ HUB 1011 (cd-grid индexing gate) を lemma で解決** (commit `c7bfe4a0`, build-green, 全 full build 3881 green):
   `Section16TypePStructure.W1_eq_K`/`.W2_eq_Kstar`/`.W_eq_kappa_join` (任意 tp、producer reduction 不要、
   cyclic-subgroup uniqueness)。cross-lane field-add は不要 (issue 1011 更新済 `e04b055e`)。
   cd は `tp.W1_eq_K hG` cite で grid を mp.K に align 可能に。

2. **⚠ 確定: cd grid は real character 必須** (formal grid 不可)。`hyp.base.eta`(=tau3∘omega) が
   S16_NonExistenceG で `OddIntegerInner betaL (eta_{0j})` として consume され、これは `typeI_orthogonality_dichotomy`
   (S15 現 sorry) 由来。lane-h が将来この sorry を埋める際 η が real でないと証明不能 ⟹ formal grid は POLE-2 を
   unfulfillable 化 ([[scaffold-sorry-free-not-done]])。∴ real certain-type grid を組む。

3. **完全攻略計画** (材料全 in-stock、多セッション): omega=certainTypeS.chiColumn transport / mu=columnFamily.mu /
   delta=.sign / nu=certainTypeT (crux=S/T-shared-omega 同定) / mu_def/nu_def=induce_chiColumn_diff_mu_diff transport /
   tau3=`TICyclicHypothesis.sigmaIntegral` of a W-in-G TICyclicHypothesis (real Dade、要§5/§13 TI-cyclic 構成) /
   tauS/tauT/Sset/A0S=free field (§7 Dade / inducedFamily / supportInSubgroup)。
   着手順: S-side (omega+mu+mu_def, χ₂(j) enumeration 要) → S/T-shared-omega (最難) → tau3 → free field → pack。

## 進捗 (2026-06-23, lane-b 再開³) — ✅ S-side grid + mu_definition COMPLETE (commit `a22c7364`)

完全攻略計画 **piece 1+2+4 (S-side) 全実装**。2 つの実 Prop obligation のうち **harder な S-side
`mu_definition` を sorry-free + axiom-clean で landing**。正本 = `notes/.../s12_s10_character_bridge.md` 更新¹⁸。

- landed (全 `FeitThompson.lean` `namespace Section16CharacterData`、AxiomsCheck 3 本登録、build 3881 green):
  `induce_compHom_subgroupCongr` (reusable transport primitive、`subst;rfl`)、`certainTypeS_W1_eq`/`_W2_eq`、
  `kstar_le_S`、`cardCertainTypeS_W1/_W2`、`eqQ`/`chi2enum`、`tpW_subgroupOf_eq`、`gridEquivE`、
  `omegaS`/`muS`/`deltaS`、**`muS_definition`** (= cd `mu_definition` field、S-side)。FeitThompson が
  `import S06_MuColumnBridge` 追加。
- **producer の sorry は不変** (building-block landing; FT-path sorry 不変、進捗は実質的証明で測る)。
- **残**: piece 3 nu_definition (T-side、S/T-shared-omega = 最難) / piece 5 tau3 / piece 6-7 free field / piece 8 pack。
  S-side machinery は対称ゆえ T-side で大半再利用可。engineering 教訓 (instance-desync は `exact` で締める 等) =
  更新¹⁸ に記録。

## 進捗 (2026-06-23, lane-b 再開⁴) — piece 3 (nu/symmetry) transport infra + 攻略計画結晶化 (commit `93e02353`)

piece 3 (最難所、S/T-shared-ω symmetry) の transport foundation を sorry-free + axiom-clean で landing。
正本 = `notes/.../s12_s10_character_bridge.md` 更新¹⁹。

- landed (4 補題、AxiomsCheck 登録、build 3869 green): `monoidHom_eq_of_eqOn_W1_W2` (generating-set 原理:
  ↥tp.W linear char は W1/W2 restriction で決まる) / `gridEquivE_coe` (G-元保存 linchpin) /
  `gridEquivE_mem_W1`/`_W2` (K/Kstar → certainTypeS.W1/W2 transport)。
- 重複削除: 自作 cleanup lemma は既存 `ClassFunction.compHom_linearIrreducibleCharacter` と同一 → cite。
- **🔑 攻略計画結晶化** (更新¹⁹ step A-F): omegaT の K/Kstar 指標を **omegaS restriction から抽出して T へ push**
  すれば `omegaS=omegaT` が construction で従い **enumeration matching 不要**。step A chi2enum base-fix →
  step B omegaProdChar restriction 値 → step D T-side mirror → step C/E symmetry → step F nu (muS_definition mirror)。
- producer の sorry 不変 (building block)。残 = piece 3 残 (step A-F) / piece 5 tau3 / piece 6-8。

## 進捗 (2026-06-23, lane-b 再開⁵) — ✅✅ cd `nu_definition` COMPLETE (piece 3 全達成)

更新¹⁹ 攻略計画 (step A→D→C/E→F) を全実行し **`nu_definition` を sorry-free + axiom-clean で landing**
(commits `33b85dfb` step A+D / `b4775e75` T-side step B / `c3c9875f` 本体)。正本 =
`notes/peterfalvi/s12_s10_character_bridge.md` 更新²⁰。**⟹ cd producer の 2 実 Prop obligation
(`mu_definition`=更新¹⁸ / `nu_definition`=本回) が両方 complete。**

- 核心 = G-元保存 equiv `eTS` で S-side index 指標を T-side へ transport → `omegaS = omegaT` が construction
  から従い enumeration-matching 不要 (`omegaProdChar_comp_subtype` 在庫が reconstruction を供給、subgroup-image
  plumbing 回避)。`omegaS_eq_omegaT` (symmetry crux) → `nuT_definition` (muS_definition 完全 mirror)。
- AxiomsCheck 17 本登録 (chi2enum_zero / T-mirror 9 本 / omegaProdCharT 2 本 / symmetry 7 本)、full build
  3883 green、producer の sorry 不変 (building block)。
- **残 cd piece**: 5=`tau3` (W=S∩T の G 内 TI-cyclic + sigmaIntegral, real η) / 6-7=free field
  (tauS,tauT,Sset,Tset,A0S,A0T) / 8=pack (producer の sorry 解消)。grid (omega/mu/nu/delta/deltaPrime/両恒等式) 完備。
