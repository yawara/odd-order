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
