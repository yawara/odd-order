---
id: 9096
slug: b-frontier-gated-direction
title: "b: S15-solo 9094 完了 (S-side hbridge closed) — 残 T-side/NormEstimates は cross-lane gated、direction 要"
created: 2026-07-14
type: HUB direction 依頼 (lane b frontier gated)
---

# b の S15-solo 9094 frontier が gated — hub direction 依頼

## 状況: b の 9094/2035 char-degree campaign の S15-solo genuine math は完了

**S-side (13.3.b) forward gate `S_caseB_facts_no_lambda` を完全証明** (hbridge closed、commit
a8b777b6、詳細 = issue 2035 #33/#35):
- caseA (`lambdaWitness_of_caseA`、regular-seed witness) + caseB
  (`lambdaWitness_of_caseB_member` via 新 S11 `caseB_xiOf_H0Cprime_eq_induce_hcPsiPair` = pair 版
  Clifford correspondence) 両方 genuine 証明。#print axioms sorryAx なし。
- `lambdaCluster_or_caseB` dichotomy の S-side が honest 化。
- 併せて: TTypeII cross-lane 移行 (overstatement 除去) + dichotomy keystone + translation API 抽出。

## 残る 9094 gate は全て cross-lane gated (b-solo S15 では close 不能)

精査確定 (issue 2035 #29/#36):

1. **`tSide_theta_package_of_not_caseB_core`** (ν-gated (13.4) T-package) と
   **`deltaPrime_eq_one_T`** (ν-gated (13.3.c) T-side): **a-owned ν-carrier** (`nuGridSupply` /
   `NuGridSupplyData`、FeitThompson{,Setup}.lean) 依存。discharge = 「hyp.nu ↔ certainTypeT grid
   同定 + muS_* T-instance readout」で a-territory (FeitThompson.lean 編集要)。

2. **`T_caseB_facts_no_lambda`** (no-λ T-mirror): **S16-gated**。T-side D/v/Galois machinery
   (`v_eq_one_twenty_one_of_caseB` 等) は S16_NonExistenceG/** (S15 の下流)、`q < p` は S16
   Hypothesis の field (S15 に無し)。S15 から到達不可。de-opacify も forward-reference で不適
   (S_caseB_facts_no_lambda が後方定義、reorder churn 過大)。

3. **NormEstimates 5 obtain-site 移行** (§13 analytic overstatement 除去、issue 2035 #29):
   honest producer (S15_CharacterDegreeSupply) が NormEstimates の**下流** (import DAG)。
   relayer に要する S15→S16 inversion `CoherenceEtaOrthogonality → S16_GridExpansion` は
   **genuine** (2 lemma 使用) かつ **S16_GridExpansion = c-owned**。cross-lane relayer。

## A-lane ν-carrier audit (2026-07-14)

### Canonical grid package は着地

`OddOrder/FeitThompsonNuGrid.lean` に、`mp.certainTypeT` から作る canonical `nuT` について
`NuGridSupplyData` の**純粋な grid field 全部**を証明した。具体的には irreducibility、
row injectivity、orthonormality、degree congruence、base sign、row-sum induction、reverse
dichotomy、(4.8) support、(4.3.c) value、(4.9.a) conjugation である。各 theorem の
`#print axioms` は `[propext, Classical.choice, Quot.sound]` のみ。関連 commits:
`bb959962`, `83d63b79`, `d0d3e9ca`, `6e106fdd`, `9d221886`。

### 現行 `NuGridSupplyData` は二つの独立理由で generic producer にできない

1. **generic `hyp.nu` の row-translation gap**: `Hypothesis.nu_definition` は各 row の差だけを
   拘束する。各 row に任意の class function を一様加算しても保存されるため、generic
   `hyp : Hypothesis G` から `nu_irreducible` 等は導けない。canonical `nuT` との同定を
   carrier 契約に明示する必要がある。
2. **`V_commutative` は grid fact ではなく post-(14.9) fact**: canonical `V` は `T_F` の
   `T'` 内補群であり、一般の type-P datumでは nilpotent までしか得られない。既存の正しい
   theorem `S15.isMulCommutative_V` も `IsTypeII T`（(14.9)）を要求する。現行
   `Hypothesis.swap` はすでに `hT2 : IsTypeP2 T` を引数に取る一方、前段の
   `NuGridSupplyData` が `V_commutative` を無条件 field に混在させている。さらに現行
   `S16.T_typeII` / `T_isTypeP2` は `sorryAx` を継承し、その前段には
   `T_side_caseB_facts` があるため、これを A 側 producer から cite して field を埋めるのは
   (13.4)→(14.9) の循環を隠すだけである。

したがって cross-lane API 修正は、(a) canonical grid facts を canonical `nuT` 同定付きで
thread し、(b) `V_commutative` をその bundle から分離して `Hypothesis.swap` の既存 `hT2`
以後に供給する、という依存順を保存する必要がある。A lane は b-owned
`HypothesisSwap.lean` の signature を無断変更しない。

## direction 依頼 (hub 裁定)

b の S15-solo char-degree frontier は上記の通り cross-lane gated。次の b work の方向を依頼:

- **(A)** a-lane の ν-carrier (nuGridSupply discharge) を優先させ、b は un-gate 波及を待って
  T-side (13.3) を再開 (tSide_theta_package + deltaPrime_T + 以後の T-side dichotomy)。
- **(B)** b に ν-carrier discharge の carve-out (FeitThompson.lean proof-only) を付与し b が build。
- **(C)** NormEstimates relayer を c と coordinate (S16_GridExpansion の grid lemma を
  CoherenceEtaOrthogonality が要する分だけ S15 へ移す/再配線)。cross-lane、規模大。
- **(D)** b を別クラスタへ reallocation (char-degree S-side 完了ゆえ)。
- **(E)** b-solo prerequisite として T-instance hbridge (S-side の T-analog、S11 char theory、
  ungated だが payoff は上記 gate 依存で deferred/speculative) を build させる。

b 推奨 = 特になし (どれも cross-lane 調整 or a-lane 進捗待ち)。hub の cross-lane 視点で裁定を。
b は待機中 re-assess を continue (a-ν landing で un-gate 波及を検出したら T-side 再開)。

## 参照
- issue 2035 (#33/#35/#36)、issue 9094 (RULING)、commit a8b777b6 (hbridge closed)
