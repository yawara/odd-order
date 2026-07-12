---
id: 9092
slug: s-instance-mu-grounding
title: "S-instance (9.11) R-family gate: mu-grid to certain-type grounding を Hypothesis field 化 (spine producer 放電、cross-lane)"
created: 2026-07-13
---

# S-instance (9.11) R-family gate: mu-grid to certain-type grounding を Hypothesis field 化 (spine producer 放電、cross-lane)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景 (lane-b /loop 2026-07-13、S-instance (9.11) campaign の cross-lane gate)

lane-b の S-instance Pf (9.11) coherence campaign (issue 1017) が caseB を concrete residual まで
decompose した後、subagent 精査 (exhaustive) で **単一の cross-lane block** に収束:

`sSet_coherent_indS_{caseA,caseB}` (HypothesisBasics:569/948/972) の残 = **reducible-μ_j R-family**
(`sSet_caseB_memberRFamily` の reducible 枝)。これを閉じるには「**reducible η ∈ sSet はどの column か**」の
dispatch = **reverse dichotomy** が要る:
```
∀ reducible η ∈ sSet, ∃ j ≠ 0, η = ∑_i hyp.mu i j
```
(等価: `mu_isColumnFamily : ∀ i j, hyp.mu i j = (someHyp46.columnFamily (χ₂ j)).mu i`)。

## なぜ cross-lane (b 単独不可)

- `Hypothesis.mu` は **abstract structure field** (SubcoherenceInputs:173)。grounding lemma 群
  (`mu_orthonormal`/`mu_diff_support`/`mu_conj`…) は grid を特徴づけるが **certain-type residue grid と
  同一視しない**。→ abstract Hypothesis 内で reverse dichotomy は証明不能。
- 真の identity は **spine producer `FeitThompson.lean:1392`** で成立: `mu := Section16CharacterData.muS`、
  `muS := (certainTypeS.columnFamily χ₂).mu` (FeitThompson:154) → そこでは **near-definitional**
  (`prTIres_irr_cases` = Coq S1cases、9014 で reachable)。だが abstract Hypothesis からは invisible。
- **counting route も b 単独不可** (verify 済): reducible count `reducible_count_sOf_H0C` は lane-a
  `S12_TypeIICrossIsometryPair.lean` 在住、`mu_colSum` の injectivity/distinctness (b) 不在。
- M-side には `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` (S12_HcBound:578) が htype/chief
  machinery 経由で存在するが S-side は未接続。

## やること (cross-lane、hub 調整要)

- [ ] **S15 `Hypothesis` に field 追加** (b): `mu_isColumnFamily` (or reverse dichotomy)。
- [ ] **全 producer で放電**: `FeitThompson.lean:1392`(+1556/1686) = **lane-a/spine、near-definitional**
      (`muS := columnFamily.mu` + `prTIres_irr_cases`) / `HypothesisSwap` producer = **b**。
      ⚠ field を追加して producer 未放電だと build 破壊 → **全 producer 同時放電が必須** (coordinated commit)。
- [ ] ⟹ b が reducible R-family を閉じる (route A = `certainTypeR` @ `hyp46S` / route B = b-buildable
      Dade→η formula `dadeHypS(μ_j−μ̄_j)=∑η-columns`) + `_orthogonal` を `eta_orthonormal` から。

## 完了条件

`sSet_coherent_indS_{caseA,caseB}` (⟹ `coherent_H0Cprime_S`) が dadeHypS 継承のみで honest 化
→ `character_degree_analysis` (13.3) unblock → §13 char cascade 全体が sound な (9.11) 基盤上に。

## hub への依頼

`FeitThompson.lean` は lane-a/spine 所有 (carrier field 追加は hub/issue 承認要、CLAUDE.md)。
**hub 裁定要**: (a) b に FeitThompson producer の当該 field 放電行の carve-out 付与 (near-definitional
ゆえ b が書ける) か、(b) lane-a が放電。b は S15 field 追加 + b-owned producer 放電 + R-family closing を担当。
near-definitional ゆえ低リスク。impact 大 (char cascade 全体の sound gate)。

## 参照

issue 1017 (S-instance (9.11) campaign)、2038 (b frontier)、9014 (prTIres_irr_cases/S1cases)、
9090 (M-instance (9.11) coordination)。FeitThompson.lean:154/1392、S12_HcBound:578 (M-side template)。
