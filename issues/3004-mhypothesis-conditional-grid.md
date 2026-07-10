---
id: 3004
slug: mhypothesis-conditional-grid
title: "HUB: MHypothesis の e=pq / betaGrid hoist を (14.11.2) 条件付き producer へ戻す"
created: 2026-07-10
---

# HUB: MHypothesis の e=pq / betaGrid hoist を (14.11.2) 条件付き producer へ戻す

## 背景

lane c の次 frontier、exists_MHypothesis の M-side betaGrid mirror に着手する前に
Peterfalvi 原文・Coq・現 Lean carrier を照合したところ、現 MHypothesis が (14.11) の結論を
(14.10) の無条件 field へ hoistし、その結論を (14.11.1)--(14.11.4) 自身の証明で
再利用する循環が判明した。CLAUDE.md の unsound carrier / signature STOP に該当するため、
Lean 編集を開始せず本 issue で hub 裁定を要請する。

### 原文 / Coq の依存順

Peterfalvi references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd:

- line 81 の (14.10) Hypothesis は M, K=M_F, Mset, tau, tau1, psi, betaM のみを置く。
  e=pq も signed eta-grid expansion も (14.10) の data ではない。
- lines 83--99 の (14.11) は K=V と e=pq を結論する。K!=V を仮定し、(14.11.1) の
  strict gapsを得た後、(14.11.2) で初めて e=pq と signed expansionを同時に導く。
- Y=0 は独立 input ではない。axis parity、orthogonal split、Bessel/tight norm chainから
  e=pq、全 coefficient +/-1、Y=0 が同時に従う。

Coq coq/theories/PFsection14.v:

- lines 173--176 の FTtype2_support_coherence は二つの strict gapを引数に取り、
  e=p*q と signed expansionを同時に返す。
- lines 884--928 の defK contradiction内で gapを作った後、line 926で同 lemmaを呼ぶ。
  DbetaM は K!=V branch内にのみ存在する。

### 現 Lean の循環 / over-strong fields

OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean:

- MHypothesis.complement_card_eq_pq (lines 58--63) が e=pq を無条件 fieldとして carry。
- MHypothesis.betaSigns / betaSigns_pm / betaGrid (lines 80--93) が (14.11.2) の
  signed expansionを無条件 fieldとして carry。
- main_size_bounds_structural (lines 543--644) は (14.11.1) の途中で line 629 の
  complement_card_eq_pqを使用する。原文ではここは e<=pqだけを使い、equalityは次段で得る。
- betaM_expansion_data (lines 754--764) は hne : K!=V を使わず、無条件 fieldsをコピーする。
- betaM_expansion (lines 806--822) と K_eq_V_index_pq (lines 1105--1114) も
  e=pqを証明せず同 fieldを返す。

ComparingLM.lean:1353以降の betaGrid sorryは、この over-strong carrierを埋めようとして閉じない
endpointである。L-side engineを条件なしでmirrorすると循環を固定化する。

### lane b coordination: (13.19) carrier の型矛盾

OddOrder/Peterfalvi/S15_SAndT.lean の TypeIOrthogonalityGridData も原文と不整合:

- 原文 (13.19.b) は L^tau1 が eta-gridに直交する。
- 原文 (13.19.c) は inner(betaL^tau, eta_0j) が j!=0で一定で、case (c2) では odd。
- 現 betaL_eta_independent は全 i,j で同 inner=0 とする一方、同 structure の caseC は
  同じ innerが oddとなる枝を持つ。case (c2) 下で両立しない。
- betaLを実際の Dade imageへ同定する fieldもない。producerは現在 sorry。

この S15 block は lane b 所有なので、c が無断変更せず hub が owner / carve-outを裁定する。

## やること

- [ ] hub ruling: unsound/over-strong carrier と確認し、C/B の修正境界を裁定。
- [ ] MHypothesisを faithfulな (14.10) carrierへ戻し、complement_card_eq_pq,
      betaSigns, betaSigns_pm, betaGridを無条件 fieldsから外す。
- [ ] main_size_bounds_structuralを K!=V と e<=p*qから (14.11.1) を証明する形へ直す。
- [ ] (14.11.2) conditional producerを作り、K!=V + gaps + faithful (13.19.c) から
      e=pq、axis parity、coefficient rigidity、Y=0、signed expansionを同時に構成する。
- [ ] betaM_expansionをconditional producerへ再配線する。
- [ ] K_eq_V_index_pqのindex halfは K=Vを得た後、faithful (13.17.c) specializationから導く。
- [ ] lane b ownerの TypeIOrthogonalityGridDataを原文 (13.19) に restateし、
      zero-axis constancy / (c1)/(c2) と actual Dade imageを正確にcarryする。
- [ ] L/M grid consumersは修正後の conditional APIだけをciteする。

## 完了条件

- (14.10) carrierに (14.11) の結論が free fieldとして残っていない。
- betaM_expansionの hne が load-bearingで、e=pq / signed expansion / Y=0 が
  conditional proof chainから得られる。
- S15 (13.19) carrierに inner=0 と odd の矛盾が残っていない。
- lake build OddOrderとAxiomsCheckがgreen、新axiomなし、証明済みからのsorry regressionなし。
- 原文番号とCoq対応をdocstring / s16_nonexistence_gate_mapへ反映。

## 参照

- issues/3002-grid-property-carrier-enrichment.md
- issues/9077-lane-c-frontier-exhausted-reallocation.md
- notes/peterfalvi/s16_nonexistence_gate_map.md
- Peterfalvi (13.19), (14.10), (14.11.1)--(14.11.2)
- Coq PFsection13.v:1987-1993, PFsection14.v:173-251, PFsection14.v:884-928
