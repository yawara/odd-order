---
id: 116
slug: s15-normestimates-relayer
title: "HUB: S15 NormEstimates/CountingLayer の layer-inversion relayer (2035 #29 恒久解、hub architecture)"
created: 2026-07-14
---

# HUB: S15 NormEstimates/CountingLayer の layer-inversion relayer (2035 #29 恒久解、hub architecture)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 問題

S15_SAndT_Setup/{NormEstimates (2), CountingLayer (2)} + S15_SAndTBasic (1) の実 sorry 5 本は、
それぞれの honest producer (本日 landing 分含む: tSide_theta_package_of_not_caseB_core、
(13.2.b) card_Q_eq_qp、dadeHypT 等) が **import DAG 下流** (CaseACoherence → hub →
NormEstimates の層順) にあり、in-place 証明は不可能 (2035 #29 で b が確定済み、
2026-07-14 hub 監査 wf_525303b8 で再確認)。

## 恒久解 (hub architecture task)

S15↔S16 の layer inversion: 下流に落ちた producer 層 (TSideDegrees / CharacterDegreeSupply の
該当宣言) を NormEstimates より上流の位置へ再配置するか、sorry site 側を hypothesis-parameterize
して obtain-site を producer の下流へ移す (2035 #29 option A)。spine-file 再層化は
[[relayer-verify-with-build-not-bfs]] に従い edge ごとに build 検証 (BFS だけで判定しない)。

## トリガー

b の 2035 T-side campaign が (13.4)/(13.3) cluster を close した節目で hub が実施
(campaign 中の再層化は b の hottest file を動かすため衝突大)。

## 参照
- issue 2035 #29 / 0115 裁定 2 註 / merge_monitor tick 41

---

## 🧭 HUB RULING (2026-07-14 監視再開時) — 調査完了・設計確定・実施 sequencing

トリガー ((13.4)/(13.3) cluster close = 2035 #74 で θ-package 組立完了) 成立を受け、hub が
5-agent workflow (wf_746d2ebb) + 自前検証 (import-BFS / 実 cite grep / TTypeII 読解 / Coq 対照)
で全容を調査した。結果、**単純な「producer 上移 or 即時 threading」では済まない構造**が判明。
以下が確定 findings と実施計画。

### Finding 0 — scope 訂正 (site 台帳)

冒頭の「実 sorry 5 本」のうち **S15_SAndTBasic:841 `V_inf_centralizer_Q_eq_bot` は本 issue の
scope 外** — 9077 HUB RULING #3 (2026-07-14 夕) で lane c の proof-only carve-out に付与済み。
hub scope = **NormEstimates 2 (exists_muT_index :238 / exists_etaT_alphaFun_one_int :259) +
CountingLayer 2 (QD_sharp_centralizer_le_T :1615 / tSide_theta_package_of_not_caseB :1727)** +
同類の T_isTypeP2_gate (CDS:1052、下記 Finding 2)。
⚠ ただし c の V_inf discharge route (T_caseB_facts_unconditional + D_eq) は **DAG-blocked**
(9077 に別記) — 本 relayer の実施が c の unblock 前提になる。

### Finding 1 — 「NormEstimates を CDS の下へ沈める」は原理的に不可能 (hub 検証済)

一見きれいな解 (NormEstimates/OrderDetermination を供給層最下部へ沈めて CDS を import、
obtain-site を直 rewire、教科書順 (13.4)<(13.6-10) にも合致) は **cycle で成立しない**:

- `c_eq_one` (13.12、OrderDetermination) の証明は `analytic_inequality` (13.10、NormEstimates)
  を obtain する (OrderDetermination:855)。= OrderDetermination は NormEstimates の下に固定。
- mid-layer が `c_eq_one` を**実 cite** (docstring でなく proof): `SAndTDefs:214 C_eq_bot` /
  `BridgeCharacter:238 PW1_index_eq_u` / `:370 betaGrid_apply_one_eq_zero`;
  `BridgeCharacter:617 betaGrid_support` は `mu_row0_apply_eq_zero_of_mem_derived_not_mem_P`
  (OrderDetermination) を cite。= mid-layer 閉包は OrderDetermination (⊇ NormEstimates) を含む。
- τ₁T エンジン (TSetMemberRFamily → NuRowPin → Tau1T) は BridgeCharacter の上に構築されており、
  CDS 閉包 ∋ mid-layer ∋ hub ∋ NormEstimates。⟹ NormEstimates → CDS import = 即 cycle。

**根本原因 = τ₁T エンジン ((13.3.c)-T machinery) が (13.12)-consuming layer の下に居る file 配置**。
教科書順では (13.3) < (13.12) であり、この inversion が全 sorry site の共通因。

### Finding 2 — (14.9) knot: T_isTypeP2_gate は layer-inversion でなく**証明循環** (hub 検証済)

`T_isTypeP2` (TTypeII:900) の証明を hub が直接読解:
`T_isTypeP2 → T_side_caseB_facts (TTypeII:191) → T_caseB_facts_unconditional (CDS:2227) →
lambda_forces_T_caseB_core → tSide_theta_package_of_not_caseB_core → T_isTypeP2_gate (sorry)`。
⟹ gate を「T_isTypeP2 の cite」で discharge するのは**どう再配置しても証明循環**。さらに gate の
signature (`hG` のみ) は producer (hnoV + hncH0C refuter 要) より**真に強い** statement で、
循環を別にしても現形では discharge 不能。

**honest fix (b の math、hub 作業でない)**: θ-package/τ₁T machinery の `hT2 : IsTypeP2 hyp.T`
入力を、ungated に取れる type-P facts (IsTypeP via T_nonI / reconciled_typePData_T) へ**弱める**。
Coq 対照で裏付け: PFsection13 の section context は `of_typeP S U defW` + `FTtype ≠ 1, 5` のみで
**FTtype = 2 を仮定しない** (coq/theories/PFsection13.v:80,102-103; (13.4) は :866 で同 context の
まま証明)。TTypeII:188-190 の cycle-hazard 注記と同根の一般形。→ 2035 に b 宛で記録済。

### Finding 3 — 実施設計 (Route T = threading、2035 #29 option A の精密化)

Route E (τ₁T エンジンを (13.12) 層より上へ raise) は b のアーキテクチャ全体の組み換え = b 裁量。
hub が実施するのは **Route T**:

1. NormEstimates の (13.4)-triple obtain-sites 5 箇所 (:295 exists_caseB_data_eta10_T /
   :455 eta10_Qsharp_norm_lower / :493 analyticEstimate_lambda / :571 analyticEstimate_eta /
   :706 analyticCounting_disjointCover) + sorried atom 2 本を明示 hypothesis 引数化
   (explicit param + legacy wrapper、optParam 不可)。hQ 成分は `card_Q_eq_qp`
   (TSideDegrees:238、無条件 proven、acyclic import 可) で場内 discharge し、param は (hD, hv) に縮小。
2. threading: analytic chain → `analytic_inequality` → OrderDetermination 3 obtain-sites
   (numeric_bounds :518 / c_eq_one :844 / caseA_parameters :896) → c_eq_one の mid-layer
   consumer (C_eq_bot / U_inf_centralizer_P_eq_bot / BridgeCharacter 3 decl) → **新 leaf**
   (例 `S15_CaseBEndgameSupply.lean`、CDS を import — CDS 2239 行超過につき CDS へは足さない)
   で `T_caseB_facts_unconditional` cite により一括 discharge。
3. CountingLayer の legacy pair (`tSide_theta_package_of_not_caseB` + `lambda_forces_T_caseB`)
   は consumer 消滅 → **削除** (実 sorry −1、CountingLayer 2001→<2000 行で size flag も解消)。
   NormEstimates の sorried atom 2 本も削除し、内容は discharge leaf 側の precisely-named
   producer (muT-index / (13.5.a)-T integrality、τ₁T エンジン到達可能層) へ移す (b が後日実証明)。
4. `QD_sharp_centralizer_le_T` は両層で真に必要 (CDS:1107/:2189 が cite) ⟹ hT2 (弱化後の型) で
   parameterize + HonestTypeP2A0 の TypePData-generic 2 補題 (conjClassSetIn_typePV_centralizer_le_M
   :165 / escaping_honestTypeP2A0Set_eq_empty :203) の SubcoherenceInputs 相方への上移で in-place
   discharge 可能化 — 残る本質は **(QD)^# ⊆ A₀(T) membership 補題 (未存在、genuine math = b)**。

### 実施 sequencing (コスト理由でなく設計依存の順序)

**(i) b の hT2 弱化裁定が先** — threading で流すパラメータの型 (IsTypeP2 か TypePData 束か) が
それで決まる。先に threading すると署名を二度組み替える。
**(ii) a の OrderDetermination active cluster との衝突回避** — threading は numeric_bounds /
c_eq_one / caseA_parameters (= a が (13.11)-(13.13) を直近 3 tick で landed、(13.15) 進行中) の
signature を編集する。本 issue のトリガー節が b に適用したのと同じ anti-collision 原則を a に適用
し、**a の同 cluster close (または quiet 化) + (i) の解決を新トリガー**とする。
それまでの hub 作業 = 監視 tick で両条件を追跡し、成立 tick で Route T を実施。

### size flags (関連)

CountingLayer 2001 行 (Route T step 3 で解消) / **CDS 2239 行 (b 分割要 — 2035 に記録)** /
NuRowPin 1261 行 (watch 継続)。
