---
id: 8022
slug: typeI-cover-reroute-to-mtilde
title: "type-I cover を kernel-cover から M̃-cover へ re-route (gate-2 faithful 化、cross-lane)"
created: 2026-06-30
---

# type-I cover を kernel-cover から M̃-cover へ re-route (gate-2 faithful 化、cross-lane)

## 背景 (ユーザー裁定 2026-06-30, lane d /loop⁴⁸)

gate-2 (`bgTheoremE_cover_data` S10:664 の covering disjunction) を lane-d が 2 iteration 精査し、
従来の **kernel-cover** ルート (`cover_subset_kernels` / consumer `TypeICovering.covers`) が
**M_σ-TI for type-I** を要すること、これが (i) deep (BG D(2) は cyclic 止まり)、(ii) **overstatement の
可能性大** (Coq `mFT_partition`/Peterfalvi 実 Dade support は **thickened M̃-cover** で kernel-cover でない)
と確定 (正本=issue 8020)。**ユーザーは faithful な M̃-cover への re-route を裁可** (/loop⁴⁸ AskUserQuestion)。

## ✅ lane-d 側の数学は完了済 (sorry-free、本 issue の土台)

M̃-cover route が必要とする群論はすべて lane-d が既に proven (S14_TypePCounting、全 sorry-free):
- **`exists_mem_conjClassSet_Mtilde_of_ne_one`** (S14:5421): all-type-F で ∀g≠1, ∃M maximal,
  `g ∈ 𝒞_G(M̃_M)` (BG Lemma 14.6 = `sigma_decomposition_dichotomy` の signalizer branch;
  κ-branch は `IsTypeF`⟹κ=∅ で vacuous)。
- **`sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`** (S14:8129): 完全な cover 等式
  `sharpSubgroup ⊤ = ⋃_{M∈maximal} 𝒞_G(M̃_M)` (= `cover_nonidentity` の本体)。
- `one_not_mem_Mtilde` (S14:8102, ⊇)、`conjClassSet_Mtilde_disjoint` (pairwise)。

∴ **gate-2 の TypeICovering branch の `cover_nonidentity` + `pairwise_disjoint_thickened` は供給可能**。

## ✅ 実行体制 (ユーザー裁定 2026-06-30 hub session): lane d に cross-lane carve-out

S10+S09+S14_MaximalI を build-green に一括必要な coupled 改修ゆえ、独立並行不可。**lane d が全体を
1 つの atomic 変更 (専用 branch) として実装** → hub が一括合流。
- **lane d に一時 cross-lane carve-out 付与** (merge_monitor.md 🔀 ブロック): d が S09
  (FrobeniusFamily/FamilyHypothesis71/G0) + S14_MaximalI (`not_all_maximal_typeI`/`covers`) を
  8022 の一環として編集してよい (逸脱としない)。
- **a/b/c への要請**: 8022 land まで S09 FrobeniusFamily/FamilyHypothesis71・S14_MaximalI
  `not_all_maximal_typeI` 周辺の編集を避ける (d の atomic 変更との衝突回避)。各 lane の他フロンティアは継続可。
- hub: d の atomic diff (S09/S14/S10 含む大型) を build-green + sorry/axiom 検証して一括合流。land 後に
  carve-out 解除 + a/b/c へ解除通知。

## やること (cross-lane re-route、coupled = build-green に一括必要)

1. **S10 (`BGTheoremETypeICovering`, lane-d carve-out 8086)**: `cover_subset_kernels` field を
   **削除** (kernel-inclusion は M_σ-TI 依存で faithful でない)。`cover_nonidentity`/`pairwise_disjoint_thickened`
   は残す。`bgTheoremE_cover_data` の type-F branch を `sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`
   (union-over-maximals → union-over-reps に `Mtilde_conj_smul` で変換) で組む。
2. **S09 (`FrobeniusFamily`/`FamilyHypothesis71`, lane-a/c 所有)**: 現 family の `dadeSupport_i =
   𝒞_G((M_i)_F#)` (kernel sharp、H(a)=1) を **M̃ ベース** (`dadeSupport_i = 𝒞_G(M̃_i)`、H(a)=R(a) signalizer)
   に再構成。Peterfalvi 実 Dade support `A~(M)=⋃_{a∈A1}class_support(R(a)·a)` に忠実化。**最も substantial な
   piece** (Dade hypothesis の H(a) を signalizer R(a) で与える)。
3. **S14_MaximalI (`exists_typeICovering`/`TypeICovering`/`not_all_maximal_typeI`, lane-b/c 所有)**:
   `covers` field を M̃-cover (`sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`) から discharge。
   `not_all_maximal_typeI` の `F.G0={1}` 証明を M̃-cover で出す (G0 が M̃-dadeSupport で定義される前提)。

## 完了条件

`bgTheoremE_cover_data` (S10:664) が M̃-cover route で sorry-free 化 (TypeICovering branch; NonTypeICovering
branch は別途) し、`cover_subset_kernels`/M_σ-TI を経由せず consumer chain (→ `not_all_maximal_typeI` →
`theorem88_caseB_holds` → FT spine) が green。

## 🔴🔴 重大訂正 (lane d, 2026-06-30 /loop⁴⁸ 後半): 「M̃-cover で plumbing だけ」は **私の誤り** — 2 構造の混同

S09 を精読し、**iteration 3 の「lane-d 数学完了、残は plumbing」評価が誤り**と判明。S09 には **2 つの別構造**:
- **`FrobeniusFamily`** (S09:4242): `G0 = {x|∀i, x∉kernelSpread i}`、`kernelSpread i = {x|∃g, gxg⁻¹∈(H_i)#}`
  = **kernel 共役ベース**。contradiction = `not_trivial_G0` ((7.10)-(7.11))。
- **`FamilyHypothesis71`** (S09:632): `G0 = {g|∀i, g∉dadeSupport_i}` = **dadeSupport ベース**。
  contradiction = `family_inequality` ((7.4)-(7.5))。

**現 consumer `not_all_maximal_typeI` (S14_MaximalI:2787) は `FrobeniusFamily.G0` (kernel-based) を使う**
(私は iteration 3 で `FamilyHypothesis71.G0` (dadeSupport) と混同した)。∴:
- **kernel-cover (`cov.covers`, M_σ-TI) が genuinely 必要**。proven M̃-cover (`sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`)
  は **M̃ ⊇ kernel# ゆえ weaker**で、kernel-based G0={1} を **discharge しない**。「lane-d 数学完了」は誤評価。
- **re-route の実体**: consumer を `FamilyHypothesis71` (dadeSupport=M̃) ベースに **作り直す** = `A_i=M̃-support` +
  `IsDadeIsometry` + `pairwise_disjoint` の **§8 Dade hypothesis 構成** が要る (Peterfalvi §8 本体、substantial)。
  `family_inequality` は既存ゆえ contradiction 部は再利用可だが、**M̃-Dade hypothesis の構成が deep**。
  「simple field swap / plumbing」ではない (私の誤った framing)。

**∴ gate-2 は両 route とも substantial**: (A) **kernel route** = M_σ-TI for type-I (BG §14 escape-impossibility、
deep、escape が起きれば false) / (B) **M̃ route** = §8 Dade hypothesis for M̃ 構成 + `family_inequality`
(faithful だが Peterfalvi §8 substantial)。**ユーザーの re-route 裁可は私の「plumbing」誤評価に基づく** ゆえ
再判断要。M̃-Dade hypothesis (`FT_Dade_support`/`DadeSupportHypothesisData`) の既存度を要確認。

## 参照

- 正本分析 = issue 8020 (gate-2 reduction 訂正、M_σ-TI/τ2-route 無効)。
- proven lane-d 補題 = S14:5421 / S14:8129 / S14:8102 (M̃-cover、但し kernel-based consumer を discharge せず)。
- consumer = `not_all_maximal_typeI` (S14_MaximalI:2787)、`FrobeniusFamily.G0` (S09:4273, **kernel-based**)。
- 別構造 = `FamilyHypothesis71.G0` (S09:660, dadeSupport-based) + `family_inequality`。
- [[scaffold-sorry-free-not-done]] [[gate2-typeF-tau2-reduction-is-false]]

## 🧾 状態整理 (2026-07-02 hub、lane d 退役後 — issue は OPEN 維持)

- **一時 cross-lane carve-out (lane d への S09/S14_MaximalI 編集権) は lane d 退役で失効**。
  merge_monitor.md の 🔀 block は除去済。a/b/c への「S09 FrobeniusFamily / S14 `not_all_maximal_typeI`
  周辺の編集を避ける」要請も**解除** (atomic 変更の主体が退役したため)。
- lane d の prep は landed 済・有効: M̃-cover 補題群 (S14_TypePCounting) / `familyHyp71_*` G₀={1}
  helpers (S10) / NonTypeICovering 分岐 sorry-free 化。
- **残タスク (route B) の owner 更新 (3 レーン)**: per-rep §8 Dade hypothesis
  (`dadeSupportHypotheses_typeI` 8.15, S10:556) は **issue 0096 carve-out で lane b** (consumer =
  b の `not_all_maximal_typeI` → `theorem88_caseB_holds` chain)。char 入力 (~30、§7-9 coherence/
  chiRho) は S09 既存機構 (lane a) + coherence infra (lane b) を cite。
(2026-07-02 hub、ユーザー委任レビュー)

## 🚧 route B は lane-a/c の §8 Dade work に block (lane d /loop⁵³ 確定)

route B の FamilyHypothesis71 assembly は **per-rep の §8 Dade 入力**を要し、全て lane-a/c の §8 領域:
- `dadeSupportHypotheses_typeI` (8.15, S10:467, **sorry**) — type-I の Dade hypothesis 構成 (§8 Dade isometry)。
- `fullDadeIsometryData` (Dade map τ + IsDadeMap/IsDadeIsometry) — §8。
- `HConjInvariant` (S04:492) — `HConjInvariant.of_forall_H_eq_bot` は type-I (H=R(x)≠⊥) に不適用ゆえ別途要 §8 証明。

⟹ **lane-d は route B を build-green に単独で進められない** (foundation が §8 character theory = lane-a/c)。
lane-d の lane-d-doable 貢献 = **assembly skeleton (gated-endpoint pattern)**: `not_all_maximal_typeI` の
M̃-cover 版を、per-rep の §8 Dade hypothesis を**名前付き仮説 (input)** に取って組む engine を作り、
M̃-cover (`sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`, lane-d 既証) + `family_inequality`
(既存) で contradiction を出す。§8 入力は cite (lane-a/c が後で充足)。これで route B の §8 residual を
named inputs に結晶化し、kernel-cover/M_σ-TI (possibly false) 依存を除去。

**hub 要請**: 8.15 (`dadeSupportHypotheses_typeI`) + type-I Dade isometry/HConjInvariant は §8 ゆえ
lane-a/c 協調が要る。lane-d は assembly skeleton を先行実装可 (次 /loop)。

## ✅ NonTypeICovering 分岐 COMPLETE (lane d, 2026-06-30, fix-W + producer)

`bgTheoremE_cover_data` の (8.8) dichotomy を **𝓜_P で case 分け**し、**𝓜_P≠∅ 側を完全証明**した
(全 sorry-free, full build 3889 green / AxiomsCheck OK):

- **fix-W 完成** (S14, 7 補題): `zTilde_comm` / `zTilde_conj_smul` / `conjClassSet_conj_smul` /
  `conjClassSet_zTilde_conj_eq` / `isHall_kappa_subgroupOf_conj` (κ-Hall 共役不変) /
  `conjClassSet_zTilde_eq_of_isConjugate` (threading) / `conjClassSet_zTilde_eq_fixed_of_isTypeP`
  (任意 type-P N の Ẑ → 固定 W=Ẑ(M))。
- **fixed-W cover** (S14): `kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde` +
  `exists_mem_conjClassSet_Mtilde_or_fixed_zTilde` (κ-branch を固定 Ẑ に着地)。
- **struct redesign** (S10): `BGTheoremENonTypeICovering.W : Subgroup` → `exceptionalSet : Set`
  (W:Subgroup は **unsatisfiable** = 本 issue で独立確認; K*#⊆M_σ#⊆M̃ が exceptional_disjoint を破る)。
  downstream consumer 0 ゆえ safe。
- **producer** (S10): `nonTypeICovering_of_isTypeP` — M̃-cover data + ref type-P ⟹
  `BGTheoremENonTypeICovering` (exceptionalSet=zTilde、cover_nonidentity=fixed-W cover+reps変換、
  pairwise=conjClassSet_Mtilde_disjoint、exceptional=conjClassSet_T_Mtilde_disjoint)。
- **wiring** (S10): 𝓜_P≠∅ → `Or.inr ⟨producer⟩` 完全証明; 𝓜_P=∅ → TypeICovering sorry のみ残。

⟹ headline sorry は (8.8) 全体から **TypeICovering/§8 case (𝓜_P=∅) のみ**に縮小。残りは
`cover_subset_kernels` (= route B / §8 Dade、lane-a/c)。lane-d の §14-16 群論 + fix-W はこれで
NonTypeICovering を閉じきった。

## ✅ lane-d milestone 再検証 + route-B contradiction engine 同定 (2026-07-01 /loop)

**(1) full build green 再検証** (3889 jobs, exit 0): Theorem D (D(3) `exists_RData_of_mem_sigmaSharp`
両枝 sorry-free / conjunct 3 `signalizer_centralizer_isComplement` / hD4 `exists_RData_escape_structure`
/ wrapper `theoremD_msigma_conjugacy_and_centralizers`) + Theorem E + NonTypeICovering 分岐すべて
build-green を確認。lane-d の BG §14-16 群論 FT-path milestone は完全に landed・solid。

**(2) route-B contradiction engine = `S09.not_trivial_G0_of_family71_coherent_zeta_source_data`
(S09:6580)**: route-B の (12.17) 矛盾は単純な FamilyHypothesis71-only path **ではない**。この engine は
**FrobeniusFamily F + FamilyHypothesis71 P を `hP_G0 : P.G0 = F.G0` で結合**し、`hG0 : F.G0 = {1}` +
**~30 の §7/§8 character 入力** (coherence `IsCoherent τ`、`Hypothesis78.BetaDecomp`、zeta 既約/norm/
degree-sum bounds、`chiRhoNormSq` lower bounds 等) を取って False を出す。これらの char 入力は全て
**lane-a/c の §7-9 coherence/Dade 領域**で、type-I family 向けには未構成。⟹ route-B の真の residual は
これら char 入力の構成 (lane-a/c)。**lane-d は難所回避でなく、上流 char infra が未整備**。

**(3) lane-d prep landed (S10, commit 本 /loop)**: route-B が必要とする `FamilyHypothesis71` の
`G₀ = {1}` step を certain-correct な純集合論 helper として供給:
- `S10.familyHyp71_one_mem_G0` (`1 ∈ G₀`、`S04.one_notMem_dadeSupport` 経由)。
- `S10.familyHyp71_G0_eq_singleton_one_of_cover` (Dade-support cover ⟹ `G₀ = {1}`、`FrobeniusFamily`
  kernel-cover の M̃-cover 類似)。M̃-cover (`S14.sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`)
  を hcov に与えれば `P.G0 = {1}` が出る。axiom-clean、full build green。
  (route-B assembly 時に `S09.FamilyHypothesis71` namespace へ hoist 可。)

⟹ **route-B の lane-d-doable prep (M̃-cover + G₀={1} helpers) は揃った**。残 = (a) §8 `dadeSupportHypotheses_typeI`
(8.15) を cite した per-rep `FamilyHypothesis71` 構成 + (b) ~30 char 入力 (coherence/Dade、lane-a/c)。
両者とも lane-a/c §7-9 char theory に gated。lane-d 単独 build-green での route-B closure は不可
(上流 char infra 待ち)。
