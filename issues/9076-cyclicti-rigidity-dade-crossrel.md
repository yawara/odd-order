---
id: 9076
slug: cyclicti-rigidity-dade-crossrel
title: "shared-infra claim: §3 cyclicTI rigidity (eq_signed_sub_cTIiso) → prDade_sub_TIirr Dade cross-relation — (13.18)/(10.5)/(11.8) 共通 gate"
created: 2026-07-08
---

# shared-infra claim (lane c): §3 cyclicTI rigidity → prDade_sub_TIirr Dade cross-relation

**claim-before-build (CLAUDE.md (C))**. Lane c claims the §3 cyclicTI rigidity lemma
`eq_signed_sub_cTIiso` (Coq PFsection3.v:1681) and the §4 Dade cross-relation `prDade_sub_TIirr`
built on it (Coq PFsection4.v:870). Grep confirms **neither is in repo** as of 2026-07-08
(`PrimeTIResidue.lean` の comment が "missing σ isometry stack (cyclicTIiso, dirr_dIirr, PFsection3.v),
not yet in this file" と明記; grep で `eq_signed_sub`/`dirr_small_norm` は repo hit 0)。

## 背景 (2026-07-08 lane c, issue 3003 (13.18) 精査で判明)

(13.18) の `S`-side βₛ bridge (issue 0098 item 3, 3003) の残 deep obligation 群
(`tauS_mu_row0_cross` cross-relation / `betaGrid_support` (13.18.a) / `gammaGrid_real` / `gammaGrid_Y_norm_bound`)
が**全て同じ §3 cyclicTI rigidity に bottom-out** すると code-level + Coq trace で確定:

- `tauS_mu_row0_cross` (= `τ_S(μ_0j−μ_01)=η_0j−η_01`) は Coq defGamma (PFsection13.v:1908) が
  `prDade_sub_TIirr` で discharge。`prDade_sub_TIirr` (PFsection4.v:880) は `eq_signed_sub_cTIiso` を適用。
- `betaGrid_support` (Coq PVSbeta PFsection13.v:1833) も `cfRes_prTIirr`/`prTIirr_id` (prime-TI 値) を使用。

**`eq_signed_sub_cTIiso` の内容** (PFsection3.v:1681, "(3.8) の帰結、(4.8)/(10.5)/(10.10)/(11.8) で使用"):
> `φ ∈ ℤ[irr G]`, `‖φ‖²=2`, `j1≠j2`, φ が `V` (regular set) 上で `ρ = ±(η_{ij1}−η_{ij2})` と一致
> ⟹ `φ = ρ` (全体で)。

= norm-2 virtual character の **rigidity**: V 上の値 (signed η-difference) で全体が決まる。

## やること (multi-piece §3 port、substantial multi-session)

- [x] **piece 1 `dirr_small_norm`** — ✅ **完了 (2026-07-08)**: `exists_signed_pair_of_mem_ZIrr_inner_self_eq_two`
  (`ZIrrFourier.lean`)。`φ ∈ ZIrr G`, `‖φ‖²=2` ⟹ `φ = ε_α•α + ε_β•β` (α≠β 既約, ε∈{±1})。**sorry-free**。
  判明: 必要 infra は `ZIrrFourier.lean` に**既に全部あった** (旧 issue 0025 layer-2): `mem_ZIrr_repr`
  (φ=∑c(a)•a, c:→₀ℤ) / `mem_ZIrr_inner_self_eq_sum_sq` (Parseval ‖φ‖²=∑(c a)²) /
  `exists_pair_of_sum_sq_eq_two` (整数 combinatorial core: 全非零・平方和2 ⟹ 相異2元各±1)。
  → 新 leaf 不要、既存 file に assembly のみ追加 (build 3152 jobs green)。
- [x] **piece 2 (3.8) cyclicTI NC theory** — ✅ **実装済みと判明 (2026-07-08 精査)**。「repo 不在」は
  Coq 名 grep による誤診 ([[verify-port-state-by-number-not-coq-name]] の実例):
  NC 定義 = `sigmaNC`、(3.7) = `sigmaCoeff_add_eq`、(3.8) 弱形 = `sigmaCoeff_eq_zero_of_sigmaNC_lt`、
  `cycTI_NC_norm` = `ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast` (全て `S05_SigmaIsometry.lean`)。
  **(3.8) full trichotomy** = `grid_trichotomy` (`S05_GridTrichotomy.lean`, 抽象版・rank-one 分解法) +
  `sigmaCoeff_trichotomy` (`S05_SigmaTrichotomy.lean`)。
- [x] **piece 3 `eq_signed_sub_cTIiso`** — ✅ **実装済みと判明**: `eq_smul_chiFam_diff_of_vanishOnV`
  (`S05_SigmaTrichotomy.lean:277`)。Coq より一般 (任意 grid index ペア P1≠P2、同一行制約なし)。
### ⚠ 重要更新 (2026-07-08 精査): rigidity engine は S05 に既存、9076 の残りは "connection"

piece 2/3 が S05 に既にあると判明したので、9076 の当初計画 (§3 from-scratch port) は**不要**。
残る piece 4 (`tauS_mu_row0_cross` discharge) は**新 leaf を建てる話ではなく**、既存 S05 rigidity を
consumer (S15 η-grid + τ_S Dade) に**接続する**話。以下は精査で確定した正確な状態。

**correctness 発見 (要 3003 調整)**: 現 (13.18) 実装 (`tauSbetaGrid`/`GammaGrid`/`tauS_mu_row0_cross`,
S15_SAndT.lean) は **'A(S)-Dade** (`hyp.dadeHypS` = `honestTypeP2ASet`) で組まれているが、Coq §13
(`A0beta`/`Dtau`/`prDade_sub_TIirr`) は **'A0(S)-Dade** ('A0(S) = 'A(S) ∪ class_support(V_S, S))。
μ差 `μ_{0j}−μ_{01}` の support は P^#∪V_S (Coq `prDade_sub_TIirr_on` = `∈ 'CF(S,'A0)`) で、V_S-part は
'A(S) に**入らない** → `dadeIntegralCharacterMap (dadeHypS) …` の arbitrary-extension 領域に落ちる
→ **現 `tauS_mu_row0_cross` statement は provable でない** (V_S 上で τ_S が未制御)。埋める前に A0 化必須。

**⚠ 既存機構の発見 (2026-07-08)**: `S16_GridExpansion.lean` (lane c 既存) が η-grid の (3.8)
機構を**大量に実装済み** — `eta_orthonormal`/`eta_mem_ZIrr`/`eta_principal_eq_trivial` (η₀₀=1_G)/
`inner_eta_grid_relation` ((3.7) separability)/`grid_eq_zero_of_relation_of_card_le_two` (NC≤2 rigidity)/
`inner_eta_eq_zero_of_vanish_of_inner_self_eq_two` (norm-2 ⊥-grid)/`eta_orthogonal_of_norm_one_pair_vanish`
((13.19.b))。着手前に grep すべきだった (CLAUDE.md「既存を再構築しない」)。ただし既存は **NC≤2
(all-zero) case のみ**で、difference rigidity `eq_signed_sub_cTIiso` が要する **NC(ψ)≤4 の full
trichotomy** (constant-row/column 除外) は欠く → 4a/4b がそれを埋める。

**piece 4 の状態**:
- [x] **4a. 抽象 rigidity engine** — ✅ **完了 (commit 0d1500cc, sorry-free)**:
  `OddOrder/Peterfalvi/S05_GridRigidity.lean` の `orthonormalGrid_diff_rigidity`。任意 orthonormal
  ZIrr grid family に対する norm-2 difference rigidity (full trichotomy 版)。既存 `grid_trichotomy`
  (S05_GridTrichotomy) を再利用、係数評価のみ抽象 χ に lift。orthonormality は decidable-agnostic
  `horth_diag`/`horth_off` で受ける (ite mismatch 回避)。**interface guard「module-level generic」準拠**。
- [x] **4b. η-grid instantiation** — ✅ **完了 (commit 9337f8d1, sorry-free)**:
  `S16_GridExpansion.eta_diff_rigidity`。4a を cite し、既存 `eta_orthonormal`/`eta_mem_ZIrr`/
  `inner_eta_grid_relation` から η-grid data + (3.7) separability を供給。行 i₀=0 形で (13.18) の
  `τ_S(μ_{0j}−μ_{01}) = η_{0j}−η_{01}` の rigidity 部品を提供。(4.8)/(10.5)/(10.10)/(11.8) でも再利用可。
- [~] **4c. (13.18) A0-Dade 化 + cross-relation 本体** — **'A0-Dade infra 完成 (2026-07-08)**、残 = rewire + prime-TI:
  - [x] **4c-1** `honestTypeP2A0Set` 定義 + set-facts (commit 144df308, sorry-free)。
  - [x] **4c-2a** V-part Dade obligation 部品 (commit 6c20b771, sorry-free): V^S は escape せず →
    escaping は A-part へ帰着。
  - [x] **4c-2b** `dadeSupportHypothesisData_honestTypeP2A0Set` (commit 79dd67c1): σ-decomposition
    engine で 7 obligation 中 6 discharge。**deep pin 1 本に isolate** = `not_isConj_honestTypeP2ASet_typePV`
    (A(S)∈S' element が V^S∉S' element と G-共役でない; TRUE by normedTI 'A0 だが循環 → type-P2
    FT-support geometry (Coq FTsupp0/BG§16 ThmII) 直接証明を要する; W₂⊆M_σ ゆえ elementary route 不成立)。
  - [x] **4c-2b′ deep pin を実証明化 (2026-07-08)** — `not_isConj_honestTypeP2ASet_typePV` を
    **sorry-free に** (旧「genuine deep content」評価を **de-risk**): 循環 normedTI 経路を捨て、
    **BG §16 Theorem II の tame conjugation** (`BG.Ch4.S16.theoremII_tame_embedding` 第1連言 = repo に
    既存・obligation discharged) で直接証明。構造 = `a∈A(S)⊆M'` ∧ `b∈V^S⊄M'` ∧ IsConj a b ⟹ tame で
    **M-共役** `b=m·a·m⁻¹` (m∈M) ⟹ `M'⊴M` ゆえ `b∈M'` (実証明: `(derivedInG M).subgroupOf M` Normal
    instance + `typePData_typePV_not_mem_derived`) ⟹ `b∉M'` と矛盾。残 deep 部は clean helper
    `honestTypeP2A0Set_tame_conj` (sorried) に精密 isolate: honest support → BG `A0Set M K` の bridge
    (`honestTypeP2ASet_subset_hatMsigma` 既存 + `V^M⊆hatMsigma` + order 論法 `V∩𝒞_G(K#)=∅`) +
    κ-Hall/`(κ∪σ)′`-Hall 供給 (M solvable ⟹ Hall 存在)。∴ **旧「FTsupp0 未形式化」は幻**、残 = mechanical
    BG-support bridge。full build 3940 green・AxiomsCheck OK・新 axiom なし。**dadeHypS0 の deepest gate 除去**。
  - [x] **4c-2b″ tame helper 完成 → deep pin 完全 discharge (2026-07-08)** ✅:
    `honestTypeP2A0Set_tame_conj` を **sorry-free 化** ⟹ `not_isConj_honestTypeP2ASet_typePV` は
    **完全に proven** (helper 依存も解消) ⟹ **dadeHypS0 の A0-normedTI gate 完全消滅** (4c-4 cross-relation が
    honest な A0-Dade に乗る)。route (下記) を uniform BG Thm II で実装、subagent 実行 + hub 検証:
    新 lemma = `honestTypeP2A0Set_subset_A0Set` (A-part `aSet_subset_A0Set` κ′/κ order + V-part
    `conjClassSetIn_typePV_subset_A0Set` σ⊆κ′ order + hatMsigma M-conj 不変) / `exists_sigma_prime_dvd_orderOf_typePV`
    (V-elt に σ-prime) / `kappaHall_conjClassSet_isPiElement` (K# = κ-elt) / `typePData_W1_inf_W2_eq_bot`。
    signature: pin+helper に κ-Hall/`(κ∪σ)′`-Hall 仮説を追加 (IsTypeP2 不要, `honestTypeP2ASet_isConj_conj_in_M`
    mirror)、唯一の caller `dadeSupportHypothesisData_honestTypeP2A0Set` (既に Halls を produce) が pass。
    **検証済 (hub)**: 変更は S15_HonestTypeP2A0.lean のみ / 新 axiom 無 / 新 sorry 無 (helper sorry 除去のみ, 4→3) /
    pin 結論 `:False` 不変 (仮説追加のみ) / full build 3941 green / AxiomsCheck OK。
    **残 S15_HonestTypeP2A0 sorry = prime-TI pin 3 本のみ** (mu_row0_ne / tauS_mu_row0_diff_support /
    tauS_mu_row0_vanish_on_V = 9014, tame とは無関係)。
  - [x] **4c-2d A0-Dade=Ind bridge 完成 (2026-07-08)** ✅ — (13.18) A0-Dade infra を **完全 honest 化**:
    `escaping_honestTypeP2A0Set_eq_empty` ((13.2.e) A0 normedTI, 既存の proven A(S)版から) →
    `dadeHypS0_H_eq_ftSupportKernel` → `forall_dadeHypS0_H_eq_bot` (全 A0-stabilizer =⊥) →
    `sInstance_dade0_eq_induce` (**τ_S = Ind_S^G on A0-support**, dadeMap_eq_induce + restrict_H 経由)。
    ⟹ gammaGrid_orthogonal_one / pin C の **τ_S=Ind 半分は解決**、残 gate は uniform に prime-TI のみ。
    full build 3941 green・AxiomsCheck OK・新 axiom/sorry 無。
  - **⚠ prime-TI frontier 精密特定 (2026-07-08 精査)**: (13.18) 全 endpoint の残 gate = prime-TI **のみ**。
    重要発見: **μ V-value は §12 で既に形式化** (`Hypothesis.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV`,
    S12_Core:2584: `muGrid i j v = columnSign j • alignedOmegaSigmaGrid i j v` on typePV)、
    `muColumnSign`/`alignedOmegaSigmaGrid`/`muGrid_apply` 一式 (S12_Core) 完備。**ただし §10/§12
    `Hypothesis M` framework の `muGrid`** であって **S15 `Hypothesis` の `hyp.mu` (free field)** ではない。
    ∴ pin discharge の道 = (a) **S15.mu ↔ §12.muGrid (M=hyp.S) framework bridge** を建てて §12 の
    V-value/distinctness を transport、or (b) S15 Hypothesis carrier に prime-TI field を追加 (constructor 供給)、
    or (c) 9014 general residue API port。いずれも substantial (次 session 級)。**mu_row0_ne** (cross-column
    distinctness) は §12 の grid injectivity 側、**vanish_on_V** は上記 V-value + 新 A0-Dade=Ind bridge の合成。
  - **✅ 決着: 残 gate = 単一の b-side grounding field (2026-07-08 lane-c /loop 精査)**。上記 (a)/(b)/(c)
    より precise。`S13_PrimeTIResidueBridge.lean` (main 合流済) が **`Hypothesis.residueS` = S-side
    prime-TI residue grid `PrimeTIResidueData ↥S`** を **`PrimeTIResidueData.ofS06Hypothesis` で sorry-free
    構成済** (type-uniform, `IsTypeP2` から `IsTypeP` 経由、`IsTypeP1` 不要)。`PrimeTIResidue.lean` も
    **100% sorry-free** (`mu2_orthonormal`/`chi_res`/`ind_chi`/`cfker_prTIres`/`prTIres_irr_cases` 全 posited
    field を実 discharge、`prTIres_irr_dichotomy` 経由)。⟹ **prime-TI 基盤は完成**。3 pin の残 gate は
    **ただ 1 つ: grounding `hyp.mu i j = hyp.residueS.mu2 (cast i)(cast j)`**。両者とも
    `columnFamily.mu` — spine の `Section16CharacterData.muS` (FeitThompson:1459) は **文字通り
    `(certainTypeS.columnFamily …).mu`**、residueS.mu2 も `(columnFamily χ₂).mu`。∴ a の spine discharge は
    **near-definitional** (certainTypeS vs s06S の identification のみ)。
    - **3-lane spec (near-mechanical)**: **(b)** `S15.Hypothesis` に grid-property field
      `mu_grounded : ∀ i j, mu i j = residue grid` (or 弱形 `mu_grid_orthonormal`) を additive 追加
      (S15_SAndT_Setup、grid-property field ゆえ 9009 で lane-b)。**(a)** spine (FeitThompson:2665) で
      `muS = columnFamily.mu = residueS.mu2` から discharge。**(c=lane-c)** 3 pin を residueS から close:
      `mu_row0_ne` ← `mu2_ne`(=`mu2_orthonormal` off-diag); `tauS_mu_row0_diff_support` ←
      `certainTypeDiffSupported` (+`hypothesis46OfTypePData`, A=honestTypeP2ASet, dade0=dadeHypS0);
      `tauS_mu_row0_vanish_on_V` ← certain-type Dade-id + V-value。
    - **なぜ arbitrary hyp で pin が unprovable**: `hyp.mu`/`hyp.omega` は S15.Hypothesis の抽象 axiom
      (orthonormal grid + `mu_definition` induced-diff + `mu_col_injective` within-col) を満たす **free
      field**、cross-column distinctness/support/V-value を fix しない (別 valid grid が反例)。∴ grounding
      無しに pin は theorem でない (scaffold でなく genuine な carrier grounding 不足)。
    - **lane-c 実施済 (2026-07-08)**: `mu_row0_ne` の proof を refine — diagonal `⟨μ_{0,#1},μ_{0,#1}⟩=1`
      (`mu_irreducible.inner_self_eq_one`) + 矛盾 logic を実証明、残 sorry を **単一 crisp obligation**
      `hoff : ⟨μ_{0j},μ_{0,#1}⟩=0` (= row-0 cross-column orthogonality = grounding) に isolate。build green。
  - **route (実装済、参考)**:
    `honestTypeP2A0Set_tame_conj` を **circularity 回避のため BG Thm II で uniform に** 証明する
    (case-dispatch は mixed case = pin ゆえ循環; 実際 `dadeSupportHypothesisData_honestTypeP2A0Set` の
    dispatch (S15_HonestTypeP2A0:236-244) は mixed に pin を cite = 逆向き依存)。既存 infra 発見:
    **V-part tame `conjClassSetIn_typePV_isConj_conj_in_M` (S10:1783) は native** (`typePData_V_ti`、
    Hall/BG Thm II 不要); **A-part `honestTypeP2ASet_isConj_conj_in_M` (S15_Setup:727) は既存**
    (ASet 経由 BG Thm II)。crux = 単一 inclusion **`honestTypeP2A0Set M data ⊆ A0Set M K`** (BG A0Set):
    (1) **A-part** `A(S)⊆ASet⊆A0Set` — `honestTypeP2ASet_subset_ASet` 既存 + `ASet⊆A0Set` は order 論法
        (`U⊔M_σ`-elt は κ′-order, `K#` は κ-order ⟹ `(U⊔M_σ)∩𝒞_G(K#)=∅`, ∴ `hatMsigma∩(U⊔M_σ)⊆hatMsigma∖𝒞_G(K#)`);
    (2) **V-part** `V^M⊆hatMsigma` (v の W₂-成分 ∈ M_σ# を centralize, W abelian + `data.W₂≤data.H≤M_σ`)
        ∧ `V^M∩𝒞_G(K#)=∅` (V-elt は σ-prime を order に持つ, K# pure κ);
    (3) **Halls** `typeP2_exists_matched_kappa_hall_pair hG hM hP2` (S16:1454) — **`IsTypeP2 M` 要**
        ⟹ pin/helper signature に `hP2` 追加要 (pin 使用箇所 = dadeSupportHypothesisData:241/243 は hP2 保持ゆえ pass 可);
    (4) helper 本体 = `theoremII_tame_embedding hG hM hKM hUM hK hU (X:=A0Set M K) (Or.inr rfl)` の第1連言 +
        (1)(2) の inclusion で a,b を A0Set に lift。**全 step tractable、mechanical support-geometry のみ残**。
  - [x] **4c-2c** `Hypothesis.dadeHypS0`/`dadeHypS0_hconj` (commit 79dd67c1 隣): S-instance 'A0-Dade bridge。
  - [x] **4c-3** tauSbetaGrid/GammaGrid/tauS_mu_row0_cross/gammaGrid_defGamma を dadeHypS0 に rewire
    (commit a6f7a2ed)。**headline correctness fix**: 旧 dadeHypS (A(S)⊆S') では μ差の V_S-part が
    arbitrary-extension 領域ゆえ statement が unprovable-as-stated → 'A0-Dade で provable-in-principle 化。
    downstream consumer 無し・full build 3940 green・新 sorry 無し。
  - **rewire soundness 検証済**: dadeHypS0 は faithful-Dade (H=ftSupportKernel、escaping P^# 点で≠⊥) で
    Coq normedTI-Dade (H=1) と P^#-image で異なりうるが sound: `eta_diff_rigidity` は X を
    (ZIrr, ‖·‖²=2, **V-agreement**) から一意決定し、V_S 上は H=⊥ (V-elem escape せず) ゆえ V-agreement は
    Dade_id で P^#-behavior 非依存。∴ rewire 正しい。
  - [x] **4c-4 assembly** — ✅ **完了 (2026-07-08)**: `tauS_mu_row0_cross` の opaque `sorry` を
    **実 assembly (S15_SAndT.lean:4019-4117、~98 行、sorry-free)** に置換。lane-c 自身の `eta_diff_rigidity`
    (4b) + Dade isometry API を genuine に呼ぶ本体を構築:
    - j=#1 trivial case (`simp [hj1, sub_self, map_zero]`, μ差=η差=0)。
    - `X := τ_S(μ差) ∈ ZIrr G` = `dadeIntegralCharacterMap_mem_ZIrr_of_supported` (Dade (2.6.b))。
    - `‖μ差‖²=2` = 2 相異既約の inner (`mu_irreducible` + `mu_row0_ne` + `irreducibleCharacter_inner`
      + `inner_self_eq_one`) → `‖X‖²=2` = `dadeIntegralCharacterMap_inner_eq_of_supported` (Dade 等長)。
    - V 上一致 → `S16.eta_diff_rigidity` (s=1) で `X = η_{0j}−η_{01}` を pin。
    残 = **3 isolated prime-TI pin** (c-owned `S15_HonestTypeP2A0.lean` に isolate、各 Coq provenance 付き):
    `Hypothesis.mu_row0_ne` (μ_{0j}≠μ_{01}, cross-column 相異)、`Hypothesis.tauS_mu_row0_diff_support`
    (μ差 ⊆ supportInSubgroup('A0(S))、Coq `prDade_sub_TIirr_on`)、`Hypothesis.tauS_mu_row0_vanish_on_V`
    ((τ_S(μ差)−η差) vanishes on conjClassSet(regular)、Coq `prTIirr_id`+Dade_id on V)。
    **(i)(ii)(iii)=prime-TI theory (未ポート、cf 9014/lane-a)**。full build 3940 green・AxiomsCheck OK・
    新 axiom なし。**architecture**: S15_SAndT が S16_GridExpansion を import (S16 は S15_SAndT_Setup のみ
    import ゆえ非循環、intended design)。**lane-c structural work 完了; 残 = prime-TI pin (9014 cross-lane)**。
  - **旧記述 (参考)** ⚠ **correctness fix**:
  現 `tauS_mu_row0_cross` (S15_SAndT.lean:4008, sorry) は **'A(S)-Dade** (`hyp.dadeHypS` =
  `honestTypeP2ASet` = `centralizerSupport(sharp(Msigma S), derivedInG S)` ⊆ S') で組まれているが、
  μ差 `μ_{0j}−μ_{01}` の support は P^#∪V_S で **V_S (⊄ S'、W₂-成分≠1) は 'A(S) に入らない** →
  `dadeIntegralCharacterMap` の arbitrary-extension 領域 → **現 statement は provable でない** (確認済:
  `honestTypeP2ASet` = derivedInG 内、V_S は W₂ 成分ゆえ S' 外)。Coq は **'A0(S) = 'A(S) ∪
  class_support(V_S)** (`FTtypeP_supp0_def`, `A0beta`) で組む。fix 手順:
  1. `honestTypeP2A0Set` (= A(S) ∪ V_S-classes) 定義 + A0-Dade `DadeSupportHypothesisData`
     (既存 `dadeSupportHypothesisData_honestTypeP2ASet` の A0 拡張、or BG `S16.A0Set` 再利用を要調査)。
  2. tauSbetaGrid/GammaGrid/tauS_mu_row0_cross/gammaGrid_defGamma の τ_S を A0-Dade に差し替え。
  3. tauS_mu_row0_cross 本体を **4b `eta_diff_rigidity`** で分解。残 isolated pins:
     μ差 support ⊆ 'A0(S) (Coq `prDade_sub_TIirr_on`) / μ の V-value = ω の V-value (Coq `prTIirr_id`,
     prime-TI) / Dade-id on V (`sInstance_dade_eq_induce_of_supported_trivial_H` の A0 拡張)。

## consumers (broad — §4/§10/§11/§13)

- **§13**: `tauS_mu_row0_cross` (3003, defGamma) / `betaGrid_support` / `gammaGrid_real` /
  `gammaGrid_Y_norm_bound` → S16 `T_typeIII_ratio_le` (S-side βₛ gap、C-lane W-side frontier)。
- **§10/§11**: Coq comment 明示 = (10.5)/(10.10)/(11.8)。lane-a の §10-13 中央核と重なる可能性 → 要 hub 調整。
- σ-isometry 土台 (`S05.TICyclicHypothesis.sigmaIntegral`) は**既存** (isometry/trivial/ZIrr/V-value 完備、
  旧 lane d 構築)。本 claim = その image の **rigidity** (norm-2 characterization)、9014 (residue API) とは別層
  だが同じ cyclicTIiso provenance。

## interface guard (dup 予防、必須)
- **9014 (prime-TI residue API) と別物だが隣接**: 9014 = residue grid (primeTIred/prTIres_irr_cases) を posit。
  本 claim = Dade/σ rigidity (eq_signed_sub_cTIiso)。両者とも "cyclicTIiso port" の一部。着手前に 9014 の
  scope と重複しないか再確認 + lane-a (§10-13 consumer) と coordination (2026-07-02 dup 事故予防)。
- shared leaf は module-level generic (σ-isometry の任意の image に対する rigidity)、side-specific predicate 禁止。

## 完了条件
- `eq_signed_sub_cTIiso` + `prDade_sub_TIirr` 相当が repo に実装され、`tauS_mu_row0_cross` を discharge。
  → (13.18.c) defGamma が完全 sorry-free (cross-relation cite が実証明に)。build green + AxiomsCheck OK。

## 参照
- Coq: `eq_signed_sub_cTIiso` PFsection3.v:1681 / `prDade_sub_TIirr` PFsection4.v:870 /
  `dirr_small_norm` (mathcomp character) / PVSbeta PFsection13.v:1833。
- 既存 σ-isometry: `OddOrder/Peterfalvi/S05_IntegralSigma.lean` (`TICyclicHypothesis.sigmaIntegral`)。
- 関連 issue: 3003 (13.18 faithful 化 + cross-relation isolate)、9014 (prime-TI residue、隣接)、
  0098 (lane c package item 3)、9000 (σ-theory typeP_Galois、別)。

## ⚠ HUB renumber (2026-07-08 合流 tick)

本 issue は lane c が **9075** として起票したが、lane a が同 tick で独立に 9075
(`9075-s07-pivot-coherence-norm-general`, (5.7) norm-general port) を採番しており衝突。
merge 順 (a→c) により a が 9075 を保持、本 issue を **9076 へ renumber** (c の参照ファイル
3003/s15 notes 内の言及も置換済)。lane c は次回 main sync で本 rename を取り込むこと。
両 claim は別 ref ((5.7) vs §3 cyclicTI) で重複建設ではない。

## ✅ HUB 裁定: piece 4c-3 の S15_SAndT carve-out 拡張 #2 付与 (2026-07-08 合流 tick)

piece 4c-3 (`tauSbetaGrid`/`tauS_mu_row0_cross`/`gammaGrid_defGamma` の τ_S を `dadeHypS`→`dadeHypS0`
に rewire) は **b 所有の `S15_SAndT.lean`** への編集。piece 4c carve-out (merge_monitor) は
S15_HonestTypeP2A0.lean のみを c に付与し、`tauS_mu_row0_cross` statement 変更は
「**b territory ゆえ b+c 調整要 (b が行うか c が carve-out 追加申請)**」と明記していた。lane c は
carve-out 申請より先に着手したが、hub は監視 tick で **「軌道修正で保全」ポリシー** (CLAUDE.md /
merge_monitor 🔧) に従い **retroactive に carve-out 拡張 #2 を付与して成果を保全** (discard/revert せず)。

**裁定根拠 (hub 自律、ユーザー escalation 不要)**:
1. **genuine correctness fix** — 旧 dadeHypS ('A(S)⊆S') では μ差の V_S-part が arbitrary-extension 領域に
   落ち statement が unprovable-as-stated。'A0-Dade 化が唯一の sound route。
2. **下流 blast radius = ゼロ** — `tauS_mu_row0_cross`/`gammaGrid_defGamma`/`tauSbetaGrid` の外部 consumer
   は repo に存在しない (grep 確認、S15_HonestTypeP2A0 docstring 言及のみ)。signature 変更は self-contained。
3. **b は S15_SAndT に一切触れていない** (`git diff main...b` 空) → 調整点の懸念 (b+c 同時編集で衝突) は
   実際には未発生。
4. **merge-safety 全通過**: build green (3940 jobs) / AxiomsCheck OK / 新 axiom なし / sorry +1 =
   新 decl `not_isConj_honestTypeP2ASet_typePV` deep-pin scaffold (regression でない)。

⟹ **(13.18) S-side A0-rewire ブロック = lane c 所有** (step 1.5 逸脱でない)。**b は次回 main sync で c の
rewire を取り込み、`tauS_mu_row0_cross` を再構築しないこと。** 正本 = merge_monitor.md「coordination 点 解決」節。

## ⚠ HUB FLAG (2026-07-08, lane c /loop): (13.18) A0-Dade 完了 → 残 pin は lane-b 依存 (reallocation 要検討)

lane c は本 session で **(13.18) A0-Dade infra を包括的に完成** (8 commit): cross-relation assembly
(`tauS_mu_row0_cross`) / deep A0-normedTI pin **完全 discharge** (`not_isConj_honestTypeP2ASet_typePV`
= BG Thm II tame conjugation, `honestTypeP2A0Set_tame_conj` 完成) / A0-Dade=Ind bridge 完成
(`escaping_honestTypeP2A0Set_eq_empty` → `forall_dadeHypS0_H_eq_bot` → `sInstance_dade0_eq_induce`)。
**A0-Dade 側は完全 honest** (新 axiom 無、build 3941 green)。

**残 (13.18) endpoint (3 pin + gammaGrid_orthogonal_one/real/Y_norm_bound) の gate は uniform に
prime-TI μ-grid の cross-column 構造のみ**。精査で判明した **重要 blocker**:
- S15 `Hypothesis` は **posited carrier** (`S16_NonExistenceGCore:43 base : S15.Hypothesis`)、`mu` は free field。
- 3 pin (mu_row0_ne=cross-column distinctness / diff_support=off-A0 一致 / vanish_on_V=V-value) は
  **全て cross-column μ 構造**を要する。`mu_definition` (13.1.e) は **within-column のみ**ゆえ不足。
- cross-column μ 構造 = **§12 で既に形式化** (`muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV`
  等, S12_Core) だが **§10/§12 `Hypothesis M` framework の `muGrid`**。S15 `hyp.mu` (free field) との
  **connection = S15 Hypothesis carrier の honest 構成** (mu = §12 muGrid) が必要 = **lane-b S15 char cascade** territory。

⟹ **lane c の ungated・非 lane-b な (13.18) 仕事は完了**。残は (a) lane-b の S15 carrier 構成 (mu を §12
prime-TI に接続)、or (b) S15↔§12 framework bridge (carrier 構成前提ゆえ bridge lemma 単独では pin 未 discharge)。
**hub 裁定要**: lane c を (i) lane-b char cascade 支援に再配置 / (ii) S16 W-side の別 gated frontier / (iii) 他。
lane c は本 flag 後も /loop 継続 (報告≠停止); 次 iteration は S16 W-side 等で ungated piece を再走査。

## ⚠ LANE-B 診断解決 (2026-07-08, /loop 再開): (13.18) μ-carrier の honest source = prime-TI residue (§12 muGrid でない)

上の HUB FLAG (lane c) は「S15.mu の honest source = §12 `Hypothesis.muGrid`、connection = S15 carrier
構成」とした。lane-b が code-level 精査し、**§12 muGrid route には type obstruction がある**ことを確定
(訂正):

- **§12.Hypothesis は type-P1 gated**: `type_alt : IsTypeIII ∨ IsTypeIV ∨ IsTypeV` (S12_Core:352)
  = `IsTypeP1`。Dade support `typePA0` も `dadeSupportHypothesisData_typePA0_of_isTypeP1` (S10:2340) で
  P1 gated。**S は type-P2** (`S_typeP2`; `not_isTypeII_of_isTypeIII_or_IV`/`not_isTypeII_of_isTypeV`,
  S16_MainResults:5670/5682 で III/IV/V と disjoint) ⟹ **S に §12.Hypothesis は構成不能**。
- **真の honest source = prime-TI residue grid** (pins 自身の docstring が既に明示: Coq `prTIres`/
  `prDade_sub_TIirr_on`/`prTIirr_id`, issue 9014)。`mu2 = (columnFamily χ₂).mu` は §12 muGrid と**同一
  オブジェクト** (両者 `h.columnFamily.mu`) だが、その構成は **S06 certain-type のみ依存で type-uniform**
  (`muGrid` は dadeData 非依存、`.toHypothesis = typePData_toS06Hypothesis` のみ使用)。
- ∴ S (P2) も `typePData_toS06Hypothesis hyp.Sdata` (IsTypeP は `isTypeP_of_isTypeP2 S_typeP2` で供給、
  **no IsTypeP1**) で S06.Hypothesis を持ち、`PrimeTIResidueData.ofS06Hypothesis` (sorry-free constructor、
  9014 で完成済) で residue grid を構成できる。

**lane-b 構築 (commit `03e9c01c`、新 leaf `OddOrder/Peterfalvi/S13_PrimeTIResidueBridge.lean`)**:
- `Hypothesis.s06S hG : S06.Hypothesis ↥S` (type-uniform bridge)。
- `Hypothesis.residueS hG : PrimeTIResidueData ↥S S' |W₁| |W₂|` (ofS06Hypothesis 経由、全 field discharged)。
- `PrimeTIResidueData.mu2_ne` (PrimeTIResidue.lean、汎用): entrywise distinctness =
  **pin 1 `mu_row0_ne` の residue-side content** (i=i'=0, j≠j' の special case)。
  `(hyp.residueS hG …).mu2_ne` で S-side 取得。
- full build 3942 green・AxiomsCheck OK・新 axiom/sorry なし。

**残 (full pin discharge に必要、lane-b 継続)**:
1. **pin 2/3 の residue facts**: μ差 support ⊆ A0(S) (Coq `prDade_sub_TIirr_on`) + V-value = ω
   (Coq `prTIirr_id`)。residue API に追加 (support は induce structure、V-value は σ-image identity on V)。
2. **carrier field `hyp.mu = residueS.mu2`** (index 整合込み): S15.mu (free field) を residue grid に
   同定。これは **FeitThompson.lean (lane-a) の `sectionSixteenHypothesis_of_inputs` 供給** = cross-lane。
   HUB 調整要 (S15.Hypothesis に field 追加 → FeitThompson で mu := residueS.mu2 供給)。
3. 上記後に **c-owned S15_HonestTypeP2A0 の 3 pins** を residue API cite で discharge (c 側 or carve-out)。

**⟹ HUB へ**: lane c の「§12 muGrid connection」route は type obstruction で dead。lane-b が
prime-TI residue route で置換中 (bridge landed)。carrier field (item 2) の FeitThompson 供給が
cross-lane 調整点。lane c の (13.18) A0-Dade infra (既 landed) はそのまま residue route で再利用可。

## ⚠ LANE-B pins 2/3 path 特定 (2026-07-08 続): S06 `Hypothesis46` certain-type route

pins 2/3 (`tauS_mu_row0_diff_support` = μ差 support ⊆ A0(S)、`tauS_mu_row0_vanish_on_V` = τ_S(μ差)=η差 on V)
の content は **S06 `Hypothesis46 A L` certain-type theory に type-uniform に既存** (S06_CertainTypeIsometry.lean):

- **pin 2 (support)** = `certainTypeDiffSupported h hχ₂ hχ₂' i (hdeg i)` (`:793` 近辺): `μ_{ij}−μ_{ik}` を
  **`A ∪ conjClassSetIn L tic.V = A₀` 上 supported** な `SupportedClassFunctions` として package。i=0,j,k=1 で
  `μ_{0j}−μ_{01}` の support ⊆ A0(S) = pin 2 そのもの。
- **pin 3 (V-value/Dade)** = `certainType_diff_dade_eq h hχ hχ₂ hχ₂' i (hdeg i)` (4.8 concl.3):
  `τ(μ_{ij}−μ_{ik}) = δ_j•(ω_{ij}^σ − ω_{ik}^σ)`。i=0 で `τ_S(μ_{0j}−μ_{01}) = δ•(ω_{0j}^σ−ω_{01}^σ)`。
  η=τ₃(ω) + V 上 ω^σ=ω-value ⟹ pin 3 (τ_S(μ差)=η差 on V)。

**必要な assembly = `Hypothesis46 (typePA S) ↥S` の構成** (s06S を `toCertainTypeHypothesis` に、tic =
`typePData_toTICyclicHypothesis Sdata`、`dade0` = **lane-c の A0-Dade `dadeHypS0`**、`tau` =
`dadeHypS0.fullDadeIsometryData …`)。⚠ 配置: dadeHypS0 は S15_HonestTypeP2A0 (§15) 内ゆえ Hypothesis46-for-S
+ pins discharge は **S15_HonestTypeP2A0 内 (lane-c owned)** が正しい (私の §13 residueS + S06 API は upstream で citable)。

⚠ 要 reconcile: Hypothesis46 の `dade0` support は `A ∪ conjClassSetIn L tic.V`、これが `honestTypeP2A0Set S Sdata`
(= dadeHypS0 の support) と一致する必要 (`A = typePA S = honestTypeP2ASet S`? / `tic.V = typePV S Sdata`)。
lane-c は既に honestTypeP2A0Set の Dade を構築済ゆえ整合可能なはず。

**⟹ HUB/lane-c へ**: (13.18) pins 2/3 の honest route = **S06 Hypothesis46 certain-type API** (§12 muGrid でない、
prime-TI residue と同じ certain-type 土台)。lane-b の `residueS` (grid) + `mu2_ne` (pin1) は landed。残:
(i) Hypothesis46-for-S 構成 (lane-c file、dadeHypS0 使用) → certainTypeDiffSupported/certainType_diff_dade_eq
cite で pins 2/3、(ii) carrier field `hyp.mu = residueS.mu2` (FeitThompson = lane-a)。3-lane collaboration。

### ⚠ support-set subtlety (pin 2 の Hypothesis46 route 非自明): typePA0 vs honestTypeP2A0Set

`honestTypeP2ASet M = centralizerSupport(sharp(Msigma M), derivedInG M)` (Msigma# を centralize する M' 元) ⊊
`typePA M = (M')# = sharpSubgroup(derivedInG M)` (M' 全 nonidentity)。∴ `honestTypeP2A0Set ⊆ typePA0`。

S06 `certainTypeDiffSupported` は support ⊆ **A ∪ V = typePA0** (A=typePA 時) を出すが、pin 2 は
`⊆ honestTypeP2A0Set` (**より狭い**) を要求 → **方向が逆で drop-in 不可**。

含意 (lane-c/hub 要判断):
- (a) type-P2 で `honestTypeP2ASet S = typePA S` が実は一致 (M'# の各元が Msigma# を centralize) なら問題なし。
  要確認 (群構造依存、M_σ ⊆ Z(M') 等)。
- (b) 真に ⊊ なら、μ差は typePA0 上 supported だが honestTypeP2A0Set 上とは限らず、**pin 2 statement が
  honestTypeP2A0Set より typePA0 で述べるべき** possibility (dadeHypS0 の support も typePA0 に合わせる必要)。
  = lane-c の A0-Dade support 設計の再確認点。

⟹ pin 2 の Hypothesis46 route は「support-set 一致 (typePA0=honestTypeP2A0Set) の確認」or「pin/dade を
typePA0 に統一」が前提。lane-c A0-Dade 領域。lane-b の residueS/mu2_ne (pin 1) は independent に valid。
## ✅ 進捗 (2026-07-08 lane c /loop, commit 4d18f60a) — gammaGrid_orthogonal_one 実証明化 → (13.18) gate 単一化

前 session の HUB FLAG (13.18 A0-Dade infra 完成、残 = prime-TI pins) を受け、**A0-Dade=Ind bridge
`sInstance_dade0_eq_induce` を consumer 側で genuine に消費**して (13.18.c) `⟨Γ,1_G⟩=0`
(`gammaGrid_orthogonal_one`) を **opaque sorry → sorry-free 実証明化**:

- `⟨Γ,1⟩ = ⟨τ_S β_{#1},1⟩ − 1 + ⟨η_{01},1⟩` に分解。η-orthogonality (`eta_principal_eq_trivial` +
  `eta_orthonormal`, S16_GridExpansion grid field) と Frobenius reciprocity + bridge で
  `⟨τ_S β,1⟩ = ⟨β,1_S⟩ = ⟨Ind_{PW₁}^S 1,1_S⟩ − ⟨μ_{01},1_S⟩ = 1 − 0`。
- `⟨μ_{01},1_S⟩=0` は μ_{01} 既約 ∧ ≠1_S (`indPW1_inner_mu` 矛盾) から導出 = **新 gate 不要**。
- FiniteInduce-scoped vs binder instance 衝突は `indPW1_inner_mu` パターン (FiniteInduce aux +
  `convert…using 2 <;> Subsingleton.elim`) で解消。

**帰結**: 残 (13.18) gammaGrid facts の gate を**単一 `betaGrid_A0_support`** ((13.18.a)
`β_j ∈ CF(S,'A0(S))`, Coq A0beta/PVSbeta) に consolidation — `gammaGrid_orthogonal_one` と
`gammaGrid_Y_norm_bound` の両方がこれに還元。`betaGrid_A0_support` の中身 (PVSbeta) は W₁-class
normedTI (Coq gammaW1) + prime-TI residue 値 `prTIirr_id` で、**prime-TI residue = S15 `hyp.mu` free
field ↔ ported S06/S12 residue theory の carrier connection (3002/9014, lane-b territory)** に
bottom-out (前 flag の linchpin と同一)。`gammaGrid_real` は grid conjugation (別の prime-TI gate)。

full build 3941 green・AxiomsCheck OK・新 axiom 無・S15_SAndT real sorry 9 で不変
(opaque 1 → proven + precise gate 1)。

### ✅ support-set subtlety 解決 (2026-07-08 続、上の「support-set subtlety」節を訂正)

上節「support-set subtlety」は **誤診 (逆)** だった。code-level 精査で解決:

- **issue 9008 で既決**: `typePA = (S')^#` こそ **over-claim (phantom、mmd OCR 由来)** で、Frobenius
  補元 `U^#` (C_{S_σ}=1) を誤って含む。`honestTypeP2ASet = centralizerSupport(M_σ^#, S')`
  (M_σ# 添字) が **honest な (8.10)/(13.2.e) 訂正 support** (strictly smaller、正しい)。
  ∴ pin 2 の target `honestTypeP2A0Set` は**正しい** (typePA0 でなく)。
- **certainTypeDiffSupported の support `A ∪ V` は Hypothesis46 の `A` に parametric (free)**
  (S06_CertainTypeIsometry:357 の signature 確認)。∴ `Hypothesis46 (honestTypeP2ASet S) ↥S` を
  `dadeHypS0` (support = honestTypeP2A0Set) で組めば certain-type bound が pin の honest support を
  **直接 deliver**。over-claim 問題は発生しない。

**⟹ 結論: pin 2/3 の route は clean・unblocked**。残 = **Hypothesis46-for-S 組立**
(`A = honestTypeP2ASet`, `toHypothesis = s06S`, `tic = typePData_toTICyclicHypothesis Sdata`,
`dade0 = dadeHypS0`, `tau = dadeHypS0.fullDadeIsometryData`) → `certainTypeDiffSupported` (pin 2) +
`certainType_diff_dade_eq` (pin 3、i=0 で `τ_S(μ_{0j}−μ_{01})=δ(ω^σ_{0j}−ω^σ_{01})`)。
**配置 = lane-c `S15_HonestTypeP2A0`** (dadeHypS0 消費、backward import 回避)。lane-b の
`residueS`/`mu2_ne`/`honestTypeP2ASet_subset_typePA` は upstream で citable。

lane-b landed (commit 01e798c6): `honestTypeP2ASet_subset_typePA` + 本 route 確定。

### ⚠ A_covers 追加 subtlety (Hypothesis46-for-S 組立時、lane-c 向け)

`certainTypeDiffSupported` は A parametric だが、`Hypothesis46 A L` の **`A_covers` field** (`∀ hh ∈ subH,
hh≠1 → hh は A で cover`) が要る。subH = K = S' ゆえ A_covers は「S'# が A で cover」を要求。
`A = honestTypeP2ASet` (⊊ S'#) では **S'# ∖ honestTypeP2ASet (= M_σ# を centralize しない S'-元) が
cover されず A_covers が直接には成立しない**可能性。∴ Hypothesis46-for-S を A=honestTypeP2ASet で組むには
(a) A_covers を honest support 向けに再証明 (S'# の非-M_σ-centralizing 元が実は別経路で cover される、or
subH を狭める)、or (b) A=typePA で組んで certainTypeDiffSupported ⊆ typePA0 を得た後、μ差が
typePA0 ∖ honestTypeP2A0Set 上 vanish を別途示す (residue値 chi_j=chi_1 on U^# の議論)。
lane-c の A0-Dade (honestTypeP2A0Set の covering 構造) 知見が要る点。

## 🎯 char-endgame bottleneck synthesis (2026-07-08 lane-b /loop): type-P2 Hypothesis46 が収束点

複数 iteration の精査で、type-P2 char endgame (pins 2/3 + coherence upgrade + (10.7)) が**単一の
type-P2 `Hypothesis46` に collapse** すると確定:

1. **pins 2/3** = `certainTypeDiffSupported` (support) + `certainType_diff_dade_eq` (V-value)、両者
   `Hypothesis46 A L` level (S06)。A=honestTypeP2ASet で組めば pin の honest support を直接 deliver (既述)。
2. **coherence upgrade** (9014 `uniform_prTIred_coherent` = Pf (4.9)) は **§13 に partial ported と判明**
   ([[verify-port-state-by-number-not-coq-name]]): `adjoin_muColumnPair_of_irrFamily`
   (S13_MaximalIII_IV:2336、lane-a) が「coherent 既約族が reducible column pair {μ,μ̄} を absorb」を
   **型-P1 (§12.Hypothesis) で実装** (deep inputs は parametric)。∴「9014 = repo 0」は Coq 名基準の誤り。
   型-P2 版は同機構を **型-P2 Hypothesis46 で instantiate** すれば得られる。
3. **(10.7) `Frob_der1_type2`** (型-P2) も同 Hypothesis46 + coherence に gated (lane-a frontier)。

**✅ type-P2 Hypothesis46 は feasible (A_covers 解決)**: `Hypothesis46` の `subH` は field (`subH ≤ K`,
`W2 ≤ subH`) ゆえ、K=S' 全体でなく **subH = M_σ** を選べば `A_covers` (subH# ⊆ A) が成立
(M_σ# の各元は自身を centralize ⟹ M_σ# ⊆ honestTypeP2ASet)。∴ **honestTypeP2ASet-Dade (dadeHypS0) +
subH=M_σ で `Hypothesis46 (honestTypeP2ASet S) ↥S` が組める**。

**⟹ 次アクション (lane-b、次 iteration)**: parameterized `hypothesis46OfTypePData` を build —
structural 部 (tic = typePData_toTICyclicHypothesis, tic_W1/W2/V reconciliation, toHypothesis = s06S)
は type-uniform に自動構成、type-P2 固有部 (A=honestTypeP2ASet, dade/dade0=lane-c Dades, subH=M_σ,
A_covers) は param。lane-c が dadeHypS0 で instantiate → pins 2/3 + 型-P2 coherence を unblock。
これが char-endgame の最高 leverage。§12 `toHypothesis46` (:1088) が type-P1 template。
