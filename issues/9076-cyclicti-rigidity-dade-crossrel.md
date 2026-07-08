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
  - [ ] **4c-2b″ tame helper 完成 route を全 de-risk (2026-07-08 精査、次 iteration 実行)**:
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
