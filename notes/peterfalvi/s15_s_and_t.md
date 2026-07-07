# Peterfalvi §15: The Subgroups S and T — mini-roadmap (本文最大規模)

**スコープ**: Peterfalvi §15 (pp.75-86, 12 ページ), mmd `04.15_pp_75_86_The_Subgroups_S_and_T.mmd` (365 行).  
**結果数**: 17 結果 ((13.1)-(13.17)) + 1 補足 ((13.18)-(13.19)) = 計 19 個の番号付き内容.  
**形式化先** (予定): `OddOrder/Peterfalvi/S15_SAndT.lean` (将来 subdirectory 分割可能性大)  
**ROADMAP 上の位置**: **Phase 2b 第 6 波** (§10-§14 完成必須, §16 直前).  
**役割**: 最小反例 G の 2 つの特殊最大部分群 S, T の **位数・正規化群・指標論的詳細**. 指標演算を極限まで詰めて §16 の最終矛盾を導く直前準備.

---

## 🗺️ FRONTIER MAP 更新³ (2026-07-07 夜, lane b — (13.4) 組立 landing + gate 2 discharge)

- **✅ (13.4) `lambda_forces_T_caseB` = 実証明** (bare sorry → typed gate、commit 95be831a):
  core 4 bricks (eta_orthonormal / eta_cross_expansion_ne_zero /
  disjoint_conjugatesIntoSet_of_centralizer / inner_induce_induce_eq_zero_of_disjoint) +
  by_contra 本体組立。**gate 2 (p-part) も type-free で discharge 済** (commit 62fb13a8、
  9073 完結の card_T_eq/Frobenius/Hall unlock を消化、hTTypeII threading 不要と確定)。
- **残 gate 2 本** (正本 = issue 9013 追記⁶ + gate 2 完了記録): gate 1 `QD_sharp_centralizer_le_T`
  ((13.2.e)-on-T A₀(T)-TI; S10 DadeSupportHypothesisData は per-point C_G(a) = C_M(a)·H(a) 分解で
  full-TI より弱い — H(a)=1 抽出 or Q_sharp_isTISubset 機構の (QD)^# 拡張が要調査) と gate 3
  `tSide_theta_package_of_not_caseB` ((13.3.b,c)-on-T; **先決 = (13.2.a)-on-T の T-type II∨III
  materialization** [basic_structure の T-mirror] — TypesIIIIIIVSetup T router の type_alt field が要求)。
- 0099 は a の検証込みで全 checkbox 完 (close 可)。

## 🗺️ FRONTIER MAP 更新² (2026-07-07 夕, lane b — 0099 landing 後の §13 原文精査)

- **✅ 0099 HUB 裁定実装 landing** (commit de2642d6): S07 `tau_isometry_diff` を zSupportedSpan 形へ
  in-place 弱化 + (5.7) chain hsuppdiff threading + 4 instantiation swap (S16 分は build-green 原子性で
  b が機械的 swap、issue 0099 に flag)。mixed-degree family で S07.Hypothesis が組めるようになった
  (a の 1019 (9.11) mixed route の構造ブロック解消)。
- **⭐ b 次 frontier = (13.4) `lambda_forces_T_caseB` (S15:2300, sorried)** — 案A (iii) の実装前の
  原文精査で判明 (正本 = issue 9013 追記⁶): (13.4) は **T-side d=1 + v-full を λ-branch で一発供給**
  し、かつ **S-side (13.10) の h2/TT 計数の唯一上流** (S15 内 5 箇所が既に cite)。文書順でも
  (13.10)-dual より上流。campaign 分解 (a)-(d) は 9013 追記⁶ 参照 — T-side gates (θ-dichotomy /
  ν₁-grid / A₀(T)-TI) を精密 sorried producer 1 本に隔離し、b-buildable core (TI 非交差 +
  disjoint-support 直交 + grid 展開) を実証明する precise-reduction パターン。
- T-side (13.10)-dual full cascade ((13.12)/(13.15)-on-T) が真に要るのは case 3 (𝒮 に λ 無し ∧ 𝒯 に
  θ 有り) のみ — 案A (ii)/(iii) の残りはその scope で再評価 (c の engine は S-side (13.15) +
  case 3 の consumer として健在)。

## 🗺️ FRONTIER MAP (2026-07-07, lane b — escape package 完遂後の char pivot 精査)

**escape package (BG Cor 15.9) 完全 sorry-free 化後**の S15_SAndT / S14_MaximalI frontier 実測 (survey は over-optimistic だった):
- **escape-adjacent char = ✅ DONE**: `dadeSupportHypothesisData_honestTypeP2ASet` (S15_SAndT_Setup:754) は
  refactored `typeP2_exists_matched_kappa_hall_pair` + escaping-exclusion 3 本 (`escaping_..._mem_sigmaSharp` /
  `..._isConj_conj_in_M` / `coprime_...`) で **既に実 assembly 済** (sorry-free)。(13.2.e) S-instance dade support 完了。
- **T-side sorry群 (V_inf_centralizer_Q_eq_bot:1887 / complement_inf_Q_structure:3060 / card_Q_eq / tConjugate_fitting_data)**
  = **`reconciled_typePData_T` gated** (T が type-P と assert されず Q=T_F elem abelian 等が無い)。**c が active discharge 中**
  (5→4→2 sorries、直近 commit d3917274/ab75ba94)。b は待ち; c 完遂後に V_inf 等を close。**⚠ survey の "V_inf は 20 行 mirror" は誤り**:
  d_eq_one = 分析的 c_eq_one chain の T-side dual (Singer/two_mul_q_dvd/(13.10)) が要 = 深い。
- **⚠ 訂正 (同 07-07、issue 0098/9013 HUB 裁定を精読)**: 上の "deep b-side = BetaData/grid" は**誤り**。
  hub 裁定で **`betaData_of_grid` (S15_SAndT:3616) は c へ de-scope** (S-side βₛ bridge carve-out、0098 de-scope②)。
  **b の genuine 現行 work = issue 9013 案A**: §13 S-side analytic estimate ((13.10)/(13.11)/(13.14)/(13.15)/
  `c_eq_one`) を **S-side hardcoded (hyp.c 等) → generic type-II maximal subgroup 版に一般化** (c が S/T 両側で
  instantiate)。具体 = (ii) cofactor v∣Singer + (iii) (13.10)-dual analytic ineq。**genericization refactor** ゆえ
  proven S-side が template (typeP2_matched_kappa_hall_pair_of_esetup / typeF_frobenius_of_esetup と同型の抽象化)。
  V_inf (:1885) は b 保持だが c の typeP_pair port gated。次 iteration で 9013 案A に着手。
- ⚠ 旧 notes (2026-07-05 以前) の "issue 2033/3001 が next front" は **stale** (両 issue closed)。

## ✅✅ LIVE STATUS (2026-07-06 loop, lane **b**): (13.12) `c_eq_one` 数値消去を実証明 — bare sorry → 構造残余のみ

- **(13.12) `c_eq_one` (a1dc3748)**: §16 `S16_NonExistenceG` が多所 (198/696/794/1315) で consume する
  on-path producer。**bare `sorry` を撤去し数値消去を実証明**。梃子 = **(13.10) `analytic_inequality`
  が sorry-free assembly になった** (it.2-55 の payoff): `u/c > m·p^(q-1)/q`。これ + (13.2.c) Singer
  u-bound (`basic_structure`, `u ≤ (p^q-1)/(p-1)`) + FPF `c ≥ 2q+1` + (13.11) m-bounds で
  `p=5 ∧ q=3 ∧ c=7` に一意収束。
- **新 `c_eq_one_forces_params` (sorry-free 自己完結 ℚ/ℕ 算術)**: 既存 `caseB_numeric_forces_q_three`
  で q=3 → q=3 bound `m < 3(p³-1)/(c p²(p-1))` で c≥13 排除 (< 49/100) → c=7 → p≥11 排除 (< 399/847)
  → p<11 → **p=7 は exact-m** (m=½−1/(2·3⁶)=½−1/1458 > bound 171/343) で排除 → p=5。
  ※ p=7 は m>49/100 では落ちない (bound≈0.4985>0.49) ため exact-m 必須 (Pf は coprimality 使用、こちらは
  exact-m で回避)。
- **残る唯一の gap = `c_eq_one_final_case` (明示 sorried)**: `p=5∧q=3∧c=7 → False`。u∣31 (case 9.7.b、
  p-1=4 に奇因子なし) → c=7 coprime u → PC normal nilpotent Hall ⊋ P=S_F 矛盾 (typeP_Galois 二分 +
  Fitting-core maximality `Fcore_max`、Coq `FTtypeP_Ind_Fitting_reg_Fcore`)。**深い §13 σ 構造残余、
  次に (13.12) を触るならここだけ**。full build 3929 green / AxiomsCheck OK / sorry 数不変 (bare→isolated 移動)。
- **副産物メモ**: 同じ (13.10)+(13.2.c) 素材は (13.15) `caseB_order_u` (現 opaque-Prop sorried) や
  (13.11) `numeric_bounds` q=3 branch (u/c > (p²-1)/6 部分) にも効く見込み。

## ✅✅ LIVE STATUS (2026-07-05 loop it.46-55, lane **b**): (13.9.a) 完全実証明 + (13.3) campaign 設計

- **it.46-48**: (13.3) producer campaign 設計 (issue 2035) — route A ((9.11) = repo
  `coherent_H0C_commutator`、(6.8)-wired、真 gap = `sibleyTarget_H0C` [multi-session]) /
  route B (Sibley 直接 (S,PC)) は (6.8.a)-split |S|=|PC|·u·q で死亡と判定。
  **⚠ S12 `mkSection11CharacterData` は H0CprimeSupport := ∅ の count-専用 placeholder —
  (9.11)-coherence に流用不可 (Sset:=∅ 型罠)**。
- **it.49 (F1)**: `mu_col_tau1_eta_col_one` field ((13.1.e) μⱼ = Σᵢμᵢⱼ 列和が
  (13.3.a) で Ind-PC-linear + (13.3.c) 列公式の bundle)。
- **it.50-51 (F2)**: `omegaSChar` pair 分解 + 行/列整列 lemmas →
  `tau3W_omegaS_fourcorner_vanish` ((3.4)/(3.5): regular 飽和外で
  1 − η_{i0} − η_{0j} + η_{ij} = 0) → `eta_fourcorner_vanish` field threading。
- **it.52-53 (F3)**: `tau3W_omegaS_row_vanish_of_one_zero` ((3.9.b): η₁₀(x)=0 →
  η_{i0}(x)=0 [i≠0]; 生成元 hom-ext + 原始 q 乗根 + `exists_mapRingEquiv_sigma_omega_pow`
  Galois twist; **i=0 は偽 (η₀₀=1) と発見し Pf 通り制限**) → field threading。
- **it.54**: helper `lambda_tau1_apply_eq_of_not_mem_H_sat`
  (λ^{τ₁}(x) = δΣᵢηᵢ₁(x) off (H^#)^G — (μⱼ−λ) の H^#-台 + TI-off-vanishing)。
  **識別子内 λ は 3 度目の parse 破壊 (疑似 case-h まで誘発) — 徹底禁止**。
- **it.55 (12a2e653)**: **`G0_nonvanishing_dichotomy` (13.9.a) 完全実証明** — regular 枝
  (ω-値 ≠ 0) + 背理枝 (q·η₀₁(x) = q−1 → 整性 + int_dvd で q∣1 矛盾)。issue 2036 close。
- **セッション累計 (it.27-55)**: sorried atom 実証明化 9 本 + (13.2.e)/(3.2.d)/(3.4)(3.5)/
  (3.9.b) の定理化 + soundness 修正 2 件 (lambda_mem / ∅-placeholder caveat)。
- **残 on-path sorry (Setup)**: `character_degree_analysis` (13.3 producer、campaign 2035 —
  sibleyTarget 系が critical) / `lambda_forces_T_caseB` (13.4) / `reconciled_typePData_T`
  (T-side 構造 build 進行中) / T-side atoms (Q-abelian gated) / 数値系
  (numeric_bounds/c_eq_one/caseA/caseB_order_u) / carrier (basic_structure_gated) /
  vestigial (sibleyTarget_S)。

## ✅✅ LIVE STATUS (2026-07-05 loop it.32-45, lane **b**): (13.3)-cluster 実証明化 campaign — (13.6)+(13.7) 全 atom real 化

**成果 (それぞれ commit 済、全 green)**:
- **it.32 (83596b65)**: CharacterDegreeData W-side restate — `lambda_mem : λ ∈ Sset` は spine の
  `Sset := ∅` で構造を uninhabited 化する soundness bug → field 除去 (0-cite 確認)。
  `lambda_irreducible`/`lambda_induced_from_PC_linear` を実 ∃-statement に materialize、
  hlam 引数 13 署名を全廃 (field が証明を運ぶ)。
- **it.33**: (13.3.c)/τ₁ 意味論の設計 (issue 2034) — Pf 原文精読で cluster atom 5 本の要求確定。
- **it.34 (116d139d)**: Hypothesis76 に `zeta_family_cover` field + `hypothesis76OfDadeTrivialBase`
  (ζ₀ = Ind 1_H pin)。**tactic-haveI は instance 本体喪失で defeq 切断 → letI** の再確認。
- **it.35 (f8ab92a9)**: kernel descent `mem_characterKernel_of_mem_characterKernel_induce`
  (Mackey orbit + 三角等号 keystone) + P-non-kernel conjunct。
- **it.36 (6ededdef)**: `exists_lambda_family_index` 実証明 (cover + trivial-base + descent)。
- **it.37 (3a541099)**: τ₁ fields 3 本 (extends-Ind/isometry/ZIrr) + `lambda_tau1_norm_one` 実証明。
- **it.38 (fe51f2be)**: TI-induce 値公式 2 本 (`IsTISubset.induce_apply_of_mem_conj` +
  off-saturation; 9011 拡張)。
- **it.39 (af545610)**: **`H_sharp_tau_eq_induce`** — Pf (13.2.e)「τ = Ind_S^G」定理化。
- **it.40 (6c7a0237)**: **`lambda_tau1_cCoeff` 完全実証明** → `exists_lambda_index` 全 real。
  Hypothesis76 に `zeta_injective`。**spelling 交差は set-fvar + 単発 rfl → rw 構文 transport**
  (isDefEq 爆発回避)、instance 橋 = h.trans congr!/convert-using-1。
- **it.41 (0826c5bc)**: `lambda_tau1_apply_mul_eq_zero` real assembly — 新 field
  `tau1S_induce_inner_eta` ((4.1)/(5.3.b)) + (3.2.d) hyp-level atom。**(3.2.d) は S05
  `eq_zero_of_mem_V_of_inner_chiFam_eq_zero` に proven と発見**。
- **it.42 (814e4f06)**: (3.2.d) spine supply — `exists_omegaS_eq_omega` (**counting exhaustion**:
  omegaS 族 = pq 個 distinct 線形指標 = 全部) + `tau3W_omegaS_complete_vanish`。
- **it.43 (f654b6f4)**: `eta_complete_vanish` field threading (3 構造+3 wiring) →
  `vanish_of_inner_eta_eq_zero` 実証明化。**(13.6) λ-package 全 chain real**。
- **it.44 (05bc7cfe)**: `eta10_cCoeff_orthogonal` 実証明 (全消滅版 cCoeff 計算) + chars param を
  η-chain 4 署名貫通。**(13.7) も全 real**。
- **it.45**: vestigial 5 wrapper (tiSubset_character_orthogonality/lambda_norm_lower/
  eta10_norm_lower/eta01_norm_lower/global_character_bound + TISubsetOrthogonalityData) retire
  (0-cite 検証済)。

**現況 Setup 残 sorry (on-path)**: `character_degree_analysis` (13.3 — τ₁-fields の構成 =
(4.9)/(5.8) coherence; S05_SigmaTrichotomy に (5.8) core あり) / `lambda_forces_T_caseB` (13.4) /
`reconciled_typePData_T` / T-side `exists_muT_index`+`exists_etaT_alphaFun_one_int` (Q-abelian
gated) / `G0_nonvanishing_dichotomy` (13.9.a) / 数値系 (numeric_bounds/c_eq_one/caseA/caseB_order_u)
/ gated (basic_structure_gated) / vestigial (sibleyTarget_S)。
**次 = 文書順で (13.3) `character_degree_analysis`** — τ₁ 構成の設計 ((4.9)/(5.8) 経由、
2034 の残 checklist と一体)。

## ✅ LIVE STATUS (2026-07-05 loop it.27-31, lane **b**): issue 2033 完遂 — ω (3.3) 意味論貫通 + (1.10)-合同層 real 化

- **2033 threading (it.27-28, commit 9c79ee63)**: `TICyclicHypothesis.omega` は hom-パラメータ化済 →
  field は 5 本 (omega_mul / col-0 W₂-自明 / row-0 W₁-自明 / W₁ q-乗根 / W₂ p-乗根)。spine supply 5 本
  実証明 (`omegaS_mul` 等 — S06 chiColumn の hom-性 + `chi2enum_zero`/`w1CharEquiv_zero`/
  `pow_card_eq_one'`) + Section16Inputs/CharacterData/S15.Hypothesis 3 構造貫通。
- **(13.7) atom real 化 (it.29, commit 688e9c93)**: `eta10_alphaCF_one_ne_zero` 実証明 — helper
  `mul_notMem_W1_union_W2` + `eta10_apply_sub_one_integral` (η₁₀(y) ≡ 1 mod 1−ε: (1.10.a) =
  `exists_integral_apply_sub_of_commute`、τ₃-regular + 2033 fields で ω₁₀(xy) = ω₁₀(x) = ε^k)。
  α(1)=0 なら (1.10.b) `int_dvd_of_one_sub_primRoot_dvd` で q∣1 矛盾。残 gate =
  `eta10_cCoeff_orthogonal` のみ。`W2_le_P`+`pgroup_le_of_normal_coprime_index` を Setup に relocate。
- **(13.6) atom real 化 (it.30, commit bd1f44aa)**: `exists_lambda_alphaFun_one_qb` 実 assembly —
  `lambda_apply_mul_eq_zero` 実証明 (q ∣ ord(xy) vs q ∤ |H|)、point formula (c₁=1, ‖ζ₁‖²=1) で
  α(x) = λ^{τ₁}(x) − λ(x)、(1.10.a) G-level + ↥S-level 二本 (λ ∈ ZIrr ↥S は `zeta_induced` から実導出)。
  新 sorried sub-atom `lambda_tau1_apply_mul_eq_zero` ((3.2.d)/(5.3.b)/(5.5) gate)。
- **α(1) ∈ ℤ real 化 (it.31, commit 4d076d23)**: `lambda_alphaFun_one_int` 完全実証明 —
  `H_sharp_cCoeff_int` 一般化 (eta10 版は 1 行 cite に refactor) + inertia 恒等式
  (`card_mul_inner_self_induce_eq_card_inertia`: |K|·‖ζ‖² = |I| → ζᵢ(1)/‖ζᵢ‖² = [S:Iᵢ]) +
  `(Int.castRingHom ℂ).range` の `Subring.sum_mem` (filter を restate しない = instance-trap 回避)。
  **技術ノート: FiniteInduce scoped Invertible と手動 invertibleOfNonzero の二重供給は induce の
  instance 不一致を起こす — scoped に任せる (haveI しない)**。
- **現況**: (13.5)–(13.10) norm cascade の (1.10)-合同層は全 real。残 sorried atom =
  (13.3)-cluster (`character_degree_analysis` / `exists_lambda_index` / `lambda_tau1_norm_one` /
  `lambda_tau1_apply_mul_eq_zero` / `eta10_cCoeff_orthogonal`) + T-side (Q-abelian gated) +
  `G0_nonvanishing_dichotomy` + `lambda_forces_T_caseB` + `reconciled_typePData_T`。
  次 frontier = (13.3)-cluster 設計精読 (tau1S の W-side routing は s16_w4_char_cascade.md
  2026-07-02 hub section が正本)。

## ✅ LIVE STATUS (2026-07-05 後半, lane **b** — (13.10) 4 producer 全 discharge、residual = 教科書番号 5 本)

### cont.⁴ (07-05 loop it.20-25): (13.5)-package 3 本全 real 化 — cascade 構造完成

- **T-side ρ-machinery mirror** (`0c541512`): Q_sharp_dadeHypothesis → hconj → h71 → h76
  (proven Q_sharp_isTISubset から、全て実証明)
- **(13.5.a) machinery generic 化** (`3ba0347b` + 後続): 任意 H76 + P' 上の point formula
  (kernel-only + distinguished-i₁)、alphaFun cluster、F-inflation、**generic P'-kernel 直交性**
  (`hypothesis76_zeta_inner_alphaFun_eq_zero`) — S/T 両側の共通基盤
- **`exists_caseB_data_eta10_T` 実 assembly** (`88fd43a0`): ζ = (1/p)μ′ 正規化、
  firstTerm = (1/p²)(|T|p−(pv)²) = |T′|−v² (card_T_eq_deriv_mul_p)、全部品 1-line cite

**cascade 最終構造**: analytic_inequality (13.10、実定理) ← 4 producer (全実 assembly) ←
sharp 3 本 (全 engine assembly) ← (13.5)-package 3 本 (全実 assembly) ← **原子 6 fact**:
`exists_lambda_index`/`lambda_tau1_norm_one` ((13.3)-同定)、`eta10_cCoeff_orthogonal`/
`exists_muT_index` ((13.3.c)-直交)、`exists_lambda_alphaFun_one_qb`/
`eta10_alphaCF_one_ne_zero` ((1.10)-合同 = **issue 2033**)、`exists_etaT_alphaFun_one_int`
(Q-abelian gated) + (13.3)/(13.4)/dichotomy/reconciled。
**b の次の ungated front = issue 2033 の supply 側** (ω-因子分解 field threading —
3002 パターン、lane-a file への additive 編集権は 07-05 裁定済)。

### cont.³ (07-05 loop it.14-19): λ-package 実 assembly + 直交性 real 化、gate-map 確定

- **`exists_caseB_data_lambda` 実 assembly** (`0dc592c0`): atom 3 本 (exists_lambda_index /
  lambda_alphaFun_inner_zero / exists_lambda_alphaFun_one_qb) — proven の H_sharp_point_formula
  が c̄/‖ζ‖² = 1 で collapse。
- **orbit 直交性 + inner-zero 実証明** (`1c756d7a`/`f9a97bdf`): lambda_alphaFun_inner_zero は
  **S-level shortcut** (λ は K 外で消える → filter-和を全和に延長 → distinct-fibre induced 直交
  `inner_induce_eq_zero_of_not_conj`) で K-side 迂回して完全 real。restrict-分解抽出 2 本も追加。
- **確定 gate-map (両 package 残 4 atom)**: `exists_lambda_index` ((13.3): λ = ζ_{i₁}、c=1、
  middle 直交 — S-coherence) / `eta10_cCoeff_orthogonal` ((13.3.c)+(5.3.b): η ⊥ S^{τ₁}) /
  **(1.10)-合同 2 本 → issue 2033** (ω の W₁×W₂ 因子分解 field 未 threading が真の gate;
  α(1) = η₁₀(x) on W₂# までは real 到達可能)。
- **次の ungated 実仕事**: T-side (13.8) package 用の ρ-machinery mirror
  (Q_sharp_isTISubset proven → Q_sharp_dadeHypothesis → hypothesis76 mirror)。

### cont.² (07-05 loop it.5-13): (13.5) 整数性 unit 完遂 — (13.7) package 実 assembly、残 grid-atom 2 本

H-side 整数性 unit を完遂 (`d24c7b9c`〜`d1be0c6e`、全て実証明):
- **Mackey orbit-sum** `card_smul_restrict_induce_eq_inertia_smul_orbitSum` (InducedIrreducible) +
  `orbitSum_mem_ZIrr`
- **`Hypothesis76.zeta_induced` field 追加** (S09、additive; 唯一の constructor OfFamily は
  term-mode 化して充足)。canonical instance = FiniteInduce instance が同一項で bridge 不要
- **(1/‖ζᵢ‖²)·Res ζᵢ ∈ ℤ[Irr K]** → **α|_K ∈ ℤ[Irr K]** (cᵢ ∈ ℤ 下) → ⟨φ,φ⟩ ∈ ℕ /
  φ(1) ∈ ℤ 抽出補題
- **`eta10_cCoeff_int` 実証明**: FullDadeIsometryData.preserves_virtualCharacters ((2.10)、
  既存発見!) + dᵢ = 1 (K abelian → θ linear) 経由
- **`H_mulCommutative`** (H = PC abelian、carrier 実導出) + Parseval bookkeeping
- **`exists_caseB_data_eta10` 実 assembly 完成**: 単一 F : Finset ↥S 上で全 bookkeeping。
  **教訓: 異なる補題の baked spelling への rw-join は不可視の Fintype/DecidablePred instance
  差で失敗する** (classical タクティクの fvar-instance も割れ要因) → **F-引数化 wrapper**
  (explicit Finset + mem-iff 特性、instance-free interface) が決定的解 —
  `sum_finset_sharp_normSq_eq` / `sum_finset_sharp_transport` /
  `H_sharp_alphaFun_inflation_finset`

**(13.7) chain 現況**: analyticEstimate_eta ← eta10_sharp_norm_lower ← exists_caseB_data_eta10
← **残 atom 2 本のみ**: `eta10_cCoeff_orthogonal` ((13.3.c)/(5.3.b) 直交性) /
`eta10_alphaCF_one_ne_zero` ((1.10)/(3.2.c) 合同)。
**次**: λ-side (13.6) package の同型 atomization (`exists_lambda_index` の設計 —
「λ = ζ_{i₁} with cCoeff = 1」の (13.3)-gated 同定) と T-side (13.8) の横展開。

### cont. (07-05 loop it.2-4): sharp 3 本 engine wiring 完了 + (13.5.a/c) 具体化、次 = H-side 整数性

- **(13.6)/(13.7)/(13.8-T) sharp 全て engine assembly 化** (`631c4538`/`d8ea58d0`): 残 =
  (13.5)-package producer 3 本 (`exists_caseB_data_lambda` / `_eta10` / `_eta10_T`)。
  `two_mul_u_le`/`two_mul_v_le` 実証明 (u/v-bound は 9000 非依存に)。engine 適用の
  DecidableEq instance 差は convert+congr! bridge (Subtype vs Classical)。
- **(13.5.a) a=0 variant + 具体 α 実証明** (`f4afa84a`): `H_sharp_point_formula_kernel_only` /
  `H_sharp_alphaFun` (P-kernel tail) / `_const_on_P` / `_eq_zero_of_not_mem` /
  `_inflation` ((13.5.c) 実証明)。
- **次 unit = H-side 整数性** (eta10-package の hs/hParseval/hn/habelian)。ルート確定済
  (部品は全て既存): (i) cᵢ ∈ ℤ ← `inner_mem_ZIrr_int` (InducedCharacter:855) + τψᵢ ∈ ZIrr;
  (ii) Res ζᵢ/‖ζᵢ‖² = orbit-sum of θᵢ ← `card_smul_restrict_induce` (Mackey, |H|·Res∘Ind =
  Σ_x θ^{x⁻¹}) + `card_mul_inner_self_induce_eq_card_inertia` (InducedIrreducible:172、
  |H|‖Indθ‖² = |inertia|) + 既約直交で orbit 集計; (iii) α ∈ ℤ[Irr H] → ⟨α,α⟩ ∈ ℕ、
  α(1) ∈ ℤ (span induction、isIntegral_apply_of_mem_ZIrr の 1-値版); (iv) habelian ←
  `exists_zsmul_irreducibleCharacter_of_inner_self_one` + H abelian (13.2.a,b) linear。
  (1.10) 合同 α(1) ≡ 1 mod q (n≥1 用) のみ grid-gated で sorried のまま。


3002 threading の consumer wiring を完遂。`analyticInequalityEstimates` (旧 terminal) は
**4 atom producer から sorry-free assembly** になり、4 producer も全て実 assembly 化:

- **(13.9.a) `analyticCounting_disjointCover` — 完全実証明** (sorry 0)。基盤を新設:
  shared `IsTISubset.sum_conjClassSet` (issue **9011**、TI saturation の weighted 和 transport;
  card 版 `S14.ncard_conjClassSet_of_isTISubset` は既存だった) + S15 counting layer
  (`p_ne_q` / `Q_sharp_isTISubset` (T-side TI、type V は vd≠1 で排除) / `q_not_dvd_card_H` /
  `disjoint_conjClassSet_sharp_H_Q` / 4-piece split `sum_univ_split` / cardinality 恒等式
  `card_S_val`・`card_T_eq` 等 — 全部実証明)。
- **(13.6) `analyticEstimate_lambda` — 実 assembly**: global Parseval (`global_normSq_split`) +
  `G0Finset_cyclicClosed` + Galois 整数性 (normSqSumQ atom) + `card_S_val`。
- **(13.7+8) `analyticEstimate_eta` — 実 assembly**: η₁₀ norm-one facts は **完全 real**
  (`eta10_mem_ZIrr`/`eta10_inner_self_one` — 3002 grid fields の payoff)。
- **(13.9.b) `analyticEstimate_galois` — 実 assembly**: [Is] 3.14 の ZIrr 版
  (product/sum form、GaloisRationalInteger 拡張) + 非零 locus cyclic-closure (Pf (1.9.b)) 全 real。

**残 sorry (S15 cascade 関連) = 教科書番号どおりの faithful producer 5 本 + 既存 3 本**:
`lambda_tau1_norm_one` ((13.2.d)/(13.3) λτ₁ coherence facts) /
`lambda_tau1_sharp_norm_lower` (**13.6 textbook** — (13.5) ρ-engine wiring + 9000 u-bound) /
`eta10_sharp_norm_lower` (**13.7 textbook**) / `eta10_Qsharp_norm_lower` (**13.8-for-T**) /
`G0_nonvanishing_dichotomy` (**13.9.a textbook** — (13.3.c)+grid gated) + 既存
`character_degree_analysis` (13.3) / `lambda_forces_T_caseB` (13.4、|Q|=q^p conjunct を enrich) /
`reconciled_typePData_T` (Setup へ relocation 済)。
**次の frontier (文書順)**: (13.6) sharp = `caseB_lambda_norm_bound` engine への (13.5.a) point
formula 供給 (H_sharp_hypothesis76 の chiRho_explicit_formula 適用 + (13.2.e) τ-agreement)、
u-bound は 9000 sorried-cite。CharacterDegreeData に `lambda_induced_from_PC_linear_holds`
((13.3.b) WLOG per (13.12) 証明) を追加済。

## ✅ LIVE STATUS (2026-07-05, lane **b** 再開 — frontier 全数の gate を ENGINE レベルで確定)

再開時 `git merge main` (HEAD..main 6→0)。b 所有 territory の全 sorry を精査し、gate の所在を
**engine レベルまで**確定 (過去の「gated」ラベルの実 gate 検証):

- **coherence infra 完了**: `S07_Coherence*` / `S08_PGroupReduction` / `S09_CertificateDischarge` は
  実 sorry **0** (comment-strip 検証)。b の group/coherence 貢献は出し尽くし。
- **§15 char cascade = lane-a upstream に comprehensively gated** (closed-sorry solo work 枯渇):
  - **norm cascade の真の terminal = `analyticInequalityEstimates` (S15_SAndT_Setup:1287)**。四 estimate
    (13.6-13.9) を real inequality で述べるが body は engine 未接続の裸 `sorry` (:1298)。中間 wrapper
    `lambda_norm_lower`/`eta10_norm_lower`/`eta01_norm_lower`/`global_character_bound` (1242-1266) は
    `∃ data:NormCascadeData, data.<opaqueProp>` の **vacuous placeholder + unconsumed** (analytic_inequality は
    これらを経由せず analyticInequalityEstimates を直接 cite)。
  - **engine は完備 sorry-free**: `caseB_lambda_norm_bound` (:840) / `caseB_eta_norm_bound` (:911) /
    `caseB_eta01_norm_core` (:935) は grid 性質を **明示仮説** (hvanish/hinner/hχ 点公式/hParseval/hs 整数性/
    hInflation(13.5.c)/hu(2u≤|P|-1)/habelian) で取り real norm bound を産む。
  - **∴ 1298 の実 gate = これら仮説を hyp.eta/omega/tau3 に対して供給すること**。bare field ゆえ供給不能。
    threading (S15.Hypothesis field 追加 + FeitThompson.lean 供給) 要 = **issue 3002 (lane a)**。加えて
    `hu` = **issue 9000** の u-bound (σ-theory engine 完備、残 block 分解 `Hbar=⊕H1^w`+hconst assembly は
    lane a §9/§11)。arithmetic shortcut 不可を検証: 四 estimate の abstract-ℚ 充足可能性 ⟺ C1≤C2+C3 ⟺
    analytic inequality 自体 (循環)。
  - `c_eq_one` (13.12, S16 が **16× cite** = 最高価値) の残 sorry (:1791) = numeric(13.11)+typeP_Galois の
    PC-Hall 矛盾。numeric q=3 (:1771) も p≥5 (=q<p, S16 downstream) gated。`P_elementaryAbelian` (:351) は
    (11.7)=`S13.H_elementaryAbelian` が **type III/IV 用で signature 不一致** (S は type-P₂=type II) ゆえ直接
    cite 不可。
- **§12 witness route (S14 5043/5064/5135/6425/6468) は endgame 用だが現 `feitThompson` path 外**
  (AxiomsCheck 6672/6789 確認: feitThompson の唯一 bare sorry = a の 11.8 via scaffold §16;
  `theorem88_caseB_holds` は「まだ axiom-clean でない」= 将来 endgame 用)。fresh Explore trace:
  `not_all_maximal_typeI`→`typeI_frobenius`(6592)→`pi_empty`→counterexample route→`witness_L_frobenius`。
  witness 3 本 (5043/5064/5135) は missing §8 facts (8.16/8.6.a/11.9.c/8.3/12.8) に **genuine BLOCKED**;
  6425 のみ (7.8) cite で provable だが S14=b cite-only・off b-focus。

**b-solo で残る tractable = 「grid obligation を GridProperties carrier + sorried producer に明示 isolate +
engine wiring」の incremental de-opacify (closed でなく isolate)。** これは reallocation 自身の flag
「下流 char cluster (b) は独立 ungated 深さ無く upstream (a) に stall」の実例。9000 note の規定通り
**cluster-blocked→cross-cluster = hub/user 裁定**案件ゆえ、2026-07-05 に user へ方針確認 (unblock 選択肢
A=3002 threading 横断 / B=b-side GridProperties wiring 先行 / C=再配分) を提示 → user が session 区切りを選択。
**次セッションはこの gate map を再導出せず、選ばれた方針から着手**。

---

## ✅ LIVE STATUS (2026-07-04, lane **b** 再開 — 07-04 reallocation で S15 が c→b 移管後の初手)

**b が S15_SAndT_Setup + S15_SAndT を所有** (07-04 3 レーン再々編、focus = ON-PATH (13.9)-(13.19)
parity/構造/norm)。再開時に `git merge main` (HEAD..main=1→0)、frontier 全数をコード検証。

### ✅ landed: (13.10) `analytic_inequality` de-opacify (commit `f17fdbcd`)
実 conclusion `u/c > m·p^(q-1)/q` を **bare sorry → 実定理** に。sorry-free 算術核
`analytic_inequality_arith` に、4 estimates を carry する faithful producer
`analyticInequalityEstimates` ((13.6)-(13.9)) を供給して discharge。full build 3916 green。
sorry は producer に isolate (net ±0) だが (13.10) 出力が real theorem 化 (下流 c_eq_one/numeric が cite 可)。

### frontier 精査結論 — b の §15 は「一律 gated」でない (要ニュアンス、過去の pessimism 訂正)
コード検証で各 sorry の gate を確定 (「上流待ち」の誤ラベルでなく実 gate):
- **(13.10) 出力**: ✅ de-opacify 済。完全 discharge には η-estimates + λ-estimates + u-bound が要る (下記)。
- **⚠⚠ 訂正 (同 07-04 loop、初回 claim は誤り)**: 「η-side は hyp.W から honest W-grid 新規構成で ungated」は
  **誤り**。理由: **spine (`FeitThompson.lean:1319` `omegaS`) が既に honest grid を `mp.certainTypeS.sdiffTICyclicHypothesis`
  (`S05.TICyclicHypothesis`) から構成済**。だが `S15.Hypothesis` は grid を **bare field** で持ち、`mp`/certainType/
  TICyclicHypothesis への **structural link を一切 carry しない** (field 精査: omega/eta/tau3/mu/nu/delta は
  bare、関係 field は `eta_eq_tau_omega`/`mu_definition`/`nu_definition` のみ = 直交性/isometry 無し)。
  ⟹ b が **fresh grid を組んでも hyp.omega と同定不能** (link 無し) → cascade は hyp の λ (CharacterDegreeData)・
  (13.5) machinery に tie されるので fresh grid では (13.10)-about-hyp を証明できない。**∴ η-side も含め §15 cascade
  全体が issue 3002 (grid property を hyp に threading、a の FeitThompson) に uniformly gated**。
- **honest grid は spine に既存**: `omegaS` orthonormal は S05:733/740、τ isometry は S07。issue 3002 の a-side
  threading = 「omegaS の直交性 + tau3W isometry を S15.Hypothesis/Section16Inputs の新 field に供給」= 機械的
  (grid は既に proven、新規構成不要)。
- **u-bound (13.2.c) `2u≤|P|-1`**: issue 9000 (typeP_Galois、hub/a dedup 中)。

**⟹ b の §15 cascade に solo build-green な深 math は無い** (uniformly gated on issue 3002 [a] + 9000 [hub/a])。
tractable solo = faithful-producer de-opacify (grid obligation を isolate、consumer-side): `GridProperties` carrier +
sorried producer で全 wrapper を engine から実証明 → grid property を単一 producer に集約 (a の threading と pair)。
**最高 leverage = issue 3002 の a-side threading** (b cascade 全体 unblock)。詳細 = issue 3002 の 07-04 b 訂正節。

### ⚠⚠ 2026-07-04 loop 続報 — 【訂正】「comprehensively gated」は誤り。§12 は substantial-but-UNGATED
**先の「§12+§15 とも a に comprehensive gated」結論は誤り** (ユーザー指摘 "cite して進められないの?" + 再検証)。
2 つの誤り: (1) **stale な issue 9003 (07-02) の「§8-§11 は grep 不在」を鵜呑み**にした。実際は多くが**その後
形式化済**: `no_typeV_maximal`/`typeV_forces_coherence` (10.10, S12:3742/3726)・`typeI_or_typeII_centralizer_unique`
(8.16, S10:407)・`typeII_centralizer_U_eq_bot` (11.6, S11:530)・`typeIIIorIV_W2_prime` (S11:588)・
`final_typeIII_conclusions` (S13:483) 等。(2) **cite-sorried-upstream モデルを適用しなかった** (欠けている
§8-§11 は consumer が sorried で pin して cite すればよい = 真の gate でない)。
- **∴ (12.10) `witness_L_isTypeI` [+ 12.11/12.12 downstream] は substantial-but-UNGATED** (available §8-§11 を
  cite + 型解析 assembly で証明可; 欠け分は sorried pin)。b の genuine 構造 work。**現在 subagent が着手中**。
- **§15 cascade**: b-solo build-green は **cite-sorried-producer** で可 ((13.10) `analytic_inequality` が先例、
  f17fdbcd)。⚠ **field-approach (S15.Hypothesis に grid property field 追加) は build-red**:
  `sectionSixteenHypothesis_of_inputs` に `#assert_only_allowed_axioms` (AxiomsCheck.lean:3221) があり、
  sorried-default field が a の constructor を sorryAx 依存にして assertion を破る。**⟹ 9009 HUB 裁定の
  「sorried default で build-green」機構は不成立** (a が値 supply + assertion 調整するまで field 追加不可)。
  b-solo は producer 経由。詳細 = issue 9009 の訂正。
- b の done: (12.6) coherence tower (9003) / (13.9.b) core (9c9b6ad4) / (13.10) de-opacify (f17fdbcd)。
- **教訓**: 「gated」と結論する前に (a) 上流 signature を**今**再 grep (notes の gate map は rot する)、
  (b) cite-sorried モデルを適用せよ ([[feedback-cite-sorried-lemmas-if-signature-correct]]
  [[verify-port-state-by-number-not-coq-name]] [[feedback-dont-mislabel-formalization-as-research]])。

---

## ✅✅ MILESTONE (2026-07-01, lane c): (13.16) W₂-side が **gate ゼロで完全 proven**

**(13.16) W₂-confinement 全体が sorry-free** (S15 sorry 12→10、full build 3890 green, AxiomsCheck OK):
- `normalizer_W2_le_S` (BG 15.7 TI reduction) / `normalizer_W2_within_S` (群 Dedekind) /
  `normalizer_W2` (N=C=P⊔W₁) — 全 proven。
- 核 `normalizer_U_inf_W2_eq_bot : U⊓N(W₂)=⊥` — **完全 proven**:
  - crux `normalizer_U_inf_W2_le_centralizer_W2 : K≤C(W₂)` (coprime FPF lifting, Isaacs Cor 3.28)
    + 2 入力 `centralizer_W1_inf_U_eq_bot` (Frobenius FPF) / `conj_W1_mem_centralizer_W2` (W₁-triviality)。
  - assembly `normalizer_U_inf_W2_eq_bot_of_data` (Gorenstein 2.3 `fitting_coprime_abelian_decomp`
    + Wielandt `frobenius_kernel_centralizes_of_complement_fpf`)。
  - gate 2 つとも解消: **hcop** = `coprime_card_P_card_UW1` (ungated: P Hall + U⋊W₁ complement で
    Coprime|P||U⋊W₁| 実証明)、**hrec** = Hypothesis field `Sdata_W2_eq` (§16-carrier、session 中に
    main で追加、constructor が supply)。
- **副産物**: `P_W1_structure` (13.17.c S-side: W₁≤N(P) ∧ P⊓W₁=⊥ ∧ q∤|P|) も coprime_card_P_card_UW1
  経由で ungated 実証明。

### 残 §13.16-17 frontier (C レーン)
- **W₁-side `normalizer_W1_structure` (S15:158)** = W₂-side の S↔T,P↔Q,U↔V,W₁↔W₂ dual。
  Hypothesis に **T-side type-P 構造 (Tdata) が無い**ため gated (T が type-P と assert されていない;
  Q=T_F elementary abelian 等が無い)。dualize には T-side basic_structure 構築が要 (issue 3001)。
- T-side sorry群 (`reconciled_typePData_T`/`card_Q_eq`/`tConjugate_fitting_data`/
  `complement_inf_Q_structure`) — 同 T-side gated。
- `card_LF_coprime_pq` — BG Theorem E (`bgTheoremE_cover_data`, owner=F) gated。
- 13.17 char (`beta_support_norm_and_remainder`/`typeI_orthogonality_dichotomy`) — char cascade。
- **⚠ 2026-07-02 更新 (現 tip)**: `normalizer_W1_structure` (S15:2045) / `card_Q_eq` (S15:2270) /
  `tConjugate_fitting_data` (S15:2330) は **PROVEN**。S15_SAndT.lean の実残 sorry は **8** =
  `reconciled_typePData_T` / `Q_elementaryAbelian_T` / `V_inf_centralizer_Q_eq_bot` /
  `card_LF_coprime_pq` / `complement_inf_Q_structure` / `complement_inf_P_structure` /
  `beta_support_norm_and_remainder` / `typeI_orthogonality_dichotomy`。
  live log = [`s16_w4_char_cascade.md`](s16_w4_char_cascade.md) cont.⁴⁰+。

---

## ✅ LIVE STATUS (2026-07-01, lane c = (13.16) W₂-confinement — Dedekind 還元 landed + 核プラン検証)

**このセッションの landing (build-green, 3856 jobs)**:
1. `C_eq_bot` / `U_inf_centralizer_P_eq_bot` — (13.12) `c=1` finish を再利用補題に抽出
   (`C = U ⊓ C_G(P) = ⊥`)。S16 のインライン重複を集約。
2. **`normalizer_W2_within_S` 実証明** — (13.16) W₂-side residual `N_G(W₂) ⊓ S ≤ P ⊔ W₁` を
   単一の群論核 `normalizer_U_inf_W2_eq_bot : U ⊓ N_G(W₂) = ⊥` に**群 Dedekind** で還元:
   - Sub-goal A (`BG.Ch3.S12.eq_sup_inf_of_le_normalizer`): `M' ⊓ N_G(W₂) = P`
     (`M'=derivedInG S=P⊔U`, `U ≤ N_G(P)`, `(M'⊓N)⊓U = U⊓N = ⊥`)。
   - Sub-goal B (`coe_mul_of_left_le_normalizer_right`): `S = W₁·M'` で `g=w·m` 分解 →
     `m ∈ M'⊓N_G(W₂) = P` → `g ∈ P⊔W₁`。
   - ⚠ 一般群の部分群束は非 modular (`IsModularLattice (Subgroup ·)` は CommGroup 限定) ゆえ
     lattice modular law 不可 → 群論的 Dedekind (正規性) を使用。

### ▶▶ 核 `normalizer_U_inf_W2_eq_bot : U ⊓ N_G(W₂) = ⊥` の**検証済フル証明プラン** (次チャンク, 新 infra 不要)

`K := U ⊓ N_G(W₂)` と置く。**全 cited 補題は repo に在庫確認済** (下記)。核は ~200 行の
MulAut plumbing だが新規 infra は不要。2 段構成:

**① crux (ungated, 抽象 W₂ について): `K ≤ C_G(W₂)` — ✅ PROVEN
(`normalizer_U_inf_W2_le_centralizer_W2`)**。`coprime_fixedPoints_quotient` (Isaacs Cor 3.28) で:
- `W₁` は abelian `U` に conjugation で coprime 作用 (`φ:↥W₁→MulAut ↥U`; coprime は
  `UW1_frobenius.coprime_card_kernel_complement`)、fixed points `C_U(W₁) = ⊥`
  (✅ `centralizer_W1_inf_U_eq_bot`)。
- `N := C_U(W₂)` は abelian U で normal・W₁-invariant。`g∈K` の coset は W₁-fixed
  (✅ `conj_W1_mem_centralizer_W2`: `g⁻¹(wgw⁻¹)∈C(W₂)`) → Cor 3.28 で W₁-fixed 代表元
  `c∈C_U(W₁)=⊥` → `c=1` → `g∈C_G(W₂)`。
- **3 補題全て build-green・ungated で landing 済** (commit `8614fad4`/`338d7a92`/`eeb212ed`)。

**② assembly (`K≤C_G(W₂)` 前提)** — 2 つの Coq 比の simplification:
- **full `U⋊W₁` Frobenius を使う** (`K⋊W₁` でなく) → `Frobenius_subl` 不要。U abelian ⟹
  `U ≤ N_G(⁅P,K⁆)`、Wielandt (`frobenius_kernel_centralizes_of_complement_fpf`, `N:=⁅P,K⁆`) で
  `U ≤ C_G(⁅P,K⁆)`。
- **Gorenstein Thm 2.3** `P = C_P(K) × ⁅P,K⁆` (`fixedPoints_inf_actionCommutator_eq_bot_of_abelian`,
  `CoprimeAbelianPGroup`/`Ch04`) で Maschke complement 構築を回避。
- FPF `C_{⁅P,K⁆}(W₁) = ⁅P,K⁆ ⊓ C_P(W₁) = ⁅P,K⁆ ⊓ W₂ ⊆ ⁅P,K⁆ ⊓ C_P(K) = ⊥` — `W₂≤C_P(K)` (crux) +
  **regularity `C_P(W₁)=W₂`** (`TypePData.centralizer_W1`)。
- ⁅P,K⁆ ≤ C_P(U) ≤ C_P(K) → `⁅P,K⁆ ⊆ C_P(K)⊓⁅P,K⁆ = ⊥` → `K≤C_G(P)` → `K ≤ U⊓C_G(P) = ⊥`
  (`U_inf_centralizer_P_eq_bot`)。

⚠ **唯一の外部 gate = `Sdata.W2 = W2` reconciliation** (assembly の regularity 段のみ)。Hypothesis
field でなく明示仮説 (`S15_SAndT_Setup.lean:349` が `(hSdataW2 : Sdata.W2 = W2)` で取る形)。§16-carrier
content (`Section16TypePStructure`, issue 3001 隣接)。crux ① は hyp.W₂ 直接ゆえ ungated。
⟹ 実装時は `Sdata.W2 = W2` を仮説引数に取る engine か、sorried-cite で discharge。

**在庫確認済** (grep 実証): `coprime_fixedPoints_quotient` ✅ / `frobenius_kernel_centralizes_of_complement_fpf`
✅ (docstring が「Pf (13.16) で使う」と明記) / `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` ✅ /
`BasicStructureData.{UW1_frobenius,U_commutative,P_elementaryAbelian}` ✅ / `TypePData.centralizer_W1` ✅ /
`U_inf_centralizer_P_eq_bot` ✅。**未在庫: なし** (Maschke complement と Frobenius_subl は上記 2
simplification で回避)。

### 残 (13.16) W₁-side: `normalizer_W1_structure` (S15:158, sorry)
`W₁≤Q ∧ Q abelian ∧ N_G(W₁)≤Q⊔W₂` の 3-tuple。前 2 conjunct は **T-side dual (issue 3001 の Q/Sdata_T
gated)**、第 3 は上記核の W₁↔W₂ dual。W₂-side (核) を先に閉じてから T-side carrier 経由で dual 化推奨。

---

## ✅ LIVE STATUS (2026-07-01, lane d = γ 上流 S15_SAndT_Setup 再配分後の初手)

**issue 0092 で lane d は S15_SAndT_Setup へ再配分** (旧 δ BG§14–16 は FT deliverable 実質完成)。

### ⚠ 重複回避: (13.9.b) [Is] 3.14 数論核は **lane c が並行 landing 済** (共有 infra へ集約)

lane d が同セッションで (13.9.b) の「Galois-invariant 代数的整数 → 有理整数」核
(`∏‖χ(aᵏ)‖²≥1`) を S15_SAndT_Setup に実証明したが、**merge 時に lane c が同核を先に
`OddOrder/Algebra/GaloisRationalInteger.lean` (共有 infra) へ landing 済と判明**
(`a6a532c7`/`35c88da5`)。lane c 版 = `IsCharacter φ` + 一般 cyclic-closed Finset
(`exists_int_prod_character_of_cyclicClosed` / `one_le_prod_normSq_character_of_cyclicClosed`)。
lane d 版は (ZMod n)ˣ-orbit 特殊化ゆえ **冗長 → 除去** (反重複方針)。

- **(13.9.b) consumer は lane c 版を cite せよ**: cyclic class `{aʲ : gcd(j,orderOf a)=1}` は
  coprime-to-|G| power closure を満たす (orderOf a | |G|) ので lane c の `hclosed` に適合。
  λ^{τ₁} は Dade 等距の像 = ±genuine character ゆえ `‖λ^{τ₁}‖²=‖θ‖²` で `IsCharacter` 版適用可。
- **教訓 (coordination)**: 2026-06-29 notes が「残る genuine work」の筆頭に (13.9.b) ANT 核を
  flag → lane c/d 双方が同時着手し重複。次の flagged-but-unowned work は着手前に main log grep で
  他レーン進行を確認する ([[cross-lane-sync-via-notes]])。

⟹ **lane d の S15_SAndT_Setup 実 landing はこの回まだゼロ** (重複除去で相殺)。残 16 sorry は全て
grid carrier (issue 3002) / σ-structure / char cascade gated。次手は下記 frontier 参照。

### ▶ §8 TI-subset (13.5 群論入力) を精査 — 完全な path 特定 + crux 1 つに de-risk (issue 4013)

ユーザー裁定で §8 TI-subset (`H_sharp_isTISubset` / `S_normalizes_H_sharp`、lane c 未着手の群論) に着手。
**両 sorry は `hyp.H = fittingInG S` (= Pf (8.5.a) `F(S)=M_F·C_U(M_F)`) に帰着**することを確定。全 TI 機構は
在庫確認済 (`FittingIsTI`=(8.6.a) / `fittingIsTI_of_isTypeP2` / `normalizer_fittingInAmbient_eq_self` /
`maxNilpotentNormalHall_le_fittingInG` / `IsTISubset.subset`)。**残る唯一の crux = `C=C_U(M_F) ≤ fittingInG S`**
= Pf (8.5.a) 本体 (M'=HU coprime-order 論法、(8.4.c) 依存) で repo 未整備。`centralizer_fittingInG_inf` route
(C が F(S) 全体中心化を要す) と Theorem 127 の A₀ (tau2 特殊ケース) は共に不一致。⟹ **次手 = (8.5.a)
`fittingInG S = P ⊔ C_U(P)` を type-P S で形式化** (carrier reconciliation 不要、P/C は Hypothesis 直取り)。
詳細 = **issue 4013**。

---

## ✅ LIVE STATUS (2026-06-29, 正本 — ゲートなし方針で再開, lane c /loop)

> **下の 2026-06-23 ブロックの「§15 lane-c ungated closable work 枯渇 / 全 cross-lane gated」は
> stale な待ち文化フレーミング** ([[ft-four-fronts-w1-w4]] の 2026-06-28 再配分が明示的に却下した症状)。
> 実際には「上流 sorried を cite する」「genuine な arithmetic core を抽出する」だけで closable work は在る。
> 技術的な carrier 診断 (U/W₂ reconciliation の所在) は今も有効な参照。

### ✅ cont. (2026-06-29 lane c=γ): (13.10) 算術核 `analytic_inequality_arith` 着地 + issue 3002 cross-lane 性確定

**(13.10) arithmetic core を sorry-free reusable lemma として抽出** (`S15_SAndT_Setup.lean`,
full build 3886 green/58.6s, AxiomsCheck OK):

- **`analytic_inequality_arith`** (sorry-free): 原文 (13.10, 04.15 pp.85-86) の導出を忠実に Lean 化。
  **grid 依存の character content を concrete な norm-sum 仮説に完全隔離**し、純算術で結論
  `u/c > m·p^(q-1)/q` を出す。abstract atoms = `gi=1/|G|`, `slam=(1/|G|)Σ_{G₀}|λ^{τ₁}|²`,
  `seta=(1/|G|)Σ_{G₀}|η₁₀|²`, `g0=|G₀|/|G|`, `LS=λ(1)²/|S|`, `HS=|H#|/|S|`, `TT=(|T'|−v²)/|T|`,
  `QT=|Q#|/|T|`。仮説 = (13.10.1)/(13.10.2)/(13.10.3) + (13.9.b) `g0≤slam+seta` + counting 恒等式
  (`hLS`/`hTT`/`hQT`/`hm`)。**Stage A** (`linarith`): h1+h2−h3+h139b+gi>0 ⟹ `LS > TT−QT`。
  **Stage B**: counting で `TT−QT = m/p`、`q/p^q>0` を factor out して `uq/(cp^q) > m/p` を
  `u/c > m·p^(q-1)/q` に。これは **§15 cascade の最終出力**で FT に直結 (→ (13.11-15) numeric q=3
  → §16 型決定 → AppC 矛盾)。**grid carrier 着地時 (issue 3002) に wrapper `analytic_inequality`
  がこれを cite** (h1-h139b を carried grid 直交性から、counting を §15 structure から供給)。

**⚠ issue 3002 の cross-lane 性を確定 (重要、s15 ユーザー裁定 (B) の単独実施可能性を精緻化)**:
`S16_NonExistenceGCore.lean:43` で **`S16.Hypothesis.base : S15.Hypothesis`**、`FeitThompson.lean:1828`
の `sectionSixteenHypothesis_of_inputs` が `base := {...}` で **S15.Hypothesis を構成** (sorry-free)。
⟹ **S15.Hypothesis に grid property field を追加すると FeitThompson (lane c 非所有、lane a/d 所有) の
constructor が build-red**。reallocation 方針「自クラスタ主所有のみ編集 + 各 commit build-green」より
**issue 3002 の field 追加は lane c 単独では build-green 不可 = genuine cross-lane** (lanes a/d or hub
が constructor を thread する必要)。⟹ lane c 単独でやれるのは **grid property を Hypothesis field でなく
定理の仮説引数に取る** consumer-side core 抽出 (本 lemma がその第一例)。FeitThompson 不変・build-green・
toolkit 活用・grid property は genuine 構成可能ゆえ honest ([[scaffold-sorry-free-not-done]] の vacuous
仮説 hoist でない)。**次手**: 同様に (13.6)/(13.7)/(13.8) の各 norm bound を grid property 仮説引数の
concrete core として抽出 (caseB_eta_norm_core 等 toolkit を接続)。grid carrier の本丸供給は hub 経由
(issue 3002, cross-lane)。

### ★★ SESSION TOTAL + FRONTIER 評価 (2026-06-29 long /loop, ~16 lemma 完走)
**完了した carrier-free chunk (全 sorry-free, build-green, axiom-clean)**:
1. **§15/§16 norm-cascade arithmetic toolkit** (8 lemma): 13.2.b (`card_P_eq`)・13.2.c bridge
   (`caseB_u_bound_arith`)・13.5.c (`sum_normSq_erase_one_ge_of_const_on_subgroup`)・innerSum-self
   + Parseval・13.6 quadratic (`caseB_quadratic_nonneg`、13.8 も被覆)・13.7 (`caseB_eta_norm_core`)・
   13.12/15 数値核 (`caseB_numeric_forces_q_three`)。
2. **13.18.b Frobenius induced-trivial norm = 完成** (5 lemma): `norm_induce_one_frobenius`
   `‖Ind_A^G 1‖²=(|N|−1)/|A|+1` + value pieces (`induce_one_apply`/kernel-vanishing/complement-count) +
   reciprocity assembly。repo の `IsFrobeniusGroup.trivialIntersection` cite。
3. **13.9.b ([Is] 3.14) arithmetic core** (1 lemma): `card_le_sum_of_one_le_prod` (∏xᵢ≥1⟹∑≥|s|、log-convexity)。

**⟹ carrier-free frontier の残りは 2 つ、いずれも「loop の 1-iteration grind に不向き」**:
- **(深い number-field infra) 13.9.b の残**: `∏|χ(aᵏ)|²≥1` = `N(χ(a))∈ℤ\{0}` が要。repo は character
  値 algebraic-integer (`character_isIntegral`) + ℂ-auto Galois action (`CyclotomicGaloisAction`) を持つが、
  **「Galois-invariant cyclotomic 元 → rational integer」(ℂ-auto ↔ number-field Galois の橋 + fixedField=ℚ
  + Algebra.norm∈ℤ) が未整備** → 大きな multi-iteration build。feeds 13.9→13.10 (cascade、carrier-gated)。
- **(cross-lane) 全 §15/§16 cascade wrapper**: Hypothesis の grid τ-isometry/orthogonality field 化
  (**issue 3002**)。toolkit + 13.18.b は完成済ゆえ、grid 性質が入れば wrapper を組める。**最高 value の unblock**
  だが lanes B/D + FT spine 波及 (要 hub coordination)。

**次の判断 (ユーザー裁定 2026-06-29)**: **(B) issue 3002 の cross-lane grid carrier を優先** = 次の正本方針。
toolkit + 13.18.b は完成済ゆえ、Hypothesis に grid τ-isometry/orthogonality field が入れば §15/§16 cascade
wrapper を組める。実施は cross-lane (lanes B grids / D carrier + FeitThompson constructor) ゆえ hub
coordination 要 — **再開時はまず issue 3002 を起点に、grid 性質 field の追加 + constructor thread を進める**
(consumer-side で sorried contract を pin しつつ並行可)。(A) 13.9.b number-field 橋 / (C) 再配置は保留。

### 本セッション成果 (2026-06-29 詳細, 16+ commits — carrier-free norm toolkit + 13.18.b + 13.9.b core)
1. **(13.2.b) 位数 `|P|=p^q` = 実証明** (`Hypothesis.card_P_eq`, commit `a1e59e84`):
   §11 の Wielandt 順序関係 `typeII_III_IV_order_relations` (type-II 側) を `typeP := Sdata` の
   `TypesIIIIIIVSetup` に適用。nontrivial-core (U≠⊥ via 不変 index / |W₁| prime / A₀(S) TI) は type-II
   witness から read off。唯一の non-derivable 入力 = `Sdata.W2 = W2` reconciliation を**明示仮説に隔離**
   (= `Sdata_U_eq`/`Sdata_W1_eq` の W₂ 版; **issue 3001** で carrier threading)。`P_elementaryAbelian`
   と `u_bound` は genuine §10/§11/§9 (lane a) content ゆえ未着手。
2. **(13.12)/(13.15) 数値核 = 抽出** (`caseB_numeric_forces_q_three`, commit `389650dd`):
   `m < qp/((2q+1)(p-1))` + (13.11) 下界 ⟹ `q=3` の純 ℚ-arithmetic (3 ケース)。`m_value_*` 族と同様の
   self-contained 補題、(13.12) c=1 と (13.15) u 値の両者が consume する再利用核。
3. **(13.5.c) inflation norm bound = 実証明** (`sum_normSq_erase_one_ge_of_const_on_subgroup`, commit `c038fc59`):
   `∑_{x∈H#}|α(x)|² ≥ (|P|−1)α(1)²` (α が P 上 α(1) に定値 = P が α の全 constituent の kernel に入る inflation
   状況)。**任意有限群 H + 部分群 P の carrier-free 一般補題** — Dade 機構も Hypothesis carrier も不要
   (α=α(1) on P + 二乗ノルム非負 only)。`H=↥hyp.H`, `P=S_F` で (13.5) に特化。
4. **innerSum self-identity = 実証明** (`innerSum_self_eq_sum_normSq`, commit `56886c1c`):
   `ClassFunction.innerSum α α = ↑(∑_g ‖α g‖²)` — 抽象 inner-product API と具体 `∑|α|²` の**橋**
   (API に欠けていた)。`RCLike.mul_conj` 経由、任意有限群 H。norm cascade 全 step が依存。
5. **(13.6) quadratic 非負 = 実証明** (`caseB_quadratic_nonneg`, commit `54a1784f`):
   `0 ≤ (|P|−1)b² − 2ub` (u ≤ (|P|−1)/2)。`α(1)=qb` 代入で (13.6) の補正項
   `q²((|P|−1)b²−2ub) ≥ 0` を与える、純 ℤ-arithmetic 核。`(|P|−1−2u)b² + 2u·b(b−1)` 分解。

### ★ 生産的手法 (2026-06-29) — **carrier-free core 抽出** (9 commit で実証、arithmetic toolkit ≈完成)
norm cascade ((13.5)-(13.10)) は「Hypothesis の opaque grid が τ-isometry/直交性/次数を carry しない」ため
**wrapper 定理 (∃ data, opaqueProp 形) は carrier-gated**。だが **各 cascade step の genuine な数学的核は
carrier-free な一般補題として抽出・実証明できる**。これが**待たずに本丸を進める正攻法**
(reallocation §2 の consumer-side prescribed path; STOP(c) の sorry-shuffle でない — 実定理・実証明・再利用可)。
**着地済 toolkit** (§15 norm-cascade + endgame の arithmetic は網羅):
- `caseB_u_bound_arith` = 13.2.c 橋 `(p−1)^{q−1}≤(p^q−1)/(p−1)` (9.7 FPF 下界 → u≤(|P|−1)/2)
- `sum_normSq_erase_one_ge_of_const_on_subgroup` = 13.5.c (inflation 下界 `∑_{H#}|α|²≥(|P|−1)d²`)
- `innerSum_self_eq_sum_normSq` = innerSum↔∑‖·‖² の橋 + `sum_normSq_eq_card_mul_inner` = Parseval `∑_H=|H|⟨α,α⟩`
- `caseB_quadratic_nonneg` = 13.6 quadratic 非負 `0≤(|P|−1)b²−2ub` (**13.8 も `b↦±b` で被覆**)
- `caseB_eta_norm_core` = 13.7 不等式核 `∑_{H#}|η₁₀|²≥|H#|` (Parseval + 13.5.c + n≥1/abelian)
- (既出) `caseB_numeric_forces_q_three` = 13.12/13.15 数値核、`card_P_eq` = 13.2.b 位数

**⟹ cheap carrier-free arithmetic cores はほぼ枯渇** (starved でなく「土台が建った」)。**残る genuine work は 2 系統**、
いずれもより重い/cross-lane:
1. **重い character-theoretic core** (carrier-free): 13.18.b Frobenius induced-trivial norm
   `‖Ind_A^F 1‖²=(|N|−1)/|A|+1`。**✅✅ 完成** (`norm_induce_one_frobenius`, commit `d15bb4fc`)。
   value 3 piece (`induce_one_apply` / `induce_one_eq_zero_of_mem_normal_inf_bot` (γ=0 on N#) /
   `induce_one_eq_one_of_mem_complement` (γ=1 on A#、repo の `IsFrobeniusGroup.trivialIntersection` cite))
   + reciprocity assembly (`inner_induce_eq_inner_restrict` + star-drop `invOf_eq_inv`/`star_inv₀` +
   sum-split)。**§13 で `‖β_j‖²=(u-1)/q+2` を組むときに直接 cite 可** (A=W̄₁, N=Ū, |N:A|=u, |A|=q)。
   **残る重い carrier-free core**: 13.9.b の [Is] Lemma 3.14 (∑_{⟨x⟩-class}|χ|²≥count、代数的整数論/Galois、
   より重い)。13.18 の他 part (13.18.a support / 13.18.c,d Γ 分解) は grid/Dade 依存 (carrier-gated)。
2. **carrier/grid enrichment** (cross-lane、**issue 3002 で hub escalate 済**): 全 cascade wrapper を
   Hypothesis の grid τ₃-isometry/ω-orthonormality field から faithful 化 (toolkit 完成済ゆえ field が入れば
   組める)。FeitThompson constructor + §16 carrier (lanes B/D) に波及。consumer-side で contract pin も可。
   **次 /loop**: 1 の Frobenius reciprocity step を継続 (solo)。

### frontier (ゲートなし方針)
- **(A) Dade norm cascade ((13.5)-(13.10) + (13.3)/(13.4))** = §15 hard core。wrapper は carrier-gated だが
  **carrier-free core は上記手法で抽出可** (13.5.c 着地)。完全な wrapper 化には Hypothesis enrich
  (FeitThompson 2 constructor + §5 性質補題に波及、cross-lane = issue で hub escalate)。
- **(B) 後半 arithmetic ((13.12)/(13.13)/(13.15))** = (A) の (13.10) に gated だが数値核抽出済 (上記 2)。
  abstract `caseX_for_S : Prop` 仮説が残課題 (scaffold design)。

---

## ✅ LIVE STATUS (2026-06-23 再開², ⚠ framing stale — 上ブロック参照) — step-3 wiring 着地後の carrier consumer

> 以下が現状の正本。下の「🔑 carrier 診断」「🔧 POLE-1 carrier 構築」節は **step-3 wiring 着地前の
> 歴史的経緯** (carrier wall の診断・解消過程)。carrier は既に sorry-free 完成 (`exists_typePData_W1_eq_of_isTypeP2`)
> + `Sdata` thread 済 + lane-h が `mp.S_typeP2` 着地 (commit `6ba0bce5`) で step-3 gate 解消済。

### carrier consumer 成果 (本セッション)
1. **`exists_typeI_maximal_overNormalizer_U` 本体 = sorry-free** (commit `7eeb4555`): 2 本の bare sorry を
   `Sdata` carrier から実証明。F-ask `P⊓U=⊥` = `Sdata.derived_complement` の disjoint から; Hall-faithfulness
   `|U|⟂[S:U]` = `[S:U]=|P|·|W₁|` index 分解 (`Sdata.card_W1_eq_derived_index`/`card_U_eq_index`) + `hcop` +
   `coprime_card_kernel_complement` (U⋊W₁ Frobenius)。
2. **`basic_structure` (13.2.a-c,e) = gated-endpoint skeleton 化** (commit `b0a60fbe`):
   - **`S_typeP2 : IsTypeP2 S` を S15.Hypothesis に追加** (mp.S_typeP2 → Section16Inputs → S15.Hypothesis、
     sorry-free thread)。型決定 (13.2.a) を `isTypeII_of_isTypeP2` (lane-f, axiom-clean) で **sorry-free 実証明**
     (`S_typeII_or_typeIII`/`q_lt_p_forces_typeII` を type-II 側で)。
   - **(13.2.b,c,e) M_F-構造を faithful producer `basic_structure_gated` に localize** (P が p^q el-ab、
     U abelian + U⋊W₁ Frobenius、u-bound、A_0(S) TI)。§16 σ-structure (M_σ=M_F el-ab p^q、**repo 未形式化**) に gated。
   - `basic_structure` 本体は sorry-free assembly。

### 現フロンティア分類 (残 21 sorry、全て他レーン/未形式化 gated)
- **char (lane-b §3-13 char API): 10** — `sibleyTarget_S`/`character_degree_analysis`/`lambda_forces_T_caseB`/
  `tiSubset_character_orthogonality`/norm cascade 4本/`analytic_inequality`/`beta_support_norm_and_remainder`/
  `typeI_orthogonality_dichotomy`。
- **numeric (char-determined / 抽象 Prop scaffold): 4** — `numeric_bounds` q=3 (u/c は analytic 待ち + p≥5 不在)、
  `c_eq_one`、`caseA_parameters`/`caseB_order_u` (`caseX_for_S : Prop` 抽象仮説ゆえ u の値は char が決定、honest 不可)。
- **§13 counting / BG Thm E: 3** — `card_Q_eq`(|Q|=q^p)、`tConjugate_fitting_data`、`card_LF_coprime_pq`(BG Thm E=lane-f)。
- **§16 σ-structure (未形式化): 2** — `basic_structure_gated` (P el-ab p^q + Frobenius、ユーザー裁可で skeleton 化、
  本体は lane-f BG§14-16 領域)、`complement_inf_Q_structure`。
- **T 側構造: 1** — `normalizer_W1` (Q⊔W2 = T 側 §16 構造)。

⟹ **§15 の lane-c 単独 ungated closable work は枯渇** (carrier consumer は完遂、型決定は sorry-free)。
残りは lane-b char / lane-f §16 σ-structure (ユーザーが新規形式化を保留) / §13 counting 待ち。
次手 = 要 hub/ユーザー判断 (基準: [[lanes-are-equivalent-no-specialty]]、再配置 or gate 待ち self-resume)。

---

## 🔑 lane-c carrier 診断 (2026-06-23, relane §11→§15 後の最初の精査)

**owner = lane-c** (`S15_SAndT.lean`、2026-06-23 に H→C 移譲、issue 4007)。最初に文書順最上流
`basic_structure` (13.2) を精査して判明した **carrier 設計の核心課題** (次 session の着手前提):

### 課題: `Hypothesis` が type-P 分解を pinning していない
- `Hypothesis` は S, T, U, V, W1, W2, P, Q を **raw subgroup** として持ち、`S_deriv_eq_PU :
  derivedInG S = P ⊔ U` は **join のみ**で `U ⊓ P = ⊥` (complement 性) を持たない。
- `typePData_of_isTypeNonI hyp.S_nonI` で `TypePData S` は取れる (public) が、その `.U`/`.W1` は
  **新 witness** で `hyp.U`/`hyp.W1` と一致保証なし。complement は一意でないため、抽出 `TypePData.U`
  ↔ `hyp.U` の **reconciliation は現フィールドから導出不能**。
- ⟹ `basic_structure` の `UW1_frobenius` (= `typeP_uW1_frobenius` は `data.U`/`data.W1` 上) /
  `U_commutative` が `hyp.U`/`hyp.W1` に転送できず **blocked**。
- これは (13.1.b)「S = (P⋊U)⋊W₁」の**形式化が不完全** (型-P witness を carry していない) のが原因。

### ⚠️ 訂正 (2026-06-23 lane-c 再開時、main マージ後の精査): enrich は **lane-local でなく cross-lane**
**上の数学的洞察 (U-reconciliation が必要) は正しい。が、当初の「`Hypothesis` は producer 無しゆえ
field 追加は C 所有・安全」は誤り。** 実際には `S15.Hypothesis` は
`sectionSixteenHypothesis_of_inputs` ([`OddOrder/FeitThompson.lean:655`]) で **record literal として
明示構成**され、各フィールドを `inp : Section16Inputs G` (= lane-f の POLE-1, issue 7005) から取る。
よって `S15.Hypothesis` に `Sdata : TypePData` を足すと:
1. `FeitThompson.lean:655` の record literal が壊れる (**lane-c 非所有**);
2. ソースとして `Section16Inputs` / `Section16TypePStructure` / `section16TypePStructure_of_components`
   にフィールド追加が必要 (**すべて lane-f 所有 = FeitThompson.lean**);
3. discharge には「**指定した complement `U` を持つ `TypePData mp.S` を構成する**」実作業が要る
   (`typePData_of_isTypeNonI` は自前の `U` を作るので使えない)。`hyp.U` の源
   `exists_kappaHall_invariant_complement_to_MF` ([`S14_TypePComplement.lean:85`]) は内部で
   Schur–Zassenhaus complement (`M_F ⊓ U = ⊥`) を作りながら**返り値型で破棄** (`obtain ⟨U, -, …⟩`)
   している。露出 + `TypePData` 化が lane-f の作業。

⟹ **honest fix = cross-lane carrier enrich** (lane-f の `Section16TypePStructure` に
`Sdata : TypePData mp.S` / `Tdata : TypePData mp.T` を reconciliation 付きで carry させ、
`S15.Hypothesis` へ thread)。lane-f の POLE-1 producer は既に sorry なので obligation は吸収されるが、
TypePData の complement 指定構成は実作業。**lane-c が独断で触れない (cross-lane judgment)** ⟹ HUB issue
4008 で escalate。当初案の reconciliation 設計 (`Sdata.U = hyp.U`, `Sdata.W1 = hyp.W1`, T-side 対称)
自体は正しい — 配置先が lane-c の `Hypothesis` でなく lane-f の `Section16TypePStructure`。

### `basic_structure` (13.2) = 5 部 capstone (単一 leaf でなく複数 session)
1. **carrier reconciliation** (上記 enrich; `hyp.U`=type-P U の pinning) → UW1_frobenius / U-side facts。
2. **type II/III 判定** = 型 IV/V 除外。V= `no_typeV_maximal` (10.10, lane-b S12 sorried, cite 可)。
   IV 除外 + 型確定は §15 解析 (cross-lane 寄り)。`one_typeII : IsTypeII S ∨ IsTypeII T` は片側のみ。
3. **P el-ab 位数 `p^q`** = §15 固有 (chief factor = 全 Fitting, H₀=1; §11 の H=p^q·|H₀| より強い)。
4. **u 上界** `u ≤ (p^q-1)/(p-1)` = (9.7) Singer (lane-c が 2026-06-23 に `clifford_dichotomy` で
   `|Ū| ∣ (p^q-1)/(p-1)` を確立済 → u=|Ū| で landable)。
5. **U_commutative** = type II/III の `TypeIIData`/`TypeIIIData.U_commutative` から (型確定後)。

### 既に証明済 (sorry なし、再着手不要)
`not_conj_of_isTypeI_of_isTypeNonI` (1179)、`isHall_subgroupOf_primeFactors_of_coprime_index` (1085)、
`le_kernel_of_isMulCommutative_of_inf_ne_bot` (1162)、`typeI_U_le_fitting_of_coprime` (1196,
basic_structure の sorried signature を cite)、`typeI_overNormalizer_U_le_fitting` (1267)、
`q_not_dvd_kernel` (1645) 等。

### frontier 全評価 (2026-06-23 lane-c, main マージ後) — 実 sorry 23 本は**全て cross-lane gated**
clean な lane-local win は無い。内訳:
- **基盤 (cross-lane carrier, lane-f)**: `basic_structure` (245, 上記訂正)、`sibleyTarget_S` (258, §14)、
  `card_LF_coprime_pq` (1154, BG Thm E = F)、`exists_typeI_maximal_overNormalizer_U` の `hdisj`/`hUhall_cop`
  (1303/1352, carrier faithfulness = F-ask)。
- **char-theory (lane-b §3-13 char API)**: `character_degree_analysis` (300)、`lambda_forces_T_caseB` (309)、
  `tiSubset_character_orthogonality` (332)、norm cascade (349/356/363/370)、`analytic_inequality` (379)、
  `numeric_bounds` q=3 conjunct (523, p≥5 不在)、`c_eq_one` (529)、`caseA_parameters` (536)、
  `caseB_order_u` (700)、`beta_support_norm_and_remainder` (1744)、`typeI_orthogonality_dichotomy` (1841)。
- **§15 固有 Fitting 構造 (`|Q|=q^p` / chief factor、type-P carrier に bottom out)**: `card_Q_eq` (1115)、
  `tConjugate_fitting_data` (1135)、`complement_inf_Q_structure` (1539)。`TypePData` は Fitting **位数**を
  pin しない (`H = maxNilpotentNormalHall M` のみ) ので、これらは Singer rank + chief-factor 論を要し、
  basic_structure の `P_order` と同じ carrier reconciliation に依存。
- **§13 multi-obligation (lane-h 確認済)**: `normalizer_W1` (831, card_Q_eq + W₁⊆Q + Q# TI + d=1 + KW₂ Frobenius)。

⟹ **lane-c の S15 frontier は現在 ungated closable Lean work が無い。要 HUB/ユーザー判断** (cross-lane enrich
を誰が所有するか、または lane-c を別 FT-path セグメントへ再配置)。正本 = この節 + issue 4008。

### ✅ 確定 (2026-06-23 続, lane-c 再開 deep dive、ユーザー裁可 option 1): carrier wall を**原文+signature で厳密再確認**
上の診断は憶測でなく確定。Pf (13.2) 証明本文 (`04.15_...mmd:35`) を読み、各 cite を repo 追跡:
- (13.2.a) type II/III 分類 = (10.10)/(11.9.b,c); U abelian = 型定義; UW₁ Frobenius = (8.4.d)。
- (13.2.b) P 基本可換 `p^q` = (10.11)/(11.7)。**(11.7)=`S13.H_elementaryAbelian` は `S13.Hypothesis M` 入力**
  (rich carrier: `base.typeP`/`s11Setup`/`chief`)。「IsTypeII M → |M_F|=p^q」の直接 lemma は無く、必ず §13.Hyp 経由。
- (13.2.c) `u≤(p^q-1)/(p-1)` = (9.7) `clifford_dichotomy` (sorry-free 既出, `|Ū|∣(p^q-1)/(p-1)`) + 算術。
  hyp.u=|Ū| は Hypothesis field (`card_U_eq_uc`/`C_eq`) から def 上成立だが、(9.7) を hyp.S に適用するには
  §11 chief-factor setup の reconciliation 要 → wall。
- (13.2.e) TI-subset = (8.13)/(12.7) char/structural。
**核心 = reconciliation wall**: `typePData_of_isTypeNonI hyp.S_nonI` で `TypePData hyp.S` は取れるが
intrinsic `.U`/`.W1` が `hyp.U`/`hyp.W1` と一致する保証が bare Hypothesis に無い (`P_eq_SF` で `.H=hyp.P` だけ一致)。
全上流が rich carrier 入力を要し、それを §15 Hypothesis から構成するには step-3 wiring = **lane-h の (13.2.a)
`IsTypeP2 mp.S` 着地**が必要。**数学は全存在 (Pf 原文 + repo sorried) = 形式化順序の問題、研究 gap でない**
([[feedback-dont-mislabel-formalization-as-research]])。⟹ deep dive は「§15 に lane-c sorry-free closable work
無し」を厳密確定。**4 回目の再 deep-dive は不要** — 次手は lane-h 待ち (self-resume) か別作業再配置。

---

## 🔧 POLE-1 TypePData carrier 構築 (2026-06-23 relane #3, issue 4008 = option A 裁定)

hub が issue 4008 を **option A** で裁定 → lane-c が POLE-1 tp producer carrier を引き取り
(`FeitThompson.lean` tp系 + `S14_TypePComplement.lean` complement 露出)。目標 = `Section16TypePStructure`
に `Sdata`/`Tdata : TypePData` を carry させ、`basic_structure` の U-side 結論を carrier から実証明。

### ✅ step 1: complement 性露出 (commit `1a807071`)
`exists_aInvariant_complement_within_normal` (AInvariantComplement.lean) / `exists_kappaHall_invariant_complement_to_MF`
(S14_TypePComplement.lean) の返り値に `M_F ⊓ U = ⊥` を追加 (内部 `IsComplement'` から、従来 `obtain ⟨U,-,…⟩` で破棄)。
→ `typePData_of_isTypeP_of_inputs` の `hDcompl` 入力に必要。

### ✅ step 2: sorry-free engine (commit `a82ca82a`)
`typePData_of_kappaHall_hallComplement` (FeitThompson.lean):
type-P M + cyclic κ-Hall K + K-invariant (κ∪σ)'-Hall complement U → `TypePData M` (`.W1 = K`, `.U = U` を
definitionally 露出 = projection lemma `_W1`/`_U`)。全フィールドは lane-f の `typeP2_mf_internal_fitting_decomposition`
/`isTypeP2_of_hall_subgroupOf_ne_bot`/`typeP_hall_derived_eq_and_abelian`/`typePData_of_isTypeP_of_inputs` で
sorry-free に discharge (cite)。**`.W1=K` の rfl は term-mode 構成必須** (obtain/have の casesOn が lane-f の
tactic-built def の projection reduce を阻む、[[lean-coupled-engine-fields-and-beta]])。

### ✅ step 2.5: hUhall discharger (commit `f1d710a4`)
`isHall_kappaSigmaCompl_of_isTypeP2_complement` (FeitThompson.lean, sorry-free): type-P2 M で carried U
(M'=M_F⊔U, M_F⊓U=⊥) が (κ∪σ)'-Hall。証明: type-P2⟹M_F=M_σ; `typeP_exists_hall_derived_eq` が (κ∪σ)'-Hall
U₀ (M'=U₀⊔M_σ) 供給; U と U₀ は共に normal M_σ を M' で complement ⟹ |M_σ|·|U|=|M'|=|M_σ|·|U₀| ⟹ |U|=|U₀|;
IsHallSubgroup は order 決定 (`isHallSubgroup_of_card_eq` 新 helper) ⟹ U も (κ∪σ)'-Hall。支持 helper:
`card_mul_card_of_complement_normal` (normal complement の card 積、`normal_mul`+`isComplement'_of_disjoint_and_mul_eq_univ`)。
**Lean 知見**: `subgroupOf` は regular def ゆえ `← comap_inf` rw 不発 → `show … from (comap_inf _ _ _).symm` で
defeq 強制; `hMFeq ▸ hUinf` を rw 引数にすると motive 不定 → `← hMFeq` で戻して `hUinf`。

**⟹ carrier 核心機構 (engine + hUhall + helpers) 完成・全 sorry-free。** engine は type-P2 input で
完全に invocable (step 1 が hUsup/hKnorm/hUinf 供給、step 2.5 が hUhall)。

### ✅ step 2.7: carrier capstone (commit `a6faa39c`、main 同期で lane-f Prop 16.1 hP2II 取り込み済)
**carrier 構成を単一 sorry-free lemma に集約完了。**
- engine `typePData_of_kappaHall_hallComplement` を **`hP2` 直接入力に refactor** (旧 hP+hUne →
  hP2; type-P2 input なら `isTypeP2_of_hall...` 不要ゆえ hUne wart 除去、`typeP2_mf_internal` は hP2 直取り)。
- **compose lemma `exists_typePData_W1_eq_of_isTypeP2`** (sorry-free): `type-P2 M + cyclic κ-Hall K →
  ∃ data : TypePData M, data.W1 = K` = exists_kappaHall_invariant_complement_to_MF + step 2.5 hUhall + engine。
  **step 3 wiring が consume する「ready」形** (指定 κ-Hall を W1 に持つ matched TypePData)。

⟹ **diagnosis が特定した U-reconciliation (元の blocker) の構成機構が完全に sorry-free で完成。**

### 🚧 残 step 3 gate = (13.2.a) producer type 判定 (deep、要 hub/lane-f 判断)
**唯一の gate**: producer (`section16TypePStructure_of_isMinimalSimpleOdd`) で `exists_typePData_W1_eq_of_isTypeP2`
を mp.S に適用するには **mp.S が type-P2** が要る。pair 構成 (`exists_section16MaximalPair_data`, lane-f) は
`IsTypeP2 S ∨ IsTypeP2 Mstar` (FeitThompson.lean:356) **disjunction のみ**で、どちらか不明。q<p (mp.K_lt_Kstar)
で「smaller κ-Hall member = S が type-P2」を resolve するのが **Pf (13.2.a)「q<p ⟹ S type II」**だが、これは:
- producer 文脈で必要 (basic_structure の上流ゆえ basic_structure では供給不可、循環)、かつ
- 証明に §15-16 type 構造を要する deep result (現状未形式化)。
**⟹ (13.2.a) は lane-f の §16 pair 構成 (disjunction を ordering で resolve) で閉じるのが自然か、
lane-c §15 か = cross-lane 判断。lane-f が Prop 16.1 を進行中ゆえ、その完成で resolve する可能性。**
**carrier 機構は完成・consume 待ち; (13.2.a) landing で step 3 wiring は機械的。**

### 🔜 step 3 wiring (gate 解消後)
1. **compose**: `exists_typePData_W1_eq_of_isTypeP2 (hP2) (K κ-Hall) : ∃ data : TypePData M, data.W1=K`
   = exists_kappaHall_invariant_complement_to_MF + step 2.5 hUhall + engine。残 sub-gate = `hUne` (U≠⊥;
   type-P2 ⟹ M_σ≠M' ⟹ U≠⊥、要小 lemma)。
2. **(13.2.a) type 判定 (producer gate)**: producer で engine を mp.S に適用するには **mp.S が type-P2 (=type II)**
   が要る。§16 carrier は q<p (`q_lt_p`) を持ち Pf (13.2.a)「q<p⟹S type II」だが、これは `BasicStructureData.q_lt_p_forces_typeII`
   field = basic_structure 自身。**producer で独立に「q<p (= smaller κ-Hall member) ⟹ type-P2」を要する**
   (Prop 16.1(b) の `IsTypeP2 S ∨ IsTypeP2 Mstar` disjunction を ordering で resolve、BG §16 の deep result、要調査)。
3. **wiring**: `Section16TypePStructure` に `Sdata`/`Tdata : TypePData` (+ `.U=U`/`.W1=K` reconciliation、
   engine `_W1`/`_U`) → producer で compose 呼び出し → `Section16Inputs`+`sectionSixteenHypothesis_of_inputs`+
   `S15.Hypothesis` に thread → `S15.basic_structure` の `UW1_frobenius`/`U_commutative` を carried `Sdata` から
   実証明 (`typeP_uW1_frobenius`)。**注意**: basic_structure の他 field (type 判定, P el-ab p^q, u 上界) は
   carrier と別の deep obligation; carrier は U-side (UW1_frobenius/U_commutative = 診断が特定した元の blocker) を解く。
4. **co-edit 境界** (FeitThompson.lean は F/B/C 共有、def 単位): C=tp系 / F=mp+Prop16.1 / B=cd。互いに別 def。

---

## 実装状況 (2026-06-05 更新, peterfalvi worktree)

**注意**: 以下の大計画は 2026-05-22 の初版 (stale)。実体は `S15_SAndT.lean` の scaffold (18 sorry)。`Hypothesis` は **opaque-Prop convention** (m/u/c 等の値は usable な等式で pin されていない field 群) で、多くの数値結果は値の不透明性ゆえブロックされる。`Hypothesis` は **どこからも構成されない** (S16 が `base : S15.Hypothesis` で参照するのみ) ので field 改変は安全。

### ✅ 実証済 (real, axiom-clean)
- **(13.14) cyclotomic number theory 一式** — `cyclotomic_divisor_facts` + 7 helper (odd / dvd_of_modEq_one / coprime / not_dvd_self / prime_dvd_modEq_one / dvd_modEq_one / modEq_one_of_forall_primeFactors)。純数論、完全証明済。
- **(13.11) m-bounds 部分** (2026-06-05, commit 987392d): opaque `m_formula : Prop` を `m_eq : m = 1 - 1/(q-1) - (q-1)/q^p + 1/((q-1)q^p)` (= (13.10) の値) に置換して **m を pin**。新 arithmetic lemma `m_value_ge_aux` (m ≥ 1-1/(q-1)-1/q², p≥3 で可) / `m_value_gt_seven_tenths` (5≤q⇒m>7/10) / `m_value_gt_four_fifths` (7≤q⇒m>8/10)。`numeric_bounds` の **q≥7, q≥5 conjunct は real** (m_eq + three_le_p 経由)。

### 🔴 残ブロッカー
- **`numeric_bounds` の q=3 conjunct** (narrow sorry): m-bound (m>49/100) は **p≥5 が要** (q=p=3 で m=4/9<49/100 と破綻)。§15 は q<p も p≠q も field に持たず (§16 は (14.1) の `q_lt_p` から p_ne_q/five_le_p を導くが §15 には無い)。p≠q は (13.1) mmd に明示されず §10-§12 由来。u/c bound (u/c>(p²-1)/6) は **analytic_inequality (13.10) 待ち** (character theory)。→ **p≠q (or q<p) を Hypothesis に追加すれば q=3 m-bound は landable** (u/c は別途)。
- **character-theoretic norm 系 (13.5)-(13.10)**: lambda/eta norm lower bounds, global_character_bound, analytic_inequality — §3-§8 (Dade/coherence/TI) の深い指標論依存。`m` は pin 済だが norm cascade 本体は未。
- **c_eq_one (13.12)**: numeric_bounds + analytic + caseA に依存、blocked。
- **caseB_order_u (13.15)**: §16 の `caseB_for_S` が `CaseBOrderUData` 経由で消費。u の値確定は (13.14) facts + character-theoretic な u 下界が要 (blocked)。
- **normalizer_W1 (13.16) / typeII_overNormalizer (13.17) / 18,19**: group/character theory, blocked。

**次の tractable 候補**: p≠q を (13.1) field 追加 (mmd 由来要確認だが FT 設定で valid) → q=3 m-bound 完成 + 他 §15 proof も恩恵。それ以外の実前進は §3-§8 character theory のスキャフォールド解消が必要。

---

## TL;DR — Peterfalvi 本文最大規模, §16 直前の最終仕込み

§15 は Peterfalvi 著作の中で **最も計算が過密** な節. §14 で確立した Type I 最大部分群 (13 個の補題) に続き、§15 は **Type II/III の 2 つの最大部分群 S, T** に焦点を絞る. 両者の位数・正規化群・Dade 等距写像を組合せ、最終的に「S, T の存在は矛盾を導く」という結論に到達させる. これが §16 の 11 個の結果による「G 非存在」の直接的な前提となる.

**本文規模**: 365 行（全 16 節中最大、§10-§14 の平均 150 行を大きく上回る）  
**指標論の深さ**: §3-§8 で確立した Dade isometry / Coherence / TI-subset 理論の **全パイプラインを§15 1 節で集約**  
**形式化上の懸念**: 17 結果 × 大規模 × 指標論特化 → **Lean コード 1500+ 行** の見込み. 2-3 ファイルへの分割戦略が必須.

---

## §15 全 17 結果 + 補足 2 (表形式)

| # | 結果 | 型 | 頁 | 主張 | 依存 | 指標論度 |
|---|------|------|------|------|------|---------|
| 0 | (13.1) | **仮説** | 75 | S, T 定義. W=S∩T=W₁×W₂, P=S_F, Q=T_F. (a)-(e) 5 条件: S=(P⋊U)⋊W₁, T=(Q⋊V)⋊W₂, Dade τ, character ω_ij, η_ij, μ_ij, ν_ij, 集合 𝒮, 𝒯 | (12.1)-(12.13) | **複雑な setup** |
| 1 | (13.2) | Prop | 75-76 | (a) S Type II or III, q<p ⇒ S Type II. UW₁ Frobenius. (b) P elementary abelian rank q. (c) u ≤ (p^q-1)/(p-1). (d) 𝒮 coherent. (e) A₀(S) is TI-subset with normalizer S, τ = Ind_S^G | (10.10), (11.9), (8.4.d), (9.11), (12.7), (8.13) | **structure + coherence** |
| 2 | (13.3) | Prop | 76-77 | (a) j≥1 ⇒ μ_j induced from linear char of PC, μ_j(1)=uq. (b) If 𝒮 has no uq-degree char from PC, then case (9.7.b) holds. (c) δ_j=δ'_i=1. μ_j^{τ₁} = Σ_{i} η_{ij} or (p=3, sign flip) | (9.8), (9.9), (4.3), (4.4), (4.9), (5.8) | **character degree analysis** |
| 3 | (13.4) | Prop | 77 | If 𝒮 has λ of degree uq from PC, then case (9.7.b) for M=T, D=1, v=(q^p-1)/(q-1) | **key case split** | (9.7.b), (13.3.b) | **character orthogonality** |
| 4 | (13.5) | Prop | 77-78 | TI-subset 上の character orthogonality formula. (a) χ(x) = (a/‖ζ₁‖²)ζ₁(x) + α(x) for x∈H^#, a=(ζ₁^τ, χ). (b), (c) norm inequality on α | (7.7.a), (1.5) | **linear algebra on character** |
| 5 | (13.6) | Prop | 78 | Σ_{x∈H#} \|λ^{τ₁}(x)\|² ≥ \|S\| - λ(1)² | (13.5), (13.2.c) | **norm lower bound** |
| 6 | (13.7) | Prop | 78-79 | Σ_{x∈H#} \|η₁₀(x)\|² ≥ \|H^#\| | (5.3.b), (5.5), (13.3.c), (1.10) | **norm lower bound** |
| 7 | (13.8) | Prop | 79 | Σ_{x∈H#} \|η₀₁(x)\|² ≥ \|S'\| - u² | (13.3.c), (13.3.a), (13.5) | **norm lower bound** |
| 8 | (13.9) | Prop | 79-80 | G₀ = G# - ((H#)^G ∪ (Q#)^G). (a) x∈G₀ ⇒ λ^{τ₁}(x) ≠ 0 or η₁₀(x) ≠ 0. (b) Σ_{x∈G₀} (\|λ^{τ₁}(x)\|² + \|η₁₀(x)\|²) ≥ \|G₀\| | (13.3.c), (3.9.b), (3.2.c), (3.4), (1.9.b) | **global character bound** |
| 9 | (13.10) | Prop | 80 | m = 1 - 1/(q-1) - (q-1)/q^p + 1/((q-1)q^p). If 𝒮 has λ, then u/c > mp^{q-1}/q | (13.9), (13.6), (13.7), (13.8), (13.4) | **analytic inequality** |
| 10 | (13.11) | Prop | 80-81 | (a) q≥7 ⇒ m > 8/10. (b) q≥5 ⇒ m > 7/10. (c) q=3 ⇒ m > 49/100 and u/c > (p²-1)/6 | (13.10) | **numeric bounds** |
| 11 | (13.12) | **Main** | 81 | **c = 1** (最重要結果) | (13.3.b), (13.10), (13.11) | **contradiction via bounds** |
| 12 | (13.13) | Prop | 81-82 | If case (9.7.a) for M=S, then q=3 and u=(p-1)²/4 | (13.3.b), (13.10), (13.12), (13.11.b) | **case elimination** |
| 13 | (13.14) | Prop | 82 | (p^q-1)/(p-1) is odd. Divisor arithmetic: if p≡1 (mod q), q divides ratio; if not, ratio is coprime to p-1 | — | **number theory** |
| 14 | (13.15) | Prop | 82 | If case (9.7.b) with M=S, then u = (p^q-1)/(p-1) [if p≢1(q)] or (p^q-1)/(q(p-1)) [if p≡1(q)] | (13.14), (13.3.b), (13.10), (13.12) | **divisor analysis** |
| 15 | (13.16) | Prop | 82-83 | **N_G(W₁) = C_G(W₁) = QW₂** | (13.12), (8.6.a), (9.1) | **normalizer determination** |
| 16 | (13.17) | Prop | 83-84 | If S is Type II, L is maximal with N_G(U)⊆L, H=L_F. Then (a) L is Frobenius group. (b) U⊆H. (c) L=H⋊W₁ or L=H⋊(W₁W₂^y) for y∈Q | (13.2.a), (13.16), (8.8.b4), (12.7), (8.17.a) | **Frobenius structure** |
| 17 | (13.18) | Prop | 84-85 | β_j = Ind_{PW₁}^S 1_{PW₁} - μ_{0j}. (a) Supp(β_j) ⊆ P# ∪ (W-(W₁∪W₂))^S ⊆ A₀(S). (b) ‖β_j‖² = (u-1)/q + 2. (c) Γ = β_j^τ - 1_G + η_{0j} independent of j, orthogonal to 1_G, real. (d) ‖Y‖² ≤ (u-1)/q where Y is orthogonal to η_{ik} | (4.5.a), (4.3.c), (13.3.c), (13.12), (1.6.b), (4.8) | **virtual character decomp** |
| 18 | (13.19) | Prop | 85-87 | L maximal Type I, H=L_F, e=\|L:H\|. (a) Ã(L)∩(P^G∪W^G)=∅. (b) ℒ^{τ₁} orthogonal to η_{ij}. (c) (β_L^τ, η_{0j}) independent of j. Two cases: (c1) (β_S^τ, φ^{τ₁})≡1(2) and (|H|-1)/e ≤ (u-1)/q, or (c2) (β_L^τ, η_{0j})≡1(2) and p ≤ e | (13.18.a), (7.8), (7.8.b), (13.18.d) | **Type I vs (S,T) orthogonality** |

**合計**: 17 結果 (13.1)-(13.17) + 2 補足 (13.18)-(13.19) = **計 19 個**.

---

## §15 の構造: 4 つのフェーズ

### Phase A: Setup と基本構造 ((13.1)-(13.2))

**役割**: 仮説の精密化. §14 の Type I 分析から §15 の (S, T) 分析への転換.

**(13.1) 仮説 (5 条件)**:
- (a) S, T: maximal subgroup pair satisfying (8.8.b conditions). W = S ∩ T = W₁ × W₂ (cyclic direct product)
- (b) P = S_F, Q = T_F. S = (P⋊U)⋊W₁, T = (Q⋊V)⋊W₂. W₁ normalizes U, W₂ normalizes V.
- (c) 𝒮 = {Ind_W^S θ | θ ∈ Irr S', P ⊄ Ker θ}, 𝒯 = similar for T. Dade isometry τ for A₀(S), A₀(T).
- (d) ω_{ij} (as in (3.3)), η_{ij} = ω_{ij}^τ.
- (e) μ_{ij}, ν_{ij}: characters from (4.3) with specific reduction properties.

**mathlib 上の課題**: (13.1) 全体が 1 つの大型 `structure` または `class` になると見込まれる. 10-15 個のフィールド.

**(13.2) 基本事実 (5 項)**:
- (a) S is Type II or III. q < p ⇒ S Type II. UW₁ is Frobenius with abelian kernel U.
- (b) P is elementary abelian of order p^q.
- (c) u ≤ (p^q - 1)/(p - 1).
- (d) 𝒮 is coherent.
- (e) A₀(S) is TI-subset of G with normalizer S. τ = Ind_S^G.

**意義**: §14 の Type I 定理群を (S, T) に特化. Coherence が明示的に現れる最初の箇所.

---

### Phase B: Character-Theoretic Analysis ((13.3)-(13.10))

**役割**: Dade isometry + Coherence を駆使した, S の指標の詳細解析. 8 個の補題で段階的に制約を積み重ねる.

**(13.3) Character Degrees**:
- μ_j (j ≥ 1) は PC の linear character から induced
- μ_j(1) = uq
- δ_j = δ'_i = 1
- μ_j^{τ₁} = Σ η_{ij} (or sign-flipped if p=3)

**ポイント**: Character の度数が (1.1.e) 内で完全に決定される → degree freedom の除外.

**(13.4) Key Case Split**:
- If 𝒮 contains λ of degree uq from PC, then **case (9.7.b) holds for M=T** with D=1, v=(q^p-1)/(q-1).

**意義**: (13.3)-(13.4) は **"Either ... or ..."** 分岐の開始. (13.3.b) で (9.7.b) の可能性を示唆, (13.4) で逆方向を固定.

**(13.5)-(13.8) Norm Lower Bounds** (4 個の補題):
- (13.5): TI-subset 上の character orthogonality (一般型). χ(x) = (a/‖ζ₁‖²)ζ₁(x) + α(x).
- (13.6): Σ |λ^{τ₁}(x)|² ≥ |S| - λ(1)².
- (13.7): Σ |η₁₀(x)|² ≥ |H^#| (H = PC).
- (13.8): Σ |η₀₁(x)|² ≥ |S'| - u².

**手法**: Frobenius-type inner product と Dade image の norm decay を逐次追跡.

**(13.9) Global Character Bound**:
- G₀ = G# - ((H#)^G ∪ (Q#)^G) (intermediate element set)
- (a) x ∈ G₀ ⇒ λ^{τ₁}(x) ≠ 0 OR η₁₀(x) ≠ 0 (完全カバー)
- (b) Σ_{x∈G₀} (|λ^{τ₁}(x)|² + |η₁₀(x)|²) ≥ |G₀|.

**意義**: 「G の generic 元は λ または η₁₀ で非自明」→ character の global 支配権確立.

**(13.10) Analytic Inequality**:
- m = 1 - 1/(q-1) - (q-1)/q^p + 1/((q-1)q^p)
- **u/c > mp^{q-1}/q**

**ポイント**: norm 計算の集約. (13.6)-(13.9) の結果を組合せて, 位数と normalizer サイズの関係式を導出.

---

### Phase C: 位数決定 ((13.11)-(13.15))

**役割**: Analytic inequality (13.10) を数値分析 + case elimination で進める. 最終的に **c=1 決定** と u の明示形を得る.

**(13.11) Numeric Bounds** (3 項):
- (a) q ≥ 7 ⇒ m > 8/10
- (b) q ≥ 5 ⇒ m > 7/10
- (c) q = 3 ⇒ m > 49/100 and u/c > (p²-1)/6

**手法**: 初等不等式 (f(x) monotonicity など)

**(13.12) MAIN RESULT: c = 1**

**Proof Strategy**:
1. (13.3.b) より λ existence 仮定
2. (13.10), (13.12) より m < uq/(p^{q-1}) ≤ q(p^q-1)/((p-1)cp^{q-1})
3. c ≠ 1 ⇒ c ≥ 2q+1 (W₁ acts fixed-point-freely on C, c odd)
4. 3 つの case (p=3, p≥5) で numerically 矛盾導出
   - p=3: m < 3/4 < 8/10, (13.11.a) と矛盾
   - p≥5: m < p/(2(p-1)) < 7/10, (13.11.b) と矛盾

**結論**: c = 1 is forced.

**形式化上の注**: この証明は **case-by-case numeric 検証**. Lean での numeric tactic (omega, norm_num 等) の活躍場.

**(13.13) Case (9.7.a) Analysis**:
- If case (9.7.a) for M=S, then q=3, u=(p-1)²/4.

**意義**: (13.3.b) の (9.7.b) assumption に対して, 逆に (9.7.a) を仮定すると矛盾 → (9.7.b) forced.

**(13.14) Number-Theoretic Facts on Cyclotomic**:
- (p^q-1)/(p-1) is always odd
- If p ≡ 1 (mod q), q divides ratio
- If p ≢ 1 (mod q), ratio is coprime to p-1, and divisors ≡ 1 (mod q)

**目的**: (13.15) の分母分析の準備.

**(13.15) u の最終形**:
- **If case (9.7.b)**:
  - p ≢ 1 (mod q): **u = (p^q-1)/(p-1)**
  - p ≡ 1 (mod q): **u = (p^q-1)/(q(p-1))**

**ポイント**: (13.14) の divisor 性質を使い, (p^q-1)/(p-1) の factorization を決定 → u の一意性.

---

### Phase D: 正規化群と Frobenius 構造 ((13.16)-(13.19))

**役割**: S, T の外部 (G 内での) normalizer 構造と, Type I との相互作用を分析.

**(13.16) KEY FACT: N_G(W₁) = C_G(W₁) = QW₂**

**Proof**: 
1. TI-subset 性質 (13.2.e) より N_G(W₁) = N_T(W₁)
2. QW₂ ⊆ C_G(W₁) は定義より
3. Maschke → Q = W₁ × Q₁ with KW₂ normalizes Q₁ (K = N_V(W₁))
4. K ≠ 1 → contradiction by (13.12) and (9.1)
5. **K = 1** ⇒ N_G(W₁) = QW₂

**意義**: W₁ の正規化群が (S の外で) exactly QW₂ に等しい → geometric constraint on T.

**▶ 2026-06-23 lane-h 着手 — §8-free Wielandt step landed, full assembly は §13-gated (再調査不要)**:
深掘りの結果、(13.16) full は当初の見立てより gating が深い。`normalizer_W1` (S15:827, `:= sorry`) は以下に bottom-out:
- **Q elem-ab order q^p (Q abelian)** = `card_Q_eq` (S15:1113, sorried 残差 B1, **lane-f/b cross-lane gate**) + basic_structure T-side。Maschke (step 3) に必須。
- **W₁ ⊆ Q** — Hypothesis field に無し (構造的 obligation 要)。
- **Q# TI-subset with normalizer T** — step 1 の核、Hypothesis に無し (§13 obligation)。
- **d = 1 (T-side of (13.12))** — `c_eq_one` は S-side のみ、T-side 不在 (obligation)。step 4 の K=1 に必須。
- **KW₂ Frobenius kernel K** — step 4 の Wielandt 入力 (§13 obligation)。
- **BG Lemma 3.2** — step 5 (K ⊆ C(W₁))。✅ **2026-06-23 完全版 landed** (`S03_FrobeniusActions.lean`,
  axiom-clean): `isFrobeniusGroup_quotient_of_normal_not_le_kernel` (= 3.2(a)(b): `N◁G`, `K⊄N` ⟹ `N<K`
  ∧ `Ḡ=G/N` Frobenius) + crux `inf_complement_eq_bot_of_normal_not_le_kernel` (`N⊓R=⊥`) +
  `normal_le_kernel_of_not_le` (`N⊆K`)。repo は Lemma 3.2 の `N≤K` 枝のみ既存だった、未実装の `K⊄N`
  枝を補完。⟹ step 5 obligation は解消 (残 5 obligation は依然 cross-lane gate)。
- **module Maschke** = `OperatorMaschke.lean` ✓ (available)。
⟹ full assembly は残 ~5 obligation の large scaffold (うち card_Q_eq は cross-lane) ゆえ「scaffold ≠ done」回避で full は保留。
**✅ 但し step 4 の genuine §8-free Wielandt 核を landing** (commit `d11f7fe9`, axiom-clean):
`OddOrder.GroupTheory.frobenius_kernel_centralizes_of_complement_fpf` (WielandtFixedPoint.lean) —
Frobenius `U⋊E ≤ N_G(N)` coprime, `C_N(E)=1` ⟹ `U ≤ C_G(N)`。`wielandt_fixedPoint_trivial_E_fixed` の
ambient form (= step 4 の「K centralizes Q₁」)。reusable。**(13.16) full は §13 structural facts (上記) 着地待ち。**

**(13.17) Type II Frobenius Structure**:
- If S is Type II, L = maximal ⊃ N_G(U), H = L_F. Then:
  - (a) **L is Frobenius group with kernel H**
  - (b) **U ⊆ H**
  - (c) **L = H⋊W₁** or **L = H⋊(W₁W₂^y)** for some y ∈ Q

**Proof Idea**:
1. L ≠ S (S は Type II → non-Frobenius)
2. L ≠ T (|H| = q^p, but W₁ ⊆ N_G(U) ⊆ L, W₁ ⊆ H, [U, W₁] ⊆ H ∩ U = 1 → contradiction with (13.2.a))
3. L は Type I → Frobenius (by (12.7))
4. Structure of L.complement via (13.16)

**形式化上の注**: L, M の 2 つの maximal subgroup を導入. これが §16 の (14.3), (14.10) に対応.

**(13.18) Virtual Character Decomposition** (補足):
- β_j = Ind_{PW₁}^S 1_{PW₁} - μ_{0j}
- (a) Supp(β_j) ⊆ P# ∪ (W-(W₁∪W₂))^S ⊆ A₀(S)
- (b) ‖β_j‖² = (u-1)/q + 2
- (c) Γ = β_j^τ - 1_G + η_{0j} independent of j, orthogonal to 1_G, real
- (d) ‖Y‖² ≤ (u-1)/q (Y orthogonal to η_{ik})

**意義**: (13.18) は (13.19) の前置き. β_j の Dade norm と support 構造を確定.

**(13.19) Type I との Orthogonality** (補足):
- L: maximal Type I, H=L_F, e=|L:H|
- ℒ = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}
- (a) Ã(L) ∩ (P^G ∪ W^G) = ∅ (A₀(L), A₀(S), A₀(T) disjoint in fixed-point-set sense)
- (b) ℒ^{τ₁} orthogonal to η_{ij}
- (c) **Two alternative cases**:
  - (c1) (β_S^τ, φ^{τ₁}) ≡ 1 (2) and (|H|-1)/e ≤ (u-1)/q
  - (c2) (β_L^τ, η_{0j}) ≡ 1 (2) for j ≥ 1 and p ≤ e

**意義**: Type I (L) と Type II (S, T) の character family が "orthogonal" → dimension analysis へ. (c1), (c2) は §16 の key case split.

---

## S, T の定義と役割

### S, T は何か?

**定義** (from (13.1), (8.8.b)):
- G: minimal odd-order non-solvable group (極小反例)
- **S, T**: maximal subgroup pair of G, both solvable, satisfying:
  - W = S ∩ T (分解 W = W₁ × W₂, cyclic)
  - |W₁| = q (prime), |W₂| = p (prime), q < p
  - W₁ cyclic Hall subgroup of S, W₂ cyclic Hall subgroup of T
  - S, T are **conjugate-free** (no S ≅^conj T in typical case, see (13.17.c) exception)

### 構造

**S の構造** (from (13.1.b), (13.2)):
- S = (P⋊U)⋊W₁ (nested semidirect product)
- P = S_F (Fitting subgroup, elementary abelian, rank q)
- U: abelian (from (13.2.a)), order u
- W₁: cyclic of order q
- U, W₁ complement P with specific action properties
- S' = PU, C = C_U(P), S'/P ≅ U/C

**対称性**:
- T は S と同じ構造で, P ↔ Q, U ↔ V, W₁ ↔ W₂, q ↔ p を交換した形.

### 指標論的特徴

**集合 𝒮, 𝒯** (from (13.1.c)):
- 𝒮 = {Ind_W^S θ | θ ∈ Irr S', P ⊄ Ker θ}
- 𝒯 = {Ind_W^T ψ | ψ ∈ Irr T', Q ⊄ Ker ψ}
- **Coherent** (from (13.2.d)): Dade isometry τ̃: Z[𝒮] → Z[Irr G] の拡張が存在

**主要指標族**:
- μ_{ij}, ν_{ij}: S, T 上の character famiglia, degree u
- η_{ij} = ω_{ij}^τ: Dade image (virtual character on G)

---

## 17 結果のグループ化

### Group 1: Type Determination (13.3)-(13.4)

**内容**: S, T の Type (II or III) 決定, character degree structure.  
**キー結果**: (13.3.a) μ_j(1) = uq, (13.4) case (9.7.b) for T with v=(q^p-1)/(q-1).  
**mathlib 上**: character degree の列挙 (finite list, Lean で直接?).

### Group 2: Norm Inequalities (13.5)-(13.10)

**内容**: Dade norm, character support, analytic inequality.  
**キー結果**: (13.10) u/c > mp^{q-1}/q (m parameterized by q, p).  
**mathlib 上**: `ℝ` 不等式の cascade. `norm_num` tactic 多用.  
**形式化量**: **最大** (6 補題 × 詳細計算 = 300-400 行?)

### Group 3: Order and Centralizer Determination (13.11)-(13.15)

**内容**: c=1 証明, u の明示形.  
**キー結果**: (13.12) c=1, (13.15) u = (p^q-1)/(p-1) [or divided by q].  
**mathlib 上**: numeric case analysis + divisor theorem.  
**形式化量**: **大** (case split 多い, 150-200 行)

### Group 4: External Structure (13.16)-(13.19)

**内容**: G 内での normalizer, Frobenius structure, Type I との orthogonality.  
**キー結果**: (13.16) N_G(W₁) = QW₂, (13.17) L Frobenius, (13.19.c) case (c1)/(c2).  
**mathlib 上**: Group theory (normalizer, Frobenius定義).  
**形式化量**: **中程度** (100-150 行)

---

## §14 (Type I) からの継承

**§14 全 13 結果** (12.1)-(12.13) は Type I 最大部分群 L の詳細分析.  
**§15 の依存**: 
- (13.1) の仮説は (12.1)-(12.13) の **逆側 (non-Type I case)**
- (13.2.a) "S is Type II or III" = **not Type I**
- (13.17) "L is Type I Frobenius" = §14 の type classification を再利用

**継承構造**:
```
§14: Type I (M) の 13 補題
    ↓ (exhaustion)
§15: Type II,III (S,T) の 17 補題 + Type I 例外 (13.17.c)
    ↓
§16: G non-existence (11 補題)
```

---

## §16 (Non-existence G) への橋渡し (final input)

**§16 全 11 結果** (14.1)-(14.11) + (14.12)-(14.17):

| §15 Result | § 16 usage | Purpose |
|------------|-----------|---------|
| (13.1) Hyp | (14.1) Hyp | Setup (q < p variant) |
| (13.2.e) τ=Ind | (14.2) FT Main | Dade simplification |
| (13.3), (13.4) char degree | (14.4) case (9.7.b) | Type constraint |
| (13.10) ineq | (14.8) key ineq | u/c bound |
| (13.12) c=1 | (14.12)-(14.16) | Simplification |
| (13.16) N_G(W₁)=QW₂ | (14.5.c) L structure | Frobenius complement |
| (13.17) L Frobenius | (14.5.a) | Type I analysis |
| (13.18)-(13.19) | (14.14.c) case (c1)/(c2) | Orthogonality switch |

**Key Mechanism**:
- §15: (13.1)-(13.19) で S, T の完全記述を達成
- §16: その記述を (14.1)-(14.11) で矛盾導出に使用
- **結論**: S, T 共存不可 ⇒ G 존재不可 (by exhaustion with Type I (13.17))

---

## BG §15 (M_F) との関係

**BG Notation**: M_F = Fitting subgroup of M (maximal Hall odd-order normal subgroup)

**Peterfalvi vs BG**:
| 項目 | BG §15 | Peterfalvi §15 |
|------|--------|-----------------|
| **焦点** | M_F の局所構造 (Frobenius action, cohomology) | S, T の指標論的詳細 (Dade, coherence, norm) |
| **手法** | Group cohomology H²(U, M_F), Maschke | Character theory, Dade isometry |
| **結果** | Type 𝓕 definition | c=1, u = (p^q-1)/(p-1) |
| **規模** | ~60 行 | ~365 行 |

**統合点**:
- BG §15 で M_F の structure 決定
- Peterfalvi §15 で M_F (= P or Q) を S_F, T_F と呼び, 指標論で再分析

---

## ファイル分割の検討 (s15_s_and_t subdirectory 戦略)

**規模見積**: 365 行 (本文) → **1500-1800 行 (Lean)**

**理由**: 
- 17 結果各々 80-120 行の Lean code (proof density 高)
- 指標論計算 (norm, character degree) の detailed lemma化
- case split 多い ((13.12), (13.13), (13.15) 等)

**分割案 A (フェーズベース)**:
```
s15_s_and_t/
  ├─ A_setup_and_types.lean       (~200 行: 13.1-13.4)
  ├─ B_norm_and_analytics.lean    (~500 行: 13.5-13.10)
  ├─ C_order_determination.lean   (~350 行: 13.11-13.15)
  ├─ D_normalizers_and_frobenius.lean (~300 行: 13.16-13.19)
  └─ S15_SAndT.lean               (imports + index)
```

**分割案 B (グループベース)**:
```
s15_s_and_t/
  ├─ Normalizers.lean             (13.16)
  ├─ TypeDetermination.lean       (13.3-13.4)
  ├─ NormInequalityMain.lean      (13.5-13.10) — **最大ファイル**
  ├─ OrderDetermination.lean      (13.11-13.15)
  ├─ FrobeniusStructure.lean      (13.17-13.19)
  └─ S15_SAndT.lean
```

**推奨**: **分割案 A** (フェーズ順に development → より readable)

---

## mathlib カバレッジ

### 完全新規 (Peterfalvi 固有)
- `DadeIsometry` API (§4 から継続)
- `Coherence` 定義・主定理 (§7 から継続)
- Virtual character norm inequality (§5-§8 application)
- Type II/III 定義と properties (from BG §11, but Peterfalvi-specific formulation)

### 部分既存 (mathlib+補強)
- `Character.degree`, `Character.induced`: existing in `Mathlib.RepresentationTheory.Character`
- Frobenius group structure: existing in `Mathlib.GroupTheory.Frobenius` (but (13.17.a)-(c) may need extension)
- Numeric inequality: `norm_num`, `omega` tactic

### 依存関係 (§15 独自)
- **§3 Preliminary** (character orthogonality, Frobenius, TI-subset)
- **§4 Dade Isometry** (全体の backbone)
- **§5 TI-Cyclic Normalizer** (13.16 preparation)
- **§7-§8 Coherence** (13.2.d, 13.3.c application)
- **§14 Type I** (13.2.a, 13.17 structure)

---

## Phase 2b 形式化着手順

### 予備調査 (準備期間, 1-2 週)
1. mmd ファイル全 365 行を Lean code 密度で分類 (proof vs setup vs lemma)
2. mathlib Character/Frobenius API の詳細確認
3. (13.12) c=1 の numeric case split strategy を mock-up

### 第 1 pass: Setup + Type (1 週)
- (13.1)-(13.4): structure 定義 + basic properties
- **形式化量**: 200-250 行

### 第 2 pass: Norm Inequalities (2-2.5 週) ← **最長**
- (13.5)-(13.10): 6 個の norm lemma, analytic inequality
- **難所**: (13.6)-(13.9) の nested character bound, (13.10) の analytic formula
- **形式化量**: 500-600 行

### 第 3 pass: Order & Divisor (1.5 週)
- (13.11)-(13.15): numeric bounds, case (9.7.a)/(9.7.b), divisor arithmetic
- **難所**: (13.12) c=1 の exhaustive case analysis (p=3 vs p≥5)
- **形式化量**: 350-400 行

### 第 4 pass: Normalizers & Frobenius (1 週)
- (13.16)-(13.19): normalizer determination, Frobenius structure, Type I orthogonality
- **形式化量**: 300-350 行

### 統合テスト (0.5 週)
- Full file build
- Cross-reference check with §16 (14.1)-(14.11)

**総所要期間**: **6-7 週** (依存コンポーネント §3-§14 完成後)

---

## 未解決 / TODO

### Theory-Level
1. **c=1 決定の formal 手法**: (13.12) の proof は numerically exhaustive (case p=3, p≥5). Lean での `interval_cases` 的な tactic の適用可能性?
2. **Divisor arithmetic の mathlib**: (13.14)-(13.15) で (p^q-1)/(p-1) の divisor properties. `Nat.dvd` + congruence `Nat.ModEq` で formalize?
3. **Frobenius complement の一意性**: (13.17.c) で "L = H⋊W₁ or L = H⋊(W₁W₂^y)" の either/or structure. Lean で case-by-case proof design?

### Formalization-Level
1. **Virtual character space Z[Irr G]**: §5 では virtual character を informal に扱う. Lean type を設計する際, `Z-Module ℂ` か, それとも custom type か?
2. **Dade isometry の norm 計算**: (13.5)-(13.8) の norm lower bound が本体. mathlib `‖·‖` notation との統一?
3. **TI-subset orthogonality** ((13.5.a) etc.): inner product (·, ·) on CF(L, A^#) の定義が (7.1) Hypothesis に依存. dependency handling?

### Integration-Level
1. **§15 → §16 引き継ぎ**: (13.19.c) の two cases が (14.14) の case (a)/(b) に対応するが, formal mapping を明確化?
2. **BG App.C との overlap check**: BG でも M_F (type 𝓕) と U の関係が扱われるが, 重複部分の elimination strategy?

---

## Summary

**Peterfalvi §15** は Phase 2b の最終直前準備として、**17 個の結果 (365 行) を使い, S, T 部分群の位数・正規化群・指標を極限まで詳細化する**.

**Key achievements**:
- (13.12) **c = 1** (C_U(P) が自明)
- (13.15) **u = (p^q-1)/(p-1)** (order 決定)
- (13.16) **N_G(W₁) = QW₂** (external normalizer)
- (13.17) **Type II ⇒ L is Frobenius** (structure)
- (13.19) **(c1)/(c2) dichotomy** (§16 key case split)

**形式化規模**: 1500-1800 行 (4 ファイル分割推奨)

**所要期間**: 6-7 週 (§3-§14 完成後, §16 前)

**最大の挑戦**: 
- Norm inequality cascade (13.5-13.10) の formal proof
- Numeric case analysis (13.12) の exhaustiveness guarantee
- Character family orthogonality (13.19) の dimensional argument

---

**作成**: 2026-05-22. **出典**: `references/peterfalvi/04.15_pp_75_86_The_Subgroups_S_and_T.mmd` (365 行, 17 結果). §14, §16 ノートのクロス参照確認済.


---

## 🧾 HUB 回答 (2026-07-05, 統合セッション) — 上記 LIVE STATUS の方針確認への裁定

**A+B 両方を b が実施** (C 再配分は不要、3 レーン維持): 3002 threading は S15.Hypothesis fields (自所有) +
`FeitThompson.lean` Section16Inputs block (一時編集権承認、9009 更新) の両半分とも b。その後 engine wiring →
terminal 1298 → c_eq_one assembly (hu = 9000 producer を sorried-cite 可)。S15 閉塞後の継続 frontier =
**Wave 2: S10 §8 facts (carve-out 0096) → S14 witness 3 本** (all-type-I branch は honest FT の必要部品)。
正本 = `ft_lane_reallocation_2026_06_28.md`「3 レーン役割更新 (2026-07-05)」節。

---

## ✅ LIVE STATUS (2026-07-05b, lane b — issue 3002 threading 両半分 LANDED)

hub 裁定 (9009 選択肢 2) の実施完了 (commit 3dc9306e, full 3917 green + AxiomsCheck green):
- `S15.Hypothesis`/`Section16Inputs`/`Section16CharacterData` に **7 grid property fields**
  (tau3_isometry/trivial/apply_of_regular/mem_ZIrr + omega_orthonormal/apply_one/mem_ZIrr) を
  追加し、**供給 chain 全段 sorry ゼロ** (tau3W→tiCyclicW 抽出 refactor + S05 σ-package 直読み;
  omegaS_inner = S05 omega_inner + inner_compHom_mulEquiv + enum injectivity)。
- **frontier 変化**: §15 cascade は「hyp が性質を carry しない」uniform gate が解消。次 =
  **consumer-side wiring** — (13.5) machinery (`H_sharp_hypothesis76`/`H_sharp_point_formula`,
  S15 内 proven) + hyp の carried properties から terminal `analyticInequalityEstimates`
  (S15_SAndT_Setup:1298) の 4 estimates ((13.6)/(13.7)+(13.8)/(13.9.a)/(13.9.b)) を実証明。
  依存: (13.3)/(13.4) `character_degree_analysis` (λ 存在+counting) の現状確認から。
  hu (2u≤|P|-1, 13.2.c) = issue 9000 producer を sorried-cite 可。
- 9009 は close (routing 完了)。3002 は wiring 完了まで open。

---

## ✅ LIVE STATUS (2026-07-07, lane b) — G2 (13.2.e normedTI) CLOSED + (3.9.a) unsound carrier 解消

**本日 2 landing で S15 frontier が変形** (詳細 = issues/1017 末尾 + issues/3002 末尾):

1. **G2 CLOSED (commit 76d1b27b)**: `escaping_honestTypeP2ASet_eq_empty` (Rung C、Coq
   FTtypeP_facts (e) port) → `Hypothesis.isTISubset_honestTypeP2ASet` (A(S) TI = normedTI TI 半分)
   + `Hypothesis.sInstance_dade_eq_induce` (isometry 半分: full-A(S) supported f 上で
   dade = Ind_S^G)。9017 (BG Cor 15.9) の landing が case-P₂ 枝を、Pf (12.7) typeI_frobenius +
   Isaacs 6.4 kernel regularity が case-F 枝を閉じた。
2. **(3.9.a) honest close (commit df1ff47f)**: `w1CharEquiv`/`chi2enum` を生成元 power
   enumeration (`S06.cyclicPowEnum`) に組替え (signature 完全保存) → finNeg = 文字反転が定義から
   成立 → `tau3W_omegaS_pair_of_coprime` sorry-free (σ Galois 等変 + (3.9.c) 整数値)。
   **AxiomsCheck assert 再有効化** (endgame plan §4 完成条件 item 2 discharge)。unsound carrier
   ゼロに。c-side (EtaGenericData.eta_pair finNeg 形) は restatement 不要で即 wire 可。

**次の frontier (文書順)**:
- **(13.3) = G1 assembly のみ残**: base `sSetIrrDeg_coherent` (landed、h2/hd0 露出) →
  `coherentPairChain` で mixed family (reducible μ_j = CharacterPsiDecomposition / 既約 conjugate
  pairs) を adjoin → NEW IsCoherent → `coherent_H0Cprime_S` (S15:~1010) re-point →
  `CharacterDegreeData` (S15:2316) の tau1S 3 fields = G1 extension + G2 dade=Ind
  (`sInstance_dade_eq_induce` + `sSet_member_diffsupp`) で discharge → (13.3.a/c) μ-column
  formulas。≥2 count sub-gate = (9.8.d) S11:11691 (sorried-cite 可)。
- **(13.4) 残 gate 1** (`QD_sharp_centralizer_le_T` S15:5949) = A₀(T)-TI。Rung C の一般定理は
  IsTypeP₂ M を取る — T 側は `T_typeII_or_III_or_IV` (type II/III/IV) で IsTypeP2 T は未 carry
  (14.9 循環回避)。type-II case は Rung C がそのまま刺さる; type-III/IV (P₁) は matched κ-Hall
  pair の一般 type-P 版 (`typeP2_exists_matched_kappa_hall_pair` の P₁ analogue) が要調査。
  (Q⊔D)^# ⊆ A(T) は D = C_V(Q) 中心化で elementary。
- **(13.4) 残 gate 3** (`tSide_theta_package_of_not_caseB` S15:6070) = (13.3.b,c)-on-T θ-package
  — T-instance の §9 data は gate-3 router (`mkSection11CharacterDataT`、88237b38) で供給済、
  中身は (13.3)-on-T ゆえ G1 の T-side mirror に帰着見込み。
