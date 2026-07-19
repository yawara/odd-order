---
id: 1041
slug: pf-13-8-s-side-mirror
title: "(13.8) S 側 mirror: ∑_{H^#}|η₀₁|² ≥ |S′| − u²"
created: 2026-07-19
---

# (13.8) S 側 mirror: `∑_{x∈H^#} |η₀₁(x)|² ≥ |S′| − u²`

## 教科書 (PDF p.79 で確定, 2026-07-19)

**(13.8)** Let `H = PC`. Then `∑_{x∈H^#} |η₀₁(x)|² ≥ |S′| − u²`.

証明: (13.3.c) で `0 < j < p`, `δ = ±1`, `μ_j^{τ₁} = δ ∑_{0≤i<q} η_{i1}`。(13.3.a) で
`μ_j ∈ S₁`。(13.5) を `ζ₁ = μ_j`, `χ = η₀₁`, `a = δ` で適用。(13.5.b,c) から
`∑_{H^#}|η₀₁|² ≥ (1/q)(|S| − (qu)²/q) − 2δu·α(1) + (|P|−1)α(1)²`。
`u ≤ (|P|−1)/2` ((13.2.c)) + `α(1) ∈ ℤ` で交差項非負 → 結論。
`firstTerm = |S|/q − u² = |S′| − u²` ([S:S′] = q)。

repo 形式化済みの `eta10_Qsharp_norm_lower_core` (Eta10Correction.lean:361) は
**(13.10.2) が使う「(13.8) applied to T」** (χ=η₁₀, Q^#, |T′|−v²) の方。
書籍の (13.8) 本体 = S 側が未形式化 (特殊化債務)。

## 実測済み在庫 (2026-07-19 — frontier note の「4 ピース未存在」は過大)

**既存 (mirror に流用可能)**:
- side 非依存エンジン: `caseB_eta01_norm_bound` / `caseB_eta01_norm_core`
  (Machinery135.lean:937/908) — S 側命名で完備。入力 7 本
  (hvanish/hinner/hχ/hfirstTerm/hcross/hδ/hinfl + hu)。
- **(13.3.c) S 側**: `tau1S_ofHonest_mu_col_eta_col_one` (S15_CaseACoherence.lean:932)
  — 「μ-column で τ₁-image = ±∑_i η_{i1}」。(13.3.a) は `mu_j_isIndPC`。
- **(7.6) base S 側**: `H_sharp_hypothesis76_base` (S15_CharacterDegreeEnginesSSide.lean:615)
  — H^# 上、kernel filter は `P.subgroupOf S`。`H_sharp_hypothesis76`
  (Machinery135.lean:1097) は非-base 版。
- **α integrality/inflation S 側**: `H_sharp_cCoeff_int` /
  `H_sharp_alphaFun_inflation_finset` (Canonicalization.lean:126/229)。
- (13.7) S 側パッケージ (χ=η₁₀ over H^#): `exists_caseB_data_eta10_H_core`
  (Eta10HCorrection.lean:89) — 組み立ての**手本** (base 選択→alphaFun→Parseval)。
- TI 構造: `H_sharp_isTISubset` / `H_sharp_dadeHypothesis` (Machinery135.lean:984/1039)。

**未存在 (作るもの)**:
1. `eta01` の定義 (`hyp.eta ⟨0⟩ ⟨1⟩`; T 側の `eta10 = hyp.eta ⟨1⟩ ⟨0⟩` の転置)。
   定義位置は eta10 と同じ場所 (S15_SAndTDefs.lean を確認)。
2. S 側 μ index core = `exists_muT_index_core_of_base_condition` の mirror:
   (13.3.c) の μ_j を H76 family の index データ (cCoeff η₀₁ i₁ = δ / 他 0 /
   zetaNormSq i₁ = q / zeta i₁ 1 = qu) に変換。
3. α(1) ∈ ℤ (mirror of `exists_etaT_alphaFun_one_int_core`)。
4. `exists_caseB_data_eta01_S_core` (mirror of `exists_caseB_data_eta10_T_core`,
   Eta10Correction.lean:207): ζ = q⁻¹·(H76.zeta i₁), α = hypothesis76AlphaFun,
   firstTerm = |S′| − u² (`card_S_eq_deriv_mul_q` mirror 要確認)。
5. `eta01_Hsharp_norm_lower_core` (mirror of `eta10_Qsharp_norm_lower_core`:361):
   `|S′| − u² ≤ ∑_{x ∈ sharpSubgroup H} ‖eta01 x‖²`。
   `2u ≤ |P^q|−1` 側の numerology (`two_mul_v_le` の mirror; (13.2.c) は
   u ≤ (|P|−1)/2, |P| = p^q) を要確認。

## 注意

- T 側は「base が irreducibly induce しない」ため直交 base 選択
  (`exists_qSharpBase_orthogonal_eta10_core`) を挟む。S 側で同じ迂回が要るかは
  μ-column formula の supply (`tau1S_ofHonest_mu_col_eta_col_one` の仮定) を見て判定。
- S 側の H = PC ≠ P: H76 base は H^# 上で kernel filter が P
  (T 側は Q^# 上で filter も Q — D = ⊥ で K = Q ゆえ一致)。α の台が
  H^# vs P^# のどちらかで inflation 係数 ((|P|−1) vs (p^q −1)) が変わる。
  教科書 (13.5.c) は (|P|−1)α(1)² ≤ s_α — T 側 mirror では (q^p−1) を使っていた。
  **(13.7) 用 `exists_caseB_data_eta10_H_core` が (p^q−1) を既に使っている**ので
  S 側の対応物はそこから読める。
- consumer: 書籍で (13.8) S 側が cite される箇所を PDF で確認してから
  結論の正確な形 (Finset 形 vs Set 形) を合わせる。

## 参照

- frontier note: `notes/peterfalvi/frontier_measured_2026_07_19.md` §13 (13.8) 行
  (2026-07-19 に本 issue の実測で訂正済み)
- T 側実装: `S15_CaseBEndgameSupply/Eta10Correction.lean` (全体が手本)

## 実装設計 (2026-07-19 iteration 2 実測 — CharacterDegreeCore ベースで書く)

**方針転換**: T 側 (`Q_sharp_*` 直呼び) でなく **S 側の既存 abstraction 層
`CharacterDegreeCore` (Machinery135.lean:95) + `H_sharp_hypothesis76_base`** の上に書く。
(13.7) 用の既存実装がこの層で完結しており、必要 field は全て揃っている:
`tau1S_apply_induce_sub` / `tau1S_inner_induce` / `tau1S_induce_mem_ZIrr` /
`tau1S_induce_inner_eta` (既約 induction は全 η 直交) /
`tau1S_induce_inner_eta_col_zero` / **`mu_col_tau1_eta_col_one`** ((13.3.c) 蒸留済:
j≠0, δ=±1, θ linear P-nonkernel, μ_j = Ind θ, τ₁ μ_j = δ•∑_i η_{i1}) /
`mu_j_linear_induced` / `mu_tau1_formula` (clean/p=3-flip 両分岐)。

**手本 3 点セット** (すべて実在・sorry-free):
- base 選択: `CharacterDegreeCore.exists_hSharpBase` (HSharpChosenBase.lean:36)
- family index: `LambdaClusterData.exists_hSharpFamilyIndex_base` (同:110) —
  `zeta_family_cover` で index、`H_sharp_hypothesis76_base_zeta_zero` で正値性
- cCoeff 計算: `lambda_tau1_cCoeff_base` (CharacterDegreeEnginesSSide.lean:663、λ で
  coefficient=1) と `eta10_cCoeff_base_eq_zero` (同:866、全係数 0)。
  cCoeff χ i = ⟨Ind_S^G(psiSupp i), χ⟩, psiSupp i = zeta i − d_i•zeta 0, d_i = 1
  (K ≅ H abelian, `hd1` パターン)。

**書くもの (S15_CaseBEndgameSupply/ に新 leaf `Eta01Correction.lean` を推奨)**:

1. `CharacterDegreeCore.exists_hSharpBase_orthogonal_eta01`:
   ∃ φ₀ P-nonkernel with `Ind φ₀ ≠ μ_j` (distinguished) かつ
   `⟨τ₁S(Ind φ₀), η₀₁⟩ = 0`。
   構成: mu_col_tau1_eta_col_one の j に対し**別の非零列 j''** を取る
   (T 側 `exists_qSharpBase_orthogonal_eta10_core` の mirror):
   clean 分岐 → τ₁ μ_{j''} = ∑η_{i,j''}, j''≠1 → η₀₁ と直交 (eta_orthonormal)。
   p=3 flip 分岐 → columns {1,2}: j=2 が distinguished、j''=1 → −∑η_{i,2} → 直交。
   ⚠ clean 分岐で p=3 のとき j=1, j''=2 (η-col 2 → 直交 OK)。
   μ_{j''} ≠ μ_j: mu_orthonormal (⟨μ_j,μ_j⟩=q≠0, ⟨μ_j,μ_{j''}⟩=0)。
   φ₀ = mu_j_linear_induced (j'') の θ。
2. `exists_eta01_muColumn_index_base` (mirror of exists_hSharpFamilyIndex_base):
   mu_col の θ_j を zeta_family_cover → i₁, zeta i₁ = μ_j, 0 < i₁
   (Ind φ₀ = μ_{j''} ≠ μ_j), P-nonkernel descent (pointwise witness は
   hθP の Set.not_subset から)。
3. `eta01_cCoeff_base` (mirror of lambda_tau1_cCoeff_base):
   cCoeff η₀₁ i₁ = δ / P-nonkernel i ≠ i₁ → cCoeff η₀₁ i = 0。
   dispatch (i ≠ i₁, θ_i := zeta_induced i):
   (a) Ind θ_i 既約 → `tau1S_induce_inner_eta` (0,1) → 0。
   (b) Ind θ_i 可約 → **要調査**: S 側「P-nonkernel 可約 induced = μ-column」
       分類 brick が存在するか。T 側は 2 段 constituent 展開で処理
       (CharacterDegreeEngines.lean:353-)。候補:
       `tau1S_ofHonest_zSpanIrr_inner_eta` (EnginesSSide:268) /
       `induce_H_mem_zSpan_sSet_irr` (同:61) を先に読む。
       μ-column なら mu_tau1_formula → η-col ≠ 1 → 0 (j' = j なら zeta i = μ_j =
       zeta i₁ → family injectivity? i = i₁ 矛盾 — zeta の単射性 brick 要確認)。
4. `exists_caseB_data_eta01_S_core` (mirror of exists_caseB_data_eta10_T_core,
   Eta10Correction.lean:207): ζ := q⁻¹ • (zeta i₁) = q⁻¹ μ_j, α := hypothesis76AlphaFun。
   - hvanish: zeta_eq_zero_of_not_mem_H (H-vanishing — ⚠ T 側は Q^# 台; S 側は H^# 台)
   - hinner: hypothesis76_zeta_inner_alphaFun_eq_zero
   - hχ point formula: hypothesis76_point_formula (i₁, cCoeff=δ, 他 0)
   - hfirstTerm: ∑_S ‖q⁻¹μ_j‖² − ‖q⁻¹μ_j(1)‖² = |S|·q/q² − (qu/q)² = |S|/q − u²
     = |S′| − u²。zetaNormSq i₁ = q (`muColumn_inner_self` 経由; T 側 hnormP mirror)。
     μ_j(1) = qu: mu_col θ 1 = 1 → μ_j(1) = |S:H| = ? **|S:H| = qu を供給する
     carrier 補題を要確認** (T 側 `card_T_eq_deriv_mul_p` + hdeg mirror;
     候補 grep: `index_H`, `card_S`, `u_eq`, S = HW₁ 分解)。
   - hcross: α(1) ∈ ℤ (mirror of exists_etaT_alphaFun_one_int_core —
     S 側候補 `H_sharp_cCoeff_int` (Canonicalization.lean:126) から組む)
   - hinfl: hypothesis76AlphaFun_inflation, 係数 (|H|−1)…
     ⚠ T 側は (q^p−1) = |Q|−1 を使った (台 = Q^#)。S 側の台は H^# だが教科書
     (13.5.c) は (|P|−1)α(1)²。**(13.7) 実装 `exists_caseB_data_eta10_H_core` は
     (p^q−1) = |P|−1 を使用** (行 96: `(hyp.p ^ hyp.q - 1) * d ^ 2 ≤ s`) —
     inflation の台が P^# に絞られる仕組みをそこから読む
     (`H_sharp_alphaFun_inflation_finset` Canonicalization.lean:229)。
5. `eta01_Hsharp_norm_lower_core` (mirror of eta10_Qsharp_norm_lower_core:361):
   `(|S′| : ℝ) − u² ≤ ∑_{x ∈ sharpSubgroup hyp.H} ‖hyp.eta01 x‖²`
   via `caseB_eta01_norm_bound` + hu: 2u ≤ |P|−1 = p^q − 1
   (T 側 `two_mul_v_le hv` mirror; u = (p^q−1)/(p−1) 型の carrier 恒等式を確認 —
   (13.2.c) は u ≤ (|P|−1)/2)。

**次 iteration の開始点**: 3(b) の可約 dispatch brick と 4 の |S:H| = qu 供給を
grep で確定してから `Eta01Correction.lean` を書き始める。

## 完了済み

- [x] stage (i): `Hypothesis.eta01` 定義 (DegreesFirstSplit.lean, commit 25689c81d)

## iteration 3 進捗 (2026-07-19)

**完了** (commit 9e02862ab):
- `eta01_mem_ZIrr` (DegreesFirstSplit)
- 新 leaf `S15_CaseBEndgameSupply/Eta01Correction.lean` (hub 登録済):
  `etaColumn_inner_eta01` / `muColumnSum_ne_of_ne` /
  `CharacterDegreeCore.exists_eta01_column_data` (j₀/c₀/δ/φ₀ packaged;
  clean=(1,2,1), p=3 flip=(2,1,−1))

**次に書くもの = S 側 hTau1IndEta mirror** (最重量、~300 行)。T 側の完全な手本 =
`exists_muT_index_core_of_base_condition` (CharacterDegreeEngines.lean:84-630)。
**⚠ hyp レベルで書く** (core レベル不可 — sSet member (Ind_HU ξ) の grid 直交
`coherentIndS_image_inner_eta_eq_zero` は core の field に無い)。статement:

```
theorem Hypothesis.exists_muS_index_core_of_base_condition
    (hG hnoV hyp chief) (φ₀ : Irr (H.subgroupOf S)) (hφ₀P : P-nonkernel)
    (hφ₀base : Ind φ₀ irreducible ∨ ⟨τ₁S(Ind φ₀), η₀₁⟩ = 0) :
    ∃ i₁ δ, 0 < i₁ ∧ P-nonkernel (zeta i₁) ∧ δ² = 1 ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta01 i₁ = δ ∧
      (∀ i, 0 < i → i ≠ i₁ → P-nonkernel (zeta i) → cCoeff hyp.eta01 i = 0) ∧
      zetaNormSq i₁ = q ∧ zeta i₁ 1 = (u*q : ℕ)
```

T 側 → S 側の対応表 (行番号は T 側):
- :155 hetaRow → 済 `etaColumn_inner_eta01`
- :175 pinned row obtain → 済 `exists_eta01_column_data` (ただし hyp-level 化:
  core := hyp.characterDegreeCore hG hnoV chief で core.tau1S = tau1S_ofHonest は rfl)
- :217 ν_r = Ind θr (nu_i_isIndQD + K=Q transport) → S 側は exists_eta01_column_data
  の hμeq (μ_{j₀} = Ind θ_{j₀}) が直接与える (transport 不要、mu_j_isIndPC_not_ker 由来)
- :231 hQkerNu (Q ⊄ Ker ν_r) → μ_{j₀} の P-nonkernel 版。
  `mu_j_isIndPC_not_ker` (EnginesSSide:445) が θ の P-nonkernel を持つ;
  S-level kernel 判定は subsetCharacterKernel_induce_of_subgroupOf の逆向き
  ((1.6.a) mem_characterKernel_of_mem_characterKernel_induce) で降ろす
  (:945-964 eta10_cCoeff_base_eq_zero の hθiP パターン流用)
- :354 hTau1IndEta (2 段展開) → **核心**。S 側の内部手本 =
  `induce_H_mem_zSpan_S` (CaseACoherence.lean:1047; HU = huSub data,
  H-in-HU ≤ HU, compHom transport, induce_induce_subgroupOf,
  induce_eq_sum_inner_restrict_smul, hcoefNat via
  isCharacter_restrict + exists_natCast_inner_irreducible)。
  ⚠ **S 側は data.H = P ≠ H** (toTypesIIIIIIVSetupS_H_eq? → DegreesFirstSplit:948:
  data.H = hyp.P): hInHu data = P-in-HU。hmem (constituent ∈ sSet = 𝒳-witness) は
  `constituent_P_not_subset_characterKernel` に (A = P-in-HU ≤ K' = H-in-HU) の
  2 段で渡す — T 側は A = K' = Q-in-HU だった。θ' の kernel guard も
  ((P-in-HU)-in-(H-in-HU)) 形に transport (induce_H_mem_zSpan_S 内部と同一)。
  - 既約 constituent → `coherentIndS_image_inner_eta_eq_zero`
    (tau1S_ofHonest_zSpanIrr_inner_eta:288 の呼び方を流用; 引数 =
    sSet_closedUnderConjugate / sSet_hasNoRealCharacters +oddCardS /
    conjDiff supported / coherent_H0Cprime_S) at (0,1)
  - 可約 constituent → `sSet_reducible_eq_muColumnSum` → 列 c:
    c = j₀ なら exfalso (⟨Ind θ, μ_{j₀}⟩ = 0 (hInd0: 相異 H-induction 直交、
    inner_induce_eq_zero_of_not_conj) vs ℕ-係数展開で n s ≥ k s·q > 0;
    T 側 :456-501 の mirror — nuRow_inner → muColumn_inner_self,
    sSet_pairwiseOrthogonal は共通)
    c ≠ j₀ → exists_eta01_column_data の orthogonality 節
- :506 family cover → zeta_family_cover ⟨θ_{j₀}, irr⟩ (transport 不要)
- :516 hi₁pos → ⟨τ₁ 比較⟩: base ⟨τ₁ Ind φ₀, η₀₁⟩ = 0 (exists_eta01_column_data
  の c₀-orthogonality から) vs δ ≠ 0
- :530 hzeta_one/hd1 → K = H.subgroupOf S abelian (H_mulCommutative;
  eta10_cCoeff_base_eq_zero :884-906 と同一パターン)
- :551 hc1/hmiddle → cCoeff 展開 + tau1S_apply_induce_sub bridge
  (eta10_cCoeff_base_eq_zero :966-987 パターン + i₁ 例外は δ)
- zetaNormSq i₁ = q: zeta i₁ = μ_{j₀} → `muColumn_inner_self` +
  Hypothesis76.zetaNormSq def (T 側 :290-293 の hnormP mirror)
- zeta i₁ 1 = uq: `mu_j_degree` (CountingLayer:433)

**その後**: base cCoeff-int mirror (`Q_sharp_hypothesis76_base_cCoeff_int`
CharacterDegreeEngines:716 → H_sharp 版; H_sharp_dadeHypothesis/H_sharp_hconj は
Machinery135:1039/1062 に既存) → α(1)∈ℤ (hypothesis76AlphaFun_one_int) →
`exists_caseB_data_eta01_S_core` (T 側 :207-353 mirror; ζ := q⁻¹ • zeta i₁,
hfirstTerm = |S′|−u² via card_S_eq_deriv_mul_q + sum_normSq_eq_card_mul_inner;
hinfl via hypothesis76AlphaFun_inflation + F↔H^# + |P-in-S| = p^q (card_P_eq)) →
最終 `eta01_Hsharp_norm_lower_core` (T 側 :361-389 mirror;
hu = two_mul_u_le (Canonicalization:94)、
sum_apply_erase_one_filter_subgroupOf + H_le_S)。
