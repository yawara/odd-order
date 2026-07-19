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
