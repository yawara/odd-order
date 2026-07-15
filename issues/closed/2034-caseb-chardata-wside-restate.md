---
id: 2034
slug: caseb-chardata-wside-restate
title: "CharacterDegreeData の W-side restate — lambda_mem (Sset=∅ で反証可能) 除去 + free Prop の honest 化"
created: 2026-07-05
---

# CharacterDegreeData の W-side restate — lambda_mem (Sset=∅ で反証可能) 除去 + free Prop の honest 化

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->
## 判定 (hub 裁定 2026-07-02 の「到達時に W-side restate or retire」を執行)

**結論 = restate** (retire 不可: (13.3)/(13.4) は `T_side_caseB_facts` (S16) 経由で on-path、
(13.10) の λ-package も Pf 原文が (13.6) の λ を直接使う)。

## 発見 (soundness bug)

`CharacterDegreeData.lambda_mem : lambda ∈ hyp.Sset` — spine
(`section16CharacterData_of_isMinimalSimpleOdd`) は **`Sset := ∅`** (vestigial placeholder,
issue 1004 裁定) を供給するため、spine の hyp では `CharacterDegreeData hyp` が
**uninhabited** → `character_degree_analysis : ∃ data, …` は**反証可能** (unprovable)。
grep 検証: `chars.lambda_mem` の cite は **0** (S16_PairingCoherence の `typeIHyp.Sset` は
別構造)。

## やること

- [x] `lambda_mem` field 除去 (0 cites、純 soundness fix)
- [x] `lambda_irreducible : Prop` (free) → `IsIrreducibleCharacter lambda` に materialize
- [x] `lambda_induced_from_PC_linear : Prop` (free) → 実 ∃-statement
      (∃ linear θ : CF(H.subgroupOf S), degree-1 irreducible ∧ lambda = Ind θ) に materialize
      — consumers は `hlam` を opaque に持ち回るだけなので signature 影響ゼロ、
      construct するのは sorried `character_degree_analysis` のみ
- [x] (07-05 it.57) 残 free Props の honest 化 — mu_j_linear_induced ((13.3.a) 全列 ∃-形) +
      mu_tau1_formula ((13.3.c) 全形 normal ∨ p=3-swap) を materialize、
      no_lambda_forces_caseB_S + sign_flip_exception (未消費 WLOG-枝/例外 doc) を除去、
      character_degree_analysis の結論を Nonempty に簡約 — (13.3.a/c/d) の τ₁↔η-grid formula 設計と一体
      (tau1S の W-side 意味論: μⱼ^{τ₁} = δ Σᵢ η_{i1} 型の formula field 群)。
      (13.3)-cluster atom 群 (exists_lambda_index / lambda_tau1_norm_one /
      lambda_tau1_apply_mul_eq_zero / eta10_cCoeff_orthogonal) の実証明もこの設計に乗る。

## 参照

- notes/peterfalvi/s16_w4_char_cascade.md「HUB 裁定 (2026-07-02 全体レビュー)」§2
  (S-side τ₁ 形の処分) + cont.⁴⁴ (T_side_caseB_facts route 検証)
- closed/2033 (この判定に到達した (1.10)-合同層 real 化の後続)

## (13.3.c)/τ₁ 意味論の設計 (07-05 it.33、Pf 原文精読)

### 原文の構造 (04.15 mmd pp.75-77)

- **τ₁ の定義**: 「τ₁ = Dade isometry τ (rel. A₀(S)) の ℤ[𝒮] への extension」。
  **(13.2.e) 末尾: 「τ coincides with Ind_S^G」** (A₀(S) TI + normalizer S ゆえ)。
- **(13.3.c)**: δⱼ = δ′ᵢ = 1 ((4.3.d)+(4.4)、u ≡ 1 mod q ⟸ (U/C)W₁ Frobenius)。
  **μⱼ^{τ₁} = Σ_{0≤i<q} η_{ij}** (j≥1)、または p=3 例外 (− 符号 + j↔j′ swap)。
  出典 = (4.9) (𝒮∩Irr S = ∅ 側) / (5.8) (≠∅ 側) — **深い §4/§5 coherence content = 真の gate**。
- **(13.6) が λ に要るもの** (= cluster atom の内訳):
  1. λ ∈ 𝒮₁ = {Ind_H^S θ : θ ∈ Irr H, P ⊄ Ker θ} — materialized field
     `lambda_induced_from_PC_linear` に **P ⊄ Ker θ conjunct を追加**すれば構造的に取れる
     (残: H76 family enumeration の exhaustiveness — `H_sharp_hypothesis76` の族が
     𝒮₁ 全体を尽くすか。構成 (`hypothesis76OfFamily`) を精査し、必要なら
     `zeta_surjective`-型 field を S09 側に足す)。
  2. c_{i₁} = 1 + middle c = 0 (`exists_lambda_index` の残 conjunct):
     ⟨τψᵢ, λ^{τ₁}⟩ = ⟨ζᵢ−ζ₀, λ⟩ (τ₁ extension+isometry) = δ_{i,i₁} (distinct-Ind 直交)。
  3. ‖λ^{τ₁}‖ = 1 (`lambda_tau1_norm_one` conj 1-2; conj 3 ⟨λ,λ⟩=1 は field から実証明可)。
  4. λ^{τ₁}(xy) = 0 (`lambda_tau1_apply_mul_eq_zero`): (3.2.d)/(5.3.b)/(5.5) —
     τ₁-image の support/直交性。
  5. η₁₀ ⊥ 𝒮^{τ₁} (`eta10_cCoeff_orthogonal`): (4.1)+(5.3.b) 「η_{ij}, λ^{τ₁}, θ^{τ₁}
     pairwise orthogonal」。

### 候補 field 設計 (CharacterDegreeData 追加分; H76/hG 非依存の induce-level 表現)

```lean
  /-- (13.2.e): τ₁ は family 差分上で Ind_S^G と一致 (τ = Ind、τ₁ extends τ)。 -/
  tau1_extends_induce : ∀ θ θ' : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
    IsIrreducibleCharacter θ → IsIrreducibleCharacter θ' →
    tau1S (induce (H…) θ - induce (H…) θ')
      = ClassFunction.induce hyp.S (induce (H…) θ - induce (H…) θ')
  /-- coherence isometry: τ₁ は 𝒮₁-members 上で内積保存 + ZIrr 値。 -/
  tau1_family_isometry : ∀ …(Ind-of-linear members f g)…,
    ⟨tau1S f, tau1S g⟩ = ⟨f, g⟩
  tau1_mem_ZIrr : ∀ …, tau1S f ∈ ZIrr G
  /-- (13.3.c) 本体 (μ-grid formula; p=3 例外込み)。mu_tau1_formula の materialize。 -/
  mu_tau1_eq_eta_sum : (∀ j ≠ 0, tau1S (hyp.mu · j) = Σ_{i<q} hyp.eta i j) ∨ (p = 3 例外形)
  /-- (4.1)/(5.3.b): η-grid ⊥ τ₁-image。eta10_cCoeff_orthogonal の直接の親。 -/
  eta_orthogonal_tau1 : ∀ i j …f…, ⟨hyp.eta i j, tau1S f⟩ = 0  (f ∈ 𝒮₁-part, f ≠ 対応 μ…)
```

**⚠ 設計上の未決**: (a) 𝒮₁-membership の Lean 表現 (∃ θ linear P-non-ker, f = Ind θ を
inline で繰り返す vs `def indFamily` 述語を切る — 後者推奨)。(b) eta_orthogonal_tau1 の
除外条件の正確な形 ((13.4) 証明では λ^{τ₁} と η 全直交だが μ^{τ₁} = Ση とは非直交 —
「f が μ-row でない」の条件設計)。(c) これら field の spine 供給可能性 —
τ₁ の honest 構成は §4/§5 coherence (lane-c の h78/`coherence_extension_*` 機械と同形) 経由。
supply 設計は field 確定後に FeitThompson 側を精査。

### 実装順 (次 iteration 以降)

1. `indFamily` 述語 + `lambda_induced_from_PC_linear` に P-non-kernel conjunct 追加
2. H76 family exhaustiveness 精査 (S09 構成読み) → exists_lambda_index の実証明可能性確定
3. τ₁ fields 追加 (extends/isometry/ZIrr) → lambda_tau1_norm_one, exists_lambda_index 実証明
4. (13.3.c)/(4.1)-直交 fields → eta10_cCoeff_orthogonal, lambda_tau1_apply_mul_eq_zero
5. supply 側 ((4.9)/(5.8) 経由の honest τ₁ 構成) は別 issue に切る (深さ = §4/§5 coherence)

## 進捗 (07-05 loop it.34-41)

τ₁-cluster の実証明化が完了域に (commits 116d139d/f8ab92a9/6ededdef/3a541099/fe51f2be/af545610/6c7a0237/+):

- [x] Hypothesis76: `zeta_family_cover` + `zeta_injective` fields + trivial-base 正規化
      (`hypothesis76OfDadeTrivialBase`、ζ₀ = Ind 1 pin)
- [x] kernel descent bridge + P-non-kernel conjunct
- [x] τ₁ fields 4 本 (extends-Ind / isometry / ZIrr / ⊥η-grid) — supply は sorried (13.3)
- [x] `H_sharp_tau_eq_induce` ((13.2.e) τ=Ind、TI-induce 値公式 2 本 [9011 拡張] と S04 値公式の貼合せ)
- [x] `exists_lambda_index` 全 real (membership: cover+base+descent / coefficient:
      `lambda_tau1_cCoeff` — (13.2.e)+線形分配+isometry+distinct-Ind 直交+単射性)
- [x] `lambda_tau1_norm_one` 実証明 (fields から)
- [x] `lambda_tau1_apply_mul_eq_zero` real assembly — field (4.1)/(5.3.b) ⊥η +
      新 sorried `Hypothesis.vanish_of_inner_eta_eq_zero` ((3.2.d))
- [ ] **残: `vanish_of_inner_eta_eq_zero` の supply** — S05
      `eq_zero_of_mem_V_of_inner_chiFam_eq_zero` (proven!) を spine の
      ω-grid ↔ hom-pair 対応 (gridEquivE/omegaProdChar/w1CharEquiv/chi2enum) で
      S15 field 化 (2033-threading パターン; Fin q×Fin p ↔ hom-pair 全単射)
- [ ] 残: `eta10_cCoeff_orthogonal` (同じ (4.1)/(5.3.b) 系 — field 化検討) /
      μ-side Props の honest 化 / `character_degree_analysis` 本体 ((4.9)/(5.8))
