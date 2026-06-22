---
id: 1009
slug: pf-10-6-summed-isometry-norm-bound
title: "Pf (10.6): summed isometry μ_j^τ₁=δ∑ω_ij^σ + ζ^τ₁ norm bound (gated on §5 (5.8))"
created: 2026-06-22
---

# Pf (10.6): summed isometry + ζ^τ₁ norm bound

## ✅✅✅ 2026-06-23 — (10.6)(a) summed isometry COMPLETE (linchpin landed)

(10.6)(a) `μ_j^τ₁ = δ∑_i ω_ij^σ` を **σ-endgame engine を使わず** honest に証明・wiring (lane-b)。
σ-grid 2D product 構造 (`exists_alignedOmegaSigmaGrid_chiFam_product` / `exists_kappa_sum_chiFam_column_eq`)
を経由する当初 route より大幅にシンプルな **§10 特化 route** を発見し完走。残り = (10.6)(b) parity bound のみ。

- **`Hypothesis.omegaSigmaDiff_inner_muColumn_tau1`** ((10.6)(a) 還元, commit `b3393682`): `(ω_ij^σ − ω_i0^σ,
  μ_j^τ₁) = δ`。`(α_ij^τ, μ_j^τ₁ − dζ̄^τ₁) = 1` (`muGridAlpha_tau1_inner_muColumn_self_sub_conj`) +
  `(α_ij^τ, ζ̄^τ₁) = 0` (= (10.5) `a=0` `muGridAlpha_tau1_zeta_eq_neg_n` + `(α^τ,ζ̄^τ₁)=(α^τ,ζ^τ₁)+n`) +
  (10.5) Dade image `alpha_tau_image` + `(ζ^τ₁,μ_j^τ₁)=0` (`zeta_tau1_inner_muColumn`) →
  `1 = (α_ij^τ,μ_j^τ₁) = δ(ω_ij^σ−ω_i0^σ,μ_j^τ₁)`。**ζ^τ₁⊥Imσ を回避** (in-stock のみ)。
- **`Hypothesis.muColumn_tau1_pin`** ((10.6)(a) summed isometry, 同 commit): `μ_j^τ₁ = δ∑_i ω_ij^σ`。
  (5.5) `μ_j^τ₁ = ∑_{x∈T} R(x)` (R=`columnRImage` 直交族, |T|=w₁) に上記還元を当て、各 i で
  `(ω_ij^σ−ω_i0^σ, μ_j^τ₁) = δ·[(false,i)∈T]` を計算 → 全 `(false,i)∈T` → cardinality count で
  `T = {false}×univ` → `μ_j^τ₁ = ∑_i δ·ω_ij^σ`。**separability / σ-coefficients / σ-endgame engine 不要** —
  対角内積 `=1` が直接 j-列を pin し、`|T|=w₁` が共役列を殺す。
- **wiring** (commit `da77ee6f`): `tau1_values_and_norm_bound` conjunct (a) = `muColumn_tau1_pin`
  (標準 bundle hmu/hos/hzS/hz1/hzconj/hδpm/hδj 追加、`[Finite G]`+FiniteInduce regime に統一)。
  両 lemma axiom-clean modulo §10 muGrid 上流 gate (theoremA/Prop16.1、自前 sorry 0)。full build 3881 green。
- **🔑 設計教訓**: §10 では (10.6)(a) 還元 `(δ(ω^σ−ω^σ),μ_j^τ₁)=1` が in-stock ゆえ、Peterfalvi の一般 (5.8)
  (vanish-on-V + (3.7) separability) を**回避**できる。当初 route が要した σ-endgame engine
  (`eq_smul_chiFam_column_of_vanishOnV`)・sigmaCoeff 翻訳・2D product (`exists_alignedOmegaSigmaGrid_chiFam_product`)
  は**不要**になった (それらは valid だが (10.6)(a) には未使用; 2D product は §10/§13 で再利用余地あり)。

## ▶ 残り = (10.6)(b) parity bound (次セッション)

`zeta_tau1_norm_bound` (現 opaque `Prop` = `True`, producer S12:2690) を de-opaque して証明:
`g ∈ G − Ã(M)`, `order g` coprime to `w₁` ⟹ `|ζ^τ₁(g)| ≥ 1`。原文 (04.12 l.63-67):
- **算術恒等式** (in-stock 材料): `δ(μ_0−ζ)^τ = δ∑ω_i0^σ − δζ^τ₁`。
  `(μ_j−dζ)^τ − ∑_i α_ij^τ` を (10.6)(a)`μ_j^τ₁` + (10.5)`α_ij^τ` で展開、`d=nw₁+δ` で `(nw₁−d)ζ^τ₁=−δζ^τ₁`。
- **τ-vanishing**: `(μ_0−ζ)^τ` は `G − Ã(M)` で消える (τ 定義) ⟹ `ζ^τ₁(g) = ∑_i ω_i0^σ(g)`。
- **parity**: ω_i0^σ(g)∈ℤ (3.9.c) + ω_00^σ=1_G ((3.2.b)=`sigma_trivial` ✅在庫) + i≠0 で
  ω̄_i0^σ=conj(ω_i0^σ) (3.9.a) かつ ω_i0 非実 (奇位数) ⟹ ∑_{i>0}∈2ℤ ⟹ ζ^τ₁(g)≡1 (mod 2) ⟹ |ζ^τ₁(g)|≥1。
- **要確認**: `Ã(M)` (tame support) の §10 表現、τ-vanishing on `G−Ã(M)` の在庫、(3.9.a)/(3.9.c)、
  order-coprime 仮定の使い所。carrier de-opaque (`zeta_tau1_norm_bound` を genuine statement に) が必要。

## 背景

(10.5) Dade-image identity 締結 (issue 1007/1008 CLOSED) に続く文書順次ターゲット。
`tau1_values_and_norm_bound` (`S12_MaximalIII_IV_V.lean:3521`, sorry) が (10.6) の Lean 化で、
2 つの conjunct を持つ:
1. **(10.6.a) summed isometry**: `∀ j ≠ 0, coh.tau1 (∑_i μ_ij) = δ • ∑_i ω_ij^σ`。
2. **(10.6.b) norm bound** (= opaque `CharacterParameters.zeta_tau1_norm_bound : Prop`, 現 `True`):
   `g ∈ G − Ã(M)` で位数 prime to w₁ ⟹ `|ζ^τ₁(g)| ≥ 1`。

原文 = `references/peterfalvi/04.12_*.mmd` (10.6) (pp. 58-63)。

## ⚠ gate: Peterfalvi (5.8) が未形式化

**(10.6.a) は Peterfalvi (5.8) [§5 Coherence, `references/peterfalvi/04.7_pp_25_29_Coherence.mmd:119`]
に gated**。原文証明:
```
1 = (α_ij, μ_j − dζ̄) = (α_ij^τ, μ_j^τ₁ − dζ̄^τ₁) = (δ(ω_ij^σ − ω_i0^σ), μ_j^τ₁)   [by (10.5)]
→ by (5.8), μ_j^τ₁ = δ ∑_i ω_ij^σ.
```
(5.8) は coherence isometry τ₁ の下で column-character μ_k の像を決定する §5 結果 (2 ケース、複雑な
statement)。**S07_Coherence.lean に未形式化** — 本 issue の真の prerequisite。

**(10.6.b)** は (10.6.a) の第2関係式 `(μ_0 − ζ)^τ = ∑_i ω_i0^σ − ζ^τ₁` + parity 論証:
- τ の定義より `(μ_0 − ζ)^τ` は G − Ã(M) で消える ⟹ `ζ^τ₁(g) = ∑_i ω_i0^σ(g)`。
- (3.9.c): `ω_i0^σ(g) ∈ ℤ`。i≠0 で `ω̄_i0 ≠ ω_i0` + (3.9.a) `ω̄_i0^σ = conj(ω_i0^σ)` ⟹ `∑_{i>0} ω_i0^σ(g) ∈ 2ℤ`。
- (3.2.b) `ω_00^σ = 1_G` ⟹ `ζ^τ₁(g) ≡ 1 (mod 2)` ⟹ `|ζ^τ₁(g)| ≥ 1`。
(10.6.b) も (10.6.a) 経由ゆえ (5.8) に gated。(3.9.a)/(3.9.c)/(3.2.b) は §5 (repo S05) に在庫見込み。

## やること

- [x] **§6 conjugate chain 一般化 DONE + §10 conjugate-column 恒等式 DONE** (2026-06-23, issue 1010 CLOSED):
  - §6 `certainType_columnSum_conj` chain を `Hypothesis46→Hypothesis` 一般化 (commit `9db31b2b`,
    完全 axiom-clean)。`column_inv_ne_self` は Hypothesis46 据置 (S08 caller 無変更)。
  - **`Hypothesis.exists_conj_column`** (S12, commit `842c9116`): `(∑_i μ_ij).conj = ∑_i μ_ij'`
    (j'≠0, j'≠j)。= column image family の `image_eq` 材料 (χ.conj = μ_j')。
- [x] **column image family + (5.5) チェーン DONE** (2026-06-23, 全 axiom-clean=§10 upstream gate のみ):
  - `alignedOmegaSigmaGrid_inner` (σ-grid orthonormality, `b97df920`): `⟨ω_ij^σ,ω_i'j'^σ⟩=[i=i'∧j=j']`
    (σ 等長 + (i,j)↦η_ij joint inj)。**joint inj で orthonormality 十分** (full product 不要)。
  - `alignedOmegaSigmaGrid_mem_ZIrr` + `columnRImage`/`_inner`/`_injective`/`_sum` (`6deff68d`): R(μ_j)
    部品 (Bool×Fin w1 → CF G ℂ, (false,i)↦δω_ij^σ, (true,i)↦−δω_ij'^σ)。
  - **`columnImageFamily`** + `exists_columnImageFamily` (`f6693952`): `OrthonormalCharacterImageFamily
    hyp.tau (∑μ_ij)` 完成 (4 field 全 discharge、§6 certainTypeR の hyp.tau 版)。
  - **`exists_muColumn_tau1_eq_sum_R`** (`bd31dd8c`): (5.5) 適用 → **`μ_j^τ₁ = ∑_{α∈E} α`** (E⊆R(μ_j),
    |E|=w₁)。ofProjection (htau1_inner_eq=extension_inner_eq / agrees=extends_on_supported /
    mem=extension_mem_ZIrr / ⟨μ_j,μ̄_j⟩=0=muGrid_inner_cross_column) + eq_sum_of_psi_eq_zero。
  - **▶ 残り = σ-endgame final step のみ** (= (10.6.a) の last piece): `μ_j^τ₁=∑_{α∈E} α` (E⊆R(μ_j)) を
    σ-endgame `eq_smul_chiFam_column_of_vanishOnV` (在) に渡し E=full column {δω_ij^σ} に pin →
    `μ_j^τ₁=δ∑ω_ij^σ` → `muColumn_tau1_eq_of_single_column` で全列。**⚠ これは column 構造
    P_i(j).2=κ(j) (W2 成分が j のみ依存=product 構造) を要する** — orthonormality と違い σ-endgame の
    sigmaCoeff 2-column support + 出力翻訳 ∑_p chiFam(p,kcol)=∑_i ω_ij^σ に product が必須。= 残る唯一の
    deep 2D-structure piece (`omegaProdChar.comp e` factorization、`exists_alignedOmegaSigmaGrid_chiFam_family`
    を 2D 化 + W2-成分 i-独立を証明)。在庫: vanish-on-V=`muColumn_tau1_vanishes_on_typePV`、
    norm=`muColumn_tau1_inner_self`。

  - **🗺 column-structure の精密証明戦略 (2026-06-23 lane-b 導出、次セッション用)**: 完全 factorization
    `c_ij = omegaProdChar_tic ρ_i κ_j` を直接出さず、**(A) W2-成分 i-非依存 + (B) injectivity+cardinality
    で列の全射性** に分解すると tractable:
    - 記号: `c_ij := (sdiff.omegaProdChar (w1CharEquiv i) (χ₂ j)).comp e` (e=alignedOmegaSigmaGrid 内の
      `tic.W ≃ sdiff.W`)、`Q(i,j) := omegaProdEquiv_tic.symm(c_ij)` (∴ ω_ij^σ=chiFam(Q(i,j)))。
    - **(A) `Q(i,j).2` は i に非依存**: `c_ij = c_{i'j} · ((w1 i)/(w1 i')).comp(wFst_sdiff.comp e)`。
      後者は **W2_tic 上自明な「W1-only char」** (w∈tic.W2 ⟹ e(w)∈sdiff.W2 ⟹ wFst_sdiff(e w)=1、
      `wFst_eq_one_of_mem_W2`)。omegaProdEquiv が**乗法的**(omegaProdChar 乗法性、要確立; ℂˣ abelian)ゆえ
      `Q(i,j).2 = Q(i',j).2 · (omegaProdEquiv.symm(W1-only)).2`、W1-only char は `=omegaProdChar a 1`
      (`omegaProdChar_one_right`) ⟹ `omegaProdEquiv.symm.2 = 1` (`omegaProdEquiv_symm_omegaProdChar`)。∴ κ(j):=Q(0,j).2。
    - **(B) 列が full**: `i↦Q(i,j).1` は injective (alignedOmegaSigmaGrid_inner の joint inj から)、
      `|W1char_tic|=w1` ゆえ全射 ⟹ `∑_i ω_ij^σ = ∑_i chiFam(Q(i,j).1, κj) = ∑_p chiFam(p, κj)`。
    - **κ injective** (κ(j)≠κ(j')): 列 j≠j' の σ-image が直交 (alignedOmegaSigmaGrid_inner) ⟹ chiFam index
      の W2 成分相異。
    - **要 foundational lemma** (未整備、次セッションで先に): (1) omegaProdEquiv の乗法性 (or `.symm` の snd が
      hom)、(2) `e(tic.W2)⊆sdiff.W2` (underlying G-element 保存 `coe`-pattern + W2 membership)、(3) W1-only char
      の omegaProdEquiv.symm snd=1。これらが揃えば (A)(B) は各 ~20-30 行。**完全 factorization (~150 行) より軽い**。
- [x] **(10.6.a) column-independence DONE** (2026-06-23 lane-b 再開セッション, `muColumn_tau1_diff_eq`,
  S12, commit `9d2fc5a0`, axiom-clean=§10 muGrid upstream gate のみ・自前 sorry 0): 任意の非自明列 j,k≠0 で
  `μ_j^τ₁ − μ_k^τ₁ = δ·(∑_i ω_ij^σ − ∑_i ω_ik^σ)`、∴ 残差 `μ_j^τ₁ − δ∑_i ω_ij^σ` は**列 j に非依存**。
  Hypothesis46 **不要** (§10-native): `μ_j − μ_k = ∑_i(α_ij − α_ik)` が A_0-supported
  (`CharacterParameters.alpha_support`、δμ_i0/nζ tail 相殺) → `extends_on_supported` で τ₁=τ → 既landed
  `tau_muGrid_columnSum_diff` (10.5) + `map_sub`。⟹ **full (10.6.a) を「1 列の pin」に還元** (残 = (5.8)
  full-column endgame が single column を確定)。
- ⚠⚠ **構造的発見 (2026-06-23, 次セッション必読)**: §10 muGrid は `CertainTypeHypothesis` 上
  (`(hyp.toCertainTypeHypothesis hG hodd).toHypothesis : S06.Hypothesis ↥M`)、一方 §6 conjugate/column 機構
  (`columnSum_conj_eq` / `column_inv_ne_self` / `certainType_columnSum_conj` / `certainTypeR` /
  `certainTypeExtension`(ν)) は全て **`Hypothesis46` 上** (構造階層 `Hypothesis46 extends CertainTypeHypothesis
  extends Hypothesis`)。**§10 用 `Hypothesis46` builder は存在しない** (§10 は意図的に避け alignedOmegaSigmaGrid 等
  §10-native 版を作ってきた)。`certainType_mu_conj_bridge` は `sigma_chiColumn` (Hypothesis46 σ_L apparatus,
  tic/dade0/tau 込み) に**真に依存**ゆえ §6 conjugate を §10 へ trivial 還元できない。= note の「§6↔§5 reconcile,
  multi-session」の構造的正体。
  - **∴ 残 linchpin の真の前提 = 以下のどちらか (次セッション着手点)**:
    - **route (A) §10 `Hypothesis46` 組立**: tic=`typePData_toTICyclicHypothesis` (在), dade0, tau, subH,
      subH_normal, W2_le_subH, subH_le_K, A_covers, tic_W1/W2/V proofs を §10 type-P データから供給。大物だが
      **certainTypeR (image family) + certainTypeExtension (ν=δ∑ω^σ) + conjugate を一気に解禁**。
    - **route (B) §10-native conjugate identity**: `μ_k = Ind_K^M θ_k` (`muGrid_column_sum_mem_inducedFamily`)
      ⟹ `μ_k.conj = Ind(θ_k.conj) = μ_{k'}`。**❌ 2026-06-23 棄却**: `columnFamily` は `chiColumn`/σ apparatus
      経由の choice 定義 (`exists_columnSignedFamily`) ゆえ σ_L 回避不可。conjugate は §6 σ 機構に内在依存。
    - **⭐ route (B') §6 conjugate 補題を `Hypothesis46`→`Hypothesis` に一般化 (HUB issue 1010, 推奨)**:
      §6 conjugate 補題群 (`columnSum_conj_eq`/`column_inv_ne_self`/`certainType_columnSum_conj`/chain) は
      **実際には Hypothesis-level 構造しか使わない** (chiColumn/sigma_chiColumn_eq_certainType/columnFamily/
      W_odd は全て `namespace Hypothesis`)。1 回の機械的 refactor で §10 host (CertainType.toHypothesis)
      に直接適用可 → conjugate + certainTypeR image family + ν を一気解禁。caller ~15 (§6+§8) 修正要 = cross-lane
      ゆえ HUB。**lane-b は 1010 解決まで image-family 段を保留** (column-independence までは landed)。
  - **その後の σ-endgame reconcile** (route 共通): `eq_smul_chiFam_column_of_vanishOnV` (在) を当てるには
    `μ_{j₀}^τ₁` の sigmaCoeff 2-column {0,±δ} 構造 (要 (5.5) image-family 分解 + **2D chiFam 構造**
    `ω_ij^σ = chiFam(Q(i,j))`, Q が積 `(ρ(i),κ(j))`)。2D 構造の crux = `(omegaProdChar_h a b).comp e
    = omegaProdChar_tic (transp a)(transp b)` (e が W1/W2 分解尊重)。`exists_alignedOmegaSigmaGrid_chiFam_family`
    は per-row のみ (同列異行/2D 直交性を供給せず)。
- [x] **(5.8) abstract combinatorial core DONE** (2026-06-22, `grid_eq_const_column_of_two_col`,
  `S05_GridTrichotomy.lean`, **axiom-clean** `[propext, Classical.choice, Quot.sound]`)。
  norm-w₁ full-column endgame の純代数核: separable grid `a:ι×κ→ℂ` + 2-column support {j,k} +
  係数 {0,δ}/{0,−δ} (δ=±1) + `∑(a)²=|ι|` ⟹ **単一 full column** (column k=δ / column j=−δ)。
  既存 norm-2 `eq_smul_chiFam_diff_of_vanishOnV` は constant-column を**排除**するが、これは逆に
  **採用** (separability+零列 q₀ で column-constant → Parseval mass → `a(i₀,j)²+a(i₀,k)²=1` →
  {0,±1} で片方のみ ±1)。= (5.8) proof step 4 を忠実に capture、reusable。
- [x] **(5.8) σ-level wrapper の (a) Parseval + (d) sigmaCoeff↔core 配線 DONE** (2026-06-22,
  `S05_SigmaTrichotomy.lean`, 両 **axiom-clean** `[propext, Classical.choice, Quot.sound]`, full build
  3881 green):
  - **(a) Fourier 復元** `eq_sum_sigmaCoeff_smul_chiFam_of_inner_self_eq`: Parseval *等式*
    `⟨X,X⟩ = ∑_pq sigmaCoeff(X) pq · conj(sigmaCoeff(X) pq)` (= X が Im σ ⊥ 成分を持たない、β=0)
    ⟹ `X = ∑_pq sigmaCoeff(X) pq • χ_pq`。chiFam 直交性のみ依存。`span(chiFam)` を定義せず Parseval-等式を
    仮説化したのが鍵 (norm-2 endgame は ‖·‖²=0 で coeff を消すが、(5.8) は復元が必要)。
    ⚠ 設計知見: index 積型に global Fintype 無 (codebase は局所 `Fintype.ofFinite`) → 文の `∑ pq`
    が Fintype を metavar 化 ⟹ 両 W1/W2 char-group の `[Fintype …]` を**instance 引数**に取る。
  - **(d) σ-level full-column endgame** `eq_smul_chiFam_column_of_vanishOnV`: X が V で消え、sigmaCoeff が
    2-column {jcol,kcol} support + {0,δ}/{0,−δ} entries + ⟨X,X⟩=w₁ + Parseval-等式 ⟹
    `X = δ•∑_p χ_{(p,kcol)}` ∨ `X = −δ•∑_p χ_{(p,jcol)}`。abstract core `grid_eq_const_column_of_two_col`
    (係数 grid → full column) + Fourier 復元 (full column → class-function 等式) を合成。
    separability は `sigmaCoeff_add_eq` (V-消失) で供給、entries 実数性で `∑ s² = ∑ s·conj s` を橋渡し。
    = norm-w₁ 版 `eq_smul_chiFam_diff_of_vanishOnV`。**(10.6.a) を (5.5) の出力に honest 還元**。
- [x] **(5.8) endgame 仮説 2/4 DONE (2026-06-22 lane-b 再開セッション)** — §5-gate 回避経路を確立:
  - **`OrthonormalCharacterImageFamily` (S07) は 2 元限定でなく汎用**と判明 (`imageSet : Finset`、
    `image_eq : τ(χ−χ̄)=∑_{α∈R} α` のみ要求) ⟹ column μ_k に直接適用可。これが (5.5)-for-column の正路。
  - **column-difference DONE** (`tau_muGrid_column_diff` + `tau_muGrid_columnSum_diff`, commit `bd4c8340`,
    axiom-clean=§10 upstream gate のみ): `τ(μ_ij−μ_ik)=δ(ω_ij^σ−ω_ik^σ)` + summed `τ(μ_j−μ_k)=δ∑(...)`。
    `alpha_tau_image` の系 (α tail 相殺)。= column image family の `image_eq` (R={δω_ij^σ}∪{−δω_ik^σ})。
  - **μ_k^τ₁ vanishes on V DONE** (`muColumn_tau1_vanishes_on_typePV`, commit `02ec7e03`, axiom-clean):
    (5.8) χ=ζ̄ ルート。(4.7)`muColumn_sub_conj_support` + `tau_apply_of_mem_typePV` + 誘導指標 vanishing
    + `tau_muColumn_sub_conj_eq_tau1` + 完成済 `tau1_zeta_vanishes_on_typePV`(ζ̄)。
  - 🔑 **§5-gate 回避が確定**: `tau1_zeta_vanishes_on_typePV` が honest 完成 (norm-1 NC≤2 トリック) ゆえ
    column 経路は直接 reduction が要する §5-gated `ζ̄^τ₁⊥Imσ` を**通らない** — (5.5) が μ_k^τ₁ を直接決定し
    V-vanishing は単一指標 vanishing + (4.7) で出る。‖μ_k^τ₁‖²=w₁ も既存 (`muColumn_tau1_inner_self`)。
  - **残 = sigmaCoeff 2-column 構造** ((5.8) 仮説 4/4 のうち最後): column `OrthonormalCharacterImageFamily`
    本体構築 (要 conjugate-column `conj(μ_k)=μ_{k'}` + orthonormality) → `CharacterPsiDecomposition.ofProjection`
    (ψ=0, tau1=coh.tau1) → (5.5)`eq_sum_of_psi_eq_zero` → sigmaCoeff 翻訳 → σ-endgame 適用。
  - **🗺 次セッション設計 (§6 `certainTypeR` を雛形に)**: §6 は **column 用 `OrthonormalCharacterImageFamily`
    の完全な雛形** `certainTypeR` (`S06_CertainTypeCoherence.lean:639`) を既に持つ — `imageSet =
    image (certainTypeRImage χ₂ χ₂⁻¹)` (signed σ-image `±δ·ω^σ`)、`mem_ZIrr`/`orthonormal`
    (`certainTypeRImage_inner`/`_injective`)、`image_eq` (`columnSum_conj_eq` + `dadeICM_columnDiff_eq_sum`)。
    ⚠ これは §6 Hypothesis46 (dade0=W\W2) ベースゆえ §10 (hyp.tau=typePV) に**直流用不可** — §10 版を
    mirror 構築する: (i) **conjugate-column** `conj(∑_i muGrid i k)=∑_i muGrid i k'` (§10 μ_k は §6
    `columnSum χ₂(k)` に一致 → `columnSum_conj_eq`(`(columnSum χ₂).conj=columnSum χ₂⁻¹`) → k'=
    `finCardEquivCharacterGroup⁻¹(χ₂(k)⁻¹)`; k≠k' は `column_inv_ne_self` 相当 = 奇位数で非実)、
    (ii) signed §10 σ-image 族 (alignedOmegaSigmaGrid 由来) + orthonormality (chiFam 直交性)、
    (iii) `image_eq` = `tau_muGrid_columnSum_diff` (本セッション済) + (i)、(iv) ofProjection の
    `htau1_agrees` = column-diff + `coherent.extends_on_supported`、`htau1_mem` = `extension_mem_ZIrr`。
    sigmaCoeff 翻訳は `exists_alignedOmegaSigmaGrid_chiFam_family` (R(μ_k) 元 ↔ chiFam 元) 経由。
- [ ] **残 linchpin = (5.8) wrapper の (b)(5.5)**: sigmaCoeff 2-column structure (上記「残」)。
  - (b) **(5.5)** `χ^τ₁ = ∑_{α∈R(χ)} α` を certain-type column μ_k に適用し R(μ_k)=2-column σ-構造を出す。
  - (c) ✅ **(4.7) A-support + μ_k^τ₁ vanishes on V DONE** (上記)。
  - ⚠ **真の gate は §6 certain-type μ ↔ §5 sigmaCoeff grid の reconcile** (deep §6↔§5、multi-session)。
    `IsCoherent` は abstract isometry で (5.5) を carry しない (2026-06-22 確認) — (5.5) を coherence
    isometry に対し別途立てる必要。`S07_RetargetScaled.lean:451`/`CharacterDifferenceImage`
    (`S07_Coherence.lean:395`) が R(χ) 機構の候補だが、§6 columnFamily R(μ_k) との reconcile が crux。
  - ⚠ Explore 監査 (2026-06-22) は「400-500 行・blocker 無」と評価したが item B (μ_k 2-column 分解) を
    「implicit」と認めており、これが linchpin。over-optimism に注意 ([[scaffold-sorry-free-not-done]] audit 版)。
- [x] **(10.6.a) M→G→τ₁ reduction chain DONE** (2026-06-22, commits `88a95a70`/`3d9eb887`/`a2ff9e18`):
  - M-side diagonal IP `(α_ij, μ_j − dζ̄) = 1` (`muGridAlpha_inner_muColumn_self_sub_conj`)
  - G-side diagonal IP `(α_ij^τ, (μ_j − dζ̄)^τ) = 1` (`muGridAlpha_tau_inner_muColumn_self_sub_conj`)
  - τ/τ₁ split `(α_ij^τ, μ_j^τ₁ − dζ̄^τ₁) = 1` (`muGridAlpha_tau1_inner_muColumn_self_sub_conj`)
  ⟹ (10.6.a) reduction opening 確立。
- **⊥落とし isometry orthogonality 2/3 DONE** (2026-06-22, S12, isometry pattern of `zeta_tau1_inner_self`):
  - `zeta_tau1_inner_conj`: `(ζ^τ₁, ζ̄^τ₁)=0` (**完全 axiom-clean**; isometry + (ζ,ζ̄)=0, ζ̄≠ζ irr)。
  - `zeta_tau1_inner_muColumn`: `(ζ^τ₁, μ_k^τ₁)=0` (sorryAx=upstream muGrid gate のみ=§10 全 muGrid lemma と同一、自前 sorry 0; isometry + ∑_i (ζ,μ_ik)=0 degree mismatch)。
- ⚠ **訂正 (audit over-optimism)**: ⊥落とし の残 3 番目 orthogonality `ζ̄^τ₁⊥Imσ` は **in-stock でない**。
  旧記述「tau1_zeta_vanishes 経由」は誤り — Pf (5.8) 原文では `χ^τ₁⊥Imσ ⟹ vanish on V (by 3.2.d)`
  であって**逆ではない**。vanish-on-V から ⊥Imσ は出ず、これは **§5 (5.3.b)/(5.5) gated** (5.8 σ-wrapper
  と同じゲート)。∴ ⊥落とし全体 = §5 gated; in-stock な 2 orthogonality のみ先行着地。
  残 (10.6.a) = `ζ̄^τ₁⊥Imσ` (§5) + (5.8) σ-wrapper。
- [ ] (10.6.a): diagonal IP + τ/τ₁ transfer (既存 `muGridAlpha_tau_inner_muColumn_sub_conj` 類比) +
      (5.8) → `μ_j^τ₁ = δ∑ω_ij^σ`。
- [ ] `zeta_tau1_norm_bound` Prop を (10.6.b) の genuine 主張に materialize + 証明。
- [ ] `tau1_values_and_norm_bound` を sorry-free に。

## 📋 (5.8) 詳細スコープ (2026-06-22 lane-b 精読) — multi-session piece

(5.8) [`04.7:119`] = coherence isometry τ₁ 下での certain-type column-char μ_k の像決定。原文証明の依存:
1. **(5.5)** `χ^τ₁ = ∑_{α∈E} α (E⊆R(χ))` ← (5.4) with ψ=0。**(5.4) は repo S07 在庫**。R(μ_j)=
   `{δ_j ω_ij^σ, −δ_j ω_ik^σ}` (2-column σ-構造, k=conj(j) 列) ← (5.3.b)/(4.9)。⟹ μ_k^τ₁ = ∑_i a_ik ω_ik^σ
   + ∑_i a_ij ω_ij^σ, a_ik∈{0,δ_k}, a_ij∈{0,−δ_k}。
2. **μ_k^τ₁ vanishes on V** (crux) ← χ∈S∩Irr(L)(=ζ deg w₁) + **(4.7)** `χ(1)μ_k−μ_k(1)χ ∈ ℤ[S,A]`
   + **ζ^τ₁ vanishes on V (✅ `tau1_zeta_vanishes_on_typePV`)** + A∩V=∅ + τ 定義。
3. **(3.7) separability** ⟹ a_ik=a_0k, a_ij=a_0j (row-constant)。repo S05 `sigmaCoeff_add_eq` 在庫。
4. **‖μ_k^τ₁‖²=w₁** + coeffs∈{0,±1} ⟹ a_0k²+a_0j²=1 ⟹ 一方のみ ±1 ⟹ **full column** δ∑ω_ik^σ or −δ∑ω_ij^σ。
5. uniqueness ("j,k のみ") ← Theorem (4.9) summed isometry (repo S06 `certainType_diff_dade_sum_eq` 在庫)。

**在庫**: (5.4) [S07]、(4.9) summed isometry [S06]、(3.7)/(3.8) [S05]、ζ^τ₁/ζ̄^τ₁ vanish on V [S12]、
diagonal IP `(α_ij,μ_j−dζ̄)=1` [✅本 issue]。**要新規**: (5.5) を certain-type column R(μ_j) で適用する形 +
**(4.7) A-support of `w₁μ_j−dζ`** + **(5.8) combinatorial core** (2-column separable + norm-w₁ → full column,
= 私の (10.5) `eq_smul_chiFam_diff_of_vanishOnV` の full-column 類比、grid 機構流用可) + assembly。

**(10.6.a) §10-specialized route** (full (5.8) より tractable な可能性): reduction
`(α_ij^τ, μ_j^τ₁−dζ̄^τ₁) = (δ(ω_ij^σ−ω_i0^σ), μ_j^τ₁)` は my infra (diagonal IP + ζ^τ₁⊥σ + isometry) で provable
だが、最終 `= δ∑ω_ij^σ` は (5.8) core 必須。⟹ (5.8) combinatorial core (full-column trichotomy) が真の linchpin。

**評価: (5.8) は §5-§8 coherence 機構に深く絡む multi-session piece** (上記 4 新規部品 + assembly、~数百行)。
単発でなく focused 複数セッションで攻めるべき。次着手の clean entry = **(5.8) combinatorial core を S05 一般補題化**
(my (10.5) trichotomy の full-column 類比、§5 σ-machinery のみ依存、reusable)。

## 完了条件

`tau1_values_and_norm_bound` (S12) が sorry-free。axiom footprint = §10 muGrid 系上流 gate のみ。
full build + AxiomsCheck green。

## 参照

- issue 1007/1008 (closed): (10.5) Dade-image identity + (10.3) n-even。
- `tau1_values_and_norm_bound` (S12:3521)、`CharacterParameters.zeta_tau1_norm_bound`。
- (5.8) = `references/peterfalvi/04.7_pp_25_29_Coherence.mmd:119`。
- 上位: [[ft-endgame-two-poles]] / `notes/peterfalvi/s12_s10_character_bridge.md`。
