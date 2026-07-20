---
id: 1049
slug: feit-sibley-lemma1a-general-adjoin
title: "Lemma 1(a) = 一般 degree-bound coherence adjoin (Isaacs 7.14): Dade特殊化 xAdjoinStep の一般化"
created: 2026-07-21
---

# Lemma 1(a) = 一般 degree-bound coherence adjoin (Isaacs 7.14): Dade特殊化 xAdjoinStep の一般化

## 背景

lane a 付録 carve-out (9204) の `Appendices/FeitSibley.lean` に 5 sorry。上流の
**Lemma 1(a) `coherent_adjoin_of_degree_bound`** = Peterfalvi Appendix IV Lemma 1(a)
= Isaacs *Character Theory* Thm 7.14 = mathcomp `extend_coherent` (PFsection5.v:1124) =
Peterfalvi (5.6) の **mixed-degree coherence adjoin**。

**重要な調査結果 (2026-07-21)**: この定理の hard content は**すべて repo に一般形で存在**する。
FT 本文 (§6.6 (9.11)) は equal-degree union しか使わなかったので、一般 adjoin は Dade map τ に
**特殊化された形でしか組み立てられていない** (`xAdjoinStep` = `S08_CoherenceCorePart1/CoherentAdjoin.lean:530`)。
Lemma 1(a) はこれを一般 `S07.Hypothesis` τ に**一般化**する task ([[feedback-generalize-specialized-fully]]
[[repo-stronger-hypothesis-is-specialization-not-gap]])。

### 既存の一般 building blocks (再利用可)

- `CharacterPsiDecomposition.ofProjection` (NormInequalities) — split constructor (β → X-Y projection)
- `norm_eq_and_X_eq_sum_of_norm_Y_ge` / `inner_self_chi_re_le_inner_self_X` — subcoherent_norm (5.4 a,b)
- `lambda_eq_zero_and_Z_eq_zero` / `Y_eq_nsmul_tau1_of_lambdaForm` (PsiDecomposition) — **degree bound → defY collapse (5.6.2)、一般**
- `X_eq_of_tau1_eq_on_chi` / `X_eq_tau1_chi_of_Y_eq` / `conjImage_eq_neg_sum_sdiff` — (5.6.3) 一般
- `crux1_of_collapse` / `crux1_of_memberFamily` (Dade `_hτ` 未使用) / `inner_decomposition_X_extension_member_eq_zero` / `inner_Y_extension_member_eq` — **一般または Dade 未使用**
- `retarget_isCoherent_of_decompositions` (CoherenceUnion) / `retarget_isCoherent_of_extensionImage` (CoherentAdjoin) — assembly engine
- `coherentUnion_of_glued_of_bridge` (S07_BridgeCoherent) — bridge gluing

### 一般化が要る Dade 特殊化 helper (4 個)

1. `inner_dade_extension_of_supported` (S08_YsetInner:413) — cross-term ⟨τ u, ext δ⟩=⟨u,δ⟩。
   一般版は `hyp.tau_isometry_diff` + `hcoh.extends_on_supported` で証明可 (u∈zSuppSpan S A, δ∈zSuppSpan S₁ A)。
2. `memberExtensionDecomposition` — 各 member の ψ=0 分解。一般版は `hyp.difference_image χᵢ` (CharacterDifferenceImage) から R(χᵢ) family + ofProjection。
3. `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` — R(χᵢ)⊥R(χ)。一般版は `hyp.difference_images_orthogonal`。
4. `retarget_isCoherent_of_extensionImage` — 最終 bridge。一般 τ 版。

## やること

- [x] 新 leaf `OddOrder/Peterfalvi/S08_GeneralAdjoin.lean` 作成 + `OddOrder.lean` 配線 (orphan gate OK)
- [x] **helper 1**: 一般 cross-term `inner_tau_extension_of_supported` (build green)
- [x] **helper 4**: 一般 bridge `retarget_isCoherent_of_extensionImage_general` — Dade の 3 箇所の
  `dadeIntegralCharacterMap_inner_eq_on_supported_span` を set-based `hisom` 仮説 1 つで置換。
  初回 build green (Dade body の mechanical transcribe が通った)。
- [x] **crux1** `crux1_of_memberFamily_general` (degree bound → crux1) — build green (commit 4f77ecd83)
- [x] **hcoeffval producer** `inner_Y_extension_member_eq_general` — build green
- [x] **member decomp** `memberExtensionDecomposition_general` (tau1=ν) — build green
- [x] **χ decomp** `decompositionDaFromDiff_general` (tau1=τ, 差 lattice isometry) — build green

**⇒ Isaacs 7.14 adjoin の hard math の general leaf は全て landed (6 lemma, 全 build green)。**
残りは統合と配線のみ:

- [x] **統合 `adjoinPairCoherent_general`** ⭐ 完成 (commit 17bd6a97d, build green)。以下は実施済の配線記録:
  各 xAdjoinStep hypothesis を対応する general leaf で discharge:
  - `Da` ← `decompositionDaFromDiff_general` (imageFamily = `(diff_image χ).toOrthonormalImage`)
  - `Dmem i` ← `memberExtensionDecomposition_general` (imageFamily = `(diff_image (χmem i)).toOrthonormalImage`)
  - `hortho_mem` ← `CharacterDifferenceImage.toOrthonormalImage_orthogonal` +
    R(χmem i)⊥R(χ) の Orthogonal (差 image の直交性; FeitSibley では `hyp.difference_images_orthogonal`)
  - `hXortho` ← `inner_decomposition_X_extension_member_eq_zero` (完全一般, htau1 は memberExtensionDecomposition_general の tau1=ν ゆえ rfl)
  - `hfound` ← `inner_tau_extension_of_supported` (helper 1)
  - `hcoeffval` ← `inner_Y_extension_member_eq_general`
  - `hcrux1` ← `crux1_of_memberFamily_general`
  - `hcrux2` ← `inner_extension_member_orthogonal_imageSet` (CoherenceUnion:630, S07 一般) を R(χ) 上で sum
  - 最終 ← `retarget_isCoherent_of_extensionImage_general` (helper 4)
  結論: `IsCoherent τ (S₁ ∪ {χ, χ̄}) A`。
### ⚠ 特殊化債務 (2026-07-21 発見): engine は integer-ratio 版

`adjoinPairCoherent_general` / `crux1_of_memberFamily_general` は `deg : ι → ℕ` (**integer** 度数比)
+ unit norm (`mc = 1`) の特殊化 (repo 既存 `crux1_of_memberFamily` に倣った)。だが Peterfalvi
Lemma 1(a) の degree bound `2χ₀(1)ψ(1) < ∑_{χ∈S₀} χ(1)²` は anchor χ₀ の被除性を **ψ にのみ**
要求 (`χ₀(1)|ψ(1)`)、member χ には課さない ⟹ 度数比 χ(1)/χ₀(1) は **rational**。
mathcomp `extend_coherent` の degree bound も `∑ χ(1)²/‖χ‖²` (rational `a_ξ = ξ(1)/ξ₁(1)/‖ξ‖²`)。

**⟹ FeitSibley (𝒮⊆Irr(H) は unit norm だが度数比 rational) には rational-ratio 版が要る可能性大。**
核心 `lambda_eq_zero_and_Z_eq_zero` (PsiDecomposition) は `rc mc : ι → ℝ` で**既に一般**なので、
`crux1_of_memberFamily_general` を real `rc` (unit norm `mc=1` 保持で可) へ再一般化する道はある。
⚠ ただし projection 係数 `cᵢ = ⟨Da.Y, νχᵢ⟩ ∈ ℤ` と `cᵢ = a·[i=i₁] − λ·rcᵢ` (λ∈ℤ, rc rational) の
整合は subtle (integer 版は自明)。着手前に FeitSibley の実度数構造 (Ind_Q^H φ, deg = d·φ(1)) を精査し、
rational 要否を確定すること。

- [ ] **FeitSibley 配線**: `coherent_adjoin_of_degree_bound` を engine へ (rational 版が要るなら先に engine 拡張)。
  ⚠ statement 調整が要る: 現状 `S = S₀ ∪ {ψ}` 単一 adjoin + degree bound `2·deg χ0·deg ψ < ∑ deg²`。
  engine は pair `{ψ,ψ̄}` adjoin + normalized `2a < ∑ (deg)²` (a = deg ψ/deg χ₀, unit norm)。
  `hisom` は `hyp.tau_isometry_diff` から (member-diff が A-supported を示す); m₁=1 (irreducible)。

## ⚠ statement 設計判断 (2026-07-21 調査)

FeitSibley 現行 `coherent_adjoin_of_degree_bound` は Peterfalvi の phrasing 通り
**single-ψ** (`S = S₀ ∪ {ψ}`, `(S₀,τ) coherent`)。だが engine (`adjoinPairCoherent_general` =
xAdjoinStep 一般版) は **pair-adjoin** (`(S₁,τ) coherent → IsCoherent τ (S₁∪{ψ,ψ̄}) A`)。
`hyp : Hypothesis S A` は S conj-closed ゆえ ψ̄≠ψ なら **ψ̄∈S₀**。すると engine が要る
「S₁ = S₀\{ψ̄} が coherent」と FeitSibley が与える「S₀ (=S₁∪{ψ̄}) が coherent」が食い違う
(coherence は単調でない)。

**裁定 (a への territory 内判断)**: FeitSibley `coherent_adjoin_of_degree_bound` を
**pair-adjoin 形へ改める** — `(S₁,τ) coherent` + `χ` (=ψ, 非実既約, ‖χ‖²=1, S₁⊥) + unit-norm
member family + degree bound `2a<∑(deg)²` ⟹ `IsCoherent τ (S₁∪{χ,χ̄}) A`。
理由: (i) Isaacs 7.14 / Peterfalvi (5.6) の実内容は共役 orbit の adjoin。
(ii) FeitSibley Theorem step (1) の用法は S(S'Q₂)⊆S(S'Q₃) の pair 逐次 adjoin (単一 ψ でない)。
(iii) Peterfalvi の "S=S₀∪{ψ}" は conj-closed 文脈での shorthand。
現行 single-ψ statement は sorried ゆえ改訂は territory 内で自由 (a 所有)。docstring に Peterfalvi
番号 (Appendix IV Lemma 1(a) / Isaacs 7.14) は保持。

## 完了条件

`FeitSibley.coherent_adjoin_of_degree_bound` の sorry が消え、`lake build` green + AxiomsCheck OK。
(理想: Dade `xAdjoinStep` を一般版の薄い instantiation に refactor して重複削減 — follow-up 可)

## 参照

- `OddOrder/Peterfalvi/Appendices/FeitSibley.lean:265` (sorry)
- `OddOrder/Peterfalvi/S08_CoherenceCorePart1/CoherentAdjoin.lean:530` (`xAdjoinStep` = Dade特殊化 template)
- `OddOrder/Peterfalvi/S07_Coherence/PsiDecomposition.lean:73,161` (一般 collapse)
- `references/peterfalvi/pdf/09.0_*.pdf` p.144 (Lemma 1), coq `PFsection5.v:1124` (`extend_coherent`)
