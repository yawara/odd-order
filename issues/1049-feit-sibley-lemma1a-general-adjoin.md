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
### 🔴 要修正 (2026-07-21 continuation): engine の hisom が FeitSibley-satisfiable でない

**engine の `hisom` (set-based `∀ T, (∀ s∈T, s.support⊆A) → ∀ φζ∈ℤ[T], ⟨τφ,τζ⟩=⟨φ,ζ⟩`) は Dade
では satisfiable (`dadeIntegralCharacterMap_inner_eq_on_supported_span` は全 supported class function
上の isometry) だが、一般 `Hypothesis.tau_isometry_diff` は `zSupportedSpan S A` (∈ℤ[S]∧supported)
のみ保証**。任意 supported T (元が ℤ[S] 外) はカバーできない ⟹ 現行 hisom は FeitSibley で供給不能。
engine の math は正しく完成 (build green) だが、この**仮説が一般 Hypothesis で充足不能**
([[scaffold-sorry-free-not-done]]: build-green≠仮説充足可能。commit の「完成」は Dade-satisfiable の
意味に留まる)。

**修正案 (B, minimal)**: 3 defs (`retarget_isCoherent_of_extensionImage_general` /
`decompositionDaFromDiff_general` / `adjoinPairCoherent_general`) に `Samb⊇S₁∪{χ,χ̄}` param 追加、
hisom precondition を `s.support⊆A` → `s∈zSupportedSpan Samb A` に変更。use site (~6 箇所: hSdiff/
hySdiff/hfound の set 証明) を「support⊆A」→「∈ℤ[Samb]∧supported」に拡張 (χ,χ̄,χ₁,χmem i,y は全て
Samb ⊆ の元ゆえ ℤ[Samb] 自明)。FeitSibley 側は `hyp.tau_isometry_diff` (Samb=𝒮) + ℤ[T]⊆zSupportedSpan
閉包で供給。関連既存インフラ: `zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration` (209),
`span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs` (173, scaled-diff)。

### ✅ 配線 feasibility 確定 (2026-07-21 continuation)

**(1) integer-ratio engine が FeitSibley に十分** — 𝒮={Ind_Q^H φ} は deg=d·φ(1)。reduction 後
Q₁ は非自明 p-群ゆえ**非完全** ⟹ 非自明 linear θ∈Irr(Q₁) を持ち、φ=1·θ (linear, deg 1, Q₁⊄Ker)
で **𝒮 は必ず degree-d member を含む**。これを anchor χ₀ (χ₀(1)=d) にとれば比 χ(1)/χ₀(1)=φ(1)∈ℕ
で **integer ratio**、かつ χ₀(1)=d | d·φ(1)=ψ(1) (Lemma 1(a) の χ₀(1)|ψ(1) も満たす)。

**(2) hSgen/hgen 討伐可** — Dade chain (`XAdjoinStepInput.adjoin`, CoherentAdjoin:940) の pattern:
`hgen` は一般 lemma `zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration` (S07) で `hSgen` +
degree 事実から従う。`hSgen : ℤ[S₀] ≤ ℤ[supported S₀ ∪ {χ₀}]` は χ = (χ−deg·χ₀)+deg·χ₀
(integer deg で χ−deg·χ₀ は degree 0 = supported) から。⟹ engine 一般版でも同 pattern で discharge。

**⟹ 次 iteration の target = FeitSibley を integer engine へ配線** (rational 不要)。plumbing:
member family = S₀ (or 代表), R-family = `hyp.difference_image`, hisom = `hyp.tau_isometry_diff`
(ℤ[T]⊆zSupportedSpan S A の closure plumbing), hSgen/hgen = 上記 pattern, degree 整数性 =
degree-d anchor。statement は engine 準拠の pair-adjoin/member-family 形へ改訂。

### ⚠ 特殊化債務 (2026-07-21): abstract Lemma 1(a) は rational — engine は integer 版 (consumer 無し)

engine は integer ratio 版。Peterfalvi 抽象 Lemma 1(a) は rational 比を許す (χ₀(1)|ψ(1) のみ要求)。
**FeitSibley Theorem の実用法は integer 比** (上記 (1)) ゆえ rational 版に consumer は無い。
rational faithful 版の構成は判明済 (**scaled difference trick**): member 差を `χᵢ−rcᵢ·χ₁` (rc rational,
非整数 ⟹ ℤ[S₁] 外) でなく **`d1·χᵢ − dⱼ·χ₁` (d1=χ₁(1), dⱼ=χᵢ(1), 整数係数, degree 0 で supported)**
に取れば ν-isometry (ℤ[S₁]) が使え、⟨Y,νχᵢ⟩ = a·⟨χ₁,χᵢ⟩ − (a·m₁+μ)·(dⱼ/d1) が出る。
`lambda_eq_zero_and_Z_eq_zero` (real rc/mc) がそのまま consume。度数 bound は 2a<∑(dⱼ/d1)² =
Peterfalvi の 2·ψ(1)·χ₁(1)<∑χ(1)²。低優先で inner_Y/crux1/adjoinPair を rc real へ再導出すれば
abstract 版も閉じる (integer engine を subsume)。

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
