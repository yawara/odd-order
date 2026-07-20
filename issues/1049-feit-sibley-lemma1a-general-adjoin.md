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
- [ ] **crux producer**: 一般 member-family → crux1/crux2 (xAdjoinStep の crux 部の一般化)。
  helper 2 (`(hyp.difference_image hχ).toOrthonormalImage` で R(χ) 構成 — 一般 constructor 既存),
  helper 3 (`toOrthonormalImage_orthogonal` + `hyp.difference_images_orthogonal`),
  `crux1_of_memberFamily` (Dade 未使用の一般 core), `inner_decomposition_X_extension_member_eq_zero`
  (一般), `decompositionPair` (一般) を組んで crux1/crux2 を出す。
- [ ] 一般 `adjoinPairCoherent` = crux producer + `retarget_isCoherent_of_extensionImage_general`
- [ ] FeitSibley `coherent_adjoin_of_degree_bound` を一般定理へ配線 (statement を Peterfalvi/engine
  準拠へ調整: pair {ψ,ψ̄} adjoin + normalized degree bound; hisom は `hyp.tau_isometry_diff` から供給)

## 完了条件

`FeitSibley.coherent_adjoin_of_degree_bound` の sorry が消え、`lake build` green + AxiomsCheck OK。
(理想: Dade `xAdjoinStep` を一般版の薄い instantiation に refactor して重複削減 — follow-up 可)

## 参照

- `OddOrder/Peterfalvi/Appendices/FeitSibley.lean:265` (sorry)
- `OddOrder/Peterfalvi/S08_CoherenceCorePart1/CoherentAdjoin.lean:530` (`xAdjoinStep` = Dade特殊化 template)
- `OddOrder/Peterfalvi/S07_Coherence/PsiDecomposition.lean:73,161` (一般 collapse)
- `references/peterfalvi/pdf/09.0_*.pdf` p.144 (Lemma 1), coq `PFsection5.v:1124` (`extend_coherent`)
