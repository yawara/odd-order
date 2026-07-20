---
id: 1050
slug: rational-adjoin-bridge-refit
title: "abstract-rational Lemma 1(a): bridge hSgen を per-member scaled+crux1 へ (rational 比 faithful 版)"
created: 2026-07-21
---

# abstract-rational Lemma 1(a): bridge hSgen を per-member scaled+crux1 へ

**優先度: 低 (deferred follow-up, 現 consumer 無し)**。issue 1049 から分離。

## 背景

issue 1049 で `FeitSibley.coherent_adjoin_of_degree_bound` を **integer-ratio 版**で閉じた
(pair-adjoin 形 → `adjoinPairCoherent_general`、build green + axiom-clean)。だが Peterfalvi
抽象 Lemma 1(a) / Isaacs 7.14 は **anchor 被除性を ψ にのみ要求** (`χ₀(1) ∣ ψ(1)`)、member χ には
課さない ⟹ 度数比 `χ(1)/χ₀(1)` は本来 **rational**。FeitSibley の実用法は integer 比
(degree-d anchor χ₀(1)=d, χ(1)=d·φ(1), 比=φ(1)∈ℕ) なので integer 版で FT 経路は閉じるが、
**faithful な一般 Isaacs 7.14 は rational 版が正** ([[feedback-generalize-specialized-fully]])。

## 現状 (2026-07-21)

- **rational engine の coeff 部は完成** (commit cb7429704): `inner_Y_extension_member_eq_general`
  (scaled diff `d₁·χᵢ−dⱼ·χ₁`, division-free), `crux1_of_memberFamily_general` (rc:ι→ℝ),
  `adjoinPairCoherent_general` (degMem:ι→ℕ 絶対度数, rc=degMem i/degMem i₁, bound 2a<∑(degMem i/degMem i₁)²)。
- **残る不完全性 = bridge の `hSgen`** (`retarget_isCoherent_of_extensionImage_general`,
  `S08_GeneralAdjoin.lean:154`): `hSgen : ℤ[S₁] ≤ ℤ[zSupportedSpan S₁ A ∪ {χ₁}]` は
  **rational 比では偽** — member χᵢ (比が非整数) は `χᵢ − rc·χ₁` が supported でも rc∉ℤ ゆえ
  `ℤ[supported∪{χ₁}]` に入らない (`χ₁(1)·χᵢ − χᵢ(1)·χ₁` = scaled diff は入るが χᵢ 自体は入らない)。
  現行の `adjoinPairCoherent_general` も `hSgen` を要求するので、integer-ratio 用途に限られる。

## やること

`retarget_isCoherent_of_extensionImage_general` の `hX_ortho` (S08_GeneralAdjoin.lean:282) を
**per-member scaled+crux1 で再導出**する (~40-60 行):

- [ ] 現行 `hX_ortho : ∀ ξ ∈ ℤ[S₁], ⟨νξ, X⟩ = 0` は `hkey ξ (hSgen hξ)` (ξ を supported∪{χ₁} の span
  で表す) 経由。これを **各 member χᵢ ごとに scaled diff `d₁·χᵢ−dⱼ·χ₁` (∈ℤ[S₁,A]) と crux1 の
  一次結合**で `⟨νχᵢ, X⟩=0` を出す形へ置換。
- [ ] `hSgen`/`hkey`/`hkeyd` hypothesis を除去し、caller (`adjoinPairCoherent_general`) が
  scaled-diff 経由の per-member 直交性を供給する形へ signature 変更。
- [ ] `adjoinPairCoherent_general` の `hSgen` param も除去 → `coherent_adjoin_of_degree_bound` から
  `hdvd` (integer 被除性) を落として **anchor|ψ のみ**の faithful 版へ。

## 完了条件

`adjoinPairCoherent_general` (と `coherent_adjoin_of_degree_bound`) が **anchor `χ₀(1) ∣ ψ(1)`
のみ** (member 比 rational 許容) で `IsCoherent τ (S₁∪{χ,χ̄}) A` を結論。build green + axiom-clean。
integer 版を subsume。

## 参照

- `OddOrder/Peterfalvi/S08_GeneralAdjoin.lean:131` (`retarget_isCoherent_of_extensionImage_general`,
  `hSgen`/`hkey`/`hkeyd`), `:561` (`adjoinPairCoherent_general`, `hSgen` param)
- issue 1049 (integer 版完成の記録), `S07_Coherence/DifferenceImage.lean:173` (integer hSgen lemma)
- coq `PFsection5.v:1124` (`extend_coherent`, rational `a_ξ = ξ(1)/ξ₁(1)/‖ξ‖²`)
