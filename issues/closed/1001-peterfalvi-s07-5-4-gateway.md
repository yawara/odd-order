---
id: 1001
slug: peterfalvi-s07-5-4-gateway
title: "Peterfalvi (5.4) gateway: general orthonormal difference lattice + norm inequalities"
created: 2026-05-30
---

# Peterfalvi (5.4) gateway: general orthonormal difference lattice + norm inequalities

## 背景

Round-9 roadmap Track B. 既存 `S07_Coherence.lean` の 2 元 `CharacterDifferenceImage`
(R(χ) = ε·(μ-ν), ‖·‖²=2) を Peterfalvi (5.2.d) の一般形「R(χ) = ℤ[Irr G] の
orthonormal subset, (χ-χ̄)^τ = ∑_{α∈R(χ)} α」へ一般化し, その上の (5.4) norm 不等式を立てる.
(5.4) は §7 内 technical hub ((5.5)/(5.6)/(5.7) が依存), §8-§16 coherence 経路の土台.

## やること

- [x] **B1**: `OrthonormalCharacterImageFamily τ χ` struct (imageSet R(χ), mem_ZIrr,
  orthonormal δ_{α,β}, image_eq) + API (inner_self_of_mem, inner_eq_zero_of_ne,
  image_conjugateDifference, Orthogonal predicate = 5.2.e). 非空性証拠
  `CharacterDifferenceImage.toOrthonormalImage` (2 元 → R(χ)={ε·μ,-ε·ν}).
- [x] **整数 Cauchy-Schwarz infra** (ZIrrFourier): int_le_sq, int_eq_sq_iff,
  finset_sum_le_sum_sq, finset_sum_eq_sum_sq_iff.
- [x] **orthonormal Parseval infra** (ZIrrFourier): inner_orthonormalSum_eq_coeff,
  inner_self_orthonormalSum_eq_sum_sq, inner_orthonormalSum_sum_eq_sum_coeff.
- [x] **inner_conj_symm** (ZIrrFourier): ⟨ψ,φ⟩=conj⟨φ,ψ⟩ ((χ,ψ)=0⟹(ψ,χ)=0 用).
- [x] **B2 (5.4.a)**: `CharacterPsiDecomposition` setup + keystone
  `inner_self_chi_eq_sum_coeff` (‖χ‖²=∑coeff) + `inner_self_chi_re_le_inner_self_X`
  (‖χ‖²≤‖X‖²).
- [x] **B3 (5.4.b)**: Pythagoras 補助 + `norm_eq_and_X_eq_sum_of_norm_Y_ge`
  (‖Y‖²≥‖ψ‖² ⟹ ‖X‖²=‖χ‖², ‖Y‖²=‖ψ‖², X=∑_{α∈E}α).
- [x] AxiomsCheck 登録 (3 件, all in allowlist) + `lake build OddOrder` 緑.

## 完了条件

`lake build OddOrder` / `lake build OddOrder.AxiomsCheck` 緑, sorry 無し. → **達成**.

## 参照

- `OddOrder/Peterfalvi/S07_Coherence.lean` (B1 struct + bridge + (5.4) setup/theorems)
- `OddOrder/GroupTheory/RepresentationTheory/ZIrrFourier.lean` (整数 CS + orthonormal Parseval + inner_conj_symm)
- mmd `references/peterfalvi/04.7_pp_25_29_Coherence.mmd` L11 (5.2.d), L31-53 (5.4)
- commits: 7aa5afc (CS+Parseval infra), 389482f (B1), a40e513 (inner_conj_symm),
  4dc95cf (B2/5.4.a), 6a189b8 (B3/5.4.b), 975bbed (AxiomsCheck)
- 残: (5.5)/(5.6)/(5.7) coherence 統合 (この (5.4) gateway を消費) は別 issue.
  `CharacterPsiDecomposition` の `imageFamily`/`tau1`/`coeff` 等は data 入力なので,
  実適用時に Dade 文脈から構成する必要あり (gateway は statement-level).
