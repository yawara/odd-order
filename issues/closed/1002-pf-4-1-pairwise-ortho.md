---
id: 1002
slug: pf-4-1-pairwise-ortho
title: "Peterfalvi (4.1): pairwise orthogonality of signed irreducibles (himg_ortho ingredient)"
created: 2026-06-07
---

# Peterfalvi (4.1): pairwise orthogonality of signed irreducibles (himg_ortho ingredient)

## 背景

(6.8) capstone の唯一の gating obligation `himg_ortho` (`X^{τ₂} ⊥ Y^{τ₁}`) は、教科書 (mmd
04.8 L166) では **(4.1)** (mmd 04.6 L5) から導かれる。(4.1) は「符号付き既約 (±Irr) で、符号付き
差が直交し次数 0 なら、4 つは pairwise 直交」という基礎補題。汎用形は未形式化だった
(既存は u=v=1・共役対専用の `orthogonal_of_signedDifference_inner_eq_zero` のみ)。

## やること

- [x] 汎用 (4.1) を `OddOrder.RepresentationTheory` namespace に形式化 (S08_CoherenceTheorems.lean)
- [x] sub-lemma: `apply_one_ne_zero_of_mem_ZIrr_of_inner_self_one` (±Irr の次数 ≠ 0)
- [x] sub-lemma: `eq_inner_smul_of_inner_ne_zero` (±Irr 内積≠0 ⟹ ψ=⟨φ,ψ⟩•φ)
- [x] core: `inner_eq_zero_of_orthogonal_signedDifference` ((α,γ)=0)
- [x] full: `pairwise_inner_eq_zero_of_orthogonal_signedDifference` (4 cross products=0)
- [x] AxiomsCheck 登録 (4 件) + build-green (`lake build OddOrder.AxiomsCheck` 3557 jobs OK)

## 完了条件

(4.1) が build-green + axiom-clean (`[propext, Classical.choice, Quot.sound]` のみ) で landed。
**達成** (2026-06-07)。

## 参照

- `notes/peterfalvi/s08_6_8_blocker_central_Z.md` 「2026-06-07 (session 3)」節 — (4.1) landing +
  2 つの framing 訂正 (himg_ortho = (4.1) step; hgen は X∪Y で false の疑い = 真の deep piece)。
- mmd: `references/peterfalvi/04.6_*.mmd` L5 (4.1), `04.8_*.mmd` L166 (himg_ortho の (4.1) 適用)。
- 後続: difference-orthogonality leaf → himg_ortho wiring → hgen 解決 (b≡0 / (6.7))。
