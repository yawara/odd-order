---
id: 9108
slug: augmentation-ideal-group-ring
title: "shared: Algebra/AugmentationIdeal.lean — Z[G] augmentation ideal API (lane c claim, Isaacs 10.19-10.23)"
created: 2026-07-17
---

# shared: OddOrder/Algebra/AugmentationIdeal.lean (lane c claim)

Isaacs §10C (10.18–10.28, principal ideal theorem / Alperin-Kuo) の基盤。
mathlib 未収載を確認済 (2026-07-17: `Mathlib/Algebra/MonoidAlgebra/*` に
augmentation 無し; `RingTheory/Ideal/IsAugmentation.lean` は無関係な一般概念)。
将来 mathlib upstream 候補 HIGH (ch10 note §5.4)。

## 設計 (2026-07-17)

- 群環 = `MonoidAlgebra ℤ G`。
- **δ (augmentation)**: `MonoidAlgebra.lift ℤ G ℤ` を trivial `G →* ℤ` に適用した
  `→ₐ[ℤ]` (または直接 `Finsupp.sum` の RingHom)。
- **Δ(G)**: δ の kernel を **`Submodule ℤ (MonoidAlgebra ℤ G)`** として持つ
  (Isaacs の議論は加法群+積閉包なので Ideal でなく Submodule ℤ が正解;
  非可換群環でも `Submodule.mul` (`Algebra/Algebra/Operations`) が
  `Δ(K)·Δ(G)`, `Δ(G)²` を与える)。
- **10.19**: `{g - 1 | 1 ≠ g}` が Δ(G) の ℤ-basis —
  `Finsupp.basisSingleOne` からの座標変換で `Basis ℤ`。
- **10.20**: `G ⧸ G' ≃+ Δ(G)/Δ(G)²` — 順方向 φ(g) = (g-1) + Δ²、
  逆方向は basis の universal property (`Basis.constr`) で θ(g-1) = G'g。
- **10.21-10.23**: t-成分分解 (`Finsupp` の fiber 分解 or transversal 和)、
  `Δ(K)² = Δ(K)Δ(G) ∩ ℤ[K]`、`Δ(K)/Δ(K)Δ(G) ≅ K/K'`。
- 消費者: Ch10 §10C leaf (`PrincipalIdeal.lean` 予定; 10.18/10.24/10.25 +
  10.26 可換環補題 + 10.27/10.28 Alperin-Kuo)。

## 完了条件

- AugmentationIdeal.lean: δ/Δ def + 10.19 + 10.20 sorry-free (10.21-10.23 も同 leaf か
  分量次第で sibling)。
