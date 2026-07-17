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

## 進捗 (2026-07-17 lane c)

- ✅ δ (`augmentation`) + Δ (`augmentationIdeal`, ℤ-Submodule) + simp 補題
- ✅ **Lemma 10.19 完成**: `augmentationIdeal_eq_span` (spanning) +
  `linearIndependent_of_sub_one` + `augmentationIdealBasis` (ℤ-basis) +
  `augmentationIdealBasis_apply`
- ✅ **Thm 10.20 完成** (`abelianizationEquivAugmentationQuotient :
  Abelianization G ≃* Multiplicative (AugmentationQuotient G)`)。
  実装どおり: 商 = `↥Δ ⧸ augmentationIdealSq` (comap Δ.subtype)、
  順方向 `toAugmentationQuotient`、逆方向 `augmentationRetraction`
  (`Basis.constr`)、`θ(Δ²)=0` は制限 mulLeft/mulRight + `Basis.ext` +
  `Submodule.mul_induction_on'`。simp 補題で e (of g) = (g−1)+Δ² を pin。
  root `OddOrder.lean` に wire 済 (leaf は consumer 0 で full build 外だった)。
- ⏭ 次: **10.21** (t-成分: `α ∈ Δ(K)Δ(G)` → `α_t ∈ Δ(K)`,
  `∑_t α_t ∈ Δ(K)²`) → **10.22** (`Δ(K)² = Δ(K)Δ(G) ∩ ℤ[K]`) →
  **10.23** (`Δ(K)bar ≅ K/K'`)。t-成分 `f_t : ℤ[G] →+ ℤ[K]` は
  Finsupp fiber 分解 or 右 transversal (`Subgroup.MemRightTransversals`?)
  で構成、`ℤ[K] ⊆ ℤ[G]` の埋め込みは `MonoidAlgebra.mapDomain`
  (`Finsupp.mapDomain` 単射) — 要 API 調査。
- Lean 注意 (10.19): `rw [MonoidAlgebra.smul_single']` は smul instance
  不一致で失敗 → exact defeq 経由; MonoidAlgebra ≠ Finsupp 型分離
  (Finsupp.* API 不可、`MonoidAlgebra.induction_linear` /
  `MonoidAlgebra.basis` を使う)。
- Lean 注意 (10.20): ① `Submodule.span_mul_span` は Algebra-section 宣言で
  `Algebra.toModule` 固定の rigid instance を持ち、Module-section の
  `Submodule.mul` instance と keyed matching 不成立 (rw/exact とも失敗) →
  span·span 展開を回避し `mul_induction_on'` (Module-section、instance が
  全部 binder) + 制限 mulLeft/mulRight + `Basis.ext` で任意元積を処理。
  ② `toAdd_zpow` の zsmul と商加群 smul (`Submodule.Quotient.instSMul'`) の
  不一致は `Int.cast_smul_eq_zsmul` でも埋まらず → `with_unfolding_all rfl`。

## 完了条件

- AugmentationIdeal.lean: δ/Δ def + 10.19 + 10.20 sorry-free (10.21-10.23 も同 leaf か
  分量次第で sibling)。
