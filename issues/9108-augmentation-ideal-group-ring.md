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
- ✅ **10.21 完成**: `augmentationIdealOf K` (Δ(K) ⊆ ℤ[G], span 定義) +
  `transversalComponent` (f_t, classical ite) / `transversalComponentSum`
  (f = ∑f_t) を `Basis.constr` + mathlib `Subgroup.IsComplement.equiv`
  (equiv_mul_left_of_mem / equiv_fst_eq_self / equiv_one) で構成。
  `transversalComponent_mem` (α_t ∈ Δ(K)) + `transversalComponentSum_mem_sq`
  (f(α) ∈ Δ(K)²)。生成元計算は Isaacs の 2 case が単一 ite 恒等式に統合。
- ✅ **10.22 完成**: `groupRingOf K` (ℤ[K] ⊆ ℤ[G]) +
  `augmentationIdealOf_sq_eq_inf_groupRingOf` / `_sq_eq_inf` (両形式)。
  f = id on ℤ[K] は ker(f − id) への span_le で無帰納。transversal は
  `Subgroup.exists_isComplement_right K 1`。
- ⏭ 次: **10.23** (`Δ(G)bar = Δ(G)/Δ(K)Δ(G)` 内で `Δ(K)bar ≅ K/K'`,
  写像 `k−1 bar ↦ K'k`)。設計: 商 = module quotient
  (`Δ(K)Δ(G) ≤ Δ(G)` comap Δ(G).subtype)、`Δ(K)bar` = Δ(K) の image。
  iso は 10.20-for-K を transport: `MonoidAlgebra.mapDomain` 橋
  (ℤ[↥K] ≃ₗ groupRingOf K, of k ↦ of ↑k) で `augmentationIdeal ↥K ≃
  augmentationIdealOf K`、10.22 で kernel 同定。その後 10.24/10.25
  (principal ideal thm) → 10.26-10.28 (Alperin-Kuo)。
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
- Lean 注意 (10.22): subtype-indexed span の membership 補題は
  `{x : G} (hx : x ∈ K)` 形式必須 — `(k : ↥K)` 形式を匿名 mk に適用すると
  1 use site ~950k heartbeats (memory lean-instance-defeq-traps §7)。

## 完了条件

- AugmentationIdeal.lean: δ/Δ def + 10.19 + 10.20 sorry-free (10.21-10.23 も同 leaf か
  分量次第で sibling)。
