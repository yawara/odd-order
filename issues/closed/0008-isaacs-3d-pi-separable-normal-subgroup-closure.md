---
id: 8
slug: isaacs-3d-pi-separable-normal-subgroup-closure
title: "Isaacs §3D IsPiSeparable normal subgroup 閉包 + Hall-Higman 一般化"
created: 2026-05-25
---

# Isaacs §3D IsPiSeparable normal subgroup 閉包 + Hall-Higman 一般化

## 背景

[issues/0005](0005-isaacs-3d-pi-separable-redefine.md) で `IsPiSeparable π G` を
`piFittingSeries`-based class として正式定義. 続編として:

1. **quotient 閉包** `[IsPiSeparable π G] [N ⊴ G] ⇒ [IsPiSeparable π (G/N)]` — 完成
   (commit `25281b5`, instance `OddOrder.Isaacs.Ch03.quotient_isPiSeparable`).
2. **map/comap helpers** `oPiCore.map_le_of_surjective` / `oPiCore.comap_le_of_injective` —
   完成 (同上).
3. **normal subgroup 閉包** `[IsPiSeparable π G] {N ⊴ G} ⇒ [IsPiSeparable π ↥N]` — **本 issue**.
4. **disjunction lemma 一般化** `[Nontrivial G] [IsPiSeparable π G] ⇒ oPiCore π G ⊔ oPiCore π' G ≠ ⊥` — **本 issue**.
5. **Hall-Higman case bodies + main の `[IsPiSeparable π G]` 化** — **本 issue** (上記 3, 4 に依存).

## 障害点

`piFittingSeries`-based 定義での normal subgroup 閉包は `comap r̄ (S ⊔ T) ≤ comap r̄ S ⊔ comap r̄ T`
を必要とするが, **comap は sup と一般に非可換** (`Subgroup.comap` は Galois adjoint で
inf 保存・sup 非保存).

数学的には, 我々のケースでは `S = oPiCore π (G/Fₙ)`, `T = oPiCore π' (G/Fₙ)` が coprime
cardinality (π-group ⊓ π'-group = ⊥, 有限群で primeFactors 共通なし) なので, 内部直積分解
`S ⊔ T ≃ S × T` が成立. この場合 distributivity が回復する.

形式化に必要な追加 helper:
1. `Subgroup.inf_eq_bot_of_coprime` (mathlib `PGroup.lean:316` 既存) で `S ⊓ T = ⊥`.
2. Bezout 経由の π-part / π'-part extraction: `x ∈ S ⊔ T` 可換 coprime-order 元の積
   ⇒ 両因子 `∈ ⟨x⟩`.
3. 上記から `A ⊓ (S ⊔ T) = (A ⊓ S) ⊔ (A ⊓ T)` (for normal A).
4. injective hom 経由で normal subgroup 閉包の証明完成.

合計 ~50-100 LOC.

## やること

- [x] Helper: `oPiCore.coprime_inf` (`oPiCore π G ⊓ oPiCore π' G = ⊥` for finite G).
- [x] Helper: π-part / π'-part extraction (commuting coprime decomp).
- [x] Helper: distributivity / normal subgroup restriction route for `piFittingSeries`.
- [x] `piFittingSeries_subgroupOf_le_of_normal` の本体 proof.
- [x] `instance normalSubgroup_isPiSeparable`.
- [x] `theorem oPiCore_sup_ne_bot_of_isPiSeparable` (disjunction lemma 一般版).
- [x] `hall_higman_1_2_3` / `centralizer_oPiCore_eq_center`
      の hypothesis を `[IsSolvable G]` から `[IsPiSeparable π G]` に変更.
- [x] BG/S01 の `hall_higman_solvable_specialization` を新 signature に追従.
- [x] AxiomsCheck flagship 維持 (3 標準公理).

`piLength_le_one_of_abelian_pi_hall` は fake `True` placeholder の正式 statement 化を伴うため,
本 issue から外して [issues/0004](../0004-isaacs-3-22-pilength-placeholder.md) に移管する.

## 完了条件

- `instance normalSubgroup_isPiSeparable` が sorry-free.
- `hall_higman_1_2_3` が `[Finite G] [IsPiSeparable π G]` で動作.
- `lake build OddOrder.AxiomsCheck` 通過.

## Close notes

- `centralizer_oPiCore_eq_center` も `[Finite G] (π : Set ℕ) [IsPiSeparable π G]` に一般化済み.
- BG §1 の solvable specialization は `[IsSolvable G]` から `isPiSeparable_of_solvable`
  instance 経由で一般版 Hall-Higman を使う形に追従済み.

## 参照

- 親 issue: [`closed/0005`](0005-isaacs-3d-pi-separable-redefine.md) (`IsPiSeparable` 正式定義).
- 前回 commit: `25281b5` (helpers + quotient closure).
- [Ch03_SplitExtensions.lean §3D](../../OddOrder/Isaacs/Ch03_SplitExtensions.lean) (`piFittingSeries` 周辺).
- Isaacs FGT pp.89-95 §3D.
- mathlib `Subgroup.inf_eq_bot_of_coprime` (`PGroup.lean:316`).
