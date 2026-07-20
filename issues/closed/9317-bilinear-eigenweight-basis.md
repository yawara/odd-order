---
id: 9317
slug: bilinear-eigenweight-basis
title: "Bilinear eigenweight from eigenbases"
created: 2026-07-20
---

# Bilinear eigenweight from eigenbases

## 背景

Higman, *Suzuki 2-groups*, p. 90 の B/C/D case split 直前の step:

> if `x₀ξ = λx₀` and `y₀ξ = μy₀`, `[xᵢ, yⱼ]` can be nonzero only if
> `λ^(2ⁱ) μ^(2ʲ)` is an eigenvalue of `ξ` on `Φ(G)`.

これは群論から独立な線形代数である。等変な双線形写像と、二つの固有ベクトル族
(source 側は基底でなくてよい — 因子の像は ambient 層の真部分空間) および
target 側の固有基底があれば、非零な積の weight は target の spectrum に属する。

同型の coordinate 論法は Higman Lemma 11 でも使っており、`PairGap.lean:434` に
`private theorem eigenvalue_eq_of_basis_repr_ne_zero` として存在する。Lemma 12 で
二度目に必要になるので、shared leaf へ昇格して private 版を廃する
(issue 0127 ① が指摘した「3 コピー目」パターンの予防)。

## やること

- [x] `eigenvalue_eq_of_basis_repr_ne_zero` を shared leaf へ public 昇格する
- [x] 固有ベクトル族の span 内にある非零積から、基底対の非零積を選ぶ補題を証明する
- [x] 等変双線形写像の weight 方程式 `w₁ i * w₂ j = w₃ k` を結論する定理を証明する
- [x] `PairGap.lean` の private 版を削除し、shared 版へ repoint する
- [x] 新 leaf を `OddOrder.lean` に配線し、公開 endpoint を `AxiomsCheck.lean` に登録する

## 完了条件

- 新規 `sorry` / `axiom` / opaque carrier なし
- `OddOrder.GroupTheory.RepresentationTheory.BilinearEigenweight` と
  `OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven.PairGap` が build-green

## 2026-07-21 完了

shared leaf `BilinearEigenweight.lean` に 4 宣言を landing:
`eigenvalue_eq_of_basis_repr_ne_zero` (public 昇格) /
`eq_zero_of_forall_basis_repr_eq_zero` / `exists_pair_ne_zero_of_mem_span` /
`exists_weight_eq_of_bilinear_ne_zero` / `exists_pair_ne_zero_and_weight_eq`。
`PairGap.lean:434` の private 版を削除し shared 版へ repoint (PairGap green)。
`OddOrder.lean` 配線 + `AxiomsCheck.lean` に公開 2 endpoint 登録、full
AxiomsCheck green (14m31s, exit 0)。Lemma 12 の消費点は次コミットの
`MixedEigenweights.lean`。

## 参照

- issue 2048 (Higman Lemma 12 = 消費点) / issue 0127 ① (dedup 方針)
- `references/higman/pages/suzuki-2-groups-p090.png`
- `OddOrder/Higman/Suzuki2Groups/HigmanLemmaEleven/PairGap.lean`
