---
id: 9310
slug: prime-supported-mersenne-order
title: "Control Frobenius degree from Mersenne prime support"
created: 2026-07-20
---

# Control Frobenius degree from Mersenne prime support

## 背景

Higman Lemma 11 では、`L = 𝔽₂(λ)` の生成元 `λ` の位数 `N` について、
`2 ^ n - 1 ∣ N` かつ `N` の素因子がすべて `2 ^ n - 1` を割ることから、
`[L : 𝔽₂] / n` が奇数であることを使う。この算術・有限体ステップは
Suzuki 2-group 固有ではなく、既存の Galois-field/Singer-model API と同じ
`FrobeniusCoordinates.lean` に置く共有補題として claim する。

この claim は lane b の shared-infra subband 9300 を使用する。実装前監査では
mathlib/repo 内に同値の公開定理は見つからず、`/tmp/HigmanPrimeSupport.lean`
で LTE に基づく証明を対象コンパイル済み。

## やること

- [x] 素因子支持から `N ∣ (a + 1) ^ (N / a) - 1` を得る純算術補題を実装する
- [x] Mersenne divisibility と最小 Frobenius period から
      `n ∣ m ∧ Odd (m / n)` を得る補題を実装する
- [x] `GaloisField 2 m` の生成元へ適用する有限体ラッパーを実装する
- [x] Higman Lemma 11 側から直接使える署名を確認する

## 完了条件

- `OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates` の対象ビルドが通る
- 新規 `sorry` / `axiom` / opaque carrier がない
- 上記 3 補題が公開 API として利用できる

## 検証 (2026-07-20)

- `lake build OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates`
  - `✔ [2027/2027] Built OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates (2.6s)`
  - `Build completed successfully (2027 jobs).`
- ソース更新時刻 `11:23:10 +0900` に対し `.olean` 更新時刻は
  `11:24:17 +0900` で、今回のソースを実際に再 elaboration したことを確認した。
- 公開 API:
  - `dvd_add_one_pow_div_sub_one_of_primeFactors_dvd`
  - `mersenne_exponent_dvd_and_odd_quotient_of_primeFactors_dvd`
  - `galoisField_degree_dvd_and_odd_quotient_of_primeFactors_dvd`
- レーン規約に従いフルビルドは実行していない。

## 参照

- `OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanFiniteFieldTrace.lean`
- `references/higman/p88_92_lemmas_10_12.layout.txt` (Lemma 11)
