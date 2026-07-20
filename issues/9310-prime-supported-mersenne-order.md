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

- [ ] 素因子支持から `N ∣ (a + 1) ^ (N / a) - 1` を得る純算術補題を実装する
- [ ] Mersenne divisibility と最小 Frobenius period から
      `n ∣ m ∧ Odd (m / n)` を得る補題を実装する
- [ ] `GaloisField 2 m` の生成元へ適用する有限体ラッパーを実装する
- [ ] Higman Lemma 11 側から直接使える署名を確認する

## 完了条件

- `OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates` の対象ビルドが通る
- 新規 `sorry` / `axiom` / opaque carrier がない
- 上記 3 補題が公開 API として利用できる

## 参照

- `OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanFiniteFieldTrace.lean`
- `references/higman/p88_92_lemmas_10_12.layout.txt` (Lemma 11)
