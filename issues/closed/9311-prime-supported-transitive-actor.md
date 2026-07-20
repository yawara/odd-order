---
id: 9311
slug: prime-supported-transitive-actor
title: "Extract a prime-supported cyclic actor from involution transitivity"
created: 2026-07-20
---

# Extract a prime-supported cyclic actor from involution transitivity

## 背景

Higman の Suzuki 2-group 定義 (p. 79) は、巡回 automorphism group が
involution を推移的に動かすことだけを仮定する。actor の位数が involution 数
`q - 1` と等しい regularity は Lemma 11 の結論側であり、先取りできない。

Lemma 11 冒頭では巡回生成元を取り、その `q - 1` の素因子に支えられた
π-part へ置き換える。π′-part の permutation image は、位数が `q - 1` を割る一方で
`q - 1` と互いに素なので自明であり、π-part は同じ full cycle を保つ。
この source-neutral reduction を Suzuki 2-group actor API に追加する。

## やること

- [x] involution set 上の automorphism permutation hom を構成する
- [x] cyclic-transitive actor の generator が full cycle になることを証明する
- [x] `PiElementDecomposition` で generator の π-part を抽出する
- [x] 抽出した cyclic subgroup が transitivity と prime support を保つことを証明する
- [x] actor order が奇数であることを系として供給する

## 完了条件

- `OddOrder.GroupTheory.SpecificGroups.Suzuki2Group.Basic` の対象ビルドが通る
- 新規 `sorry` / `axiom` / opaque carrier がない
- Higman Lemma 11 が regularity を仮定せず、抽出 actor を直接利用できる

## 完了記録

`involutionPermHom`, `exists_primeSupported_cyclic_actor`,
`involutions_ncard_odd_of_isPGroup`,
`exists_odd_primeSupported_cyclic_actor` を追加した。後者は有限 `2`-群と
cyclic-transitive actor から、involution 数を位数が割り、かつ同じ素因子だけを
持つ奇数位数の cyclic-transitive subgroup を構成する。regularity は仮定しない。

対象ビルド:

```text
Build completed successfully (1309 jobs).
```

## 参照

- `references/higman/suzuki-2-groups.pdftotext.txt` (pp. 79, 88--89)
- `OddOrder/GroupTheory/PiElementDecomposition.lean`
- `OddOrder/GroupTheory/SpecificGroups/Suzuki2Group/Basic.lean`
- issue 9310 (prime-supported Singer degree)
