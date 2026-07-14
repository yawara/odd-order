---
id: 9100
slug: faithful-irreducible-galois-field-repr
title: "SHARED: realize faithful irreducible actions over a Galois field"
created: 2026-07-14
---

# SHARED: realize faithful irreducible actions over a Galois field

## 背景

Peterfalvi (9.7.b) は、既に faithful・irreducible と分かった可換群の `F_p`-線形作用を
`GF(p^q)^×` の乗法作用として実現する。既存 `exists_galoisField_repr` は irreducibility
を full cyclotomic order から導く (14.2.a) 専用入口であり、(14.6) の S-side case B、特に
`p ≡ 1 (mod q)` の divided-order branch には使えない。

**CLAIM (lane a, 2026-07-14)**: `SingerField` に、simple module と faithfulness を直接入力して
Galois-field 表現を返す汎用入口を公開する。他レーンは同じ maximal-ideal / finite-field
transport を再構築しない。

## やること

- [x] faithful irreducible action から `M ≃+ GF(p^q)` と injective `C → GF(p^q)^×` を構成する。
- [x] 既存 full-order theorem を新しい汎用入口経由へ再配線する。
- [x] target build / AxiomsCheck / full build を通す。

## 完了条件

full cyclotomic order を仮定せず、実際の `IsSimpleModule` と faithfulness だけから field model が
構成されること。新しい opaque data・構造体 field・axiom を追加しない。

## 参照

- `OddOrder/GroupTheory/RepresentationTheory/SingerField.lean`
- `OddOrder/Peterfalvi/S11_MaximalII_III_IV/ChiefFactorCore.lean`, `CliffordCaseBData`
- `OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean`, `s_side_field_repr`
- `references/peterfalvi/04.16_pp_87_92_Non-existence_of_G.mmd`, (14.6)

## 完了報告 (2026-07-14)

- `exists_galoisField_repr_of_faithful_irreducible` を追加し、simple module と pointwise
  faithfulness から additive equivalence、injective scalar hom、作用の intertwining を構成した。
- 既存 `exists_galoisField_repr` は full cyclotomic order から irreducibility を証明した後、
  新しい汎用入口を使うよう再配線した。
- `AxiomsCheck` に新定理を登録し、許可された標準公理だけへの依存を確認した。
- `lake build OddOrder.GroupTheory.RepresentationTheory.SingerField` (1990 jobs)、
  `lake build OddOrder.AxiomsCheck` (4199 jobs)、`lake build OddOrder` (4214 jobs) 成功。
