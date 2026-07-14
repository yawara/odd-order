---
id: 1031
slug: s11-caseb-galois-field-model
title: "Peterfalvi (9.7.b): construct the chief-factor Galois-field model"
created: 2026-07-14
---

# Peterfalvi (9.7.b): construct the chief-factor Galois-field model

## 背景

`CliffordCaseBData.actsIrreducibly` は chief factor `H̄ = H/H₀` 上の実際の `U`-作用が
既約であることを保持し、`uActionHom_range_comm` は忠実 image `Ū` が可換であることを証明済み。
共有 issue 9100 で faithful irreducible module を `GF(p^q)` 上の乗法作用として実現する入口も
完成した。残る §11 producer は、これらを接続して Peterfalvi (9.7.b) の具体的 field model を
構成すること。

## やること

- [x] `Ū = range(uActionHom)` の chief-factor作用を simple module として組み立てる。
- [x] `Additive (H/H₀) ≃+ GF(p^q)`、injective `Ū → GF(p^q)^×`、作用互換性を構成する。
- [x] `cSub = ⊥` の場合に元の `U`-作用へ輸送できる入口を整備する。
- [x] target build / AxiomsCheck / full build を通す。

## 完了条件

`CliffordCaseBData.field_model : Prop` を cite せず、`actsIrreducibly` と既存の非 opaque な
group-action data だけから field carrier と scalar embedding が構成されること。新しい axiom、
free field、opaque structure field を追加しない。

## 参照

- `OddOrder/Peterfalvi/S11_MaximalII_III_IV/CliffordData.lean`
- `OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean`
- `OddOrder/GroupTheory/RepresentationTheory/SingerField.lean`
- Peterfalvi (9.7.b), (14.6); `coq/theories/PFsection9.v`, `PFsection14.v`

## 完了報告 (2026-07-14)

- `caseB_exists_galoisField_repr` が `CliffordCaseBData.actsIrreducibly` から忠実像
  `range(uActionHom)` の simple/faithful module を組み立て、共有 Singer 構成を適用する。
- `uActionHom_injective_of_cSub_eq_bot` が二重の subgroup map をほどいて作用の忠実性を証明する。
- `caseB_exists_galoisField_repr_of_cSub_eq_bot` が field model と scalar embedding を元の `U` へ輸送する。
- `lake build OddOrder.Peterfalvi.S11_GaloisFieldModel`、`lake build OddOrder.AxiomsCheck`、
  `lake build OddOrder` はすべて成功。3 定理を `AxiomsCheck.lean` に登録済み。
