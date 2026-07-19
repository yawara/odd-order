---
id: 9302
slug: fixed-point-free-order-three-class-two
title: "Neumann: order-three fixed-point-free automorphisms force class at most two"
created: 2026-07-19
---

# Neumann: order-three fixed-point-free automorphisms force class at most two

## 背景

Higman, *Suzuki 2-groups*, Lemma 6 の parity step は、偶数次元の場合に
`H/H₄` 上の位数 3 fixed-point-free automorphism を作り、Neumann の定理
（有限群なら nilpotency class `≤ 2`）に反することで閉じる。これは
Peterfalvi Appendix III Lemma 5 の genuine prerequisite であり、既存の
`Mathlib.GroupTheory.FixedPointFree` には位数 2 の場合しかない。

文献境界を明示するため、source-specific な商群への適用は
`OddOrder/Higman/Suzuki2Groups/HigmanLemmaSix.lean` に残し、一般の
fixed-point-free order-three calculus をこの shared GroupTheory leaf に置く。

## やること

- [x] norm identity と commutator-map surjectivity から Burnside の
      right 2-Engel identity を証明する
- [x] Hopkins--Levi の交換子恒等式
      `⁅⁅x,y⁆,z⁆ ^ 3 = 1` を right 2-Engel 条件から証明する
- [x] fixed-point-free な位数 3 作用から `3 ∤ |G|` を証明する
- [x] 上記を合成し `(⊤ : Subgroup G).lowerCentralSeries 2 = ⊥` を得る
- [x] Higman Lemma 6 の `H/H₄` consumer へ接続する

## 完了条件

- 新 `axiom` / `sorry` / opaque carrier なし
- [x] `lake build OddOrder.GroupTheory.FixedPointFreeOrderThree` が通る
- [x] Higman consumer の targeted leaf build が通る
- [x] public endpoint を `OddOrder/AxiomsCheck.lean` の監査対象へ追加する

## 2026-07-19 checkpoint

`OddOrder/GroupTheory/FixedPointFreeOrderThree.lean` に一般の有限群版を
実装し、targeted build を確認した。さらに
`H² = H₂` から `H₂² ≤ H₃`, `H₃² ≤ H₄` を下中心列上で帰納的に証明し、
`L₁,L₂,L₃` の fixed-point-free 性を `H/H₄` へ直接降ろした。
`L₃ ≠ 0` からこの商の class が exactly three であることも接続済みである。
B レーンでは main が実施する full build / AxiomsCheck build は重ねて実行していない。

## 参照

- B. H. Neumann, *Groups with automorphisms that leave only the neutral
  element fixed*, Arch. Math. 7 (1956), 1--5.
- W. Burnside, *Theory of Groups of Finite Order*, 2nd ed. (1911), §160.
- M. P. Gallego, P. Hauck, M. D. Pérez-Ramos,
  *2-Engel Relations between Subgroups*, Proposition 3.3, Corollary 3.5.
- `issues/2048-pf-suzuki-lemma5.md`
- `OddOrder/Higman/Suzuki2Groups/HigmanLemmaSix.lean`
