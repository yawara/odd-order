---
id: 2040
slug: huppert-order-p-fixed-space-decomposition
title: "Pf App.B: Huppert noncyclic irreducible case via order-p fixed-space decomposition"
created: 2026-07-18
---

# Pf App.B: `pGroup_cyclic_fixedPointFree` non-cyclic irreducible case

## ✅ CLOSED (2026-07-18)

`OddOrder/Peterfalvi/Appendices/Huppert.lean` の唯一の `sorry` だった
`pGroup_cyclic_fixedPointFree` の irreducible non-cyclic case を証明した。

正規 elementary abelian 部分群 `R ⊴ P`, `|R| = p²` を取り、faithfulness と
irreducibility から `C_E(R)=1` を得る。`R` の位数 `p` 部分群 `T` に対する
固定部分群 `C_E(T)` は BG Proposition 1.16 により `E` を生成し、orbit-product
projection と `q ≠ p` による `p` 乗写像の単射性から独立族になる。

`P` は共役でこれらの fixed spaces を置換する。非零 summand を一つ取り、その
`P`-orbit が singleton なら対応する位数 `p` 部分群は `P` で正規、従って中心的に
なるが、faithful irreducible action では非自明な中心元の fixed space は `⊥` となり
矛盾する。よって二つ以上の非零 summand があり、
`fpf_of_constant_stabilizer_of_permuted_decomp` を適用できる。

この結果、`pGroup_cyclic_fixedPointFree` と
`fitting_cyclic_fixedPointFree` は sorry-free となり、Suzuki §2 Prop 2 の
`fitting_Dbar_cyclic_fpf_abelian` gate も axiom-clean になった。

当初予定した Schur lemma → `Z(P)` cyclic の経路は不要になった。

## 参照

- `OddOrder/Peterfalvi/Appendices/Huppert.lean`
- `OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic`
  (BG Proposition 1.16)
- `OddOrder.BG.Ch1.S04.exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic`
  (BG Lemma 4.5(a))
- `OddOrder/Peterfalvi/Appendices/Suzuki/KCyclic.lean`
