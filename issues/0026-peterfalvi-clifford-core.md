---
id: 26
slug: peterfalvi-clifford-core
title: "Peterfalvi Part I: Clifford decomposition の proof core を証明する"
created: 2026-05-26
---

# Peterfalvi Part I: Clifford decomposition の proof core を証明する

## 背景

`issues/0023-peterfalvi-clifford-decomposition.md` から分割した proof core。
`clifford_decomposition` の statement は Peterfalvi §3 (1.5)/(1.7) と BG §2 で
共有できる形に確認済みだが、証明本体は character-level induction/restriction
API がまだ不足している。

必要な層:

- `ClassFunction.restrict` と irreducible character inner product による constituent
  multiplicity API。
- `InducedCharacter` の numerical Frobenius reciprocity。
- `Res_H^G χ` の irreducible constituents が単一 `G`-orbit になる Clifford core。
- inertia subgroup `I_G(θ)` からの induction bijection ([Is] Thm 6.11)。
- cyclic inertia quotient の multiplicity-one specialization (Peterfalvi §3 (1.7))。

## やること

- [x] restriction inner product で constituent/multiplicity predicate を定義する。
- [ ] `χ` irreducible なら restriction constituents are one `G`-orbit を statement 化する。
- [ ] common multiplicity `e` と orbit-sum decomposition を証明する。
- [ ] inertia induction bijectionの statement を切る。
- [ ] `clifford_decomposition` に proof core を戻して `sorry` を消す。

## 2026-05-26 update

- `ClassFunction.restrictionMultiplicity H χ θ` を追加した。
- `ClassFunction.IsRestrictionConstituent H χ θ` を追加した。
- `IrreducibleCharacter.LiesOver H χ θ` を追加し、raw class-function
  constituent predicate への bridge を証明した。
- `IrreducibleCharacter.RestrictionConstituentsSingleOrbit` と
  `IrreducibleCharacter.HasCommonRestrictionMultiplicity` を predicate として追加した。
- `ClassFunction.inertiaQuotient θ = I_G(θ)/H` と
  `IrreducibleCharacter.HasCyclicInertiaQuotient` を追加し、§3 (1.7) の
  cyclic inertia quotient hypothesis を名前にした。
- `liesOver_iff_restrictionConstituent`,
  `RestrictionConstituentsSingleOrbit.exists_conj`, and
  `HasCommonRestrictionMultiplicity.eq_of_liesOver` を追加し、Clifford core
  の predicate 結論を unfold せずに使えるようにした。
- `ClassFunction.conjByEquiv`, `conjBy_restrict`, `innerSum_conjBy_conjBy`,
  and `inner_conjBy_conjBy` を追加し、normal subgroup 上の ambient conjugation を
  finite sum / inner product の permutation として扱えるようにした。
- `restrictionMultiplicity` の add/sub/neg/smul API と
  `restrictionMultiplicity_conjBy_right` を追加し、restriction constituent の
  nonzero multiplicity が ambient conjugation で保たれることを直接使えるようにした。
- `IsRestrictionConstituent.conjBy` を追加し、conjugate 側の irreducibility が
  supply されれば restriction constituent を transport できるようにした。
- `ClassFunction.conjByMulEquiv` を追加し、ambient conjugation を `H ≃* H`
  として使えるようにした。
- `Representation.IsIrreducible.comp_mulEquiv` と
  `ClassFunction.IsIrreducibleCharacter.conjBy` を追加し、`conjBy` が
  irreducible character を保つことを証明した。
- `IsRestrictionConstituent.conjBy` から conjugate 側 irreducibility 引数を消し、
  restriction constituent の orbit transport をそのまま使える形にした。
- `ClassFunction.conjBy_inv_conjBy` / `conjBy_conjBy_inv` と
  `IrreducibleCharacter.conjBy` を追加し、`Irr(H)` 上で ambient conjugation を
  直接使えるようにした。
- `liesOver_conjBy` / `liesOver_conjBy_iff` を追加し、`LiesOver` が
  `G`-conjugation orbit に沿って不変であることを theorem 化した。
- `IrreducibleCharacter.inertia`, `subgroup_le_inertia`, `inertiaQuotient`, and
  `conjBy_eq_conjBy_iff_mul_inv_mem_inertia` を追加し、`Irr(H)` 上の orbit
  representative equality を `g*h⁻¹ ∈ I_G(θ)` で扱えるようにした。
- 次の小単位は、restriction constituents が単一 orbit になる Clifford core
  theorem の statement/proof 入力、または inertia induction bijection の API 化。

## 完了条件

- `OddOrder.RepresentationTheory.clifford_decomposition` から `sorry` が消える、または
  上記の constituent/orbit/inertia-bijection lemmas が独立 theorem として statement 化される。
- `lake build OddOrder.GroupTheory.RepresentationTheory.Clifford` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0023-peterfalvi-clifford-decomposition.md`
- related: `issues/0021-peterfalvi-second-orthogonality.md`
- `OddOrder/GroupTheory/RepresentationTheory/Clifford.lean`
- `OddOrder/GroupTheory/RepresentationTheory/Inertia.lean`
- `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`
- `OddOrder/GroupTheory/RepresentationTheory/SecondOrthogonality.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
- `OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`
