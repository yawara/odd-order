---
id: 46
slug: peterfalvi-s08-6-8-coherence
title: "Peterfalvi (6.8): SibleySetup → CoherenceTarget + IndChainDecomposition"
created: 2026-05-28
---

# Peterfalvi (6.8): SibleySetup → CoherenceTarget + IndChainDecomposition

## 背景

`issues/0044-peterfalvi-s09-card-g0-lower-bound.md` の sub-issue。
(7.10) 証明で最初に呼ばれるのが (6.8) Theorem (Sibley coherence):

> *Let G be a finite group, L ≤ G. Assume (a)-(c). Then S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H} is coherent.*

(7.10) 内では:
> By Theorem (6.8), there are orthonormal subsets `X_i = {χ_{it} | 1 ≤ t ≤ w_i}` of `Z[Irr G]`
> such that `Ind_{L_i}^G(ζ_{it} - d_{it}ζ_{i1}) = χ_{it} - d_{it}χ_{i1}` for `2 ≤ t ≤ w_i`.

S08 には既に `SibleySetup` structure と `CoherenceTarget` abbrev は揃っている
(`S08_CoherenceTheorems.lean:133` 以降)。**残るは (6.8) 本体定理**
`SibleySetup → CoherenceTarget` の statement と, (7.10) 用 consumer interface
`IndChainDecomposition` の packaging。

## やること

- [x] (6.8) 本体定理 `sibleySetup_is_coherent : (hyp : SibleySetup S A) → hyp.CoherenceTarget`
      を statement 化 (proof は sorry)。`noncomputable def` で書いた (CoherenceTarget = IsCoherent
      は extension map を data field として持つので Type, not Prop)。
- [x] `IndChainDecomposition` structure を追加: `χ : Fin n → ClassFunction G ℂ`,
      `norm_one`, `pairwise_inner_zero`, `d_zero`, `image_eq` の 5 フィールド。
- [x] `IndChainDecomposition.ofIsCoherent` constructor: `χ t := hτ.extension (ζ t)`,
      各フィールドを `extension_inner_eq` (isometry) と `extends_on_supported`
      + `LinearMap.map_sub` + `map_zsmul` で組み立て。sorry-free。
- [x] `IndChainDecomposition.image_eq_zero` simp lemma (`t = 0` 時の vacuous case)。
- [x] build pass: `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` 緑、`lake build OddOrder` 緑。
- 残: `sibleySetup_is_coherent` の **本体 proof** ((6.1)-(6.7), (5.2), (4.6) 等の積み上げ; 別 issue で長期的に)。
  これ自体は (7.10) を書く時点では sorry のまま invoke して進められる。

## 完了条件

- `sibleySetup_is_coherent` statement が定義される (proof は sorry で OK)。
- `IndChainDecomposition` structure + constructor + 主要 helper が `IsCoherent` 経由で組まれる。
- (7.10) `card_G0_lower_bound` 証明から `IndChainDecomposition.of_isCoherent` を経由して
  必要なデータが取れることが概念的に明確 (proof は別 issue)。
- lake build 通る。

## 参照

- parent: `issues/0044-peterfalvi-s09-card-g0-lower-bound.md`
- file: `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean` (SibleySetup, CoherenceTarget)
- file: `OddOrder/Peterfalvi/S07_Coherence.lean` (IsCoherent, IntegralCharacterMap)
- mmd: `references/peterfalvi/04.8_pp_30_37_Some_Coherence_Theorems.mmd` L136 以降
- mmd: `references/peterfalvi/04.9_pp_38_43_*.mmd` L133-135 (consumer 使用箇所)
