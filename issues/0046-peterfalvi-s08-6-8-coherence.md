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
- [x] (2026-05-30) (6.7) 前段の **AlgInt.cong infra** を `OddOrder/Algebra/AlgInt.lean` に landing
      (commit dde7758, AxiomsCheck 登録)。`α ≡ β [ALGMOD n] := IsIntegral ℤ ((α-β)/n)` +
      refl/symm/trans/add/sub/neg/`smul_left`(任意代数的整数倍)/`intMul`/導入形。これが (6.7.3)
      `ψ(z)≡ψ(1) (mod |P|)` の合同算術部品。**(6.7.3) 本体の残依存**は (6.7.1) P の Ω 上 fixed-point-free
      作用 (TI-subset+Sylow-in-L, ~40-60 LOC 未着手) + (6.7.2) class-algebra product rule mod |P|。
      詳細は `notes/peterfalvi/s08_coherence_theorems.md` の 2026-05-30 進捗。
- [x] (2026-05-30) **(6.7.1) orbit-counting half** を `ClassSumAlgebra.lean` に landing
      (unconditional, AxiomsCheck 登録)。
      - `card_dvd_of_stabilizer_eq_bot` : 有限群 `Γ` が有限集合 `β` に**自由**作用 (全 stabilizer = ⊥)
        ⟹ `|Γ| ∣ |β|`。proof は free-action 分解 `β ≃ (β/Γ) × Γ`
        (`MulAction.selfEquivOrbitsQuotientProd`)。**これが planner の指摘した CRITICAL 欠落 primitive**
        ("MulAction.fixedPoints cardinality divisibility for sets" の正しい形 = 自由作用の `|Γ| ∣ |Ω|`)。
      - `card_dvd_of_no_nontrivial_fixed` : 同値な仮説形「`x ≠ 1` は任意の点を固定しない」⟹ `|Γ| ∣ |β|`。
      - `classPairMulAction` : 部分群 `P ≤ G` の `Ω = {(u,v)∈C_i×C_j | uv∈C_s}` (subtype `ClassPair`)
        上の共役作用 `x•(u,v)=(xux⁻¹,xvx⁻¹)`。`isClassPair_conj` で well-defined。
      - `card_classPair` : `|Ω| = classSumCoeff Ci Cj Cs` (= Peterfalvi の `a_{ijs}|C_s|`)。
      - **`card_dvd_classSumCoeff_of_fixedPointFree`** : fixed-point-free (no `x∈P^#` fixes a pair)
        ⟹ `|P| ∣ a_{ijs}|C_s|` = (6.7.1) の結論。
      - **残**: (6.7.1) の fixed-point-free *仮説の検証* (TI-subset ⟹ `C_G(x)⊆L`, p-元 ⟹ y∈P,
        conjugacy into Z^# + Z⊴L ⟹ y∈Z, `C_s∩Z=∅` 矛盾) = `IsTISubset`+Sylow-in-L の group-theory 組み立て
        (repo 未実装の Sylow/TI/Z setup を要する `needs-infra`)。これが揃えば (6.7.2)/(6.7.3) は本 module の
        `centralCharacterOfRep_classSum_mul` + `AlgInt.Cong.{smul_left,add,trans}` で assembly 可能。
- [x] (2026-05-30) **(6.7.1) fixed-point-free 仮説検証** を `ClassSumAlgebra.lean` に landing
      (commit 384e5b5, unconditional, AxiomsCheck 登録)。上記「残」を解消し (6.7.1) の group-theory
      部分が完全に閉じた。
      - `mem_sylow_of_mem_normalizer_of_isPGroup` : `N_G(P)` の p-元は Sylow p-部分群 `P` に属する
        (`IsPGroup.to_sup_of_normal_left'` で `P⊔⟨u⟩` が p-群 + `Sylow.is_maximal'` で collapse)。
      - `fixedPointFree_classPair_of_isTISubset` : (6.7) setup (P Sylow p in L=N_G(P), P^# TI-subset,
        Z ≤ P normal in L; C_i,C_j∩Z^#≠∅, C_s∩Z=∅) で P が Ω={(u,v)∈C_i×C_j|uv∈C_s} に fixed-point-free 作用。
        argument: x∈P^# 固定 ⟹ u,v∈C_G(x)⊆L (TI) ⟹ u,v p-元 ⟹ u,v∈P ⟹ (TI で conjugator∈L, Z⊴L) u,v∈Z
        ⟹ uv∈Z, C_s∩Z=∅ に矛盾。
      - `card_dvd_classSumCoeff_of_fixedPointFree` と合成で (6.7.1) 結論 `|P| ∣ a_{ijs}|C_s|` (C_s∩Z=∅) 完全形。
      - 残: (6.7.2)/(6.7.3) の class-algebra/合同算術 assembly (group-theory 依存は解消済; 別 issue)。

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
