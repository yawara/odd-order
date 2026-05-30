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
- [x] (2026-05-30) **(6.7.2) product rule mod |P|** を `ClassSumAlgebra.lean` に landing
      (commit 3735af4, AxiomsCheck 登録)。(6.7.1) keystone を product rule に流す:
      - `coeff_mul_card_eq_classSumCoeff` : per-element 因子数 `a_{ijs}=(classSum Ci*classSum Cj) Cs.out`
        × `|C_s|` = pair-count `classSumCoeff` (= Peterfalvi `a_{ijs}|C_s|`)。class-sum 係数と pair-count の橋。
      - `character_one_mul_coeff_mul_centralChar` : 各項 `ψ(1)·a_{ijs}·ω(C_s) = (a_{ijs}|C_s|)·χ(C_s.out)`。
      - `character_one_mul_coeff_mul_centralChar_cong_zero` : `m ∣ a_{ijs}|C_s|` ((6.7.1) 入力) ⟹ 当該項 `≡ 0 [ALGMOD m]`
        (代数的整数 `χ(C_s.out)` の `m` 倍)。
      - **`centralCharacterOfRep_classSum_mul_cong`** = (6.7.2) :
        `ψ(1)·ω(C_i)·ω(C_j) ≡ ∑_{C_s∩Z≠∅} ψ(1)·a_{ijs}·ω(C_s) [ALGMOD m]` (`C_s∩Z=∅` 項が mod m で脱落)。
        Peterfalvi の `ψ(1)α² ≡ ψ(1)(a_{ij0}+a_{ij}α)` の `ω(C_s)=α` collapse 前形。
- [x] (2026-05-30) **(6.7.2) geometric form** (abstract `hdvd` を (6.7) setup から放電) を
      `ClassSumAlgebra.lean` に landing (AxiomsCheck 登録, 3 axioms 全 allowlist 内)。
      - **`centralCharacterOfRep_classSum_mul_cong_of_isTISubset`** : `centralCharacterOfRep_classSum_mul_cong`
        (abstract `hdvd : ∀ Cs, ¬inZ Cs → m ∣ classSumCoeff`) を **実 (6.7) setup** へ特殊化 —
        Sylow `P`, `Z ≤ P` で `Z ⊴ L=N_G(P)`, `P^#=P∖{1}` TI-subset, source class `C_i,C_j` が `Z^#` と交わる。
        `m = |P| = Nat.card P`, `inZ Cs := ∃ w, ⟦w⟧=Cs ∧ w∈Z` (= `C_s∩Z≠∅`)。
      - `hdvd` 放電: `¬inZ C_s` (= `∀ w, ⟦w⟧=Cs → w∉Z`) で (6.7.1) `fixedPointFree_classPair_of_isTISubset`
        → fixed-point-free 仮説, それを (6.7.1) counting `card_dvd_classSumCoeff_of_fixedPointFree` に流し
        `|P| ∣ a_{ijs}|C_s|` (ℕ) → `exact_mod_cast` で ℤ 版。これで **(6.7.1)+(6.7.2) を 1 定理に合成**し,
        (6.7.3) `peterfalvi_673` の `h11`/`h12` 入力 (`ψ(1)α²≡ψ(1)(a_{ij0}+a_{ij}α)`) を生む geometric source
        が揃った (残 atoms = `a_{110}=0`/`a_{120}=|C₁|`/`ω(C_s)=α` const/`(|C₁|,p)=1` の構造定数計算のみ)。
- [x] (2026-05-30) **(6.7.3) 合同算術 assembly** を `ClassSumAlgebra.lean` + cancellation infra を
      `AlgInt.lean` に landing (commits 27ed939, 2be1cc3, AxiomsCheck 登録)。(6.7.3) を group-theory atoms
      (`a_{110}=0`, `a_{120}=|C₁|`, `z⁻¹∤z`, `ω(C_s)=α` const) を仮説とする **conditional** assembly に還元:
      - `AlgInt.Cong.intMul_cancel_left` : `c·a≡c·b (mod n)` + `IsCoprime c n` + a,b 代数的整数 ⟹ `a≡b`
        (Bézout `uc+vn=1` で `(a-b)/n=u(c(a-b)/n)+v(a-b)`)。= (6.7.3) の「`|C₁|` で割る」step。
      - `peterfalvi_673_combine` : 2 つの (6.7.2) instance (1,1)/(1,2) の trans。
      - `peterfalvi_673_cancel` : `ψ(1)α=|C₁|ψ(z)` 代入 + `|C₁|` cancel ⟹ `a_{11}ψ(z)≡ψ(1)+a_{12}ψ(z)`。
      - `peterfalvi_673_final` : `1_G` instance `a_{11}≡1+a_{12}` を `ψ(z)` 倍して subtract ⟹ `ψ(z)≡ψ(1)`。
      - **`peterfalvi_673`** = (6.7.3) : 上記 chain を atoms 仮説から組む。**残依存** = atoms の group-theory
        証明 (`a_{110}=0`/`a_{120}=|C₁|` の構造定数計算, `|L| odd ⟹ z⁻¹∤z`, `ω(C_s)=α` 不変性, `(|C₁|,p)=1`)。
        これらは (6.7) full setup (`IsTISubset`+Sylow+`|C_L(z)|` const) を要する `needs-infra` (別 issue)。
- [x] (2026-05-30) **(6.7.3) atom discharge (4 件中 3.5 件)** を `ClassSumAlgebra.lean` に landing
      (commits 5105064 / 4588590 / 399945c / ed4fae7, 全 AxiomsCheck 登録, unconditional)。
      `peterfalvi_673` の 8 仮説のうち group-theory atoms を放電する standalone 補題群を実装:
      - **構造定数 (i)**: `classSumCoeff_one_eq_zero` (= `a_{110}=0`; 抽象仮説 `∀u, mk u=Ci → mk u⁻¹≠Cj`
        で identity class 係数 = 0; filter 空) / `classSumCoeff_one_eq_card` (= `a_{120}=|C₁|`; `Cj` が
        inverse class なら係数 = `|Ci|`; bijection `u ↦ (u,u⁻¹)`)。`classSumCoeff` の filter 定義から直接。
      - **z-keyed bridge**: `mk_inv_eq_of_mk_eq` (`mk a=mk b ⟹ mk a⁻¹=mk b⁻¹`, unconditional, 2 行;
        `ConjClasses.isConj_inv` は import cycle `ClassSumAlgebra←ZIrr←IrrIndexing←BrauerPermutation`
        で import 不可ゆえ local 再証明) / `classSumCoeff_self_one_eq_zero` (= `a_{110}=0` for `C₁=⟦z⟧`,
        **唯一の仮説 = real-class atom `⟦z⁻¹⟧≠⟦z⟧`**) / `classSumCoeff_self_inv_one_eq_card`
        (= `a_{120}=|C₁|` for `C₂=⟦z⁻¹⟧`, **完全 unconditional**)。
      - **coprimality (iv)**: `card_class_eq_index_centralizer` (orbit-stabilizer: `|⟦z⟧|=[G:C_G(z)]`;
        `ConjAct G` 作用, orbit=carrier, stabilizer=centralizer) / `coprime_card_class_card_sylow`
        (= `(|C₁|,p)=1`; `P ≤ C_G(z)` (z∈Z(P)) ⟹ `[G:C_G(z)]∣[G:P]`, `p∤[G:P]`, `|P|=p^k`)。
      - **(iii) の一部**: `centralCharacterOfRep_one` (= `ω(C₀)=1`; identity class singleton)。
      - **残 atom (真の unconditional 化に残るもの)**:
        (ii-wrap) **real-class atom `⟦z⁻¹⟧≠⟦z⟧`** の **TI-reduction** (`|L| odd` + `P^#` TI + `z∈P` ⟹
          `¬IsConj_G z⁻¹ z`; Peterfalvi L122)。core `ConjClasses.eq_one_of_isConj_inv_of_odd_card` は
          repo 既存 (`BrauerPermutation.lean`) だが, それを呼ぶ TI-reduction wrapper は **`ClassSumAlgebra`
          に置けない** (上記 import cycle)。**downstream module (例: `ZIrr` か新規 file) に置く必要**。
        (iii-collapse) **`centralCharacterOfRep_classSum_mul_cong_of_isTISubset` の RHS sum →
          Peterfalvi `ψ(1)(a_{ij0}+a_{ij}α)` 形への collapse**。`{C_s∩Z≠∅}` を `{⟦1⟧}` (ω=1, 上記
          `centralCharacterOfRep_one`) と `{C_s∩Z^#≠∅}` (ω=α, **atom iii = `ω` 不変性, `ψ`+`|C_L(z)|`
          の Z^# 不変性に依存**) に分割し per-element count を regroup。これが最深部で `|C_L(z)|` const の
          (6.7) setup 仕込みを要する `needs-infra`。
      - **総括**: (i)/(iv)/`ω(C₀)=1` は完全放電。残るは (ii) の TI-reduction (cycle で配置先が `ClassSumAlgebra`
        外) と (iii)+sum-collapse (`|C_L(z)|` const 依存)。**fully unconditional `peterfalvi_673` 化は
        この 2 件が前提**で本 issue scope 内では未了 (PARTIAL)。

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
