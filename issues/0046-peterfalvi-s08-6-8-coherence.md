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
- [x] (2026-06-02) `IndChainDecomposition.inner_chi_eq_ite`: output family `χ` の
      orthonormality を `if t = u then 1 else 0` 形にまとめる consumer lemma。sorry-free、
      `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` 緑。
- [x] (2026-06-04) `IndChainDecomposition` consumer helper 5 件を AxiomsCheck 登録。
      `ofIsCoherent` と weighted-output Parseval まで allowlist 内で、(7.10) packaging が
      (6.8) 本体 sorry と独立に axiom-clean であることを CI で固定。
- [x] (2026-06-04) `IndChainDecomposition.weightedDifferenceInput` と
      `image_weightedDifferenceInput` を追加。Peterfalvi (7.10) の整数係数付き source difference
      `∑ d_t(ζ_t - d_tζ_0)` に既存 `image_eq` を線形合成する consumer lemma。AxiomsCheck 登録済み。
- [x] (2026-06-04) T6/Y-family 側の landed bricks (`coherentYFamily`, c2/case-A inertia,
      degree-one induced degree/support, Xset irreducibility) を AxiomsCheck 登録。いずれも 3 axiom
      allowlist 内で、(6.8) 本体 sorry と独立に axiom-clean。
- [x] (2026-06-04) `SibleyDadeHypothesis.coherentYFamily_of_pairwiseNonconj` を追加。
      Y-family caller から `hirr` family 仮定を消し、nontrivial linear characters +
      pairwise non-`L`-conjugacy から T6/c1-c2 の
      `isIrreducibleCharacter_induce_of_degree_one` を内部適用して `coherentYFamily` へ渡す。
      AxiomsCheck 登録済み。
- [x] (2026-06-04) `induce_linearIrreducibleCharacter_mem_Yset` と
      `range_induce_linearIrreducibleCharacter_subset_Yset` を追加。nontrivial linear source family
      から作った induced range が `Yset = S(H')` に入ることを、commutator kernel containment
      で証明。AxiomsCheck 登録済み。
- [x] (2026-06-04) `exists_linear_source_of_mem_Yset` /
      `mem_Yset_iff_exists_linear_source` を追加。`Yset` member の source `θ` を
      `Abelianization.of : H → H/H'` で factor し、有限可換群上の irreducible character が
      degree-one/linear であることから nontrivial linear source representation を得る。
- [x] (2026-06-04) `range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective` /
      `coherentYset_of_pairwiseNonconj` を追加。`Fin n` family が nontrivial linear characters
      の induced `Yset` members を全て覆うという caller-supplied cover から constructed
      induced range を `Yset` そのものへ rewrite できるようにした。
- [x] (2026-06-04) `finite_linearCharacters_of_finite` / `Yset_finite` /
      `isIrreducibleCharacter_of_mem_Yset` / `exists_Yset_linearRepresentativeFamily` /
      `coherentYset_of_two_le_ncard` を追加。全 nontrivial linear characters を直接 quotient
      せず、有限な `Yset` を enumerate して各 member の linear source を選ぶ設計で、exact range
      と pairwise non-`L`-conjugacy を誘導既約文字の injective enumeration から構成。T6/Y-family は
      `2 ≤ hyp.Yset.ncard` まで圧縮済み。
- [x] (2026-06-04) `induce_conj` / `Yset_nonempty` / `Yset_hasNoRealCharacters` /
      `Yset_closedUnderConjugate` / `two_le_Yset_ncard` / `coherentYset` を追加。S07 の
      `two_le_ncard_of_conjugate_closed_of_noReal` に finite/nonempty/closed/no-real を渡し、
      T6/Y-family coherence の cardinality 仮定を discharge。
- [x] (2026-06-04) `SsubFiltration_subset_S` / `Xset_union_Yset_eq_S` /
      `disjoint_Xset_Yset` / `coherentS_of_Xset_commutator_Yset_glued` を追加。`X=S-S(H')` と
      `Y=S(H')` の set partition を Lean 化し、`coherentYset` を `coherentUnion_of_glued` 経由で
      `hyp.CoherenceTarget` に差し込む adapter まで接続。
- [x] (2026-06-04) Frobenius case の `Z=H'` 特殊化
      `Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius` /
      `Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`
      を追加。`H'≤H`, `H'⊴L`, `X⊆Irr L` を内部化し、c1 側の `hX` は
      `Xset H'` nonempty + per-step common-index p-power data だけで作れる形に圧縮。
- [x] (2026-06-04) `SsubFiltration_antitone` / `Xset_mono` /
      `Xset_commutator_eq_Xset_union_filtrationDiff` を追加。c2/case-A は `H'` へ直接
      `X⊆Irr` を出す既存 primitive がなく、`Z≤H'` から
      `X(H') = X(Z) ∪ (S(Z) \\ S(H'))` の差分層を扱う必要があることを Lean 側で固定。
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
      - **総括**: (i)/(iv)/`ω(C₀)=1` は完全放電。(ii) の TI-reduction も別 leaf module で放電完了
        (下記 2026-05-30 追記)。残るは (iii)+sum-collapse (`|C_L(z)|` const 依存) **のみ**。
        **fully unconditional `peterfalvi_673` 化はこの 1 件が前提**で本 issue scope 内では未了 (PARTIAL)。
- [x] (2026-05-30) **(6.7.3) 残 atom (ii-wrap) real-class TI-reduction 完了** を新規 leaf module
      `OddOrder/GroupTheory/RepresentationTheory/RealClassTISubset.lean` に landing (unconditional,
      AxiomsCheck 登録, sorry-free, `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑)。
      - 配置判断: `BrauerPermutation` (= `eq_one_of_isConj_inv_of_odd_card` の在処) と `ClassSumAlgebra`
        の**両方の downstream**。`ZIrr` は `BrauerPermutation` の *upstream*
        (`ZIrr←IrrIndexing←BrauerPermutation`) ゆえ不可と判明 ⟹ `BrauerPermutation` を import する新規
        file (これで `ClassSumAlgebra`/`TISubset`/`Sylow` も transitive に入る)。
      - `not_isConj_inv_of_isTISubset` (`P∈Syl_p`, `Odd |N_G(P)|`, `P^#=P∖{1}` が `N_G(P)` 相対 TI-subset,
        `z∈P`, `z≠1` ⟹ `¬IsConj z⁻¹ z`): conjugator `c` (`c z⁻¹ c⁻¹=z`) が `z⁻¹∈P^#`→`z∈P^#` ⟹ TI で
        `c∈L=N_G(P)` ⟹ `↥L` 内で `IsConj (⟨z,_⟩⁻¹) ⟨z,_⟩` ⟹ `|L|` odd で
        `eq_one_of_isConj_inv_of_odd_card` が `z=1` 強制し矛盾。= Peterfalvi L122。
      - `mk_inv_ne_self_of_isTISubset` (`⟦z⁻¹⟧≠⟦z⟧`, `mk_eq_mk_iff_isConj`): `classSumCoeff_self_one_eq_zero`
        の唯一仮説に直接プラグイン ⟹ **(ii) 残を解消**。
      - mathlib rc2 quirk: `Subgroup.normalizer : Set G→Subgroup G` (Set 引数) のため型位置
        (`Nat.card`/`Finite`/subtype 注釈) で `Subgroup→Set` 引数 coercion が非挿入 ⟹
        `set L := Subgroup.normalizer ((P:Subgroup G):Set G)` で `hodd`/`hti` を畳み一貫化し回避。
      - **残**: fully unconditional `peterfalvi_673` は (iii-collapse) `|C_L(z)|` const 依存のみ。
- [x] (2026-05-30) **(6.7.3) atom (i) `a_{110}=0` を (6.7) setup から hypothesis-free 化** を
      `RealClassTISubset.lean` に landing (unconditional, AxiomsCheck 登録, sorry-free,
      `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑, 3 axioms 全 allowlist 内)。
      - `classSumCoeff_self_one_eq_zero_of_isTISubset` : `[Fintype G]`, `[DecidableEq (ConjClasses G)]`,
        `P∈Syl_p`, `Odd |N_G(P)|`, `P^#=P∖{1}` が `N_G(P)` 相対 TI-subset, `z∈P`, `z≠1` ⟹
        `classSumCoeff ⟦z⟧ ⟦z⟧ 1 = 0`。`mk_inv_ne_self_of_isTISubset` (real-class atom) を
        `classSumCoeff_self_one_eq_zero` (唯一仮説 `⟦z⁻¹⟧≠⟦z⟧`) にプラグインし, **(6.7.3) の `a_{110}=0`
        入力を group-theory 仮説ゼロ**で (6.7) data から導く。placement は atom と同理由で本 leaf
        (`BrauerPermutation` downstream; `ClassSumAlgebra` への `BrauerPermutation` import は cycle
        `ClassSumAlgebra←ZIrr←IrrIndexing←BrauerPermutation` を閉じる)。
      - **残 (fully unconditional `peterfalvi_673` の唯一の前提)**: (iii-collapse) のみ。
        `centralCharacterOfRep_classSum_mul_cong_of_isTISubset` は (6.7.2) を **SUM 形**
        (`ψ(1)ω(C_i)ω(C_j) ≡ ∑_{C_s∩Z≠∅} ψ(1)a_{ijs}ω(C_s)`) で無条件に出すが, `peterfalvi_673` の
        `h11`/`h12` 入力は **collapse 形** (`ψ(1)α² ≡ ψ(1)(a_{ij0}+a_{ij}α)`)。橋には `ω(C_s)=α`
        (`C_s∩Z^#≠∅` 上不変) が要り = `|C_L(z)|` const = `[G:C_G(z)]·ψ(z)` が `z∈Z^#` 上不変 = (6.7)
        hypothesis の deep character-theory 仕込み (`needs-infra`)。memory `scaffold-sorry-free-not-done`
        に照らし**仮説外出ししない** (外出しは vacuous/too-strong になる)。真完了には `|C_L(z)|`-constancy
        部品の実装が要る (別 issue 化候補)。
- [x] (2026-05-30) **§7 (5.6)(b) degree-ratio integrality** = (5.6) 証明開始 "Set χ(1)=aχ₁(1)" の
      `a∈ℕ` 導出を `OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean` に landing (commit 別; sorry-free,
      AxiomsCheck 登録, `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑, 3 axioms 全 allowlist)。
      - `exists_pos_natDegreeRatio_of_dvd` : `[Finite G]`, `χ χ₁ : IrreducibleCharacter G`,
        仮説 `∀ d d₁:ℕ, χ 1=(d:ℂ) → χ₁ 1=(d₁:ℂ) → d₁ ∣ d` (= (5.6)(b) on nat degrees) ⟹
        `∃ a:ℕ, 0<a ∧ characterDegree χ = a · characterDegree χ₁`。`a` は (5.6) の `a` (および族の `a_i`)。
      - **honest-statement 訂正**: 本ラウンド roadmap の first leaf 候補 A3 ("χ(1)=a·χ₁(1) for `a∈ℚ` ⟹ `a∈ℤ`")
        は **数学的に偽** (degree 2,3 → 2/3)。divisibility (5.6)(b) が本質 datum (mmd 04.7 L60-67 が
        "this is compatible … if aᵢ∈**N**" と明記) なので divisibility を明示仮説に取る形が honest。
        roadmap の無条件 ℚ→ℤ は採用せず (scaffolding/偽 statement 回避)。詳細 `notes/peterfalvi/s07_coherence.md`
        「형식화 진행 (Track A)」。残: (5.6.1) Y 분해 / (5.6.2) `0<b<1⇒λ=0` quadratic forcing /
        (5.4.a/b) Cauchy–Schwarz — いずれも R(χ) 一般 orthonormal lattice (B1) 선행 필요。
- [x] (2026-05-31) **(6.6) G2.2 residual: 真正 character の ℕ-分解** を
      `OddOrder/GroupTheory/RepresentationTheory/Clifford.lean` (+ `IsCharacter` 述語を `ZIrr.lean`) に
      landing (sorry/axiom 無 — `#print axioms` = {propext, Classical.choice, Quot.sound}; AxiomsCheck
      登録 4 件 各 3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360/3343 jobs)。
      G2.2 equality-case consumer が end-to-end で食う「真正 character は ⟨χ,ψ⟩∈ℕ で分解」を honest 一般形で:
      - **`IsCharacter`** (`ZIrr.lean`, `IsIrreducibleCharacter` の隣): `φ` が**有限次元 ℂ-表現 `ρ` の
        character** (irreducibility 落とした版)。`IsIrreducibleCharacter.isCharacter` /
        `repCharacterClassFunction_isCharacter` で導入。
      - **`IsCharacter.mem_ZIrr`**: 真正 character ∈ ZIrr (`character_mem_ZIrr` を canonical class-function
        同定後に適用)。
      - **`IsCharacter.exists_natCast_inner_irreducible`** (非負性の核): 真正 `χ=χ_ρ`, irreducible `ψ=χ_σ`
        で `⟨χ,ψ⟩ = dim_ℂ Hom_{ℂ[G]}(σ,ρ)` = cast ℕ。`restrictionMultiplicity_nonneg` の **G-level 版** —
        `inner` を `χ_σ(g⁻¹)=star(χ_σ g)` (`character_inv`) で書き換え mathlib の
        `Representation.card_inv_mul_sum_char_mul_char_eq_finrank` (Hom-dim 特성화) に流す。
        `inner_irreducible_nonneg` は `0 ≤ ⟨χ,ψ⟩` の系。
      - **`IsCharacter.exists_natFinsupp_eq_sum`** (= GOAL, G2.2): `∃ m : ClassFunction G ℂ →₀ ℕ`,
        `supp m ⊆ Irr(G)`, `χ = ∑_{ψ∈supp m} (m ψ:ℂ)•ψ`, `∀ψ∈Irr, (m ψ:ℂ)=⟨χ,ψ⟩`。`mem_ZIrr_repr`
        (ℤ-Finsupp 분해) + `inner_eq_coeff_of_repr` (係수=Fourier coeff) + 비음성 ⟹ 각 係수 ≥0 を
        `Int.toNat` 로 ℕ 化 (support 불변: support 위 係수는 양수). Peterfalvi 의 "χ=∑mᵢψᵢ, mᵢ=⟨χ,ψᵢ⟩∈ℕ".
      - **honest 판정**: thin wrapper 아님 — `IsCharacter` 는 진짜 새 述語 (genuine vs virtual character),
        비음성은 `restrictionMultiplicity_nonneg` 가 H-level 만 주는 것을 G-level Hom-dim 으로 새로 끌어옴.
        ℕ-Finsupp 分解은 ℤ-repr + 비음성의 비자명한 합성 (`Int.toNat` support-preservation 포함).
      - **배치**: `Clifford.lean` (= `restrictionMultiplicity_natCast` 의 家; `character_mem_ZIrr` +
        Fourier (`mem_ZIrr_repr`/`inner_eq_coeff_of_repr`) + `character_inv` 가 모두 import closure 내
        유일 모듈). `IsCharacter` 述語만 `ZIrr.lean` (其 `.mem_ZIrr` 는 downstream `character_mem_ZIrr`
        필요해 Clifford 에).
- [x] (2026-05-31, G2.6 PASS 2) **(6.6) named conclusion `peterfalvi_66_coherence_of_X` + enum-cover
      bridge** 를 `S07_Coherence.lean` (`coherentOfPairChainCover` 직후) 에 landing (sorry/axiom 無 —
      `#print axioms peterfalvi_66_coherence_of_X` = {propext, Classical.choice, Quot.sound};
      AxiomsCheck 등록 2건 각 3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck`
      緑 3360/3343 jobs). PASS 1 의 `coherentOfPairChainCover` (set-level cover `hcover` 를 opaque
      가설로 받음) 를 (6.6) 의 실제 증명구조 — degree-monotone enumeration `exists_monotoneDegreeEnum`
      (mmd L76 "Set X = {χ₁,…,χₙ}, χ₁(1) ≤ ⋯ ≤ χₙ(1)") 를 engine accumulator 에 threading — 으로
      끌어올림:
  - **`pairUnion_eq_of_enumCover`** (genuinely new bridge, NOT thin wrapper): enum `e : Fin n →
    ClassFunction L ℂ` 의 *surjectivity* `hsurj : ∀ χ∈X, ∃ i, e i=χ` + **index-level** cover
    `hcoverIdx : ∀ i, e i ∈ S₀ ∨ ∃ j<N, e i ∈ pairSet pair j` ⟹ `pairUnion S₀ pair N = X`.
    set-level cover (`pairUnion_eq_of_cover` 가 요구) 를 χ=e i 치환으로 index-level 에서 도출 —
    `exists_monotoneDegreeEnum` 가 `Fin n` 으로 주는 사실들과 engine 의 set-level cover 사이의
    connective tissue (PASS 1 note 의 residual "threading the enum sort into the accumulator").
  - **`peterfalvi_66_coherence_of_X`** (`noncomputable def`, = G2.6 GOAL, textbook altitude): enum
    `e`/`hsurj` (mmd L76 opening) + pair-chain decomposition (`S₀`/`pair`/`N`/`hS₀`/`hpairs` +
    index-cover `hcoverIdx`) + base prefix coherence `h0` ((1.1)+(1.4)) + per-step (5.6) adjoining
    `hstep` (`retarget_isCoherent`) ⟹ `IsCoherent τ X A` (mmd L84 "Repeated use of (5.6) shows X is
    coherent"). proof = `pairUnion_eq_of_enumCover hsurj … ▸ coherentPairChain S₀ pair h0 N hstep`.
    `hXfin` 는 (6.6) X 유한성 (enum 존재 정당화), `e`/`hcoverIdx`/`h0`/`hstep` 가 *공급* 데이터,
    결론은 chain 으로 derived (posit 無).
  - **honest 판정**: thin wrapper 아님 — `coherentOfPairChainCover` 보다 (a) (6.6) 의 named 결론
    statement 를 textbook altitude 로 제시하고 (b) `exists_monotoneDegreeEnum` enumeration 을
    surjectivity 경유로 engine 에 연결 (set-level cover 를 index-level `hcoverIdx` 로 약화 = caller 가
    χ₁,…,χₙ 따라 index 별 확인). degree-inequality 측은 이미 landed (`two_mul_lt_sq_of_primePow_gap`/
    `sumInflatedDegreeSq`).
  - **정밀 잔존 (G2.7, 불변)**: `hstep` 각 step 의 `retarget_isCoherent` 입력 중 **target characters
    `{Xᵢ, X̄ᵢ}` + image equation + lattice 직교** 의 *구성* = **Dade isometry ν basis extension** 미완
    (orthonormal `X∪Y`/`X` 의 ℤ-linear independence ⟹ free-module basis extension, repo/mathlib 부재).
    + caller 의 decomposition data (`pair`/`N`/index-cover) 를 enum + conjugate-pairing 에서 구성하는
    작업 (conjugation-closed set 의 canonical pairing, 별도 leaf). 상세는 issue 0046 G2.6 PASS 2.

## 進捗 (2026-05-30, issue 1001, Round-9 Track B)

- **(5.4) gateway B1+B2+B3 完了** (`S07_Coherence.lean`, sorry-free):
  - **B1** `OrthonormalCharacterImageFamily τ χ` = (5.2.d) の一般 R(χ) (ℤ[Irr G] の
    orthonormal subset, (χ-χ̄)^τ=∑α). 2 元 `CharacterDifferenceImage` は特殊例で,
    `toOrthonormalImage` で一般 gateway が subsume することを証明 (上の「(5.4.a/b) は
    R(χ) 一般 orthonormal lattice (B1) 선행 필요」を解消)。
  - **B2 (5.4.a)** `CharacterPsiDecomposition.inner_self_chi_re_le_inner_self_X` (‖X‖²≥‖χ‖²)。
  - **B3 (5.4.b)** `norm_eq_and_X_eq_sum_of_norm_Y_ge` (norm 等号 + X=∑_{α∈E}α)。
  - infra: 整数 Cauchy-Schwarz + orthonormal Parseval + inner_conj_symm (ZIrrFourier)。
  - 詳細 `notes/peterfalvi/s07_coherence.md` 「Lean status: (5.2.d) gateway + (5.4)」。
  - これで (5.6)/(5.7) coherence 統合 (上記 Track A の残 (5.6.1)/(5.6.2)) が
    (5.4) gateway を直接消費して書ける土台が揃った (実適用時 `CharacterPsiDecomposition`
    の data 入力を Dade 文脈から構成する作業は残)。
- **(5.4.b) 強化 + (5.5) 追加** (PASS 2, sorry-free, `S07_Coherence.lean`/`ZIrrFourier.lean`):
  - **(5.4.b) に `|E|=‖χ‖²` を追加** (`norm_eq_and_X_eq_sum_of_norm_Y_ge` の結論に
    `(E.card:ℂ)=⟨χ,χ⟩`)。coeff∈{0,1} から `∑coeff=|E|`, keystone で `=‖χ‖²`。
    これは (5.6.3) (mmd 04.7 L101: "X=∑_{α∈E}α for some E⊂R(χ) such that **|E|=‖χ‖²**")
    が `‖χ̄^{τ₂}‖²=|R(χ)|-|E|=‖χ-χ̄‖²-‖χ‖²=‖χ̄‖²` を計算するのに必須の形 (bare ∃E では不足)。
  - **(5.5)** `eq_sum_of_psi_eq_zero` (mmd L55-57): ψ=0 で (5.4) を適用。`‖ψ‖²=⟨0,0⟩=0≤‖Y‖²`
    が正半定値性で自動成立し (5.4.b) を起動, norm 等号 `‖Y‖²=0` が正定値性で **Y=0** を強制,
    `χ^{τ₁}=(χ-0)^{τ₁}=X=∑_{α∈E}α`。(5.5) は §8-§16 で forward 最多 hub (×11 cite)。
  - **正(半)定値性 infra** (ZIrrFourier, ℂ 全体一般・ZIrr 不要): `inner_self_eq_realCast`
    (⟨φ,φ⟩=(|G|:ℝ)⁻¹·∑‖φ(g)‖²) / `inner_self_re_nonneg` / `eq_zero_of_inner_self_re_eq_zero`。
  - AxiomsCheck: (5.5) を追加登録 (計 4 件, 全 allowlist; `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑)。
- [x] (2026-05-31) (6.8)/(6.2) が依存する **§7 Theorem (5.6)** coherence-union hub の
      family-free sub-lemma 2 件を `S07_Coherence.lean` に landing (sorry/axiom 無, 既存 axiom 件数不変):
  - `int_eq_zero_of_sq_mul_le_of_two_mul_lt` ((5.6.2) integer-forcing core, division-free
    `0<D, 0≤z, 0≤a, 2a<D, λ²D-2λa+z≤0 ⇒ λ=0`; sign trichotomy)。
  - `CharacterPsiDecomposition.inner_self_Y_re_le_inner_self_psi` ((5.6.2) 첫 norm bound
    `‖Y‖² ≤ ‖ψ‖²`; landed (5.4.a) + total-norm 항등식에서 `linarith`)。
  - 残 (5.6): (5.6.1) Y-decomposition (family `{χᵢ}`+degree ratio bundle 要), (5.6.3)/main の
    `τ₂` **전역** `IsIntegralIsometry` 확장 생성자 (repo/mathlib 부재; orthonormal-basis →
    전역 등거리)。상세 `notes/peterfalvi/s07_coherence.md` "(2026-05-31)" 절。
- [x] (2026-05-31, pass 2) **(5.6.2) capstone end-to-end + (5.6.3) conjugate-image** を
      `S07_Coherence.lean`/`ZIrrFourier.lean` に landing (sorry/axiom 無, AxiomsCheck 登録,
      full `lake build OddOrder` 緑 3351 jobs)。
  - ZIrrFourier 일반 helper: `inner_self_orthogonalSum_add_re` (직교족+잔차 Pythagoras
    `‖∑cᵢ•vᵢ+Z‖²=∑cᵢ²mᵢ+‖Z‖²`), `inner_self_sum_orthonormal_eq_card`,
    `inner_sum_orthonormal_eq_zero_of_disjoint`。
  - (5.6.2): `sum_sq_mul_add_normSq_Z_le` (기하 절반 `∑cᵢ²mᵢ+‖Z‖²≤‖ψ‖²`) +
    **`lambda_eq_zero_and_Z_eq_zero`** ((5.6.2) **capstone** `λ=0 ∧ Z=0`: 기하∘대수전개∘pass-1
    정수forcing∘정정치성; (5.6.1) 분해 데이터 + `‖ψ‖²=a²m₁` + `r₁m₁=1` + `2a<D` 소비, 전부 구성가능).
  - (5.6.3): `conjImage_eq_neg_sum_sdiff` (`χ̄^{τ₂}=-∑_{R(χ)-E}α`),
    `inner_self_conjImage_eq_card_sdiff` (`‖χ̄^{τ₂}‖²=|R(χ)|-|E|=‖χ̄‖²`),
    `inner_X_conjImage_eq_zero` (`⟨χ^{τ₂},χ̄^{τ₂}⟩=0`) — `τ₂` 구성 없이 (5.4.b) `E` 데이터에서.
  - 남은 단일 장애물 불변: (5.6.1) ambient bundle 구성 + `τ₂` 전역 `IsIntegralIsometry` 확장 생성자.
- [x] (2026-05-31, pass 3) **(5.6.3) re-targeting keystone + (5.6.1) family bundle** を
      `S07_Coherence.lean` に landing (sorry/axiom 無, AxiomsCheck 登録 2 件 各 3 axiom 全 allowlist,
      full `lake build OddOrder` 緑 3351 jobs)。`namespace IntegralCharacterMap` /
      `CharacterFamilyBundle`:
  - **`retarget`** (構成): `τ₁ ∘ₗ orthoResidualMap + (innerLeftℤ χ).smulRight X +
    (innerLeftℤ χ̄).smulRight Xbar`. 즉 `τ₂ φ = τ₁ φ⊥ + ⟨φ,χ⟩·X + ⟨φ,χ̄⟩·X̄`,
    `φ⊥ = φ − ⟨φ,χ⟩χ − ⟨φ,χ̄⟩χ̄` (Gram–Schmidt 잔차). **핵심 미묘점**: 잔차를 `τ₁` *전에* 취함
    — `τ₁` 은 ℤ-선형뿐이므로 복소 Fourier 계수를 통과시킬 수 없다 (naive `τ₁+correction` 형은 틀림).
    `innerLeftℤ` (ℤ-선형 functional `φ↦⟨φ,η⟩`), `orthoResidualMap` (ℤ-선형 projection) 도 구성.
  - 일치 보조정리: `retarget_apply_left` (χ↦X), `retarget_apply_right` (χ̄↦X̄),
    `retarget_eq_of_orthogonal` ({χ,χ̄}^⊥ 위 τ₁ 일치) — 전부 orthonormal pair 가정에서.
  - **`retarget_isIntegralIsometry`** (CRUX, 전역 등거리): `τ₁` 전역 등거리 + {χ,χ̄}/{X,X̄}
    동일 gram orthonormal + `∀ξ⊥{χ,χ̄}, ⟨τ₁ξ,X⟩=⟨τ₁ξ,X̄⟩=0` ⟹ `IsIntegralIsometry (retarget …)`.
    증명: `inner_block_expand` (sesquilinear block normal form) 을 source/image 양변에 적용,
    둘 다 `⟨φ⊥,ψ⊥⟩+s·conj s'+t·conj t'` 로 환원 (φ⊥ 직교성 + 가설 직교성 + τ₁ 등거리).
  - **`CharacterFamilyBundle`** (5.6.1 구성, posit 無): family `{χᵢ}_{i∈s}⊆S₁`, ratio aᵢ∈ℕ
    (a₁=1), degree scaling, `χ⊥S₁` + `{χᵢ}` pairwise 직교. **`crossDifference_inner`** (정리, 비-posit):
    `⟨χ−aχ₁, χᵢ−aᵢχ₁⟩ = a·aᵢ·‖χ₁‖²` (i≠i₁), `χ⊥S₁`+pairwise 직교에서 도출.
  - **정밀 잔존 (main (5.6) 미착지)**: repo 의 `IsIntegralIsometry` 는 **전역** (모든 φ,ψ) 인데
    Peterfalvi (5.6.3) 의 `τ₂` 등거리는 격자 `ℤ[S₁∪{χ,χ̄}]` 위에서만 검증된다. keystone 의
    가설 `∀ξ⊥{χ,χ̄}, ⟨τ₁ξ,X⟩=0` 은 `X∈ℤ[R(χ)]` 가 `span{τ₁χ,τ₁χ̄}` 밖이면 (일반적으로 그렇다)
    주어진 S₁-coherence 확장 τ₁ 에 대해 **충족 불가** (τ₁ 의 span 밖 값은 비제어). 따라서 main (5.6)
    은 추가 brick = **"부분공간 등거리 → 전역 등거리 확장" (유한차원 ℂ class-function 공간의
    Witt/Gram–Schmidt 확장)** 또는 격자-상대 `IsCoherent` 재정식화가 필요. keystone 자체는
    R(χ)⊆span{τ₁χ,τ₁χ̄} (예: 2-원소 (5.2.d) base) 에서 직접 사용 가능하며 (5.6) 의 대수적 심장.
- [x] (2026-05-31, pass 4) **(5.6.3) 격자-相対 keystone + 大域 assembly bridge + span infra**
      (sorry/axiom 無, AxiomsCheck 신규 7 건 各 3 axiom 全 allowlist, full `lake build OddOrder`
      緑 3351 jobs; commits 63f7437 / e5ac588 / fede79c). Pass 3 의 "전역 vs 격자" 잔존의 **격자
      측 해결**:
  - **`retarget_inner_eq_on`** (격자-相対 keystone, 진짜 충족가능형): 전역 keystone 가설
    `∀ξ⊥{χ,χ̄},⟨τ₁ξ,X⟩=0` 은 (5.6) 일반위치 비충족 (X=μ∉span{τ₁χ,τ₁χ̄}; τ₁=hS₁.extension 은
    χ−χ̄ 위 τ 와 무관, χ∉S₁). 대신 ℂ-부분가군 `M` ({χ,χ̄}-잔차 닫힘, χ,χ̄∈M) 위 `⟨·,·⟩` 보존,
    `X,X̄⊥τ₁ξ` 도 `ξ∈M⊥{χ,χ̄}` 한정. `M=span_ℂ(S₁∪{χ,χ̄})` ⟹ 잔차∈span_ℂ S₁ ⟹ 가설은 정확히
    honest 한 (5.5)+(5.2.e) `X,X̄⊥S₁^{τ₁}`. **(5.6.3) 격자 등거리 `Z[S₁∪{χ,χ̄}]→Z[Irr G]`, §7 가
    실제 공급.** 증명 전역판과 동일 `inner_block_expand` (잔차 ∈M submodule 닫힘).
  - **`retarget_isCoherent`** (`noncomputable def`): hS₁ + orthonormal {χ,χ̄}/{X,X̄} +
    `X̄=X−(χ−χ̄)^τ` + (5.5)+(5.2.e) 전역 orthogonality + (5.6.2) image eq (a:ℕ) + (5.1)-generation
    ⟹ `IsCoherent τ (S₁∪{χ,χ̄}) A`. τ₂:=retarget **구성** (posit 無). extends_on_supported 는
    차이생성원 `{χ−χ̄,χ−a·χ₁}∪Z[S₁,L^#]` 일치 + span-induction. ⚠️ 전역 keystone 의존 ⟹
    X,X̄∈span{τ₁χ,τ₁χ̄} 특수상황 (예: (5.2.d) 2-원소 base) 에서만 적용 (정직하나 main 일반형 아님).
  - **재사용 infra**: `eq_on_zSpan_of_eq_on` (생성집합 일치 ⟹ ℤ-span 일치),
    `inner_eq_zero_of_mem_zSpan` (η⊥T ⟹ η⊥ℤ[T]), `retarget_eq_on_zSpan_of_orthogonal`,
    `inner_eq_zero_of_eq_intCast_sum` (X=∑c(α)•α + η⊥각 α ⟹ η⊥X; `X_eq`→hX_ortho 다리).
  - **정밀 잔존 (단 하나, 정의적 결정)**: main (5.6) 유일 gap = `IsCoherent.extension_isometry` 가
    **전역** `IsIntegralIsometry` 요구. 격자 등거리 `retarget_inner_eq_on` 은 이미 구성. **권장
    경로**: `extension_isometry` 를 격자-相対 (`Z[S]` 위) 로 약화 — (a) Peterfalvi (5.6.3) 자체가
    격자만 주장, (b) 하류 `S08 IndChainDecomposition.ofIsCoherent` 는 `extension_inner_eq` 를
    ζt∈S (격자원) 에만 적용 (S08_CoherenceTheorems.lean:251-253, 전역성 미사용), (c) 전역은
    dim CF(L)≤dim CF(G) 필요 — FT 비보장 ⟹ 현 정의 일반 충족불가 가능성. 약화 후 본 라운드 infra 가
    즉시 main (5.6) 완성. **단 shared `IsCoherent`/S08 영향 ⟹ main 합류 시 결정 (worktree 단독
    변경 회피).** 대안 (Witt 전역확장) 은 dim 조건 + bespoke mathlib 부재로 열세.
- [x] (2026-05-31, pass 5) **USER-APPROVED def 약화 + general (5.6) UNCONDITIONAL 완성**
      (`S07_Coherence.lean`/`S08_CoherenceTheorems.lean`/`AxiomsCheck.lean`; sorry/axiom 無 —
      `#print axioms retarget_isCoherent` = {propext, Classical.choice, Quot.sound}, full
      `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351/3334 jobs; commit b14a987). Pass-4 의
      "권장 경로" (격자-相對 약화) 를 실행하여 **main (5.6) 의 유일 gap 해소**:
  - **`IsCoherent` 약화**: 전역 `extension_isometry : IsIntegralIsometry extension` 필드를
    격자-相對 `extension_inner_eq : ∀ φ ψ ∈ zSpan S, ⟨ν φ, ν ψ⟩ = ⟨φ, ψ⟩` 로 교체. FT 에서
    `dim CF(L) > dim CF(G)` 이라 전역 등거리는 일반 부재; Peterfalvi 의 실제 대상 = 격자 등거리.
  - **신규 keystone 2 건**: `IntegralCharacterMap.orthoResidualMap_mem_zSpan` ({χ,χ̄} Gram–Schmidt
    잔차가 `ℤ[S₁∪{χ,χ̄}]→ℤ[S₁]`, `span_induction`; 생성원 x∈S₁↦x, χ↦0, χ̄↦0) +
    **`retarget_inner_eq_on_zSpan_union`** (정직 충족형 integral-span keystone: 재타게팅이
    `ℤ[S₁∪{χ,χ̄}]` 전체에서 `⟨·,·⟩` 보존, **τ₁ 의 `ℤ[S₁]`-등거리** + 격자 직교 `X,X̄⊥τ₁ξ` (ξ∈ℤ[S₁])
    만 사용 — 전역 등거리 불요). 잔차∈ℤ[S₁] ⟹ `inner_block_expand` 로 폐합.
  - **`retarget_isCoherent` 이제 UNCONDITIONAL general (5.6)**: `hX_ortho`/`hXbar_ortho` 를 정직한
    격자형 (∀ξ∈ℤ[S₁]) 으로 약화, τ₂:=retarget 구성, `retarget_inner_eq_on_zSpan_union` 로 약화된
    `IsCoherent` 산출. special-position 제한 제거; X,X̄⊥S₁^{τ₁} 는 진짜 (5.5)+(5.2.e) 격자 사실
    (전역 over-strong 판 아님, posit 無).
  - **S08 consumer 적응**: `IndChainDecomposition.ofIsCoherent` 에 `hζ_mem : ∀ t, ζ t ∈ S` 추가,
    `Submodule.subset_span` (ζt∈S⊆zSpan S) 로 격자 `extension_inner_eq` 공급. 약화는 consumer 의
    증명을 **쉽게** 만들 뿐 (전역성 미사용이었음). `sibleySetup_is_coherent` (여전히 sorry) 는 약화된
    `CoherenceTarget` 에 그대로 typecheck — 향후 증명도 약화로 더 쉬워짐.
  - **§5 coherence hub (5.6) 일반형 완료** = 쌍 인접으로 coherence 를 짓는 귀납 엔진, §6 (case-A/B
    coherence) 및 궁극적으로 S08:188 `sibleySetup_is_coherent` 로의 관문.
- [x] (2026-05-31, pass 6) **(6.8.1)/(6.8.2) `τ₃`-gluing 의 algebraic heart 2건** 을
      `S07_Coherence.lean` 에 landing (PARTIAL; sorry/axiom 無, AxiomsCheck 등록 2건 각 3 axiom 全
      allowlist, full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351 jobs). **이번 round 의
      recommended first leaf `case_A_X_union_Y_coherent` (L2.2) 는 NOT tractable 로 판정** — roadmap 의
      "(5.6) `retarget_isCoherent` direct consumer ~100-140 LOC" 는 과대평가 (실제 (6.8.1) mmd L158-176
      은 (6.6) coherence-of-X + (6.7) congruence forcing + **두 family** orthonormal union 구성을
      요하며 single-pair `retarget` 로는 불가; thin `SibleySetup` 은 S=Ind/Dade/X/Y/τ₁/τ₂/(6.6) 미보유
      ⟹ statement화하면 scaffolding). 대신 L2.2 와 case (B) 가 공통 소비하는 foundational primitive landing:
  - **`inner_orthogonal_glued_eq`** : `a,a'∈ℤ[X]`,`b,b'∈ℤ[Y]`, `νX`/`νY` 각 lattice 등거리 + source
    직교 `⟨a,b'⟩=⟨b,a'⟩=0` + image 직교 `⟨νX a,νY b'⟩=⟨νY b,νX a'⟩=0` ⟹
    `⟨νX a+νY b, νX a'+νY b'⟩=⟨a+b,a'+b'⟩`. `inner_block_expand` 의 two-lattice 판, gluing 의 대수적 심장.
  - **`inner_eq_on_zSpan_union_of_orthogonal`** : 위를 `ℤ[X∪Y]=ℤ[X]⊔ℤ[Y]` (`Submodule.span_union`)
    전체로 lift — `νX`/`νY` 에 일치하는 임의 `ν` 가 `ℤ[X∪Y]` 에서 `⟨·,·⟩` 보존. = 합집합 glued map
    `τ₃` 의 약화된 `IsCoherent.extension_inner_eq` field.
  - **정밀 잔존 (full L2.2)** : (i) (6.6) coherence-of-X witness, (ii) `νX`(τ₂)/`νY`(τ₁) extension 및
    `himg_ortho` 를 case-A/B character theory ((6.7) 포함) 에서 생성, (iii) glued `ν=τ₃` 의 well-defined
    구성 = orthonormal `X∪Y` 의 ℤ-linear independence ⟹ free-module basis extension (repo/mathlib 부재
    infra) + `extends_on_supported` (case별 difference-generator). (iii) 이 핵심 missing infra.
- [x] (2026-05-31, pass 7) **(6.8.1)/(6.8.2) `τ₃` 두-family `IsCoherent` 조립기
      `coherentUnion_of_glued`** 를 `S07_Coherence.lean` 에 landing (PARTIAL; sorry/axiom 無 —
      `#print axioms coherentUnion_of_glued` = {propext, Classical.choice, Quot.sound}; AxiomsCheck
      등록 1건 3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351/3334 jobs).
      pass-6 의 잔존 (iii) 중 **`extends_on_supported` + 실제 `IsCoherent` witness 산출**을 정직하게 해소
      (= pass-6 의 두 항등식 `inner_orthogonal_glued_eq`/`inner_eq_on_zSpan_union_of_orthogonal` 의
      자연스러운 소비자, single-pair `retarget_isCoherent` 의 **두-family 유사물**):
  - **`coherentUnion_of_glued`** (`noncomputable def`) : `hX : IsCoherent τ X A`,
    `hY : IsCoherent τ Y A` (= **공급** 데이터, posit 無 — (6.6) / (1.1)·(1.4) 의 결론), 글루된 map
    `ν : IntegralCharacterMap L G` (`hX.extension` 에 `ℤ[X]` 에서, `hY.extension` 에 `ℤ[Y]` 에서 일치 =
    Peterfalvi 의 `τ₃` "coincides with τ₂ on X and τ₁ on Y"), source 직교 `hsrc_ortho` + image 직교
    `himg_ortho`, 그리고 (5.1)-type 생성 가설 `hgen : Z[X∪Y,A] ⊆ span ℤ(Z[X,A] ∪ Z[Y,A])` ⟹
    `IsCoherent τ (X∪Y) A`. 두 field 방전: `extension_inner_eq` = `inner_eq_on_zSpan_union_of_orthogonal`
    (격자 등거리 `hX`/`hY.extension_inner_eq` + 두 직교성 투입), `extends_on_supported` =
    `eq_on_zSpan_of_eq_on` over generator `Z[X,A]∪Z[Y,A]` (`Z[X,A]` 위 `ν=νX=τ`,
    `Z[Y,A]` 위 `ν=νY=τ`), `nonzero` 는 `X⊆X∪Y` 에서 상속. **character theory 미포함** ((6.7)
    congruence / 명시 `X=χ₁^{τ₁}` / Dade isometry 는 입력 `hX`/`hY`/`hagreeX`/`hagreeY`/직교성을
    *생산* 하는 별도 작업).
  - **정밀 잔존 (full L2.2, pass-7 이후)** : (i) **(6.6)** coherence-of-X witness `hX`
    (별 issue; ~8-step character theorem), (ii) **case-A/B character theory** 가 `hY`(=Y coherence,
    (1.1)·(1.4)) / `hagreeX`·`hagreeY` (glued map `ν=τ₃` 의 lattice 일치) / `hsrc_ortho` (X⊥Y on source)
    / `himg_ortho` (`X^{τ₂}⊥Y^{τ₁}`, (4.1)+(6.7) congruence) / `hgen` 을 생산 (가장 무거운 미형식화 덩어리),
    (iii) glued map `ν=τ₃` 자체의 **canonical 구성** — orthonormal `X∪Y` 의 ℤ-기저 확장 (ℂ-valued
    class-function 공간이라 ℤ-projection 이 비정수 계수 ⟹ free-module 기저 확장 infra 必, repo/mathlib
    부재). 현 `coherentUnion_of_glued` 는 `ν` 를 **공급 데이터**로 받음 (Peterfalvi 의 `τ₃` 가 실제로
    orthonormal 기저에서 구성되는 정직한 supplied data) ⟹ assembler 자체는 honest·general·완결.
    조립기는 끝났고, 남은 건 그 입력을 채우는 (i)/(ii)/(iii)-canonical 의 character/free-module 작업.
- [x] (2026-05-31, pass 8) **(6.6) "repeated use of (5.6)" iteration engine** `coherentPairChain` 를
      `S07_Coherence.lean` 에 landing (sorry/axiom 無 — `#print axioms coherentPairChain` =
      {propext, Classical.choice, Quot.sound}; AxiomsCheck 등록 2건 각 3 axiom 全 allowlist; full
      `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351/3334 jobs). (6.6) 증명의 결론
      "**Repeated use of Theorem (5.6)** then shows that X is coherent" (mmd L84) 을 정직하게 형식화 —
      single-pair `retarget_isCoherent` 를 pair 수에 대한 induction 으로 fold 하는 **반복 엔진**.
      이번 round 의 G1 plumbing (L1.1 Dade 추출 / L1.2 case-A/B split) 은 **honest 하지 않다고 판정**해
      skip (아래 G1 판정).
  - **`pairSet pair i := {(pair i).1, (pair i).2}`** (i-번째 adjoined pair `{χᵢ, χ̄ᵢ}`),
    **`pairUnion S₀ pair`** (`0 ↦ S₀`, `i+1 ↦ pairUnion … i ∪ pairSet … i`; i 번 adjoin 후 누적집합),
    `pairUnion_zero`/`pairUnion_succ` (simp), `subset_pairUnion_succ`, **`pairUnion_mono`**
    (`i ≤ j ⟹ pairUnion … i ⊆ pairUnion … j`; `Nat.le` induction).
  - **`coherentPairChain`** (`noncomputable def`): coherent base `h0 : IsCoherent τ S₀ A` +
    per-index adjoining step `hstep : ∀ i < N, IsCoherent τ (pairUnion S₀ pair i) A →
    IsCoherent τ (pairUnion S₀ pair (i+1)) A` ⟹ `IsCoherent τ (pairUnion S₀ pair N) A`. proof 는
    `N` 에 대한 well-founded recursion (`0 ↦ h0`, `N+1 ↦ hstep N _ (코herentPairChain … N (step 약화))`).
    각 `hstep i _` 는 (5.6) 1회 적용 = `retarget_isCoherent` 에 caller 의 per-step (5.6) data
    (orthonormal `{χᵢ,χ̄ᵢ}`/`{Xᵢ,X̄ᵢ}`, image 방정식, lattice 직교, (5.1)-generation; *현재* 확장
    `hcoh.extension` 을 참조하므로 running witness 의 함수로 주어짐) 를 투입하면 산출. 엔진은
    **induction 자체** 만 기여 — 최종 coherence 는 **derived** (posit 無). general·reusable
    (임의 chain; (6.6) 의 degree/divisibility 산술과 decouple). = roadmap 의 G2.7 "repeated (5.6)"
    의 honest core. 남은 (6.6) 작업 = 각 step 의 (5.6) data 생산 (degree sort/θᵢ(1) p-power/
    [Is]Cor 2.30/(6.4.c) coprimality forcing) + base prefix coherence ((1.1)/(1.4)).
  - **G1 판정 (skip 사유, honest 하지 않음)**: `SibleySetup` 는 **Dade isometry 필드도, X/Y 집합도,
    case-A/B flag (`Z(H)∩[H,H]` vs `W₂`) 도, (6.6) data 도 보유하지 않음** (필드 = `coherence`,
    `K`, `H`, `W1`, `H_sharp_ti`, normality). (L1.1) "Dade τ 추출" = `hyp.coherence.tau` 단순 필드
    접근이며 이미 `coherence_tau_inner_eq` 로 노출됨 ⟹ 순수 thin wrapper (repo 규약 금지). (L1.2)
    case-A/B split = 분기에 필요한 `Z`·`W₂`·case 술어를 새 가설로 *외출* 해야 함 ⟹ scaffolding
    (memory `scaffold-sorry-free-not-done` + task 금지). 따라서 G1 은 honest 하게 착지할 수 없어
    skip; 대신 task (b) 의 §5-engine-consuming first leaf 를 landing.
- [x] (2026-05-31, pass 2-cont) **(6.6) prime-power degree gap (mmd L82) leaf** 를 `S07_Coherence.lean`
      에 landing (sorry/axiom 無 — `#print axioms` = {propext, Classical.choice, Quot.sound}; AxiomsCheck
      등록 2건 각 3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351/3334 jobs).
      pass-1 `coherentPairChain` 의 각 `hstep` 이 소비하는 **strict degree-ratio bound**
      `2·χᵢ(1)·χ₁(1) < ∑_{j<i}χⱼ(1)²` (= (5.6.2) core `int_eq_zero_of_sq_mul_le_of_two_mul_lt` 의 `2·a < D`
      전제) 를 (6.6) 의 prime-power 구조에서 정직하게 도출하는 number-theoretic leaf.
      `int_eq_zero_of_sq_mul_le_of_two_mul_lt` (line 1032) 직후 (5.6) section 안에 배치:
  - **`two_mul_lt_sq_of_primePow_gap`** (ℕ): `dᵢ = q·d₁`, `q = p^m`, `p ≥ 3`, `d₁ < dᵢ` ⟹
    `2·dᵢ·d₁ < dᵢ²`. proof: `q > 1` (else `dᵢ ≤ d₁`) + `q = p^m > 1` ⟹ `m ≥ 1` ⟹ `p ≤ q` ⟹
    `dᵢ = q·d₁ ≥ p·d₁ ≥ 3·d₁`, `nlinarith`. = mmd L82 의 `2χᵢ(1)χ₁(1) < pχᵢ(1)χ₁(1) ≤ χᵢ(1)²` 의
    load-bearing 산술 (χⱼ(1)=|L:K|·θⱼ(1), θⱼ(1) p-power ⟹ χᵢ(1)/χ₁(1)=p^m, `|L| odd ⟹ p ≥ 3`).
  - **`two_mul_lt_of_sq_dvd_of_gap`** (ℕ): gap `2·dᵢ·d₁ < dᵢ²` + `dᵢ² ∣ D` (= `χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`)
    + `0 < D` ⟹ `2·dᵢ·d₁ < D` (positivity 로 `dᵢ² ≤ D`).
  - **`two_mul_degree_lt_sum_ratCast`** (ℚ, consumer-facing): 위 둘을 합쳐 prime-power gap data +
    square-divisibility 에서 `2·((dᵢ:ℚ)·(d₁:ℚ)) < (D:ℚ)` 산출 = (5.6) core 의 `2·a < D` 전제 직접 공급.
    각 `coherentPairChain` step 의 (5.6.2) integer-forcing 의 degree 가설이 ℕ degree data 에서 방전됨.
  - **honest 판정**: prime-power gap (`dᵢ = q·d₁`, `q = p^m`) 와 square-divisibility (`dᵢ² ∣ D`) 는 둘 다
    (6.6) data 의 정직한 귀결 (K = p-group ⟹ θ degree p-power; (6.4.c) coprimality + sum identity ⟹
    `χᵢ(1)² ∣ ∑_{j<i}`). posited hypothesis 아님 — 실수 부등식을 실 number-theoretic 가설에서 도출.
  - **(6.6) 남은 작업 (pass-2 이후)**: 각 step 의 (5.6) data *나머지* 생산 — degree sort (X 를
    `χ₁(1) ≤ ⋯ ≤ χₙ(1)` 로 정렬해 `coherentPairChain` 의 `pair` index 화) + per-index prime-power gap
    가설 (`χᵢ(1) = q·χ₁(1)`, `q = p^m`; θ degree p-power) + square-divisibility (`χᵢ(1)² ∣ ∑_{j<i}`;
    [Is] Cor 2.30 `θᵢ(1)²≤|K:Z|` + sum identity + (6.4.c) coprimality) 를 본 leaf 에 plug; + base prefix
    coherence ((1.1)/(1.4)). degree-bound 부분은 본 leaf 가 공급, 나머지가 `hstep`/`h0` 의 잔여 입력.
- [x] (2026-05-31, pass 2 leaf 2) **(6.6) square-divisibility producers (mmd L78-80)** 를
      `S07_Coherence.lean` (`two_mul_degree_lt_sum_ratCast` 직후) 에 landing (sorry/axiom 無 —
      `#print axioms` = {propext, Quot.sound} (Classical.choice 불요); AxiomsCheck 등록 2건 각 2 axiom 全
      allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351/3334 jobs). leaf 1 의 `hdvd`
      입력 (`χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`) 을 *생산* 하는 mmd L80 chain 의 두 load-bearing 산술 step 을 분리:
  - **`dvd_of_add_eq_of_dvd_dvd`** (ℕ): `head + tail = total`, `a∣tail`, `a∣total` ⟹ `a∣head`.
    mmd L78+L80 의 combination step — `head = ∑_{j<i}χⱼ(1)²`, `tail = ∑_{j≥i}χⱼ(1)²`,
    `total = |L|-|L:Z|` 로 `θᵢ(1)² ∣ tail` (smallest p-power) + `θᵢ(1)² ∣ total` ([Is] Cor 2.30
    `θᵢ(1)²≤|K:Z|`) ⟹ `θᵢ(1)² ∣ head`. **additive equation** 로 진술해 ℕ truncated subtraction 회피
    (`Nat.dvd_sub` + `omega` rewrite).
  - **`sq_dvd_of_factored_coprime`** (ℕ): `χᵢ(1) = idx·θ` (idx=|L:K|, θ=θᵢ(1)), `θ²∣D`, `idx²∣D`,
    `Coprime idx θ` ⟹ `χᵢ(1)²∣D`. mmd L80 의 coprimality forcing — `(|L:K|,p)=1` & θ p-power ⟹
    `Coprime idx² θ²` (`Nat.Coprime.pow`), coprime divisors 곱 (`mul_dvd_of_dvd_of_dvd`),
    `χᵢ(1)²=idx²·θ²` (`ring`).
  - **2026-06-04 追記**: `sq_dvd_sum_sq_mul_of_dvd` を追加。`∀ j∈tail, θ∣θⱼ` から
    `θ²∣∑_{j∈tail}(idxⱼ·θⱼ)²` を返す `Finset.dvd_sum` leaf で、残入力のうち
    `θᵢ(1)² ∣ ∑_{j≥i}` の summand-divisibility 部分を切り出した。
  - **2026-06-04 追記 2**: `sq_dvd_primePow_of_sq_le` / `sq_dvd_primePow_mul_of_sq_le` を追加。
    `θ=p^m`, `q=p^n`, `θ²≤q` から `θ²∣q` と `θ²∣q*c` を作り、[Is] Cor 2.30 の
    `θᵢ(1)²≤|K:Z|` を p-power 比較で total 側 divisibility へ落とす算術部分を切り出した。
  - **2026-06-04 追記 3**: `dvd_primePow_of_le` / `dvd_primePow_of_mul_le_mul` /
    `sq_dvd_sum_sq_mul_const_of_primePow_mul_le` を追加。degree-sort の `idx·θ≤idx·θⱼ` から
    固定正 `idx` をキャンセルして `θ∣θⱼ` を作り、tail 側 `θ²∣∑(idx·θⱼ)²` まで直接返す。
  - **2026-06-04 追記 4**: `mul_primePow_dvd_mul_primePow_of_le` /
    `sq_dvd_head_of_commonIndex_primePower_sums` と S08 adapter
    `natDegreeDvd_of_commonIndex_primePowerData` /
    `degreeDivisibilityInputs_of_commonIndex_primePowerData` /
    `xAdjoinStepInput_of_memberFamily_degreeDivisibility_primePowerSums` を追加。common `idx` + p-power
    残差 + degree sort から degree-ratio 用 divisibility と `dχ²∣D` を構成し、S08 `XAdjoinStepInput`
    の black-box 算術入力を一段削った。
  - **2026-06-04 追記 5**: `xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums` を追加。
    前項 producer を `primePowerSums` constructor に接続し、`hdvd_mem` / `hdvdχ` / `dχ²∣D` を
    common `idx` + p-power 残差 + degree sort + tail/head sum data から内部生成する interface にした。
  - **2026-06-04 追記 6**: `natDegree_pos_of_irreducibleCharacter_apply_one_eq` /
    `natDegreeSquareSum_pos_of_memberFamily` を追加し、`primePowerSums` / `commonIndexPrimePowerSums`
    の caller 入力から `hpos₁`/`hDpos` を除去。common-index 版の `hleχ` も `hlt` から内部導出。
  - **2026-06-04 追記 7**: `xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums` を追加。
    actual accumulator `pairUnion (xBaseBlock Z) pair i` の injective finite enumeration から cover /
    non-real / conjugate support / conjugate membership / orthonormality を内部構成し、step caller に残す入力を
    同じ enumeration 上の genuine (6.6) degree・p-power・sum・coprimality data へ絞った。
  - **2026-06-04 追記 8**: `PairUnionCommonIndexPrimePowerStepData` /
    `Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X` を追加。per-step caller は
    `XAdjoinStepInput` record を構成せず、actual pair-cover prefix ごとの common-index/p-power data package を
    返せば chain fold が internally `pairUnion` adapter を適用して `X` coherence まで進む。
  - **2026-06-04 追記 9**: `natDegree_le_of_xBaseBlock_anchor` /
    `natDegree_lt_of_xBaseBlock_anchor_of_not_mem` と
    `xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums` を追加。base-block anchor から
    `d₁≤dmem j` を、current pair と prefix の disjointness から `χs i∉xBaseBlock Z` および
    `d₁<dχ` を内部導出し、step caller の sorted-degree 入力を 2 つ削った。
  - **2026-06-04 追記 10**: `PairUnionBaseAnchorCommonIndexPrimePowerStepData` /
    `Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X` を追加。
    base-anchor step adapter を chain fold まで持ち上げ、per-step data package から `hlt`/`hlemem`
    を削除。caller が渡す sorted-degree 情報は base-block anchor と actual pair-cover disjointness から
    internally 復元される。
  - **2026-06-04 追記 11**: `sq_dvd_natDegreeSquareSum_of_commonIndex` を追加し、`hDsum` と
    common-index member factorizations `hdmem` から `idx²∣D` を内部導出。`memberFamily` / `pairUnion` /
    base-anchor common-index adapters と `PairUnion*StepData` から caller-supplied `hidx_D` を削除した。
    低層 `degreeDivisibility_primePowerSums` は tail 側 sum data だけを受ける層なので `hidx_D` 入力を残し、
    common-index adapter が局所 `have hidx_D` を作って接続する。
  - **2026-06-04 追記 12**: actual `Fin k` prefix 版で `D` / `hDsum` を内部化。
    `xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums` と base-anchor 版は
    `Dprefix := ∑ j : Fin k, dmem j*dmem j` を局所定義して generic member-family adapter へ渡す。
    両 `PairUnion*StepData` からも `D` / `hDsum` field を削除し、caller は direct sum identity
    `(∑j dmem(j)^2) + tail = total` だけを供給すればよい。
  - **2026-06-04 追記 13**: `commonIndex_pos_of_natDegree_factor` を追加し、
    `degreeDivisibility_primePowerSums` 以降の common-index adapters と両 `PairUnion*StepData` から
    caller-supplied `hidxpos : 0 < idx` を削除した。`idx > 0` は `χ(1)>0` と
    `dχ = idx*θχ` から内部導出される。
  - **2026-06-04 追記 14**: `coprime_commonIndex_primePower` を追加し、
    `degreeDivisibility_primePowerSums` 以降の common-index adapters と両 `PairUnion*StepData` から
    caller-supplied `hcop : Nat.Coprime idx θχ` を削除した。caller は (6.4.c) の
    `hidx_p : Nat.Coprime idx p` を渡し、`θχ = p^mχ` から adapter 内で必要な coprimality を復元する。
  - **honest 판정**: 이 producer들은 순수 산술 — 입력 divisibility 는 character-degree 구조의 정직한 귀결
    (additive sum identity, [Is] Cor 2.30, (6.4.c) coprimality). posited 아님.
  - **(6.6) 잔여 (pass-2 leaf-2 이후)**: 이 producer들의 *입력* divisibility 생산 (sum identity
    `∑_{j<i}+∑_{j≥i}=|L|-|L:Z|` = column-orthogonality 의 character theory; `θᵢ(1)² ∣ ∑_{j≥i}`
    = smallest-p-power-divides-sum, `Finset.dvd_sum`+`pow_dvd_pow`; `θᵢ(1)²≤|K:Z|` = [Is] Cor 2.30;
    `(|L:K|,p)=1` = (6.4.c)) + degree sort + base prefix coherence ((1.1)/(1.4)). 이 character-theory
    덩어리들이 leaf 1+2 의 가설을 채우면 (6.6) 의 `coherentPairChain` `hstep` data 가 완성.
- [x] (2026-05-31, G2.0) **(6.6) opening "By (1.1), `n ≥ 2`" (mmd L76)** 를 `S07_Coherence.lean`
      ((6.6) section 의 `pairSet` 직전) 에 landing (sorry/axiom 無 — AxiomsCheck 등록 1건 3 axiom 全
      allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351/3334 jobs).
  - **`two_le_ncard_of_conjugate_closed_of_noReal`**: `X : Set (ClassFunction L ℂ)` 가 finite +
    nonempty + `ClosedUnderConjugate` + `HasNoRealCharacters` ⟹ `2 ≤ X.ncard`.  mmd L76 "Let
    `n=|X|`. By (1.1), `n ≥ 2`" 의 정직한 일반형: (1.1) 이 공급하는 두 사실 — conjugation 폐쇄
    (`χ∈X ⟹ χ̄∈X`, `Z` normal 로 `Ker χ̄ = Ker χ`) + non-self-conjugate (`χ̄ ≠ χ`, `|L|` odd &
    nontrivial) — 가 nonempty 와 결합해 `χ`, `χ̄` 두 distinct member 를 주어 `1 < X.ncard`
    (`Set.one_lt_ncard`) → `2 ≤ X.ncard` (`omega`).
  - **honest 판정**: thin wrapper 아님 — `Set.one_lt_ncard ↔ ∃ a∈s ∃ b∈s, a≠b` 는 bridge 일 뿐,
    내용은 conjugation involution 으로부터 distinct witness `χ̄ ≠ χ` 를 *구성* 하는 부분.
    두 가설 (`ClosedUnderConjugate`/`HasNoRealCharacters`) 은 §7 `Hypothesis` 필드 (각각
    `conjugate_closed`/`no_real_characters`) 이고 `X ⊆ S` 로 상속 (`HasNoRealCharacters.mono`,
    `ClosedUnderConjugate` 는 caller 가 `S(Z)` conj-폐쇄성과 함께 공급) — posited 아님.
  - **caller 측 잔여 (G2.0 이후)**: (6.6) 본문이 이 leaf 를 instantiate 하려면 `X = S − S(Z)` 의
    nonemptiness (`Z ≠ 1` ⟹ `Z ⊄ Ker χ` 인 irreducible 존재) + `S(Z)` conj-폐쇄성 (그래야 `X`
    가 conj-폐쇄) 을 공급해야 함. 이는 §6 setup-specific character theory 로 별도 leaf.
- [x] (2026-05-31, G2.1) **(6.6) opening "Set `X = {χ₁,…,χₙ}`, where `χ₁(1) ≤ ⋯ ≤ χₙ(1)`" (mmd L76)**
      = degree-sort 단계 를 `S07_Coherence.lean` ((6.6) section, `two_le_ncard_…` 직전) 에 landing
      (sorry/axiom 無 — `#print axioms` = `[propext, Classical.choice, Quot.sound]`; AxiomsCheck 등록
      1건 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑).
  - **`exists_monotoneDegreeEnum`**: `X : Set (ClassFunction L ℂ)` finite ⟹ `∃ e : Fin X.ncard →
    ClassFunction L ℂ`, injective + `∀ i, e i ∈ X` + range = X (`∀ χ∈X, ∃ i, e i = χ`) + real degree
    key `χ ↦ (characterDegree χ).re` 따라 monotone (`i ≤ j ⟹ (deg (e i)).re ≤ (deg (e j)).re`).
    mmd L76 의 정직한 일반형. 구성: 유한성 → `Fintype.equivFinOfCardEq` 로 `g : X ≃ Fin n`
    (`n=X.ncard`; bridge `Fintype.card = Nat.card = ncard`), key `k i := (deg (g.symm i)).re`,
    `σ := Tuple.sort k`, `e i := g.symm (σ i)`. injective = `Subtype.val ∘ g.symm ∘ σ` 세 합성;
    surjective = `i = σ⁻¹(g⟨χ,_⟩)`; monotone = `Tuple.monotone_sort k` (`(deg (e i)).re = (k∘σ) i`).
  - **honest 판정**: thin wrapper 아님 — `Tuple.sort`/`Tuple.monotone_sort` 만으로는 *set* 의 monotone
    enumeration 이 안 나옴 (임의 `Fin n ≃ X` 선택 + key pull-back + injective/surjective/range 재조립).
    순수 order-이론적 "finite family 를 real key 로 sort" 단계 — irreducibility/induced-from-K/p-power
    degree 전혀 미사용, 임의 finite class-function set 에 일반형. import `Mathlib.Data.Fin.Tuple.Sort`.
  - **caller 측 잔여 (G2.1 이후)**: enumeration → `coherentPairChain` 의 `pair : ℕ → χ×χ̄` + base
    prefix `{χ₁,…,χₖ}` (equal-minimal-degree, (1.1)+(1.4) coherent) 연결 + per-step (5.6) data 생산
    (θᵢ(1) p-power, [Is] Cor 2.30, `χᵢ(1)² ∣ ∑_{j<i}` → `two_mul_lt_sq_of_primePow_gap`). enumeration
    자체는 `Fin n` monotone; pair-인덱스(`ℕ`) 캐스팅·base 분리는 별도 leaf.
- [x] (2026-05-31, G2.3) **(6.6) "For all `j`, `θⱼ(1)` is a power of `p`" (mmd L80)** =
      induced-from-`K` の degree datum を 2 層で landing (sorry/axiom 無 — 各 `#assert_only_allowed_axioms`
      = 3 axiom 全 allowlist, no `sorryAx`; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑).
  - **`IsIrreducibleCharacter.exists_charValue_one_eq_prime_pow_of_isPGroup`** (`ZIrr.lean`, RT 一般形):
    `[Finite G]`, `[Fact p.Prime]`, `IsPGroup p G`, `IsIrreducibleCharacter φ` ⟹ `∃ k, φ 1 = (p^k : ℂ)`。
    既存 `exists_natDegree_charValue_one_dvd_card` (`φ 1 ∣ |G|` のみ) を、より鋭い prime-power 事実
    `exists_finrank_eq_prime_pow_of_isPGroup` (証言表現の `dim V = p^k`) + `char_one` (`φ 1 = dim V`)
    で精密化。
  - **`exists_characterDegree_eq_prime_pow_of_isPGroup`** (`S03_PreliminaryCharacter.lean`, Peterfalvi
    consumer 形): `IrreducibleCharacter G` subtype + `characterDegree` 経由で `∃ k, characterDegree χ = (p^k:ℂ)`。
    `characterDegree_def` (= `χ 1`) rewrite で RT 形を bundled-character/`characterDegree` API に橋渡し
    (既存 `exists_natDegree_characterDegree_dvd_card` と同じ二層パターン — predicate→subtype + `φ 1`→`characterDegree`
    の convention 適応)。
  - **依存 verify**: (6.5.b) "`K/M` は非可換 `p`-群" の `p`-群仮説は本 leaf では `IsPGroup p K` として
    *引数* に取る (honest fully-general; `K` が `p`-群という結論を仮定 posit せず、それを供給する (6.5) は
    別 leaf)。消費した landed lemma = `exists_finrank_eq_prime_pow_of_isPGroup` (`ClassSumAlgebra.lean:1564`,
    既に AxiomsCheck 登録済) — 確認済みで存在。
  - **caller 측 残 (G2.3 以後)**: (6.6) 本文の "`θᵢ(1)² ∣ ∑_{j≥i} χⱼ(1)²`" は本 leaf の p-power 事実
    + `sq_dvd_of_factored_coprime`/`two_mul_lt_sq_of_primePow_gap` (Round 15 landed) を `K=p群` setup で
    instantiate して得る (degree-sort `exists_monotoneDegreeEnum` [G2.1] と接続)。
- [x] (2026-05-31, G2.2) **(6.6) `Z ⊄ Ker χ` 判定が要する induced-character kernel + constituent
      infrastructure** を 3 file に landing (sorry/axiom 無 — 各 `#assert_only_allowed_axioms` = 3 axiom
      全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑). Round-16 G2.2 honest-revert
      で欠落と判明した「`Ind_K^L θ` の核」「constituent ⟺ LiesOver」「lies-over 存在」を foundational
      primitive として実装 (case-B L3.1 も同部品を再利用):
  - **(A) Peterfalvi (1.6.a) forward** — `Ind_H^G θ` の核 (mmd 04.3 L73-77):
    - **`ClassFunction.induce_apply_of_mem_normal_of_const`** (`InducedCharacter.lean`, RT 一般形, 任意
      `CommRing k`): `A ⊴ G`, `A ≤ H`, `θ` が `A` 上一定 `= c` ⟹ `a ∈ A` で `Ind_H^G θ(a) = |G|·c·|H|⁻¹`。
      正規性で全共役 `x⁻¹ a x ∈ A ≤ H` ⟹ 誘導和の filter が `G` 全体, 各項 `= c` (補助
      `induceTerm_of_mem_normal`)。これが (1.6.a) の計算的心臓。
    - **`Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf`** (`S03_PreliminaryCharacter.lean`):
      `(A.subgroupOf H : Set ↥H) ⊆ characterKernel θ` ⟹ `(A:Set G) ⊆ characterKernel (Ind_H^G θ)`。
      forward 半分 (`A ⊆ Ker θ ⟹ A ⊆ Ker Ind θ`)。(6.6) は **対偶** `Z ⊄ Ker (Ind θ) ⟹ Z ⊄ Ker θ` を消費。
      **逆方向** ((1.6.a) converse) は [Is] *Character Theory* Lemma 2.21 (genuine character の固有値論法)
      で本 round では未形式化 (repo の value-based `characterKernel` には表現核の固有値機構が無い)。
  - **(B) constituent ⟺ LiesOver bridge** — `inner_induce_ne_zero_iff_liesOver`
    (`Clifford.lean`, `IrreducibleCharacter` namespace, `[Fintype G] [Invertible (Nat.card G:ℂ)]`):
    `⟨Ind_H^G θ, χ⟩ ≠ 0 ↔ LiesOver H χ θ`。numerical Frobenius reciprocity
    (`inner_induce_eq_inner_restrict`) を `LiesOver` 言語に packaging — constituent multiplicity
    `⟨θ, Res χ⟩` = restriction multiplicity `⟨Res χ, θ⟩` の共役 (`inner_conj_symm` + `star_ne_zero`)。
    (6.6) が「χ は `Ind_K^L θ` の constituent」と「χ lies over θ」を往復する橋。
  - **(C) lies-over existence** — `IrreducibleCharacter.exists_liesOver` (`Clifford.lean`, `[Finite G]`):
    任意 `χ ∈ Irr G` は **ある** `θ ∈ Irr H` の上にある。`Res^G_H χ ≠ 0` (値 `χ(1)>0` at `1`,
    `exists_natDegree_charValue_one_dvd_card`) ⟹ 全 irreducible と直交不可
    (`classFunction_eq_zero_of_orthogonal`)。正規性不要。case-B `X`-characterization が消費。
  - **honest 判定**: (A)-forward/(B)/(C) は完全 unconditional・fully-general。posited 仮説無し。
    唯一 (1.6.a) converse のみ [Is] 2.21 (deep) で未着 ⟹ (6.6) は forward 対偶のみ使うため G2.2 の
    `Z ⊄ Ker θ` step には十分。
  - **caller 측 残 (G2.2 以後)**: (6.6) で `X = S − S(Z)` が conj-閉 (= G2.0 caller 残) を出すには
    `S(Z) := {χ ∈ S | Z ⊆ Ker χ}` の conj-閉性が要り, それは本 leaf の `subsetCharacterKernel_induce_of_subgroupOf`
    対偶 + constituent bridge で「χ ∈ S(Z) ⟺ χ が `Ind θ` (θ∈Irr(K) with Z⊆Ker θ) の constituent」を
    回す setup-specific character theory (別 leaf)。
- [x] (2026-05-31, G2.2 assembly) **(6.6) `X`-characterization の honest 2 brick** を上記 R17 infra
      (commit b45164f) から組み上げて `S03_PreliminaryCharacter.lean` に landing (sorry/axiom 無 —
      `#print axioms` 両者 = `{propext, Classical.choice, Quot.sound}`; AxiomsCheck 登録 2 件 各 3 axiom
      全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3352/3335 jobs). (6.6) mmd 04.8
      L76「Let `χ∈Irr L` be such that `Z⊄Ker χ`. There is a character `θ∈Irr K` for which `χ` is an
      irreducible component of `Ind_K^L θ`; by (1.6), `Z⊄Ker θ`」の **R17 で消化可能な正直部分**:
  - **`not_subsetCharacterKernel_of_not_induce`** (= (1.6.a) **対偶**, `InducedKernel` section):
    `A ⊴ G`, `A ≤ H` で `Z ⊄ Ker (Ind_H^G θ) ⟹ Z ⊄ Ker θ` (`(A.subgroupOf H:Set ↥H) ⊄ characterKernel θ`)。
    R17 の forward `subsetCharacterKernel_induce_of_subgroupOf` の literal 対偶 (`fun hker => hind (… hker)`)。
    (6.6) が `Z⊄Ker θ` を読み取る step そのもの (= consumer-facing 形)。
  - **`exists_inner_induce_ne_zero`** (= constituent-existence half, 新 `InducedConstituent` section,
    `[Fintype G] [Fintype H] [Invertible (Nat.card G:ℂ)] [Invertible (Nat.card H:ℂ)]`): 任意 `χ∈Irr G` に
    対し **ある** `θ∈Irr H` で `⟨Ind_H^G θ, χ⟩ ≠ 0` (χ は `Ind θ` の constituent)。R17 の
    `exists_liesOver` (χ lies over 何らかの θ) ∘ `inner_induce_ne_zero_iff_liesOver` (lies-over ⟺
    constituent) の合成。**`Z` 不参照の完全 unconditional/fully-general** = "every χ∈Irr L is a
    constituent of some `Ind_K^L θ`" という (6.6)/(1.7)-type の存在 backbone。
  - **honest 判定**: 両者 posited 仮説無し・thin wrapper でない (前者は対偶を consumer 形で固定し
    AxiomsCheck gate, 後者は 2 つの R17 lemma を non-trivial に compose し `IrreducibleCharacter`
    bundled 形へ橋渡し)。
  - **精密残 (G2.2 で R17 を超える唯一の piece)**: (6.6) が `Z⊄Ker χ` から `Z⊄Ker(Ind θ)` を得る
    リンク = **「irreducible constituent χ が ambient character `Ind θ` の核包含を継承する」**
    (`Z ⊆ Ker(Ind θ) ⟹ Z ⊆ Ker χ`)。これは character-value 不等式 `|χ(a)| ≤ χ(1)` + 等号成立条件
    (ρ(a) scalar) の標準論法で, repo には**中心元限定**の Schur 等号 `‖χ(z)‖²=χ(1)²`
    (`SchurCenterBound.lean:108`) しか無く一般 `a` 版が未形式化 ⟹ `needs-infra` (別 leaf/issue 候補:
    "general character-value bound `|χ(a)| ≤ χ(1)` + equality case")。この piece が入れば
    `not_subsetCharacterKernel_of_not_induce` ∘ constituent-inherits-kernel ∘ `exists_inner_induce_ne_zero`
    で (6.6) `X = {χ∈Irr L | Z⊄Ker χ}` の `Z⊄Ker θ` 帰結が完全に閉じる。

- [x] (2026-05-31, G2.5 infra) **Inflation infrastructure ([Isaacs] (2.22)) PASS 1** を新規 leaf module
      `OddOrder/GroupTheory/RepresentationTheory/InflationCharacter.lean` に landing (sorry/axiom 無 —
      4 主定理 `#print axioms` 全 `{propext, Classical.choice, Quot.sound}`; AxiomsCheck 登録 4 件 各
      3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3353/3336 jobs). (6.6)
      G2.5 degree-sum identity `Σ_{j≥i}χⱼ(1)² = |L|−|L:Z|−Σ_{j<i}χⱼ(1)²` の **核 = inflation 対応**
      (`Irr(L/Z) ≃ {χ∈Irr L | Z⊆Ker χ}`, degree 保存) の **injective degree-preserving 半分**を消化:
  - **`Subrepresentation.compHomEquiv`** : surjective `f : H →* G` で
    `Subrepresentation (σ.comp f) ≃o Subrepresentation σ` (台 submodule 上 identity; `σ(f h)`-不変 ⟺
    `σ g`-不変 が `f` 全射で一致)。`ofCompSurjective`/`comapComp` を両 inverse に持つ order iso。
  - **`Representation.isIrreducible_comp_of_surjective`** : `IsIrreducible σ ⟹ IsIrreducible (σ.comp f)`
    (`f` 全射)。`IsIrreducible = IsSimpleOrder (Subrepresentation ·)` を上 order iso で `e.isSimpleOrder`
    transport。**任意全射 hom 一般** (quotient に限らない)。
  - **`IsIrreducibleCharacter.compHom_of_surjective`** (= **最 foundational brick**, hom-general (2.22)):
    `f` 全射, `φ∈Irr G` ⟹ `ClassFunction.compHom f φ ∈ Irr H`。witness `σ` (φ=χ_σ) を `σ.comp f` へ
    precompose (上の irreducibility transfer) し character `χ_σ∘f = compHom f φ` を確認。landed `compHom`
    API 再利用。
  - **`inflate`** : `IrreducibleCharacter (G⧸N) → IrreducibleCharacter G`, `χ̄ ↦ χ̄∘(mk' N)`
    (`mk'_surjective` で irreducibility 供給)。**`inflate_apply_one`** (= **degree 保存**
    `(inflate N χ̄) 1 = χ̄ 1`, `map_one`)。**`subset_characterKernel_inflate`** (`N ⊆ Ker(inflate N χ̄)`;
    `n∈N ⟹ mk' n = 1 ⟹ (inflate N χ̄) n = χ̄ 1 = (inflate N χ̄) 1`)。後二者で image ⊆
    `{χ∈Irr G | N⊆Ker χ}` を確立 = G2.5 が ranging する集合。
  - **honest 判定**: posited 仮説無し・thin wrapper でない (irreducibility transfer は
    `Subrepresentation` order-iso の non-trivial 構成; mathlib の `Representation.ofQuotient` を**使わず**
    任意全射 hom へ一般化したため repo 再利用性が高い)。`characterKernel`/`characterDegree` は
    `OddOrder.Peterfalvi.S03` の既存定義を直接参照 (import `S03_PreliminaryCharacter`)。
  - **精密残 (G2.5 完了に向けた surjectivity/degree-sum 半分)**: (a) inflation **BIJECTION**
    `Irr(G⧸N) ≃ {χ∈Irr G | N⊆Ker χ}` の **surjectivity** = 「`N⊆Ker χ` なる `χ∈Irr G` は `G⧸N` の
    irreducible character から inflate される」。これは `χ` の witness rep `ρ` が `N` 上 trivial ⟹
    `ρ` が `G⧸N` を factor (`Representation.ofQuotient`, mathlib 既存) ⟹ その character が `χ̄` で
    `inflate N χ̄ = χ`。kernel⊆ ⟹ rep-trivial-on-N の橋 (`characterKernel` の値等式 ⟹ `ρ n = id`) が
    要 (Schur/中心限定でなく `n∈N` 一般; `SchurCenterBound` 不足) = `needs-infra`。(b) injectivity
    (`compHom (mk' N)` 単射, `mk'` 全射性から) + (a) で得た全単射 + `Fintype.sum_bijective` +
    landed `sumIrreducibleDegreeSq` (`Σ_{χ∈Irr L}χ(1)²=|L|`) ⟹ `Σ_{χ∈S(Z)}χ(1)²=|L/Z|=|L:Z|` ⟹
    `Σ_X χ(1)²=|L|−|L:Z|` (X=Irr L∖S(Z))。infra (a) が入れば (b) は機械的。
- [x] (2026-05-31, G2.5 infra PASS 2) **Inflation の injective 半分を確定** (同 `InflationCharacter.lean`,
      sorry/axiom 無; AxiomsCheck +2 件 各 3 axiom 全 allowlist; full `lake build OddOrder` 緑 3353 jobs):
  - **`ClassFunction.compHom_injective_of_surjective`** : `f : H →* G` 全射 ⟹ `compHom f` 単射
    (`compHom f φ = compHom f ψ` から `∀h, φ(f h)=ψ(f h)`, `f` 全射で `g=f h` を取り `φ g=ψ g`)。
    任意全射 hom 一般 (quotient に限らず repo 再利用可)。
  - **`inflate_injective`** : `Function.Injective (inflate N)` (上記を `mk'_surjective N` に特殊化し
    `Subtype.ext` で包む)。⇒ `inflate` は **degree 保存 injection** `Irr(G⧸N) ↪ {χ∈Irr G | N⊆Ker χ}`
    として確定 (injection 半分 + `inflate_apply_one` + `subset_characterKernel_inflate`)。
  - **精密残 (G2.5 完了に残る唯一の keystone = surjectivity)**: 全単射の **surjectivity** =
    「`N⊆Ker χ` なる `χ∈Irr G` は `inflate N χ̄` の形」。唯一の欠片は **`χ_ρ(n)=χ_ρ(1) ⟹ ρ n = id`**
    (`n∈N`)。これがあれば `IsTrivial (ρ.comp N.subtype)` ⇒ mathlib `Representation.ofQuotient ρ N`
    (既存, `ofQuotient_coe_apply : ofQuotient ρ N (g) x = ρ g x`) で `ρ̄:Representation ℂ (G⧸N) V`,
    `ρ̄.comp (mk' N)=ρ` ⇒ `compHomEquiv` で `ρ̄` irreducible, `χ̄=ρ̄.character` が `inflate N χ̄=χ` を与える。
    `χ_ρ(n)=dim V ⟹ ρ n = id` の mathlib 経路: `ρ n` は有限位数 ⇒ `(ρ n)^m=1` ⇒ `X^m−1` が零化
    かつ ℂ 上 squarefree ⇒ `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` で diagonalizable,
    固有値は 1 の冪根 (norm 1), `trace=Σλ_i=dim` ⇒ `|Σλ_i|≤Σ|λ_i|=dim` 等号で全 `λ_i=1`,
    semisimple+唯一固有値 1 ⇒ `ρ n=id` (`IsSemisimple.eq_zero_iff_forall_eigenvalue` 系)。
    この diagonalization keystone は数時間規模の独立 leaf = 次 PASS。入れば (b) sum-bijection は機械的。
- [x] (2026-05-31, **DIAGONALIZATION KEYSTONE landed** — G2.2/G2.5 共有 gate) 上で予告した keystone
      を honest + sorry/axiom 無で着地 (各 `#assert_only_allowed_axioms` = 3 axiom 全 allowlist; full
      `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360/3343 jobs)。commit c9723a1 / 89744b4 /
      6512956 / a5bde78:
  - **`RepresentationTheory.rep_eq_id_of_character_eq_one`** (`ClassSumAlgebra.lean`): 予告通りの経路
      ((ρ g)^n=1 ⇒ squarefree `X^n−1` 零化 ⇒ `isSemisimple_of_squarefree_aeval_eq_zero`; trace =
      `charpoly.roots.sum` = 単位円固有値和 = degree = roots.card ⇒ 三角等号
      `all_eq_one_of_norm_eq_one_of_sum_eq_card` (real-part / 非負和論法) で全固有値 = 1; semisimple +
      唯一固有値 1 ⇒ `IsSemisimple.iSup_eigenspace_eq_top` で `eigenspace 1 = ⊤` ⇒ `ρ g − 1 = 0`)。
      `character_isIntegral` の eigenvalue/trace 機構を再利用。
  - **G2.5 surjectivity 完了**: `RepresentationTheory.exists_inflate_eq_of_subset_characterKernel`
      (`InflationCharacter.lean`) — `N ⊆ Ker χ` なる `χ∈Irr G` は `inflate N χ̄` の形。keystone で `ρ` が
      `N` 上自明 ⇒ `Representation.ofQuotient ρ N` で `G⧸N` へ降下 (`σ` 既約は新 reverse lemma
      `isIrreducible_of_isIrreducible_comp_of_surjective`, `compHomEquiv` 逆向き transport) ⇒
      `χ_σ ∘ mk' = χ`。`inflate_injective` と合わせ degree 保存 **全単射**
      `Irr(L/Z) ≃ {χ∈Irr L | Z⊆Ker χ}` 確定 ⇒ G2.5 degree-sum `Σ_{Z⊆Ker χ}χ(1)²=|L/Z|` が機械的に閉じる。
  - **G2.2 needs-infra 完了**: `ClassSumAlgebra.norm_character_le_finrank` (一般 `‖χ(g)‖ ≤ χ(1)`,
      中心限定 Schur の一般化) + `character_eq_one_iff_rep_eq_id` (等号両方向) →
      `S03.norm_irreducibleCharacter_le_natDegree` + `S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq`
      (constituent-inherits-kernel 等号 case: `(∑ mᵢ χᵢ)(g) = (∑ mᵢ χᵢ)(1) ⟹ mᵢ≠0 の χᵢ で g∈Ker χᵢ`)。
      上記「精密残 (G2.2 で R17 を超える唯一の piece)」を閉じる。**残**: ψ=Ind_K^L θ の `∑ mᵢ χᵢ` 分解
      (genuine character = `Irr` 上 ℕ-結合) は別 leaf (G2.2 caller assembly)。
- [x] (2026-05-31, G2.6 WIRING) **(6.6) coherence-of-X 結論 `IsCoherent τ X A` の組立** を
      `S07_Coherence.lean` ((6.6) section の `coherentPairChain` 直後) に landing (sorry/axiom 無 —
      `#print axioms coherentOfPairChainCover` = {propext, Classical.choice, Quot.sound}; AxiomsCheck
      登録 3件 各 3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360/3343 jobs).
      (6.6) 証明の結論 "Repeated use of Theorem (5.6) then shows that X is coherent" (mmd L84) を,
      landed leaves (G2.1 degree-sort, pass-8 `coherentPairChain`, pass-2 gap leaf, G2.5
      `sumInflatedDegreeSq`) の上に honest に組み上げる **wiring 定理**:
  - **`mem_pairUnion`** (membership 특성화): `χ ∈ pairUnion S₀ pair N ↔ χ ∈ S₀ ∨ ∃ j<N, χ ∈ pairSet pair j`.
    `N` induction (`Nat.lt_succ_iff_lt_or_eq` 분기). engine accumulator 의 멤버십 결정.
  - **`pairUnion_eq_of_cover`** (set-decomposition bridge, 본 round 의 핵심 신규 content): `S₀ ⊆ X`,
    각 pair `pairSet pair j ⊆ X` (`j<N`), `X` 가 `S₀`+pairs 로 covered ⟹ `pairUnion S₀ pair N = X`.
    `Set.Subset.antisymm` + `mem_pairUnion`. = degree-monotone enum (`exists_monotoneDegreeEnum`)
    이 `X = S − S(Z)` 를 equal-min-degree prefix `S₀` 와 나머지 conjugate pair 들로 쪼갠 것을
    engine accumulator `pairUnion S₀ pair N` 와 동일시하는 다리.
  - **`coherentOfPairChainCover`** (`noncomputable def`, = G2.6 GOAL `IsCoherent τ X A`): pair-chain
    decomposition data (`pair`, `N`, `hS₀`/`hpairs`/`hcover`) + base coherence `h0 : IsCoherent τ S₀ A`
    ((1.1)+(1.4) prefix) + per-step (5.6) adjoining `hstep` ⟹ `IsCoherent τ X A`. 증명 =
    `pairUnion_eq_of_cover … ▸ coherentPairChain S₀ pair h0 N hstep`. (6.6) 결론 shape 산출.
  - **honest 판정**: thin wrapper 아님 — `coherentPairChain` 은 `IsCoherent (pairUnion S₀ pair N) A`
    만 주고, `coherentOfPairChainCover` 는 set-decomposition bridge (`pairUnion_eq_of_cover`,
    `mem_pairUnion` 위) 를 추가해 **(6.6) 의 실제 결론 `IsCoherent τ X A`** 를 산출. `h0`/`hstep`
    은 (6.6) 증명구조를 정직히 반영하는 *공급* 입력 (base prefix coherence / per-step retarget) 이며
    결과를 posit 하지 않음 — 결론은 chain 으로 **derived**. memory `scaffold-sorry-free-not-done` 에
    비추어, instruction 이 명시적으로 허용한 wiring boundary (ν basis extension G2.7 미완) 까지만 landing.
  - **정밀 잔존 (G2.6 이후, G2.7 = `hstep` 입력 생산)**: `hstep` 의 각 step 은 `retarget_isCoherent`
    1회이며, 그 입력 중 **target characters `{Xᵢ, X̄ᵢ}` (orthonormal in `ℤ[Irr G]`) + image equation
    `(χ − a·χ₁)^τ = X − a·χ₁^{τ₁}` + lattice 직교 `X,X̄ ⊥ τ₁ξ`** 의 *구성* 이 미완 = **G2.7 Dade
    isometry ν basis extension** (Dade context 의 character theory; `coherentPairChain` 의 docstring
    이 "references the current extension `hcoh.extension`, hence given as a function of the running
    witness" 로 명시한 부분). degree 부등식 부분 (`2χᵢ(1)χ₁(1) < ∑_{j<i}χⱼ(1)²`) 은 이미 landed
    (`two_mul_lt_sq_of_primePow_gap` ← G2.5 `sumInflatedDegreeSq` degree-sum). 또한 caller 가
    decomposition data (`pair`/`N`/cover) 를 `exists_monotoneDegreeEnum` enum 과 conjugate-pairing
    에서 *구성* 하는 작업 (conjugate pair `{χᵢ, χ̄ᵢ}` 를 degree-block 안에서 짝짓기) 도 별도 — 본
    wiring 정리는 그 decomposition 을 추상 data 로 받아 engine 에 정직히 흘림.

## 進捗 (2026-05-31, G2.7 調査 + (5.2.d) producer landing)

**調査結論 (honest verdict, Round-20 の roadmap を訂正)**: G2.7 の `hstep` 構成は **Dade
isometry の wiring ではなく genuine 新 infra**。Round-20 roadmap は「FullDadeIsometryData の τ を
`χᵢ−χ̄ᵢ` に適用 → (5.4.b)/(5.5) 分解で Xᵢ を取れる (wiring)」と判定したが, **型レベルで誤り**:

- `IsCoherent`/`retarget_isCoherent`/`CharacterPsiDecomposition`/`OrthonormalCharacterImageFamily`
  は `IntegralCharacterMap L G := ClassFunction L ℂ →ₗ[ℤ] ClassFunction G ℂ` (**全** class function
  上の ℤ-線形写像, `L G` 独立群) で動く。
- `FullDadeIsometryData`/`DadeMap` は `SupportedClassFunctions ℂ A L → ClassFunction G ℂ`
  (**supported 部分加群上のみ**の bare 関数, 線形ですらない, `L : Subgroup G`)。

両者は別型。Dade τ は `Z[S, L^#]` 上の **固定** 写像であり, `hstep` が各 step で要求する **running
`τ₁ = hS₁.extension`** (直前 set `S₁` の coherence 拡張, χᵢ 自身を含む `Z[S₁]` 全体への isometry) は
Dade τ から得られない。mmd 04.8 L156/L166 が "Let τ₁ be **an isometry from Z[Y] to Z[Irr G]** which
coincides with τ on Z[Y, L^#]" と書く通り, この lattice isometry の**存在こそ (5.6)/(6.6) が示す
結論**であって, Dade τ を virtual character に適用して作るものではない (FT では
`dim CF(L) > dim CF(G)` ゆえ大域 isometry は一般に無い)。`CharacterPsiDecomposition` は repo 内に
**constructor が皆無** (consume only), `isometry_difference_pair_structure` (§3 (1.4) keystone) も
**適用例が皆無** — §7 coherence 界面は §3 存在定理から完全に断絶していた。⟹ G2.7 は確かに
「running-τ₁ + lattice basis extension」の新 infra。

**landed brick (`OddOrder/Peterfalvi/S07_Coherence.lean`, sorry-free, axioms 3 個 allowlist)**:
G2.7 への最基礎の一個 = **(5.2.d) `R(χ)` の producer**。§3 (1.4) keystone の最初の実 consumer:

- `characterDifferenceImageOfIsometry` (`noncomputable def`): integral isometry `τ`, non-real
  irreducible `χ` (⟹ `χ ≠ χ̄`), family `{χ, χ̄}` 上の (1.4) 三仮定 (images virtual / vanish at 1 /
  norm-preserving) から **`CharacterDifferenceImage τ χ` を構成** (posit ではない —
  `SignedIrreducibleDifferenceFamily` を `isometry_difference_pair_structure` の `Exists.choose` で
  抽出, `image_eq : τ(χ−χ̄)=ε•(μ−ν)` を index-1 family 方程式 `τ(χ̄−χ)=ε•(μ₁−μ₀)` から導出)。これまで
  `CharacterDifferenceImage` は constructor 無しで全 §7 補題が仮定取りしていた欠落を埋める。
  `toOrthonormalImage` がこれを `OrthonormalCharacterImageFamily` (orthonormal `R(χ)`) に持ち上げる。
- `conjIrreducibleCharacter`/`conjPairFamily`/`coe_conjIrreducibleCharacter`: `χ̄` と family `{χ,χ̄}`
  の packaging helper。
- `irreducibleCharacter_conj_apply_one`: `χ̄(1)=χ(1)` (指標の 1 での値は自然数=実 ⟹ 共役不変,
  `exists_natDegree_charValue_one_dvd_card`)。(1.4) の equal-degree 仮定 discharge。

**残存 (G2.7 本体, 不変)**: running `τ₁` の構成と, それを使った per-step
`CharacterPsiDecomposition` の **構成** ((5.5) で `Xᵢ=∑_{E}α`), さらに `{Xᵢ,X̄ᵢ}` orthonormal pair
+ image equation `(χᵢ−aᵢχ₁)^τ=Xᵢ−aᵢχ₁^{τ₁}` + lattice 직교 `Xᵢ,X̄ᵢ⊥τ₁ξ`。本 brick はこの連鎖の
入口 (`τ`-image → signed irreducible difference → orthonormal `R(χ)`) を供給する。次段は (a) running
`τ₁` を `coherentPairChain` の各 step witness から取り出す配線, (b) `R(χ)` を使った
`CharacterPsiDecomposition` constructor。

- [x] (2026-05-31, G2.7 PASS 2) **(5.6.3) target pair `{X, X̄}` を (5.5) decomposition から構成** を
      `S07_Coherence.lean` に landing (sorry/axiom 無 — `#print axioms` 両者 =
      `{propext, Classical.choice, Quot.sound}`; AxiomsCheck 登録 2 件 各 3 axiom 全 allowlist; full
      `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360/3343 jobs; commit c6df07e). PASS 1 で genuine
      新 infra と判定した G2.7 の **source-independent な部分** = `retarget_isCoherent` の `{X, X̄}` block
      を `CharacterPsiDecomposition τ χ 0` から **構成** (posit 無) し, **Round-20 roadmap の「Gram–Schmidt
      / free-module basis-extension 欠落」判定を反証**:
  - **`CharacterPsiDecomposition.RetargetTargetPair`** (structure) + **`.retargetTargetPair`** (producer):
    irreducible `χ` (`‖χ‖²=1`) の (5.5) 分解 `D` と source-pair orthonormality (`⟨χ,χ⟩=1`,
    `⟨χ̄,χ̄⟩=1`, `⟨χ,χ̄⟩=0`, `⟨χ̄,χ⟩=0`) から `X := D.X`, `X̄ := D.X − (χ−χ̄)^τ` の orthonormal pair を
    構成。**rescaling/Gram–Schmidt 不要**: (5.5) `eq_sum_of_psi_eq_zero` が `X = ∑_{E}α`, `|E|=‖χ‖²=1`
    を与え (X = 単一 R(χ) 元 ⟹ `‖X‖²=|E|=1`); `|R(χ)| = ‖(χ−χ̄)^τ‖² = ‖χ−χ̄‖² = 2` (image_eq +
    `inner_self_sum_orthonormal_eq_card`; `(χ−χ̄)^τ = (χ−χ̄)^{τ₁}` は `tau1_agrees`, `tau1_isometry` で
    `‖·‖²` 保存; orthonormal `{χ,χ̄}` で `‖χ−χ̄‖²=2`) ⟹ `‖X̄‖²=|R(χ)|−|E|=2−1=1`
    (`inner_self_conjImage_eq_card_sdiff`); `⟨X,X̄⟩=0` (`inner_X_conjImage_eq_zero`); 両者 ∈ `ℤ[Irr G]`
    (`Submodule.sum_mem` over R(χ) ⊆ ZIrr)。**irreducible χ では target pair は FORCED** = roadmap の
    "missing orthonormalization primitive" は不要 (`|E|=1` ゆえ単一元, scaling 自明)。
  - **`retarget_isCoherent_of_decomposition`** (`noncomputable def`): per-step (5.6.3) assembly で
    `{X, X̄}` を data として取らず `D` から `retargetTargetPair` 経由で構成し `retarget_isCoherent` に投入
    ⟹ `IsCoherent (S₁ ∪ {χ, χ̄}) A`。これにより `retarget_isCoherent` の残仮説のうち **running
    `τ₁ = hS₁.extension` に genuine に結合する 2 つ** だけを explicit residual として分離: (i) (5.2.e)
    cross-orthogonality `D.X, X̄ ⊥ τ₁ ξ` (`hX_ortho`/`hXbar_ortho`), (ii) (5.6.2) image equation
    `(χ−aχ₁)^τ = D.X − a·τ₁χ₁` (`himg`)。orthonormality + virtual-character membership は全て `D` 由来。
  - **honest 判定**: thin wrapper でない — `RetargetTargetPair` producer は (5.5)/(5.6.3) の既存 norm 計算
    (`inner_self_conjImage_eq_card_sdiff`/`inner_X_conjImage_eq_zero`/`eq_sum_of_psi_eq_zero`) を
    **irreducible 仮定で閉じた orthonormal pair に組み上げる** non-trivial 合成 (`|R(χ)|=2` の導出が核);
    assembly def は `{X,X̄}` を posit せず `D` から構成。scaffolding 無し (D は consume, 結論は derived)。
  - **精密残 (G2.7 本体, PASS 2 以後)**: 真に残るのは **running `τ₁` 結合の 2 piece** のみ —
    (a) `CharacterPsiDecomposition τ χ 0` instance の **構成** (auxiliary isometry `tau1` が `χ−χ̄` 上で
    running τ と一致, かつ (5.5) を満たす `X`/`Y` を持つ); これは §3 (1.4) keystone
    `isometry_difference_pair_structure` + running coherence extension からの組立を要する。
    (b) `hX_ortho`/`himg` の per-step 放電 (= R(χ) ⊥ τ₁(S₁) cross-family orthogonality と image eq の
    running-τ₁ 一致)。これらは `coherentPairChain` の各 step witness `hS₁.extension` に本質的に依存し,
    Dade τ (固定写像) からは出ない (PASS 1 型ミスマッチ判定通り)。本 PASS は `{X,X̄}` 構成という
    source-independent layer を消化し, 残 gap を「running-τ₁ + (5.5) instance 構成」に精密化した。

- [x] (2026-05-31, G2.7 PASS 3) **§4 Dade isometry を (5.1) base map `τ` として実体化** (type-bridge)
      を `S04_DadeIsometry.lean` + `S07_Coherence.lean` に landing (sorry/axiom 無, AxiomsCheck 登録
      3 件 全 allowlist; `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360/3343 jobs)。PASS 1/2 で
      「§4 Dade map と §7 `IntegralCharacterMap` は別型」と判定した残 gap のうち **base map `τ` 側の
      bridge を構成**。
  - **mmd 04.7 L3 (5.1) の決定的読解で roadmap Q1 を訂正**: coherence base map `τ` は「Dade isometry
    (supported sublattice 上)」で, Lean `IsCoherent τ S A` は `τ` を `extends_on_supported`
    (`zSupportedSpan S A` 上のみ) で制約し span 外は inspect しない。roadmap の「τ は別 running
    isometry」は `τ`/`extension` の混同 → 正しくは **Q2 (= τ は Dade isometry, supported span 上で
    一致する bridge が必要)**。
  - `Hypothesis.dadeLinearMap` (S04): bare `DadeMap` を `ℂ`-linear `CF(L,A) →ₗ[ℂ] CF(G)` に package
    (`dadeValue α g = α(a)` 評価ゆえ linear)。
  - `dadeIntegralCharacterMap` (S07): `LinearMap.exists_extend` (体 ℂ 上の分裂) で `CF(L) →ₗ[ℂ] CF(G)`
    に延長 → `restrictScalars ℤ` で `IntegralCharacterMap ↥L G`。延長は非標準だが supported span 外は
    無害。
  - `dadeIntegralCharacterMap_apply_of_support`: 定義性質 = supported subspace 上で lift = Dade map。
    (5.6.3) の `τ` on `Z[S,L^#]` を実 §4 isometry から供給。
  - **PASS 3 後の残** (hstep の (5.6.2) image eq): `τ = dadeIntegralCharacterMap` に対し
    `himg : τ(χ−aχ₁) = D.X − a•hS₁.extension χ₁` を組む = (5.6.2) `Y = aχ₁^{τ₁}`。capstone
    `lambda_eq_zero_and_Z_eq_zero` (λ=0∧Z=0) は landed, 残は **(5.6.1) λ-係数分解 `hY` を Dade τ・
    running `τ₁` から導き λ=0,Z=0 代入で `himg`** の assembly (PASS 4+, `D.tau1`↔`hS₁.extension` 結合
    + (5.6.1) cross-difference 計算を要し本質的に hard)。詳細 `notes/peterfalvi/s08_coherence_theorems.md`
    G2.7 PASS 3 節。
- [x] (2026-05-31, G2.7 PASS 4) **(5.6.2) image-equation supplier `himg` を *構成* + end-to-end
      per-step adjoining 組立器** を `S07_Coherence.lean` に landing (sorry/axiom 無, AxiomsCheck 登録
      2 件 全 allowlist; `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑)。PASS 3 後の残 (`himg` の
      *posit せず構成*) を解消 — `peterfalvi_66_coherence_of_X` の `hstep` が Dade-isometry targets から
      放電可能になった。
  - **`image_eq_of_decomposition`** (= (5.6.2) image eq supplier): `retarget_isCoherent` の唯一の
    running-`τ₁`-結合仮説 `himg : τ(χ−aχ₁) = X − a·τ₁χ₁` を, (5.4)/(5.6.1) decomposition
    `D : CharacterPsiDecomposition τ χ (a·χ₁)` と 3 つの honest 入力から構成: `htau1_diff`
    ((5.4) `D.tau1 = τ` on supported difference `χ−aχ₁`), `hY` ((5.6.2) `D.Y = a·D.tau1 χ₁`,
    λ=0/Z=0 後), `htau1_chi1` (`D.tau1 χ₁ = hS₁.extension χ₁`)。連鎖
    `τ(χ−aχ₁) = D.tau1(χ−aχ₁) = D.X − D.Y = D.X − a·D.tau1 χ₁ = D.X − a·hS₁.extension χ₁`
    (`D.tau1_image` 経由)。**これが §4↔§7 結合点**: Dade-isometry 側は LHS `τ(χ−aχ₁)` で入る
    (= supported difference の §4 Dade 像; `dadeIntegralCharacterMap_apply_of_support`)。
  - **`retarget_isCoherent_of_decompositions`** (= 完全 per-step adjoining, `himg` 内部放電):
    (6.6)/(6.8) `coherentPairChain` の 1 step `IsCoherent τ S₁ A → IsCoherent τ (S₁∪{χ,χ̄}) A` の
    単一入口。(5.5)/(5.6.1) の 2 decomposition `D₀`/`Da` + 共通 `R(χ)`-射影 `hX_eq : Da.X = D₀.X`
    ((5.6.2) 同定) を取り, orthonormal pair `{D₀.X, X̄}` を `retargetTargetPair` で構成しつつ
    `retarget_isCoherent` の `himg` を `image_eq_of_decomposition` で内部放電。
  - **PASS 4 後の残** (この round 範囲外): (a) 各 step の **decomposition `D₀`/`Da` の生産** (`D.tau1`
    が Dade `τ` と supported diff 上で一致する (5.4) auxiliary isometry の構成); (b) **(5.6.2) `hY` の
    導出** ((5.6.1) λ-係数分解を `lambda_eq_zero_and_Z_eq_zero` に流す cross-difference 計算 — capstone
    自体は landed); (c) `Da.X = D₀.X` の (5.6.2) 同定。これらは wiring でなく (5.4)/(5.6.1) 本体 content。
- [x] (2026-05-31, Round 23 PASS 1) **(5.6.3) 射影同定 `Da.X=D₀.X` (residual c) + (5.5)+(5.2.e)
      image-side orthogonality (residual b) を構成** (commits 32a8c37 / e340467, AxiomsCheck 4 件 新規
      全 allowlist, `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360 jobs)。PASS 4 残 (c) と残 (b) の
      reduction を解消。`retarget_isCoherent_of_decompositions` から **3 つの opaque 仮説**
      (`hX_eq`/`hX_ortho`/`hXbar_ortho`) が消えた:
  - `CharacterPsiDecomposition.X_eq_tau1_chi_of_Y_eq` : (5.6.2) collapse `Da.Y = a·χ₁^{τ₁}` ⟹
    `Da.X = χ^{τ₁}` (tau1 の χ−a·χ₁ 上線形性 map_nsmul + `sub_left_inj`; `a:ℕ`)。
  - `CharacterPsiDecomposition.X_eq_of_tau1_eq_on_chi` : 上 + τ₁-agreement `Da.tau1 χ=D₀.tau1 χ`
    (honest 入力) + `D₀.tau1 χ=D₀.X` ((5.5)) ⟹ `Da.X=D₀.X`。posited `hX_eq` → `htau1_chi` に置換。
  - `CharacterPsiDecomposition.inner_X_eq_zero_of_orthogonal_imageSet` /
    `inner_conjImage_eq_zero_of_orthogonal_imageSet` : per-element `∀α∈R(χ),⟨η,α⟩=0` ⟹
    `⟨η,X⟩=0`/`⟨η,X̄⟩=0`。posited sum-level `hX_ortho`/`hXbar_ortho` → 単一 `hperElem` に置換し内部導出。
  - **残 (次パス)**: posited-conclusion 仮説は `hY : Da.Y=a·Da.tau1 χ₁` ((5.6.2) collapse, (5.6.1)
    form 存在を要する) ただ 1 つ + 各 step `D₀`/`Da` 生産 + `hperElem` の family `{R(χᵢ)}` 結合。
- [x] (2026-05-31, Round 23 PASS 2) **residual (b) image-side coupling `hperElem` を完全構成** (commit
      8c48fe7, AxiomsCheck 4 件 新規 全 allowlist, `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑
      3343 jobs)。PASS 1 残 (b) の「family `{R(χᵢ)}` 結合」を解消 — `hperElem` が
      `retarget_isCoherent_of_decompositions` の最後の image-side opaque 仮説だったが, honest per-member
      (5.5)+(5.2.e) data から **構成** (posit せず) できるようになった。これは mmd L77
      「χᵢ^{τ₁} is orthogonal to R(χ) by (5.5) and (5.2.e)」を members → ℤ[S₁] へ lift したもの:
  - `CharacterPsiDecomposition.inner_X_orthogonal_imageSet_of_orthogonal` : (5.2.e) feed.
    `X = D.X ∈ ℤ[R(χ')]` が, `R(χ')⊥R(χ)` (`D.imageFamily.Orthogonal R₀`) なら 各 `α∈R(χ)` と直交。
    `⟨X,α⟩ = ∑ coeff·⟨β,α⟩ = 0`。`inner_X_eq_zero_of_orthogonal_imageSet` の双対 (左因子が X)。
  - `inner_extension_member_orthogonal_imageSet` : per family member `χ'∈S₁`。その ψ=0 decomposition
    `D'` (⟹ `χ'^{τ₁'}=D'.X` by (5.5)) + `R(χ')⊥R(χ)` (5.2.e) + running agreement
    `D'.tau1 χ'=hS₁.extension χ'` から, running image `χ'^{τ₁}=hS₁.extension χ'` が `R(χ)` と直交。
  - `inner_extension_orthogonal_imageSet_of_members` : span induction で per-member 直交性を
    全 `ξ∈ℤ[S₁]` へ lift (extension の ℤ-線形性 + `⟨·,α⟩` の ℤ-線形性; `mem`/`zero`/`add`/`smul`)。
  - `retarget_isCoherent_of_decompositions_and_memberFamily` : **完全** (5.6.3) per-step adjoining で
    `hperElem` も内部放電。`hperElem` を per-member family `{Dmem, hmemOrtho, hmemTau1}` で置換し
    上 2 lemma で導出。**(5.6.3) の全入力が genuine Dade-map / running-extension fact に帰着** —
    image-side coupling は一切 posit されない。(6.6) `peterfalvi_66_coherence_of_X` の `hstep` が
    Dade isometry の per-member (5.5)+(5.2.e) data から放電可能に。
  - **Round 24 PASS 1 (2026-05-31)**: source-side ① `hY` producer 完了。
    `CharacterPsiDecomposition.Y_eq_nsmul_tau1_of_lambdaForm` が (5.6.1) λ-form
    `D.Y = (a:ℂ)•χ₁^{τ₁} − λ•∑ᵢ(aᵢ/‖χᵢ‖²)•χᵢ^{τ₁} + Z` を capstone pointwise-coeff form に bridge し
    `lambda_eq_zero_and_Z_eq_zero` で λ=0∧Z=0 → 戻して `D.Y = a • D.tau1 χ₁` (= `hY`) を *構成*。
    4 consumer (`X_eq_tau1_chi_of_Y_eq` 他) が消費するのみだった唯一の source-side posited-conclusion を
    除去。sorry/axiom 無, AxiomsCheck 1 件 新規 全 allowlist; build 緑 3360 jobs。
  - **Round 24 PASS 2 (2026-05-31)**: source-side ② のうち projection infra 完了。
    `ClassFunction.exists_intProjection_of_orthonormal_ZIrr` (整数係数直交射影: φ∈ZIrr + ZIrr-正規直交族
    R → 整数 c α=⟨φ,α⟩ + 残差 Y⊥R) + `CharacterPsiDecomposition.ofProjection` (smart constructor:
    hard 6 fields を `(χ−ψ)^{τ₁}∈ZIrr G` から projection で *計算* 供給; 残 input = structural data
    のみ)。D₀/Da 生産を 2 primitive に縮約。sorry/axiom 無, AxiomsCheck 2 件 新規 全 allowlist; 緑 3360 jobs。
  - **Round 24 PASS 2 (final) (2026-05-31)**: source-side ② の per-step D₀/Da *生産パッケージ* 完了。
    `CharacterPsiDecomposition.decompositionPair` — *同一* shared `(R(χ), τ₁, isom, agrees)` + 2 つの
    `ZIrr`-membership `(χ−0)^{τ₁}, (χ−a·χ₁)^{τ₁} ∈ ℤ[Irr G]` から `ofProjection` を 2 回呼び D₀ (ψ=0) と
    Da (ψ=a·χ₁) を *同時* 生産。両者の `.tau1` field が同一 `tau1` ゆえ τ₁-agreement
    `Da.tau1 χ = D₀.tau1 χ` が **構造的** (`decompositionPair_tau1_agree`, `rfl`)。
    `retarget_isCoherent_of_sharedDecomposition` — (5.6.3) per-step coherence entry point: shared
    isometry data を取り pair を内部生産, `htau1_chi` を構造的放電。`a·χ₁` 直交性は bare χ⊥χ₁/χ̄⊥χ₁ から
    nsmul で導出。sorry/axiom 無, AxiomsCheck 3 件 新規 全 allowlist; 緑 3360 jobs (commit f8bb55e)。
    これで「ad-hoc な 2 decomposition を供給し τ₁ 共有を *主張*」する per-step 義務を除去。
  - **残 (次パス) — 精密化した唯一の真の残**: (6.6) hstep の *完全放電* は **global-vs-lattice isometry
    mismatch** で blocked。`CharacterPsiDecomposition.tau1_isometry` は *global* `IsIntegralIsometry tau1`
    (= `∀ φ ψ, ⟨τ₁φ,τ₁ψ⟩=⟨φ,ψ⟩` on ALL of CF(L)) を要求するが、(a) Dade 等距 (`FullDadeIsometryData`/
    `IsDadeIsometry`) は **supported subspace `CF(L,A)` 上のみ** isometric、(b) FT では
    `dim CF(L) > dim CF(G)` ゆえ **global isometry は一般に存在しない** (`IsCoherent` docstring L1023 が
    明言、だから `IsCoherent` は lattice-relative `extension_inner_eq` を採用)。よって roadmap の
    「② τ₁ 2D Gram–Schmidt 拡張」は *global* 版としては **構成不能** (statement 自体が FT で false)。
    真の修正は `tau1_isometry` を `ℤ[χ−ψ, χ−χ̄]` 上の **lattice-relative isometry** に弱める refactor
    (使用は L904/L971/L1838 の 3 箇所のみ、いずれも差分対 `{χ−ψ,χ−χ̄}` 上でしか `inner_eq` を使わない —
    weakening は健全)。ただしこれは `CharacterPsiDecomposition` 構造体 + 3 内部証明 + `ofProjection` +
    `decompositionPair` + `retarget_isIntegralIsometry` (L2023 も *global* τ₁ を要求し global を産出する
    retarget chain 全体) に cascade する大規模・高リスク refactor で、本ラウンド scope 外。
    ① Dade R(χ) 抽出 (`dadeIntegralCharacterMap` → `OrthonormalCharacterImageFamily`) は依然 missing だが
    ②の lattice-relative 化が前提。image-side (b)+(c) は完了済。
  - **Round 25 (2026-05-31) — ②の lattice-relative 化 (前パスの「真の修正」) 完了**: Round-13 で
    `IsCoherent.extension_isometry` に施した lattice-relative 弱化 (pass 5, commit b14a987) と **同一原理**を
    `CharacterPsiDecomposition.tau1_isometry` に適用 (USER 永続承認済)。sorry/axiom 無 —
    `#print axioms` 不変 ({propext, Classical.choice, Quot.sound}); AxiomsCheck 件数不変 (S07 既存 5 件
    `ofProjection`/`decompositionPair`/`decompositionPair_tau1_agree`/`retargetTargetPair`/
    `retarget_isCoherent_of_sharedDecomposition` 全 3 axiom allowlist 内); full `lake build OddOrder`/
    `OddOrder.AxiomsCheck` 緑 3360/3343 jobs。
  - **field 弱化**: 構造体 `CharacterPsiDecomposition` の global `tau1_isometry : IsIntegralIsometry tau1`
    を lattice-relative `tau1_inner_eq_on_support : ∀ φ ζ ∈ zSpan {χ, χ.conj, ψ}, ⟨τ₁ φ, τ₁ ζ⟩ = ⟨φ, ζ⟩`
    に置換。FT では `dim CF(L) > dim CF(G)` ゆえ global 等距は一般不在; Dade 等距/running extension は
    supported sublattice `ℤ[χ, χ̄, ψ]` 上でのみ inner 保存 — それが (5.4.b)/(5.5)/(5.6.2) の全使用 (L904/
    L971/L1838、いずれも `χ−ψ` か `χ−χ̄`、両者 ∈ ℤ[χ, χ̄, ψ]) に充分。
  - **blast radius (実測, 前パス見積りを精密化)**: field アクセスは `.inner_eq` 経由の **3 箇所のみ**
    (`inner_self_chi_eq_sum_coeff` L904 / `inner_self_chi_add_psi_eq` L971 / `retargetTargetPair` 内
    `hχχbar_equiv_card_R` L1838)、構造分解・pattern-match 無。membership cert は新規 helper 2 件
    `chi_sub_conj_mem_zSpan_support` / `chi_sub_psi_mem_zSpan_support` (各 `Submodule.sub_mem` +
    `Submodule.subset_span`、4 行) で供給。**前パスが「大規模 cascade」と見た `retarget_isIntegralIsometry`
    (L2023) は struct field を経由せず standalone global `τ₁` 仮説で動く別系統 ⟹ blast radius 外**
    (global `τ₁` を要求し global retarget を産む chain は本 refactor と独立、不変)。
  - **constructor 供給**: `ofProjection` は入力 `htau1_isom : IsIntegralIsometry tau1` (global) のまま
    保持し、field を `fun φ ζ _ _ => htau1_isom.inner_eq φ ζ` で供給 (global→lattice は健全な特殊化)。
    `decompositionPair`/`retarget_isCoherent_of_sharedDecomposition` の入力も global のまま (変更不要)。
  - **supply-ability (Round-24 (ii) unblock の実体)**: 弱化は **field レベル**のみ ⟹ 構造体に *もはや
    global isometry を要求する field が無い* (唯一だった `tau1_isometry` を除去)。よって将来の per-step
    D₀/Da 生産者が `tau1` を **Dade 等距 + running `IsCoherent.extension`** から組む際 (extension は
    `extension_inner_eq` = lattice-relative inner-eq しか証明せず global 等距は証明し得ない)、
    `tau1_inner_eq_on_support` を直接供給して `CharacterPsiDecomposition` を *手構成* 可能になった
    (`IsCoherent` 自身の構成と完全並行)。これが Round-24 (ii) per-step D production の構造的 unblock。
  - **Round 25 PASS 2 (2026-05-31) — constructor 弱化 + supply-ability 橋 + per-step D 生産者 完了**:
    PASS 1 (commit 8577211) は *field* のみ弱化し constructor `ofProjection`/`decompositionPair`/
    `retarget_isCoherent_of_sharedDecomposition` の入力は global `htau1_isom : IsIntegralIsometry tau1`
    のままだった。だが「Dade 等距から per-step D を組む」には constructor が **lattice-relative 入力を
    受理**せねばならない (Dade 等距は global isometry を *供給し得ない*)。PASS 2 でこれを完了:
    - **constructor cascade**: `ofProjection` / `decompositionPair` / `decompositionPair_tau1_agree` /
      `retarget_isCoherent_of_sharedDecomposition` の `htau1_isom : IsIntegralIsometry tau1` を
      lattice-relative `htau1_inner_eq : ∀ φ ζ ∈ zSpan {χ, χ̄, ψ}, ⟨τ₁ φ, τ₁ ζ⟩ = ⟨φ, ζ⟩` に置換
      (`decompositionPair` は 2 個の `ofProjection` 呼出 `ψ=0`/`ψ=a·χ₁` を共有格子
      `{χ, χ̄, 0, a·χ₁}` 上の 1 つの inner-eq から `Submodule.span_mono` で特殊化)。`rfl` 証明
      (`decompositionPair_tau1_agree`) 不変。外部 caller 0 (`AxiomsCheck` の登録のみ、名前参照で不変)。
    - **supply-ability 橋 (実 Lean、prose でなく)**: `support_subset_of_mem_zSpan_of_supported`
      (supported 生成系の `ℤ[S]` は全 supported — `Submodule.span_le` で
      `supportedSubmodule.restrictScalars ℤ` へ) + `dadeIntegralCharacterMap_inner_eq_on_supported_span`
      (Dade 基底写像 `τ` は supported span 上で inner 保存 — `IsDadeIsometry.inner_eq` (2.6.a) を
      `hyp.dadeIsometryData hconj` 経由で `hyp.dadeMap` に移送、`dadeIsometryData_toDadeMap` rfl)。
      これが **weakened form が Dade 等距から実際に供給される**ことの Lean 証明。
    - **per-step D 生産者 (Round-24 (ii) を閉じる)**: `decompositionPairFromDade` —
      orthonormal `R(χ)` + supported `χ,χ̄,a·χ₁` + 2 つの `ZIrr`-membership から
      `(D₀, Da)` を **(5.1) 基底写像 `τ = dadeIntegralCharacterMap` から直接構成**、欠けていた
      `htau1_inner_eq` を上記橋で *内部放電* (global 等距仮説なし)。これが Round-24 (ii) per-step
      `(D₀, Da)` production の実体。`retarget_isCoherent_of_sharedDecomposition` に直接供給可。
    - sorry/axiom 無; `#assert_only_allowed_axioms` 3 新規 (`support_subset_of_mem_zSpan_of_supported`/
      `dadeIntegralCharacterMap_inner_eq_on_supported_span`/`decompositionPairFromDade`) 全 3 axiom
      allowlist 内; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑。
    - **残**: `decompositionPairFromDade` は (5.4) **基底ケース `τ₁ = τ`** を構成。一般 (5.4) `τ₁ ⊋ τ`
      (running coherence extension への拡張) と `OrthonormalCharacterImageFamily` の Dade `R(χ)` 抽出
      (① 依然 missing) は別パス。だが lattice-relative 化が前提で、その前提は本パスで除去済 —
      per-step `hstep` を `decompositionPairFromDade` + `retarget_isCoherent_of_sharedDecomposition` で
      組む経路が型レベルで開通した。
  - **Round B (2026-05-31) — Dade `R(χ)` extractor + ZIrr-membership 完了 (上記残① を閉じる)**:
    前パス残「`OrthonormalCharacterImageFamily` の Dade `R(χ)` 抽出 (① 依然 missing)」を実装。
    `decompositionPairFromDade` は `imageFamily : OrthonormalCharacterImageFamily τ χ` と 2 つの
    `ZIrr`-membership を **入力** として要求していた; Round B はこれら 3 つを **Dade 等距から構成**:
    - **support-side keystone (S04)**: `Hypothesis.one_notMem_dadeSupport` — `1 ∉ dadeSupport`。
      `1 ∈ dadeSupport ⟹ IsConj (a·h) 1 (a∈A, h∈H(a)) ⟹ a·h=1` (`isConj_one_left`) `⟹ a=h⁻¹∈H(a)`;
      同時に `a∈C_L(a)` (a∈L, 自己可換)、`centralizer_disjoint (H a) (C_L a)` ((2.2)) で
      `a∈H(a)⊓C_L(a)=⊥ ⟹ a=1`、`ne_one` (A⊆G^#) と矛盾。
    - **vanish-at-1 (S07)**: `dadeIntegralCharacterMap_apply_one_eq_zero` — supported φ の Dade 像は
      `dadeSupport` 外で 0 (`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport` via `isDadeMap_dadeMap`)、
      `1 ∉ dadeSupport` ゆえ `(φ^τ)(1)=0`。(1.4) `IsometryDifferenceImagesVanishAtOne` を放電。
    - **virtual-char (S07)**: `dadeIntegralCharacterMap_mem_ZIrr_of_supported` — supported かつ
      `φ∈ℤ[Irr L]` なら `φ^τ∈ℤ[Irr G]` ((2.6.b) `PreservesVirtualCharacters`/`maps_virtualCharacter`、
      `apply_of_support` で `hyp.dadeMap` に移送)。(1.4) `IsometryDifferenceImagesAreVirtual` +
      `htau1_mem0`/`htau1_mema` の双方を放電。
    - **R(χ) extractor**: `dadeOrthonormalCharacterImageFamily hyp hconj χ hreal hχsupp hχbarsupp` —
      χ irreducible 非実 + χ,χ̄ supported から、`conjPairFamily χ=![χ,χ̄]` 上で (1.4) keystone
      `characterDifferenceImageOfIsometry` の 3 仮説を上記で放電し、`toOrthonormalImage` で
      `OrthonormalCharacterImageFamily τ χ` を構成。inner-eq 仮説は差 χ̄−χ, χ−χ が `ℤ[χ,χ̄]` 内ゆえ
      `dadeIntegralCharacterMap_inner_eq_on_supported_span` で供給。
    - **full assembly**: `decompositionPairFromDadeOfIrreducible` — χ irreducible 非実 supported +
      `χ₁∈ℤ[Irr L]` から `R(χ)` も `htau1_mem0`/`htau1_mema` も **内部構成**し `(D₀,Da)` を生産。
      これで per-step `(5.6)` 入力が **opaque 仮説ゼロ**で実 Dade τ から得られる (Round C の
      running τ₁ 一般化を残すのみ; 基底ケース `τ₁=τ` は完全構成)。
    - sorry/axiom 無; `#assert_only_allowed_axioms` 5 新規 (`one_notMem_dadeSupport`/
      `dadeIntegralCharacterMap_apply_one_eq_zero`/`dadeIntegralCharacterMap_mem_ZIrr_of_supported`/
      `dadeOrthonormalCharacterImageFamily`/`decompositionPairFromDadeOfIrreducible`) 全 3 axiom
      allowlist 内; full `lake build OddOrder` 緑 3360 jobs、`OddOrder.AxiomsCheck` 緑。
  - **Round C (2026-05-31) — running-`τ₁` instantiation `retarget_isCoherent_fromDade` 完了**:
    `coherentPairChain` の 1 step `IsCoherent τ S₁ A → IsCoherent τ (S₁∪{χ,χ̄}) A` を **(5.1) 基底写像
    `τ = dadeIntegralCharacterMap` を running 補助等距 `τ₁ = τ` *そのもの* として** DISCHARGE する
    producer。`retarget_isCoherent_of_sharedDecomposition` の 4 つの agreement 義務を **内部放電**:
    - `htau1_agrees : τ(χ−χ̄)=τ(χ−χ̄)` / `htau1_diff : τ(χ−a·χ₁)=τ(χ−a·χ₁)` — 共に `rfl`
      (decomposition の `tau1` field が `τ` そのもの)。
    - `htau1_chi1 : τ χ₁ = hS₁.extension χ₁` / per-member `hmemTau1 : (Dmem x).tau1 x = hS₁.extension x`
      — `IsCoherent.extends_on_supported` から: running extension は **supported sublattice
      `Z[S₁,A]` 上で 基底 `τ` と一致**、χ₁ も全 member `x∈S₁` も supported (`hchi1supp`/`hmemSupp`)
      ゆえ `(Dmem x).tau1 x = τ x = hS₁.extension x`。これが「running extension への一般化」の核心。
    - `R(χ)` + 2 `ZIrr` facts = Round B (`dadeOrthonormalCharacterImageFamily`/
      `dadeIntegralCharacterMap_mem_ZIrr_of_supported`); `htau1_inner_eq` =
      `dadeIntegralCharacterMap_inner_eq_on_supported_span`。
    - **残 input** = 真正 (6.6) 文字次数内容 (Dade 等距の責務外、(6.6) enumeration が供給):
      (5.6.2) collapse `hY`、per-member (5.2.e) image-orthogonality `hmemOrtho`、source
      orthogonalities `hχ_S1`/`hχbar_S1`/`hχχbar`、generation `hgen`。各 per-member decomposition
      `Dmem x` も Dade 等距から生産 (`decompositionPairFromDadeOfIrreducible … .1`、`.tau1=τ` を
      `hmemTau1Base` で保証)。
    - これで **opaque な補助等距 agreement 仮説なしに** `coherentPairChain` step が 実 Dade τ +
      前段 coherence から DISCHARGE される。B+C 合わせて per-step `hstep` の Dade-isometry 由来部分
      (`τ₁` 構成・R(χ)・ZIrr・agreement) が全構成、(6.6) 由来の文字次数部分のみが supplied として残る。
    - sorry/axiom 無; `#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.retarget_isCoherent_fromDade`
      3 axiom allowlist 内; full `lake build OddOrder` 緑 3360 jobs、`OddOrder.AxiomsCheck` 緑。
    - **`peterfalvi_66_coherence_of_X` 完全 instantiate の到達性 (正直評価)**: `hstep` から opaque
      補助等距 agreement は除去済 (Round C)。ただし `peterfalvi_66_coherence_of_X` の `hstep` を
      *完全に* 埋めるには各 step の `hY`/`hmemOrtho`/次数比/`hgen` (= (6.6) 列挙・degree 算術) が
      なお必要で、これは Dade 等距の責務外 (roadmap の "Residual (post-instantiation)" と一致)。
      よって本 round では `retarget_isCoherent_fromDade` までを landing し、完全 instantiate は
      (6.6) per-step degree データの threading (別 round) に残す。
  - **Round C assembly (2026-05-31) — instantiated `peterfalvi_66_coherence_of_X_from_dade` 完了**
    (= 上記「完全 instantiate は別 round に残す」を消化): Round C の per-step engine
    `retarget_isCoherent_fromDade` を `coherentPairChain` accumulator 形に組み上げ、(6.6) coherence-of-X
    を **実 Dade 等距 `τ = dadeIntegralCharacterMap` で instantiate**。`hstep` はもはや posit されず
    Dade 等距 + 前段 coherence から **構成**される。3 piece:
    - `pairUnion_succ_eq_union_pair` (汎用 set 橋): `(pair i)=(c₁,c₂)` のとき
      `pairUnion S₀ pair (i+1) = pairUnion S₀ pair i ∪ {c₁,c₂}`。per-step adjoining engine の
      `S₁∪{χ,χ̄}` 結論を `coherentPairChain` accumulator 形に接続。
    - `DadeChainStep hyp hconj S₁ A χ` (構造体): Dade 等距が供給しきった**後に残る真正 (6.6) per-step
      文字次数内容**を field として束ねる残余 interface — `χ₁`/`a`/非実性/supports/orthonormality/
      per-member (5.5)+(5.2.e) family (`Dmem`/`hmemTau1Base`/`hmemSupp`/`hmemOrtho`)/source
      orthogonalities/(5.6.2) collapse `hY`/generation `hgen`。どれも Dade 等距の *image-side* 構造に
      触れない (source-side degree/orthogonality data = (6.6) enumeration の責務)。
      `DadeChainStep.advance` が 1 step を `retarget_isCoherent_fromDade` で放電し
      (R(χ)・ZIrr・inner-preservation・`τ₁=τ` agreement は内部供給)、
      `DadeChainStep.chainStepAdvance` が橋で accumulator 形に書き換え。
    - `peterfalvi_66_coherence_of_X_from_dade` (主定理): 上記を chain 上で fold。残 input は
      enumeration `e`/cover `hcoverIdx`/base coherence `h0`/per-step `hstepData`+`hpairχ` のみ
      (= 真正 (6.6) 文字内容、Dade 等距の責務外)。これで **§5/§6 coherence engine が実 Dade τ に対し
      完全 constructive**: 各 step は 1 つの完全 Dade 由来 (5.6) adjoining。
    - sorry/axiom 無; `#assert_only_allowed_axioms` 4 新規 (`pairUnion_succ_eq_union_pair`/
      `DadeChainStep.advance`/`DadeChainStep.chainStepAdvance`/`peterfalvi_66_coherence_of_X_from_dade`)
      全 3 axiom allowlist 内; full `lake build OddOrder` 緑 3360 jobs、`OddOrder.AxiomsCheck` 緑。
  - **`DadeChainStep` source-side fields 放電 — (5.6.1) existence-half primitive landing + 残余
    精密化 (2026-05-31)**: 目標は `DadeChainStep` の source-side fields (`hY`/`hmemOrtho`/`hgen`) を
    landed pieces で WIRE し、(6.6) coherence-of-X を 真正 (6.6) setup 仮説のみに帰着すること。
    精査の結果、3 fields はいずれも *wiring-size* では放電不能 (roadmap の「clean wiring / pure
    algebra」評価は誤り) で、各々 真正に新規の数学内容を要する。本 round では **最も基礎的かつ
    完全 closable な (5.6.1) existence-half primitive** を landing:
    - `OddOrder.RepresentationTheory.exists_orthogonalProjection_of_orthogonal_family`
      (`OddOrder/GroupTheory/RepresentationTheory/ZIrrFourier.lean`, commit 741e769): 任意の `w` を
      有限 orthogonal family `vᵢ` (実 gram `⟨vᵢ,vⱼ⟩=δᵢⱼmᵢ`, `mᵢ≠0`) 上に射影 —
      `w = ∑ᵢ(⟨w,vᵢ⟩/mᵢ)•vᵢ + Z`, `Z ⊥ vⱼ`。純 diagonal Gram 射影 (completeness 不要)。
      これは (5.6.1) λ-form `Y = a·χ₁^{τ₁} − λ·∑ᵢ(aᵢ/‖χᵢ‖²)·χᵢ^{τ₁} + Z` の **存在半** (step 1)。
      Pythagoras `inner_self_orthogonalSum_add_re` の sibling、AxiomsCheck 登録済、緑。
    - **正直な残余 (各 field がなぜ wiring 不能か)**:
      * `hY` (5.6.2 collapse `Da.Y = a•Da.tau1 chi1`): tautology ではない (roadmap 誤認)。
        `Y_eq_nsmul_tau1_of_lambdaForm` は `hYform` (λ-form) を *消費*するが、その producer が無い。
        producer の core 障害 = **joint-lattice isometry**: 係数計算 (mmd L79)
        `aaᵢ‖χ₁‖² = ((χ−aχ₁)^τ, (χᵢ−aᵢχ₁)^τ)` は `χ−aχ₁` と `χᵢ−aᵢχ₁` を *同時に* 含む格子
        `Z[S₁∪{χ−χ̄,χ−aχ₁}]` 上の等距を要するが、`Da.tau1_inner_eq_on_support` は `{χ,χ̄,ψ}` 上のみ。
        `DadeChainStep` 現 fields はこの joint 等距を供給せず → interface 拡張 (joint 等距 field 追加)
        無しには放電不能。existence-half (上記 primitive) は landing 済だが coefficient-value
        (`λᵢ=λaᵢ/‖χᵢ‖²`) + integrality (`λ∈ℤ`) + joint-等距 transport が残る。
      * `hmemOrtho` (`R(x) ⊥ R(χ)`): `Dmem` は `DadeChainStep` の **field (任意データ)**。任意データの
        image family 直交性は構成法を知らずには証明不能。放電には `Dmem` も Dade 等距から *構成*
        (`decompositionPairFromDade…`) し Dade `R(x) ⊥ R(χ)` を `x⊥{χ,χ̄}` から (4.1)型で導く必要 →
        interface 変更 (Dmem を field でなく構成へ)。
      * `hgen` (生成 `Z[S₁∪{χ,χ̄},A] ⊆ ℤ[Z[S₁,A]∪{χ−χ̄,χ−aχ₁}]`): pure module theory ではない
        (roadmap 誤認)。(4.7) `Z[S,L^#]=Z[S,A]` を要する (χ 単体は A 上 supported とは限らず、
        `mχ+nχ̄` の support 制約が差 generator 経由の関係を強制)。(4.7) は未形式化、`DadeChainStep`
        のデータに無い。
    - 結論: `peterfalvi_66_coherence_of_X` を 真正 (6.6) setup のみへ帰着する milestone は本 round 未到達
      (3 fields とも interface 拡張 + 新規数学を要す)。本 round の純益 = (5.6.1) existence-half
      primitive (汎用・再利用可・λ-form の step 1)。次 step 候補 = (a) `DadeChainStep` に joint-lattice
      isometry field を足し coefficient-value 計算 + integrality を載せ `hY` 放電、(b) (4.7) 形式化で
      `hgen`、(c) `Dmem` の Dade 構成化で `hmemOrtho`。
    - sorry/axiom 無; primitive `#assert_only_allowed_axioms` 3 axiom allowlist 内; full
      `lake build OddOrder` 緑 3360 jobs、`OddOrder.AxiomsCheck` 緑。

## 進捗 (2026-05-31 続き, (5.6.1) λ-form hY を完全放電 — crux 解決)

HANDOFF が指す「次の crux = `DadeChainStep.hY` = (5.6.1) λ-form」を **3 コミットで完全に解決**
(commits `ae6b8e4` / `26c6509` / `968f2c5`、いずれ sorry/axiom 無・AxiomsCheck 登録・full build 緑 3360 jobs)。
posited だった `hY` フィールドが消え、(6.6) coherence-of-X が **image-side の posit を一切持たず**
真正の source-side 文字次数データのみから実 Dade τ で構成されるようになった。

- **`CharacterPsiDecomposition.Y_collapse_of_family`** (S07, 汎用 producer): (5.4) 分解 `Da` +
  source family bundle `B` から (5.6.2) collapse `Da.Y = a·χ₁^{τ₁}` を *構成*。教科書 (5.6.1)/(5.6.2)
  (mmd 04.7 L71-97) をそのまま形式化 — (i) `Y` を直交族 `{χᵢ^{τ₁}}` に射影
  (`exists_orthogonalProjection_of_orthogonal_family`)、(ii) 各 i≠i₁ の係数を cross-orthogonality
  `crossDifference_inner` を等距で transport して単一 λ に同定 (`c i = a·[i=i₁] − λ·aᵢ/‖χᵢ‖²`)、
  (iii) λ∈ℤ を `inner_mem_ZIrr_int` + `‖χ₁‖²∈ℤ` で示し、(iv) `Y_eq_nsmul_tau1_of_lambdaForm`
  (既存 capstone) で λ=0,Z=0 に collapse。**繊細点 (HANDOFF 警告) はクリア**: 係数計算は running
  isometry 像 `χᵢ^{τ₁}` の直交性 (`hiso_fam`) を使い、全 scalar が実 (a,aᵢ,‖χᵢ‖²) ゆえ
  conjugation で破綻しない。
- **`dade_Y_collapse_of_family`** (S07, Dade 特化): 上 producer の全仮説を **Dade 等距 + (5.5)** から
  放電 — `hiso_fam`/`hiso_cross` ← `dadeIntegralCharacterMap_inner_eq_on_supported_span`、`hXortho`
  (R(χ)⊥S₁^{τ₁}) ← 各 member の `(Dmem χᵢ).X` (`eq_sum_of_psi_eq_zero` +
  `inner_X_orthogonal_imageSet_of_orthogonal`、**hS₁ 不要**)、`χ₁^{τ₁}∈ZIrr` ←
  `dadeIntegralCharacterMap_mem_ZIrr_of_supported`、norm 実性/正値 ← `inner_self_eq_realCast` 等。
  `Da.tau1 = τ` な任意 `Da` で動く (hDa_tau1 仮説)。
- **`DadeChainStep` の posited `hY` を除去 → 真正フィールドに置換**: `famS`(S₁ の Finset 列挙)/
  `famS_eq`/`famRatio`/`famRatio_chi1`/`famDegree`/`famDegree_chi`/`famPairwise`/`famNe`/`famSupp`/
  `hdeg_c` (= (5.6) (c))。`advance` が `CharacterFamilyBundle` (ι=CF(L), chiFam=id) を組んで
  `dade_Y_collapse_of_family` で `hY` を *証明*。**memory `scaffold-sorry-free-not-done` の観点**:
  hY は posited から「genuine data から constructible」に転換 — 残るフィールドは全て (6.6) 列挙が
  供給する文字次数・直交性データ (image-side の posit ゼロ)。

**次の crux** = **(6.8) capstone** (`S08_CoherenceTheorems.lean:188` sorry,
`sibleySetup_is_coherent`)。(6.6) coherence-of-X が実 Dade τ で完全 constructive になったので、
残りは mmd 04.8 L150- の H 非可換 p群 case-A/case-B split を `coherentUnion_of_glued` で結合し、
SibleySetup の data を per-step `DadeChainStep` stream に wire する組立 (別 issue 級の大物)。
その後 S09:1589 ((7.10) `card_G0_lower_bound`)。

## 進捗 (2026-05-31 続き, 等次数 coherence primitive `coherentEqualDegree[_fromDade]`)

**前回 HANDOFF item #1「Y-coherence」の正体を訂正して landing** (commits `dd1b2b9` / `8e8fd93`、
sorry/axiom 無 `{propext, Classical.choice, Quot.sound}`、AxiomsCheck 4 件登録、full
`lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360 jobs)。

**訂正**: 前回 HANDOFF は Y-coherence を「`DadeChainStep.advance` を degree-ratio=1 で反復 (wiring)」と
書いたが**誤り**。(5.6) per-step の次数不等式 `hdeg_c: 2a < ∑ aᵢ²/‖χᵢ‖²` は等次数 (a=1, ‖χᵢ‖²=1) で
`2 < |famS|` を要し、**2 番目の対を足す時点 (|S₁|=2) で偽**。教科書 (mmd 04.8 L156, 04.3 (1.4)) も Y を
**「By (1.1) and (1.4)」直接**で coherent と言う — (5.6) 反復ではない。等次数 coherence は (1.4) 由来の
**独立 primitive** で、(6.6) の base prefix `{χ₁,…,χ_k}` (等最小次数) も同じ primitive。

- **`coherentEqualDegree`** (S07, 抽象 core): 直交等次数族 `χ : Fin n → CF(L)` (n≥2, 値 d≠0 at 1∉A,
  差 χⱼ−χ₀ が A 上 supported) + 直交 target `X : Fin n → CF(G)` + (1.4) image eq `τ(χⱼ−χ₀)=Xⱼ−X₀`
  ⟹ `IsCoherent τ (range χ) A`。拡張は **Fourier-image map** `ν φ = ∑ⱼ⟨φ,χⱼ⟩•Xⱼ` (`coherentImageMap`)。
  **`retarget` の τ₁-residual 項は不要** — `ℤ[range χ]` 上で residual が消え、`extension_inner_eq` は
  純 Parseval (`coherentImageMap_inner_eq`)、τ は `extends_on_supported` でのみ効く (差生成子
  `zSupportedSpan_range_subset_span_sub_zero` = n 元版 `zSupportedSpan_pair_subset_span`)。
  補助: `classFunction_sum_apply`/`coherentImageMap_apply[_eq]`/`eq_sum_inner_smul_of_mem_span`
  (Fourier 展開)/`inner_eq_sum_inner_mul_conj` (Parseval)。import `LinearAlgebra.Finsupp.LinearCombination`
  追加 (`Submodule.mem_span_range_iff_exists_fun`、R 明示引数)。
- **`coherentEqualDegree_fromDade`** (S07, Dade 特化): τ=実 Dade `dadeIntegralCharacterMap`。(1.4)
  `isometry_difference_pair_structure` を τ に適用し signed family `{μⱼ,ε}` を**構成** (3 仮説を
  `dadeOrthonormalCharacterImageFamily` と同様 Dade 等距で放電)、target `Xⱼ=ε•μⱼ` (直交,
  `classFunction_inner_eq_if`+`sign_mul_self` で ε²=1)、image eq `τ(χⱼ−χ₀)=ε•(μⱼ−μ₀)` から
  `coherentEqualDegree` で組立。**opaque 仮説ゼロ** — 入力は genuine な等次数 + supports のみ。
  `Exists.choose` 抽出 (結論は Type)。

これで **(6.6) chain の `h0` (等最小次数 prefix) と (6.8) `Y=S(H')` の両方が実 Dade τ で直接構成可能**に
なった (前者は `coherentPair_fromDade` の n=2 を任意 n に一般化、後者は新規)。

**精密残 (次)**: (a) (6.6)/(6.8) で `coherentEqualDegree_fromDade` を実際に呼ぶには **§8 setup 由来の
等次数族の構成** が要る — (6.8) Y は「η_j(1)=|W₁| for all j」を (c)+(1.6)+[Is]Thm 6.34 から出す
setup-specific character theory、(6.6) prefix は degree-sort `exists_monotoneDegreeEnum` の
等最小次数ブロック抽出。これらは未形式化 (posit すると scaffolding)。(b) capstone 本体
(case A/B + (6.5)/(6.7) + τ₃-gluing `coherentUnion_of_glued` + (6.8.3))。

**追加 landed (同セッション, commit `f60d1c1`)**: G2.5 degree-sum の **complement** `sumNonInflatedDegreeSq`
(`InflationCharacter.lean`, sorry/axiom 無, AxiomsCheck 登録): `∑_{χ∈Irr G, N⊄Ker χ} χ(1)² =
|G|−|G⧸N|` = landed `sumInflatedDegreeSq` (`∑_{N⊆Ker} = |G⧸N|`) の Burnside `sumIrreducibleDegreeSq`
(`∑_{Irr} = |G|`) 内補集合 (`Finset.sum_filter_add_sum_filter_not` + `linear_combination`)。N=Z で
**(6.6)/(6.8) の X=S−S(Z) total `∑_{χ∈X}χ(1)² = |L|−|L:Z|`** (mmd 04.8 L78/L234) = (6.6) per-step
square-divisibility (`∑_{j<i} = |L|−|L:Z| − ∑_{j≥i}`) と (6.8.3) final inequality の入力。
issue notes 627-628 の「infra が入れば 機械的」を消化。**残**: (6.6) は enum split (∑_{j<i}/∑_{j≥i})、
(6.8.3) は `|L|−|L:Z|=|W₁||H:Z|(|Z|−1)` 群位数算術 (L=H⋊W₁ setup) — どちらも setup-specific。
ℂ→ℕ companion (`∑(natDegree)²=card G−card(G⧸N)`) は (6.6) ℕ-divisibility 用に将来有用だが未着。

## 進捗 (2026-05-31, worktree `gracious-hermann` — degree-sum leaf + 6.34 frontier 確定)

別 worktree (`claude/gracious-hermann-78e4d8`) で (6.8) capstone 攻略開始。worktree セットアップ
(symlink `.lake/packages`/`references`、`.lake/build` は独立) 後 baseline green 確認 (3373 jobs)。

### ✅ landed: (6.8.3) degree-sum factored form (commit `78e7561`)
`OddOrder/GroupTheory/RepresentationTheory/InflationCharacter.lean` に
**`sumNonInflatedDegreeSq_eq_index_mul`** : `N ⊴ G`, `N ≤ K ≤ G` で
`∑_{χ∈Irr G, N⊄ker χ}χ(1)² = [G:K]·[K:N]·(|N|−1)`。landed `sumNonInflatedDegreeSq` (`=|G|−|G⧸N|`)
+ Lagrange index 算術 (`index_mul_card`/`relIndex_mul_index`/`index_eq_card`) を cast→`linear_combination`
で合成。= mmd 04.8 L234 の `∑_{χ∈X}χ(1)²/‖χ‖²=|W₁||H:Z|(|Z|−1)` ((6.8.3) 最終不等式の degree-sum、
`G=L`/`K=H` (⇒[G:K]=|W₁|)/`N=Z`)。sorry/axiom 無 (`{propext, Classical.choice, Quot.sound}`)、
AxiomsCheck 登録、full build green。**Burnside-on-L 経由ゆえ Peterfalvi の `Ind_H^L`-orbit counting
不要の clean・coherence-setup-free identity**、§10–§16 degree counting でも再利用可。

### (6.8) frontier 確定マッピング — 残り = 3 つの未形式化 character-theory prerequisite
coherence ENGINE は完成済 (`coherentUnion_of_glued` (S07:3468) の入力 = `hX`/`hY`/glued `ν`/
source・image 直交/`hgen`)。これらを供給する character theory が残:
1. **[Is]Thm 6.34** (Frobenius/Dade induced irreducibility): `θ∈Irr H, θ≠1 ⟹ Ind_H^L θ∈Irr L,
   degree=|W₁|θ(1)`。**η_j(1)=|W₁| と X⊂Irr L の両方を供給 (case-A/B 共通) = 最高レバレッジ**。repo 未実装。
2. **Peterfalvi (1.9)** Galois action on Irr + **(5.9.a)** Galois-coherence invariance ((6.8.2.1) 用)。未実装。
3. **(6.8.1)/(6.8.2.1-3) の計算** (b≡c≡0 mod a congruence chain, (6.7) 適用, regular char formula)。

(NB: tractable-but-small な (6.8.3) final 算術 `4|W₁|²>[H:Z](|Z|−1)²` は単独 pre-landing せず —
case-A/B fixed-point-free order bounds (Hyp 4.6 構造、本層未露出) と合流時に hypotheses を正確化して
inline 化する方が honest。`d²≤[H:Z]` = `SchurCenterBound.exists_degree_sq_le_index` は済。)

### 🎯 次の major target = [Is]Thm 6.34 (Mackey-first, multi-session)
依存確認済: Frobenius 相互律 `inner_induce_eq_inner_restrict` (InducedCharacter:482)✅、inertia group
(Inertia:162)✅、Brauer permutation lemma unconditional (`brauer_permutation_lemma'`)✅、per-element
共役値 `induceTerm_of_mem_normal` (InducedCharacter:517)✅、conjBy (Inertia:57, 規約 `conjBy g θ h=θ(ghg⁻¹)`)✅。
**欠落の核 = Mackey 制限公式** (repo/mathlib に ready-made の coset-sum 無)。build chain (各 sorry-free leaf):
- **(i) Mackey 制限** `Res_H(Ind_H^L θ)=∑_{w∈transversal} conjBy w⁻¹ θ` (H⊴L)。導出:
  `(Ind θ)(g)=⅟|H|∑_{x∈L}θ(x⁻¹gx)` (`induceTerm_of_mem_normal` A=H) `=⅟|H|∑_x(conjBy x⁻¹ θ)(g)`、
  `x=h'·w` 分解で `conjBy x⁻¹ θ=conjBy w⁻¹(conjBy h'⁻¹ θ)=conjBy w⁻¹ θ` (h'∈H で conjBy 自明、
  `θ.conj_eq` 5行 inline) ⟹ `=∑_w(conjBy w⁻¹ θ)(g)`。coset-sum は `Subgroup.groupEquivQuotientProdSubgroup`
  /`IsComplement`。~60-100 LOC、最も重い brick。
- **(ii) norm 公式** `‖Ind θ‖²=|I_L(θ):H|`: `inner_induce_eq_inner_restrict` + (i) + `⟨θ,θ^w⟩=δ`。
- **(iii) Frobenius 既約性** θ≠1 ⟹ `I_L(θ)=H` (Brauer: W₁ が Irr(H)∖{1} に自由作用 ← classes∖{1} 自由)
  ⟹ `‖Ind θ‖²=1`+genuine ⟹ `Ind θ∈Irr L`。
- **(iv) degree** `(Ind θ)(1)=|W₁|θ(1)` (`induce` の 1 評価 + [L:H]=|W₁|)。
配置案: 新 `OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean` (Frobenius char theory の家)。

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

---

## 🔁 HANDOFF (2026-05-31 更新, 別セッション引き継ぎ) — branch `claude/naughty-nash-c3ffc7` @ `968f2c5`

**状態**: build green (`lake build OddOrder OddOrder.AxiomsCheck`、3360 jobs)、tree clean。実 sorry は 2 個のみ:
`S08_CoherenceTheorems.lean:188` (`sibleySetup_is_coherent` = (6.8))、`S09_NonexistenceCertain.lean:1589` ((7.10))。

**⚡ 前回 HANDOFF の crux「(5.6.1) λ-form hY」は解決済** (commits ae6b8e4/26c6509/968f2c5、上記 進捗節参照)。
posited `hY` フィールドは `DadeChainStep` から除去され、真正 (6.6) family data から `advance` 内で証明される。
(6.6) coherence-of-X が実 Dade τ で image-side posit ゼロの完全 constructive に到達。**次の crux は (6.8) capstone**。

### ここまでに構成済み (§4-§6 coherence engine、全て sorry-free/axiom-clean)
- **§4 Dade 等距 = `FullDadeIsometryData`** (issue 0040 closed) — `(2.6)` 実構成。
- **§5 coherence hub (5.4)/(5.5)/(5.6)** — `retarget_isCoherent` (S07)、lattice-relative `IsCoherent`
  (`extension_inner_eq`、Round-13 弱化済)、`coherentUnion_of_glued` (2族 assembler)、`coherentPairChain` ((5.6) 反復engine)。
- **§6 (6.6) coherence-of-X を実 Dade τ で instantiate** = `peterfalvi_66_coherence_of_X_from_dade` (S07 ~L4285)。
  opaque hstep は除去済。残るのは per-step `DadeChainStep` (S07 ~L4106) の field を genuine (6.6) data から discharge すること。
- **型ブリッジ G2.7**: `dadeIntegralCharacterMap` (S07 ~L3640) = Dade 写像を total ℤ-linear に lift。
  `decompositionPairFromDadeOfIrreducible` (~L3927) = per-step (D₀,Da) producer。
  `dadeOrthonormalCharacterImageFamily` (~L3794) = R(χ) producer。
- **DadeChainStep field**: 全フィールドが genuine (6.6) data に到達 (**posited フィールド ゼロ**)。`hgen`
  discharge 済、`hmemOrtho` content 済、**`hY` 除去済** (本更新: famS/famRatio/famPairwise/hdeg_c 等の
  source-side フィールドに置換し `advance` 内で `dade_Y_collapse_of_family` で証明)。`Dmem`/`hmemTau1Base`
  は `decompositionPairFromDadeOfIrreducible` でほぼ定義的。

### ✅ 解決済: `DadeChainStep.hY` = Peterfalvi (5.6.1) λ-form (前回 crux)
3 コミットで完了 (上記 進捗節に詳細)。`Y_collapse_of_family` (汎用 (5.6.1)/(5.6.2) producer) +
`dade_Y_collapse_of_family` (Dade 特化、hS₁ 不要) + `DadeChainStep` の hY 除去 + `advance` 内証明。
教科書 mmd 04.7 L71-97 をそのまま形式化。前回 HANDOFF の「繊細点」(running τ₁ の直交性、conjugation) は
クリア済 — `Y_collapse_of_family` は `hiso_fam` (running 等距の族直交性) を仮説に取り、全 scalar が実ゆえ
conjugation で破綻しない。

### ✅ 追加で解決: (5.2.d) base coherence seed (chain の `h0`) — commit `c265a3c`
(6.8) prerequisite を調査中に発見した **構造的ギャップ**を解消: 全 coherence producer
(`coherentPairChain`/`retarget_isCoherent_fromDade`/`peterfalvi_66_coherence_of_X_from_dade`/
`coherentUnion_of_glued`) は prior `IsCoherent` (`h0`/`hS₁`) を **consume するのみで construct しない**
— 最小種 `IsCoherent τ {χ,χ̄} A` (1 共役対) を作る base case が皆無だった。これを実装:
- `zSupportedSpan_pair_subset_span`: `Z[{χ,χ̄}]` の supported 部分は `χ−χ̄` で生成 (supported ⟹ 1 で
  消える (`1∉A`)、equal degree `χ̄(1)=χ(1)≠0` で `m+n=0`)。`adjoinPair` の `S₁=∅` 版 (χ₁ で χ を
  再構成できないため vanish-at-1 論法)。
- `coherentPair`: orthonormal target pair `{X,X̄}` (`X̄=X−τ(χ−χ̄)`) から `IsCoherent τ {χ,χ̄} A`。
  (5.6.3) retarget の `S₁=∅` 退化 (`retarget`/`retarget_inner_eq_on_zSpan_union`、残差消滅)。
- `coherentPair_fromDade`: 実 Dade τ での seed。`R(χ)` (ψ=0 分解 + `retargetTargetPair`) が `{X,X̄}` を、
  generation は `irreducibleCharacter_apply_one_eq_pos_natCast`/`_conj_apply_one`/`1∉A` で供給。
sorry/axiom 無、AxiomsCheck 3 件登録、full build 緑 3360 jobs。

### 🎯 次の crux = (6.8) capstone (`sibleySetup_is_coherent`, S08:188)
(6.6) coherence-of-X が image-side posit ゼロの完全 constructive、chain の base seed
(`coherentPair_fromDade`)、**かつ等次数 coherence primitive (`coherentEqualDegree[_fromDade]`,
commits dd1b2b9/8e8fd93) も landed** したので、残るは:

1. ~~Y-coherence = `DadeChainStep.advance` 反復~~ **← 誤り、解決済**。等次数では (5.6) 次数不等式が
   2 番目の対で偽 ([上記 進捗節](#))。正しくは **(1.1)+(1.4) 由来の `coherentEqualDegree_fromDade`**
   (landed)。これが (6.6) base prefix `h0` (任意 n に一般化済) と (6.8) `Y=S(H')` の両方を実 Dade τ で
   供給する。**残る wiring** = §8 setup から**等次数族そのものを構成**: (6.8) Y の `η_j(1)=|W₁|`
   ((c)+(1.6)+[Is]Thm 6.34)、(6.6) prefix の等最小次数ブロック抽出 (`exists_monotoneDegreeEnum`)。
   未形式化 character theory ゆえ posit 不可 (scaffolding)。
2. **(6.8) capstone** (mmd 04.8 L150-): H 非可換 p群の case-A (Z=Z(H)∩[H,H]) / case-B (Z=W₂) split、
   各 case で (6.6) coherence-of-X (`peterfalvi_66_coherence_of_X_from_dade`) + Y-coherence
   (`coherentEqualDegree_fromDade`) を `coherentUnion_of_glued` で結合。**未形式化の前提**: (6.5)
   (非可換 p群への還元)、(6.7) (合同 `ψ(z)≡ψ(1) mod |H|`、class-algebra 論法、self-contained だが
   ~300 行)、Isaacs Thm 6.34/Lemma 7.7/2.27。→ `sibleySetup_is_coherent` (S08:188) を discharge。
3. その後 **S09:1589** ((7.10) `card_G0_lower_bound`)。

**主要 landed 部品 (S07)**: `coherentEqualDegree`/`coherentEqualDegree_fromDade` (等次数 base = (6.6)
prefix `h0` + (6.8) Y; `coherentImageMap` Fourier-image 拡張)、`coherentPair_fromDade` (2 元 base seed)、
`peterfalvi_66_coherence_of_X_from_dade` (coherence-of-X)、`DadeChainStep` (全 genuine フィールド) +
`.advance`/`.chainStepAdvance`、`Y_collapse_of_family`/`dade_Y_collapse_of_family` (5.6.1 producer)、
`coherentUnion_of_glued` (2族 assembler)。

### 運用上の制約 (厳守)
- **共有 `main` は触らない** (ユーザー firm 指示)。作業は worktree `…/.claude/worktrees/naughty-nash-c3ffc7` の
  branch `claude/naughty-nash-c3ffc7` のみ。`/home/ywr/odd-order/OddOrder/...` (primary=main) は OFF LIMITS。
- coherence isometry field の **global→lattice-relative 弱化は durably authorized** (Round 13/25、`IsCoherent`/
  `CharacterPsiDecomposition.tau1_isometry` が前例; FT で `dim CF(L)>dim CF(G)` ゆえ全域等距は非存在)。
- NO sorry/admit/axiom、scaffolding 禁止 (hard content を仮説に逃がさない、memory `scaffold-sorry-free-not-done`)、
  thin wrapper 禁止、AxiomsCheck 登録、commit は green 単位ごと + 末尾 `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`。
- 進め方の知見: ループ workflow より**単一集中セッション (直接編集 + leaf build `lake build OddOrder.Peterfalvi.S07_Coherence`)**
  が深い鎖には速い (再読込/decompose-report オーバーヘッド無し)。memory `peterfalvi-frontier-workflow-pattern` 参照。

### 主要ファイル
- `OddOrder/Peterfalvi/S07_Coherence.lean` (coherence engine 4600+ 行; `DadeChainStep` ~L4489 (全 genuine
  フィールド), `.advance` ~L4576 (hY を内部証明), `peterfalvi_66_coherence_of_X_from_dade` ~L4400+,
  `Y_collapse_of_family` ~L3650, `dade_Y_collapse_of_family` ~L4240, `CharacterFamilyBundle` ~L3542,
  `Y_eq_nsmul_tau1_of_lambdaForm` ~L1801, (5.2.e) Dade lemmas ~L3863)。
- `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean:188` (sorry, SibleySetup/CoherenceTarget = 次の crux)。
- `references/peterfalvi/04.7_pp_25_29_Coherence.mmd` (L86-105 = (5.6.1)/(5.6.2) 証明、形式化済) /
  `04.8_*` (L150- = (6.8) case split、次のターゲット)。

---

## 進捗 (2026-06-01, worktree `lucid-kapitsa-c87a31`) — [Is]Thm 6.34 bricks + 完全 assembly plan

**正本 plan = 新ノート `notes/peterfalvi/s08_6_8_assembly_plan.md`** (2 並列 explore 統合 + 監査訂正 +
T0–T11 task DAG)。以下サマリ。

### [Is]Thm 6.34 (induced irreducibility) 着手 — 新 file `OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean`
6.8 の `Y=S(H')` (η_j(1)=|W₁|) + case-A `X⊂Irr L` を供給する最高レバレッジ brick。**landed (sorry-free,
axiom-clean, AxiomsCheck 登録)**:
- **(i) Mackey 制限** `card_smul_restrict_induce` (commit 8e1b74e): `|H|•Res_H(Ind θ)=∑_{x∈G} θ^{x⁻¹}`。
  **非正規化形**で transversal/Quotient.out/fiber-card を全回避 (設計上の鍵)。
- **(ii-pre)** `card_mul_inner_self_induce` + **(ii)** `card_mul_inner_self_induce_eq_card_inertia`
  (commit 9c505fc): `|H|·‖Ind θ‖²=|I_G(θ)|` (=`[I_G(θ):H]`)、irreducible θ。Frobenius∘Mackey∘orthonormality。
- **残**: (iv) degree = `induce_apply_one` **既存**; (iii) 既約性 = `induce_mem_ZIrr`(764) +
  ‖·‖²=1 ⟹ ±irr (新 sub-brick, `exists_irr_sub_irr_of_inner_self_two`@ZIrrFourier:528 を template に) +
  degree>0 で符号確定。

### 監査訂正 (explore が code 照合; handoff の stale 箇所)
1. **(6.7) は ~90% 既 landed** (`peterfalvi_673`@ClassSumAlgebra:1651 等)。handoff の「~300行未実装」は誤り。
   残=上位定理 wiring + (iii)-collapse + rationality (~150-250 LOC, **6.34 非依存・今すぐ可**)。
2. **隠れた最重 blocker = `SibleySetup` が thin** (T1): `coherence.tau` が opaque+大域等距だが engine は
   `dadeIntegralCharacterMap` 専用に `IsCoherent` を産む。**再 param + `tau:=dadeIntegralCharacterMap` 必須**
   (詳細・field 骨子・build-order はノート §B)。**(6.8.a) は H NILPOTENT** (IsPGroup 化は scaffolding)、
   現 `H_sharp_ti` は ambient 誤り。shared/frozen file 変更ゼロで実行可。
3. **今すぐ並行可 (6.34 非依存) leaf**: T0(Cor2.30) / T1(SibleySetup) / T3(6.7 wiring) / T4(Galois) / T5(Lem2.27)。

---

## 🔁 HANDOFF (2026-06-01, worktree `lucid-kapitsa-c87a31`)

### 操作状態 (まず読む)
- **branch `claude/lucid-kapitsa-c87a31`、main (`d46ded5`) から 20 commits ahead、push/merge 未**
  (local-first; push は指示時のみ)。**継続はこの branch 上で**、または先に main へ merge。
- worktree setup 済 (mathlib `.lake/packages` symlink + 自前 olean を main からコピー)
  → `lake build OddOrder OddOrder.AxiomsCheck` が **~数秒で green (3412 jobs)**。手順は
  `notes/meta/worktree_setup.md` (olean warm-start 追記済)。
- **real sorry は不変の 2 個**: `S08_CoherenceTheorems.lean:251` `sibleySetup_is_coherent` ((6.8))、
  `S09_NonexistenceCertain.lean:1596` `card_G0_lower_bound` ((7.10))。`#assert_only_allowed_axioms` 全 green。

### このセッションで landed (5 件、全 green/axiom-clean)
1. **[Is]Thm 6.34 完全形式化** (`GroupTheory/RepresentationTheory/InducedIrreducible.lean`,
   commits 8e1b74e/9c505fc/2f7d545): capstone `isIrreducibleCharacter_induce_of_inertia_eq`
   (`H⊴G, θ:Irr H, inertia(θ)=H ⟹ Ind θ∈Irr G`) + reusable `card_smul_restrict_induce` (Mackey 非正規化),
   `card_mul_inner_self_induce_eq_card_inertia` (‖Ind θ‖²=|I_G(θ)|), `isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos` (norm-1 判定)。
2. **T1 完了** (commits 3f83e90/a01dafc/ebf2c60/48af3d5/53bbbf9): `SibleyDadeHypothesis` (S08) が
   (6.8)(a)(b)(c) faithful + 実 Dade `tau:=dadeIntegralCharacterMap`、`sibleySetup_is_coherent` を
   それに retarget・legacy opaque `SibleySetup` 削除。
3. **S06 監査+修正** (commit e6090a0): `CertainTypeHypothesis.W_sup:W1⊔W2=⊤` の実バグ ((4.2.c) では
   `W=W₁×W₂` は真部分群) を発見・修正 → 真の (4.2) (`isComplement`/cyclic/`W2≤K`/`C_K(x)=W₂`/`W_odd`)。
4. **(6.8) T6 engine unblock** (commit): `coherentEqualDegree_fromDade` を個別→**差分 support** に弱化
   (誘導既約は 1 で非零ゆえ個別不可、等次数差分は OK)。
5. **(6.8) T6 等次数 infra** (commit dde1dcd): `SibleyDadeHypothesis.index_H_eq_card_W1` (`[L:H]=|W₁|`)。
6. **(6.8) T6 c1+degree consumer** (2026-06-02): Frobenius case c1 は
   inertia_eq_of_frobeniusGroup / isIrreducibleCharacter_induce_of_frobeniusGroup まで landing。
   さらに S08 で degree-one source θ の (Ind_H^L θ)(1)=|W₁| helper を landing。
7. **(6.8) T6 difference-support consumer** (2026-06-02): normal H の induction support を
   generic infra として landing し、S08 で degree-one induced differences の H^# support helper を landing。

### 現フロンティア = (6.8) proof T6 family / case-c2 wiring
- (6.8) proof は `sibleySetup_is_coherent` (S08:251) を埋める作業。task DAG (T0–T11) + 全 spec の
  **正本 = `notes/peterfalvi/s08_6_8_assembly_plan.md`** (§A 6.34 / §B-C T1 / §D T6)。
- **T6 (Y coherent) の律速** = `inertia(θ)=H` (W₁ が Irr(H)∖{1} に自由作用、6.34 の前提)。精査結果:
  repo `brauer_permutation_lemma'` は **inversion 専用**だったが、2026-06-02 までに一般版 Layer A と
  conjugation 実体化 Layer B (`ConjugationBrauer.lean`: `IrreducibleCharacter.conjByPerm`,
  `ConjClasses.conjByPerm`, `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`) が landed。
  群レベル自由作用は Frobenius `FrobeniusActionTI` で既存。Layer C のうち
  **fixed conjugacy classes count = 1 ⇒ nontrivial Irr は固定されない** は 2026-06-02 に landed。
  Frobenius case (c1) は centralizer_kernel_le から inertia=H、6.34、degree-one source の
  (Ind θ)(1)=|W₁| helper まで landed。
  残る T6 は Y=S(Hprime) family construction、coherentEqualDegree_fromDade 接続、case c2 側の inertia discharge。
  **これが (6.8)/§9–§16 の Frobenius-induced irreducibility 全体の鍵**。
- 次セッション推奨: issue 0053 Layer D2c を進める。Y=S(Hprime) family construction を
  S08 の新 degree/support helpers + difference-support engine に接続し、case c2 の inertia を別途放電する。

### 並行可能な独立 leaf (6.34/Brauer 非依存、`s08_6_8_assembly_plan.md` C 表)
T0 (Cor 2.30) / T3 ((6.7) 上位 wiring、atoms は ClassSumAlgebra/AlgInt 既存) / T4 ((1.9)+(5.9.a) Galois,
case B) / T5 ([Is]Lem 2.27)。他に S09 (7.10) の (7.8.a)(7.9) (issue 0044)。

### 厳守事項
shared `main` 不可侵 / NO sorry-admit-axiom (scaffolding 禁止) / AxiomsCheck 登録 / green 単位 commit +
`Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>` / push は指示時のみ。
