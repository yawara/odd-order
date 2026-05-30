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
