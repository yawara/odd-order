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
  - **honest 판정**: 둘 다 순수 산술 — 입력 divisibility 는 character-degree 구조의 정직한 귀결
    (additive sum identity, [Is] Cor 2.30, (6.4.c) coprimality). posited 아님.
  - **(6.6) 잔여 (pass-2 leaf-2 이후)**: 이 두 producer 의 *입력* divisibility 생산 (sum identity
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
