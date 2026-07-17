/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import OddOrder.Algebra.AlgInt
import OddOrder.Algebra.GaloisRationalInteger
import OddOrder.GroupTheory.ChermakDelgado
import OddOrder.GroupTheory.CoprimeFixedPoints
import OddOrder.GroupTheory.MinimalInvariantNormal
import OddOrder.GroupTheory.WielandtAssembly
import OddOrder.GroupTheory.WielandtPerFactorDischarge
import OddOrder.GroupTheory.RepresentationTheory.ElemAbelianAutAction
import OddOrder.GroupTheory.RepresentationTheory.FongSwan
import OddOrder.GroupTheory.RepresentationTheory.WielandtKernelFPF
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabFrobenius
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import OddOrder.GroupTheory.RepresentationTheory.ConjugationFieldModel
import OddOrder.GroupTheory.RepresentationTheory.BlockScalarSylow
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialSinger
import OddOrder.GroupTheory.WielandtFixedPoint
import OddOrder.GroupTheory.PiElementDecomposition
import OddOrder.GroupTheory.RepresentationTheory.CharacterCount
import OddOrder.GroupTheory.RepresentationTheory.CharacterCompleteness
import OddOrder.GroupTheory.RepresentationTheory.GaloisCharacter
import OddOrder.GroupTheory.RepresentationTheory.SchurCenterBound
import OddOrder.GroupTheory.RepresentationTheory.SylowTICongruence
import OddOrder.GroupTheory.RepresentationTheory.CyclotomicGaloisAction
import OddOrder.GroupTheory.RepresentationTheory.ColumnOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutationUnconditional
import OddOrder.GroupTheory.RepresentationTheory.ConjugationBrauer
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
import OddOrder.GroupTheory.RepresentationTheory.ClassSumCoefficientFormula
import OddOrder.GroupTheory.RepresentationTheory.RealClassTISubset
import OddOrder.GroupTheory.RepresentationTheory.Clifford
import OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialThm25Final
import OddOrder.GroupTheory.NilpotentAbelianization
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch04_Commutators.HartleyTurull
import OddOrder.Isaacs.Ch04_Commutators.Mann
import OddOrder.Isaacs.Ch05_Transfer.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.OddComplement
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroupQuotient
import OddOrder.Isaacs.Ch06_FrobeniusActions.KernelNilpotent
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main
import OddOrder.Isaacs.Ch09_MoreSubnormality.Quasisimple
import OddOrder.Isaacs.Ch09_MoreSubnormality.Components
import OddOrder.Isaacs.Ch09_MoreSubnormality.Semisimple
import OddOrder.Isaacs.Ch09_MoreSubnormality.Layer
import OddOrder.Isaacs.Ch09_MoreSubnormality.GeneralizedFitting
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.ForwardFromCh03
import OddOrder.Isaacs.Ch10_MoreTransfer.Main
import OddOrder.Isaacs.Ch10_MoreTransfer.HuppertMetacyclic
import OddOrder.BG.Ch1_Preliminary.PLengthPComplement
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.BG.Ch1_Preliminary.S04d_GorThm415
import OddOrder.BG.Ch1_Preliminary.S04e_GorThm37
import OddOrder.BG.Ch1_Preliminary.S04g_Thm418
import OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups
import OddOrder.BG.Ch1_Preliminary.S01b_Prop116
import OddOrder.BG.Ch1_Preliminary.S03d_Thm34
import OddOrder.BG.Ch1_Preliminary.S03e_Thm35
import OddOrder.BG.Ch1_Preliminary.S03f_Thm36
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310General
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310ElemAbelian
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310Nilpotent
import OddOrder.BG.Ch1_Preliminary.S03h_Thm38
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
import OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal
import OddOrder.BG.Ch3_MaximalSubgroups.S10_BetaRadical
import OddOrder.BG.Ch3_MaximalSubgroups.S10_LocalLemmas
import OddOrder.BG.Ch3_MaximalSubgroups.S11_MsigmaANormal
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Corollary126
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Corollary129
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Corollary1210
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1211
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212b
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212c
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1213
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Proposition1215
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Corollary1214
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1217
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Corollary1216
import OddOrder.BG.Ch3_MaximalSubgroups.S12_E
import OddOrder.BG.Ch3_MaximalSubgroups.S12_ExceptionalBridge
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma128
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma128d
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1218
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem125
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem127
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem127d
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeActionTransition
import OddOrder.BG.Ch3_MaximalSubgroups.S14_Prop142Support
import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting
import OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_PairIntersection
import OddOrder.BG.AppA_PStability
import OddOrder.BG.AppB_Puig
import OddOrder.BG.AppB_PuigB3B4
import OddOrder.BG.AppB_Thm62
import OddOrder.Peterfalvi.S03_PreliminaryCharacter
import OddOrder.Peterfalvi.S03b_Vanishing
import OddOrder.Peterfalvi.S04_DadeIsometry
import OddOrder.Peterfalvi.S05_TICyclic
import OddOrder.Peterfalvi.S05_SigmaIsometry
import OddOrder.Peterfalvi.S05_IntegralSigma
import OddOrder.Peterfalvi.S05_OmegaGrid
import OddOrder.Peterfalvi.S05_OmegaSigmaGrid
import OddOrder.Peterfalvi.S06_CertainTypeSupport
import OddOrder.Peterfalvi.S06_CertainTypeStructure
import OddOrder.Peterfalvi.S06_CertainTypeIsometry
import OddOrder.Peterfalvi.S06_CertainTypeConjugation
import OddOrder.Peterfalvi.S06_MuColumnBridge
import OddOrder.Peterfalvi.S07_Coherence
import OddOrder.Peterfalvi.S07_CoherenceConstantDegree
import OddOrder.Peterfalvi.S07_CoherenceGalois
import OddOrder.Peterfalvi.S08_CoherenceTheorems
import OddOrder.Peterfalvi.S08_Theorem62_63_Standalone
import OddOrder.Peterfalvi.S08_SixTwoGeneral
import OddOrder.Peterfalvi.S13_CoreStructure
import OddOrder.Peterfalvi.S09_NonexistenceCertain
import OddOrder.Peterfalvi.S09_FrobeniusFamilyOrthogonality
import OddOrder.Peterfalvi.S09_FrobeniusGammaDecomposition
import OddOrder.Peterfalvi.S09_FrobeniusGammaNormEstimate
import OddOrder.Peterfalvi.S09_FrobeniusBsumEstimate
import OddOrder.Peterfalvi.S09_FrobeniusGoodIndexEstimate
import OddOrder.Peterfalvi.S09_FrobeniusSelectedEstimate
import OddOrder.Peterfalvi.S09_FrobeniusParity
import OddOrder.Peterfalvi.S10_CoherenceWiring
import OddOrder.GroupTheory.RepresentationTheory.GaloisInnerTransport
import OddOrder.Peterfalvi.S11_ImprimitiveUBound
import OddOrder.Peterfalvi.S11_GaloisFieldModel
import OddOrder.Peterfalvi.S12_Noncoherence
import OddOrder.Peterfalvi.S12_TypeVCaseC
import OddOrder.Peterfalvi.S13_TypeIIIGalois
import OddOrder.Peterfalvi.S13_NonGaloisExclusion
import OddOrder.Peterfalvi.S15_Tau1T
import OddOrder.Peterfalvi.S15_CharacterDegreeEnginesSSide
import OddOrder.FeitThompson
import OddOrder.BG.AppC_NormSet
import OddOrder.BG.AppC_FrobeniusClassSum
import OddOrder.BG.AppC_LemmaC2
import OddOrder.Peterfalvi.Appendices.SemilinearField
import OddOrder.Peterfalvi.Appendices.NearFields
import OddOrder.GroupTheory.RepresentationTheory.CyclotomicCharacterCongruence

/-!
# Axioms check for chapter flagship theorems

本ファイルは, **各 Isaacs 章の代表定理が許可された公理のみに依存していること**を
elaboration 時に検査する CI ガード. moore57 プロジェクトの `Moore57/AxiomsCheck.lean`
パターンを踏襲.

## 検査対象 (各章 1 つ)

| 章 | 定理 | Isaacs 番号 |
|---|---|---|
| Ch.1 (Sylow Theory) | `Subgroup.chermakDelgado` | Thm 1.41 (Chermak-Delgado) |
| Ch.2 (Subnormality) | `OddOrder.Isaacs.Ch02.matsuyama` | Thm 2.13 (Matsuyama involution) |
| Ch.2 (Subnormality) | `baerSuzuki_pCore` | Thm 2.12 系 (Baer-Suzuki) |
| Ch.2 (Subnormality) | `lucchini_index_normalCore_lt_index` | Thm 2.20 (Lucchini) |
| Ch.3 (Split Extensions) | `horosevskii_aut_order_lt` | Thm 3.3 (Horosevskii) |
| Ch.3 (Split Extensions) | `OddOrder.Isaacs.Ch03.hall_E_exists` | Thm 3.13 (Hall E for solvable) |
| Ch.3 (Split Extensions) | `piLength_le_one_of_abelian_pi_hall` | Thm 3.22 (π-length ≤ 1) |

## 許可公理

* **Lean / mathlib 標準**: `propext`, `Classical.choice`, `Quot.sound`.

`sorryAx` (= `sorry` 由来) や本プロジェクトの "暫定 axiom"
(`OddOrder.Mathlib.SchurZassenhausConj` の `IsComplement'.exists_conj_of_coprime` 等) に依存する
定理が紛れ込むと
elaboration が失敗し, `lake build` も失敗する.

これは "**flagship 定理は無条件 (unconditional) である**" という CI 保証.

## 将来追加

Ch.4-Ch.10, BG, Peterfalvi の flagship が完成した順に追記する.
-/

-- 機械列挙ファイル (flagship axioms check) のため分割・行長規約の対象外 — CLAUDE.md の明示例外
set_option linter.style.longFile 8500
set_option linter.style.longLine false

open Lean Elab Command

namespace OddOrder.AxiomsCheck

/-- Lean / mathlib 標準の公理. -/
def allowedStandard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- 名前 `n` が許可された公理であるかどうかを判定. -/
def isAllowed (n : Name) : Bool :=
  allowedStandard.contains n

end OddOrder.AxiomsCheck

/-- 指定された定数が allowlist の公理のみに依存していることを assertion.
disallow された公理 (`sorryAx`, プロジェクト固有 axiom 等) が依存性閉包に
現れた場合は elaboration が失敗 ⇒ `lake build` が失敗する. -/
elab "#assert_only_allowed_axioms " name:ident : command => do
  let constName := name.getId
  let env ← getEnv
  unless env.contains constName do
    throwError m!"axioms check: constant `{constName}` not found"
  let axs ← liftCoreM <| Lean.collectAxioms constName
  let bad := axs.filter (fun a => !OddOrder.AxiomsCheck.isAllowed a)
  if bad.isEmpty then
    logInfo m!"axioms check OK: `{constName}` depends on {axs.size} axiom(s), all in allowlist"
  else
    throwError m!"axioms check FAILED: `{constName}` depends on {bad.size} \
disallowed axiom(s):{indentD m!"{bad.toList}"}"

/-! ### Per-chapter flagship checks. -/

-- Ch.1 (Sylow Theory): Thm 1.41 Chermak-Delgado main theorem
-- ∃ characteristic abelian N, |G:N| ≤ |G:A|² ∀ abelian A
#assert_only_allowed_axioms Subgroup.chermakDelgado
#assert_only_allowed_axioms Subgroup.card_quotient_lt_of_ne_bot

-- Ch.2 (Subnormality): Thm 2.13 Matsuyama
-- 奇素数位数 inversion `x^t = x⁻¹` の存在 (`t ∉ O_2(G)` 下)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch02.matsuyama

-- Ch.2 (Subnormality): Baer-Suzuki single-element p-core form (lean-eval problem)
-- x ∈ O_p(G) ↔ ∀ g, ⟨x, gxg⁻¹⟩ p-group. Isaacs 2.12 iff から導出.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch02.baerSuzuki_pCore

-- Ch.2 (Subnormality) / Ch.4 forward dependency: Thm 2.20 Lucchini
-- A cyclic proper subgroup A, K = core_G(A) ⇒ |A:K| < |G:A|.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.lucchini_index_normalCore_lt_index

-- Ch.3 (Split Extensions): Thm 3.3 Horosevskii
-- Every automorphism of a nontrivial finite group G has order < |G|.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.horosevskii_aut_order_lt

-- Ch.3 (Split Extensions): Thm 3.13 Hall E (solvable case)
-- Hall π-subgroup の存在 (solvable G)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.hall_E_exists

-- Ch.3 (Split Extensions): Thm 3.21 Hall-Higman 1.2.3 ⭐ **FT クリティカル**
-- G π-separable + O_{π'}(G) = ⊥ ⇒ C_G(O_π(G)) ≤ O_π(G)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.hall_higman_1_2_3

-- Ch.3 (Split Extensions): π-core quotient reduction
-- Quotienting by O_π(G) kills the π-radical.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot

-- Ch.3 (Split Extensions): π-separability passes to arbitrary subgroups.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.Subgroup.isPiSeparable_of_isPiSeparable

-- Ch.3 (Split Extensions): Thm 3.22 Hall-Higman π-length ≤ 1
-- G π-separable + abelian π-Hall ⇒ [O_{π',π}(G), O_{π',π}(G)] ≤ O_{π'}(G)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.piLength_le_one_of_abelian_pi_hall

-- Ch.4 (Commutators): Lem 4.28 ⭐ **= BG Prop 1.6(a), FT クリティカル**
-- coprime action + solvability ⇒ `G = C_G(A) · [G,A]`.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top

-- Ch.4 (Commutators): Lem 4.29 ⭐ **= BG Prop 1.6(b), FT クリティカル**
-- coprime action + solvability ⇒ `[G,A,A] = [G,A]` in semidirect-product form.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.iterCommutator_inl_inr_two_eq_one

-- Ch.4 (Commutators): Lem 4.29 書籍印刷形 (無条件): coprimality alone ⇒ `[G,A,A] = [G,A]`.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.iterCommutator_inl_inr_two_eq_one_of_coprime

-- Ch.4 (Commutators): Cor 4.30
-- faithful action + `[G, A, ..., A] = 1` ⇒ every prime divisor of |A| divides |G|.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.prime_dvd_card_of_faithful_iterCommutator_eq_bot

-- Ch.4 (Commutators): Thm 4.24
-- finite faithful action + `[G, A, ..., A] = 1` ⇒ `A` is nilpotent.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.isaacs_thm_4_24

-- Ch.4 (Commutators): Thm 4.31 (external direct-product form)
-- P p-group, Q p'-group, Q fixes all P-fixed elements ⇒ Q acts trivially.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.isaacs_thm_4_31_external

-- Ch.4 (Commutators): Lem 4.32 (両半) P p-群 on G p-群 nontrivial
-- 前半: Γ = G ⋊ P 内で ⁅inl(G), inr(P)⁆ < inl(G) (strict)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.commutator_inl_inr_lt_inl_of_pgroup_action
-- 後半: fixedPointsOfMulAut φ > ⊥ (C_G(P) > 1)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.fixedPoints_ne_bot_of_pgroup_action_pgroup

-- Ch.4 (Commutators): Thm 4.33 setup
-- Hall-Higman 1.2.3 specialized from `O_π` to the usual p-core `O_p(G)`.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.hall_higman_opCore
-- Normal p-subgroups commute with normal p'-subgroups in a finite group.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.commute_of_normal_isPGroup_of_normal_isPiCompl
-- First 4.33 step: `O_{p'}(N_G(P))` centralizes `O_p(G)`.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.oPiCore_compl_normalizer_le_centralizer_opCore
-- Reduced 4.33 case after Hall-Higman: `O_{p'}(G)=1` ⇒ `O_{p'}(N_G(P))=1`.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch04.oPiCore_compl_normalizer_eq_bot_of_oPiCore_compl_eq_bot
-- Full 4.33: p-local `H` satisfies `O_{p'}(H) ≤ O_{p'}(G)`.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.oPiCore_compl_le_oPiCore_compl_of_isPLocal

-- Ch.4 (Commutators): Thm 4.34 ⭐ **= BG Prop 1.6(d), FT クリティカル**
-- abelian coprime action ⇒ `C_G(A) ∩ [G,A] = 1`.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian

-- Ch.4 (Commutators): Cor 4.35 ⭐ **= BG Prop 1.6(e), FT クリティカル**
-- abelian p-group + p'-group action fixing all order-p elements ⇒ trivial action.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p

-- Ch.4 (Commutators): Thm 4.36 ⭐⭐⭐ **= BG Thm 1.11, FT クリティカル**
-- p > 2, G p-群, A p'-群 acts on G, A fixes all order-p elements ⇒ A trivial on G.
-- Baer trick (Lem 4.37) + Cor 4.35 + 強帰納法 (Three-subgroups).
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.isaacs_thm_4_36

-- Ch.4 (Commutators): Thm 4.38
-- P p-subgroup, Q normal p'-subgroup, Q fixes all P-fixed elements ⇒ Q acts trivially.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.isaacs_thm_4_38

-- Ch.5 (Transfer): Cor 5.4 quotient form (Z ≤ Γ' ∩ Z(Γ), p ∣ |Z| ⇒ Sylow_p(Γ/Z) noncyclic)
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch05.not_isCyclic_sylow_quotient_of_le_commutator_inf_center

-- Ch.5 (Transfer): Thm 5.10 (Dietzmann: finite conjugation-closed bounded-exponent X ⇒ ⟨X⟩ finite)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.dietzmann

-- Ch.5 (Transfer): Lem 5.12 (N_G(P) controls C_G(P) fusion)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.normalizer_controls_centralizer_fusion

-- Ch.5 (Transfer): Thm 5.13 (Burnside normal p-complement)
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer

-- Ch.5 (Transfer): Cor 5.19 general form (Sylow 2 with strict-max cyclic direct factor ⇒ not simple)
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch05.not_isSimpleGroup_of_sylow_two_cyclic_strict_max_factor

-- Ch.5 (Transfer): Thm 5.20 (focal transfer kernel is A^p(G))
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.APrime_eq_transferFocal_ker

-- Ch.5 (Transfer): Thm 5.21 (Focal Subgroup Theorem)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.focalSubgroupTheorem

-- Ch.5 (Transfer): Thm 5.24 (nilpotent maximal subgroup of a finite simple group is a p-group)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.exists_isPGroup_of_isCoatom_of_isNilpotent

-- Ch.5 (Transfer): Thm 5.25 (normal p-complement iff Sylow controls own fusion)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_controlsOwnFusion

-- Ch.5 (Transfer): Thm 5.26 (Frobenius normal p-complement)
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer

-- Ch.5 (Transfer): Cor 5.29 (prime-divisor obstruction gives normal p-complement)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.hasNormalPComplement_of_no_prime_dvd_pow_sub_one

-- Ch.5 (Transfer): Cor 5.30 (odd p, order-p elements central)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.normal_p_complement_of_order_p_central_odd

-- Ch.6 (Frobenius Actions): Thm 6.4 (2)⇒(1) constructor (TI ⇒ Frobenius action)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.IsFrobeniusGroup.of_trivialIntersection

-- Ch.6 (Frobenius Actions): Thm 6.7 (self-centralizing normal subgroup is complemented,
-- and is a Frobenius kernel when proper nontrivial)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.exists_isComplement'_of_centralizer_le

-- Ch.6 (Frobenius Actions): Thm 6.9 solvable Frobenius subgroup obstruction
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup

-- Ch.6 (Frobenius Actions): Thm 6.9 elementary abelian subgroup obstruction
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_ge_prime_sq

-- Ch.6 (Frobenius Actions): Thm 6.9 `p = q` order-`pq` branch
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_prime_sq

-- Ch.6 (Frobenius Actions): Thm 6.9 full order-`pq` branch
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime

-- Ch.6 (Frobenius Actions): Cor 6.10 Sylow subgroups have unique order-`p` subgroup
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.subgroups_card_prime_unique_of_frobeniusAction_sylow

-- Ch.6 route to Thm 6.11: finite commutative p-groups with unique order-`p`
-- subgroup are cyclic, and hence commutative Sylow subgroups of Frobenius complements are cyclic.
#assert_only_allowed_axioms IsPGroup.isCyclic_of_subgroups_card_prime_unique
#assert_only_allowed_axioms IsPGroup.isCyclic_subgroup_of_subgroups_card_prime_unique
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.sylow_isCyclic_of_frobeniusAction_of_isMulCommutative
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.isCyclic_of_frobeniusAction_of_isMulCommutative
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.isCyclic_of_comm_two_group_unique_involution
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.unique_involution_of_comm_of_involutions_invert_element
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.isCyclic_of_comm_two_group_involutions_invert_element
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_distinct_subgroups_card_two_of_external_involution

-- Ch.6 (Frobenius Actions): Thm 6.24 (Thompson) — Frobenius kernels are nilpotent
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.isNilpotent_of_isFrobeniusAction
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.IsFrobeniusGroup.isNilpotent_kernel

-- Ch.9 (More on Subnormality): Lem 9.1 — G/Z(G) simple ⇒ G' quasisimple with
-- G'/Z(G') ≅ G/Z(G); Lem 9.2 — proper normals of a quasisimple group are central,
-- nonidentity quotients are quasisimple.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.isQuasisimple_commutator
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.commutatorQuotientCenterEquiv
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.IsQuasisimple.normal_le_center
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.IsQuasisimple.quotient

-- Ch.9 (More on Subnormality): Lem 9.3 — a component not inside a minimal normal
-- subgroup centralizes it; Thm 9.4 — distinct components commute.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch09.commutator_eq_bot_of_isMinimalNormal_of_isComponent
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.IsComponent.commutator_eq_bot_of_ne

-- Ch.9 (More on Subnormality): Lem 9.5 — a product of nonabelian simple normal subgroups
-- is direct (Pi-equiv) and the family is exactly the set of minimal normal subgroups;
-- payload: semisimple groups are centerless with nonabelian simple minimal normals and
-- no nontrivial solvable normal subgroups.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.piEquivOfSemisimpleFamily
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.mem_semisimpleFamily_of_isMinimalNormal
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch09.IsSemisimpleGroup.isSimpleGroup_of_isMinimalNormal
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch09.IsSemisimpleGroup.eq_bot_of_normal_of_isSolvable

-- Ch.9 (More on Subnormality): Lem 9.6 — a minimal normal subgroup of a finite group is
-- abelian or semisimple.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch09.isMulCommutative_or_isSemisimpleGroup_of_isMinimalNormal

-- Ch.9 (More on Subnormality): the layer E(G) and Theorem 9.7 — (a) E' = E,
-- (b) E/Z(E) semisimple, (c) [E,M] = 1 for every solvable normal subgroup M.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.commutator_layer_eq_layer
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.isSemisimpleGroup_layer_quotient_center
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.commutator_layer_eq_bot_of_normal_isSolvable

-- Ch.9 (More on Subnormality): generalized Fitting F*(G) = F(G)E(G); Cor 9.9 (←) —
-- F(G) ⊇ C_G(F(G)) implies F*(G) = F(G) (via Thm 9.7(c)).
#assert_only_allowed_axioms OddOrder.Isaacs.Ch09.genFitting_eq_fitting_of_centralizer_fitting_le

-- Ch.6 (Frobenius Actions): Cor 6.17 full form — Sylow subgroups of a Frobenius complement
-- are cyclic or generalized quaternion.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.sylow_isCyclic_or_two_quaternion_of_frobeniusAction

-- Ch.6 (Frobenius Actions): Thm 6.19 — odd Frobenius complement has a unique subgroup of
-- order `r` for each prime `r ∣ |A|` (action + subgroup-pair forms).
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.existsUnique_card_prime_of_isFrobeniusAction_of_odd
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.existsUnique_card_prime_of_isFrobeniusGroup_of_odd

-- Ch.6 (Frobenius Actions): Huppert V.8.18 b) — odd Frobenius complement is a Z-group,
-- its order-`r` subgroups centralize the commutator, and every prime-order subgroup is normal.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.isZGroup_of_isFrobeniusAction_of_odd
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.centralizes_commutator_of_card_prime_coprime
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusAction_of_odd
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusGroup_of_odd
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_unique_subgroups_card_two_of_external_involution
-- Lem 6.21 setup: `K = ⟨ C_N(a) | a ≠ 1 ⟩` and its abelian-action invariance.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.actionFixedBy_eq_actionFixedPoints_zpowers
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure_le_iff
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.subgroup_le_nontrivialActionFixedByClosure_of_closure_eq_top
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.actionFixedBy_invariant_of_commute
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure_invariant_of_commutative
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.quotient_isFrobeniusAction_of_fixedBy_le
-- Group-level companion of the action-quotient above: a Frobenius *group* transports across an
-- isomorphism (kernel/complement/normality/complement-relation/Frobenius-condition all carried).
-- Used in Peterfalvi (14.9) to move `V ⋊ W₂` onto `T/Q` for the `calT1` inertia `I_T(inflate θ)=QV`.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.isFrobeniusGroup_map_equiv
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.normal_of_commutator_le
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.sylow_not_le_of_prime_dvd_index
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_aInvariant_sylow_eq_top_of_prime_dvd_index_of_proper_invariant_le
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.commutator_le_of_proper_invariant_le_of_isSolvable
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure_eq_top_of_proper_invariant_le
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic_of_nontrivial
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.isCyclic_of_faithful_trivial_on_proper_invariant
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_involution_mem_of_nontrivial_two_subgroup
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_unique_subgroups_card_two_of_external_involution_of_nontrivial_two_subgroup
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_unique_subgroups_card_two_of_external_involution_of_index_two
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_unique_subgroups_card_two_of_dihedral_of_not_isCyclic
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_unique_subgroups_card_two_of_semiDihedral_of_not_isCyclic
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_normal_isMulCommutative_relIndex_prime_of_lt_centralizer
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_maximal_normal_isMulCommutative
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.centralizer_eq_of_maximal_normal_isMulCommutative
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.quotient_card_le_mulAut_of_self_centralizing
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.quotient_commutative_of_isCyclic_of_self_centralizing
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.quotient_commutative_of_maximal_normal_isCyclic
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.dihedralOrQuaternion_of_self_centralizing_cyclic_card_four
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_normal_noncomm_relIndex_prime_of_maximal_normal_zpowers_lt_top
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.card_ne_eight_of_relIndex_prime_of_card_ne_four
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.normal_of_le_of_quotient_commutative
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.center_lt_subgroupOf_of_self_centralizing_of_relIndex_prime_of_not_isMulCommutative
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.center_index_eq_prime_sq_of_subgroupOf_relIndex_prime
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.center_relIndex_zpowers_eq_prime_of_pow_mem_center
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_characteristic_isElementaryAbelian_of_self_centralizing_relIndex_prime
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_characteristic_isElementaryAbelian_of_zpowers_relIndex_pow_mem_center
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.not_exists_characteristic_isElementaryAbelian_card_prime_sq_of_normal_abelian_cyclic
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.pow_not_mem_center_of_zpowers_relIndex_of_normal_abelian_cyclic
-- Thm 6.12 conjugation exponent dispatch: `a^p ∈ ⟨c⟩` gives `i^p ≡ 1`, while
-- non-fixity of `c^p` excludes `i ≡ 1`, so Lem 6.16 forces the two 2-adic cases.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.conj_exponent_pow_modEq_one_of_pow_mem_zpowers
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.conj_exponent_not_modEq_one_of_pow_conj_ne
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.conj_exponent_two_cases_of_pow_mem_zpowers_of_pow_conj_ne
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_conj_exponent_two_adic_cases_of_zpowers_relIndex_of_normal_abelian_cyclic
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.three_le_exponent_of_zpowers_relIndex_of_normal_abelian_cyclic
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.conj_square_eq_inv_of_pow_mem_zpowers_of_pow_conj_ne
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.conj_square_eq_inv_of_normal_zpowers_of_pow_mem_of_pow_conj_ne
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.quotient_involution_comap_card_ne_eight_of_card_ne_four
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.quotient_involution_conj_square_eq_inv_of_zpowers
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.quotient_isCyclic_of_involutions_invert_zpowers_square
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.conj_eq_inv_or_twist_of_two_adic_cases
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.conj_exponent_modEq_sq_of_quotient_sq_eq
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_sq_eq_of_isCyclic_two_group_involution_of_card_ne_two
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.index_eq_two_of_cyclic_quotient_of_two_adic_conj_cases
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.dihedralOrQuaternionOrSemiDihedral_of_cyclic_quotient_two_adic_conj_cases
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.dihedralOrQuaternionOrSemiDihedral_of_zpowers_relIndex_cyclic_quotient
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.dihedralOrQuaternionOrSemiDihedral_of_zpowers_relIndex_of_quotient_involutions
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.dihedralOrQuaternionOrSemiDihedral_of_maximal_normal_zpowers_lt_top
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.dihedralOrQuaternionOrSemiDihedral_of_maximal_normal_zpowers_lt_top_card_ne_four
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.isCyclic_or_two_dihedralOrQuaternionOrSemiDihedral_of_normal_abelian_cyclic
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_prime_ne_two
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.isCyclic_or_two_quaternion_of_subgroups_card_prime_unique

-- Ch.6 (Frobenius Actions): Lem 6.15 p=2 abelian index-two branch
-- finite abelian noncyclic 2-group with cyclic index-two subgroup has characteristic
-- elementary abelian subgroup of order 4.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_characteristic_isElementaryAbelian_four_of_noncyclic_abelian_two_group
-- Lem 6.15 p=2 setup: `T/T'` is abelian, and it is noncyclic under the center-index
-- hypothesis.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.quotient_commutator_commutative
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.quotient_commutator_not_isCyclic_of_center_index_prime_sq
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.quotient_commutator_image_cyclic_index_two_of_center_index_four
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_characteristic_lift_quotient_commutator_four_of_center_index_four
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.card_lift_quotient_commutator_eq_eight_of_center_index_four
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_lift_quotient_commutator_order_eight_of_center_index_four
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_lift_order_eight_noncyclic_cyclic_index_two_of_center_index_four
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_lift_order_eight_noncyclic_abelian_cyclic_index_two_of_center_index_four
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_characteristic_isElementaryAbelian_four_of_center_index_four
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.exists_characteristic_isElementaryAbelian_of_center_index_prime_sq
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_unique_subgroups_card_prime_of_center_index_prime_sq_odd
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_unique_subgroups_card_two_of_center_index_four
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.false_of_unique_subgroups_card_prime_of_center_index_prime_sq

-- Ch.7 (Thompson Subgroup): Thm 7.5 GL(2,p) bridge for automorphism subgroups.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.gl2_pSubgroup_card_le_prime
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.opCore_eq_bot_of_sylow_card_le_prime_of_not_normal
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.centralizer_oPiCore_compl_le_of_opCore_eq_bot
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.sylow_eq_bot_of_le_oPiCore_compl
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.normal_of_isPGroup_index_le_prime
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.actionCentralizer_inf_normal_of_index_le_prime
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.mulAut_centralizes_of_gl2_image_hypotheses
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.le_centralizer_of_map_le_centralizer_of_injective
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.subgroup_centralizes_of_mulAut_gl2_image_hypotheses
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.map_le_normalizer_map_of_normal
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.not_dvd_card_map_of_isPiGroup_compl_of_injective
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.two_subgroup_abelian_of_le_map_of_injective
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.sylow_normal_of_elementaryAbelian_card_prime_sq_of_faithful
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.subgroup_normal_of_injective_mulAut_of_isCyclic
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotientActionKernel_normal
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotientActionFaithfulHom_injective
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.actionCentralizer_quotient_image_le_quotientActionHom_actionCentralizer
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.actionCentralizer_quotient_image_le_quotientActionFaithful_actionCentralizer
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.actionCentralizer_quotientActionFaithful_index_le
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.normal_of_quotient_image_normal_of_le
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.sylow_normal_of_quotient_image_normal_of_normal_isPGroup
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotient_images_ne_of_ne_of_le
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotient_sylow_images_ne_of_ne_of_normal_isPGroup
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotient_sylow_image_not_normal_of_not_normal_of_normal_isPGroup
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotient_two_subgroup_abelian
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotient_sylow_normal_of_elementaryAbelian_card_prime_sq_of_actionKernel
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.false_of_quotient_elementaryAbelian_card_prime_sq_of_sylow_not_normal
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotient_sylow_normal_of_isCyclic_of_actionKernel
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.false_of_quotient_isCyclic_of_sylow_not_normal
#assert_only_allowed_axioms
  IsPGroup.isElementaryAbelian_card_prime_sq_of_card_le_prime_sq_of_not_isCyclic
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotient_card_le_prime_sq_of_actionCentralizer_inf
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotient_isElementaryAbelian_card_prime_sq_of_actionCentralizer_inf_not_isCyclic

-- Ch.7 (Thompson Subgroup): Thm 7.6 ⭐⭐⭐ **FT クリティカル**
-- p ≠ 2, G p-solvable, abelian Sylow-2, O_{p'}(G)=1, C_G(Z(P))=P ⇒ J(P) ⊴ G.
-- Goldschmidt 帰納 (Steps 1-8) を full discharge; §7B 内に focused axiom 残無し.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch07.normal_J
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.hasNormalPComplement_of_mulEquiv
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.center_map_subtype_map_of_restrict_injective
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.HasThompsonLocalPComplements.map_mulEquiv
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.HasThompsonLocalPComplements.of_sylow
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.hasThompsonPComplementHypothesis_iff
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.hasNormalPComplement_of_le
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.map_normalizer_le_normalizer_map
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.HasThompsonLocalPComplements.of_subgroup
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.normalizerPPart_eq_card_sylow
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.card_le_normalizerPPart_of_isPGroup
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.exists_isBadNormalizerPSubgroup
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.exists_lexicographically_maximal_badNormalizerPSubgroup
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.normalizer_le_normalizer_thompsonJ
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.exists_badNormalizerPSubgroup_of_not_hasThompsonLocalPComplements
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.lt_normalizer_inf_sylow_of_lt
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.maximal_badNormalizer_normalizer_eq_top
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.maximal_badNormalizer_eq_opCore
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.hasNormalPComplement_of_sylow_eq_bot
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.normalizer_map_quotient_eq_of_le
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.hasNormalPComplement_normalizer_of_maximal_bad_lt
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.maximal_badNormalizer_quotient_hasNormalPComplement
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.hasNormalPComplement_of_quotient_of_isPiGroup_compl
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.oPiPrimeCore_eq_bot_of_minimal_counterexample
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.oPiCorePrime_subgroup_eq_bot_of_opCore_le
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.hasNormalPComplement_of_sylow_eq_top
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.sylow_isCoatom_of_minimal_counterexample
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.centralizer_center_eq_sylow_of_minimal_counterexample
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.quotientComplement_isMulCommutative_of_sylow_isCoatom
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.twoSubgroups_commutative_of_minimal_counterexample
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.thompson_normal_p_complement_of_local_hypotheses
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch07.center_map_subtype_map_of_coprime_kernel

-- Ch.7 (Thompson Subgroup): Thm 7.8 Burnside p^a q^b solvability ⭐⭐⭐ **character-free**
-- |G| = p^a q^b ⇒ G solvable.  Goldschmidt-Bender-Matsuyama 9-step proof (no character
-- theory).  Steps 1-9 + Step 3 の faithful-action 分岐まで full discharge; §7D 内に
-- sorry / project-axiom 残無し ⇒ 真に unconditional.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch07.burnside_p_pow_q_pow

-- Ch.3 (Split Extensions): Thm 3.17 Wielandt — H, K, L pairwise coprime index,
-- 各 solvable ⇒ G solvable.  Burnside 不要 (教科書 p.89 の帰納法そのまま).
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.isSolvable_of_pairwise_coprime_index

-- Ch.7 owner の Ch.3 forward dep: Thm 3.15 (converse of Hall E) — 全素数 p の
-- p-complement 存在 ⇒ G solvable.  Burnside (Thm 7.8) + Wielandt (Thm 3.17) 経由.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch07.isSolvable_of_pcomplement_exists

-- Ch.3 (Split Extensions): Lemma 3.18 — subnormal π/π' series ⇒ π-separable
-- (upper-series 定義への橋; 支配補題 + 拡大閉包 isPiSeparable_of_normal_of_quotient 経由).
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.isPiSeparable_of_subnormal_ladder
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.isPiSeparable_of_normal_of_quotient

-- Ch.3 (Split Extensions): Thm 3.22 完全形 — abelian π-Hall ⇒ G/O_{π',π} は π'-群
-- (genuine π-length ≤ 1; Hall-Higman 1.2.3 経由).
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch03.quotient_oPiPrimePiCore_isPiGroup_compl_of_abelian_pi_hall

-- Ch.3 §3E (Ch.4 owner): Thm 3.26 — A-不変共役類 ↔ C_G(A) の類の全単射 (Glauberman 経由).
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.aInvariantConjClassesEquiv

-- Ch.4 §4B Mann クラスタ: Lem 4.17 計数 / Cor 4.18 / Thm 4.15 / Lem 4.16 (nilpotent 一般化) /
-- Thm 4.14 Mann / Thm 4.19 (F(M(G)) class ≤ 4).
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch04.card_centralizer_lt_card_centralizer_commutator
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.commutator_mannSubgroup_le_center
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch04.nilpotencyClass_mannSubgroup_le_of_centralizer_eq_self
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch04.centralizer_eq_self_of_maximal_abelian_normal_of_isNilpotent
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.nilpotencyClass_mannSubgroup_le_of_isNilpotent
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.nilpotencyClass_map_fitting_mannSubgroup_le

-- Ch.3 §3E Hartley-Turull クラスタ: Lem 3.32 / Lem 3.33 / Thm 3.31 / Thm 3.34.
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch04.card_inf_fixedSubgroup_of_aInvariant_sylow
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch04.exists_equivariant_equiv_of_card_fixedPoints_eq
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.exists_abelian_fixedPoint_replacement
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch04.exists_orbit_card_mul_of_coprime_orbit_card

-- Ch.3 (Split Extensions): Thm 3.12 Schur-Zassenhaus conjugacy ⭐⭐⭐ **FT クリティカル**
-- N ⊴ G finite, (|N|, |G:N|) = 1, IsSolvable N or IsSolvable (G/N) ⇒
-- any two complements of N are conjugate by an element of N.
#assert_only_allowed_axioms Subgroup.IsComplement'.exists_conj_of_coprime

-- Ch.3 (Split Extensions): Thm 3.14 Hall-C ⭐⭐⭐ **FT クリティカル**
-- G finite solvable, π set of primes, H K both π-Hall ⇒ ∃ g, H^g = K.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.hall_C

-- Ch.3 (Split Extensions): Thm 3C.1 Hall-D (Wielandt) — π-subgroup ⊆ Hall π-subgroup.
-- G finite solvable, U a π-subgroup ⇒ ∃ Hall π-subgroup H with U ≤ H. (BG Cor 10.9 の前提)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.hall_D
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.exists_conj_le_of_isComplement'_of_coprime

-- Ch.3 (Split Extensions): Hall ∩ normal — H が π-Hall, N ⊴ G ⇒ H ∩ N は N の π-Hall.
-- (BG Cor 10.9 で W ∩ M' / W ∩ M_σ が Hall になることに使う; unconditional)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.isHallSubgroup_subgroupOf_of_normal

-- Ch.3 (Split Extensions): Thm 3.36 cyclic extension existence (Phase 4 完成)
-- N, m > 0, a ∈ N, σ ∈ Aut(N) で σ a = a かつ σ^m = MulAut.conj a
--   ⇒ ∃ G ⊇ N (N ⊴ G), G/N cyclic of order m, generator g, g^m = a, x^g = σ x.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.cyclic_extension_exists

-- Ch.3 (Split Extensions): Thm 3.35 existence 半分 — matching data から拡大同型を構成
-- (uniqueness 半分 cyclic_quotient_extension_unique と合わせて 3.35 完結).
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.cyclic_quotient_extension_iso_exists

-- Ch.4 ForwardFromCh03 (Isaacs Ch.3 §3E Lemma 3.24(a) Glauberman fixed-point) ⭐
-- A acts on G via auto, A,G finite, (|A|,|G|)=1, A or G solvable.
-- A and G act on Ω with compatibility, G transitive ⇒ ∃ A-invariant α ∈ Ω.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.glauberman_fixed_point_exists

-- Ch.4 ForwardFromCh03 (Isaacs Ch.3 §3E Thm 3.27): A-invariant coset has C_G(A) elem
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.aInvariant_coset_mem_centralizer

-- Ch.4 ForwardFromCh03 (Isaacs Ch.3 §3E Cor 3.28) ⭐⭐⭐ **transitive blocker**
-- N ⊴ G A-inv, coprime + solvable, A-fixed coset gN ⇒ ∃ c ∈ C_G(A), cN = gN.
-- Ch.4 多数定理 (4.26, 4.28-30, 4.34-36, 4.38) の transitive 前提.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient

-- Ch.4 ForwardFromCh03 (Isaacs Ch.3 §3E Thm 3.23(a)): A-invariant Sylow ⭐ FT クリティカル
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.exists_aInvariant_sylow

-- Ch.4 ForwardFromCh03 (Isaacs Ch.3 §3E Cor 3.29): A trivial on G/Φ ⇒ A trivial on G
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.aFixed_quotient_frattini

-- Ch.4 ForwardFromCh03 (Isaacs Ch.3 §3E Cor 3.30 実用形): A faithful + trivial on G/Φ ⇒ trivial
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.aFaithful_quotient_frattini

-- Ch.4 ForwardFromCh03 (Isaacs Ch.3 §3E Lemma 3.24(b) Glauberman conjugacy): C_G(A) で結ぶ
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.glauberman_fixed_points_conj

-- Ch.4 ForwardFromCh03 (Isaacs Ch.3 §3E Thm 3.23(b)): A-invariant Sylow C_G(A)-conjugate
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.aInvariant_sylow_conj

-- Ch.4 ForwardFromCh03 (Isaacs Ch.3 §3E Cor 3.25): A-invariant p-subgroup ⊆ A-invariant Sylow ⭐
-- Tier 1 最後の残課題. 極大化 + 3.23(a) + Normalizer-grow-in-p-groups で完成 (2026-05-24).
#assert_only_allowed_axioms OddOrder.Isaacs.Ch04.aInvariant_pSubgroup_le_aInvariant_sylow

-- RepresentationTheory (Peterfalvi §3 root-bridge): the first orthogonality relation is
-- unconditional (discharges the row-orthogonality hypothesis of SecondOrthogonality.lean).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.characterTableRowOrthogonality_holds
-- RepresentationTheory: `|Irr G| ≤ |ConjClasses G|` (orthonormality ⇒ linear independence).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_irreducibleCharacter_le
-- RepresentationTheory: there are finitely many irreducible characters of a finite group.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.finite_irreducibleCharacter
-- RepresentationTheory (Singer, case-(9.7.b) entry): a faithful irreducible abelian action on an
-- `F_p`-module of order `p^q` is realized by multiplication on `GF(p^q)`, with no order
-- assumption on the acting group.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_galoisField_repr_of_faithful_irreducible
-- RepresentationTheory (Singer, commutativity as a hypothesis): an abelian group acting
-- faithfully + irreducibly on a finite 𝔽_p-module is cyclic with order dividing |M| - 1.
-- This is the `CommGroup`-instance-free Singer mechanism (Peterfalvi (12.12) / (14.2)(a) core),
-- realized via the quotient field `𝔽_p[E] ⧸ I`; it accepts BG Thm 2.6(a)'s commutativity output.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.isCyclic_and_card_dvd_of_faithful_irreducible_comm
#assert_only_allowed_axioms OddOrder.RepresentationTheory.mul_comm_monoidAlgebra_of_comm
-- Peterfalvi (9.7)(b) coprimality core: a finite abelian group acting faithfully + irreducibly on
-- a finite 𝔽_p-module, together with a fixed-point-free additive automorphism, has order coprime to
-- p - 1 (the 𝔽_p-scalars `𝔽ₚ*` meet the image trivially in the cyclic Singer units).  The cyclic
-- helper `coprime_card_of_inf_eq_bot_isCyclic` converts trivial intersection to coprime orders.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.coprime_card_of_inf_eq_bot_isCyclic
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.coprime_card_sub_one_of_faithful_irreducible_comm_fpf
-- Peterfalvi (12.12) irreducible-case core: an odd group acting faithfully + irreducibly on a
-- 2-dimensional 𝔽_p-space is cyclic with order dividing |V| - 1 = p² - 1 (BG Thm 2.6(a) +
-- the commutativity-free Singer mechanism).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.isCyclic_and_card_dvd_of_odd_two_dim_irreducible
-- Peterfalvi (12.12) Case-A core: a group acting faithfully on a 1-dimensional 𝔽_p-space is
-- cyclic with order dividing p - 1 (End of a line ≅ 𝔽_p, so E ↪ (ℤ/p)ˣ).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.isCyclic_and_card_dvd_of_faithful_one_dim
-- Peterfalvi (12.12) rep-theory core (combined): an odd FPF group acting on an 𝔽_p-space of
-- dim ≤ 2 is cyclic with |E| ∣ |V| - 1 (dim 1 / dim-2-reducible ⟹ Case A on the invariant line;
-- dim-2-irreducible ⟹ Case B).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.isCyclic_and_card_dvd_of_fpf_dim_le_two
-- Peterfalvi (12.12) rep-theory bridge (MulDistribMulAction form): an odd FPF group acting on an
-- elementary abelian p-group of 𝔽_p-dim ≤ 2 is cyclic with |E| ∣ |M| - 1 (lifts the dim≤2 core
-- from `Representation` to `MulDistribMulAction` via `Representation.ofDistribMulAction`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.isCyclic_and_card_dvd_of_fpf_mulDistribMulAction
-- Peterfalvi (12.12) rep-theory bridge (conjugation form): `E ≤ N_G(T)` acting FPF by conjugation
-- on an elementary abelian `T` of order `p` or `p²` (|E| odd, coprime to p) is cyclic with
-- |E| ∣ p-1 or p²-1.  The §8-free structural core (12.12) consumes (before the p+1 refinement).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.isCyclic_and_card_dvd_of_fpf_conj_elemAbelian
-- Peterfalvi (12.9) centralizer core: a noncyclic abelian group acting coprimely on a finite group
-- with nontrivial abelianization has a nonidentity element whose fixed subgroup escapes [K, K]
-- (BG Prop 1.16(1) on K/[K,K] + the coprime fixed-point lifting, Isaacs Cor 3.28).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.exists_ne_one_actionFixedBy_not_le_commutator
-- Peterfalvi (12.9) centralizer core, conjugation/ambient form: a noncyclic abelian `A ≤ G`
-- normalizing a coprime `K` with `⁅K, K⁆ ≠ K` has `x ∈ A^#` with `C_G(x) ⊓ K ⊄ ⁅K, K⁆`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.exists_mem_centralizer_inf_not_le_commutator
-- Peterfalvi (12.9) order-p centralizer witness (the §8-free heart of (12.9)): from the
-- counterexample data (P₀ abelian, coprime to K = M_F, normalizing K, K not perfect) there is
-- an order-p element x ∈ Ω₁(P₀)^# with C_K(x) ⊄ K' (centralizer core + order-p power).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.exists_orderP_centralizer_witness
-- General 5-type HasPeterfalviType conjugation-invariance (issue 2015): a maximal subgroup's
-- Peterfalvi type and its `M_s = mainSubgroup` are preserved under `MulAut G`.  Unblocks the
-- Sylow-conjugation step of Pf (8.17.a) `exists_second_maximal`.
#assert_only_allowed_axioms
  OddOrder.GroupTheory.hasPeterfalviType_pointwise_smul
#assert_only_allowed_axioms OddOrder.GroupTheory.mainSubgroup_pointwise_smul
-- Hall ⟹ contains Sylow: a `p`-Hall subgroup with `p ∣ |H|` contains a Sylow `p`-subgroup of `G`
-- (`v_p(|H|) = v_p(|G|)` since `p ∤ [G:H]`; `Sylow.ofCard`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.exists_sylow_le_of_hall
-- Pf (12.1)/(12.2.b): the genuine type-I family `S = {Ind_H^L θ}` (`H = L_F`) is closed under
-- complex conjugation (`Ind_H^L θ̄ ∈ S`), the `χ̄ ∈ S` input to (12.2.b).  Axiom-clean.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.Sset_closedUnderConjugate
-- Pf §3 (1.4) reconciliation core: difference-uniqueness for signed irreducible-character
-- differences.  `s • (a − b) = t • (c − d)` (a ≠ b, c ≠ d, s ≠ 0) forces the unordered pairs to
-- agree with the sign tracking orientation (a=c,b=d,s=t  or  a=d,b=c,s=−t).  Orthonormality +
-- left-linearity of `ClassFunction.inner`.  Reconciles per-φ `R₁(φ)` with the global (1.4) family
-- in (12.4) pin (a) `constituent_diff_tau_mem_span`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.irreducibleCharacter_signed_difference_uniqueness
-- Pf (12.4) pin (a) piece 3: the underlying irreducibles `μ_φ, ν_φ` of `R₁(φ)` lie in `ℤ[R(χ)]`
-- (`R₁(φ).imageSet = {ε·μ, −ε·ν} ⊆ R(χ)`, `ε = ±1`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.R1cdi_muNu_mem_span_Rset
-- Pf (12.4) pin (a) piece 1 (global (1.4) coherence): the conjugate-closed constituent set is a
-- single coherent family under the Dade isometry `τ` — uniform sign `ε` + injection `μ` into `Irr G`
-- with `τ(α−β)=ε·(μ α−μ β)`.  `isometry_difference_pair_structure` on the constant-degree family.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.exists_uniform_image_of_constituents
-- Pf (12.4) pin (a): `(φ₁−φ₂)^τ ∈ ℤ[R(χ)]` for constituents `φ₁,φ₂ ∈ S(χ)`.  Reconciles the global
-- (1.4) family with the per-φ blocks `R₁(φ)` via difference-uniqueness.  Genuine; no longer sorried.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.constituent_diff_tau_mem_span
-- Pf (1.10.b) cyclotomic congruence (field form): in a `p`-th cyclotomic field, an integer `n` with
-- `n = (ζ-1)·a` (`a` integral) has `p ∣ n` (norm argument `N(ζ-1)=p`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.int_dvd_of_zeta_sub_one_dvd
-- Pf (1.10.b) **ℂ-form** (global algebraic integers, the FT-usable form): for `p` prime, `ε` a
-- primitive `p`-th root, an integer `n` with `(n:ℂ) = (1-ε)·z` (`z` any algebraic integer) has
-- `p ∣ n`.  Via `∏(1-ε^k)=p` + each `(1-ε^k)∣(1-ε)∣n` ⟹ `p∣n^{p-1}`, descend to ℤ.  Used by
-- (12.16)/(13.5) directly (no specific field needed; matches Coq `Z[η]` formulation).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd
-- (1.10.b) supporting: `1-ε^k` and `1-ε` are associates (`1-ε = (1-ε^k)·w`, `w` integral).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.one_sub_pow_dvd_one_sub
-- (1.10.b) supporting: a rational integer `a` with `(a:ℂ)=(b:ℂ)·W` (`W` integral, `b≠0`) has `b∣a`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.int_dvd_of_intCast_eq_mul_isIntegral
-- Pf (1.10.a) linear-char core: for a linear character `α` of a finite group, `x^p=1` element `x`,
-- `α(xy)-α(y) = (1-ε)·z` with `z` an algebraic integer (`α(x)=ε^k`, `α(y)` a root of unity).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.exists_integral_linearChar_apply_sub
-- Pf (1.10.a) full: for a virtual character `χ ∈ ℤ[Irr A]` of a finite ABELIAN group `A`, an
-- `x^p=1` element `x`, `χ(xy)-χ(y) = (1-ε)·z` with `z` an algebraic integer (submodule framing over
-- the linear-char core + `exists_linearIrreducibleCharacter_eq_of_isMulCommutative`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.exists_integral_zirr_apply_sub
-- Pf (1.10.a) G-form: for a virtual character `ψ ∈ ℤ[Irr G]` of ANY finite group, `x^p=1` and `y`
-- COMMUTING with `x`, `ψ(xy)-ψ(y) = (1-ε)·z`.  Reduce to the abelian subgroup `A=⟨x,y⟩` via
-- `restrict_mem_ZIrr` + `exists_integral_zirr_apply_sub`.  Directly usable by (12.16)/(13.5).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute
-- [Isaacs] Lemma 3.14 / Pf (13.9.b) ANT core: an algebraic integer `α : ℂ` fixed by every ring
-- automorphism `σ : ℂ ≃+* ℂ` is a rational integer (works inside the splitting field `ℚ(rootSet)`,
-- Galois correspondence + `ℤ` integrally closed in `ℚ`).  Feeds the field-norm-`≥ 1` step of (13.9.b).
#assert_only_allowed_axioms OddOrder.Algebra.exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed
-- [Isaacs] 3.14 support: every `σ : ℂ ≃+* ℂ` acts as a uniform power `(· ^ k)` (`k` coprime `n`) on
-- the `n`-th roots of unity — the converse of `exists_complexRingEquiv_pow_of_rootsOfUnity`.
#assert_only_allowed_axioms OddOrder.Algebra.exists_pow_of_complexRingEquiv
-- [Isaacs] 3.14 character bridge: for a cyclic-closed `Finset A` (closed under `x ↦ x^k`, `k` coprime
-- `|G|`), `∏_{x∈A} χ(x)` is a rational integer (algebraic integer fixed by all `σ`, via (1.9)
-- `σ(χ x)=χ(x^k)` + reindex).  Its nowhere-zero form gives `∏_{x∈A} ‖χ(x)‖² ≥ 1` (field-norm `≥ 1`).
#assert_only_allowed_axioms OddOrder.Algebra.exists_int_prod_character_of_cyclicClosed
#assert_only_allowed_axioms OddOrder.Algebra.one_le_prod_normSq_character_of_cyclicClosed
-- Pf (12.4) pin (b) step 1: general TI-induction self-value — for a TI subset `A` rel. `L` and an
-- `A`-supported class function `α`, `Ind_L^G α` agrees with `α` on `A`.  Generalizes the TI-cyclic
-- `induce_apply_eq_self_of_mem_V` to arbitrary TI subsets (the value-half of "Dade map = Ind").
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.induce_apply_eq_self_of_mem_tiSubset
-- Pf (12.4) pin (b) step 2: for a trivial-stabilizer Dade hypothesis (`∀ a, H(a)=⊥`), induction
-- `Ind_L^G` IS the Dade map (generalizes `TICyclicHypothesis.isDadeMap_inducedDadeMap`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.isDadeMap_induce_of_forall_H_eq_bot
-- Pf (12.4) pin (b) step 3: on functions supported in a trivial-`H` sub-support `A₁ ⊆ A`, the
-- abstract Dade map of `hyp` equals `Ind_L^G` (restrict to `A₁` + step 2 + `IsDadeMap.unique`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.dadeMap_eq_induce_of_supported_on_trivial_H
-- Pf (12.4) pin (b) type-I bridge: for a type-I maximal `L`, on a function supported in a trivial-`H`
-- sub-support `A₁ ⊆ A(L)`, the type-I Dade isometry `τ` acts as `Ind_L^G` (instantiates step 3 at
-- `hyp.tau` via `dadeIntegralCharacterMap_apply_of_support`).  Axiom-clean (parameterized by A₁).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.typeI_tau_eq_induce_of_supported_trivial_H
-- (12.16) `π = ∅` case): a type-F/I maximal whose complement `U` is a Z-group (all Sylow cyclic)
-- is Frobenius with kernel `M_F`, via `IsZGroup.exponent_eq_card` + `typeF_frobenius_of_card_eq_exponent`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.typeF_frobenius_of_isZGroup_complement
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.typeI_frobenius_of_isZGroup_complement
-- Pf (12.8) minimal-counterexample existence: a nonempty prime set `π` yields a
-- `CounterexampleHypothesis` at its least element `p = Nat.find` (the `InPi` witness + `Nat.find_min'`
-- minimality).  The §8-free well-ordering step opening the minimal-counterexample analysis of (12.7).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.exists_counterexampleHypothesis
-- RepresentationTheory: completeness of irreducible characters — `f ⊥ Irr G ⇒ f = 0`
-- (regular representation + Maschke + Schur).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.classFunction_eq_zero_of_orthogonal
-- RepresentationTheory: `|Irr G| = |ConjClasses G|` (completeness ⇒ the reverse inequality).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_irreducibleCharacter_eq
-- RepresentationTheory: the irreducible characters span the class functions.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.span_irreducibleCharacter_eq_top
#assert_only_allowed_axioms OddOrder.RepresentationTheory.irreducibleCharacter_apply_inv
#assert_only_allowed_axioms OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul
-- RepresentationTheory (Peterfalvi §3, [Is] Thm 2.18/6.10): second (column) orthogonality is
-- unconditional — the `CharacterTableIndexing` and weighted-row-orthogonality inputs of the
-- matrix proof core are discharged for any `[Finite G]` (issue 0027 closed unconditionally).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.column_orthogonality_diagonal
#assert_only_allowed_axioms OddOrder.RepresentationTheory.column_orthogonality_conjugate
#assert_only_allowed_axioms OddOrder.RepresentationTheory.column_orthogonality_not_conjugate
-- RepresentationTheory: conjugacy-class representative/cardinality adapters used by
-- class-sum character formulae.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.conjClass_mk_out
#assert_only_allowed_axioms OddOrder.RepresentationTheory.conjClass_carrier_ncard_eq_natCard
-- RepresentationTheory: class-sum coefficient character formula used in BG App C.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.sum_classSumCoeff_mul_irreducibleCharacter_apply
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter
-- RepresentationTheory (Peterfalvi (1.5.d), Burnside degree-sum): the diagonal column relation
-- at `g = 1` gives `∑_{χ ∈ Irr G} χ(1)² = |G|` and, restricted to nontrivial characters,
-- `∑_{χ ≠ 1} χ(1)² = |G| - 1` (issue 0044 building block for §9 (7.8)).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.sumIrreducibleDegreeSq
#assert_only_allowed_axioms OddOrder.RepresentationTheory.sumNontrivialIrreducibleDegreeSq
-- RepresentationTheory (Peterfalvi (6.7.1), orbit-counting primitive): a finite group acting freely
-- (all stabilizers trivial / no non-identity element fixes a point) on a finite set divides its
-- cardinality. Free-action decomposition `β ≃ (β/Γ) × Γ`. This is the missing counting primitive
-- behind the fixed-point-free `P`-action of (6.7.1).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_dvd_of_stabilizer_eq_bot
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_dvd_of_no_nontrivial_fixed
-- RepresentationTheory (Peterfalvi (6.7.1), orbit-counting half): a subgroup `P ≤ G` acting
-- fixed-point-freely by conjugation on the pair set `Ω = {(u,v) ∈ C_i × C_j ∣ u·v ∈ C_s}` has
-- `|P| ∣ a_{ijs}|C_s|` (= `classSumCoeff Ci Cj Cs`). The residual content of (6.7.1) is the
-- group-theoretic verification of fixed-point-freeness (TI-subset + Sylow-in-`L`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_dvd_classSumCoeff_of_fixedPointFree
-- RepresentationTheory (Peterfalvi (6.7.1), p-element step): a p-element of `N_G(P)` lies in the
-- Sylow p-subgroup `P` (P is normal, hence the unique Sylow p in its normalizer).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.mem_sylow_of_mem_normalizer_of_isPGroup
-- RepresentationTheory (Peterfalvi (6.7.1), fixed-point-free hypothesis): under (6.7)'s setup
-- (P Sylow p in L = N_G(P), P^# TI-subset, Z ≤ P normal in L; C_i, C_j meet Z^#, C_s ∩ Z = ∅),
-- `P` acts fixed-point-freely by conjugation on `Ω = {(u,v) ∈ C_i × C_j ∣ u·v ∈ C_s}`. Combined
-- with `card_dvd_classSumCoeff_of_fixedPointFree` this gives the full (6.7.1) `|P| ∣ a_{ijs}|C_s|`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.fixedPointFree_classPair_of_isTISubset
-- RepresentationTheory (Peterfalvi §3 (1.1), [Is] Thm 6.32): Brauer's permutation lemma is
-- unconditional — `# real Irr = # real ConjClasses` for any `[Finite G]`. The conjugation
-- involution `χ ↦ χ̄` is discharged via dual-representation irreducibility (issue 0022 closed).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.brauer_permutation_lemma'
-- RepresentationTheory (Peterfalvi §3 (1.1), pointwise): in a finite group of odd order a
-- nontrivial irreducible character is not real (`χ̄ ≠ χ`). Unconditional parity core, the
-- common unblocker for §3 (1.1) and §9 (7.9).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
-- Peterfalvi §3 (1.1), conjugate-difference (nondegeneracy) form for §7: in a finite group of
-- odd order, the conjugate difference `χ - χ̄` of a nontrivial irreducible character is nonzero.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S03.conjugateDifference_ne_zero_of_ne_trivial_of_odd_card
-- Peterfalvi §3 (1.6.a), forward direction: for `A ⊴ G` with `A ≤ H`, if `A ⊆ Ker θ` (as a
-- subgroup of `H`) then `A ⊆ Ker (Ind_H^G θ)`.  Elementary from the value formula
-- `induce_apply_of_mem_normal_of_const`; the converse is [Is] Lemma 2.21 (not formalised).
-- (6.6) uses the contrapositive: `Z ⊄ Ker (Ind_H^G θ)` ⟹ `Z ⊄ Ker θ`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
-- Peterfalvi §3 (1.6.a), contrapositive form (the (6.6) `X`-characterization consumes this):
-- `Z ⊄ Ker (Ind_H^G θ)` ⟹ `Z ⊄ Ker θ`.  Literal contrapositive of the forward (1.6.a) lemma.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S03.not_subsetCharacterKernel_of_not_induce
-- Peterfalvi §3 (6.6) `X`-characterization, constituent-existence half (mmd 04.8 L76): every
-- `χ ∈ Irr G` is a constituent of `Ind_H^G θ` for some `θ ∈ Irr H` (`⟨Ind_H^G θ, χ⟩ ≠ 0`).
-- Frobenius reciprocity via the Clifford `LiesOver` bridge (`exists_liesOver` +
-- `inner_induce_ne_zero_iff_liesOver`); unconditional, no reference to a center `Z`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero
-- Peterfalvi §3 (6.6) G2.2, the keystone-driven residual: a constituent inherits a kernel
-- containment.  `‖χ(g)‖ ≤ χ(1)` (norm_irreducibleCharacter_le_natDegree, via the keystone bound)
-- + the equality case give: if `(∑ mᵢ χᵢ)(g) = (∑ mᵢ χᵢ)(1)` then every `χᵢ` (mᵢ ≠ 0) has
-- `g ∈ ker χᵢ`.  Closes the `needs-infra` piece flagged in notes/peterfalvi/s03.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S03.norm_irreducibleCharacter_le_natDegree
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq
-- Peterfalvi §3 (1.1), set form: in a finite group of odd order the set of nontrivial irreducible
-- characters contains no real class function. Discharges the `no_real_characters` field of the §7
-- coherence hypothesis (Hypothesis (5.2)(a)) directly from oddness.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S03.hasNoRealCharacters_nontrivialIrreducibleClassFunctions
-- Peterfalvi §3 (1.2): if `H ⊴ G`, `χ ∈ Irr G` has `H ⊄ Ker χ`, and `C_H(g) = 1`, then `χ(g) = 0`.
-- Second (column) orthogonality on `G` and on `G ⧸ H` + the value-preserving inflation bijection
-- `Irr(G ⧸ H) ≃ {χ | H ⊆ ker χ}` + the centralizer embedding `|C_G(g)| ≤ |C_{G ⧸ H}(ḡ)|`; the
-- resulting squeeze on `∑ |χ(g)|²` forces the `H ⊄ ker` terms to vanish.  Feeds Peterfalvi (4.7).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot
#assert_only_allowed_axioms OddOrder.Peterfalvi.S03.card_centralizer_le_card_centralizer_quotient
-- Peterfalvi (4.7), support form (core + induced): for `χ ∈ Irr K` with `H ⊄ Ker χ` (`H ⊴ K` the
-- (4.6.c) normal subgroup), `Supp χ ⊆ A ∪ {1}` and `Supp (Ind_K^L χ) ⊆ A ∪ {1}`.  (1.2) applied to
-- `χ` on `K` + the (4.6.d) `A`-cover (core), then `L`-conjugacy invariance of `A` (induced).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S06.mem_A_of_apply_ne_zero_of_not_subset_characterKernel
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S06.apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S06.induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel
-- Character-kernel translation invariance: `g ∈ Ker χ ⟹ χ(x·g) = χ(x)` (diagonalization keystone
-- `rep_eq_id_of_character_eq_one` forces `ρ g = id`).  Feeds the Peterfalvi (4.7) `j ≥ 1` kernel
-- step (and any future use of kernel elements inside character values).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.apply_mul_eq_of_mem_characterKernel
-- Peterfalvi (4.7), `j ≥ 1` half: `H ⊄ Ker χ_j` for a nontrivial column `χ₂ ≠ 1` (the `ω_{0j}`
-- argument via the (4.3.c) value identity on `V = W − W₂` + kernel translation invariance), and
-- the resulting supports `Supp χ_j, Supp μ_j ⊆ A ∪ {1}`.  Completes Theorem (4.7); feeds the
-- (5.3.b) R-producer for the reducible certain-type characters (the (6.8.3) break-pair input).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S06.Hypothesis.not_subset_characterKernel_chiRestrict_of_ne_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.not_subset_characterKernel_chiRestrict
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.chiRestrict_apply_eq_zero_of_not_mem_union
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S06.induce_chiRestrict_apply_eq_zero_of_not_mem_union
-- Peterfalvi (4.8), step (1): equal-degree certain-type characters share their column sign
-- (`μ_{ij}(1) = μ_{ik}(1) ⟹ δ_j = δ_k`).  Via the (4.3.d) degree congruence `μ(1) ≡ δ (mod w₁)`
-- twice and `w₁ ≥ 3` (`W₁ ≠ 1` of odd order): `w₁ ∣ (δ_j − δ_k)` with `|δ_j − δ_k| ≤ 2 < w₁`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_sign_eq_of_degree_eq
-- Peterfalvi (4.8), step (2): equal-degree certain-type characters agree on `W₁`
-- (`certainType_apply_eq_of_mem_W1`), via the column-independence of `ω` on `W₁`
-- (`chiColumn_apply_of_mem_W1`: the `W₂`-projection `wSnd` is trivial on `W₁`) + step (1).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.chiColumn_apply_of_mem_W1
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_apply_eq_of_mem_W1
-- Peterfalvi (4.8), conclusion (1): `Supp(μ_{ij} − μ_{ik}) ⊆ A₀ = A ∪ V^L`.  `z = 1` excluded by
-- equal degree; `z ∈ K` lands in `A` via (4.7) (`μ_{ij}|_K = μ_{ik}|_K = χ` off `A ∪ {1}`); and
-- `z ∈ L − K` lands in `V^L` via (2.1) (`mem_compl_conj_into_W`: `z` conjugate to `xy ∈ W − W₂`,
-- whose image lies in `tic.V = ↑W \ ↑W₂`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_diff_supp_subset_A0
-- Peterfalvi (4.8) conclusion (3) foundation: the `σ_G` image `ω_{ij}^σ ∈ CF(G)` (`ticVdiff`,
-- the `V = W − (W₁ ∪ W₂)` TI-cyclic), its value on `V`, and the certain-type Dade isometry `τ`
-- preserving values on `A₀`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_apply_of_mem_V
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.tau_toDadeMap_apply_of_mem
-- Peterfalvi (4.8), step (4): the two sides agree on `V` (`(μ_{ij} − μ_{ik})^τ(v) =
-- δ_j(ω_{ij}^σ(v) − ω_{ik}^σ(v))` for `v ∈ V`), the `hψ` input to the (3.8) trichotomy endgame.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_diff_dade_apply_eq_of_mem_V
-- Peterfalvi (4.8), steps (5)/(6) inputs to the (3.8) trichotomy endgame: `‖φ‖² = 2` (τ isometry +
-- (4.1) distinctness), `NC(φ) ≤ 2` (norm-2 ⟹ two constituents, each `≤ 1` against the χ-family),
-- and `ω_{ij}^σ = χ_{P_{ij}}` (the σ-image is a χ-family member, identifying the δ-term positions).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_diff_dade_inner_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.sigmaNC_dade_le_two
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam
-- Peterfalvi (4.8), step (7) input: the σ-coefficients of φ lie in `{0, ±1}` (norm-2 ⟹ two
-- constituents `ε_α·α + ε_β·β`, each χ_{pq} matching at most one).  The `|·| ≤ 1` bound (beyond
-- NC ≤ 2) excludes the `w₂ = 3` row case in the trichotomy endgame.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.sigmaCoeff_dade_eq_zero_or_one
-- Peterfalvi (4.8), assembly: the σ-coefficient grid of `ψ = φ − δ_j(ω_ij^σ − ω_ik^σ)` is
-- `⟨φ, χ_pq⟩ − δ_j([P_ij = pq] − [P_ik = pq])` (the δ-part hits exactly the two positions P_ij, P_ik).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.sigmaCoeff_psi_eq
-- Peterfalvi (4.8), conclusion (3) from trichotomy case (a): if every σ-coefficient of ψ vanishes
-- then ψ = 0, i.e. (μ_ij − μ_ik)^τ = δ_j(ω_ij^σ − ω_ik^σ).  ⟨ψ,ω_ij^σ⟩=0 pins ⟨φ,ω_ij^σ⟩=δ_j,
-- ⟨φ,ω_ik^σ⟩=−δ_j; then ‖ψ‖² = ⟨ψ,φ⟩ = 2 − 2 = 0 by positive-definiteness.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_diff_dade_eq_of_all_sigmaCoeff_zero
-- Peterfalvi (4.8), conclusion (3) — the FT-critical isometry identity:
-- (μ_ij − μ_ik)^τ = δ_j(ω_ij^σ − ω_ik^σ).  ψ vanishes on V (step 4) ⟹ separable σ-grid with
-- NC ≤ 4 < 2·min(w₁,w₂); the (3.8) trichotomy (in the orientation given by coprimality of w₁,w₂)
-- leaves only all-zero (constant column/row excluded by grid_no_constant_column/row), whence ψ = 0.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_diff_dade_eq
-- Peterfalvi (4.9)(b), summed isometry: the Dade map is additive over finite sums of supported
-- class functions (`tau_toDadeMap_sum`, via the (2.5) uniqueness `IsDadeMap.unique` reducing the
-- abstract `τ` to the genuine `ℂ`-linear `dadeLinearMap`); summing (4.8) conclusion 3 over the rows
-- `0 ≤ i < w₁` gives `(μ_j − μ_k)^τ = δ_j ∑_i (ω_ij^σ − ω_ik^σ)`, the (4.9)(b) τ-agreement on Z[T,A].
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.tau_toDadeMap_sum
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_diff_dade_sum_eq
-- Peterfalvi (4.9) degree bridge: every `μ_ij` in column `j` shares the degree `μ_0j(1)`
-- (`columnFamily_mu_apply_one_eq`, from `(μ_ij − μ_0j)(1) = 0`), so the column-sum degree equality
-- `μ_j(1) = μ_k(1)` (`= ∑_i μ_ij(1) = ∑_i μ_ik(1)`) gives the per-row equalities
-- (`forall_columnFamily_mu_apply_one_eq_of_sum_eq`), restating the summed isometry under the `T`
-- membership condition (`certainType_diff_dade_sum_eq_of_degree`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.columnFamily_mu_apply_one_eq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.forall_columnFamily_mu_apply_one_eq_of_sum_eq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_diff_dade_sum_eq_of_degree
-- Peterfalvi (4.9)(b), the isometry property: the σ-image column sums `∑_i ω_ij^σ` (in CF(G)) and
-- the certain-type column sums `μ_j = ∑_i μ_ij` (in CF(L)) carry the same Gram matrix `w₁·δ_jk`
-- (`certainTypeOmegaSigma_sum_inner` / `columnFamily_mu_sum_inner`, both via per-element
-- orthonormality: `certainTypeOmegaSigma_inner` from σ-isometry + ω-orthonormality and grid-index
-- distinctness `omegaProdCharTic_eq_iff`; the μ-side from `columnFamily` injectivity/cross-column
-- distinctness).  Hence `μ_j ↦ δ_k ∑_i ω_ij^σ` is an isometry (δ_k² = 1), which is (4.9)(b).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.omegaProdCharTic_eq_iff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_sum_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_omega_sum_isometry
-- Peterfalvi (4.9)(a) conjugation foundation: the complex conjugate of a linear character `ω(χ)` is
-- `ω(χ⁻¹)` (`galoisMap_conj_omega`; values are roots of unity, where `z̄ = z⁻¹`), so the conjugate of
-- a certain-type σ-image `ω_ij^σ` is the σ-image of the inverse grid character `ω((P_ij)⁻¹)`
-- (`certainTypeOmegaSigma_conj`, via the (3.9) Galois commutation `sigma_mapRingEquiv_comm`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.galoisMap_conj_omega
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_conj
-- (4.9)(a) grid-index conjugation: the inverse grid character is the grid character at the conjugate
-- index (`omegaProdChar_inv` coordinatewise, `omegaProdCharTic_inv` with column `χ₂⁻¹`, row `rowInv`),
-- so the conjugate of a σ-image is the σ-image at the conjugate index `(ω_ij^σ)̄ = ω_{i'j'}^σ`
-- (`certainTypeOmegaSigma_conj_eq`).  This is the σ-side of Peterfalvi's `ω̄_ij = ω_{i'j'}`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.omegaProdChar_inv
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.omegaProdCharTic_inv
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_conj_eq
-- (4.9)(a) L-side conjugation closure: the column source character conjugates to the conjugate-index
-- character (`chiColumn_conj`: χ_{ij}̄ = χ_{i'j'}), and the L-side σ-isometry `σ_L` intertwines it
-- (`sigma_chiColumn_conj`: σ_L(ω_ij)̄ = σ_L(ω_{i'j'})).  With (4.3.b) `sigma_chiColumn_eq_certainType`
-- (σ_L(ω_ij) = δ_j μ_ij) this gives the L-character bridge δ_j μ_ij̄ = δ_{j'} μ_{i'j'} of (4.9)(a).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.chiColumn_conj
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.sigma_chiColumn_conj
-- (4.9)(a) the L-character conjugation bridge δ_j·μ_{ij}̄ = δ_{j'}·μ_{i'j'} (`certainType_mu_conj_bridge`):
-- complex conjugation of (4.3.b) `σ_L(ω_{ij}) = δ_j·μ_{ij}`, using `sigma_chiColumn_conj` + (4.3.b) on
-- the left and `mapRingEquiv_zsmul` on the right (δ_j ∈ ℤ).  The heart of (4.9)(a).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_mu_conj_bridge
-- (4.9)(a) `μ_ij̄ = μ_{i'j'}` (`certainType_mu_conj_eq`): pairing the bridge δ_j·μ_ij̄ = δ_{j'}·μ_{i'j'}
-- with μ_{i'j'} gives δ_j·⟨μ_ij̄, μ_{i'j'}⟩ = δ_{j'} ≠ 0, so the (0/1) inner product of the two
-- irreducibles is 1, forcing equality.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_mu_conj_eq
-- (4.9)(a) `μ̄_j = μ_{j'}` (`certainType_columnSum_conj`): the conjugate of the column sum
-- `μ_j = ∑_i μ_ij` is the conjugate column `μ_{j'} = ∑_i μ_{ij'}` (`j' = χ₂⁻¹`).  mapRingEquiv conj is
-- additive, each `μ_ij̄ = μ_{i'j'}`, and `i ↦ rowInv i` is a permutation (`rowInvEquiv`, involution).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_columnSum_conj
-- (4.9)(a) the conjugate column is a new certain-type character: `χ₂⁻¹ ≠ χ₂` (`column_inv_ne_self`,
-- the column character group has odd order `= |W₂|`, no involutions), so `μ̄_k = μ_{k'}` is orthogonal
-- to `μ_k` (`columnFamily_mu_sum_inner`), whence `μ̄_k ≠ μ_k` (`certainType_columnSum_conj_ne`) — the
-- nonvanishing `0 ≠ μ̄_k − μ_k ∈ Z[T,A]` input to the (4.9)(a) coherence.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.column_inv_ne_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainType_columnSum_conj_ne
-- Peterfalvi (2.1): the coprime-coset structure lemma.  `g` normalizes `H` with `(o(g), |H|) = 1`
-- ⟹ every element of `Hg` is `H`-conjugate to an element of `C_H(g)·g`.  Proof: a uniform Bézout
-- exponent `e` (`≡1 mod o(g)`, `≡0 mod |H|`) collapses `(w·g)^e = g` for `w ∈ C_H(g)`, making the
-- conjugation map `(H ⧸ C_H(g)) × C_H(g) → Hg` injective; equal cardinality forces surjectivity.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.coset_conj_into_centralizer_coset
-- (2.1) applied to `L = K ⋊ W₁`: every `z ∈ L − K` is `L`-conjugate to `x·y` (`x ∈ W₁^#`, `y ∈ W₂`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.Hypothesis.mem_compl_conj_into_W
-- RepresentationTheory ⭐ **KEYSTONE** (Peterfalvi §2 / [Is] Thm 2.8 系): the character of *any*
-- finite-dim complex representation of a finite group is a virtual character (`∈ ℤ[Irr G]`).
-- Strong `finrank` induction: Maschke splits a reducible rep into smaller summands whose characters
-- add (`character_add_of_isCompl` = `trace_conj' + trace_prodMap'`); the irreducible base case is
-- `exists_isIrreducibleCharacter_eq`. Unblocks `induce`/`restrict ∈ ℤ[Irr]` ⇒ Dade (2.6.b)/§9.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.character_mem_ZIrr
-- RepresentationTheory (Peterfalvi (2.6.b) prerequisites): restriction and induction preserve
-- virtual characters. `restrict ∈ ℤ[Irr]` reduces (via span induction) to the keystone
-- `character_mem_ZIrr` applied to `ρ.comp H.subtype`; `induce ∈ ℤ[Irr]` then follows from
-- numerical Frobenius reciprocity (`inner_induce_eq_inner_restrict`) + integer Fourier
-- coefficients (`inner_mem_ZIrr_int`) + completeness (`classFunction_eq_zero_of_orthogonal`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr
-- RepresentationTheory (Peterfalvi §7 (5.4) projection primitive): integral orthogonal projection
-- of a virtual character `φ ∈ ZIrr G` onto a finite ZIrr-orthonormal family `R`.  Integer
-- coefficients `c α = ⟨φ, α⟩` (integral because `R ⊆ ZIrr G`, `inner_mem_ZIrr_int`); residual
-- `Y = φ − ∑ c•α ⊥ R` by orthonormal coefficient recovery.  Supplies the `X`/`Y`/`coeff` fields of
-- `CharacterPsiDecomposition` (the (5.4)/(5.5)/(5.6.1) projection content), consumed by
-- `CharacterPsiDecomposition.ofProjection`.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.ClassFunction.exists_intProjection_of_orthonormal_ZIrr
-- RepresentationTheory (Peterfalvi (2.10.3) transversal value): the induction sum at `g`
-- collapses to a sum over only those `x` with `x⁻¹ g x ∈ H` (off-support terms vanish via
-- `induceTerm_of_not_mem`), in unscaled (`induceSum`) and normalized (`induce`) form.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induceSum_apply_eq_sum_filter
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induce_apply_eq_sum_filter
-- RepresentationTheory (complex conjugation): induction commutes with conjugating values in `ℂ`;
-- used to show `Y = S(H')` is closed under complex conjugation in Peterfalvi (6.8).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induceTerm_conjStar
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induceSum_conj
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induce_conj
-- RepresentationTheory ([Is] Thm 6.34 degree part): the induced class function at `1` is
-- `[G : H] · θ(1)`.  All `|G|` conjugates `x⁻¹ · 1 · x = 1` lie in `H`, so every summand is
-- `θ(1)`; dividing by `|H|` and using `|G| = [G:H]·|H|` (`Subgroup.index_mul_card`) leaves `[G:H]`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induce_apply_one
-- RepresentationTheory (induction support): if H is normal, then conjugates into H are exactly
-- elements of H, so Ind_H^G θ vanishes outside H and is supported on H.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.conjugatesInto_eq_of_normal
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induce_eq_zero_of_not_mem_normal
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
-- RepresentationTheory (Peterfalvi (1.6.a) value core): for a normal subgroup `A ⊴ G` with
-- `A ≤ H` on which `θ` is constant `= c`, every term of the induction sum at `a ∈ A` is `c`
-- (conjugates `x⁻¹ a x` stay in `A ≤ H` by normality), so `Ind_H^G θ(a) = |G|·c·|H|⁻¹`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induce_apply_of_mem_normal_of_const
-- RepresentationTheory (Peterfalvi §3 (1.6.b)-bridge): `χ` is a constituent of `Ind_H^G θ`
-- (`⟨Ind θ, χ⟩ ≠ 0`) iff `χ` lies over `θ`.  Numerical Frobenius reciprocity
-- (`inner_induce_eq_inner_restrict`) packaged into `LiesOver`; the constituent multiplicity
-- `⟨θ, Res χ⟩` is the conjugate of the restriction multiplicity `⟨Res χ, θ⟩`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver
-- RepresentationTheory (lies-over existence): every `χ ∈ Irr G` lies over some `θ ∈ Irr H`.
-- Completeness: `Res^G_H χ ≠ 0` (value `χ(1) > 0` at `1`), so it is not orthogonal to all
-- irreducibles of `H` (`classFunction_eq_zero_of_orthogonal`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
-- RepresentationTheory (Peterfalvi (2.10.1) L-conjugacy invariance): inducing from a conjugate
-- subgroup `H^ℓ = H.map (MulAut.conj ℓ)` with the transported class function `transportConj ℓ θ`
-- equals inducing from `H`.  Re-index the induction sum by `x ↦ x * ℓ` (`induceTerm_transportConj`);
-- the `|H^ℓ| = |H|` normalization factors agree by `Subgroup.card_map_of_injective`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induceSum_map_conj
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induce_map_conj
-- RepresentationTheory (Peterfalvi (2.9)): pullback `φ ∘ f` along a group hom `f : H →* G`
-- preserves virtual characters (the "Res along a homomorphism" generalization of
-- `restrict_mem_ZIrr`).  Same span-induction proof via `character_mem_ZIrr (ρ.comp f)`; this
-- is the `α_B = α ∘ f_B ∈ ℤ[Irr M(B)]` step of the Dade-map construction.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.compHom_mem_ZIrr
-- RepresentationTheory (Peterfalvi (1.5.a), inertia/coset well-definedness): conjugation by an
-- element of the normal subgroup `H` acts trivially on class functions of `H` (`θ^g = θ` for
-- `g ∈ H`).  `conjBy g θ` evaluates `θ` at the `H`-conjugate `⟨g⟩ * h * ⟨g⟩⁻¹`, and class
-- functions are `H`-conjugacy invariant.  This is what makes `θ^x = θ^y ⇔ y ∈ I(θ)x`, i.e.
-- `conjBy w θ` constant on the coset `wH` in the Mackey restriction formula.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.conjBy_eq_self_of_mem
-- RepresentationTheory (Peterfalvi §2 orthogonality): class functions with disjoint supports
-- are orthogonal (`⟨φ, ψ⟩_G = 0`). Each summand `φ g · star (ψ g)` vanishes since `g` lies
-- outside at least one support. Basic vanishing for the Dade isometry / §9 coherence arguments.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.inner_eq_zero_of_disjoint_support
-- RepresentationTheory (Isaacs §3 (3.6)/(3.7); Peterfalvi (6.7.2)/(6.7.3)): the class-sum algebra.
-- `classSum_mul` expresses `C_i · C_j = ∑_s m_s · C_s` with the per-element factorization counts
-- `m_s` (constant on each class), and `centralCharacterOfRep_classSum_mul` transports this through
-- the central character `ω_ρ`.  The keystone `centralCharacterOfRep_classSum_isIntegral`: `ω_ρ(C)`
-- is an algebraic integer (module-finite ℤ-subalgebra of ℂ generated by the `ω_ρ(C_s)`), the
-- structure-constant integrality used in the `mod |P|` congruence (6.7.3).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.classSum_mul
#assert_only_allowed_axioms OddOrder.RepresentationTheory.centralCharacterOfRep_classSum_mul
#assert_only_allowed_axioms OddOrder.RepresentationTheory.centralCharacterOfRep_classSum_isIntegral
-- Peterfalvi (6.7.2) (product rule mod |P|): `ψ(1)·ω(C_i)·ω(C_j) ≡ ∑_{C_s∩Z≠∅} ψ(1)·a_{ijs}·ω(C_s)`,
-- i.e. classes `C_s` disjoint from `Z` drop out modulo `m` once `m ∣ a_{ijs}|C_s|` for those classes
-- (the (6.7.1) input, `card_dvd_classSumCoeff_of_fixedPointFree`).  Each dropped term equals
-- `(a_{ijs}|C_s|)·χ_ρ(C_s.out)` (`character_one_mul_coeff_mul_centralChar`, via the pair-count
-- identity `coeff_mul_card_eq_classSumCoeff`), an algebraic-integer multiple of `m`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.coeff_mul_card_eq_classSumCoeff
#assert_only_allowed_axioms OddOrder.RepresentationTheory.character_one_mul_coeff_mul_centralChar
#assert_only_allowed_axioms OddOrder.RepresentationTheory.centralCharacterOfRep_classSum_mul_cong
-- Peterfalvi (6.7.2) geometric form: the same congruence with the abstract divisibility hypothesis
-- discharged from the (6.7) setup (Sylow `P`, `Z ⊴ N_G(P)`, `P^#` TI) via (6.7.1)
-- (`fixedPointFree_classPair_of_isTISubset` + `card_dvd_classSumCoeff_of_fixedPointFree`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.centralCharacterOfRep_classSum_mul_cong_of_isTISubset
-- Peterfalvi (6.7.3) structure-constant atoms (the identity-class coefficients `a_{ij0}`):
-- `classSumCoeff_one_eq_zero` is `a_{110} = 0` (no pair `(u,u⁻¹)` with both `u, u⁻¹ ∈ C₁` when
-- `⟦z⁻¹⟧ ≠ ⟦z⟧`), and `classSumCoeff_one_eq_card` is `a_{120} = |C₁|` (the pairs with product `1`
-- in `C₁ × C₁⁻¹` are exactly `(u, u⁻¹)`, `u ∈ C₁`).  These discharge two of the (6.7.3) atoms.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.classSumCoeff_one_eq_zero
#assert_only_allowed_axioms OddOrder.RepresentationTheory.classSumCoeff_one_eq_card
-- The `z`-keyed instances consumed by (6.7.3): `classSumCoeff_self_one_eq_zero` (`a_{110} = 0`
-- with `C₁ = ⟦z⟧`, sole hypothesis the real-class atom `⟦z⁻¹⟧ ≠ ⟦z⟧`) and
-- `classSumCoeff_self_inv_one_eq_card` (`a_{120} = |C₁|` with `C₂ = ⟦z⁻¹⟧`, *unconditional* — the
-- inverse-class membership `mk u = ⟦z⟧ → mk u⁻¹ = ⟦z⁻¹⟧` is `mk_inv_eq_of_mk_eq`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.mk_inv_eq_of_mk_eq
#assert_only_allowed_axioms OddOrder.RepresentationTheory.classSumCoeff_self_one_eq_zero
#assert_only_allowed_axioms OddOrder.RepresentationTheory.classSumCoeff_self_inv_one_eq_card
-- Peterfalvi (6.7.3) real-class atom (TI-reduction, `RealClassTISubset.lean`): the sole remaining
-- hypothesis of `classSumCoeff_self_one_eq_zero` — `⟦z⁻¹⟧ ≠ ⟦z⟧` — discharged from the (6.7) setup
-- (`P ∈ Syl_p`, `L = N_G(P)` of *odd* order, `P^#` TI-subset).  `not_isConj_inv_of_isTISubset`
-- proves `¬ IsConj z⁻¹ z` (a `G`-conjugator of `z⁻¹` to `z` lands in `L` by TI, so `z` is
-- `L`-conjugate to `z⁻¹`, forcing `z = 1` by `eq_one_of_isConj_inv_of_odd_card`); the class form
-- `mk_inv_ne_self_of_isTISubset` is what plugs into `classSumCoeff_self_one_eq_zero`.  This is
-- Peterfalvi's "since `|L|` is odd, `z⁻¹` is not conjugate to `z` in `G`" ((6.7.3), proof opening).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.not_isConj_inv_of_isTISubset
#assert_only_allowed_axioms OddOrder.RepresentationTheory.mk_inv_ne_self_of_isTISubset
-- The `a_{110} = 0` structure constant with its real-class hypothesis discharged from the (6.7)
-- setup: `classSumCoeff_self_one_eq_zero_of_isTISubset` feeds `mk_inv_ne_self_of_isTISubset` into
-- `classSumCoeff_self_one_eq_zero`, so the `a_{110} = 0` input to (6.7.3) is hypothesis-free under
-- `P ∈ Syl_p(G)`, `Odd |N_G(P)|`, `P^#` TI-subset, `z ∈ P ∖ {1}`.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.classSumCoeff_self_one_eq_zero_of_isTISubset
-- Peterfalvi (6.7.3) coprimality atom `(|C₁|, p) = 1`: `card_class_eq_index_centralizer` is the
-- orbit-stabilizer identity `|⟦z⟧| = [G : C_G(z)]` (conjugation action of `ConjAct G`), and
-- `coprime_card_class_card_sylow` derives `IsCoprime |⟦z⟧| |P|` from `P ≤ C_G(z)` (so
-- `[G:C_G(z)] ∣ [G:P]`, `p ∤ [G:P]`) and `|P| = p^k`.  Discharges the last (6.7.3) atom.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_class_eq_index_centralizer
#assert_only_allowed_axioms OddOrder.RepresentationTheory.coprime_card_class_card_sylow
-- Peterfalvi (6.7.3) central-character value on the identity class: `ω_ρ(⟦1⟧) = 1` (the identity
-- class is the singleton `{1}`, so `ω = 1·χ(1)/χ(1) = 1`).  This is the `ω(C₀) = 1` ingredient of
-- the right-hand-sum collapse `∑ → ψ(1)(a_{ij0} + a_{ij}α)` in (6.7.2)/(6.7.3).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.centralCharacterOfRep_one
-- Peterfalvi (6.7.3) (`ψ(z) ≡ ψ(1) (mod |P|)`), the congruence-arithmetic assembly of the two
-- (6.7.2) instances at `(1,1)`/`(1,2)`: combine (transitivity) ⟶ substitute `ψ(1)α = |C₁|ψ(z)` and
-- cancel the coprime factor `|C₁|` (`Cong.intMul_cancel_left`) ⟶ multiply the `1_G` congruence
-- `a₁₁ ≡ 1 + a₁₂` by `ψ(z)` and subtract.  The group-theoretic atoms (`a_{110}=0`, `a_{120}=|C₁|`,
-- `z⁻¹` not `G`-conjugate to `z`, `ω(C_s)=α` constant) feed in as hypotheses (the (6.7.1) setup).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.peterfalvi_673_combine
#assert_only_allowed_axioms OddOrder.RepresentationTheory.peterfalvi_673_cancel
#assert_only_allowed_axioms OddOrder.RepresentationTheory.peterfalvi_673_final
#assert_only_allowed_axioms OddOrder.RepresentationTheory.peterfalvi_673
-- The explicit character-value form `|C| · χ_ρ(g) / χ_ρ(1) ∈ ℤ̄` (algebraic integer), obtained
-- from the keystone via `centralCharacterOfRep_classSum` + `sum_character_eq_card_mul` + `char_one`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.isIntegral_card_mul_character_div
-- RepresentationTheory (Isaacs §3 (3.7) preamble): character values χ_ρ(g) = trace(ρ g) are
-- algebraic integers — `ρ g` has finite order (`g^|G| = 1`), the charpoly splits over ℂ, the trace
-- is the sum of its roots, and each root μ is a root of unity (μ^|G| = 1, root of `X^|G| - 1`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.character_isIntegral
-- RepresentationTheory: a rational algebraic integer is an integer — `ℤ` is integrally closed (UFD),
-- so transferring `IsIntegral ℤ (q : ℂ)` down the injection `ℚ ↪ ℂ` yields `∃ n : ℤ, (q : ℂ) = n`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.isIntegral_rat_imp_int

-- Algebra (Peterfalvi, proof of (6.7), pp. 31–32): the algebraic-integer congruence `α ≡ β (mod n)`
-- on ℂ — `(α - β)/n ∈ ℤ̄`.  An additive congruence: reflexive/symmetric/transitive, closed under
-- addition (`Cong.add`) and under scaling one side by an algebraic integer (`Cong.smul_left`, the
-- multiplicative step of (6.7.2)/(6.7.3)).  Introduction forms `cong_of_exists_isIntegral`/`.of_int`.
#assert_only_allowed_axioms OddOrder.AlgInt.Cong.trans
#assert_only_allowed_axioms OddOrder.AlgInt.Cong.add
#assert_only_allowed_axioms OddOrder.AlgInt.Cong.smul_left
#assert_only_allowed_axioms OddOrder.AlgInt.cong_of_exists_isIntegral
#assert_only_allowed_axioms OddOrder.AlgInt.Cong.of_int
-- The "divide by |C₁|" cancellation of (6.7.3): a congruence `c·a ≡ c·b (mod n)` with `c` coprime
-- to `n` and `a`, `b` algebraic integers gives `a ≡ b (mod n)` (Bézout `u·c + v·n = 1`).
#assert_only_allowed_axioms OddOrder.AlgInt.Cong.intMul_cancel_left
-- RepresentationTheory (Isaacs Thm 3.11): for an irreducible complex representation ρ of a finite
-- group G, the degree χ_ρ(1) = dim V divides |G|.  The first orthogonality relation regrouped over
-- conjugacy classes expresses |G|/χ(1) = ∑_C ω_ρ(C)·χ((g_C)⁻¹) as a sum of products of algebraic
-- integers, hence a rational algebraic integer ⇒ integer (the three linked pieces above).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.sum_centralCharacter_mul_character_inv_mul_character_one
#assert_only_allowed_axioms OddOrder.RepresentationTheory.finrank_dvd_card
-- ClassFunction-level bridge: an irreducible character's value at 1 is the witnessing
-- representation's dimension, and (Isaacs Thm 3.11) that natural number divides |G|.  This recasts
-- `finrank_dvd_card` through `φ 1`, which is definitionally Peterfalvi's `characterDegree φ`.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.exists_finrank_charValue_one
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card
-- Peterfalvi-side consumer: the same divisibility on the `IrreducibleCharacter G` subtype, phrased
-- through `characterDegree` (= `χ 1`), the degree datum used throughout Peterfalvi §6.7.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S03.exists_natDegree_characterDegree_dvd_card
-- Peterfalvi (5.6) degree-ratio integrality ("Set χ(1) = a·χ₁(1)"): when χ₁'s natural degree
-- divides χ's, the quotient `a` is a *positive* natural with `characterDegree χ = a·characterDegree χ₁`.
-- This is the honest §5.6 opening step — divisibility (hyp (5.6)(b)) is essential, not scaffolding.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatio_of_dvd
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S03.exists_pos_natDegreeRatioFamily_of_dvd
-- Corollary (Isaacs Cor. 3.12): the degree of an irreducible representation of a finite p-group is
-- a power of p.  Immediate from `finrank_dvd_card` (`dim V ∣ |G| = p^n`) and `Nat.dvd_prime_pow`.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_finrank_eq_prime_pow_of_isPGroup
-- ClassFunction-level form of the same corollary: an irreducible character of a finite p-group has
-- `χ(1) = p^k`.  Routes the witnessing representation's `dim V = p^k` onto `χ 1` via `char_one`.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.exists_charValue_one_eq_prime_pow_of_isPGroup
-- Peterfalvi-side consumer (the degree datum for (6.6) "θⱼ(1) is a power of p", mmd L80): the same
-- prime-power degree on the `IrreducibleCharacter G` subtype, phrased through `characterDegree`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S03.exists_characterDegree_eq_prime_pow_of_isPGroup
-- Same datum with a shared natural witness `d`: `characterDegree χ = d`, `d = p^k`, and `0<d`,
-- ready for the S08 natural-degree/gap inputs without reopening the representation witness.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S03.exists_natDegree_characterDegree_eq_prime_pow_of_isPGroup

-- Peterfalvi §4 (2.8): the semidirect structure `M(B) = H(B) ⋊ N_L(B)` for a nonempty
-- `B ⊆ A`, recorded as the order identity `|M(B)| = |H(B)| · |N_L(B)|` (internal-product
-- bijection: `N_L(B)` normalizes `H(B)` by (2.4.a), and `H(B) ∩ N_L(B) = 1`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.card_mBSubgroup
-- Peterfalvi §4 (2.9): the quotient hom `f_B : M(B) →* L` has kernel `H(B)`, and the
-- pullback `α_B = α ∘ f_B` sends virtual characters of `L` to virtual characters of `M(B)`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.ker_dadeQuotientHom
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.alphaB_mem_ZIrr
-- Peterfalvi §4 (2.9): the defining equation `α_B(h·b) = α(b)` (h ∈ H(B), b ∈ N_L(B)),
-- via `f_B` retracting `N_L(B)` (`dadeQuotientHom_coe_of_mem_nLStabilizerIn`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.dadeQuotientHom_coe_of_mem_nLStabilizerIn
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.alphaB_apply_mul
-- Peterfalvi §4 (2.10.2): `C_{H(B)}(a) = H(B ∪ {a})`, with the `O_{π'}`-containment lemma
-- (a coprime-order element of `C_G(a)` lies in the normal complement `H(a)`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.mem_H_of_mem_centralizer_coprime
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.centralizer_inf_hIntersection
-- Peterfalvi §4 (2.5)/(2.6.a): the explicit pointwise Dade map `dadeMap` satisfies the (2.5)
-- defining equations (`isDadeMap_dadeMap`, well-defined by (2.4.b)), and bundles with the
-- (2.6.a) isometry into an actual `DadeIsometryData` (no longer an interface assumption).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.isDadeMap_dadeMap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.dadeIsometryData
-- Peterfalvi §4 (2.5) uniqueness + (2.11) restriction compatibility of the explicit Dade map:
-- the (2.5) equations pin the map down (`IsDadeMap.unique`), so the constructed Dade map of the
-- restricted hypothesis is the domain-restriction of the constructed Dade map (`dadeMap_restrict`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.IsDadeMap.unique
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_restrict
-- Peterfalvi §4 (2.10.1) Dade-specific conjugation: `M(B^x) = M(B)^x`, with the factor
-- conjugations `H(B^x) = H(B)^x` and `N_L(B^x) = N_L(B)^x` (via (2.4.a) `HConjInvariant`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.hIntersection_conjFinset
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.nLStabilizerIn_conjFinset
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.mBSubgroup_conjFinset
-- Peterfalvi §4 (2.10.1) Dade-specific induced-character invariance:
-- `Ind_{M(B^x)} α_{B^x} = Ind_{M(B)} α_B`, via the transport `α_{B^x} = transportConj x α_B`
-- (`alphaB_conjFinset_eq_transportConj`) and the generic `induce_map_conj`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.alphaB_conjFinset_eq_transportConj
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.induce_alphaB_conjFinset
-- Peterfalvi §4 (2.10.3) pointwise value of `Ind_{M(B)}^G α_B`, transversal half:
-- `(Ind_{M(B)} α_B)(g) = ⅟|M(B)| · ∑_{x ∈ 𝒜(g,M(B))} induceTerm M(B) α_B x g`
-- (`induce_alphaB_apply_eq_sum_conjFiber`), and the per-term `α_B(x⁻¹gx) = α(b)` collapse
-- via the (2.9) defining equation (`exists_nLStabilizerIn_alphaB_induceTerm`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.induce_alphaB_apply_eq_sum_conjFiber
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.exists_nLStabilizerIn_alphaB_induceTerm
-- Peterfalvi §4 (2.10.3) vanishing case: if `g ∉ ⋃_a (aH(a))^G` then `(Ind_{M(B)} α_B)(g) = 0`.
-- Each nonzero summand forces (via the (2.1) keystone `exists_mem_centralizer_conj` and (2.10.2))
-- `g ∈ (bH(b))^G ⊆ dadeSupport`, contradicting `g ∉ dadeSupport` (`coprime_orderOf_card_hIntersection`
-- supplies the (2.2.c) coprimality input).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.coprime_orderOf_card_hIntersection
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport
-- Peterfalvi §4 (2.10.3) value case (N_L(B)-aggregated): `f_B` projects M(B) onto its N_L(B)-factor
-- with H(B)-coset fibers (`dadeQuotientHom_eq_iff_mem_hIntersection_mul`,
-- `dadeQuotientHom_mem_nLStabilizerIn`), so `(Ind_{M(B)} α_B)(g) = ⅟|M(B)|·∑_{b∈N_L(B)} α(b)·|𝒜(g,H(B)b)|`
-- (`induce_alphaB_apply_eq_sum_nLStabilizerIn`): the conjFiber sum regrouped over the component `b`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.dadeQuotientHom_eq_iff_mem_hIntersection_mul
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.dadeQuotientHom_mem_nLStabilizerIn
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.induce_alphaB_apply_eq_sum_nLStabilizerIn
-- Peterfalvi §4 (2.10.3) value case, support-restricted: when `α ∈ CF(L,A)`, the `N_L(B)`-sum
-- may be taken over `{b ∈ N_L(B) | b ∈ A}` since terms with `b ∉ A` carry `α(b) = 0`
-- (`induce_alphaB_apply_eq_sum_nLStabilizerIn_inA`) — first reduction of (2.10.3)'s value formula.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.induce_alphaB_apply_eq_sum_nLStabilizerIn_inA
-- Peterfalvi §4 (2.10) `L`-conjugacy transversal `ℬ`: the `conjFinset` action is a `MulAction`
-- whose stabilizer is `N_L(B)` (`stabilizer_conjFinsetAction`), with `Quotient.out` representatives
-- `L`-conjugate to their class (`transversalRep_conj`); the orbit-stabilizer weight
-- `|orbit B|·|N_L(B)| = |L|` (`card_orbit_mul_card_setLStabilizer`) is the (2.10.3) sum normalization.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.stabilizer_conjFinsetAction
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.transversalRep_conj
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.card_orbit_mul_card_setLStabilizer
-- Peterfalvi §4 (2.10)/(2.6.b) right-hand-side virtual-character infrastructure: each
-- inclusion–exclusion summand `Ind_{M(B)}^G α_B` is a virtual character (`induce_alphaB_mem_ZIrr`,
-- packaged with its own invertibility as `induceAlphaBTerm` / `induceAlphaBTerm_mem_ZIrr`), hence
-- any ℤ-combination `∑ c_B • Ind_{M(B)} α_B` is one (`zsmul_induceAlphaBTerm_sum_mem_ZIrr`).  The
-- bridge `preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum` reduces (2.6.b) to the
-- (2.10) identity `α^τ = -∑_{B∈ℬ} (-1)^|B| Ind_{M(B)} α_B`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.induce_alphaB_mem_ZIrr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.induceAlphaBTerm_mem_ZIrr
-- (2.10.1) packaged form: the summand `induceAlphaBTerm` is `L`-conjugacy invariant
-- (`Ind_{M(B^l)} α_{B^l} = Ind_{M(B)} α_B`), the well-definedness fact for the transversal `ℬ` sum.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.induceAlphaBTerm_conjFinset
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.zsmul_induceAlphaBTerm_sum_mem_ZIrr
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.preservesVirtualCharacters_dadeMap_of_eq_induceAlphaBTerm_sum
-- (2.10) Möbius-assembly primitives: the survivor cardinality `|𝒜(g, K·a)| = |C_G(a)|` for a
-- subgroup centralized by `a` (`card_conjFiber_coset_eq_card_centralizer`, the (2.1) coset
-- conjugacy `card_conj_fiber` translated to the conjugating set `𝒜`); the per-component conjugacy
-- witness `𝒜(g, H(B)b) ≠ ∅ ⇒ ∃c∈H(b), (b·c)~g` (`exists_mem_H_isConj_of_mem_conjFiber_coset`) and
-- its support corollary (`mem_dadeSupport_of_mem_conjFiber_coset`); and the (2.10.3) value case
-- `a^L`-specialized: `(Ind α_B)(g) = (α(a)/|M(B)|)·∑_{b∈N_L(B)∩a^L}|𝒜(g,H(B)b)|`
-- (`induce_alphaB_apply_eq_alpha_mul_sum_conjL`), dropping the `b ∉ a^L` terms by the conjugacy
-- witness + (2.4.b) and collapsing `α(b)` to `α(a)`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.card_conjFiber_coset_eq_card_centralizer
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.exists_mem_H_isConj_of_mem_conjFiber_coset
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_of_mem_conjFiber_coset
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.induce_alphaB_apply_eq_alpha_mul_sum_conjL
-- conjugation invariance of the conjugating set `|𝒜(g, c·X·c⁻¹)| = |𝒜(g, X)|`
-- (`card_conjFiber_conj_eq`), the reindexing fact `|𝒜(g, H(B^x)b)| = |𝒜(g, H(B)a)|` used to
-- collapse the `a^L`-sum (right translation by `c` bijects the conjugating sets).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.card_conjFiber_conj_eq
-- (2.1)/(2.10) STEP 2 fiber factorization: the conjugacy-image fiber count
-- (`card_cosetConjFiber_eq_card_centralizerInf`, each `(c,x) ↦ x⁻¹(c·a)x` fiber over a point of
-- `K·a` has size `|C|`, via `mem_centralizer_of_coset_conj_eq` rigidity) and the resulting
-- factorization `|𝒜(g,K·a)|·|C| = |𝒜(g,C·a)|·|K|` (`card_conjFiber_coset_mul_card_centralizerInf`,
-- `C = K ⊓ C_G(a)`), computed via the bridge set `S = {(y,c,x) | y⁻¹gy = x⁻¹(c·a)x}` both ways
-- (fiber count over `y`, and the `(y,c,x) ↦ (yx⁻¹,c,x)` bijection freeing `x ∈ K`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.card_cosetConjFiber_eq_card_centralizerInf
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.card_conjFiber_coset_mul_card_centralizerInf
-- (2.10) Möbius cancellation identity (`card_conjFiber_hIntersection_mul_eq`):
-- `|𝒜(g,H(B)a)|·|H(B∪{a})| = |𝒜(g,H(B∪{a})a)|·|H(B)|` for `a ∈ N_L(B)` — STEP 2 factorization
-- specialized to `K = H(B)`, `C = C_{H(B)}(a) = H(B∪{a})` by (2.10.2).  Shows the toggle-`a`
-- summands `(-1)^|B|/|H(B)|·|𝒜(g,H(B)a)|` for `B` and `B∪{a}` are equal, hence cancel.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.card_conjFiber_hIntersection_mul_eq
-- (2.10) STEP 3b, the toggle-`a` Möbius cancellation collapsing `𝒫(a)` to its `B = {a}` survivor:
-- the Finset `mobiusIndex` `𝒫(a)` (nonempty `B ⊆ A` with `a ∈ N_L(B)`), the summand
-- `mobiusSummand` `(-1)^|B|/|H(B)|·|𝒜(g,H(B)a)|`, the pairwise cancellation
-- `mobiusSummand_add_insert_eq_zero` (`= 0` via `card_conjFiber_hIntersection_mul_eq` + sign flip),
-- and the involution `sum_mobiusSummand_eq_singleton` (`∑_{𝒫(a)} = mobiusSummand {a}` by
-- `Finset.sum_involution` on `𝒫(a) \ {{a}}` with `toggleA` `B ↦ B △ {a}`); the survivor
-- `mobiusSummand_singleton_eq` (`= -|C_L(a)|` via `card_conjFiber_coset_eq_card_centralizer` +
-- `card_centralizer_eq`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.mobiusSummand_add_insert_eq_zero
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.sum_mobiusSummand_eq_singleton
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.mobiusSummand_singleton_eq
-- (2.10) STEP 3a, the orbit-averaging of the transversal sum to the powerset
-- (`sum_transversalRep_eq_sum_div_orbit`: for orbit-constant `h`, `∑_{C∈ℬ} h(rep C) =
-- ∑_{B⊆A} h B / |orbit B|`, via `Finset.sum_fiberwise_of_maps_to` along `Quotient.mk''`), and the
-- `b = a^x` reindex via `L`-conjugation invariance of the `𝒫(b)`-sum
-- (`sum_mobiusSummand_conjFinset`: `∑_{𝒫(a^l)} mobiusSummand (a^l) = ∑_{𝒫(a)} mobiusSummand a`,
-- a `Finset.sum_bij'` with `B₀ ↦ B₀^l`, summand preserved by `mobiusSummand_conjFinset` =
-- `card_conjFiber_conj_eq`).  These make the (2.10) RHS sum independent of transversal
-- representatives and of `b ∈ a^L`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.sum_transversalRep_eq_sum_div_orbit
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.sum_mobiusSummand_conjFinset
-- (2.10) STEP 3a per-`B` orbit-weight algebra (`mobiusSummand_orbit_weighted`):
-- `(-1)^|B|/|orbit B|·(Ind α_B)(g) = (α(a)/|L|)·∑_{b∈N_L(B)∩a^L} (-1)^|B|/|H(B)|·|𝒜(g,H(B)b)|`,
-- collapsing `1/(|orbit B||M(B)|) = 1/(|L||H(B)|)` via `card_orbit_mul_card_setLStabilizer` +
-- `card_mBSubgroup` + `card_nLStabilizerIn_eq` (|N_L(B)|=|setLStabilizer B|).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.mobiusSummand_orbit_weighted
-- (2.10) STEP 3 final assembly: the per-`B` orbit-weight identity over the fixed `a^L` index
-- (`mobiusTermCF_div_orbit_eq`, reindexing the inner `b`-sum from the `B`-dependent `N_L(B)`-subtype
-- to `aOrbitFinset a = a^L` for the `Finset.sum_comm` swap), and the support-side total
-- (`sum_mobiusTermCF_transversalRep_eq_neg`: `∑_{C∈ℬ} mobiusTermCF(rep C) = -α(a)` via orbit-average
-- + double-sum swap + survivor collapse `mobiusSummand b' g {b'} = -|C_L(b')|` + the (2.7) count
-- `sum_card_centralizerIn_eq` giving `∑_{b'∈a^L}|C_L(b')| = |L|`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.mobiusTermCF_div_orbit_eq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.sum_mobiusTermCF_transversalRep_eq_neg
-- (2.10) STEP 4: the pointwise inclusion–exclusion identity `α^τ = -∑_{C∈ℬ} mobiusTermCF(rep C)`
-- (`dadeMap_eq_neg_sum_mobiusTermCF`, support side = `sum_mobiusTermCF_transversalRep_eq_neg`,
-- non-support side = `induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport`), its reindex over the
-- representative subtype (`sum_mobiusTermCF_transversalRep_eq_sum_subtype`), the (2.6.b) preservation
-- `PreservesVirtualCharacters (hyp.dadeMap)` (`preservesVirtualCharacters_dadeMap`, via the bridge),
-- and the honest `FullDadeIsometryData` construction (`fullDadeIsometryData`, = (2.6)).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_eq_neg_sum_mobiusTermCF
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.sum_mobiusTermCF_transversalRep_eq_sum_subtype
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.preservesVirtualCharacters_dadeMap
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S04.Hypothesis.fullDadeIsometryData

-- BG App.A Thm A.4(a) (= Gorenstein 6.5.1 翻訳): odd-order solvable + O_p(G)=1 ⇒ p-stable.
#assert_only_allowed_axioms OddOrder.BG.AppA.thmA4a
-- BG App.A Thm A.4(c) (= Gorenstein 6.5.3 翻訳, stability lift) ⭐ **= issue 0047 PSTAB**.
-- O_{p'}(G)P ◁ G, A ≤ N_G(P) p-subgroup, [P,A,A]=1 ⇒ AC_G(P)/C_G(P) ⊆ O_p(N_G(P)/C_G(P)).
-- per-chief-factor p-stability (`stability_perFactor`) を含む全証明が unconditional であることの保証.
#assert_only_allowed_axioms OddOrder.BG.AppA.thmA4c
-- BG App.A Thm A.4(b) (= Gorenstein 6.5.2 翻訳 = BG Thm 6.1): P∈Syl_p, A abelian normal of P
-- ⇒ A ⊆ O_{p',p}(G). A.4(c) の stabilityLiftAux を K=O_p(G/O_{p'}) で再利用。
#assert_only_allowed_axioms OddOrder.BG.AppA.thmA4b
-- BG App.A Thm A.5(1): P ◁ G p-group, X gen by P-normalized abelian p-groups
-- ⇒ XC_G(P)/C_G(P) ⊆ O_p(G/C_G(P)). stabilityLiftAux を K=P で直接適用 + iSup 分解。
#assert_only_allowed_axioms OddOrder.BG.AppA.thmA5_part1
-- BG App.A Thm A.5(2): 上記 + O_{p'}(G)=1 ∧ C_{O_p(G)}(P) ⊆ P ⇒ X ⊆ O_p(G).
-- Prop 1.10 (⟨u⟩ の O_p(G) 上共役作用) で C_G(P) の p'-元を消去 ⇒ C_G(P) p-群
-- ⇒ part(1) を comap 還元。
#assert_only_allowed_axioms OddOrder.BG.AppA.thmA5_part2

-- BG App.B (Puig L(S)) Lemma B.1 + B.2 (issue 2000). 定義 lRelIn/lNIn/lOddIn/lStarIn の
-- 主要性質が unconditional であることの保証. B.3/Thm B.4 (= Thm 6.2 代替) は A.5 消費の別 issue.
-- B.1(a) 反変単調 / (b) 偶 ≤ 奇 / (c) 停留 / (d) L_* ⊆ L.
#assert_only_allowed_axioms OddOrder.BG.AppB.lRelIn_anti_right
#assert_only_allowed_axioms OddOrder.BG.AppB.lNIn_even_le_odd
#assert_only_allowed_axioms OddOrder.BG.AppB.exists_lNIn_stable
#assert_only_allowed_axioms OddOrder.BG.AppB.lStarIn_le_lOddIn
-- B.1(e) abelian normal ⊆ L_i / (g) L_G(L_*)=L, L_G(L)=L_*.
#assert_only_allowed_axioms OddOrder.BG.AppB.abelian_normal_le_lNIn
#assert_only_allowed_axioms OddOrder.BG.AppB.lRelIn_lStarIn
#assert_only_allowed_axioms OddOrder.BG.AppB.lRelIn_lOddIn
-- B.1(f) p-群自己中心性 C_G(L_i) ⊆ L_i ⊇ Z(G) + L_*≠1, L≠1.
#assert_only_allowed_axioms OddOrder.BG.AppB.centralizer_lNIn_le
#assert_only_allowed_axioms OddOrder.BG.AppB.center_le_lNIn
#assert_only_allowed_axioms OddOrder.BG.AppB.lOddIn_ne_bot
-- B.2 L(G) ⊆ H ⇒ L(H) = L(G).
#assert_only_allowed_axioms OddOrder.BG.AppB.lOddIn_eq_of_lOddIn_le
-- B.3 (issue 2001): p odd solvable, O_{p'}(G)=1, S∈Syl_p, T=O_p ⇒ L_*(S)⊆L_*(T)⊆L(T)⊆L(S).
-- 相対 B.1(f) + thmA5_part2 を消費する最初の結果.
#assert_only_allowed_axioms OddOrder.BG.AppB.b3_chain
-- B.4(b) Step2 (issue 2001): Z(L(S)) ⊆ Z(L(T)) (keystone bridge + B.3 + 相対 B.1(f)).
#assert_only_allowed_axioms OddOrder.BG.AppB.zCenterLOdd_sylow_le_zCenterLOdd_opCore
-- B.4(b) 基盤: L-operator の normalizer 同変性 N_G(H) ⊆ N_G(L(H)) (共役同変, transport 回避).
#assert_only_allowed_axioms OddOrder.BG.AppB.normalizer_le_normalizer_lOddIn
-- B.4(b) 本体 (issue 2001): O_{p'}(G)=1 ⇒ Z(L(S)) ⊴ G (= BG Thm 6.2 Glauberman Z(J) 代替).
#assert_only_allowed_axioms OddOrder.BG.AppB.zCenter_lOdd_normal_of_oPiCore_eq_bot
-- BG Thm 6.2 一般形 (issue 2002 合流): Z(L(S))·O_{p'}(G) ⊴ G (B.4(b) を G/O_{p'} に適用し引き戻し).
#assert_only_allowed_axioms OddOrder.BG.AppB.zCenter_lOdd_sup_oPiCore_normal

-- BG §1 Thm 1.13 (J. G. Thompson critical, issue 0016): p odd, G 非自明 p-群 ⇒
-- characteristic H = Ω₁(C) (C critical) で [H,G]⊆Z(H), cl≤2, exp=p, C_{Aut G}(H) p-群.
-- 証明本体は OddOrder.GroupTheory.CriticalSubgroup (Gorenstein Finite Groups Thm 5.3.11+5.3.13).
#assert_only_allowed_axioms OddOrder.BG.Ch1.S01.thompson_critical_omega
-- BG §4 Lem 4.7 hard dir = **G** Thm 5.4.15(i) (precursor 1, issue 0051): p odd 非自明 p-群 R で
-- SCN₃(R)=∅ ⇒ pRank R ≤ 2. Gorenstein Lemma 4.14 + GL(≤2,p) rank squeeze。§5 / Thm 4.16 の gate.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S04.pRank_le_two_of_scn3_empty
-- BG §4 Lem 4.17 (§4G): p odd, r(R)≤2, A ≤ Aut R faithful odd ⇒ A' は p-群。Thm 1.13 critical +
-- Thm 1.8 Burnside (elementwise) + Prop 4.8 + Thm 2.6 GL(2,p) engine。§5 Thm 5.5(a)/Thm 4.18 の gate。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S04.isPGroup_commutator_of_mulAut_odd_of_pRank_le_two
-- BG §4 Thm 4.18 (§4H): G solvable odd, p∣|G|, r_p(G)≤2 ⇒ (a) p は |G/O_{p'}| の最大素因子
-- (b) p=3∨p最小 ⇒ normal p-complement (c) G' が normal p-complement (d) G' の p'-部分群 ⊆ O_{p'}(G')
-- (e) G/O_{p',p} abelian p'-群。Hall-Higman 1.2.3 (= G Thm 6.3.2) + Lem 4.17 + Lem 4.13。§5 Thm 5.6/5.7 の gate。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S04.solvable_structure_of_pRank_le_two
-- BG §5 Lem 5.1(a): p odd 有限 p-群 R, r(R)≥3 ⇒ SCN₃(R)≠∅ (= Lem 4.7 hard dir の対偶)。§5 着手。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S05.scn3_nonempty_of_three_le_pRank
-- BG §5 Lem 5.2: E∈ℰ²∩ℰ* ⇒ E⊄T ∧ (|Ω₁(Z(R))|=p ∧ W=Ω₁(Z₂(R))∈ℰ²) ∧ [R:T]=p (T=C_R(W))。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S05.lemma52
-- BG §5 Thm 5.3: r(R)≥3 ⇒ (narrow ⟺ ℰ²(R)∩ℰ*(R)≠∅)。⇐ は 5.3(d) の分解論法で witness 構成。
#assert_only_allowed_axioms
  OddOrder.BG.Ch1.S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq
-- BG §5 Thm 5.3(d): narrow, |S|=p, r(C_R(S))≤2 ⇒ C_T(S) cyclic ∧ S∩R'=S∩T=1 ∧ C_R(S)=S×C_T(S)。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S05.narrow_centralizer_decomp
-- BG §5 Cor 5.4: r(R)≥3 ⇒ (narrow ⟺ ∃S, |S|=p ∧ r(C_R(S))≤2)。
#assert_only_allowed_axioms
  OddOrder.BG.Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two
-- BG §5 Thm 5.5 (§5 最重量): p odd, R narrow, A ≤ Aut R solvable odd ⇒ (a) A/O_p(A) abelian p'-群
-- (b) r≥3 で p'-元の位数 ∣ p-1 (critical H_i 降鎖 + Lem 1.9 stability) (c) |A|=q prime ∤ p(p-1) で
-- q ∣ (p+1)/2 (Lem 4.14) + R=[R,A] 非可換なら |R|=p³ (Thm 4.16 Blackburn + Aut(C_{p^t}) totient)。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S05.solvableAut_of_narrow
-- BG §5 Thm 5.6: G solvable odd, S narrow Sylow p (r(S)≥3 なら p-length one 仮定) ⇒ Thm 4.18 と
-- 同じ結論 5 連。r(S)≤2 は Sylow-rank 橋 (pRank_le_pRank_sylow) + Thm 4.18; r(S)≥3 は
-- Ḡ=G/O_{p'} で S̄=O_p(Ḡ) が唯一の Sylow → Thm 5.5(a)(b) を Lem 4.17/4.13 の代替に使う
-- core56 + 共通 assembly (structure_of_quotient_commutator_le_opCore)。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S05.narrow_sylow_solvable_structure
-- BG §5 Thm 5.7 (§5 完結): G solvable odd, E elem-ab p ≤ F(G), r(C_{F(G)}(E)) ≤ 2 (全素数 rank;
-- scaffold の pRank p は BG 原文に合わせ rank へ修正) ⇒ G' ≤ F(G)。Prop 1.2 chief-factor 還元
-- (S01, G*=⊤ glue) + q-chief factor U/V は U⊓O_q(G) で被覆 (U の Sylow q ≤ F(G) の正規 Sylow)
-- + O_q(G) narrow (q≠p は Fitting 異素数可換で排除; q=p は EZ ∈ ℰ²∩ℰ* + Thm 5.3)
-- + Thm 5.5(a) で G' の Ū-作用が q-群 + 固定点論法 (Isaacs Lem 4.32) + Ū minimal normal。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S05.derived_le_fitting_of_centralizer_rank_le_two
-- BG Thm 4.20(a) (rank 版): G solvable odd, rank F(G) ≤ 2 ⇒ G' ≤ F(G)。F(G)≠1 から elem-ab E≤F(G)
-- を 1 つ作り Thm 5.7 を適用 (C_G(E)⊓F ≤ F ゆえ centralizer-rank 仮説は自動)。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S05.derived_le_fitting_of_rank_fitting_le_two
-- BG Thm 4.20(c) 存在 (mmd L1786): G solvable odd, rank F(G) ≤ 2 ⇒ characteristic Sylow series。
-- |G| 強帰納: G'≤F (4.20a) で G/F abelian → p₁=最小素数, H=(mk' F)⁻¹(O_{p₁'}(G/F)) で G/H が
-- p₁-群 + F が H の Sylow-p₁ を含む → Thm 4.18(b) で H に normal p₁-complement → G の normal
-- p₁-complement K=O_{p₁'}(G) → F(K)≤F(G) で K に IH → 上層 (top layer p₁) を付けて lift。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two
-- BG Prop 1.16(2) (mmd L501): noncyclic abelian A が coprime 作用 ⇒ G=⟨C_G(Y)|A/Y cyclic⟩
-- (第1式 G=⟨C_G(x)|x∈A^#⟩ = Gorenstein 6.2.4 = Isaacs 6.21 既存; 第2式を |A| 帰納で構成)。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic
-- BG Prop 1.16(1) = Gorenstein 6.2.4 = Isaacs 6.21 の φ:A→*MulAut G 形 (interface 適応)。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
-- BG Lem 1.14 (centralizer 形): C_{G/M}(TM/M) の引き戻し = C_G(T)·M (M⊴G p'-群, T p-群)。
-- normalizer 形 + T⊓M=⊥ から導出 (Prop 1.15(b) の O_{p'}(G)=1 還元に使用)。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S01.centralizer_comap_mk'_eq_centralizer_sup_of_pGroup_coprime
-- BG Prop 1.15(b) (Goldschmidt), O_{p'}(G)=⊥ case: O_{p'}(C_G(R))=⊥ (R p-subgroup, G solvable)。
-- ⟨u⟩ が RT=R⊔O_p(G) に共役作用 + Prop 1.10 で O_{p'}(C_G(R))⊆C_G(O_p(G))⊆O_p(G) (Prop 1.15(a))。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S01.oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot
-- BG Prop 1.15(b) (Goldschmidt), general form: O_{p'}(C_G(R)) ≤ O_{p'}(G) (R p-subgroup, G solvable)。
-- M₀=O_{p'}(G) で商 Ḡ=G/M₀ に落とし, Lem 1.14 で C_Ḡ(R̄)=(C_G(R)).map f, 特殊形@Ḡ で K=M.map f=⊥。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S01.oPiPrimeCore_centralizer_le_oPiPrimeCore
-- BG Cor 1.12 (mmd L457): p 奇, G p-群, E elem ab, A p'-operators が C_G(E) の order-p 元を全固定
-- ⇒ A は G 上自明。Thm 1.11 (=Isaacs 4.36) を C_G(C_G(A)) に + Prop 1.10 (G nilpotent)。Thm 6.7 で使用。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S01.corollary_1_12
-- Isaacs Thm 3.21 / Hall-Higman 1.2.3 (general form, no O_{π'}=1 hyp): π-separable G で
-- C_G(O_{π',π}(G)) ≤ O_{π',π}(G)。Ḡ=G/O_{π'}(G) へ特殊形を転送する Isaacs Thm 3.22 還元。BG §9 Thm 9.1 で使用。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S01.centralizer_oPiPrimePiCore_le
-- BG §6/§7 共有 engine: ↥V 可解 + π-Hall 共役 (Isaacs hall_C を subtype 像で G レベルへ);
-- §7 Thm 7.4(d) と §6 Lem 6.5(c) の両方で使用。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf
-- BG §6 Lem 6.5 (可解 N/C 分解, mmd L2048): K⊴G, G=KU, H≤U, (|H|,|K|)=1 ⇒ (a) H⊓G'=H⊓U';
-- (c) H^g=g⁻¹Hg≤U ⇒ g=cu (c∈C_K(H),u∈U); (b) N_G(H)=C_K(H)·N_U(H)。(c)=↥V=(H⊔K)⊓U 内 Hall 共役。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.inf_commutator_eq_of_coprime
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.exists_mem_centralizerK_mul_of_conj_le
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.normalizer_eq_centralizerK_mul_normalizerU
-- BG §6 Lem 6.6 (p-length 1 特性化, mmd L2090): G 可解, S∈Syl_p, hasPLengthOne ⇒
-- foundation O_{p',p}=O_{p'}⊔S; (1b) G=O_{p'}⊔N_G(S) (Frattini); (2) S⊆G'⇒S⊆(N_G(S))';
-- (3) Y⊆S, Y^x⊆S ⇒ ∃c∈C_G(Y),g∈N_G(S),cg=x (Lem6.5c); (4) Q p-部分群 ⇒ ∃x∈C_G(Q∩S),Q^x⊆S。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.top_eq_oPiPrimeCore_sup_normalizer_sylow
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.sylow_le_commutator_normalizer_of_le_commutator
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.exists_mem_centralizer_mul_normalizer_of_conj_subset_sylow
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.exists_mem_centralizer_inf_conj_le_sylow
-- BG Thm 6.7 (mmd L2105): G 可解, p 奇, E∈E*_p(G) (包含極大 elem ab), L p'-部分群 normalized by E,
-- hasPLengthOne ⇒ L⊆O_{p'}(G)。reduced case (O_{p'}=⊥: 6.6 で S⊴G, Cor 1.12 で L 中心化 S,
-- Prop 1.15(a) で L⊆S=O_p, L p'⟹L=⊥) + G/K reduction (E*_p quotient lift)。§7 Prop 7.5 case1 で使用。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S06.le_oPiPrimeCore_of_normalized_by_maximalElementaryAbelian
-- BG §7 Note (Hyp 7.1 直後, mmd L2145): C_G(A) の π'-元は K=O_{π'}(C_G(A)) に入る
-- (X=A⊔C_G(A)<G simplicity + Hyp 7.1(2) で c∈O_{π'}(X), O_{π'}(X)⊓C ⊴ C は π'-群)。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.mem_kSubgroup_of_piPrime_mem_centralizer
-- BG §7 Lemma 7.1 (Inductive Lemma, mmd L2147, 推移性の核): Hyp 7.1, q∈π', Q₁,Q₂∈ℋ_G*(A;q),
-- 真部分群 H⊇A で H⊓Q₁≠1≠H⊓Q₂ ⇒ Q₂=Q₁^k (k∈K)。|G|-|Q₁∩Q₂| 強帰納 + 共通構成 (Prop 1.5(b)(c)
-- を O_{π'}(H) 上で適用) + Case B normalizer 増大 (q-群 nilpotent)。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.inductiveLemma
-- BG Prop 1.16(1) 共役形 (§7 Thm 7.2/7.3 + §8–§16 で再利用): noncyclic abelian B が coprime な
-- Q≠1 を正規化 ⇒ ∃ x∈B^#, Q⊓C_G(x)≠1 (Isaacs 6.21 を conjAction に橋渡し)。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.exists_mem_inf_centralizer_ne_bot_of_not_isCyclic
-- BG Thm 7.3 (mmd L2187): Hyp 7.1, q∈π', m(Z(A))≥2, q∈π(C_G(A)) ⇒ K は ℋ_G*(A;q) 上推移的
-- (Prop 1.16 共役形で B∈ℰ_p²(Z(A)) の C_{Qᵢ}(x)≠1 → Cauchy で R 経由 Lem 7.1 連鎖)。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.transitive_of_two_le_rank_center_of_dvd
-- BG Prop 1.16(2) 共役形 (Thm 7.2 + §8–§16 で再利用): noncyclic abelian B が coprime Q≠1 を
-- 正規化 ⇒ ∃ Y≤B (B/Y cyclic) で Q⊓C_G(Y)≠1 (Prop 1.16(2) cocyclic を conjAction に橋渡し)。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.exists_cocyclic_inf_centralizer_ne_bot_of_not_isCyclic
-- BG Thm 7.2 (mmd L2177): Hyp 7.1, q∈π', m(Z(A))≥3 ⇒ K は ℋ_G*(A;q) 上推移的 (Prop 1.16(2)
-- cocyclic 共役形で B∈ℰ_p³(Z(A)) の noncyclic Y → C_{Q₁}(Y)⊆C_G(z) (z∈Y) → Lem 7.1)。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.transitive_of_three_le_rank_center
-- BG Prop 7.5 case (2) (mmd L2252, SCN₂ branch): A∈SCN₂(P) ⇒ A satisfies Hypothesis 7.1.
-- B∈ℰ_p²(A), B⊴P を Z(P) cyclic/noncyclic で構成 (cyclic = Isaacs Lem 1.23 で ⟨z⟩<L≤Ω₁(A) +
-- special case 2 の coprime 分解 / 軌道-stabilizer crux z∈O_{p',p}(C_G(b)))、coreClaimGeneral へ。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.hypothesis71_of_scn2
-- BG Prop 7.5 完全形 (mmd L2252, 両分岐): A abelian p-部分群が (1) A=Ω₁(C_G(A)) ∧ 全真部分群
-- p-length one, または (2) A∈SCN₂(P) ⇒ A は Hypothesis 7.1。case (1) は Thm 6.7 を ↥X に適用
-- (A=Ω₁(C_G(A)) で A.subgroupOf X が包含極大 elem ab)。§7 完全 sorry-free 化の最終ピース。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.hypothesis71_of_scn2_or_pLengthOne
-- BG Thm 7.6 ⭐⭐⭐ **FT クリティカル** (Thompson Transitivity, mmd L2311): A∈SCN₃(p), q∈p' ⇒
-- O_{p'}(C_G(A)) が ℋ_G*(A;q) 上推移的。Prop 7.5(2) で Hyp 7.1 を得て Thm 7.2 (rank≥3) を適用。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.thompsonTransitivity
-- BG Thm 7.4 (Propagation, mmd L2197): Hyp 7.1, q∈π', P 真 π-部分群が A を subnormal に含み K が
-- ℋ_G*(A;q) 上推移的 ⇒ (a) C_K(P)=O_{π'}(C_G(P)), (b) O_{π'}(C_G(P)) が ℋ_G*(P;q) 上推移的,
-- (c) ℋ_G*(P;q)⊆ℋ_G*(A;q), (d) P∩N(P)′⊆N(Q)′ かつ N(P)=O_{π'}(C_G(P))(N(P)∩N(Q))。
-- |P:A| 帰納 + composition series 還元 ((7.3) 不動点 / Hall 共役 / Lem 6.5(a))。§8–§16 で多用。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S07.transitivity_propagates
-- BG Thm 8.1(a) (mmd L2319-L2321): M∈ℳ, p∈π(F(M)), A₀∈ℰ_p^*(F(M)), m(A₀)≥3,
-- F(M) が p-群でなければ C_{F(M)}(A₀) は一意最大部分群に含まれる。
#assert_only_allowed_axioms OddOrder.BG.Ch2.S08.cFitting_isUniquelyMaximal_of_not_pGroup
-- BG Thm 8.1(b) (mmd L2319-L2322): F(M) が p-群なら M の Sylow p-subgroup は G の Sylow,
-- かつ SCN₃(P) の各元は F(M) に含まれ一意最大部分群に属する。
#assert_only_allowed_axioms
  OddOrder.BG.Ch2.S08.sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup
-- Gorenstein Thm 3.7 (precursor 2, issue 0051): ψ が全 proper A-不変正規部分群上自明 + P 上非自明
-- ⇒ P′⊆Z(P), P/P′ elem ab + A irreducible + ψ nontrivial, P special. Thm 3.8/3.10 → BG Lem 4.13.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S04.isSpecial_of_pprimeAction_trivialOnProper
-- Gorenstein Thm 3.8 (precursor 2): minimal A-不変 (ψ 非自明) 部分群 Q は special (Thm 3.7 適用)。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S04.exists_minimal_aInvariant_isSpecial_of_pprimeAction
-- precursor 2 完成 (= G Thm 4.15(ii) 入力, p odd): minimal A-不変 (ψ 非自明) 部分群 Q は
-- special かつ exp p。Thm 3.8 + minimality で full Thm 3.10 帰納を回避 (Lem 3.9 + stability)。
#assert_only_allowed_axioms OddOrder.BG.Ch1.S04.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction
-- Clifford BLOCKER A (issue 0026): ρ g は simple ℂ[H]-部分加群を simple に送る.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.Representation.isSimpleModule_map_conjBySimpleSemilinear
-- Clifford gap #5 非負半分 (issue 0026): ⟨Res^G_H χ, θ⟩ = dim Hom(σ, ρ|_H) ≥ 0.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.ClassFunction.restrictionMultiplicity_eq_finrank_intertwiningMap
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.ClassFunction.restrictionMultiplicity_nonneg
-- Clifford gap #5 完結 (issue 0026): multiplicity ⟨Res^G_H χ, θ⟩ = (k : ℂ), k : ℕ
-- (整数性 restrictionMultiplicity_int + 非負性 restrictionMultiplicity_nonneg の合成).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.ClassFunction.restrictionMultiplicity_natCast
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IrreducibleCharacter.restrictionMultiplicity_natCast

-- 真正 character の ℕ-分解 (issue 0046, Peterfalvi (6.6) G2.2 residual): 真正 character `χ_ρ`
-- の Fourier 係数 ⟨χ,ψ⟩ は非負整数 (= dim Hom(σ,ρ)) で, χ = ∑_{ψ∈Irr} ⟨χ,ψ⟩•ψ と ℕ-係数で分解.
-- G-level 非負性 (restrictionMultiplicity_nonneg の G 版) + mem_ZIrr_repr/inner_eq_coeff_of_repr 合成.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.IsCharacter.mem_ZIrr
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsCharacter.exists_natCast_inner_irreducible
#assert_only_allowed_axioms OddOrder.RepresentationTheory.IsCharacter.inner_irreducible_nonneg
#assert_only_allowed_axioms OddOrder.RepresentationTheory.IsCharacter.exists_natFinsupp_eq_sum
-- θ-bound bricks: constituent degree bound `(θ 1).re ≤ (χ 1).re` for `θ` an irreducible
-- constituent of a genuine `χ` (brick 1), and the converse decomposition
-- `ℕ-combination of irreducibles ⇒ genuine character` (brick 2 infra).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsCharacter.apply_one_re_le_of_inner_ne_zero
#assert_only_allowed_axioms OddOrder.RepresentationTheory.isCharacter_of_natFinsupp_eq_sum

-- Peterfalvi (2.1) (issue 0040, Dade-isometry spine): g normalizing H, (|H|,orderOf g)=1
-- ⇒ Hg = ⋃_{x∈H} (C_H(g)g)^x (set form) / every hg ∈ Hg is H-conjugate to C_H(g)g (existence).
-- 反復 conjugacy 剛性 (`conj_fixes_of_commute`) + 繊維数 |C_H(g)| の数え上げ closure.
#assert_only_allowed_axioms OddOrder.GroupTheory.coset_eq_cosetConjImage
#assert_only_allowed_axioms OddOrder.GroupTheory.exists_mem_centralizer_conj

-- BG §1 σ-decomposition foundation (lane-h): the π-part / π′-part decomposition of a
-- finite-order element, `g = a·b` (a a π-element, b a π′-element, commuting powers of g),
-- with existence (CRT exponents) and uniqueness (both factors determined as powers of g).
#assert_only_allowed_axioms OddOrder.GroupTheory.exists_isPiElement_mul
#assert_only_allowed_axioms OddOrder.GroupTheory.isPiElement_mul_unique

-- Peterfalvi §7 (5.4) gateway (issue 1001, Round-9 Track B): R(χ) を ℤ[Irr G] の
-- 一般 orthonormal subset へ一般化した OrthonormalCharacterImageFamily と, その上の
-- (5.4.a) ‖X‖²≥‖χ‖² / (5.4.b) norm 等号 + X=∑_{α∈E}α. 整数 Cauchy-Schwarz +
-- orthonormal Parseval (ZIrrFourier) で sorry-free.
-- (5.2.d) gateway の非空性証拠 (2 元 CharacterDifferenceImage → 一般 family).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage
-- (5.4) projection smart-constructor (issue 0046): `CharacterPsiDecomposition` の hard
-- `X`/`Y`/`coeff`/`X_eq`/`Y_orthogonal` 6 fields を, 単一 number-theoretic input
-- `(χ−ψ)^{τ₁} ∈ ZIrr G` から integral projection (`exists_intProjection_of_orthonormal_ZIrr`) で
-- *計算* 供給。残 input = structural data (imageFamily R(χ), tau1 + isom + agrees, 3 直交スカラー)。
-- 各 step の D₀/Da 生産を「Dade R(χ) 抽出 + τ₁ isometry 拡張」の 2 primitive に縮約する seam。
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
-- (5.6.3) PASS 2 (ii): per-step shared-isometry decomposition PAIR.  `decompositionPair` produces
-- BOTH `D₀` (ψ=0) and `Da` (ψ=a·χ₁) from ONE shared `(R(χ), τ₁, isom, agrees)` + the two
-- `ZIrr`-membership facts `(χ−0)^{τ₁}, (χ−a·χ₁)^{τ₁} ∈ ℤ[Irr G]` via two `ofProjection` calls, so
-- the τ₁-agreement `Da.tau1 χ = D₀.tau1 χ` is STRUCTURAL (`decompositionPair_tau1_agree`, `rfl`) —
-- never posited.  This is the honest packaging of the per-step D₀/Da production from the running τ₁.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.decompositionPair
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.decompositionPair_tau1_agree
-- (5.4.a) ‖X‖² ≥ ‖χ‖².
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.inner_self_chi_re_le_inner_self_X
-- (5.4.b) norm 等号 + X = ∑_{α∈E} α (E ⊆ R(χ), |E| = ‖χ‖²).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.norm_eq_and_X_eq_sum_of_norm_Y_ge
-- (5.5) ψ=0 の特殊化: Y=0 かつ χ^{τ₁} = ∑_{α∈E} α. ⟨φ,φ⟩ の正定値性
-- (eq_zero_of_inner_self_re_eq_zero) で ‖Y‖²=0 → Y=0.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
-- Peterfalvi §7 (5.6.2) integer-forcing + Pythagoras layer (issue 0046):
-- orthogonal-family Pythagoras `‖∑cᵢ•vᵢ + Z‖² = ∑cᵢ²mᵢ + ‖Z‖²` (ZIrrFourier),
-- the (5.6.2) opening bound `‖Y‖² ≤ ‖ψ‖²`, the (5.6.2) quadratic bound
-- `∑cᵢ²mᵢ + ‖Z‖² ≤ ‖ψ‖²`, and the division-free integer-forcing core
-- `2a < D, λ²D-2λa+z ≤ 0 ⇒ λ = 0`. すべて (5.4)/(5.5) API 直載 sorry-free.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.inner_self_orthogonalSum_add_re
-- (5.6.1) existence half (issue 0046): orthogonal projection of any `w` onto a finite orthogonal
-- family `vᵢ` with nonzero real grams `mᵢ` — `w = ∑(⟨w,vᵢ⟩/mᵢ)•vᵢ + Z`, `Z ⊥ vⱼ`.  Pure diagonal
-- projection (no completeness): supplies the (5.6.1) decomposition `Y − a·χ₁^{τ₁} = −λ·∑(aᵢ/‖χᵢ‖²)·
-- χᵢ^{τ₁} + Z` whose coefficients are then computed from `χᵢ^{τ₁} ⊥ R(χ)` and fed to the capstone.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_orthogonalProjection_of_orthogonal_family
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.inner_self_Y_re_le_inner_self_psi
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.sum_sq_mul_add_normSq_Z_le
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.int_eq_zero_of_sq_mul_le_of_two_mul_lt
-- (5.6.2) capstone `λ = 0 ∧ Z = 0`: Pythagoras (geometric half) + 整数 forcing (arithmetic
-- half) + 代数展開 `∑(a·[i=i₁]-λrᵢ)²mᵢ = a²m₁ - 2aλ + λ²D` + 正定値性 を end-to-end 合成。
-- (5.6.1) 分解データ (構成可能) を消費し (5.6.2) 結論 `Y = a·χ₁^{τ₁}` を出す。
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.lambda_eq_zero_and_Z_eq_zero
-- (5.6.1)→(5.6.2) `Y`-collapse producer `Y = a·χ₁^{τ₁}` (issue 0046): consumes the (5.6.1) λ-form
-- `Y = a·χ₁^{τ₁} − λ·∑(aᵢ/‖χᵢ‖²)·χᵢ^{τ₁} + Z`, bridges it to the capstone's pointwise-coefficient
-- form, applies `lambda_eq_zero_and_Z_eq_zero` (λ=0, Z=0), and feeds back → `D.Y = a • D.tau1 χ₁`.
-- CONSTRUCTS the `hY` hypothesis that `X_eq_tau1_chi_of_Y_eq` / `image_eq_of_decomposition` /
-- `retarget_isCoherent_of_decompositions[_and_memberFamily]` consume, not posited.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.Y_eq_nsmul_tau1_of_lambdaForm
-- (5.6.3) projection identity `Da.X = D₀.X` (issue 0046): the `R(χ)`-projection `X` is independent
-- of `ψ`.  `X_eq_tau1_chi_of_Y_eq` : from the (5.6.2) collapse `Y = a·χ₁^{τ₁}` (`hY`), the
-- `ψ = a·χ₁` decomposition has `X = χ^{τ₁}` (linearity of `tau1` on `χ - a·χ₁`).
-- `X_eq_of_tau1_eq_on_chi` : chaining with `D₀.tau1 χ = D₀.X` (5.5) and the τ₁-agreement
-- `Da.tau1 χ = D₀.tau1 χ` gives `Da.X = D₀.X` — CONSTRUCTS the `hX_eq` hypothesis of
-- `retarget_isCoherent_of_decompositions`, not posited.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.X_eq_tau1_chi_of_Y_eq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.X_eq_of_tau1_eq_on_chi
-- (5.5)+(5.2.e) image-side orthogonality (issue 0046): the (5.6.3) lattice orthogonalities
-- `hX_ortho`/`hXbar_ortho` (`⟨τ₁ ξ, X⟩ = ⟨τ₁ ξ, X̄⟩ = 0`) derived from the per-element
-- `R(χ)`-orthogonality `∀ α ∈ R(χ), ⟨η, α⟩ = 0`.  `inner_X_eq_zero_of_orthogonal_imageSet` :
-- `X = ∑ coeff•α` (`X_eq`) ⟹ `⟨η, X⟩ = 0`.  `inner_conjImage_eq_zero_of_orthogonal_imageSet` :
-- `X̄ = X − (χ−χ̄)^τ` with `(χ−χ̄)^τ = ∑_{α∈R(χ)}α` both in `ℤ[R(χ)]` ⟹ `⟨η, X̄⟩ = 0`.  These
-- CONSTRUCT the `hperElem`-fed `hX_ortho`/`hXbar_ortho` of `retarget_isCoherent_of_decompositions`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.inner_X_eq_zero_of_orthogonal_imageSet
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.inner_conjImage_eq_zero_of_orthogonal_imageSet
-- (5.2.e) FEED `inner_X_orthogonal_imageSet_of_orthogonal` (issue 0046, PASS 2): the dual of the
-- above — `X = D.X ∈ ℤ[R(χ')]` is orthogonal to every member `α` of a *second* family `R(χ)` when
-- `R(χ') ⊥ R(χ)` (`D.imageFamily.Orthogonal R₀`).  `⟨X, α⟩ = ∑ coeff·⟨β, α⟩ = 0`.  This is the
-- per-character half of mmd L77 "`χᵢ^{τ₁}` is orthogonal to `R(χ)` by (5.5) and (5.2.e)".
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.inner_X_orthogonal_imageSet_of_orthogonal
-- Peterfalvi §7 (5.6.3) conjugate-image computation (issue 0046): given the (5.4.b)/(5.5)
-- output `X = ∑_{α∈E} α`, the candidate `χ̄^{τ₂} = X - (χ-χ̄)^τ = -∑_{α∈R(χ)-E} α`, with
-- `‖χ̄^{τ₂}‖² = |R(χ)| - |E|` and `⟨X, χ̄^{τ₂}⟩ = 0`.  orthonormal `R(χ)` の Parseval/card で
-- sorry-free; (5.6.3) extension `τ₂` の isometry 検証に直接供給 (大域 isometry 拡張は別途).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.conjImage_eq_neg_sum_sdiff
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.inner_self_conjImage_eq_card_sdiff
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.inner_X_conjImage_eq_zero
-- (5.2.d) PRODUCER `characterDifferenceImageOfIsometry` (issue 0046): the first actual consumer of
-- the §3 (1.4) keystone `isometry_difference_pair_structure`.  CONSTRUCTS (not posits) the §7
-- `CharacterDifferenceImage τ χ` record — the two-element `R(χ) = {μ,ν}` gateway used throughout §7
-- — from an integral isometry `τ`, a non-real irreducible `χ` (so `χ ≠ χ̄`), and the three (1.4)
-- hypotheses on the family `{χ,χ̄}` (images virtual, vanish at 1, norm-preserving).  Reads `μ,ν,ε`
-- off the `SignedIrreducibleDifferenceFamily` delivered by the keystone (`Exists.choose`, hence
-- `noncomputable`); `image_eq : τ(χ-χ̄) = ε•(μ-ν)` from the index-1 family equation
-- `τ(χ̄-χ) = ε•(μ₁-μ₀)`.  Until now the §7 `CharacterDifferenceImage` had NO constructor — every §7
-- lemma took it hypothetically; this supplies the missing existence (`toOrthonormalImage` then lifts
-- it to `OrthonormalCharacterImageFamily`, the orthonormal `R(χ)`).  Equal-degree of `χ,χ̄` is
-- `irreducibleCharacter_conj_apply_one` (char value at 1 is a natural number, fixed by conjugation).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.characterDifferenceImageOfIsometry
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.irreducibleCharacter_conj_apply_one
-- (5.6.3) keystone: the orthonormal-block isometry re-targeting constructor `τ₂`.  Given a global
-- integral isometry `τ₁` and orthonormal pairs `{χ,χ̄}`, `{X,X̄}` with the same gram, with `X,X̄ ⊥
-- τ₁ ξ` for every `ξ ⊥ {χ,χ̄}`, the rank-2 re-targeting is again a global integral isometry.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.retarget_isIntegralIsometry
-- (5.6.3) lattice-relative keystone (the genuinely satisfiable form): the re-targeting preserves
-- `⟨·,·⟩` *on a submodule `M`* (closed under the Gram–Schmidt residual against `{χ,χ̄}`, `χ,χ̄∈M`)
-- requiring `X,X̄ ⊥ τ₁ ξ` only for `ξ ∈ M ⊥ {χ,χ̄}`.  For `M = span_ℂ(S₁∪{χ,χ̄})` the residual of
-- `φ∈M` lies in `span_ℂ S₁`, so this is the honest (5.5)+(5.2.e) `X,X̄ ⊥ S₁^{τ₁}` (not the
-- over-strong global version that forces `X,X̄ ∈ span{τ₁χ,τ₁χ̄}`).  This is the (5.6.3) *lattice*
-- isometry `Z[S₁∪{χ,χ̄}] → Z[Irr G]`.  The weakened `IsCoherent.extension_inner_eq` is the
-- *integral-span* form below (`retarget_inner_eq_on_zSpan_union`), needing only the `ℤ[S₁]`-isometry
-- of `τ₁` — no global lift is required (and none exists in FT, where `dim CF(L) > dim CF(G)`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.retarget_inner_eq_on
-- (5.6.3) integral-span keystone (the honest realization of `IsCoherent.extension_inner_eq`): the
-- re-targeting preserves `⟨·,·⟩` on all of `ℤ[S₁∪{χ,χ̄}]`, using only the `ℤ[S₁]`-isometry of
-- `τ₁ = hS₁.extension` and the lattice orthogonality `X,X̄ ⊥ τ₁ ξ` for `ξ ∈ ℤ[S₁]`.  Every
-- Gram–Schmidt residual of `φ∈ℤ[S₁∪{χ,χ̄}]` lands in `ℤ[S₁]` (`orthoResidualMap_mem_zSpan`), so the
-- block expansion closes with no global-isometry input — directly feeding the weakened `IsCoherent`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.orthoResidualMap_mem_zSpan
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.retarget_inner_eq_on_zSpan_union
-- (5.6.1) family bundle: the source-side cross-difference orthogonality
-- `⟨χ−aχ₁, χᵢ−aᵢχ₁⟩ = a·aᵢ·‖χ₁‖²`, derived (not posited) from `χ ⊥ S₁` + pairwise orthogonality.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.CharacterFamilyBundle.crossDifference_inner
-- (5.6.3) MAIN coherence-union assembly (general (5.6), UNCONDITIONAL): `IsCoherent (S₁ ∪ {χ,χ̄}) A`.
-- CONSTRUCTS the extension `τ₂ := retarget τ₁ χ χ̄ X X̄`, proves it a *lattice* isometry on
-- `ℤ[S₁∪{χ,χ̄}]` (`retarget_inner_eq_on_zSpan_union`, the weakened `extension_inner_eq` field — no
-- global isometry, none exists in FT), and discharges `extends_on_supported` by agreement on the
-- three difference generators `{χ−χ̄, χ−a·χ₁} ∪ Z[S₁,L^#]` (`eq_on_zSpan_of_eq_on`).  The data
-- threaded in are the honest (5.4)/(5.5)/(5.6.2) outputs (orthonormal `{X,X̄}`, `X̄ = X−(χ−χ̄)^τ`, the
-- *lattice* (5.5)+(5.2.e) orthogonality `X,X̄ ⊥ τ₁ ξ` for `ξ ∈ ℤ[S₁]`, the (5.6.2) image equation)
-- plus the (5.1)-type generation `hgen`.  No special-position restriction.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.retarget_isCoherent
-- (5.6.3) target-pair PRODUCER (G2.7 foundational brick): CONSTRUCTS the orthonormal `{X,X̄}` block
-- of `retarget_isCoherent` *from* a (5.5) decomposition `D : CharacterPsiDecomposition τ χ 0` of an
-- irreducible `χ` (`‖χ‖²=1`) plus the source-pair orthonormality.  `X := D.X`, `X̄ := D.X−(χ−χ̄)^τ`;
-- `(5.5)` gives `X = ∑_{E}α` with `|E|=‖χ‖²=1` (single element, ‖X‖²=1), `|R(χ)|=‖χ−χ̄‖²=2` (via
-- `tau1_agrees`+τ₁-isometry), so `‖X̄‖²=|R(χ)|−|E|=1`; `⟨X,X̄⟩=0` off the orthonormal family; both
-- ∈ℤ[Irr G].  This refutes the Round-20 "missing Gram–Schmidt/basis-extension" claim: for irreducible
-- `χ` the target pair is FORCED, no rescaling/orthonormalization primitive is needed.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.retargetTargetPair
-- (5.6.3) per-step assembly with target pair constructed from (5.5): `IsCoherent (S₁∪{χ,χ̄}) A` where
-- `{X,X̄}` is NOT data but built from `D` via `retargetTargetPair`.  Isolates exactly the residual that
-- genuinely couples to the running `τ₁ = hS₁.extension`: the (5.2.e) cross-orthogonality `X,X̄ ⊥ τ₁ ξ`
-- (`hX_ortho`/`hXbar_ortho`) and the (5.6.2) image equation `(χ−aχ₁)^τ = D.X − a·τ₁χ₁` (`himg`).  All
-- else (orthonormality + virtual-character membership of `{D.X, X̄}`) comes from `D`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.retarget_isCoherent_of_decomposition
-- (5.6.2) IMAGE-EQUATION SUPPLIER (G2.7 wiring): CONSTRUCTS the `himg : τ(χ−aχ₁) = X − a·τ₁χ₁`
-- hypothesis of `retarget_isCoherent` — the single genuinely running-τ₁-coupled fact — from the
-- (5.4)/(5.6.1) decomposition `D : CharacterPsiDecomposition τ χ (a·χ₁)` and three honest textbook
-- inputs: `htau1_diff` ((5.4) τ₁'=τ on the supported difference `χ−aχ₁`), `hY` ((5.6.2) `Y=a·χ₁^{τ₁'}`
-- after λ=0/Z=0), `htau1_chi1` (τ₁' agrees with the running coherence extension at `χ₁∈S₁`).  Chains
-- `τ(χ−aχ₁) = D.tau1(χ−aχ₁) = D.X − D.Y = D.X − a·D.tau1 χ₁ = D.X − a·hS₁.extension χ₁` via `tau1_image`.
-- This is the precise §4↔§7 coupling: the Dade-isometry side enters as `τ(χ−aχ₁)` (LHS, the §4 Dade
-- image of the supported difference via `dadeIntegralCharacterMap_apply_of_support`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.image_eq_of_decomposition
-- (5.6.3) COMPLETE per-step adjoining with `himg` discharged internally: the single entry point a
-- (6.6)/(6.8) `coherentPairChain` step calls — `IsCoherent τ S₁ A → IsCoherent τ (S₁∪{χ,χ̄}) A`.
-- Consumes BOTH (5.5)/(5.6.1) decompositions `D₀`/`Da` and their common `R(χ)`-projection
-- (`hX_eq : Da.X = D₀.X`, the (5.6.2) identification), builds the orthonormal pair `{D₀.X, X̄}` via
-- `retargetTargetPair` AND discharges `retarget_isCoherent`'s `himg` via `image_eq_of_decomposition`.
-- Makes (6.6) `peterfalvi_66_coherence_of_X`'s `hstep` dischargeable from the Dade-isometry targets.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.retarget_isCoherent_of_decompositions
-- (5.5)+(5.2.e) IMAGE-SIDE coupling `hperElem`, *constructed* not posited (issue 0046, PASS 2).
-- `inner_extension_member_orthogonal_imageSet` : for a member `χ'∈S₁` with its `ψ=0` decomposition
-- `D'` (so `χ'^{τ₁'}=D'.X` by (5.5)) and `R(χ')⊥R(χ)` (5.2.e) + the running agreement
-- `D'.tau1 χ'=hS₁.extension χ'`, the running image `χ'^{τ₁}` is ⊥ `R(χ)` — the per-member mmd L77.
-- `inner_extension_orthogonal_imageSet_of_members` : span induction lifts that to all `ξ∈ℤ[S₁]`
-- (`ℤ`-linearity of the extension and of `⟨·,α⟩`).  These two SUPPLY the `hperElem` of
-- `retarget_isCoherent_of_decompositions` from honest per-member data.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.inner_extension_orthogonal_imageSet_of_members
-- (5.6.3) COMPLETE per-step adjoining with ALSO `hperElem` discharged internally (issue 0046,
-- PASS 2): the final form where every (5.6.3) input reduces to genuine Dade-map / running-extension
-- facts — no image-side coupling remains posited.  Replaces `hperElem` by the per-member family of
-- `ψ=0` decompositions `Dmem`/orthogonality `hmemOrtho`/agreement `hmemTau1`, deriving `hperElem`
-- via the two lemmas above.  This makes (6.6) `peterfalvi_66_coherence_of_X`'s `hstep` dischargeable
-- from the actual Dade isometry's per-member (5.5)+(5.2.e) data.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.retarget_isCoherent_of_decompositions_and_memberFamily
-- (5.6.3) PASS 2 (ii) ENTRY POINT: per-step coherence from a SHARED-isometry decomposition pair.
-- `retarget_isCoherent_of_sharedDecomposition` takes the shared `(R(χ), τ₁, isom, agrees)` + the two
-- `ZIrr`-membership facts, builds `(D₀, Da)` via `decompositionPair`, and discharges the τ₁-agreement
-- `htau1_chi : Da.tau1 χ = D₀.tau1 χ` STRUCTURALLY (`decompositionPair_tau1_agree`).  The (5.6.3)
-- projection identity `Da.X = D₀.X` then follows from the structural agreement.  This is the clean
-- (6.6) `hstep` shape: a caller supplies the per-step Dade `R(χ)` + global τ₁ + per-member family.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.retarget_isCoherent_of_sharedDecomposition
-- (5.6.3) supporting bricks: span-agreement (`eq_on_zSpan_of_eq_on`), orthogonality lifts to the
-- ℤ-span (`inner_eq_zero_of_mem_zSpan`), and the re-targeting collapses to `τ₁` on the span of any
-- set orthogonal to `{χ,χ̄}` (`retarget_eq_on_zSpan_of_orthogonal`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.retarget_eq_on_zSpan_of_orthogonal
-- (5.5)+(5.2.e) orthogonality in sum form: from `X = ∑_{α∈R} c(α)·α` (the (5.5) `X ∈ ℤ[R(χ)]` in
-- explicit `X_eq` form) and per-element `⟨η, α⟩ = 0`, conclude `⟨η, X⟩ = 0`.  Packages the
-- `hX_ortho`/`hXbar_ortho` inputs of `retarget_isCoherent` from the per-`R(χ)`-element (5.2.e) fact.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_eq_intCast_sum
-- (6.8.1)/(6.8.2) orthogonal coherent union: the two-lattice block identity
-- `⟨νX a + νY b, νX a' + νY b'⟩ = ⟨a + b, a' + b'⟩` for `a,a'∈ℤ[X]`, `b,b'∈ℤ[Y]` under source +
-- image orthogonality (the algebraic heart of Peterfalvi's `τ₃` gluing of two coherent pieces).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.inner_orthogonal_glued_eq
-- (6.8.1)/(6.8.2) the same identity lifted to all of `ℤ[X∪Y]` for any map `ν` agreeing with `νX` on
-- `ℤ[X]` and `νY` on `ℤ[Y]` (`Submodule.span_union` decomposition) — the weakened
-- `IsCoherent.extension_inner_eq` field for the union `X ∪ Y` once the two coherent pieces exist.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.inner_eq_on_zSpan_union_of_orthogonal
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.image_orthogonal_of_mixed_inner_eq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.mixed_inner_eq_on_zSpan_of_eq_on
-- (6.8.1)/(6.8.2) the `τ₃` assembly into an actual `IsCoherent (X∪Y) A` witness: from two coherence
-- witnesses `hX`, `hY`, a glued map `ν` agreeing with `hX.extension`/`hY.extension` on `ℤ[X]`/`ℤ[Y]`,
-- and source+image orthogonality, build `IsCoherent τ (X∪Y) A` — `extension_inner_eq` via
-- `inner_eq_on_zSpan_union_of_orthogonal`, `extends_on_supported` via `eq_on_zSpan_of_eq_on` on the
-- generator `Z[X,A] ∪ Z[Y,A]` and a (5.1)-type generation hypothesis.  The two-family analogue of
-- `retarget_isCoherent`; carries no character theory (its inputs are supplied by (6.6)/(6.7)/Dade).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherentUnion_of_glued
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_mixed_inner_eq
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_generator_mixed_inner_eq
-- (6.6) "repeated use of (5.6)" iteration engine: from a coherent base `S₀` and a per-index
-- adjoining step `IsCoherent (pairUnion S₀ pair i) → IsCoherent (pairUnion S₀ pair (i+1))` (each step
-- one application of (5.6) = `retarget_isCoherent` with the caller's per-step data), the union after
-- `N` adjoinings `pairUnion S₀ pair N` is coherent — the induction is derived, never posited.  The
-- accumulated-set monotonicity helper is `pairUnion_mono`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherentPairChain
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.pairUnion_mono
-- (6.6) conclusion "X is coherent" (mmd L84): `coherentOfPairChainCover` assembles it from the
-- degree-ordered pair-chain decomposition of `X` (base prefix `S₀` + remaining conjugate pairs,
-- certified to recover `X` by `pairUnion_eq_of_cover` via the membership lemma `mem_pairUnion`)
-- and the `coherentPairChain` engine.  The base coherence `h0` (= (1.1)+(1.4) prefix) and the
-- per-step (5.6) adjoining `hstep` are *supplied* (the residual to fill is `hstep`'s per-step
-- `{Xᵢ, X̄ᵢ}` target data, needing the Dade-isometry ν basis extension, G2.7); the conclusion
-- `IsCoherent τ X A` is derived from them through the chain.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.mem_pairUnion
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.pairUnion_eq_of_cover
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherentOfPairChainCover
-- (6.6) named conclusion `peterfalvi_66_coherence_of_X : … → IsCoherent τ X A` (mmd L74/L84):
-- "X = {χ ∈ Irr L | Z ⊄ Ker χ} is coherent".  Assembles the (6.6) proof at the textbook altitude
-- by threading the degree-monotone enumeration `e` of `exists_monotoneDegreeEnum` (mmd L76 opening
-- "Set X = {χ₁,…,χₙ}, χ₁(1) ≤ ⋯ ≤ χₙ(1)") into the `coherentPairChain` accumulator via
-- `pairUnion_eq_of_enumCover`: the enum's *surjectivity* onto `X` reduces the engine's set-level
-- cover to the index-level cover `hcoverIdx` (checked along χ₁,…,χₙ), so the accumulator
-- `pairUnion S₀ pair N` is identified with `X` and folded coherence (`coherentPairChain`) lands as
-- `IsCoherent τ X A`.  Base prefix coherence `h0` ((1.1)+(1.4)) and per-step (5.6) adjoining `hstep`
-- (degree side already discharged by `two_mul_lt_sq_of_primePow_gap`/`sumInflatedDegreeSq`) are
-- supplied; the residual is `hstep`'s per-step `{Xᵢ,X̄ᵢ}` target data (Dade-isometry ν extension, G2.7).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.pairUnion_eq_of_enumCover
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.peterfalvi_66_coherence_of_X
-- (6.6) opening "Set X = {χ₁,…,χₙ} where χ₁(1) ≤ ⋯ ≤ χₙ(1)" (mmd L76): the degree-sorted indexing
-- of the finite set `X = S − S(Z)`.  `exists_monotoneDegreeEnum` produces an injective surjection
-- `e : Fin (X.ncard) → X` monotone in the real degree key `χ ↦ (characterDegree χ).re` — the purely
-- order-theoretic "sort a finite family by a real key" step (`Tuple.sort`/`Tuple.monotone_sort`),
-- stated for an arbitrary finite class-function set (no irreducibility / induced-structure used).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.exists_monotoneDegreeEnum
-- (6.6) opening "By (1.1), n ≥ 2" (mmd L76): the count `n = |X|` of the irreducible characters of
-- `L` not killing `Z` satisfies `n ≥ 2`.  The two consequences of (1.1) used — closure under
-- conjugation (`ClosedUnderConjugate`) and no real character (`HasNoRealCharacters`), both §7
-- `Hypothesis` fields inherited by `X ⊆ S` — plus nonemptiness yield, via the conjugation
-- involution `χ ↦ χ̄`, a second distinct member, hence `2 ≤ X.ncard` (`Set.one_lt_ncard`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.two_le_ncard_of_conjugate_closed_of_noReal
-- (6.6) prime-power degree gap (mmd L82): the strict bound `2·χᵢ(1)·χ₁(1) < ∑_{j<i}χⱼ(1)²` that
-- each `coherentPairChain` step's (5.6.2) integer-forcing (`int_eq_zero_of_sq_mul_le_of_two_mul_lt`)
-- consumes.  `two_mul_lt_sq_of_primePow_gap`: `dᵢ = q·d₁`, `q = p^m`, `p ≥ 3`, `d₁ < dᵢ` ⟹
-- `2·dᵢ·d₁ < dᵢ²` (`q ≥ p ≥ 3` gives `dᵢ ≥ 3·d₁`).  `two_mul_degree_lt_sum_ratCast`: chains the gap
-- through the square-divisibility `dᵢ² ∣ D` (= `χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`) to the `ℚ` bound `2·a < D`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_primePow_gap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.two_mul_degree_lt_sum_ratCast
-- (5.6.1)→(5.6.2) Y-collapse producer (mmd L71-97): from the (5.4) decomposition `Da` and the
-- source family bundle `B`, *constructs* `Da.Y = a·χ₁^{τ₁}` — projects `Y` onto `{χᵢ^{τ₁}}`,
-- computes the single integer `λ` via the cross-orthogonality `crossDifference_inner` transported
-- through the isometry, and collapses `λ = 0` with `Y_eq_nsmul_tau1_of_lambdaForm`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.Y_collapse_of_family
-- (5.2.d) base coherence — the seed `h0`/`hS₁` every chain consumes but none constructed.
-- `zSupportedSpan_pair_subset_span`: supported combos of `{χ,χ̄}` (equal degree, `1∉A`) are multiples
-- of `χ−χ̄`.  `coherentPair`: `IsCoherent τ {χ,χ̄} A` from orthonormal target pair `{X,X̄}` (S₁=∅
-- retarget).  `coherentPair_fromDade`: the seed at the real Dade τ, target pair from `retargetTargetPair`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.zSupportedSpan_pair_subset_span
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherentPair
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherentPair_fromDade
-- (5.6.1)→(5.6.2) at the Dade base map: the same Y-collapse for any `Da` with `Da.tau1 = τ`, with
-- every hypothesis of `Y_collapse_of_family` discharged from the Dade isometry + prior coherence
-- (`dadeIntegralCharacterMap_inner_eq_on_supported_span`, `inner_extension_member_orthogonal_imageSet`,
-- `dadeIntegralCharacterMap_mem_ZIrr_of_supported`).  Only genuine (6.6) source data remains as input.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dade_Y_collapse_of_family
-- (6.6) square-divisibility producers (mmd L78-80): the `hdvd : χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²` input.
-- `dvd_of_add_eq_of_dvd_dvd`: additive complement `head + tail = total`, `a∣tail`, `a∣total` ⟹
-- `a∣head` (combine `θᵢ(1)² ∣ ∑_{j≥i}` and `θᵢ(1)² ∣ |L|-|L:Z|` through the sum identity).
-- `sq_dvd_of_factored_coprime`: `χᵢ(1) = idx·θ`, `θ²∣D`, `idx²∣D`, `Coprime idx θ` ⟹ `χᵢ(1)²∣D`
-- (mmd L80 coprimality forcing, `idx = |L:K|` prime to `p`).
-- `sq_dvd_of_factored_coprime_add_complement`: combines the additive complement with coprimality
-- forcing so the consumer can derive `χᵢ(1)²∣head` directly from tail/total divisibility data.
-- `sq_dvd_sum_sq_mul_of_dvd`: degree-sort divisibility `θ∣θⱼ` over the tail implies
-- `θ²∣∑(idxⱼ·θⱼ)²`, discharging the `Finset.dvd_sum` part of `θ²∣tail`.
-- `dvd_primePow_of_le`/`dvd_primePow_of_mul_le_mul`: sorted p-power degree factors imply
-- divisibility, with cancellation of the common positive induction index `idx`.
-- `mul_primePow_dvd_mul_primePow_of_le`: upgrades that factor divisibility to full induced degrees.
-- `sq_dvd_sum_sq_mul_const_of_primePow_mul_le`: packages that cancellation with `Finset.dvd_sum`
-- to produce the tail-side divisibility directly from sorted induced p-power degrees.
-- `sq_dvd_primePow_of_sq_le`/`sq_dvd_primePow_mul_of_sq_le`: turn the Schur-center bound
-- `θ²≤p^n` for p-power degrees into total-side divisibility, with an optional product factor.
-- `sq_dvd_head_of_commonIndex_primePower_sums`: assembles tail/total/head divisibility into
-- the `χᵢ(1)²∣head` input consumed by the §8 X-adjoin constructors.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dvd_of_add_eq_of_dvd_dvd
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.sq_dvd_of_factored_coprime
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.sq_dvd_of_factored_coprime_add_complement
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.sq_dvd_sum_sq_mul_of_dvd
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dvd_primePow_of_le
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dvd_primePow_of_mul_le_mul
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.mul_primePow_dvd_mul_primePow_of_le
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.sq_dvd_sum_sq_mul_const_of_primePow_mul_le
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.sq_dvd_primePow_of_sq_le
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.sq_dvd_primePow_mul_of_sq_le
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.sq_dvd_head_of_commonIndex_primePower_sums

-- Peterfalvi (5.1) Dade-isometry base map (G2.7 type-bridge): the §4 Dade map is `ℂ`-linear on the
-- supported subspace `CF(L,A)` (`Hypothesis.dadeLinearMap`, the bare `DadeMap` repackaged via the
-- pointwise `dadeValue α g = α(a)` evaluation), and `dadeIntegralCharacterMap` extends it to a total
-- `IntegralCharacterMap ↥L G` (`LinearMap.exists_extend` over the field `ℂ`, then `restrictScalars
-- ℤ`).  `dadeIntegralCharacterMap_apply_of_support` is its defining property: on `CF(L,A)` the lift
-- *is* the Dade map, supplying the (5.6.3) base map `τ` from the actual §4 isometry.  The extension
-- off `CF(L,A)` is unconstrained — `IsCoherent τ S A` only inspects `τ` on `zSupportedSpan S A`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.dadeLinearMap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support

-- Peterfalvi (5.1)/(5.4) Round-13 supply-ability + Round-24 (ii) per-step production.  The
-- `CharacterPsiDecomposition.tau1_inner_eq_on_support` field (and the `ofProjection`/`decompositionPair`
-- inputs) were weakened from a GLOBAL `IsIntegralIsometry` to LATTICE-RELATIVE inner-preservation on
-- the supported sponsoring span `ℤ[χ, χ̄, ψ]` (the same Round-13 weakening already applied to
-- `IsCoherent.extension_inner_eq`; a global isometry `CF(L)→CF(G)` does not exist in FT where
-- `dim CF(L) > dim CF(G)`).  `support_subset_of_mem_zSpan_of_supported` is the `ℤ`-submodule closure
-- fact (`Submodule.span_le` into `supportedSubmodule.restrictScalars ℤ`);
-- `dadeIntegralCharacterMap_inner_eq_on_supported_span` SUPPLIES the weakened form from the Dade
-- isometry's `CF(L,A)` inner-preservation (`IsDadeIsometry.inner_eq`, (2.6.a)).
-- `decompositionPairFromDade` then PRODUCES the per-step `(D₀, Da)` pair directly from the Dade
-- isometry — `htau1_inner_eq` discharged internally — closing Round-24 (ii).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.support_subset_of_mem_zSpan_of_supported
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.decompositionPairFromDade

-- Round B: the Dade `R(χ)` extractor + ZIrr-membership, constructing the per-step (5.6) inputs
-- ENTIRELY from the Dade isometry (no opaque `OrthonormalCharacterImageFamily`/`ZIrr` hypotheses).
-- `one_notMem_dadeSupport` (S04): `1 ∉ dadeSupport` (from `a ≠ 1` + `centralizer_disjoint`).
-- `dadeIntegralCharacterMap_apply_one_eq_zero`: the Dade image vanishes at `1` (vanishes off
-- `dadeSupport` via `IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`; `1 ∉ dadeSupport`) — discharges
-- the (1.4) `IsometryDifferenceImagesVanishAtOne`.  `dadeIntegralCharacterMap_mem_ZIrr_of_supported`:
-- supported virtual characters map into `ℤ[Irr G]` ((2.6.b) `PreservesVirtualCharacters`/
-- `maps_virtualCharacter`) — discharges the (1.4) `IsometryDifferenceImagesAreVirtual` and the two
-- `htau1_mem0`/`htau1_mema` facts.  `dadeOrthonormalCharacterImageFamily` is the R(χ) extractor: it
-- discharges the three (1.4) hypotheses of `characterDifferenceImageOfIsometry` for the Dade map on
-- `{χ, χ̄}` and lifts via `toOrthonormalImage` to `OrthonormalCharacterImageFamily`.
-- `decompositionPairFromDadeOfIrreducible` is the full assembly: from `χ` irreducible non-real +
-- supported + `χ₁ ∈ ℤ[Irr L]` it builds BOTH `R(χ)` AND the `ZIrr` facts internally, producing the
-- per-step `(D₀, Da)` pair for `retarget_isCoherent_of_sharedDecomposition` from the real Dade τ.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S04.Hypothesis.one_notMem_dadeSupport
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamily
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_conjDifference_eq_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamily_orthogonal
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.decompositionPairFromDadeOfIrreducible

-- Round C: the running-`τ₁` instantiation.  `retarget_isCoherent_fromDade` discharges one (6.6)
-- `coherentPairChain` step `IsCoherent τ S₁ A → IsCoherent τ (S₁ ∪ {χ, χ̄}) A` against the (5.1)
-- base map `τ = dadeIntegralCharacterMap` AS the running auxiliary isometry `τ₁ = τ` itself.  The
-- four agreement obligations of `retarget_isCoherent_of_sharedDecomposition` are discharged
-- internally: `htau1_agrees`/`htau1_diff` are `rfl` (the decomposition's `tau1` field IS `τ`), and
-- `htau1_chi1`/`hmemTau1` (agreement with the running `hS₁.extension` on `χ₁` and on every member
-- `x ∈ S₁`) come from `IsCoherent.extends_on_supported` — the running extension agrees with `τ` on
-- the supported sublattice `Z[S₁, A]`, where `χ₁` and the members are supported.  The `R(χ)` family +
-- `ZIrr` facts are Round B; the residual inputs (`hY` (5.6.2) collapse, `hmemOrtho` (5.2.e) image
-- orthogonality, source orthogonalities, `hgen`) are the genuine per-step (6.6) character-degree
-- content (the (6.6) enumeration's responsibility, not the Dade isometry's).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.retarget_isCoherent_fromDade

-- Round C assembly: the (6.6) coherence-of-X INSTANTIATED at the real Dade isometry.
-- `pairUnion_succ_eq_union_pair`: the set-level bridge `pairUnion S₀ pair (i+1) = pairUnion S₀ pair i
-- ∪ {c₁, c₂}` when `(pair i) = (c₁, c₂)` — connects the per-step adjoining engine's `S₁ ∪ {χ, χ̄}`
-- conclusion to the `coherentPairChain` accumulator shape.  `DadeChainStep` bundles the genuine
-- per-step (6.6) character-degree content (the residual after the Dade isometry supplies `R(χ)`, the
-- `ZIrr` facts, the inner-preservation, the `τ₁ = τ` agreements); `DadeChainStep.advance` discharges
-- one (5.6) step via `retarget_isCoherent_fromDade`, and `DadeChainStep.chainStepAdvance` rewrites it
-- into the accumulator shape.  `peterfalvi_66_coherence_of_X_from_dade` then folds these over the
-- chain: the (6.6) `hstep` is no longer posited but CONSTRUCTED from the Dade isometry + prior
-- coherence, so the §5/§6 coherence engine is fully constructive against the real Dade `τ`.  The only
-- remaining inputs (enumeration `e`, cover `hcoverIdx`, base coherence `h0`, per-step `hstepData`/
-- `hpairχ`) are the genuine (6.6) character content, not the Dade isometry's responsibility.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.pairUnion_succ_eq_union_pair
-- `zSupportedSpan_adjoinPair_subset_span`: the (5.6.3) generation containment `ℤ[S₁ ∪ {χ, χ̄}, A] ⊆
-- ℤ[ℤ[S₁, A] ∪ {χ − χ̄, χ − a·χ₁}]`, discharged as pure ℤ-module theory routed through the
-- difference generators (no (4.7) `ℤ[S, L^#] = ℤ[S, A]` needed): `χ = (χ − a·χ₁) + a·χ₁`,
-- `χ̄ = χ − (χ − χ̄)`, every `s ∈ S₁` a right-hand generator by supportedness.  This is what makes
-- `DadeChainStep.advance` discharge the (5.1) generation hypothesis internally rather than positing it.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.DadeChainStep.advance
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.DadeChainStep.chainStepAdvance
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.peterfalvi_66_coherence_of_X_from_dade

-- Diagonalization keystone (shared gate for Peterfalvi (6.6) G2.2 + G2.5):
-- `character g = character 1 ⟹ ρ g = id`.  `ρ g` finite-order ⇒ semisimple (squarefree
-- `X ^ n - 1`); trace = sum of unit-modulus eigenvalues = degree = count forces every eigenvalue
-- to be `1` (triangle-inequality equality case `all_eq_one_of_norm_eq_one_of_sum_eq_card`).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.all_eq_one_of_norm_eq_one_of_sum_eq_card
#assert_only_allowed_axioms OddOrder.RepresentationTheory.rep_eq_id_of_character_eq_one
#assert_only_allowed_axioms OddOrder.RepresentationTheory.character_eq_one_iff_rep_eq_id
-- Peterfalvi (6.7) central-character constancy core: `ω_ρ(⟦z⟧) = |⟦z⟧|·χ_ρ(z)/χ_ρ(1)` depends only
-- on `χ_ρ(z)` and `|⟦z⟧|`, so equal class size + equal char value ⟹ equal `ω` (the "α does not
-- depend on s" of mmd 04.8 L102).  Plus the TI fact `C_G(x) ⊆ L` (`x ∈ A`, `A` TI / normalizer `L`)
-- giving `|C_G(z)| = |C_L(z)|`, the source of the class-size constancy from `|C_L(z)|`-constancy.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.centralCharacterOfRep_eq_of_card_eq_of_character_eq
#assert_only_allowed_axioms OddOrder.RepresentationTheory.centralizer_le_of_mem_isTISubset
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_class_eq_of_inf_centralizer_card_eq
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.centralCharacterOfRep_eq_of_tiSubset_card_eq_of_character_eq
#assert_only_allowed_axioms OddOrder.RepresentationTheory.character_one_mul_centralCharacterOfRep_mk
-- Peterfalvi (6.7.2)/(6.7.3) RHS collapse and top wiring: split the `C_s ∩ Z` sum into the
-- identity class and the nonidentity `Z^#` classes, then feed the two collapsed congruences into
-- the existing (6.7.3) arithmetic assembly to obtain `ψ(z) ≡ ψ(1) (mod |P|)`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.classSum_mul_apply_one_eq_classSumCoeff_one
#assert_only_allowed_axioms OddOrder.RepresentationTheory.isIntegral_sum_classSum_mul_coeff
#assert_only_allowed_axioms OddOrder.RepresentationTheory.nonidentityZClassCoeffSum_isIntegral
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.centralCharacterOfRep_sum_inZ_eq_identity_add_nonidentity
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset
#assert_only_allowed_axioms OddOrder.RepresentationTheory.peterfalvi_67
-- General character-value bound `|χ(g)| ≤ χ(1)` (the inequality the (6.6) G2.2 residual flags as
-- needs-infra), via the same root-of-unity / triangle machinery; equality case is the keystone.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.norm_character_le_finrank
-- Peterfalvi (6.6) G2.2 representation-level constituent-inherits-kernel: `g ∈ ker χ_ρ` (whole-rep
-- character = degree) ⟹ `g ∈ ker χ_{ρ'}` for every subrepresentation `ρ'` (keystone: `ρ g = id`
-- restricts to `id` on the invariant submodule, so its character = dimension = degree).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.subrepresentation_character_eq_one_of_character_eq_one

-- Inflation infrastructure ([Isaacs] (2.22), gating Peterfalvi (6.6) G2.5 degree-sum):
-- irreducibility is preserved under surjective precomposition, hence the inflation map
-- `Irr(G ⧸ N) → Irr G`, `χ̄ ↦ χ̄ ∘ (mk' N)`, is degree-preserving with `N ⊆ ker`.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.Representation.isIrreducible_comp_of_surjective
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
#assert_only_allowed_axioms OddOrder.RepresentationTheory.inflate_apply_one
#assert_only_allowed_axioms OddOrder.RepresentationTheory.subset_characterKernel_inflate
-- Injective half of the inflation bijection: distinct quotient characters inflate to distinct
-- characters (surjective precomposition is injective on class functions).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.ClassFunction.compHom_injective_of_surjective
#assert_only_allowed_axioms OddOrder.RepresentationTheory.inflate_injective
-- Surjective half (the keystone consumer): every irreducible `χ` with `N ⊆ ker χ` is an inflation
-- `inflate N χbar`.  `ρ n = id` on `N` (keystone) ⇒ `ρ` descends through `Representation.ofQuotient`
-- to an irreducible `σ` on `G ⧸ N` with `χ_σ ∘ mk' = χ`.  Completes the inflation bijection (2.22).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.Representation.isIrreducible_of_isIrreducible_comp_of_surjective
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_inflate_eq_of_subset_characterKernel
-- Peterfalvi (6.6) degree-sum (the G2.5 payoff): the inflation bijection transports Burnside on
-- `G ⧸ N` to `∑_{χ ∈ Irr G, N ⊆ ker χ} χ(1)² = |G ⧸ N|`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.sumInflatedDegreeSq
-- Complement degree-sum (the planned G2.5 payoff): `∑_{χ ∈ Irr G, N ⊄ ker χ} χ(1)² = |G| − |G ⧸ N|`,
-- the (6.6)/(6.8) set `X = {χ | Z ⊄ ker χ}` total `|L| − |L:Z|` (mmd 04.8 L78, L234).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.sumNonInflatedDegreeSq
-- Peterfalvi (6.8.3) degree-sum factored form: `∑_{χ ∈ Irr G, N ⊄ ker χ} χ(1)² = [G:K][K:N](|N|−1)`
-- for `N ⊴ G`, `N ≤ K ≤ G` (= `sumNonInflatedDegreeSq` + Lagrange index arithmetic).  The mmd
-- 04.8 L234 identity `|W₁||H:Z|(|Z|−1)` of the (6.8.3) final inequality (`G = L`, `K = H`, `N = Z`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.sumNonInflatedDegreeSq_eq_index_mul
-- Section form of [Is] Cor 2.30 (Peterfalvi (6.2)/(6.6) θ-bound section case): φ trivial on N,
-- D/N central in G/N ⟹ φ(1)² ≤ |G:D|, via inflation to G/N + the central degree bound.
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.RepresentationTheory.degree_sq_le_index_of_central_quotient
-- An irreducible character trivial on `N ⊴ G` with abelian quotient `G/N` is linear (degree 1),
-- via inflation/descent + abelian degree-one.  Peterfalvi (9.9.a) `(θλ)(1)=1` (issue 2031/2030).
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
-- Constituent transitivity: A ≤ B ≤ G, A ⊄ ker χ ⟹ some constituent ψ of Res_B χ has A ⊄ ker ψ.
-- Clifford-correspondent existence for Peterfalvi (9.9.a) (issue 2031/2030).
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_constituent_not_subset_characterKernel

-- Coefficientwise Galois transport for class functions, irreducible-character indices,
-- virtual-character lattices, and S07 coherence data.  Galois conjugates of irreducible
-- characters are irreducible (unconditional; witness = the σ-twisted representation
-- `galoisTwist`), giving the Galois permutation of Irr(G) and ℤ[Irr G] invariance.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_inner
#assert_only_allowed_axioms OddOrder.RepresentationTheory.character_galoisTwist
#assert_only_allowed_axioms OddOrder.RepresentationTheory.isIrreducible_galoisTwist
#assert_only_allowed_axioms OddOrder.RepresentationTheory.IsIrreducibleCharacter.mapRingEquiv
#assert_only_allowed_axioms OddOrder.RepresentationTheory.IrreducibleCharacter.galoisMap
#assert_only_allowed_axioms OddOrder.RepresentationTheory.IrreducibleCharacter.galoisPerm
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_mem_irreducibleCharacters
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_mem_ZIrr
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_mem_ZIrr_iff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.ClassFunction.mapRingEquiv_mem_zSpan_image
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.ClassFunction.mapRingEquiv_mem_zSupportedSpan_image
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.IntegralCharacterMap.galoisTransport
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.IsCoherent.galoisTransport
-- Peterfalvi (1.9): cyclotomic Galois automorphisms of ℂ and the character value formula
-- χ^σ(g) = χ(g^k).  Trace of finite-order endomorphisms (eigenvalue decomposition), the
-- extension theorem (subfield automorphisms extend to ℂ via a transcendence basis), the
-- CRT cyclotomic automorphism (1.9.a), and the uniform virtual-character form (1.9.b).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.map_trace_of_pow_eq_one
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr
#assert_only_allowed_axioms OddOrder.RepresentationTheory.exists_complexRingEquiv_extends
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_complexRingEquiv_pow_of_rootsOfUnity
#assert_only_allowed_axioms OddOrder.RepresentationTheory.exists_complexRingEquiv_pow_and_fixed
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_complexRingEquiv_mapRingEquiv_eq_pow
-- Peterfalvi (5.9)(a): coherent isometric extensions of the Dade map commute with
-- coefficientwise automorphisms on the coherent set (no star-commutation needed).  Inputs:
-- the explicit Dade map is pointwise evaluation (commutes with σ) and vanishes at 1; norm-1
-- virtual characters are ± irreducible with a uniform sign.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_zsmul_irreducibleCharacter_of_inner_self_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_mem
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.IsCoherent.extension_mapRingEquiv_comm
-- Peterfalvi (6.8.2.1), generic forms: the coherent extension takes equal values at x and
-- x^k ((1.9.b) + (5.9.a) + Dade value restoration), hence is constant on Z^# for prime Z.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.IsCoherent.extension_apply_coe_pow_eq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IsCoherent.extension_constant_on_sharp_of_prime
-- [Is] Lemma 2.27 (central restriction): Res_Z χ = χ(1)·φ with φ a linear character of
-- Z ≤ Z(G), via Schur central scalars.  Peterfalvi (6.8.2.3) `Res^H_Z θ = a·φ`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.isIrreducible_complex_rep
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.exists_central_linear_restriction
-- Peterfalvi (6.7), odd-order assembly: hreal from |L| odd, the structure-constant
-- congruence from the trivial-character specialization of (6.7.2)-(6.7.3).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.nonidentityZClassCoeffSum_cong_of_isTISubset
#assert_only_allowed_axioms OddOrder.RepresentationTheory.peterfalvi_67_of_odd
-- Peterfalvi (1.1)+(1.4) equal-degree coherence: `range χ` is coherent for an orthonormal,
-- equal-degree family, with extension the Fourier-image map `ν φ = ∑ⱼ ⟨φ, χⱼ⟩ • Xⱼ`
-- (`coherentImageMap`).  The seed for both the (6.6) equal-minimal-degree base prefix and the
-- (6.8) set `Y = S(H')`, where the (5.6) degree induction is unavailable.  The isometry on
-- `ℤ[range χ]` is pure Parseval (`coherentImageMap_inner_eq`); the supported sublattice is
-- generated by the differences `χⱼ − χ₀` (`zSupportedSpan_range_subset_span_sub_zero`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S07.IntegralCharacterMap.coherentImageMap_inner_eq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.zSupportedSpan_range_subset_span_sub_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherentEqualDegree
-- Dade specialization: equal-degree coherence at the real (5.1) base map `τ = dadeIntegralCharacterMap`.
-- The (1.4) signed family `{μⱼ, ε}` is constructed by `isometry_difference_pair_structure` applied to
-- `τ` (its three hypotheses discharged from the Dade isometry), giving `Y = S(H')`/(6.6)-prefix
-- coherence with no opaque hypotheses — only the genuine equal degree and supports.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade
-- Peterfalvi S08 T7 X-characterization support layer: restriction preserves characters,
-- nonzero constituents force kernel containment, induced characters decompose with natural
-- multiplicities, and the resulting `Xset` is exactly the irreducibles not killing `Z`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.isCharacter_restrict
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.induce_exists_natFinsupp_eq_sum
-- θ-bound a-half: `Ind_C^K φ` of a genuine `φ` is genuine (brick 2), assembled with brick 1 into
-- the (6.2) degree bound `θ(1) ≤ |K:C|·φ(1)` for an induced-character constituent `φ` of `θ`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.isCharacter_induce
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.theta_degree_le_index_mul_constituent
-- full (6.2) θ-bound: a-half × b-half + √ arithmetic ⟹ `θ(1) ≤ |K:C|·√|C:D|` (constituent kernel
-- inheritance discharges the b-half's `N ⊆ Ker φ` from `N ⊆ Ker(Res θ)`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.theta_degree_le_index_mul_sqrt_index
-- (6.2) step (ii), B2 assembled: the `S(A)` degree-sum `∑_{χ∈S(A)} χ(1)²/‖χ‖² = [G:H]·(|H:A|−1)`,
-- combining the orbit-counted `sum_div_normSq_induce_image_eq` with the inflation degree-sum
-- `sumInflatedDegreeSq_ntrivial` over the (conjugation-invariant, as `A ⊴ G`) kernel-filter `T`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.sum_div_normSq_induce_kernelFilter_eq
-- Standalone general Hypothesis (6.1) coherence theorems (`K` solvable, `H ≤ K` nilpotent, `K ≠ H`),
-- the form the §11/§13 maximal-subgroup analysis needs (the Sibley `six_two`/`six_three` have `K = H`).
-- `IsCoherent.subset`: coherence is inherited by subsets with a nonzero supported witness (general
-- monotonicity of the (5.1) predicate).  `six_three_descent`: Peterfalvi (6.3)'s minimal-`A` descent
-- (maximal-`B` + nilpotency-forces-centrality + `√`-arithmetic) reduced to the (6.2) index oracle.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.IsCoherent.subset
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.six_three_descent
-- (6.3) per-step index bound, general form: tower index multiplicativity (`|K:A| = |H:A|·|K:H|`,
-- `|L:H| = |K:H|·|L:K|`) feeding `six_three_HH1_le`; reduces the `six_three_descent` `h62` oracle to
-- the general `six_two` (6.2) bound for a solvable `K` (the single remaining deep gate).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.six_three_index_bound_general
-- general `six_two` assembly: `map_mk'_le_center_iff` (image-in-centre ⟺ commutator condition);
-- `inducedMember_re_le_general` (the (6.2) θ-degree bound `ψ(1) ≤ |L:H|·√|H:A|` for a member induced
-- from the *solvable* kernel `K ⊋ H`, Clifford a-half + b-half via `theta_degree_le_index_mul_sqrt_index`,
-- centrality transported across `↥(H.subgroupOf K) ≃* ↥H`); `six_two_general` (Peterfalvi (6.2), general
-- (6.1) form: reduces `|K:A|−1 ≤ 2|L:H|·√|H:A|` to the (5.6) coherence oracle `h56` — the cross-lane
-- §10–§12 muGrid bound, issue 2022 — by proving everything downstream of it).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.map_mk'_le_center_iff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inducedMember_re_le_general
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.six_two_general
-- `six_three_of_six_two_oracle`: the single-cite (6.3) producer for §11/§13 — bundles
-- `six_three_descent ∘ six_three_index_bound_general ∘ six_two_general`, leaving the (5.6) break-member
-- oracle `h56` (the §10–§12 muGrid bound) as the only character-theoretic hypothesis.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.six_three_of_six_two_oracle
-- General-kernel (6.1) family `S(X) = {Ind_K^L θ | θ ∈ Irr K, θ ≠ 1, X ⊆ Ker θ}` (the issue-2022
-- `h56` producer layer, Coq `seqIndD K L K X`): the antitone/finite/conjugation-closed suite, the
-- degree-`|L:K|` anchor member (Coq `exists_linInd`), and the (6.2) B2 degree-square identity
-- `∑_{χ∈S(X)} χ(1)²/‖χ‖² = |L:K|·(|K:X|−1)` in real form (general-kernel form of
-- `sum_re_div_normSq_SsubFiltration_eq`; members may be reducible μ-columns).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.exists_inducedKernelFamily_member_degree_index
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.sum_re_div_normSq_inducedKernelFamily_eq
-- Break pair for *incomparable* filtrations (Peterfalvi (6.2) assumes no `S(A) ⊆ S(B)`; §11's
-- (11.4) instantiates `(A,B) = (H₁, H₀C)` with neither containing the other): the absorption chain
-- runs over `Sa ∪ Sb`, and a fully-absorbed chain would make `Sb` coherent by restriction
-- (`IsCoherent.subset` + the nonzero supported witness), so a break pair `ψ ∈ Sb` exists.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_coherentBreakPair_union
-- General-kernel family structure + the h56 producer chain (issue 2022): pairwise orthogonality /
-- real positive norms / real-freeness (odd order) of the possibly-reducible family; K^#-supported
-- scaled and conjugate member differences; the norm-weighted (5.6) member-family bound at a break
-- (`coherentDegreeSqNormBound_of_not_coherentW_k` fed from the family layer, with the (5.2.d)
-- decomposition data `Da`/`datum` as the sole grid-backed inputs); the (6.2) S(A')-sum comparison
-- (B2); and the producer `exists_source_index_le_two_psi_of_break` — from `S(A')` coherent,
-- `S(B)` not, an anchor, and the decomposition data, a source `θ ∈ Irr K` trivial on `B` with
-- `|K:A'| − 1 ≤ 2·(Ind_K^L θ)(1)` — exactly the `h56` oracle of `six_three_of_six_two_oracle`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inducedKernelFamily_breakChar_fields
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.inducedKernelFamily_degreeSqNormReBound_of_break_k
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inducedKernelFamily_SA_sum_le_two_psi_k
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_source_index_le_two_psi_of_break
-- h56 hdatum discharge helpers: the per-member (5.2.d) datum for an *irreducible* member
-- (`memberExtensionDecomposition` with the coherent extension, coupling definitional), the break
-- decomposition `Da` for an *irreducible* break (`decompositionDaFromDadeOfDiff`, `tau1 = τ`
-- definitional), both exposing their `R(·)` image families as equations; their composition
-- discharges the full `hdatum` clause on the irreducible–irreducible diagonal
-- (`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` + family orthogonality), leaving only
-- pairs involving a reducible μ-column to the §11 grid (issue 2022).  Plus the anchor from a
-- non-invariant linear source ([Is] 6.34) and the `S(X)`-nonemptiness pin.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.inducedKernelFamily_memberDatum_of_irreducible
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inducedKernelFamily_breakDa_of_irreducible
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.inducedKernelFamily_memberDatum_orthogonal_breakDa_of_irr_irr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_anchor_of_linear_of_inertia_eq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.inducedKernelFamily_nonempty_of_commutator_ne_top
-- §11 routine pins for the h56 producer (S13_SixTwoBridge): Peterfalvi's type-P support is
-- exactly `A(M) = (M')^#` (typePA_eq_sharpSubgroup_derivedInG), so `(M')^# ⊆ A₀(M)` (hKsupp);
-- `1 ∉ A₀(M)` (h1A, S04.ne_one); `|M|` odd in the minimal-simple-odd ambient (hodd); and the
-- pinned §10 family `S12.inducedFamily` IS the general kernel-filter family at `X = ⊥`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.mderivSharp_subset_A0
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.one_notMem_A0
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot
-- The h56 producer fully pinned to the §10/§11 context (S12.Hypothesis): genuine Dade data on
-- A₀(M), kernel M', routine pins burned in; remaining hypotheses = anchor + S(B)-nonempty +
-- the grid-backed (5.2.d) decomposition data.  Conclusion = the h56 oracle shape.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.exists_source_index_le_two_psi
-- NOTE: `S12.Hypothesis.isTypeIIIorIV` / `coprime_card_W1_derived` (anchor prerequisites,
-- S13_SixTwoBridge) cite `no_typeV_maximal` ((10.10), currently sorried upstream) — honest
-- sorried-cites, NOT registered here until the (10.10) chain is axiom-clean.
-- (6.5) chief-factor core + (6.5)(b) reduction: a Frobenius-acted abelian section obeying the (6.3)
-- index bound `≤ 4|R|²+1` is a `p`-group (chief-factor argument via the `p`-primary component,
-- `card_modEq_one` + `six_five_chief_factor_contradiction`); combined with the nilpotent
-- abelianization lemma this yields "`H` is a `p`-group" for the (6.8) capstone.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.isPGroup_of_card_le_of_isFrobeniusAction
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization
-- (6.5)(b) in the (6.8)(c1) Frobenius case: `IsFrobeniusGroup G N A` + nilpotent kernel + the
-- `≤ 4|A|²+1` bound ⟹ `N` is a `p`-group.  The FPF `A`-action on `Abelianization N` is supplied
-- from the Frobenius group (`toFrobeniusAction` + `IsFrobeniusAction.quotient` through `⁅N,N⁆`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.isPGroup_of_isFrobeniusGroup_of_card_le
-- (6.5)(b) in the (6.8)(c2) certain-type case: a coprime `W`-action on nilpotent `H` whose
-- nonidentity-element fixed points lie in `⁅H,H⁆` (`C_H(x) = W₂ ⊆ ⁅H,H⁆`) + the bound ⟹ `H` is a
-- `p`-group.  Underlying Frobenius brick: `IsFrobeniusAction.quotient_of_fixedPoints_le` (FPF on
-- `N ⧸ M` from the coprime fixed-point lifting Isaacs Cor 3.28, without FPF on `N`).
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch06.IsFrobeniusAction.quotient_of_fixedPoints_le
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.characterKernel_subset_of_inner_induce_ne_zero
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_eq_irreducible_not_subset_characterKernel
-- Peterfalvi S08 (6.2) `S₁`/`S₂` first-obstruction decomposition + its `S` no-real input.
-- `exists_coherentBreakPair`: for `Sa ⊆ Sb` (conj-closed irreducible, `Sb` finite real-free) with
-- `Sa` coherent and `Sb` not, the conjugate-pair cover `exists_conjugatePairCover` + the discrete
-- first-failure extraction `exists_index_predicate_break` produce the intermediate coherent `S₁`
-- and the breaking pair `{ψ, ψ̄}` cited at the start of the (6.2) proof.  `S_hasNoRealCharacters`
-- (Frobenius case) supplies the real-free input for any `S(A) ⊆ S`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_coherentBreakPair
-- (6.8.3)/case-(c2) generalizations: drop the irreducibility hypothesis so the breaking pair `ψ`
-- may be reducible (needed where `S` contains the `w₂−1` reducible induced characters).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_conjugatePairCover_general
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_coherentBreakPair_general
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.S_hasNoRealCharacters
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.SsubFiltration_hasNoRealCharacters
-- (6.2) member-family per-member facts over `S₁ ⊆ S` (Frobenius case): orthonormal conjugate pair
-- (`sMember_characterFacts`) and conjugate-difference support on `H^#` (`sMember_diffSupport`).
-- These are the per-member `hreal`/`hχχ`/…/`hdiffsupp` fields B1 consumes for each `S`-member.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sMember_characterFacts
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sMember_diffSupport
-- (6.2) member-family degree ratio: an `S`-member `χ = Ind θ` against a degree-`|W₁|` anchor `χ₁`
-- has integer ratio `χ(1) = θ(1)·χ₁(1)` (the `deg`/`ha1` data feeding the scaled-diff support and
-- `htau1_memaχ` fields).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sMember_charValue_one_eq_mul_anchor
-- (6.2) member-family core: flat enumeration of a finite conj-closed `S₁ ⊆ S` with the per-member
-- orthonormality/non-real/diff-support/membership fields B1 consumes (degree data layered on).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.exists_sMemberOrthonormalFamily
-- (6.2) member-family degree data: integer ratios `deg`/`ha1`/`hmemdegdiffsupp` against a
-- degree-`|W₁|` anchor, layering on the member-family core.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.exists_sMemberDegreeData
-- (6.2) anchor existence: `S(A)` has a degree-`|W₁|` member (degree-1 source of `H/A` inflated and
-- induced), discharging the `hanchordeg` of `exists_sMemberDegreeData`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.exists_mem_SsubFiltration_degree_W1
-- (6.2) adjoined-pair fields for the breaking pair `{ψ, ψ̄}`: non-realness, orthonormality,
-- conjugate-difference support, and orthogonality to all of `S₁` (the `ψ ∉ S₁` from the
-- strengthened `exists_coherentBreakPair`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sBreakPair_fields
-- (6.2) member-family → B1 degree-sum bound: the full assembly threading the member-family core,
-- degree data, adjoined-pair fields, scaled-diff support/Dade image, and the abstract generation
-- bridges into B1 (`coherentDegreeSumBound_of_not_coherent`), yielding `∑ⱼ (degⱼ)² ≤ 2a`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sMember_degreeSumBound_of_not_coherent
-- (6.2) range-sum reindex + the degree-square real bound `∑ⱼ χⱼ(1)² ≤ 2ψ(1)χ₁(1)` (B1 rescaled by
-- the anchor degree), the form ready to compare with B2 via `S(A) ⊆ S₁`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.sum_toFinset_range_eq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sMember_degreeSqReBound_of_not_coherent
-- (6.2) B2 in real/Frobenius form: `∑_{χ∈S(A)} (χ(1).re)² = |L:H|·(|H:A|−1)` (each S(A) member is
-- irreducible so `χ(1)²/‖χ‖² = (χ(1).re)²`), the real-degree-square identity to compare with the
-- member-family bound.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sum_re_sq_induce_kernelFilter_eq
-- (6.2) core inequality `|K:A|−1 ≤ 2ψ(1)`: the member-family degree-square bound `∑_{S₁} ≤ 2ψ(1)χ₁(1)`
-- combined (via `S(A) ⊆ S₁`) with the real B2 identity `∑_{S(A)} = |L:H|(|H:A|−1)`, cancelling |L:H|.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sMember_index_le_two_psi
-- (6.2) θ-bound for an induced member `ψ = Ind_H^L θ`: `ψ(1) = |L:H|·θ(1) ≤ |L:H|·|H:C|·√|C:D|`
-- (`induce_apply_one` + `theta_degree_le_index_mul_sqrt_index`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.psi_degree_le_of_source
-- (6.2) first-obstruction + core wiring: `S(A)` coherent ∧ `S(B)` not ⟹ ∃ ψ∈S(B), `|K:A|−1 ≤ 2ψ(1)`
-- (the breaking pair from `exists_coherentBreakPair` fed to the (6.2) core `sMember_index_le_two_psi`).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.six_two_index_bound
-- (6.2) restriction kernel inheritance: `θ` trivial on `M` ⟹ `Res_C θ` trivial on `M.subgroupOf C`
-- (discharges the θ-bound's kernel hypothesis from `ψ = Ind θ ∈ S(B)`, `θ` trivial on `B`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf
-- Peterfalvi (6.2) fully assembled (Frobenius case): under the section hypotheses (S(A) coherent,
-- S(B) not, B ⊆ D ⊆ C ⊆ H with D/B central in C/B), `|K:A|−1 ≤ 2|L:C|·√|C:D|`.  Threads the
-- first-obstruction + core (`six_two_index_bound`) with the θ-bound (`psi_degree_le_of_source`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.six_two
-- Peterfalvi (6.2) central case `C = H` (the form (6.3) consumes): θ-bound via the direct b-half
-- `degree_sq_le_index_of_central_quotient` (no Clifford restriction), giving `|K:A|−1 ≤ 2|L:H|√|H:D|`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.psi_degree_le_of_source_central
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.six_two_central
-- (6.3) per-step index bound: a section `B ⊆ A ⊆ H₁` (A/B central, S(A) coherent, S(B) not) gives
-- `|H:H₁| ≤ 4|L:K|²+1` (six_two_central + the arithmetic core six_three_HH1_le).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.six_three_index_bound
-- (6.3) `hAcomm` provider: `H` nilpotent ⟹ for normal `A ⊊ H`, `[H/A, H/A] ≠ ⊤` (nontrivial
-- nilpotent ⟹ not perfect).  Supplies the degree-`|W₁|` anchor hypothesis of six_two/six_three.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.commutator_subgroupOf_quotient_ne_top
-- (6.3) THEOREM (Frobenius K=H): `M ≤ H₁ ⊊ H`, `S(H₁)` coherent, `|H:H₁| > 4|L:H|²+1` ⟹ `S(M)`
-- coherent.  Minimal-A induction: maximal-B + maximality-central + per-step index bound contradiction.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.six_three
-- (6.5) bridge: `⁅H,H⁆.subgroupOf H = commutator ↥H` (so `|H:⁅H,H⁆| = |Abelianization ↥H|`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.commutator_subgroupOf_self
-- (6.5) bridge: `S(⊥) = S` (the bottom filtration is everything; kernel condition is vacuous).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.SsubFiltration_bot
-- (6.5) THEOREM (Frobenius): if `S` is not coherent then `H` is a `p`-group.  `six_three`
-- contrapositive (M=⊥, H₁=⁅H,H⁆) gives `|Abelianization H| ≤ 4|W₁|²+1`, then the Frobenius/odd
-- p-group reduction `isPGroup_of_isFrobeniusGroup_of_card_le`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.isPGroup_of_not_coherent
-- (6.6) ingredient: for a finite p-group, every irreducible character degree is a power of p
-- (degree ∣ |K| = pⁿ).  Feeds the `θ = p^m` source-degree fields of the X-chain step data.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_primePow_natDegree_of_isPGroup
-- (6.6) ingredient: a nontrivial odd-order p-group has p ≥ 3 (its order pⁿ is odd).  The `3 ≤ p`
-- field of the X-chain step data.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.three_le_prime_of_isPGroup_of_odd
-- (6.6) X degree-sum identity (Frobenius): ∑_{χ∈X=S−S(Z)} (χ 1).re² = |L:H|·(|H| − |H:Z|),
-- the difference of the S(A) degree-sum identity at A=⊥ and A=Z.  The `total` of the X-chain step.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sum_re_sq_Xset_eq
-- (6.6) ingredient: a quotient of a finite p-group has p-power order (so |H:Z| = p^k), the key to
-- θχ(1)² ∣ |H:Z| (both p-powers) in the (6.6) divisibility.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_primePow_card_quotient_of_isPGroup
-- (6.6) per-member degree shape: every S-member χ = Ind θ has χ(1) = |L:H|·θ(1) = |L:H|·p^k
-- (H a p-group).  The common-index p-power degree of each X-chain member.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.exists_index_primePow_degree_of_mem_S
-- (6.6) vectorized per-member degree data (χmem j (1) = |L:H|·p^(mmem j)) for an X-member family.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.exists_memberDegreeData
-- (6.6) htotal factorization: |L:H|·(|H|−|H:Z|) = |H:Z|·(|L:H|·(|Z|−1)) (Lagrange); total=qtot·c.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.index_mul_card_sub_factor
-- (6.3) nilpotency central step: in a finite nilpotent group, a nontrivial normal subgroup meets
-- the centre (`N ⊓ Z(G) ≠ ⊥`), via the upper central series least-index argument.  Discharges the
-- `A/B ⊆ Z(H/B)` central condition of the (6.3) minimal-A induction (with maximality of B).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.isNilpotent_normal_inf_center_ne_bot
-- (6.3) maximal-B step: in a finite group, `M < A` (M normal) has a maximal normal `B` with
-- `M ≤ B < A` (any normal `C` with `B ≤ C < A` is `B`).  The maximal-B of the (6.3) induction.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_maximal_normal_between
-- (6.3) maximality forces centrality: with `H ◁ Γ` nilpotent, `B < A ≤ H` and `B` maximal normal
-- below `A`, the nilpotency central step + maximality give `A/B ⊆ Z(H/B)`.  Discharges the
-- `hcentral` hypothesis of `six_three_index_bound` in the (6.3) minimal-A / maximal-B induction.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.normal_central_of_maximal_normal_below
--- Peterfalvi S08 T8 base-block bridges: the Frobenius-specific X-base coherence helpers
--- are factored through the honest abstract hypothesis `X ⊆ Irr L`, and the case-A specialization
--- consumes `isIrreducibleCharacter_of_mem_Xset_caseA`.  These are assembly bridges only; they do
--- not add new hard hypotheses or depend on `sibleySetup_is_coherent`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xMember_characterFacts_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xMember_diffSupport_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.sMember_scaledDiffSupport_of_charValue_eq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.scaledDiff_dadeImage_mem_ZIrr
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xMember_scaledDiffSupport_of_degreeData
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xMember_scaledDiffSupports_of_degreeData
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_closedUnderConjugate_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_hasNoRealCharacters_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xSet_finite_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.natDegree_le_of_xBaseBlock_anchor
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.natDegree_lt_of_xBaseBlock_anchor_of_not_mem
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xBaseBlock_closedUnderConjugate_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.two_le_xBaseBlock_ncard_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xBaseBlock_isCoherent_of_irreducible_X
-- Frobenius-specialized wrappers used by downstream c1/S09 assembly callers.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xMember_characterFacts
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xMember_diffSupport
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_closedUnderConjugate
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_hasNoRealCharacters
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xSet_finite
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xBaseBlock_closedUnderConjugate
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.two_le_xBaseBlock_ncard
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xBaseBlock_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xBaseBlock_isCoherent_caseA
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_isCoherent_from_adjoinSteps_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.pairCover_orthogonal_to_prefix
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xPair_stepCoreFacts_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.exists_pairUnion_memberFamily_of_irreducible_X
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xAdjoinStepInput_of_memberFamily_degreeRatios
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.exists_natDegreeData_for_xAdjoinMemberFamily
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.natDegree_pos_of_irreducibleCharacter_apply_one_eq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.commonIndex_pos_of_natDegree_factor
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.coprime_commonIndex_primePower
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.natDegreeSquareSum_pos_of_memberFamily
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.sq_dvd_natDegreeSquareSum_of_commonIndex
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xAdjoinStepInput_of_memberFamily_natDegreeGap
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.natDegreeDvd_of_commonIndex_primePowerData
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.degreeDivisibilityInputs_of_commonIndex_primePowerData
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xAdjoinStepInput_of_memberFamily_degreeDivisibility_primePowerSums
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.mem_xSetFinset_iff_mem_Xset
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_centralCommutator_isCoherent_of_irreducible_X
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_centralCommutator_isCoherent_of_c2_caseA
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.two_mul_lt_sq_of_commonIndex_primePower_gap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.normalizedDegreeGap_of_natDegreeSumCommonIndexPrimePowerGap
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xAdjoinStepInput_of_memberFamily_degreeDivisibility_commonIndexNatGap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.normalizedDegreeGap_of_realDegreeBound
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.realDegreeBound_of_natDegreeSumPrimePowerGap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.normalizedDegreeGap_of_natDegreeSumPrimePowerGap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.xAdjoinStep
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.coherentDegreeSumBound_of_not_coherent
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.six_three_HH1_le
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.six_five_index_contradiction
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.six_five_chief_factor_contradiction
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.six_five_c_contradiction
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.XAdjoinStepInput.adjoin
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.IndChainDecomposition.image_eq_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_eq_ite
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_weightedOutput
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.weightedOutput_inner_self_eq_sum_sq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.weightedOutput_inner_self_re_eq_sum_sq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.one_le_weightedOutput_inner_self_re
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.IndChainDecomposition.ofIsCoherent
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.IndChainDecomposition.image_eq_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_eq_ite
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.IndChainDecomposition.image_weightedDifferenceInput
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_zero_image_weightedDifferenceInput
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_zero_image_weightedDifferenceInput_re_nonpos
-- [Is] Thm 6.34 (Mackey restriction, normal-subgroup case): `|H| • Res_H (Ind_H^G θ) = ∑_{x∈G} θ^{x⁻¹}`.
-- The unnormalized Frobenius/Mackey restriction formula; the heaviest analytic brick of [Is] 6.34,
-- feeding Peterfalvi (6.8)'s `Y = S(H')` (induced irreducibles of common degree `|W₁|`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_smul_restrict_induce
-- [Is] Thm 6.34 (norm part): `|H| · ‖Ind_H^G θ‖² = |I_G(θ)|` for irreducible `θ` (= `[I_G(θ):H]`),
-- via Frobenius reciprocity + the Mackey sum + orthonormality of irreducibles.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_mul_inner_self_induce
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
-- Cross Mackey inner product + orthogonality of induced characters from non-conjugate irreducibles
-- (`⟨Ind θ, Ind ψ⟩ = 0`), used to prove the (6.8) `Y = S(H')` family `j ↦ Ind_H^L θ_j` injective.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.card_mul_inner_induce
#assert_only_allowed_axioms OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj
-- Linear (degree-one) irreducible character from a hom `H →* ℂˣ`: the source characters of the
-- (6.8) `Y = S(H')` family are the nontrivial linear characters of `H` (`= Irr(H/H') ∖ {1}`).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.linearIrreducibleCharacter
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.ClassFunction.compHom_linearIrreducibleCharacter
-- Degree-one irreducible characters are multiplicative / kill commutators — lets a linear `θ` of `H`
-- inflate from the abelian quotient `H/⁅H,H⁆` (the (6.8)(c2) inertia bridge).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.map_mul_of_apply_one_eq_one
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_ne_zero_of_apply_one_eq_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_commutatorElement_eq_one_of_apply_one_eq_one
-- (6.8)(c2) inertia bridge infra: inflation–conjugation equivariance + inertia transfer
-- (`g ∈ I_L(inflate θ̄) ↔ ḡ ∈ I_Ḡ(θ̄)`), and the abelian Brauer count (`C_{H̄}(ḡ)=1 ⟹ ḡ` fixes only
-- the trivial class). With Isaacs 3.28 these discharge `inertia(θ)=H` for linear `θ` in case c2.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.conjBy_compHom_eq_compHom_conjBy
#assert_only_allowed_axioms OddOrder.RepresentationTheory.mem_inertia_compHom_iff
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot
#assert_only_allowed_axioms OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel
-- Norm-1 virtual character with positive degree is irreducible (reusable Fourier criterion).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos
-- Brauer conjugation bridge: if ambient centralizers of nonidentity elements of `H` lie in `H`,
-- every `g ∉ H` fixes only the identity conjugacy class, hence nontrivial irreducibles have
-- inertia group exactly `H`. This is the free-action input for [Is] Thm 6.34 in Peterfalvi (6.8).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.card_fixedPoints_conjClassPerm_eq_one_of_not_mem_of_centralizer_le
#assert_only_allowed_axioms OddOrder.RepresentationTheory.inertia_eq_of_freeAction
-- Frobenius-group specialization: centralizer-kernel property from Isaacs Ch.6 discharges inertia.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.inertia_eq_of_frobeniusGroup
-- [Is] Thm 6.34 capstone: H ⊴ G, θ ∈ Irr H, I_G(θ) = H  ⟹  Ind_H^G θ ∈ Irr G.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq
-- Frobenius-group consumer form of [Is] Thm 6.34, used by Peterfalvi (6.8) case c1.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_frobeniusGroup
-- Degree side of Clifford's theorem: `χ(1) = ∑_θ ⟨Res χ,θ⟩·θ(1)` (Fourier expansion of `Res χ`).
-- The degree component of the (9.9.a) Clifford-degree assembly (issue 2031).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.apply_one_eq_sum_restrictionMultiplicity_mul
-- Clifford single-orbit (module level): two simple `k[H]`-submodules of a `G`-irreducible
-- restriction have conjugate characters `χ_{N'}(h) = χ_N(g⁻¹ h g)` — the core of
-- `RestrictionConstituentsSingleOrbit` (issue 2031), from `iSup_map_conjSemilinearEnd_eq_top`.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.character_conj_of_simpleSubmodule
-- Constituent ⟺ submodule bridge (module side): a nonzero `H`-intertwiner `σ → Res^G_H ρ`
-- (`σ` irreducible) yields a simple `k[H]`-submodule of `Res^G_H ρ` with character `χ_σ` (Schur +
-- `equivLinearMapAsModule` + `LinearEquiv.ofInjective` + `char_iso`); issue 2031 補題4 core.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_simpleSubmodule_character_eq_of_ne_zero_intertwiner
-- **Clifford's theorem, single-orbit (character level)** ([Is] Thm 6.5, first clause): for a
-- `G`-irreducible χ and `H ⊴ G`, the constituents of `Res^G_H χ` form a single `G`-conjugation
-- orbit.  Discharges the `RestrictionConstituentsSingleOrbit` scaffold hypothesis (issue 2031).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.restrictionConstituentsSingleOrbit_of_isIrreducible
-- **Clifford's theorem, degree formula** ([Is] Thm 6.5): `χ(1) = ⟨Res χ,θ₀⟩·[G:I_G(θ₀)]·θ₀(1)` for a
-- constituent `θ₀` (degree expansion + single-orbit + common multiplicity + orbit size). issue 2031.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.apply_one_eq_restrictionMultiplicity_mul_index_inertia
-- **Clifford correspondence** ([Is] Thm 6.11): an irreducible `χ` lying over `ψ ∈ Irr I` whose
-- induction `Ind_I^G ψ` is irreducible equals that induction, so `χ(1) = [G:I]·ψ(1)`.  This is the
-- (9.9.a) "induced from a linear character of `HC`, degree `u`" route (issue 2031/2030).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.apply_one_eq_index_mul_of_liesOver_of_isIrreducibleCharacter_induce
-- **Constituent degree bound**: an irreducible `χ` lying over `ψ ∈ Irr I` has degree `χ(1) ≤
-- (Ind_I^G ψ)(1)` (genuine-character Fourier expansion + nonneg multiplicities).  Unlike the Clifford
-- correspondence it needs no irreducibility of `Ind ψ`; it forces `e = 1` in (9.9.a) (issue 2031).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.apply_one_le_induce_apply_one_of_liesOver
-- **Clifford correspondence degree (e=1 sandwich)**: `χ` over a linear `θ₀ ∈ Irr H` with inertia `I`
-- and over a linear `ψ ∈ Irr I` ⟹ `χ(1) = [G:I]`.  Sandwiches the Clifford lower bound `e·[G:I]`
-- against the constituent upper bound `[G:I]`, forcing `e = 1`.  Abstract core of (9.9.a) (issue 2031).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.apply_one_eq_index_of_liesOver_linear_inertia

-- Peterfalvi (6.8) T6/Y-family consumer side: degree-one induced families have common degree,
-- supported differences on `H#`, irreducibility from c1/c2 inertia, and equal-degree coherence.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.induce_apply_one_eq_card_W1_of_degree_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.support_sub_induce_subset_sharpImage_of_apply_one_eq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.support_sub_induce_subset_sharpImage_of_degree_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentInducedDegreeOneFamily
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.inertia_eq_H_of_c2
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.inertia_eq_H_of_c2_caseA
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.isIrreducibleCharacter_induce_of_degree_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentYFamily
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentYFamily_of_pairwiseNonconj
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.induce_linearIrreducibleCharacter_mem_Yset
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.exists_linearIrreducibleCharacter_eq_of_YsetSource
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.exists_linear_source_of_mem_Yset
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.mem_Yset_iff_exists_linear_source
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.SsubFiltration_subset_S
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_subset_S
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Yset_subset_S
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.disjoint_Xset_SsubFiltration
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_union_SsubFiltration_eq_S
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.SsubFiltration_antitone
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_mono
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_commutator_eq_Xset_union_filtrationDiff
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.disjoint_Xset_Yset
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_union_Yset_eq_S
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.irreducibleCharacter_conj_ne_trivial
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.S_finite
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.SsubFiltration_finite
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_finite
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.S_closedUnderConjugate
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.SsubFiltration_closedUnderConjugate
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Xset_closedUnderConjugate_unconditional
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.xBaseBlock_closedUnderConjugate_unconditional
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.SsubFiltration_nonempty_of_commutator_quotient_ne_top
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.SsubFiltration_nonempty_of_nontrivial_solvable_quotient
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.SsubFiltration_nonempty_of_subgroupOf_ne_top
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.range_induce_linearIrreducibleCharacter_subset_Yset
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.finite_linearCharacters_of_finite
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Yset_finite
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.isIrreducibleCharacter_of_mem_Yset
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.inner_eq_zero_of_mem_span_of_disjoint_irreducible
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.inner_span_Xset_Yset_eq_zero_of_irreducible_X
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.exists_Yset_linearRepresentativeFamily
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentYset_of_pairwiseNonconj
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentYset_of_two_le_ncard
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Yset_nonempty
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Yset_hasNoRealCharacters
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.Yset_closedUnderConjugate
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.two_le_Yset_ncard
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentYset
-- (6.8) capstone X-empty (abelian) branch: `S = Y` ⟹ CoherenceTarget = coherentYset.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherenceTarget_of_Xset_empty
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.isIrreducibleCharacter_of_mem_S_of_frobenius
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.isIrreducibleCharacter_of_mem_Xset_of_frobenius
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.inner_span_Xset_Yset_eq_zero_of_frobenius
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_frobenius
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_frobenius_mixed_inner
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_frobenius_generator_mixed_inner
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentS_of_frobenius_pairUnionCommonIndexPrimePowerData_generator_mixed_inner
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.isIrreducibleCharacter_of_mem_Xset_caseA
-- Peterfalvi (4.1) (mmd 04.6 L5): signed irreducibles with orthogonal, degree-`0` signed
-- differences are pairwise orthogonal — the lemma promoting difference-orthogonality to full
-- image-orthogonality (`X^{τ₂} ⊥ Y^{τ₁}`), the (6.8.1) `himg_ortho` ingredient.  Sub-lemmas:
-- `eq_inner_smul_of_inner_ne_zero` (`±Irr` equal up to sign) and
-- `apply_one_ne_zero_of_mem_ZIrr_of_inner_self_one` (`±Irr` has nonzero degree).
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.pairwise_inner_eq_zero_of_orthogonal_signedDifference
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.inner_eq_zero_of_orthogonal_signedDifference
#assert_only_allowed_axioms OddOrder.RepresentationTheory.eq_inner_smul_of_inner_ne_zero
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.apply_one_ne_zero_of_mem_ZIrr_of_inner_self_one
-- (4.1) inputs for `himg_ortho`: two coherences off the same Dade base map have cross
-- inner products (`inner_extension_eq_inner_of_supported`, the difference-orthogonality) and
-- degree-`0` values (`extension_apply_one_eq_zero_of_supported`) governed by the Dade isometry on
-- supported lattice elements (`extends_on_supported` + the §4 Dade isometry / vanish-at-`1`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inner_extension_eq_inner_of_supported
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.extension_apply_one_eq_zero_of_supported
-- (6.8.1) norm-bound forcing (mmd L176): `a ∣ b` (from (6.7)) + the `Y`-part norm bound
-- `(b−a)² + (m−1)b² ≤ 1 + a²` (`a,m ≥ 2`) ⟹ `b = 0` (or the relabel-reducible edge `b=a, m=2`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.eq_zero_or_edge_of_dvd_of_normBound
-- (6.8.1) Dade reciprocity gateway (TI case `H a = ⊥`): the (2.7) `adjoint_formula` collapses
-- (`adjointAverageFun_eq_of_H_eq_bot`) to `⟨α^τ, ψ⟩_G = ⟨α, Res_L ψ⟩_L` for supported `α`, the
-- structural input for the `Res_L(η₁^{τ₁})` decomposition.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.adjointAverageFun_eq_of_H_eq_bot
#assert_only_allowed_axioms OddOrder.Peterfalvi.S08.inner_dadeIntegralCharacterMap_eq_inner_restrict
-- Sibley-carrier reciprocity wrapper (uses the new `dade_H_eq_bot` TI field).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.inner_tau_eq_inner_restrict
-- Peterfalvi (7.10) consumer algebra: sum and normalize the weighted Ind equations.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.image_weightedDifferenceInput
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.image_weightedDifferenceInput_eq_weightedOutput_sub_norm_smul_chi_zero
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_zero_image_weightedDifferenceInput
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.IndChainDecomposition.inner_chi_zero_image_weightedDifferenceInput_re_nonpos
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S08.SibleyDadeHypothesis.indChainDecomposition_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
-- Peterfalvi (7.8) bridge from the S09 `ν` interface to a concrete S07 coherence witness.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.nu_mem_ZIrr_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.nu_mem_ZIrr_of_isCoherent_of_mem
-- Peterfalvi (7.8) indexed source set and `ζᵢ` image consumers for the same S07 witness.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.zeta_mem_sourceSet
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.zetaDistinct_mem_sourceSet
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChainDecomposition_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChainDecomposition_of_coherenceOn
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChainDecomposition_of_sibley_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_image_eq_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_image_eq_zero_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_inner_chi_eq_ite_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_inner_chi_weightedOutput_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_image_weightedDifferenceInput_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_image_weightedDifferenceInput_eq_weightedOutput_sub_sum_sq_smul_chi_zero_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_image_weightedDifferenceInput_eq_weightedOutput_sub_norm_smul_chi_zero_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_inner_chi_zero_image_weightedDifferenceInput_eq_one_sub_norm_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_inner_chi_zero_image_weightedDifferenceInput_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_weightedOutput_inner_self_eq_sum_sq_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_weightedOutput_inner_self_re_eq_sum_sq_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_one_le_weightedOutput_inner_self_re_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.indChain_inner_chi_zero_image_weightedDifferenceInput_re_nonpos_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.nu_zeta_mem_ZIrr_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.nu_zetaDistinct_mem_ZIrr_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.sourceDiff_mem_ZIrr_of_irreducible
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.beta_mem_ZIrr_of_irreducible_sourceDiff
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.delta_mem_ZIrr_of_irreducible_sourceDiff_and_isCoherent
-- Peterfalvi (7.8) norm-one and signed-irreducible image bridges for coherent `ζᵢ`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.zeta_inner_self_eq_one_of_irreducible
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.nu_zeta_inner_self_eq_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.nu_zeta_inner_self_eq_one_of_irreducible
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.zetaImage_inner_self_eq_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.zetaImage_inner_self_eq_one_of_irreducible
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.exists_zsmul_irreducibleCharacter_nu_zeta_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.exists_zsmul_irreducibleCharacter_zetaImage_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.nu_zeta_isIrreducibleCharacter_of_isCoherent_of_apply_one_pos
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.zetaImage_isIrreducibleCharacter_of_isCoherent_of_apply_one_pos
-- Peterfalvi (7.8.b) raw norm-bound consumers from `NormEstimates`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRho_inner_self_re_ge_of_normEstimates
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.gamma_inner_self_re_le_of_normEstimates
-- Peterfalvi (7.8.a)/(7.8.b) `BetaDecomp` algebra and norm consumers.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.weightedNuSum_orth_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.constOne_orth_weightedNuSum
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.weightedNuSum_orth_gamma
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.gamma_orth_weightedNuSum
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.delta_eq_weightedNuSum_add_gamma
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.delta_orth_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.constOne_orth_delta
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.betaNormSq_eq_of_weightedNuSum_norm
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.weightedNuSum_inner_zetaImage_eq_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.sourceZeta_inner_zetaDistinct_eq_ite_of_irreducible_distinct
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.weightedNuSum_inner_zetaImage_eq_one_of_irreducible_source_data
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.weightedNuSum_inner_self_eq_of_source_orthogonal
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.betaNormSq_eq_of_source_orthogonal
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.gammaNormSq_eq_of_source_orthogonal
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.normEstimates_of_source_orthogonal
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.normEstimates_of_inner_values_irreducible_source_data_and_uv_formula
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRho_inner_self_re_ge_of_inner_values_irreducible_source_data_and_uv_formula
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.gamma_inner_self_re_le_of_inner_values_irreducible_source_data_and_uv_formula
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.beta_inner_zetaImage_eq_int_sub_one_of_weighted
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.beta_inner_zetaImage_eq_int_sub_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.beta_inner_zetaImage_eq_int_sub_one_of_irreducible_source_data
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis78.zetaNuRhoNormSq_eq_kernelRatio_mul_int_sub_one_of_irreducible_source_data
-- Peterfalvi (7.9) residual cross-term reduction.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.beta_inner_beta_eq_zero
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.zetaImage_cross_eq_zero_of_support_subset
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.zetaImages_mem_ZIrr_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.delta_and_zetaImages_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.beta_inner_beta_expand_delta
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.delta_cross_equation
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.delta_cross_integral_of_ZIrr
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.delta_cross_integral_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.delta_cross_integral_of_irreducible_sourceDiff_and_isCoherent
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity_of_zeta_support
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.conclusion_of_irreducible_sourceDiff_and_isCoherent_parity
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.conclusion_of_delta_cross_nonzero
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.conclusion_of_delta_cross_integral_parity
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Hypothesis79.conclusion_of_delta_cross_even_of_ZIrr
-- Peterfalvi (7.5) reduced family inequality input for the (7.10) assembly.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.reduced_inequality_of_estimates
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.one_le_G0_norm_sum_of_one_le_norm_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.one_le_norm_sq_apply_one_of_signed_irreducible
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.one_le_G0_norm_sum_of_signed_irreducible
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h_real
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.base_estimate_of_family71_reduced_estimates
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_family71_reduced_estimates
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.base_estimate_of_family71_reduced_estimates_of_signed_irreducible
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible
-- Peterfalvi (7.10) final assembly sockets for `CharacterEstimateData`.
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_family71_signed_decomposition
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_family71_coherent_zeta_decomposition
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_family71_coherent_zeta_source_data
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.lowerBoundTerm_of_family71_coherent_zeta_source_data
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.localKernelOrder_eq_h
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.localComplementIndex_eq_e
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.localSmallIndex_of_family_cardinalities
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.zetaNuRho_inner_self_re_ge_of_family_source_data
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.gamma_inner_self_re_le_of_family_source_data
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.zetaNuRhoNormSq_eq_familyRatio_mul_int_sub_one_of_source_data
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.Bsum_le_of_orthogonal_integer_decomposition
-- Peterfalvi (7.10) lower-bound bridge constructors from the penultimate,
-- rational B-sum, and real reduced-inequality inputs.
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.exists_lowerBoundTerm_of_exists_penultimate
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.lowerBoundTerm_of_Bsum_bound
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.exists_lowerBoundTerm_of_exists_Bsum_bound
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.base_estimate_of_real_reduced_family_inequality
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_real_reduced_family_inequality
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.lowerBoundTerm_of_real_Bsum_bound
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.exists_lowerBoundTerm_of_exists_real_Bsum_bound
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_real_reduced_family_inequality_and_decomposition
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_real_reduced_family_inequality_and_source_decomposition
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_source_decomposition_of_family_cardinalities
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_family_source_decomposition
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.lowerBoundTerm_of_characterEstimateData
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.lowerBoundTerm_of_real_reduced_family_inequality_and_decomposition
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.lowerBoundTerm_of_family_source_decomposition
-- Peterfalvi (7.11) terminal contradiction from the displayed (7.10) lower bound.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.not_trivial_G0_of_lowerBoundTerm
-- Peterfalvi (7.11) terminal contradictions from existential final-assembly inputs.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.not_trivial_G0_of_exists_penultimate
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.not_trivial_G0_of_exists_Bsum_bound
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.not_trivial_G0_of_exists_real_Bsum_bound
-- Peterfalvi (7.11) conditional terminal contradiction from the named (7.10) estimate data.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.not_trivial_G0_of_characterEstimateData
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.not_trivial_G0_of_family71_coherent_zeta_source_data
-- Peterfalvi (7.11) consumer from the `𝓑`-sum bound and real reduced family inequality.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.not_trivial_G0_of_real_Bsum_bound
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.not_trivial_G0_of_real_reduced_family_inequality_and_decomposition
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.not_trivial_G0_of_family_source_decomposition

/-! ### Top-level Feit–Thompson reduction (downstream). -/

-- Minimal-counterexample reduction: *if* no minimal simple group of odd order exists,
-- *then* every finite group of odd order is solvable. Pure group theory (strong induction
-- on `|G|` + `solvable_of_ker_le_range`).  The complete downstream chain is guarded again
-- at the end of this file after the Section 16 producers.
#assert_only_allowed_axioms OddOrder.feitThompson_of_noMinimalSimpleOdd

-- Section 16 assembly boundary:
-- `sectionSixteenHypothesis_of_inputs` builds `Peterfalvi.S16.Hypothesis` from an explicit
-- `Section16Inputs` menu *without* `sorry` (it derives `η = τ₃∘ω`, `m`, oddness, `finiteG`).
-- This assertion locks in that the assembly itself remains axiom-clean.
#assert_only_allowed_axioms OddOrder.sectionSixteenHypothesis_of_inputs

-- Pure T-side ν-grid facts threaded through the named-input carrier and assembled at the same
-- axiom-clean boundary; this deliberately excludes the post-(14.9) commutativity of V.
#assert_only_allowed_axioms OddOrder.sectionSixteenNuGridSupplyData_of_inputs

-- cd producer (POLE-1 charData) building block: the §6 certain-type Hypothesis (4.2) with `W₁ = K`
-- the chosen κ-Hall pairing factor, built from the BG §14/§16 type-`P` theory (complement +
-- centralizer law).  Lets the cd producer index the `ω`/`μ`-grids by `tp.W₁ = mp.K` directly.
#assert_only_allowed_axioms OddOrder.certainTypeHypothesis_of_typeP_kappaHall
-- The two members' certain-type machinery wired to `mp` (S-side `W₁ = mp.K`, T-side `W₁ = mp.Kstar`).
#assert_only_allowed_axioms OddOrder.Section16MaximalPair.certainTypeS
#assert_only_allowed_axioms OddOrder.Section16MaximalPair.certainTypeT

/-! ### BG Appendix C (finite-field norm-set argument). -/

-- Peterfalvi §15/§16 standalone cyclotomic and growth arithmetic feeding the
-- final Section 16 comparison.  These are independent of the theorem-level
-- Section 15/16 scaffolds that still carry `sorry`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.q_ne_two
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.p_ne_two
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.three_le_q
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.three_le_p
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.cyclotomic_quotient_odd
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.cyclotomic_quotient_coprime_of_not_modEq_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.cyclotomic_quotient_not_dvd_self_of_not_modEq_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.cyclotomic_divisor_facts
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.m_value_ge_aux
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.m_value_gt_seven_tenths
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.m_value_gt_four_fifths
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.Hypothesis.q_not_modEq_one_mod_p
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.Hypothesis.tSide_cyclotomic_quotient_odd
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.Hypothesis.tSide_cyclotomic_quotient_coprime
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.Hypothesis.tSide_cyclotomic_quotient_divisor_modEq_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.CaseBForTData.v_odd
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.CaseBForTData.v_pos
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.CaseBForTData.v_ne_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.CaseBForTData.v_coprime_q_sub_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.CaseBForTData.divisor_modEq_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.CaseBForTData.pq_lt_v
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.CaseBForTData.two_p_lt_v
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.q_pow_gt_p_pow
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.Hypothesis.q_pow_gt_p_pow
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.cyclotomic_quotient_sub_one_ge_pow_pred
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.gap_coefficients_nonzero_of_delta_parity
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_typeIII_primeTIredZero
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tSideDadeMap_inner_trivial
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_typeIII_primeTIDifference
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_typeIII_primeTIredZero_with_inner
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_typeIII_primeTIredZero_with_projectionData
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.exists_typeIII_primeTIredZero_with_projectionData_galois_and_eq_induce
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.exists_typeIII_primeTIredZero_with_projectionData_and_galois
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.exists_typeIII_primeTIredZero_with_conjugateProjectionData
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_typeIII_primeTIDifference_induced_inner_self
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_typeIII_induced_primeTIDifference_with_norm
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.exists_typeIII_induced_primeTIDifference_with_norm_and_anchor_orthogonality
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_typeIII_primeTIDifference_with_anchor_inner
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tSideCoherentExtension_inner_trivial
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.T_typeIII_calT1_family_galois
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.inducedFamily_mapRingEquiv_mem
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.primeTIred_zero_mapRingEquiv
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tSideDadeMap_mapRingEquiv_bridge
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tSideDadeMap_inner_eq_zero_of_coherent_difference
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tSideDadeMap_inner_galois_eq_intCast
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tSideDadeMap_eta_axis_coefficients_constant
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.eta_axis_galois_orbits_of_hypothesis
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tSideDadeMap_conj_of_support
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tSideCoherentExtension_conj
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tSideDelta_isReal
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.dadeHypothesis_eq_of_H_eq
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.tSideDadeMap_eq_full_typeP1DadeMap_of_support
-- ⏳ pending (issue 3004): `escaping_typePA0_eq_empty_of_isTypeP1` /
-- `typePA0_isTISubset_of_isTypeP1` は sorried deep inputs に推移依存 (sorryAx) のため
-- assert しない — deep inputs が閉じたら再登録 (2026-07-11 hub fix-forward、618a0285 の過剰主張除去)。
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.fullTypeP1Dade_H_eq_bot_of_typePA_centralizer_le
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.fullTypeP1Dade_H_eq_bot_of_isTISubset
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.tSideDadeMap_eq_induce_of_full_typeP1_H_eq_bot
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.tSideDadeMap_eq_induce_of_typePA_centralizer_le
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.tSideDadeMap_eq_induce_of_isTISubset
-- ⏳ pending (issue 3004): `tSideDadeMap_eq_induce_of_isTypeP1` は上記 typePA0-TI 系の
-- sorried 依存を継承するため assert しない (同上)。
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.disjoint_conjugatesIntoSet_of_prime_order_separator
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.disjoint_conjugatesIntoSet_S_Tderived_of_p_dvd
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.p_dvd_orderOf_of_mem_sharpP_union_typePV
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.disjoint_conjugatesIntoSet_sharpP_union_typePV_Tderived
-- ⏳ pending (issues 3004/9084): `S15.betaGrid_support` は仮説なしの局所証明だが、
-- 独立 AxiomsCheck では既存 upstream の `sorryAx` を継承する。これを cite する無条件 endpoint
-- `tSideDadeMap_inner_tauSbetaGrid_eq_zero` も同じく `sorryAx` を継承するため assert しない。
-- exact dependency を上流が閉じた時点で両方を再登録する (2026-07-12 lane c 検証)。
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.inner_eq_swap_of_mem_ZIrr
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.gap_cross_inner_identity
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.tSide_beta_inner_eta_of_zeroColumn_projection
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.exists_etaGrid_intProjection_of_inner_self_eq
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGridProjection_mem_ZIrr
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGrid_projection_residual_ne_zero_of_inner
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.tSide_etaGridProjection_residual_ne_zero_of_coherent_pair
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.tSide_etaGridProjection_residual_ne_zero_of_anchor_orthogonal
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGrid_projection_sum_sq_le_of_residual_ne_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.tSideDadeMap_inner_eta_principal
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.axis_coefficients_eq_column_or_row
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGrid_axis_sum_eq_sum_sq
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGrid_axis_bound_of_sum_sq_le
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGrid_coefficients_eq_column_or_row
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGrid_coefficients_eq_column_or_row_of_sum_sq_le
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGrid_zeroColumn_projection_of_coefficients_eq_column
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.etaGridProjection_inner_eta
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGrid_projection_residual_inner_eta_eq_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.etaGridProjection_eq_zeroRow_of_coefficients_eq_row
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.s12HypothesisOfTypePData
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.s12_muGrid_zeroColumn_sum_eq_induce_trivial
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.s12Tau_zeroColumn_sub_eq_tSideDadeMap
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.tau_muColumnSum_sub_zeta_eq_of_grid_alphaImage
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.tau_muColumnZero_sub_zeta_dichotomy_of_grid_orthogonal
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.SHC_swap_grid_h114
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.exists_coherent_extension_h114_of_grid_orthogonal
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.SHC_residual_eq_grid_diff
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.grid_diff_inner_zeroColumnSum
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.R_sum_inner_grid_zeroColumnSum
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.charParam_a_eq_zero_of_grid_residualEq
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.tau_muGridAlpha_apply_eq_of_grid_value_alignment
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSourceCharacter
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSigmaGrid_apply_eq_sourceCharacter
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.eta_diff_classifier_of_typePV_value
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.eta_column_diff_rigidity
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.eta_column_diff_classifier_of_typePV_value
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaMonoidHom
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaMonoidHom_coe
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.monoidHom_eq_of_eq_on_W1_W2
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW1Restriction
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW2Restriction
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaMonoidHom_bijective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW1Restriction_injective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW2Restriction_injective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW1Restriction_bijective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW2Restriction_bijective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW1RestrictionEquiv
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW2RestrictionEquiv
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW1Restriction_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW2Restriction_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW1RestrictionEquiv_symm_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaW2RestrictionEquiv_symm_one
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.monoidHomTransportSubgroupEq
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.monoidHomTransportSubgroupEq_apply
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaMonoidHomEquiv
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaMonoidHomEquiv_apply
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaSourceCharacterOnBase
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaEtaIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.omegaMonoidHom_alignedOmegaEtaIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaSourceCharacter_injective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaSourceCharacter_eq_mul_axes
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaEtaIndex_injective
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.alignedOmegaSigmaGrid_apply_eq_eta_alignedIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.alignedOmegaSourceCharacter_zero_row_apply_of_mem_W1
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.alignedOmegaSourceCharacter_zero_column_apply_of_mem_W2
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaSourceW1Restriction
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaSourceW2Restriction
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaColumnIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaRowIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.omegaMonoidHom_alignedOmegaColumnIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.omegaMonoidHom_alignedOmegaRowIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.alignedOmegaSourceCharacterOnBase_zero_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaColumnIndex_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaRowIndex_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaColumnIndex_injective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaRowIndex_injective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaColumnIndex_bijective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaRowIndex_bijective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaColumnEquiv
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaRowEquiv
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaColumnEquiv_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaRowEquiv_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.alignedOmegaSourceCharacterOnBase_eq_mul_axes
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaProductIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.omegaMonoidHom_alignedOmegaProductIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.alignedOmegaProductIndex_eq_alignedOmegaEtaIndex
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaProductIndex_zero_column
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaProductIndex_zero_row
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaEtaGrid
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaEtaGrid_zero_column
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaEtaGrid_zero_row
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaProductIndex_injective
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaEtaGrid_orthonormal
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.alignedOmegaSigmaGrid_apply_eq_alignedOmegaEtaGrid
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.eta_pair_diff_rigidity
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.eta_pair_diff_classifier_of_typePV_value
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.alignedOmegaEtaGrid_classifier
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.eta_eq_of_norm_one_regular_value_eq
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.alignedOmegaSigmaGrid_eq_alignedOmegaEtaGrid
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_omegaMonoidHom_eq
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.residual_not_orthogonal_of_transposed_reindexing
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_charParameters_full_for_member
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_s13Hypothesis_for_member
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.typeIII_induced_source_support
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.typeIII_induced_source_degree
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.u_le_cyclotomicQuotient
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.CaseBForSData.u_le_full_cyclotomic
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.CaseBForSData.two_q_lt_u
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.cyclotomic_ratio_gt_of_q_lt_p
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.key_ratio_inequality_of_caseB_data
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.key_inequality_of_caseB_data
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.key_inequality_of_caseB_outputs
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.norm_error_terms_lt_inv_q
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.norm_cascade_contradiction
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.norm_cascade_contradiction_of_T_caseB
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.norm_cascade_contradiction_of_caseB_data
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.norm_cascade_contradiction_of_caseB_outputs
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.norm_cascade_contradiction_of_main_size_bound
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.norm_cascade_contradiction_of_caseB_data_main_size_bounds
set_option linter.style.longLine false in
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.norm_cascade_contradiction_of_caseB_outputs_main_size_bounds

-- BG App C Theorem C bridge: once Section 16 supplies the field-normalizer data,
-- C.1/C.2 plus the carried C.3 generator-relation conclusion force `p ≤ q`.
#assert_only_allowed_axioms OddOrder.BG.AppC.theoremC
#assert_only_allowed_axioms OddOrder.BG.AppC.lemmaC2_card_ge_two_of_conditionA
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.appCNormSetTwistedUnitStep_of_field_step
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.appCNormSetGeneratorRelation_of_twisted_unit_step
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.appCNormSetGeneratorRelation_of_twisted_normOne_step
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.appC_normSet_generator_relation

#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.sigma_eq_left_eq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.sigma_eq_right_eq
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.sigma_eq_iff_left_right_eq

#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.fieldNormalizerKernel_inf_complement_eq_bot
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.P_inf_U_eq_bot
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.s_mem_W2
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.s_ne_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.s_pow_p_eq_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.s_normalizes_Q

#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerPrimeLineElement_mem
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerPrimeLineElement_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerPrimeLineElement_neg
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerPrimeLineGenerator_mem
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerPrimeLineGenerator_ne_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerPrimeLineGenerator_pow_p
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerNormOneUnits_card_gt_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.exists_fieldNormalizerNormOneUnit_ne_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.fieldNormalizerKernel_sup_complement_eq_top
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.P_sup_U_eq_sigma_top
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.exists_normOne_primeLine_normOne
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.exists_sigma_normOne_primeLine_normOne_of_mem_PU
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.generatorRelation_step2_primeLine
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.generatorRelation_step2_primeLine_of_sigma_mem_U
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.s_not_normalizes_U
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.W2_not_le_normalizer_U
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.s_mem_P
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.s_zpow_mem_P
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.s_zpow_mem_P_sup_U
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.subgroup_eq_P_sup_U_of_U_le_of_le_P_sup_U_of_ne_U
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.t_pow_normalizes_U
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.t_zpow_normalizes_U
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.t_zpow_conj_sigma_inr_mem_U
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.s_zpow_mul_t_zpow_conj_sigma_inr_mul_s_zpow_mem_P_sup_U
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.exists_step4_decomposition_of_zpow_tConj_normOne
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.s_zpow_mul_t_pow_conj_sigma_inr_mul_s_zpow_eq_sigma_inr_tConjNormOneUnitsAut_pow
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.s_zpow_mul_sigma_inr_tConjNormOneUnitsAut_pow_mul_s_zpow_mem_P_sup_U
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.exists_step4_decomposition_of_zpow_tConjNormOneUnitsAut_pow
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.right_component_of_step4_tConjNormOneUnitsAut_pow_decomposition
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.exists_step4_first_k_three_decomposition
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.right_component_of_step4_first_k_three_decomposition
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.s_zpow_neg_two_eq_primeLineElement_neg_two
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.normN_two_mul_sub_one_of_step4_first_k_three_decomposition
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.appC_normSet_generator_relation_of_first_k_three_coordinate
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.t_mem_P1
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.t_ne_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.t_pow_p_eq_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.P1_normalizes_U
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.t_normalizes_U
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.P1_ne_W2
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.W2_ne_P1
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.P_sup_U_inf_conj_eq_U_or_eq_P_sup_U_of_normalizes_U
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.P_sup_U_inf_conj_t_pow_eq_U_or_eq_P_sup_U

#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.normOneUnitsEquivU_twistedInv_tConjNormOneUnitsAut_apply_coe
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.normOneUnitsEquivU_tConjNormOneUnitsAut_pow_apply_coe
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.appC_twisted_normOne_step_of_tConjNormOneUnitsAut

-- BG App C Lemma C.3 Step 4: the transported `Q` is commutative, so the
-- `s^{-n}t^n` commutator factors used to pass from (C.3) to (C.4)
-- can be reordered.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.Q_mul_comm
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.W2_pow_p_eq_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.Q_pow_q_eq_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.W2_inf_Q_eq_bot
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.s_inv_pow_mul_t_pow_mul_comm
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.t_inv_pow_mul_s_pow_mul_comm
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.FieldNormalizerData.s_inv_pow_mul_t_pow_mul_comm_t_inv_pow_mul_s_pow

-- Peterfalvi (14.7) σ-bridge (POLE-2): the ungated transport of the (14.2)(a) field
-- model into `G` and its assembly into `FieldNormalizerData`. Takes the field iso as
-- *input*, so it is independent of the §13 character theory that supplies it.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerKernelTransport_injective
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerKernelTransport_range
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerComplementTransport_injective
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerComplementTransport_range
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerComplementTransport_exists
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.fieldNormalizerData_of_repr

-- BG App C Remark (I): condition (A) `gcd((p^q-1)/(p-1), p-1)=1` ⟺ `q ∤ (p-1)`.
-- Foundation lemma of the finite-field norm-set argument toward BG Theorem C (`p ≤ q`).
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.conditionA_iff_not_dvd

-- BG App C Remark (VII): the norm-one subgroup `U ≤ 𝔽_{p^q}ˣ` has order
-- `(p^q - 1)/(p - 1)`, the `|U|` used in the `q ≥ 5` branch of Lemma C.2.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneUnits_card
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.pow_sub_one_le_normOneUnits_card
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.pow_sub_one_add_pow_sub_two_le_normOneUnits_card
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneUnits_card_sq_ge_pow_mul_one_add_pow_sub_two

-- BG App C Remark (VII): under condition (A), every unit of `𝔽_{p^q}` splits
-- as a prime-field unit times a norm-one unit.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.exists_primeFieldUnit_mul_normOne

-- BG App C Remark (VII): the prime-field units and `U` meet trivially, giving
-- the direct-product side of `𝔽_{p^q}ˣ = 𝔽_pˣ × U` under condition (A).
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.primeFieldUnits_inf_normOneUnits_eq_bot

-- BG App C Remark (VII): the carrier-set product `𝔽_pˣ · U` is all of
-- `𝔽_{p^q}ˣ` under condition (A).
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.primeFieldUnits_mul_normOneUnits_eq_univ

-- BG App C Lemma C.3 Step 1: under condition (A), every field element
-- lies in the `U`-orbit of any fixed nonzero prime-field line; equivalently,
-- every concrete `P ⋊ U` element has a `u s₁ v` decomposition with
-- `s₁ ∈ 𝔽_p s`.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.exists_normOne_mul_primeFieldUnit_mul_eq
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.exists_normOne_mul_primeLine_eq
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_exists_inr_primeLine_inr

-- BG App C Lemma C.3 Step 3: the norm-one subgroup acts irreducibly on
-- the additive `𝔽_p`-space `𝔽_{p^q}` under condition (A), and therefore
-- any nonzero `U`-stable subspace or subgroup-kernel preimage generates all of
-- `P ⋊ U` together with `U`.
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneUnits_invariant_submodule_eq_top_of_ne_bot
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusSubspaceKernel_inl
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusSubspaceGroup_eq_top_of_ne_bot
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.mem_normOneFrobeniusKernelPreimageSubmodule
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusKernelPreimageSubmodule_invariant_of_inr_range_le
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusKernelPreimageSubmodule_ne_bot_of_exists_inl
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_exists_inl
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusSubgroup_eq_top_of_inr_range_le_of_ne_inr_range

-- BG App C Lemma C.3 Step 2: on a prime-field line, the direct-product
-- intersection `U ∩ 𝔽_pˣ = 1` forces the generator-relation alternatives,
-- both as a finite-field equation and as a concrete `P ⋊ U` membership test.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneUnits_eq_one_of_mem_primeFieldUnits
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneUnits_eq_one_of_primeLine_relation
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.generatorRelation_step2_primeLine
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_generatorRelation_step2_primeLine

-- BG App C Lemma C.3 Step 4 final paragraph: reading the additive coordinate
-- of the first `k = 3` equation in concrete `P ⋊ U` gives `N(2*w-1)=1`.
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition

-- BG App C Lemma C.3 Step 4: the `p`-power Frobenius preserves the norm-set
-- relation `a,b ∈ E` and `a+b=2` used in the generator-relation propagation.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.pow_p_natCast_two
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normN_pow_p
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.two_sub_pow_p
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normSetE_pow_p
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normSetE_frobenius_pair
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneUnits_eq_one_of_pow_sub_one_eq_one
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.inv_mem_of_twistedInv_step
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.twisted_unit_step_of_twisted_field_step
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normSetE_eq_inv_of_twisted_unit_step
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normSetE_eq_inv_of_twisted_field_step
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.forall_normN_two_mul_sub_one_of_normSetE_eq_inv
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.forall_normN_two_mul_sub_one_of_twisted_field_step
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.forall_normN_two_mul_sub_one_of_twisted_unit_step
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normSetE_eq_inv_of_twisted_normOne_step
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.forall_normN_two_mul_sub_one_of_twisted_normOne_step

-- BG App C Lemma C.2 q≥5 setup: the concrete Frobenius group `P ⋊ U` action
-- conjugates additive-kernel elements by field multiplication.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_conj_inl

-- BG App C Lemma C.2 q≥5 setup: the concrete semidirect product has a
-- nontrivial normal additive kernel, a nontrivial norm-one complement, and the
-- resulting subgroup pair is a Frobenius group.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_normal
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_isComplement_normOneFrobeniusComplement
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_ne_bot
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneUnits_card_gt_one
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusComplement_ne_bot
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_isFrobeniusGroup
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup_card_eq
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_index_eq_normOneUnits_card
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_mul_comm
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_irreducibleCharacter_apply_one_eq_one
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_induce_isIrreducible
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_induce_apply_one
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_induced_irreducible_apply_one_eq_normOneUnits_card
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_induce_eq_zero_of_not_mem_kernel
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_induce_support_subset_kernel
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_induce_apply_inr_eq_zero
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_inl_ne_one
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_inl_eq_commutator
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_linear_irreducible_apply_inl
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_irreducibleCharacter_apply_inl_of_apply_one_eq_one
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_apply_inl_eq_apply_one_of_kernel_subset
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_sum_kernelCharacter_degree_sq_eq_normOneUnits_card
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_sum_kernelCharacter_column_inl_eq_normOneUnits_card
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_le_centralizer_inl
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_centralizer_inl_le_kernel
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_centralizer_inl_eq_kernel
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobeniusKernel_card_eq
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_centralizer_inl_card_eq
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_column_sq_sum_inl_eq
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_column_sq_sum_two_mul_eq
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_sum_nonKernelCharacter_column_inl_eq

-- BG App C Lemma C.2 q≥5 setup: the pair condition `us+vs=2s` is the
-- corresponding product equation in the additive kernel of `H = P ⋊ U`.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.mem_normOnePairSetAt_iff_inl_mul_inl

-- BG App C Lemma C.2 q≥5 class-sum bridge: every `U`-translate `u*s`
-- lies in the conjugacy class of `s` in `H = P ⋊ U`.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneClassAt_mul_eq

-- BG App C Lemma C.2 q≥5 class-sum bridge: arbitrary conjugation of an
-- additive-kernel element is controlled by the `U`-coordinate, and hence the
-- conjugacy class of `s` is exactly its `U`-orbit.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_conj_inl_any
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.exists_normOne_mul_of_mem_normOneClass
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneClassAt_carrier_ncard_eq_normOneUnits_card
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneClassAt_two_mul_carrier_ncard_eq_normOneUnits_card
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneClassAt_out_centralizer_card_eq
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_classSumCoeff_one_mul_pow_eq_character_sum
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneClassAt_out_apply_eq_inl
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneClassAt_out_inv_irreducibleCharacter_apply_eq_star_inl
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_classSumCoeff_one_mul_pow_eq_concrete_character_sum
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_kernelCharacter_concrete_classSumContribution_eq
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_classSumCoeff_one_mul_pow_eq_kernelContribution_add_nonKernelContribution
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_sum_nonKernelCharacter_normSq_inl_eq
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_sum_nonKernelCharacter_normSq_inl_le
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.sum_normSq_mul_norm_le_sum_normSq_mul_sqrt_sum_normSq
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusClassSumConcreteTerm_norm_le_of_normOneUnits_card_le_degree
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusNonKernelContribution_norm_le_sum_of_degree_ge
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt_of_degree_ge
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobeniusNonKernelContribution_norm_le_pow_mul_sqrt
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card_of_error_separation
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_error_separation_of_five_le
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOneFrobenius_classSumCoeff_one_gt_normOneUnits_card
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normSetE_ncard_ge_two_of_five_le

-- BG App C Lemma C.2 q≥5 class-sum bridge: the finite-field pair set is the
-- fixed-product fiber over `inl (2*s)` before passing to the full product class.
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.classPairSet_eq_iUnion_fixedProductClassPairSet
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.classPairSet_ncard_eq_finsum_fixedProductClassPairSet_ncard
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.classPairSet_ncard_eq_classSumCoeff
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.classSumCoeff_eq_finsum_fixedProductClassPairSet_ncard
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneFrobenius_mk_conj_eq
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.fixedProductClassPairSet_ncard_eq_of_isConj
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.finsum_fixedProductClassPairSet_ncard_eq_carrier_ncard_mul
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.classSumCoeff_eq_carrier_ncard_mul_fixedProductClassPairSet_ncard
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOnePairSetAt_isFixedProductClassPair
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.exists_normOnePairSetAt_of_isFixedProductClassPair
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normOnePairSetAt_ncard_eq_fixedProductClassPairSet_ncard
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_pairSetAt_ncard
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.classSumCoeff_normOneClassAt_self_two_mul_eq_normOneUnits_card_mul_normSetE_ncard
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.two_ne_zero_galoisField
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normSetE_ncard_ge_two_of_normOneCoeff_gt_normOneUnits_card
#assert_only_allowed_axioms
  OddOrder.BG.AppC.NormSet.normSetE_ncard_ge_two_of_normOneCoeff_one_gt_normOneUnits_card

-- BG App C Lemma C.2 q≥5 class-sum bridge: a finite-field pair counted by
-- `normOnePairSetAt` gives a class pair for the class-sum structure constant.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOnePairSetAt_isClassPair

-- BG App C Lemma C.2 bridge: `|E|` equals the number of norm-one pairs
-- `(u, v) ∈ U × U` satisfying `u + v = 2`, the finite-field structure constant.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOnePairSet_ncard_eq_normSetE_ncard

-- BG App C Lemma C.2 bridge in the class-sum form `u*s + v*s = 2*s`.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOnePairSetAt_ncard_eq_normSetE_ncard

-- BG App C Lemma C.3 Step 4 finite-field pair API: an element `a ∈ E` gives
-- the concrete norm-one pair `(a, 2-a)` in both `u + v = 2` and
-- `u*s + v*s = 2*s` forms.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOneUnitOfMemNormSetE_coe
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOnePairOfMemNormSetE_mem_normOnePairSet
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normOnePairOfMemNormSetE_mem_normOnePairSetAt

-- BG App C Lemma C.3 note (`p = 3`): characteristic three makes
-- `2*a - 1 = 2-a`, so the norm-set inverse closure is purely finite-field.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normSetE_eq_inv_of_p_eq_three

-- BG App C Lemma C.1: if the norm set `E = {a | N(a)=N(2-a)=1}` is inverse-closed and
-- `|E| ≥ 2`, then `p ≤ q`. The Möbius iterate `aₖ` gives `N((1-a)k+1)=1` for all `k ∈ 𝔽_p`,
-- and the degree-`q` Frobenius polynomial `∏_{i<q}((1-a)^{p^i}X+1)-1` then has `p` roots.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.lemmaC1

-- BG App C Lemma C.2 (q=3): a root-free cubic `f_c = X(X-2)(X-c)+(X-1)` (pigeonhole) is
-- irreducible, its root `a ∈ 𝔽_{p^3}` has Frobenius orbit `{a, a^p, a^{p²}}` of 3 distinct
-- roots, so `f_c = ∏(X - a^{p^i})` and reading `f_c(0)=-1`, `f_c(2)=1` gives `N(a)=N(2-a)=1`.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.exists_mem_normSetE_three
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.normSetE_ncard_ge_two_of_eq_three

-- BG App C Lemma C.2: combine the q=3 cubic branch with the q≥5 class-sum
-- branch to show that the norm set has at least two elements.
#assert_only_allowed_axioms OddOrder.BG.AppC.NormSet.lemmaC2

-- BG (2.11) keystone: for the conjugation operator `T = ρ x` on `End V`, the `εᵐ`-eigenspaces
-- satisfy `dim E₀ = dim E_m + 1` (`m ≢ 0`).  Combines the abstract orbit-count
-- (`CyclicPermEigen.finrank_eigenspace_fixed_succ`) with the Burnside-basis monomial action.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.finrank_cyclicEndConjEigenspaceFin_succ

-- BG Prop 2.2(a) (alg-closed Clifford) materialised for an extraspecial `H`: the restriction
-- `Res^G_H ρ` of a faithful irreducible `ρ` is irreducible — `hVP`, via Clifford multiplicity-one
-- (`CliffordMultiplicityOne`), the conjugate-character bridge, and BG 2.10 constituent faithfulness.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.restriction_isIrreducible_of_extraspecial

-- BG Theorem 2.5 (group level), divisibility part, conditional on `hVP`: `dim V ≡ ±1 (mod h)`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.finrank_modEq_of_faithful_irreducible

-- BG Theorem 2.5 (group level), fully grounded for an extraspecial `P` (no `hVP` hypothesis):
-- the divisibility `dim V ≡ ±1 (mod h)` and the `C_V(H)` dichotomy.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.finrank_modEq_of_extraspecial
#assert_only_allowed_axioms OddOrder.RepresentationTheory.finrank_eq_sub_one_of_extraspecial

-- BG Lemma 2.3 (Fong–Swan): for a finite solvable group `G` and an absolutely irreducible
-- `FG`-module `V` over any field `F`, `dim_F V ∣ |G|`.  Proved by the elementary BG Clifford
-- induction (not Brauer lifting): alg-closed core `finrank_dvd_card_of_isAlgClosed_of_irreducible`
-- (strong induction on `|G|`, prime-index `H ◁ G`, char-free Clifford, case (i)/(ii) split) plus
-- base change to `AlgebraicClosure F`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.finrank_dvd_card_of_isAlgClosed_of_irreducible
#assert_only_allowed_axioms OddOrder.RepresentationTheory.finrank_dvd_card_of_isAbsolutelyIrreducible

-- BG Theorem 3.10 (general nilpotent M packaging): a solvable Frobenius group `H = KR` acting on a
-- nontrivial nilpotent (in fact solvable) `M` with `(|H|,|M|)=1`, `C_M(K)=1`, prime-manner
-- `C_M(⟨x⟩)=C_M(R)` gives `|M| = |C_M(R)|^{|R|}` (b) and `C_M(R)` cyclic ⟹ `⁅K,K⁆` acts trivially (c).
-- The group-level Case-1 induction gluing the elementary-abelian base leaf (issue 3011); closes BG §3.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03g.bgThm310_nilpotent

-- BG Lemma 1.21(d): `G` has `p`-length one iff the subgroup generated by all `p`-elements
-- (`pElementsSubgroup` = O^{p'}(G)) has a normal `p`-complement.  Closes BG §1 (the last of the
-- five parts of Lemma 1.21).
#assert_only_allowed_axioms OddOrder.BG.Ch1.hasPLengthOne_iff_hasNormalPComplement_pElementsSubgroup

-- BG Lemma 2.7: for distinct primes `p ≠ q`, an elementary abelian `Q` of order `q²` acting
-- faithfully (`𝔽_p`-linearly) on a `2`-dimensional `𝔽_p`-space `P` (= `Q ⊆ Aut(P)`) has
-- `q ∣ p − 1` and a non-identity element acting as a scalar of order `q`.  The crux
-- `isCyclic_of_faithful_isIrreducible` = Gorenstein Thm 3.2.3 (finite abelian + faithful
-- irreducible ⟹ cyclic).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.isCyclic_of_faithful_isIrreducible
#assert_only_allowed_axioms OddOrder.RepresentationTheory.elemAbelian_aut_action

-- Gorenstein Theorem 3.2.2 (input to BG Theorem 3.4): a finite group with a faithful irreducible
-- representation over an algebraically closed field has cyclic centre `Z(G)`.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.isCyclic_center_of_faithful_irreducible

-- Peterfalvi (3.1)/(3.3): the linear-character family `ω` of the cyclic group `W = W₁ × W₂`.
-- `W` is abelian (cyclic), so `χ ↦ ω(χ) = linearIrreducibleCharacter χ` is a bijection
-- `Hom(W, ℂˣ) ≃ Irr(W)` (`omegaEquiv`); each `ω(χ)` has degree one (`omega_apply_one`).
-- Foundation for the `ω_{ij}` / `α_{ij}` basis (3.4) and the `σ`-isometry (3.5).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.isMulCommutative_W
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaEquiv

-- Peterfalvi (3.1)/(3.3): `W = W₁ × W₂` as an internal direct product — the multiplication map
-- `↥W₁ × ↥W₂ ≃* ↥W` (W abelian, W₁ ⊓ W₂ = ⊥, W₁ ⊔ W₂ = ⊤), used to split `ω_{ij} = ω_{i0}·ω_{0j}`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.wProdEquiv

-- Peterfalvi (3.3): the `ω_{ij} = ω_{i0}·ω_{0j}` factorization of a linear character of `W`,
-- via the internal-product projections `wProj1`/`wProj2` and their reconstruction `w = w₁·w₂`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.char_eq_wProj_comp_mul

-- Peterfalvi (3.3): the `ω_{i0}` / `ω_{0j}` factors have `W₂` / `W₁` in their kernels (the
-- defining property of the two sub-families of `Irr(W)`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.W2_subgroupOf_le_ker_comp_wProj1
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.W1_subgroupOf_le_ker_comp_wProj2

-- Peterfalvi (3.3)→(3.4): factor projections `wFst`/`wSnd : ↥W →* ↥W₁/↥W₂` kill `W₂`/`W₁`,
-- so `χ₁.comp wFst` / `χ₂.comp wSnd` are the `ω_{i0}` / `ω_{0j}` used to build the `α_{ij}`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.wFst_eq_one_of_mem_W2
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.wSnd_eq_one_of_mem_W1

-- Peterfalvi (3.4): `α_{ij} = (1_W - ω_{i0})(1_W - ω_{0j})` as a class function, its vanishing on
-- `W₁`/`W₂`, and its membership in `CF(W, V)` (`V = W ∖ (W₁ ∪ W₂)`), packaged as `alpha`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.mem_Vdiff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaCF
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaCF_eq_zero_of_mem_W2_subgroupOf
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaCF_eq_zero_of_mem_W1_subgroupOf
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaCF_mem_supportedSubmodule
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alpha

-- Peterfalvi (3.4) dimension input: for a finite commutative group the class functions supported
-- on `A` have dimension `|A|` (restriction/extension-by-zero gives `CF(H,A) ≃ (↥A → ℂ)`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.finrank_supportedSubmodule_eq_card

-- Peterfalvi (3.4) dimension count: `W = W₁ × W₂` membership characterization (`x ∈ W₂ ↔ wFst x = 1`
-- etc.), the bijection `V ≃ (W₁ \ 1) × (W₂ \ 1)`, the count `|V| = (w₁−1)(w₂−1)`, and the resulting
-- `dim CF(W, V) = (w₁−1)(w₂−1)` behind the `α_{ij}` basis.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.eq_wFst_mul_wSnd
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.mem_W2_subgroupOf_iff_wFst_eq_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.mem_W1_subgroupOf_iff_wSnd_eq_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.supportInVdiffEquiv
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.card_supportInSubgroup_Vdiff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.finrank_supportedOnV

-- Peterfalvi (3.4) linear-independence foundations: the Fourier expansion of `α_{ij}` into the
-- `ω`-family (`α = 1 - ω_{i0} - ω_{0j} + ω_{ij}`) and orthonormality of `Irr(W) = {ω(χ)}`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaCF_eq_omega_combination
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_inner_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_inner_ne

-- Peterfalvi (3.4) Fourier coefficients `⟨α_{kl}, ω_{ij}⟩ = δ`: the character-group dual
-- `(χ₁,χ₂) ↦ χ₁∘wFst·χ₂∘wSnd` is injective (`comp_mul_injective`, the dual of W = W₁ × W₂), and the
-- inner products of α against the ω_{ij} collapse to the Kronecker delta.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.comp_mul_injective
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar_inj
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alpha_inner_omega_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alpha_inner_omega_ne

-- Peterfalvi (3.4): the `α_{ij}` family is a basis of `CF(W, V)`.  Linear independence via the
-- biorthogonal system, the index count via Pontryagin self-duality `|Hom(W_k, ℂˣ)| = |W_k|`, and
-- the basis = lin-indep family of the right cardinality.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.card_charGroup_subgroupOf
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaLinearIndependent
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.nonempty_charNeOne
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaBasis

-- §5 (3.5.1): the Gram matrix of the induced family `(Ind_W^G α_{ij})`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_omegaProdChar_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaCF_eq_omegaProdChar_combination
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaCF_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.tau_alpha_inner

-- §5 (3.2.a): the §4 Dade map for the TI-cyclic hypothesis is induction `Ind_W^G`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.induceTerm_eq_of_mem_V
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.induce_apply_eq_self_of_mem_V
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.isDadeMap_inducedDadeMap
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.tau_eq_induce

-- §5 (3.5.1) complete: Frobenius reciprocity input + the norm-3 virtual characters `β_{ij}`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.restrict_trivialClassFunction_eq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaCF_inner_omega_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.tau_alpha_inner_trivial
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alpha_mem_ZIrr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.inner_trivialClassFunction_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.beta_mem_ZIrr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.beta_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.beta_inner_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.beta_inner_trivial

-- §5 (3.5.1): the norm-3 decomposition `β_{ij} = ∑_{χ ∈ A_{ij}} χ` into signed nontrivial irreducibles.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.card_eq_three_of_sum_sq_eq_three
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedNontrivialIrr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.exists_signedTriple_of_inner_self_three
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_betaSet

-- BG Theorem 3.4 (algebraically closed core, the keystone consumer of BG Theorem 2.5): a solvable
-- group `G` of odd order with a normal Hall subgroup `K`, a prime-order complement `R`, acting on
-- `V/F` with `char F ∤ |G|`, `F` algebraically closed, and `C_V(R) = 0`, gives `[R,K] ⊆ C_K(V)`.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03d.thm34_algClosed
-- BG Theorem 3.4 (general field, via base change to the algebraic closure, BG (2.9)).
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03d.thm34

-- §5 (3.5.2): the signed-irreducible API and the lemma `L(ij, i'j')`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedNontrivialIrr.apply_one_ne_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedNontrivialIrr.ne_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.irreducibleCharacter_coe_ne_neg
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.isSignedNontrivialIrr_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedNontrivialIrr.ne_neg_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedNontrivialIrr.inner_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedNontrivialIrr.mem_ZIrr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedNontrivialIrr.inner_trivial
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.orthonormal_option_trivial
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTriple
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.exists_isSignedTriple_of_inner_self_three
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTriple.neg_not_mem
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTriple.inner_right_signed
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTriple.inner_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTriple.no_neg_of_inner_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTriple.L_of_inner_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTriple.O_card_inter_eq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.beta_apply_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_isSignedTriple_beta
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.beta_inner_eq_one_of_one_shared
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.betaTriple_L
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.beta_inner_eq_zero_of_both_diff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.betaTriple_O

-- §5 (3.5.3): `sup(w₁, w₂) ≥ 5`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sup_card_ge_five

-- §5 (3.5.1/3.5.2): the fixed family of signed triples `A_{ij}` with its `L`/`O` relations.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.Afam
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.Afam_isSignedTriple
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.Afam_L
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.Afam_O

-- §5 (3.5.4): the abstract signed-triple grid + uniqueness + triangle reduction + Case II.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.exists_third_of_card_three
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.card_inter_triple
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.card_filter_neg_triple
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.triple_distinct
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.neg_not_mem_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.common_unique
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.exists_triangle_of_not_exists_common
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.exists_namedTriangle
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.caseII_false
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.ne_neg_of_Llinked
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.eq_of_mem_Llinked
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.lStep
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.oStep
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.oStep_out
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.oStep_force
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.oStep_both_out
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.lStep_third
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.not_two_shared
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.not_disjoint_Llinked
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.cell_eq_triple
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.pencilCell
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.transversalCell
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.caseI_tail
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.caseI_special
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.caseI_false
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.exists_common
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.existsUnique_common
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.common_not_mem_other_column
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.transpose
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.cell_decomposition
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.common_ne_other_column_mem
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.symm_cell_decomposition
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.third_not_mem_far_cell
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.common_ne_other_row_mem
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.orthonormal_of_injective_of_no_neg
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.gridFamily
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.gridFamily_orthonormal
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.symm_orthonormal_family
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.two_col_orthonormal_family
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.IsSignedTripleGrid.two_col_orthonormal_family_reindexed
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.Afam_isSignedTripleGrid
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.Afam_existsUnique_common
-- BG Theorem 3.5 (algebraically closed core): a Frobenius group `G = KR` with solvable kernel `K`
-- and prime-order complement `R`, acting on `V/F` (`char F ∤ |G|`, `F` algebraically closed), with
-- `dim C_V(R) = 1`, gives `K' = ⁅K,K⁆ ⊆ C_K(V)`.  Hard core = step-9 Clifford theory.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03e.thm35_algClosed
-- BG Theorem 3.5 (general field, via base change to the algebraic closure, BG (2.9)).
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03e.thm35
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_colCommon
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_rowCommon
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_chiFamily_of_decomposition
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_chiFamily_symm
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_chiFamily_two_col
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_chiFamily_transpose
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_chiFamily
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.classFunction_span_irreducibleCharacter_eq_top
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.irreducibleCharacterBasis
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar_surjective
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdEquiv
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaIrrEquiv
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.inner_sum_smul_sum
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_irreducibleCharacter
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_inner_irreducibleCharacter
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdEquiv_symm_omegaProdChar
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_omega
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_trivial
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_alphaCF
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_mem_ZIrr
-- FT-path signature bridge (endpoint C, ft_path_policy.md §4): the (3.2) σ-isometry
-- as an integral character map `S07.IntegralCharacterMap ↥W G` (= §13 `S15.Hypothesis.tau3`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_isIntegralIsometry
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_trivial
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_mem_ZIrr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply_of_mem_V
-- FT-path signature bridge (endpoint B, ft_path_policy.md §4): the (3.3) ω-grid indexed by
-- `Fin |W₁| × Fin |W₂|` with `0 ↦ 1` (= §13 `S15.Hypothesis.omega`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.charBaseEquiv
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.charEquiv
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.charEquiv_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaGrid
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaGrid_zero_zero
-- FT-path signature bridge (endpoint E, ft_path_policy.md §4): the ω^σ-grid = σ(ω), the
-- virtual characters ω_{ij}^σ ∈ ZIrr G (= S12.CharacterParameters.omegaSigma / S15.Hypothesis.eta).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaSigmaGrid
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaSigmaGrid_apply
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaGrid_mem_ZIrr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaSigmaGrid_mem_ZIrr
-- FT-path signature bridge (endpoint D, ft_path_policy.md §4): the certain-type μ-column
-- (13.1.e) induction relation in explicit `δ·(μ_i − μ_0)` form (= §13 `S15.Hypothesis.mu_definition`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.Hypothesis.induce_omegaColumnDiff_mu_diff
-- Same (13.1.e), in the `ω`/`μ`-grid difference form `Ind_W^S(ω_{ij} − ω_{0j}) = δ_j(μ_{ij} − μ_{0j})`
-- consumed directly by the §13/§16 character-data producer (`Section16CharacterData.mu_definition`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.Hypothesis.induce_chiColumn_diff_mu_diff
-- §5 (3.2.a) full: `σ` agrees with the Dade map `τ = Ind_W^G` on all of `CF(W, V)`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaBasis_apply
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.induceLinear
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.induceLinear_apply
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_eq_tau
-- §5 Peterfalvi (1.3)(a) engine + (3.2)(c)(d): vanishing on `V` from orthogonality to `CF(W, V)`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.eq_zero_of_mem_of_inner_supported_eq_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.innerLeftFunctional
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.innerLeftFunctional_apply
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.vanishOnV_of_inner_alphaCF
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_apply_irreducibleCharacter_of_mem_V
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_apply_of_mem_V
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.eq_zero_of_mem_V_of_inner_chiFam_eq_zero
-- §5 Peterfalvi Theorem (3.2) capstone: the linear isometry `σ` with properties (a)-(d).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_sigma
-- §5 Peterfalvi (3.6)-(3.7): the σ-image coefficient grid `a_{ij}` and its additive identity.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaCombo_mem_supportedSubmodule
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaCombo
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaCombo_coe
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.inner_sigma_eq_zero_of_vanishOnV
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaNC
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff_add_eq
-- §5 Peterfalvi (3.8) corollary: a small-support separable coefficient grid is identically zero.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.grid_eq_zero_of_ncard_support_lt
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff_eq_zero_of_sigmaNC_lt
-- §5 norm-`2` Dade-image trichotomy endgame (Peterfalvi (4.8)/(10.5)): the `TICyclicHypothesis`-level
-- toolkit shared by the §6 certain-type isometry and the §10 (10.5) Dade-image identity.  A virtual
-- character `X` with `‖X‖² = 2` whose difference with `s·(χ_{P₁} − χ_{P₂})` vanishes on `V` equals it.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.ncard_sigmaCoeff_ne_zero_le_two
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff_eq_zero_or_one_of_inner_self_two
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff_sub_smul_chiFam_diff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.eq_smul_chiFam_diff_of_all_sigmaCoeff_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.eq_smul_chiFam_diff_of_vanishOnV

-- BG Theorem 3.6 (the vertex of the §3 subprogram and the engine of BG Theorem 10.6): `G`
-- solvable of odd order, `H ◁ G` a normal Hall subgroup with complement `R`, `R₀ ≤ R` of prime
-- order such that `C_H(R₀)` is a `Z`-group, gives `⁅H,R⁆` of `p`-length one for every prime `p`.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03f.thm36
-- BG Proposition 3.9 (§3E): an odd `p`-group acting in a Frobenius (fixed-point-free) manner on a
-- nontrivial finite group is cyclic.  Feeds BG Theorem 3.10 → Proposition 14.2(g) (issue 2007).
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.isCyclic_of_isPGroup_of_isFrobeniusAction
-- BG Theorem 3.10 conclusion-(b) ladder (issue 8013): the rank formula `finrank V = |R|·finrank V^R`
-- of the free block permutation, at the abelian-Frobenius-weight and elementary-abelian levels.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.prime_card_and_finrank_of_abelian_frobenius_weight
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.prime_card_and_finrank_of_elemAbelian
-- BG Theorem 3.10 general (non-abelian) kernel, the `K₀`-reduction dichotomy (issue 8013, piece 3):
-- for an irreducible `ρ` and normal `K₀ ⊴ G`, the `K₀`-invariants `C_V(K₀)` are `⊥` or `⊤`.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.invariants_normal_eq_bot_or_top_of_isIrreducible
-- BG Theorem 3.10 general kernel, induction base case (issue 8013, piece 3): `K` minimal normal ⟹
-- elementary abelian ⟹ the abelian-kernel rank theorem gives (a)+(b).
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.prime_card_and_finrank_of_minimalNormal_kernel
-- BG Theorem 3.10 general kernel, Case B transfer (issue 8013, piece 3): `K₀` acting trivially ⟹ `ρ`
-- factors through `G ⧸ K₀`, and `ρ̄`-invariants of `S·K₀/K₀` equal `ρ`-invariants of `S`.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.invariants_lift_map_eq_of_trivial
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.card_map_mk'_eq_of_disjoint
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.caseB_transfer
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.isIrreducible_lift_of_trivial
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.fpf_lift_of_centralizer_bot
-- BG Theorem 3.10 (a)+(b), general (non-abelian) kernel (issue 8013, piece 3 capstone): the
-- `K₀`-reduction strong induction assembling base + Case A + Case B into the irreducible-module form
-- `|R|` prime ∧ `finrank V = |R|·finrank C_V(R)` for a general Frobenius kernel `K ⊴ G`.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.prime_card_and_finrank_of_frobenius_general
-- BG Theorem 3.10 elementary-abelian reducible-module induction infrastructure (issue 8013, piece 5):
-- invariants of a subrepresentation as an ambient `finrank` (`C_V(H) ⊓ W`), and their additivity over
-- an internal direct sum of `H`-stable subrepresentations.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.invariants_toRepresentation_map_eq
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.finrank_invariants_toRepresentation_inf
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.finrank_inf_invariants_sup_of_disjoint
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.invariants_toRepresentation_eq_bot
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.invariants_toRepresentation_eq_of_inf_eq
-- BG Theorem 3.10 (a)+(b), elementary-abelian reducible-module case (issue 8013, piece 5): drops the
-- irreducibility hypothesis of piece 3 via a Maschke `⊤ = U ⊕ U'` strong induction on `finrank V`.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.exists_maschke_split
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.prime_card_and_finrank_of_frobenius_elemAbelian
-- BG Theorem 3.10 (c) elementary-abelian (issue 8013, piece 5): `C_V(R)` cyclic ⟹ `K' ⊆ C_K(V)`,
-- threaded through the same Maschke induction (irreducible leaf = Theorem 3.5 `thm35`).
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.commutator_eq_one_of_frobenius_elemAbelian
-- Base change preserves a subgroup-equality of invariants (issue 8013, piece 5): the prime-manner
-- transfer `C_M(x) = C_M(R)` from `ZMod p` to its algebraic closure, for the group↔module bridge.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.invariants_baseChangeRepresentation_comp_eq
-- BG Theorem 3.10 (a)+(b), elementary-abelian GROUP case, general kernel (issue 8013, piece 5+2b):
-- the `MulDistribMulAction` group form, dropping the abelian-kernel restriction by base change to the
-- algebraic closure + the general-kernel reducible-module Theorem 3.10.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.prime_card_and_finrank_of_elemAbelian_general
-- BG Theorem 3.10 (b) cardinality form (issue 8013, piece 5+2b = §15.2 step-4 (f) `|Q̄|=q^p`):
-- `|M| = |C_M(R)|^{|R|}` from the rank formula via `Module.card_eq_pow_finrank`.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.card_eq_pow_card_invariants_of_elemAbelian_general
-- BG Theorem 3.10 (c) GROUP form (issue 8013, piece 5 = §15.2 step-4 (g) `D'⊆C_D(Q̄)`): with the
-- genuine `IsFrobeniusGroup` and `C_M(R)` cyclic, `K'` acts trivially on `M` (`∀ g∈⁅K,K⁆, g•m=m`).
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.commutator_acts_trivially_of_elemAbelian_general
-- BG Lemma 3.2 (§3A), general branch `K ⊄ N`: in a finite Frobenius group `G = K R` with solvable
-- kernel `K`, a normal subgroup `N ⊴ G` with `K ⊄ N` meets the complement trivially (`N ⊓ R = ⊥`),
-- is contained in `K` (`N < K`), and `Ḡ = G/N` is again Frobenius with kernel `K̄`, complement `R̄`.
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.inf_complement_eq_bot_of_normal_not_le_kernel
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.normal_le_kernel_of_not_le
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03.isFrobeniusGroup_quotient_of_normal_not_le_kernel
-- BG Theorem 3.8 (§3D): `G = KR` solvable of odd order, `K ⊴ G`, `(|R|,|K|)=1`, `C_K(x)=C_K(R)` for
-- `x ∈ R^#`, and `C_{F(K)}(R)=1`, gives `⁅K,R⁆ ⊆ F(K)`.  Unblocks BG §15 Theorem 15.2 (issue 8011).
#assert_only_allowed_axioms OddOrder.BG.Ch1.S03h.thm38
-- BG Theorem 3.6 in the §10 interface form (`S10_ForwardFromKeystone`): the former forward
-- axiom `pLengthOne_commutator_of_zgroupCentralizer`, de-axiomatized (2026-06-10) to a
-- convention bridge onto `thm36`.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.pLengthOne_commutator_of_zgroupCentralizer
-- BG Theorem 15.2 (`S15_MF`, issue 8012): if `M_F < M_σ` then `M` is type `P1` with the normal
-- `q`-subgroup `Q` / minimal chief-factor `Q̄ = Q/Q₀` structure (the §15→§16 keystone, supplying
-- `Cor 15.3`'s `Q` and `Cor 15.6`'s `K* ⊆ M_F`).  The full wrapper is now sorry-free AND axiom-clean
-- (2026-06-20): the final semidirect-product gate `hsigmaprime : M_σ' ⊆ Q ⊔ ⁅D, D⁆` was discharged
-- via `S13.derivedInG_le_sup_of_normal`, and every §14 lemma it cites (`typeP_duality`, the
-- `_of_inputs` chief-factor helpers, …) is itself axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.mf_ne_msigma_typeP1_structure
-- BG Theorem 15.2(b) contrapositive (`S15_MF`, issue 8015): `π(M_F) ∩ β(M) = ∅ ⟹ M_F = M_σ`.
-- The `M_F = M_σ` endgame of Theorem 15.7(a) / the `FittingIsTI` clause of Theorem A(8): once the
-- rank-theoretic core (`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`, the sole residual) gives
-- `π(M_F) ∩ β(M) = ∅`, this lemma delivers `M_F = M_σ` via Theorem 15.2.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.mf_eq_msigma_of_piSet_inf_beta_disjoint
-- BG Theorem 15.7(a), the `≥ 3` side of the rank dichotomy (`S15_MF`, issue 8015): any prime
-- `r ∈ π(M_F) ∩ β(M)` has `r_r(M_F) ≥ 3` (via `M_F` Hall ⟹ `r_r(M_F) = r_r(M)`, and `β ⊆ α`).
-- The proved half of the rank core `piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`; sorry-free +
-- axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.three_le_pRank_mf_of_mem_beta
-- BG Proposition 14.2(e), second clause (`S14_TypePCounting`, issue 2025): in a type-`P` `E`-setup
-- with the `κ`-Hall `K` playing the `E₁`-role, no Sylow `q`-subgroup `S` of `M_σ` lies in
-- `K* = C_{M_σ}(K)`.  Proven non-circularly (Lemma 13.13 ⟹ `ℳ(K*) ≠ {M}`, Lemma 13.6 ⟹
-- `ℳ(S) = {M}`).  The linchpin of the general-Hall κ'-fact for Cor 15.3(a).  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_sylow_not_le_kstar
-- BG Proposition 14.2(e) core (`S14_TypePCounting`, issue 8016/2025): `K* = C_{M_σ}(K) ⊊ M_σ`.  Now
-- an immediate corollary of `typeP_sylow_not_le_kstar` (a Sylow `S ≤ M_σ = K*` would violate it).
-- Exposed as the 7th conjunct of `typeP_structure`.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.kstar_ne_msigma_aux
-- BG Corollary 15.3 step (`S14_TypePCounting`, issue 8016): `C_M(M_σ)` is a `κ(M)'`-group.  The
-- exact statement BG cites at the start of Cor 15.3's proof (mmd L4209).  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.centralizer_msigma_isPiSubgroup_kappa_compl
-- §12 `E`-setup adapted to a `κ(M)`-Hall `K` (`S14_TypePCounting`, issue 2025): the preamble of
-- Prop 14.2's proof, producing an `E`-setup with `E₁ ≤ K ≤ E`.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_typePESetup_kappaHall
-- BG Prop 14.2(e) packaged for `typeP_structure` inputs (`S14_TypePCounting`, issue 2025): `S ⊄ K*`
-- with `M` maximal type-`P`, `K` a Hall `κ(M)`-subgroup (no raw `E`-setup).  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_sylow_not_le_kstar_of_isHall
-- BG Corollary 15.3(a) `κ'`-fact for general Hall `H` (`S14_TypePCounting`, issue 2025): `C_M(H)` is a
-- `κ(M)'`-group for every nontrivial Hall `H ≤ M_σ`.  Via Prop 14.2(b1) + (e); the general analogue
-- of `centralizer_msigma_isPiSubgroup_kappa_compl`.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.centralizer_hall_isPiSubgroup_kappa_compl
-- BG Corollary 15.3(a) for `H = M_σ` (`S15_MF`, issue 8016): `C_M(M_σ) = (C_G(M_σ) ⊓ M_σ) ⊔ X`,
-- `X` cyclic `τ₂`.  The `ha` input that `fitting_decomposition` consumes; assembled from the
-- `κ'`-group property + Schur–Zassenhaus + Lemma 15.1(c).  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.mf_centralizer_msigma_decomp
-- BG Corollary 15.3(a) for general Hall `H` of `M_σ` (`S15_MF`, issue 2025): `ha` input modulo the
-- single `κ(M)'` fact — given `C_M(H)` is `κ'`, `C_M(H) = (C_G(H) ⊓ M_σ) ⊔ X` with `X` cyclic `τ₂`.
-- Generalizes `mf_centralizer_msigma_decomp` (κ' via hypothesis; `C_{M_σ}(X) ≠ 1` from `H ≠ ⊥`).
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.mf_centralizer_hall_decomp_of_kappaCompl
-- BG Corollary 15.3(a) for general Hall `H` of `M_σ`, **unconditional** (`S15_MF`, issue 2025): the
-- `ha` input of `mf_hall_centralizer_control` with the `κ(M)'` hypothesis now discharged by
-- `centralizer_hall_isPiSubgroup_kappa_compl`.  Closes the `ha` gate of Cor 15.3.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.mf_centralizer_hall_decomp
-- BG Corollary 15.3(b) entry helper (`S15_MF`, issue 2025): a Hall subgroup `H` of a *nilpotent*
-- `M_σ` is normal in `M` (`H = O_{π(H)}(M_σ)`, characteristic).  Contrapositive: `H ⋬ M ⟹ M_σ` not
-- nilpotent `⟹ M_F ≠ M_σ`, the `hfratt` entry.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.hall_subgroupOf_normal_of_msigma_nilpotent
-- BG Corollary 15.3(b) `QH ◁ M` core (`S15_MF`, issue 2025): three reusable nilpotent-quotient
-- facts for the step "`QH ◁ M` because `M_σ/Q` is nilpotent" (mmd L4213).
-- `isHallSubgroup_eq_oPiCore_of_nilpotent`: a Hall `π`-subgroup of a finite nilpotent group equals
-- its characteristic `π`-core `O_π`.  `isHallSubgroup_map_mk'`: the image of a Hall subgroup under a
-- quotient map is Hall in the quotient.  `characteristic_sup_hall_of_quotient_nilpotent`:
-- `N` characteristic, `Γ/N` nilpotent, `H` Hall `π` ⟹ `N ⊔ H` characteristic (the preimage of
-- `O_π(Γ/N)`).  Instantiated at `Γ = ↥M_σ`, `N = O_q(M_σ)` they make `QH` characteristic in `M_σ`,
-- hence normal in `M`.  All sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.isHallSubgroup_eq_oPiCore_of_nilpotent
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.isHallSubgroup_map_mk'
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.characteristic_sup_hall_of_quotient_nilpotent
-- BG Corollary 15.3 reusable plumbing (`S15_MF`, issue 2025).  `opiCoreInG_eq_of_normal_le`:
-- `O_π(M) = O_π(N)` when `N ◁ M` and `O_π(M) ≤ N` (identifies `Q = O_q(M)` with `O_q(M_σ)`).
-- `normal_subgroupOf_of_characteristic_subgroupOf_le`: a characteristic subgroup of an `M`-normal
-- `N` is `M`-normal (lifts `QH` char-in-`M_σ` to `QH ◁ M`).  `normal_isPiGroup_le_isHall`: a normal
-- `π`-subgroup lies in every Hall `π`-subgroup (places `Q = O_q(M_σ) ≤ H` when `q ∈ π(H)`).
-- All sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.opiCoreInG_eq_of_normal_le
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.normal_subgroupOf_of_characteristic_subgroupOf_le
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.normal_isPiGroup_le_isHall
-- BG Corollary 15.3(b) `hfratt` input (`S15_MF`, issue 2025): for `H ≤ M_σ` Hall with `H ⋬ M`, the
-- Frattini factorization `M = N_M(H)·Q` (`Q = O_q(M)`, `Q ∩ H = 1`).  `M_σ` non-nilpotent ⟹ type
-- `P₁` ⟹ `Q` with `M_σ/Q` nilpotent (Thm 15.2 engine), `QH ◁ M` (char-in-`M_σ` lift), `q ∉ π(H)`,
-- Frattini.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.hfratt_of_hall_not_normal
-- BG Corollary 15.3 itself (`S15_MF`, issue 2025): `C_M(H) = C_{M_σ}(H)·X` (cyclic `τ₂`) **and**
-- `N_M(H)`-fusion control, for `H ≤ M_σ` a nonidentity Hall subgroup.  **Now fully sorry-free +
-- axiom-clean** — the three inputs (`ha`/`hconj`/`hfratt`) are all discharged.  Resolves the BG
-- Theorem I fusion gate consumed by Peterfalvi (8.8) → `theorem88_caseB_holds`.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.mf_hall_centralizer_control
-- BG Theorem A(8) `FittingIsTI` (`S15_MF`, issue 8016): `M_F ≠ M_σ ⟹ F(M)` is a `TI`-subgroup.
-- Now **fully axiom-clean** — the last sorryAx (via `fitting_decomposition`'s cite of the sorried
-- general Corollary 15.3) is eliminated by routing through `mf_centralizer_msigma_decomp`.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.fitting_isTI_of_mf_ne_msigma
-- BG Theorem A(8) full form (`S16_MainResults`, issue 8016): `M_F ≠ M_σ ⟹ U = ⊥ ∧ FittingIsTI M ∧
-- (∃ p prime, |K| = p)`.  All three conjuncts now axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.theoremA8_structure
-- BG Corollary 15.5 (`S15_MF`, issue 8016): the full Fitting decomposition `F(M) = F(M_σ) × Y`
-- (`Y` cyclic `τ₂`), `M'' ⊆ F(M)`, `M_F ≤ M'`, etc.  Now **fully axiom-clean** — the H=M_σ cite of
-- the sorried general Cor 15.3 (the corollary's only sorryAx source) is routed through the
-- sorry-free `mf_centralizer_msigma_decomp`.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.fitting_decomposition
-- BG Corollary 15.5(a) (`S15_MF`, issue 8016): `O_{σ(M)'}(F(M))` is cyclic.  Extracted from the
-- now-clean `fitting_decomposition`; the bridge that the A(8) `FittingIsTI` rank core consumes.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic
-- BG Corollary 15.5(a), `τ₂`-membership form (`S15_MF`, issue 7007): `O_{σ(M)'}(F(M))` is a
-- `τ₂(M)`-group.  Companion to the cyclic form; the `κ'` half of the `(κ∪σ)'`-group fact used by the
-- `M_F`-internal Fitting decomposition (`τ₂ ∩ κ = ∅` by rank).  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.opiCoreInG_sigmaCompl_fittingInAmbient_primeFactors_subset_tau2
-- BG Corollary 15.5, type-`P₂` `M_F`-internal Fitting decomposition (`S15_MF`, issue 7007): for a
-- type-`P₂` maximal `M` with `κ`-Hall `K` and `(κ∪σ)'`-Hall `U`, `M' = M_F × U` (the complement
-- `hDcompl`), `F(M) = M_F ⊔ (U ⊓ C_M(M_F))` (`hFiteq`), and `M'' ≤ F(M)` (`hSDfit`).  Discharges the
-- three deep `M_F`-internal residuals of `typePData_of_isTypeP_of_inputs`; the shared linchpin of the
-- Prop 16.1 forward bridges `hP2II`/`hP1neIIIIV`/`hP1eqV`.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.typeP2_mf_internal_fitting_decomposition
-- BG Corollary 15.5(b) consequence + Peterfalvi (8.6.b II) `(M')_F = H` reduction (`S15_MF`, issue
-- 7007): for a type-`P₂` maximal `M` with `τ₂(M) = ∅`, `F(M) = M_σ` (the `Y = ⊥` half of Cor 15.5(b),
-- since `Y = O_{σ'}(F(M))` is a `τ₂(M)`-group) and the Fitting core of the derived subgroup is `M_σ`
-- (`maxNilpotentNormalHall M' = M_σ`, the `hderfit` input of `isTypeII_of_isTypeP2_of_derived_typeF`).
-- Discharges `hderfit` down to the single residual gate `τ₂(M) = ∅` (BG Theorem 15.8,
-- `tau2_transfer_constraint`).  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.fittingInAmbient_eq_Msigma_of_isTypeP2_of_tau2_empty
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2_of_tau2_empty
-- **`(M')_F = M_σ` for type-`P₂`, UNCONDITIONAL** (`S15_MF`, issue 7007 cont.¹¹; Coq `defM'F`,
-- BGsection16.v l.1135 — the `M'`_\F = H` conjunct of `of_typeII`).  Supersedes the `_of_tau2_empty`
-- reduction above: the `τ₂(M) = ∅` route was an unnecessary detour (and `τ₂(M) = ∅` is *false* for
-- some type-`P₂` `M`, cf. Cor 15.9's `N ∈ ℳ_𝓟₂` with `r ∈ τ₂(N)`).  The Fitting core of `M'` equals
-- `M_σ` by elementary `F`-core maximality + Hall transitivity: `M'` is `κ'`-Hall in `M` (complement to
-- the cyclic `κ`-Hall `K`), so `maxNilpotentNormalHall M'` is a nilpotent normal Hall subgroup of `M`,
-- hence `≤ M_F = M_σ`; conversely `M_σ` is nilpotent normal Hall in `M'`.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.coprime_card_index_subgroupOf_trans
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.isHallSubgroup_primeFactors_of_coprime_index
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2
-- BG Theorem 15.7(a), the type-classification clause (`S15_MF`, issue 7007): a type-`P₂` maximal
-- subgroup has a `TI` Fitting subgroup (contrapositive: `¬FittingIsTI ⟹ M` is type `F` or `P₁`).
-- Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2
-- BG Theorem 15.7, the full `¬FittingIsTI` structure theorem (`S15_MF`, issue 7007): `M ∈ M_F ∪ M_P1`,
-- `M_F = M_σ`, a cyclic nontrivial `X ≤ M_F`, and the faithful conjunct (c) `M' ≤ F(M)` (the printed
-- equality `M' = F(M)` is an overstatement, weakened to the inclusion matching MathComp `BGsection15`).
-- The `M' ≤ F(M)` proof is type-independent: `M' = M_σ ⊔ E'`, `E'` centralizes `M_σ` (Lemma 12.19,
-- since `π(M_σ) ∩ β = ∅`), so both summands lie in `F(M)` via `fitting_decomposition`.  Now fully
-- sorry-free + axiom-clean (the type-`F` residual is closed; the `= F(M)` gate `C_Y(E₁) = 1` is gone).
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.fitting_not_ti_cases
-- BG **Theorem 15.7(e)** infrastructure (`S15_MF`, issue 7007, type-`F` trichotomy for `isTypeI_of_isTypeF`):
-- the shared order-`p` non-TI witness extraction (`g ∉ M`, `p ∈ σ(M)`, order-`p` `X₁ ≤ M_σ ⊓ M_σ^g`,
-- `rank (M_F ⊓ C_G(X₁)) < 3`); `O_p(M_F)` noncyclic at such a witness (Coq `not_cycMp`); and the additive
-- `abelian_rank1_cyclic` (abelian noncyclic odd `p`-group ⟹ `2 ≤ pRank`).  All sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.exists_inf_conj_fitting_orderP_witness
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.not_isCyclic_opiCore_mf_of_orderP_le_conj
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.two_le_pRank_of_comm_isPGroup_not_isCyclic
-- 15.7(e) non-abelian branch (E1X_facts): `C_{M_F}(X₁)` not uniquely maximal from `¬ C_G(X₁) ≤ M`,
-- abelian `C_{M_F}(X₁)` (nilpotent + Sylows abelian via uniqueness), and the abstract
-- "nilpotent + Sylows abelian ⟹ abelian" lemma backing it.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.not_isUniquelyMaximal_mf_inf_centralizer_of_not_le
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.isMulCommutative_of_isNilpotent_of_sylow_comm
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.isMulCommutative_mf_inf_centralizer_of_not_le
-- 15.7(e) conjunct A divisibility crux (mathcomp `regular_norm_dvd_pred`, `IsFrobeniusAction` form):
-- a Frobenius action of `A` on `N` gives `|A| ∣ |N| - 1`.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.card_dvd_sub_one_of_isFrobeniusAction
-- 15.7(e) conjunct B (Coq `cycHp'`): `cyclic O_{p'}(M_F)` for non-abelian `M_F`, plus the two
-- reusable group-theory lemmas it rests on (commuting commutative join is commutative; an odd
-- commutative group of rank ≤ 1 is cyclic, via the `Z`-group `exponent = card` route).
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.isMulCommutative_sup_of_le_centralizer
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.isCyclic_of_isMulCommutative_of_rank_le_one
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.typeF_nonabelian_cyclic_opiCore_compl
-- 15.7(e) shared "`O_p(M_F)` non-abelian" step (Coq `not_cPP`), and the completed per-prime witness
-- (Coq `oZ`): every `q ∈ π(M_F)` has an `M`-normal order-`q` subgroup `Z ≤ M_F`.  `q ≠ p` uses the
-- cyclic `O_{p'}(M_F)`; `q = p` takes `Z = Ω₁(Z(O_p(M_F)))`, of order `p` by the rank-`< 3` argument
-- on `B = X₁ × Z ≤ C_{M_F}(X₁)` (Sylow-of-`G` free).  Both sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.opiCore_singleton_not_isMulCommutative_of_witness
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI
-- BG **Lemma 15.1** (`S15_MF`, issue 7007): the auxiliary `U`-factor structure of an arbitrary
-- maximal `M = K U M_σ` — `K ≠ 1 → M' = U M_σ ∧ U` abelian (15.1b); the cyclic-`τ₂` centralizer
-- funnel (15.1c); `⟨C_U(x) | x ∈ M_σ#⟩` abelian (15.1d); the Frobenius factor `U₀ M_σ` (15.1e).
-- The §14-gated content is isolated in `typeP_auxiliary_structure_gated`, which is now **fully
-- sorry-free** (its four conjuncts are the standalone clean lemmas `typeP_hall_derived_eq_and_abelian`
-- / `typeP_hall_small_subgroup_cyclic_tau2` / `typeP_centralizerGeneratedBySigma_isMulCommutative` /
-- `typeP_hall_frobenius_factor`); `typeP_auxiliary_structure` assembles it with Thm 14.7
-- (`typeP_duality`, now clean) and Thm 10.2(c)/Cor 12.10(b).  Both axiom-clean (issue 7007 "5 deep
-- theorems": this entry was stale — landed when the standalone component lemmas did).
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.typeP_auxiliary_structure_gated
#assert_only_allowed_axioms OddOrder.BG.Ch4.S15.typeP_auxiliary_structure
-- General TI-transport (`TISubset.lean`, issue 7007): if `T` is TI with normalizer-bound `Z ≤ M` and
-- every element of `A` is `M`-conjugate into `T`, then `A` is TI with normalizer-bound `M`.  Pure
-- group theory; the abstract content of BG Theorem B(5)/C(9).  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.GroupTheory.IsTISubset.of_subset_conj_of_isTISubset
-- BG Theorem C(9), structural inclusion (`S16_MainResults`, issue 7007): every element of
-- `A_0(M) − A(M)` is `M`-conjugate to an element of `Ẑ` (the `⊆` half of `A_0(M) − A(M) = 𝒞_M(Ẑ)`).
-- κ/κ'-decompose `a = a_κ·a_{κ'}`, conjugate `a_κ` into `K`, then `a_{κ'} ∈ M' ⊓ (K ⊔ K*) = K*`.
-- Discharges conjunct 10 (`A_0(M) − A(M)` TI) of `theoremC_paired_structure`.  Sorry-free + axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.a0_minus_a_subset_conj_zTilde

/-! ### Forward-axiom islands (historical mechanism; currently empty)

While a chapter is wired against **provisional forward axioms** (`sorry`-free but
mathematically contingent on the named axioms, see `scaffold-sorry-free-not-done`), the
`#assert_axioms_island` guard below pins each conditional theorem to depend on *exactly* the
standard axioms plus the explicitly listed forward axioms: stricter than mere existence (any
unlisted axiom — a `sorryAx`, or a different forward axiom — fails the build) and it requires
each listed axiom to actually be used (no stale entries). When a keystone lands and its forward
axiom becomes a theorem, the island entries migrate to `#assert_only_allowed_axioms`.

**The §10 keystone island is dissolved.** Its two members were de-axiomatized in
`S10_ForwardFromKeystone`: BG Theorem 3.6 (2026-06-10, bridge to `S03f.thm36`) and
BG Lemma 10.4(b) (2026-06-11, reduction to `S10_LocalCriteria`). Every former island entry
below is now an unconditional `#assert_only_allowed_axioms` check; the elaborator is kept for
future forward-axiom phases. -/

/-- Assert that `name` depends on *exactly* the standard axioms together with the explicitly
listed forward axioms (an "expected island"). Fails if `name` uses any unlisted axiom, or if any
listed axiom is not actually used. -/
elab "#assert_axioms_island " name:ident " expecting " "[" extra:ident,* "]" : command => do
  let constName := name.getId
  let env ← getEnv
  unless env.contains constName do
    throwError m!"axioms island: constant `{constName}` not found"
  let extraNames : List Name := (extra.getElems.toList).map (·.getId)
  for e in extraNames do
    unless env.contains e do
      throwError m!"axioms island: expected forward axiom `{e}` not found"
  let axs ← liftCoreM <| Lean.collectAxioms constName
  let allowed := OddOrder.AxiomsCheck.allowedStandard ++ extraNames
  let bad := axs.filter (fun a => !allowed.contains a)
  let missing := extraNames.filter (fun e => !axs.contains e)
  unless missing.isEmpty do
    throwError m!"axioms island FAILED: `{constName}` does not depend on listed \
axiom(s):{indentD m!"{missing}"} — remove them from the island"
  if bad.isEmpty then
    logInfo m!"axioms island OK: `{constName}` ⊆ standard ∪ {extraNames}"
  else
    throwError m!"axioms island FAILED: `{constName}` has unexpected \
axiom(s):{indentD m!"{bad.toList}"}"

/-! #### BG §13 Lemma 13.1 / Corollary 13.2 (de-axiom 済, issues 8000/0065)

Lemma 13.1 と Corollary 13.2 は BG Corollary 12.16(a)(b) を本質的に使う。当初は provisional forward
axiom (`cor1216_*`) → S12_E の sorry'd faithful statement (issue 0065) へ差し替えて de-axiom した。
**2026-06-14: Lane F が Cor 12.16 の一般 `σ(M)`-subgroup 形を `S12_Corollary1216` に PROVEN で実装**
(`S12.sigma_subgroup_pRank_normalizer_le_one` / `…not_mem_primeFactors_derived_of_tau1`,
characteristic `q`-subgroup `O_q(Y)` で `q`-group 形へ reduce; sorry-free・axiom-clean、上で `#assert`
済)し、`S13_Lemma131` の cite 先を S12_E (sorry'd, 削除済) から本一般形へ差し替えた ⟹ **§13 の
Cor 12.16 依存は完全に unconditional 化** (もはや sorry に bottom-out しない)。13.1(a) `#assert` を下記に維持。 -/

-- BG Lemma 13.1(a): every `p`-subgroup of `M ⊓ M*` centralizes `M_σ ⊓ M*`
-- (S12_E Cor 12.16 に非依存; axiom-clean).
#assert_only_allowed_axioms OddOrder.BG.Ch3.S13.pSubgroup_centralizes_Msigma_inf

-- BG Theorem 13.5: `E₁ ≠ 1` acts in a prime manner on `M_σ`. Fully unconditional —
-- Theorem 13.4 and Corollary 13.3 are axiom-clean now that Lane F's §12 (Prop 12.15 /
-- Thm 12.13 / Cor 12.16) is PROVEN, so `E1_actsPrime` bottoms out at the standard axioms only.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S13.E1_actsPrime

-- BG Lemma 13.6: `1⊂P⊆E₁`, `q∈σ(M)`, `X∈ℰ_q¹(C_{M_σ}(P))`, `S` a Sylow `q` of `M_σ` ⟹
-- `ℳ(C_G(X)) = ℳ(S) = {M}`. Reduction branch (`q∈β ∨ X⊆M_σ'`) = faithful Cor 12.14 + `M_σ`-Sylow
-- conjugacy; contradiction branch (`q∉β ∧ X⊄M_σ'`) = conjugate complement `F` (Prop 1.5 + Lemma
-- 12.19) with `X⊆C(F')`, then `A∈ℰ_p²(F)` (`p∈τ₂`) centralizes `X` (Thm 13.4 + `⁅A,E₁⁆≤F'`)
-- contradicting `C_{M_σ}(A)=1`. Fully unconditional (§12 PROVEN), axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S13.maximalContaining_eq_singleton_of_E1

-- BG Lemma 13.8: the forbidden configuration (`M*` non-conjugate to `M`, `p ∈ τ₁(M)∩τ₁(M*)`,
-- `P`-invariant Sylow `Q, Q*` with `C_Q(P)=C_{Q*}(P)=1` and `N_G(Q)⊆M*`, `N_G(Q*)⊆M`) is
-- impossible. GAP 3 (coprime quotient cover → `R` of order `r` → Theorem 13.4 conjugated to the
-- Hall complement `E` → nilpotent `M*'/M*_α` collapse) is fully unconditional and axiom-clean.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S13.forbidden_config_impossible

-- BG §10 (β-radical spine): Theorem 10.6 (every proper subgroup has `p`-length one).
-- Originally wired against two forward axioms of `S10_ForwardFromKeystone`
-- (BG Thm 3.6 + BG Lem 10.4(b)), both de-axiomatized; see that file.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.proper_hasPLengthOne

-- BG §10: Lemma 10.8(c) — for `p ∈ π(M) - β(M)`, `M'` and `M_σ` have normal `p`-complements.
-- Forward-conditional via Theorem 10.6 (`proper_hasPLengthOne`), formerly the §10 keystone island (now unconditional).
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.derived_msigma_hasNormalPComplement_of_not_mem_beta

-- BG §10: Lemma 10.8(a) — `M_β` is a Hall `β(M)`-subgroup of `G`. The intersection of the
-- normal `p`-complements of Lemma 10.8(c) over `p ∈ π(M) - β(M)`, formerly the §10 keystone island (now unconditional).
-- (The engine `isHall_oPiCore_of_forall_hasNormalPComplement` is itself unconditional.)
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.Mbeta_isHall

-- BG §10: Lemma 10.8 (full bundle): `M_β` Hall, `M'`/`M_σ` have nilpotent Hall `β(M)'`-subgroups,
-- and normal `p`-complements for `p ∈ π(M) - β(M)`. Formerly the same keystone island (via Theorem 10.6); now unconditional.
-- (The (b)-engines `isNilpotent_of_forall_hasNormalPComplement` /
-- `exists_isNilpotent_isHall_compl` are themselves unconditional.)
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.isHall_Mbeta

-- BG §10: Lemma 10.8(c) largest-prime part + its "O_{p'}(M) ⊇ all q-elements (q > p)" consequence.
-- Formerly the same keystone island (via Theorem 10.6 / Theorem 5.6's first conjunct); now unconditional.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.largestPrime_quotient_oPiCore_compl_of_not_mem_beta
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.sylow_le_oPiCore_compl_of_lt_of_not_mem_beta

-- Cor 10.9 核 (W ∩ M' is nilpotent): M' の任意の β(M)'-部分群は nilpotent。
-- Lemma 10.8(b) (`isHall_Mbeta`) 経由 — 旧 keystone island、現在は unconditional。
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.betacompl_subgroup_derived_isNilpotent

-- Cor 10.9(a) producer (W nilpotent) と Cor 10.9(a)(1)(2) (`beta_complement_centralizes`):
-- `betacompl_subgroup_derived_isNilpotent` / `sylow_le_oPiCore_compl_of_lt_of_not_mem_beta`
-- 経由 — 旧 keystone island、現在は unconditional。
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.exists_nilpotent_hall_pq
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.beta_complement_centralizes

-- M'/M_β nilpotent (Lemma 10.8 系, §13 + Cor 10.9(a)(3)/(b) で使う): isHall_Mbeta 経由 — 旧 island、現在は unconditional。
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.derivedQuotientMbeta_isNilpotent

-- Cor 10.9(a)(3): `N_M(X)'` contains a Sylow `p`-subgroup of `M'` (Frattini + Lemma 6.5(a) +
-- the nilpotent Hall `{p,q}`-producer `exists_nilpotent_hall_pq`), formerly the §10 keystone island (now unconditional).
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.beta_complement_normalizer_derived_contains_sylow

-- Cor 10.9(b): `N_G(S) ⊆ H ∩ M` (`H ≠ M`) ⟹ `M = (H∩M)·M_β` and `α(M)=β(M)`. Uses the
-- Uniqueness Theorem (`q ∉ α(M)` via `S ∈ 𝒰` contradiction), the same Frattini argument as (a)(3)
-- (`K = O_{β∪{q}}(M') = M_β·S`), and Cor 10.9(a)(2) (`beta_complement_centralizes`); formerly the same island (now unconditional).
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.beta_factorization_of_sylow_normalizer_in_intersection

-- Cor 10.7 (`sylow_structure`, 5 parts a–e): Sylow `p`-structure. All parts route through a maximal
-- `M ⊇ N_G(P)` with `p ∈ σ(M)`, where `↥M` has `p`-length one (Theorem 10.6, formerly forward-conditional);
-- Lemma 6.6 / 6.3(a) / Theorem 10.1 / Blackburn 4.16 then control `P`. Formerly the same keystone island; now unconditional.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.sylow_structure

-- Prop 10.10 (`normalizer_factorization`): for `A ∈ ℰ_p²(G)∩ℰ_p*(G)` and `Q ∈ ℋ_G*(A;q)`, some
-- Sylow `p`-subgroup `P ⊇ A` factors `N_G(P) = O_{p'}(C_G(P))·(N_G(P)∩N_G(Q))` with `P ⊆ N_G(Q)'`.
-- Part (a) is the §7 transitivity core (Prop 7.5 + Thm 7.3/7.4, unconditional); parts (b)/(c) use
-- Cor 10.7 (`sylow_structure`) and Thm 5.5(a). Formerly the same keystone island; now unconditional.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.normalizer_factorization

-- Prop 10.11(a) (`sigma_complement_not_isUniquelyMaximal`): a `σ(M)'`-subgroup `K ≤ M` is not
-- uniquely maximal. Hall `σ'`-overgroup + Theorem 4.20(c) terminal normal Sylow + `q ∉ σ(M)`
-- normalizer escape. **Unconditional** (no keystone dependency).
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.sigma_complement_not_isUniquelyMaximal

-- Prop 10.11(b) (`rank_centralizer_Msigma_inf_le_one`): `r(C_K(M_σ)) ≤ 1`. Routes through the
-- Uniqueness Theorem (contrapositives), Theorem 4.20(a) (`M' ⊆ F(M)`), and Prop 10.10
-- (`normalizer_factorization`). Formerly the same keystone island; now unconditional.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.rank_centralizer_Msigma_inf_le_one

-- Prop 10.11(a)(b)(c) capstone (`sigma_complement_rank_le_one`): part (c) applies (b) to
-- `Z = O_{σ'}(F(M))` (cyclic) and pins `C_K(M_σ) ∩ M' ≤ Z` via the Fitting centralizer chain.
-- Formerly the same keystone island (via part (b)); now unconditional.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.sigma_complement_rank_le_one

-- Prop 10.11(d) (`sigma_complement_commutator_cyclic_normal`): `[K,P]` centralizes `M_σ` and is
-- cyclic normal in `M` (Thm 3.7 fixed-point-free nilpotency + part (c)). Formerly the same island via (c); now unconditional.
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.sigma_complement_commutator_cyclic_normal

-- BG §10: Lemma 10.13 (`nonabelian_pSubgroup_rankTwo_elemAbelian_structure`): for a maximal
-- rank-two elementary abelian `A` inside a nonabelian `p`-subgroup `P`, `Z₀ = Ω₁(Z(P)) ∈ ℰ¹(A)`,
-- `C_P(A) = A₀ × Z` (`Z` cyclic ⊇ `Z₀`), and `N_P(A)` is transitive on `ℰ¹(A) − {Z₀}`.
-- Low rank via Cor 10.7(b) (central product), high rank via Thm 5.3(d)
-- (`narrow_centralizer_decomp`); part (c) is a multiplicative GL₂(p)-transvection argument.
-- **Unconditional** (the §10 island dissolved before this landed).
#assert_only_allowed_axioms OddOrder.BG.Ch3.S10.nonabelian_pSubgroup_rankTwo_elemAbelian_structure

-- BG §11: Theorem 11.5 (`sylow_p_isCommutative`) and Corollary 11.6
-- (`omega1_eq_and_centralizer_trivial`): under Hypothesis 11.1 the Sylow `p`-subgroups of the
-- exceptional maximal `M` are abelian (Thompson-transitivity ideas: Lemma 11.1(b) + Prop 1.16
-- + Lemma 10.13(c) conjugation-transitivity), `A = Ω₁(P)`, and `C_{M_σ}(A) = 1`
-- (Corollary 11.2(b)). **Unconditional.**
#assert_only_allowed_axioms OddOrder.BG.Ch3.S11.sylow_p_isCommutative
#assert_only_allowed_axioms OddOrder.BG.Ch3.S11.omega1_eq_and_centralizer_trivial
-- BG §11: Corollary 11.6(c) (`exists_distinct_conj_lines`): two distinct conjugate lines
-- `A₁ = A₀^{g₁} ≠ A₂ = A₀^{g₂}` with `A = A₁ × A₂` and trivial `M_σ`-centralizers
-- (odd index `|N_G(P) : N_M(P)| ≥ 3`). Input for Theorem 11.7. **Unconditional.**
#assert_only_allowed_axioms OddOrder.BG.Ch3.S11.exists_distinct_conj_lines
-- BG §11: Theorem 11.7 (`MsigmaA_normal`): `M_σ A ⊴ M` — the climax of §11. The complement
-- `E ⊇ A` to `M_σ` carries the descending Hall radicals `K = O_τ(E)`, `W = O_{τ∪{p}}(E)`
-- (Thm 4.20(c), `S05b_Thm420Hall`); either `A` centralises `K` and `A = Ω₁(O_p(W))` is
-- characteristic in `W ⊴ E`, or an `A`-invariant Sylow `q` of `K` forces `q ∈ σ(M)` via
-- Prop 10.10(c) / Prop 1.6(d) + Cor 11.6(c) + Prop 10.11(d). **Unconditional.**
#assert_only_allowed_axioms OddOrder.BG.Ch3.S11.MsigmaA_normal

/-! ### BG §12: Lemma 12.1 (`subgroupE_basic`) — unconditional

Lemma 12.1 (the easy structure of the complement `E = E₁E₂E₃`) is fully grounded:
its proof routes Thm 10.2's "`M'/M_σ` nilpotent" through Thm 4.20(a) instead, and the
per-prime core replaces BG's Frattini argument with Burnside + the mathlib cyclic-Sylow
commutator dichotomy. No keystone forward axiom is involved. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.subgroupE_basic

/-! ### BG §12: Lemma 12.2(a) (`prime_mem_sigma_or_tau2`) — unconditional

For a nonidentity `p`-subgroup `X` and `M* ∈ ℳ(N_G(X))`, the prime `p` lies in
`σ(M*) ∪ τ₂(M*)`. The proof needs no keystone input: `p ∉ σ(M*)` forces `r_p(M*) ≤ 2`
(via `α ⊆ σ`), and `r_p(M*) = 1` would make a Sylow `p` of `M*` cyclic with `X`
characteristic in it, so `N_G(P) ≤ N_G(X) ≤ M*` and `p ∈ σ(M*)`, a contradiction. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.prime_mem_sigma_or_tau2

/-! ### BG §12: Lemma 12.17 (`Msigma_E_relations`) — unconditional

`C_{M_σ}(E) ⊆ M_σ'` and `⁅M_σ, E⁆ = M_σ`. Both are Lemma 6.3(a) applied inside `↥M`
(`M_σ` a normal Hall subgroup with complement `E`, `M_σ ⊆ M'`) and transported to `G` along
`M.subtype`: the first conclusion gives `⁅M_σ, E⁆ = M_σ`, the second (coprime split) gives
`C_{M_σ}(E) ⊆ M_σ'`. No keystone input. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.Msigma_E_relations

/-! ### BG §12: Lemma 12.17 third clause (`Msigma_inf_conj_isBetaCompl`) — unconditional

`M_σ ∩ M^g` is a `β(M)′`-group for `g ∉ M`.  For each prime `p`, a rank-one `X ≤ M_σ ∩ M^g`
of order `p` has `C_G(X) ⊄ M` (Theorem 10.1(b)), so `ℳ(C_G(X)) ≠ {M}`, and the contrapositive
of Corollary 12.14 gives `p ∉ β(M)`.  Consumed by Proposition 14.2(g). -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.Msigma_inf_conj_isBetaCompl

/-! ### BG §12: Lemma 12.17 third clause — σ-uniqueness core + TI part — unconditional

`centralizer_not_le_of_isPGroup_le_Msigma_inf_conj`: for a nontrivial `p`-subgroup
`X ≤ M_σ ∩ M^g` (`g ∉ M`, `p ∈ σ(M)`), `C_G(X) ⊄ M` (Theorem 10.1(b) σ-fusion transitivity).
`Msigma_inf_conj_inf_derived_eq_bot`: `M_σ ∩ M^g ⊓ M_σ' = 1` (the TI part; a nontrivial element
yields a rank-one `X ≤ M_σ'`, and Corollary 12.14's `Or.inr` disjunct forces `C_G(X) ≤ M`). -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.centralizer_not_le_of_isPGroup_le_Msigma_inf_conj
#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.Msigma_inf_conj_inf_derived_eq_bot

/-! ### BG §12: Corollary 12.4 (`norm_noncyclic_sigma`) — unconditional

A noncyclic `σ(M)`-`p`-subgroup `P ≤ M` has `N_G(P) ≤ M`.  A rank-two elementary abelian
`A ≤ P` (`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`) has `C_G(A) ≤ M`
(`centralizer_le_of_elemAb_rank_two`, Prop 12.4(a)), and `σ`-fusion control
(`fusion_control_of_mem_sigma`, `N_G(P) = (N_G(P) ⊓ M)·C_G(P)`) plus `C_G(P) ≤ C_G(A) ≤ M` gives
`N_G(P) ≤ M`.  The `σ`-uniqueness input to BG Lemma `sigma_compl_embedding` / Theorem D(2). -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.norm_noncyclic_sigma

/-! ### BG §12: Lemma 12.19 (`derivedE_centralizes_betaComplement`) — unconditional

`E'` centralizes a Hall `β(M)'`-subgroup of `M_σ`. The proof consumes Corollary 10.9(a)
(`beta_complement_centralizes`, per-prime Sylow centralization) and Prop 1.5(c)
(`aInvariant_hall_conj`) to coordinate the per-Sylow data into one `E'`-centralized Hall via the
abstract `exists_hall_actsTrivially_of_forall_sylow`. Formerly in the §10 keystone island via
Cor 10.9(a); unconditional since the 2026-06-11 de-axiomatization. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.derivedE_centralizes_betaComplement

/-! ### BG §12: Lemma 12.18 (`tau1_Malpha_interaction`) — unconditional

For `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(M)`, and a nontrivial `P`-invariant `q`-subgroup `Q ≤ M` with
`C_Q(P) = 1` and `ℳ(N_G(Q)) ≠ {M}`: (a) if `M_α ≠ 1` and `q ∉ α(M)` then `C_{M_α}(P) ≠ 1` and
`C_{M_α}(PQ) = 1`; (b) if `Q` is moreover a Sylow `q`-subgroup of `M` then `α(M) = β(M)` and
the conclusions of (a) hold. Part (b) consumes Corollary 10.9(a)(2) — unconditional since the
2026-06-11 de-axiomatization — together with the Uniqueness Theorem 9.6 and the degenerate
Theorem 10.2(d) (`isNilpotent_derived_of_Malpha_eq_bot`). -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.isNilpotent_derived_of_Malpha_eq_bot

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.tau1_Malpha_centralizer_PQ_eq_bot

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.tau1_Malpha_interaction

/-! ### BG Lemma 12.3 + Hypothesis 11.1 constructor (`S12_ExceptionalBridge`)

**BG Lemma 12.3** (mmd L3101): for `M* ∈ ℳ − {M}`, `A ∈ ℰ_p²(M ∩ M*)`, `A₀ ∈ ℰ¹(A)` with
`N_G(A₀) ⊆ M*`: (a) if `p ∉ σ(M)` then `A` centralizes `M_σ ∩ M*`
(`elemAb_centralizes_Msigma_meet`); (b) if `p ∈ σ(M) − α(M)` then `A` centralizes
`M_α ∩ M*` (`elemAb_centralizes_Malpha_meet`). Root of the §12 τ₂-cascade. Consumes
Theorem 11.7 (`MsigmaA_normal`) through the new Hypothesis 11.1 constructor
(`Hypothesis111.of_normalizer_le`), Corollary 11.4, Theorem 10.1(b), Lemma 10.12(a), and
the Theorem 10.2(d) Sylow closure — all unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S11.Hypothesis111.of_normalizer_le

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.not_conj_of_mem_sigma_of_normalizer_le

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.normalizer_Malpha_sup_sylow_of_mem_sigma

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.commutator_le_inf_Msigma_of_normalizer_le

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.elemAb_centralizes_Msigma_meet

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.elemAb_centralizes_Malpha_meet

/-! ### BG Proposition 12.4 (`S12_ExceptionalBridge`)

**BG Proposition 12.4** (mmd L3125): for `A ∈ ℰ_p²(M)`: (a) `C_G(A) ≤ M`
(`centralizer_le_of_elemAb_rank_two`); (b) if `ℳ(N_G(A₀)) ≠ {M}` for every
`A₀ ∈ ℰ¹(A)`, then `p ∈ σ(M)`, `M_α = 1`, `M_σ` is nilpotent, and `C_G(A) ≤ M`
(`mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne`). Consumes Lemma 12.3, the
Uniqueness Theorem (9.6), Proposition 1.16(2) (`cocyclicFixedByClosure`),
Proposition 10.11(b), Theorem 10.2 (Hall structure + BB4), and `Ω₁(Z(P))`
(`omega1CenterInG`) — all unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.centralizer_le_of_elemAb_rank_two

/-! ### BG Theorem 12.5 (`S12_Theorem125`)

**BG Theorem 12.5** (mmd L3159): for `p ∈ τ₂(M)` and `A ∈ ℰ_p²(M)`: (a) `M_σ` is
nilpotent; (b) `M` has abelian Sylow `p`-subgroups and a Sylow `p`-subgroup `P ⊇ A` with
`N_G(P) ⊄ M`; (c) `M_σ A ⊴ M`; (d) `C_{M_σ}(A) = 1`; (e) `M_σ ∩ M* = 1` for every
`M* ∈ ℳ(A) − {M}`; (f) some `A₁ ∈ ℰ¹(A)` has `C_{M_σ}(A₁) = 1`
(`Msigma_nilpotent_of_tau2`). The τ₂-case gateway: Proposition 12.4(b) supplies
Hypothesis 11.1, then Theorems 11.3/11.5/11.7, Corollary 11.6, and Lemma 12.3(a) give
the conclusions — all unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.Msigma_nilpotent_of_tau2

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.omega1_eq_of_tau2

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.not_conj_of_mem_tau1_union_tau3_of_normalizer_le

/-! ### BG Corollary 12.6(a)(b) (`S12_Corollary126`)

**BG Corollary 12.6(a)(b)** (mmd L3179): for `p ∈ τ₂(M)` and `A ∈ ℰ_p²(E)`:
(a) `A ⊴ E` (`E_le_normalizer_of_tau2`) and every line of `E` lies in `A`
(`line_le_of_le_E_of_tau2`); (b) `C_G(A) ≤ E`, `N_M(A) = E`, `N_G(A) ⊄ M`
(`centralizer_le_E_of_tau2`). Consume Theorem 12.5(b)(c)(d), `omega1_eq_of_tau2`, and
Proposition 12.4(a) — all unconditional. (c) `ℳ(C_G(X)) = {M}` for lines with nontrivial
`M_σ`-centralizer, (d)(e) `C_{M_σ}(x) = 1` for `(τ₁∪τ₃)`-elements of `E₃` / `C_{E₁}(A)`
(via Lemma 12.2(b) and Theorem 12.5(e)), (f) `M_σ ∩ M*_σ = 1` for non-conjugate `M*`
(Lemma 10.12(b)); assembled as `elemAb_normal_in_E_of_tau2`. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.E_le_normalizer_of_tau2

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.line_le_of_le_E_of_tau2

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.centralizer_le_E_of_tau2

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.maximalContaining_centralizer_line_eq_singleton

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.Msigma_inf_centralizer_eq_bot_of_le_centralizer

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.elemAb_normal_in_E_of_tau2

/-! ### BG Theorem 12.7 (`S12_Theorem127` / `S12_Theorem127d`)

**BG Theorem 12.7** (mmd L3201-3251): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `G` with nonabelian
Sylow `p`-subgroups. (a) `p` is the only prime in `τ₂(M)`
(`tau2_prime_eq_of_nonabelianSylow`; faithful 化 = 素数限定形); (b)(c) the canonical
line `A₀ = A ⊓ C_G(M_σ)` of order `p` with the dichotomy for other lines
(`exists_canonical_line_of_nonabelianSylow`, via Lemma 10.13) and
`F(M) = M_σ × A₀` (`fitting_eq_sup_of_canonical_line`); (d) the complement `E₀` of
`A₀` in `E` (`exists_complement_of_canonical_line`, via Maschke on `E₂/℧¹(E₂)`);
(e) `π(C_{E₀}(x)) ⊆ τ₁(M)` (`primeFactors_centralizer_le_tau1_of_disjoint`);
assembled as `tau2_singleton_of_nonabelianSylow`. All unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.tau2_prime_eq_of_nonabelianSylow

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_canonical_line_of_nonabelianSylow

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.fitting_eq_sup_of_canonical_line

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_complement_of_canonical_line

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.primeFactors_centralizer_le_tau1_of_disjoint

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.tau2_singleton_of_nonabelianSylow

/-! ### BG Lemma 12.8(a)(b)(c) (`S12_Lemma128`)

**BG Lemma 12.8** (mmd L3253), abelian-Sylow case, parts (a)(b)(c): with `S` an abelian
Sylow `p`-subgroup of `G` containing `A ∈ ℰ_p²(E)`, every `τ₂`-prime has abelian Sylow
subgroups in `G` (12.7(a) contrapositive), each contributing its full `G`-Sylow inside
`E`; the chain `S ⊆ N_G(S)' ⊆ F(E) ⊆ C_G(S) ⊆ E` (`sylow_chain_of_abelianSylow`, via
Corollary 10.7(a) `sylow_le_derivedInG_normalizer`, the Fitting chain through `N_G(A)`
`derivedInG_normalizer_elemAb_le_fittingInG` [Theorem 4.20(a)], and the
`O_q × O_q'`-decomposition `sylow_eq_opiCore_fittingInG_of_tau2`); and
`E₂ = O_{τ₂}(F(E))` is abelian, normal in `E`, and Hall `τ₂(M)` in `G`
(`E2_abelian_normal_hall_of_abelianSylow`). All unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sylow_le_derivedInG_normalizer

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.derivedInG_normalizer_elemAb_le_fittingInG

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sylow_eq_opiCore_fittingInG_of_tau2

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.E2_abelian_normal_hall_of_abelianSylow

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sylow_chain_of_abelianSylow

/-! ### BG Lemma 12.8(d)(e)(f) + assembly (`S12_Lemma128d`)

(d) the normalizer chain `N_G(A) = N_G(S) = N_G(E₂) = N_G(E₂E₃) = N_G(F(E))`
(`normalizer_chain_of_abelianSylow`; characteristic chain
`A = Ω₁(S)`, `S = O_p(E₂)`, `E₂ = O_{τ₂}(E₂E₃)`, `E₂E₃ = O_{τ₂∪τ₃}(F(E))`, closed up by
`F(N_G(A)) = F(C_G(A)) = F(E)`); (e) lines of `E₁` with trivial `M_σ`-centralizer are
central in `E` (`central_line_of_abelianSylow`; `⁅E₂E₃, X⁆ ⊴ N_G(S)` against
Proposition 10.11(d) and `N_G(S) ⊄ M`); (f) `C_S(X), ⁅S,X⁆ ⊴ N_G(S)`
(`relative_normality_of_abelianSylow`); assembled as `E2_abelian_of_abelianSylow`.
All unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.normalizer_chain_of_abelianSylow

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.central_line_of_abelianSylow

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.relative_normality_of_abelianSylow

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.E2_abelian_of_abelianSylow

/-! ### BG Corollary 12.9 (`S12_Corollary129`)

For `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `q ∈ τ₁(M)`, `Q ∈ ℰ_q¹(E)` with `C_{M_σ}(Q) = 1` and
`[A,Q] ≠ 1`: (a) `A₀ = [A,Q] ∈ ℰ¹(A)` equals `C_A(M_σ)` and is normal in `M`
(Proposition 10.11(d) at `K := A`, `P := Q`, sharpened by the 10.11(b) rank bound);
(b) `A₀` is not conjugate to `A₁ = C_A(Q)` in `G` (cyclic Sylow `q` of `M` forces
`Q ≤ C_G(A₀)`, collapsing the coprime decomposition `A = A₁ × A₀`);
(c) `A₁ ∈ ℰ¹(A)` and `C_G(A₁) ⊄ M` (Theorem 12.7(c) after excluding the abelian-Sylow
case via Lemma 12.8(e) and a Hall-`τ₁` conjugation). Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.commutator_decomp_of_tau1_action

/-! ### BG Corollary 12.10 (`S12_Corollary1210`)

(a) every nilpotent `σ(M)'`-subgroup of `M` is abelian (the supporting
`sylow_isMulCommutative_of_sigma_compl` gives abelian Sylow `r`-subgroups of `M` for all
`r ∉ σ(M)` — cyclic for `r ∈ τ₁ ∪ τ₃` by the rank-1 bound, Theorem 12.5(b) for `r ∈ τ₂` —
and `isMulCommutative_of_isNilpotent_of_forall_sylow` assembles the Sylow direct product);
(b) `E₂` and `E' = derivedInG E` are abelian; (c) `E₂E₃ ≤ C_E(A) ⊴ E` with
`π(E/C_E(A)) ⊆ τ₁(M)`; (d) noncyclic `p`-subgroups for `p ∈ σ(M)` satisfy `N_G(P) ≤ M`
(Theorem 10.1(c) + Proposition 12.4(a)); (e) `τ₂`-elements `x` with `C_{M_σ}(x) ≠ 1` have
`ℳ(C_G(x)) = {M}` (Hall-conjugate into `E₂`, then Theorem 12.5(e)). Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.isMulCommutative_of_isNilpotent_of_forall_sylow

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sylow_isMulCommutative_of_sigma_compl

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.nilpotent_sigmaComplement_abelian

/-! ### BG §12 `SubgroupESetup` existence (`S12_Lemma1211`)

The §12-preamble existence statement: every `M ∈ ℳ` carries a `SubgroupESetup`
(Schur–Zassenhaus complement `E` to `M_σ`, Hall `τᵢ` pieces with `E₁E₂` a subgroup via
the Hall-in-Hall transfer `isHallSubgroup_of_isHallSubgroup_of_le`). Required to apply
the §12 results on the `M*` side in Lemma 12.11 and later. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.isHallSubgroup_of_isHallSubgroup_of_le

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_subgroupESetup

/-! ### BG Lemma 12.11(a)(b) (`S12_Lemma1211`)

(a) the primes of `τ₂(M)` lie in `σ(M*) − β(M*)` for `M* ∈ ℳ(N_G(A))` (stated for primes —
the repo `tau2` does not exclude composites, same faithfulness correction as 12.3/12.10(c));
(b) `π(E/C_E(A)) ⊆ τ₁(M*) ∪ τ₂(M*)`, via the normal `p`-complement of `M*'`
(Lemma 10.8(c)) instead of the nilpotent quotient `M*'/M*_β`. Supporting engine:
`exists_conj_smul_le_hallPiece` (parametric Hall push-in extracted from 12.10(e)).
Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_conj_smul_le_hallPiece

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.mem_sigma_of_tau2_of_mem_maximalContaining

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.tau2_prime_mem_sigma_diff_beta

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.index_primeFactors_subset_tau1_union_tau2

/-! ### BG Lemma 12.11(c) + assembly (`S12_Lemma1211`)

(c) `q ∈ π(E/C_E(A)) ∩ π(C_E(A))` forces `q ∈ τ₂(M*)`, a Sylow `p`-subgroup of `G` normal
in `M*` (`M*_σ` nilpotent by 12.5(a)), and an abelian Sylow `q`-subgroup of `G` inside `M*`
(12.8(c) chain; the nonabelian case is killed by the 12.7(d) complement against the
no-complement property of `Ω₁` of the cyclic `q`-Sylow). The maximal `M** ∈ ℳ(N_G(Q₀))`
is identified with `M*` via 12.6(f) + Theorem 10.1(b). `tau2_transfer_to_maximal` bundles
(a)(b)(c) (scaffold moved from `S12_E`, (a)-conjunct prime-restricted). Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.tau2_normalSylow_abelianSylow_of_mem_index_card

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.tau2_transfer_to_maximal

/-! ### BG Theorem 12.12 prep: Proposition 3.9 (`S12_Theorem1212`)

Gorenstein 5.3.14: a finite `p`-group (`p` odd) acting coprimely and fixed-point-freely on a
nontrivial finite group is cyclic. Via an elementary abelian `p²`-subgroup `B` (when not cyclic),
Isaacs 6.21 forces `⟨C_H(b) | b ∈ B^#⟩ = H`, contradicting fixed-point-freeness. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.isCyclic_of_coprime_fpf_pgroup_action

/-! ### BG Theorem 12.12: Frobenius packaging + case `τ₂(M) = ∅` (`S12_Theorem1212`)

`isFrobeniusGroup_of_regular`: a nontrivial complement `E₀ ≤ E` acting regularly on `M_σ`
(`M_σ ⊓ C_G(a) = 1` for `a ∈ E₀#`) makes `M_σ E₀` a Frobenius group with kernel `M_σ`
(`M_σ ⊴ M`, `M_σ ⊓ E₀ = 1` from the `SubgroupESetup`, `M_σ ≠ 1` by Theorem 10.2(e)).
`frobFact_of_regular_all`: when `E = E₁E₃` (the regularity covers all of `E`), `A₀ = 1` and
`E₀ = E` discharge both conclusions. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.isFrobeniusGroup_of_regular

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.frobFact_of_regular_all

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exponent_eq_of_forall_factorization_le

/-! ### BG Theorem 12.12: Case 2 (nonabelian Sylow `p`) (`S12_Theorem1212`)

Shared infrastructure (`eq_sup_inf_of_le_normalizer` = Dedekind decomposition under a normalizer
condition; `inf_centralizer_bot_symm` = symmetry of centralizer-disjointness) and the exponent
machinery (`factorization_exponent_le_of_sylow` = the `p`-part of `exp E` lives in a Sylow;
`exists_orderOf_eq_rpow_in_complement` / `exists_factorization_le_at_prime` realise the `r`-part
of `exp E` inside the complement `E₀` for `r ≠ p` resp. `r = p`). The capstone
`frobFact_of_nonabelianSylow` assembles `FrobFactConclusion M E` for the nonabelian-Sylow case
via the canonical line `A₀` (Theorem 12.7) and its complement `E₀`. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.eq_sup_inf_of_le_normalizer

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.inf_centralizer_bot_symm

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.factorization_exponent_le_of_sylow

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_orderOf_eq_rpow_in_complement

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_factorization_le_at_prime

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.frobFact_of_nonabelianSylow

/-! ### BG Theorem 12.12: Case 3 (abelian Sylow `p`) building blocks (`S12_Theorem1212b`)

`sylow_maximal_in_M_of_le`: a Sylow `p`-subgroup of `G` inside `M` is also Sylow in `M`.
`inf_centralizer_line_eq_bot_of_invariant` (key fact, BG L3345-3347): since `N_G(S) ⊄ M`, an
`N_G(S)`-invariant line `L ≤ S` has `C_{M_σ}(L) = 1` (`L ≤ Ω₁(S) = A`, then Corollary 12.6(c)
forces `N_G(L) ⊆ M ⊇ N_G(S)`, contradiction). Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sylow_maximal_in_M_of_le

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.inf_centralizer_line_eq_bot_of_invariant

/-! ### BG Theorem 12.12: Case 3 cyclic-`Z` regularity bridge (`S12_Theorem1212b`)

`line_le_zpowers_in_cyclic`: in a finite cyclic `p`-group the order-`p` subgroup is the unique
minimal one, contained in `⟨a⟩` for every `a ≠ 1` (generator + `orderOf_pow` gcd + Bézout).
`inf_centralizer_eq_bot_of_line_le_cyclic`: transfers `N ⊓ C_G(L) = 1` (for a line `L ≤ Z`,
`Z` cyclic) to `N ⊓ C_G(a) = 1` for all `a ∈ Z#`, since `L ≤ ⟨a⟩` gives `C_G(a) ≤ C_G(L)`.
This connects the key fact to the per-element Frobenius regularity. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.line_le_zpowers_in_cyclic

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.inf_centralizer_eq_bot_of_line_le_cyclic

/-! ### BG Theorem 12.12: Case 3 φ̄ quotient action wrapper (`S12_Theorem1212b`)

`conjActionHom_ker`: the kernel of the conjugation action `Q →* MulAut S` (`Q ≤ N_G(S)`) is
`C_Q(S) = C_G(S) ⊓ Q`, via `Subgroup.normalizerMonoidHom_ker`.
`isCyclic_quotient_of_conjugation_fpf`: a `q`-group `Q ≤ N_G(S)` acting on a `p`-group `S ≠ 1`
(`p ≠ q`) fixed-point-freely outside its kernel `C_Q(S)` has cyclic quotient `Q ⧸ C_Q(S)`;
the lifted action is FPF, so Proposition 3.9 (`isCyclic_of_coprime_fpf_pgroup_action`) applies.
Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.conjActionHom_ker

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.isCyclic_quotient_of_conjugation_fpf

/-! ### BG Theorem 12.12: Case 3 back-half — rank-2 abelian split ⟹ factors cyclic
(`S12_Theorem1212b`)

`isCyclic_of_inf_eq_bot_of_pRank_le_two`: in a finite abelian `p`-group `T` (`p` odd) of
`p`-rank `≤ 2`, a subgroup `T₀` disjoint from a nontrivial `T₁` is cyclic (else `T₀ ⊇ B₀`
elem-ab order `p²`, with `y ∈ T₁` order `p` the join `B₀ ⊔ ⟨y⟩` is elem-ab order `p³`, so
`pRank T ≥ 3`). For `S = C_S(X) × [S,X]` in Case 3: both factors cyclic since `r(S) = 2`.
Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.isCyclic_of_inf_eq_bot_of_pRank_le_two

/-! ### BG Theorem 12.12: Case 3 back-half — exponent of internal product (`S12_Theorem1212b`)

`exponent_eq_of_sup_eq_top_of_exponent_dvd`: in a finite abelian `T = T₀ ⊔ T₁ = ⊤`, if
`exp(T₁) ∣ exp(T₀)` then `exp(T) = exp(T₀)` (each `g = a·b` factors, `ord g ∣ lcm(ord a, ord b)
∣ exp T₀`). For `Z` = the larger cyclic factor of `S = C_S(X) × [S,X]`: `exp(Z) = exp(S)`.
Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exponent_eq_of_sup_eq_top_of_exponent_dvd

/-! ### BG Theorem 12.12: Case 3 back-half — invariant cyclic `Z` acts regularly (`S12_Theorem1212b`)

`inf_centralizer_eq_bot_of_invariant_cyclic`: an `N_G(S)`-invariant nonidentity cyclic `Z ≤ S`
has `M_σ ⊓ C_G(z) = 1` for every `z ∈ Z#`. Its order-`p` subgroup `L = Ω₁(Z)` is a line
(`|Ω₁(Z)| = p` via cyclic exponent), `N_G(S)`-invariant (`Ω₁` characteristic in `Z`), so the key
fact `inf_centralizer_line_eq_bot_of_invariant` gives `M_σ ⊓ C_G(L) = 1` and the cyclic bridge
`inf_centralizer_eq_bot_of_line_le_cyclic` spreads it to all of `Z#`. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.inf_centralizer_eq_bot_of_invariant_cyclic

/-! ### BG Theorem 12.12: Case 3 back-half — the `Z`-construction assembly (`S12_Theorem1212b`)

`isCyclic_of_le_of_inf_eq_bot_of_pRank_le_two` / `exponent_eq_of_le_of_sup_eq_of_exponent_dvd`:
`subgroupOf` casts of the two abstract back-half primitives to subgroups of `G` inside an abelian
Sylow `S`.
`exists_invariant_cyclic_sameExponent_regular`: in the abelian-Sylow regime, `X ≤ N_G(S)`
(coprime to `S`) with `1 ⊊ C_S(X) ⊊ S` yields a cyclic `N_G(S)`-invariant `Z ≤ S` with
`exp(Z) = exp(S)` acting regularly on `M_σ`. `S = C_S(X) × [S,X]` (`fitting_coprime_abelian_-`
`decomp`), both factors cyclic (`r(S) = 2`) and invariant (Lemma 12.8(f)); `Z` is the larger.
Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.isCyclic_of_le_of_inf_eq_bot_of_pRank_le_two

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exponent_eq_of_le_of_sup_eq_of_exponent_dvd

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_invariant_cyclic_sameExponent_regular

/-! ### BG Theorem 12.12: Case 3 front-half — `Ω₁`-rank reasoning (`S12_Theorem1212b`)

`omega_le_of_ne_bot_in_cyclic`: in a finite cyclic `q`-group the order-`q` subgroup `Ω₁` lies in
every nontrivial subgroup (`|Ω₁| = q` + `line_le_zpowers_in_cyclic`).
`pRank_le_one_of_cyclic_quotient`: the `r(Q) = 1` side of the Case 3 rank contradiction — a finite
`q`-group `Q` with cyclic quotient `Q ⧸ Q₀` and `Q₀ ⊊ Q₁ ≤ Q` (`Q₁` cyclic) has `pRank Q q ≤ 1`,
since `Ω₁(Q) ≤ Q₁` (via `Ω₁(Q ⧸ Q₀) ≤ Q₁ ⧸ Q₀`) and every elem-ab `B ≤ Ω₁(Q) ≤ Q₁` is cyclic
of order `≤ q`. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.omega_le_of_ne_bot_in_cyclic

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.pRank_le_one_of_cyclic_quotient

/-! ### BG Theorem 12.12: Case 3 front-half setup — `E ≤ N_G(S)` (`S12_Theorem1212b`)

`E_le_normalizer_sylow_of_abelianSylow`: in the abelian-Sylow regime `E ≤ N_G(S)`. `S ≤ F(E)`
(Sylow chain), `S` is the Sylow `p`-subgroup of the nilpotent `F(E)` hence characteristic in it,
and `E` normalizes `F(E)`, so `E ≤ N_G(F(E)) ≤ N_G(S)`. Lets the Sylow `q`-subgroups of `E` sit
inside `N_G(S)` for the front-half rank argument. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.E_le_normalizer_sylow_of_abelianSylow

/-! ### BG Proposition 1.6(e): `Ω₁`-centralizing coprime action is trivial (`S12_Theorem1212b`)

`centralizer_le_of_omega1_le_centralizer`: an abelian `p`-group `S` with a coprime operator
`Q ≤ N_G(S)` that centralizes `Ω₁(S)` is centralized by `Q` entirely. Via the coprime split
`S = C_S(Q) × [S, Q]` (`fitting_coprime_abelian_decomp`): a nontrivial `[S, Q]` would contain an
order-`p` element of `Ω₁(S) ⊆ C_S(Q)`, contradicting `C_S(Q) ⊓ [S, Q] = 1`. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.centralizer_le_of_omega1_le_centralizer

/-! ### BG Theorem 12.12: Case 3 front-half — the `r_q = 2` side (`S12_Theorem1212b`)

`sylow_eq_of_le_normalizer`: two Sylow `p`-subgroups, one normalizing the other, coincide (`P`
is the unique Sylow `p` of `N_G(P)`).
`pRank_normalizer_eq_two_of_index_card`: in the abelian-Sylow regime, `q ∣ [E : C_E(A)]` and
`q ∣ |C_E(A)|` force `r_q(N_G(S)) = 2`. Lemma 12.11(c) gives `M* ∈ ℳ(N_G(A))` with `q ∈ τ₂(M*)`
and a Sylow `p`-subgroup `P` of `G` normal in `M*`; `S ≤ N_G(S) = N_G(A) ≤ M* ≤ N_G(P)` and
`S = P` make `M* = N_G(S)`, so `pRank (N_G(S)) q = pRank M* q = 2`. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sylow_eq_of_le_normalizer

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.pRank_normalizer_eq_two_of_index_card

/-! ### Prime divides index of normal subgroup missing a Sylow (`S12_Theorem1212b`)

`prime_dvd_index_of_sylow_not_le_of_normal`: if `H ⊴ K` does not contain the Sylow `q`-subgroup
`P`, then `q ∣ [K : H]` (the image of `P` in `K ⧸ H` is a nontrivial `q`-group). Front-half
setup tool: feeds `q ∈ π(E/C_E(A))` from `Q₁ ⊄ C_E(A)` with `C_E(A) ⊴ E`. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.prime_dvd_index_of_sylow_not_le_of_normal

/-! ### BG Theorem 12.12: Case 3 front-half — setup + `X` existence (`S12_Theorem1212b`)

`exists_sylow_tau1_cyclic_notCentralizing`: in the abelian-Sylow regime with the regularity
hypothesis, `C_E(S) ≠ E` yields a prime `q ≠ p` and a cyclic Sylow `q`-subgroup `Q₁` of `E` with
`q ∈ τ₁(M)`, `Q₁ ⊄ C(S)`, and `q ∈ π(E/C_E(A)) ∩ π(C_E(A))` (the data for the `r_q = 2` lemma).
`exists_partial_centralizer_of_abelianSylow`: hence some `X ≤ N_G(S)` has `1 ⊊ C_S(X) ⊊ S` —
otherwise `Q ⧸ C_Q(S)` is cyclic (`pRank Q q ≤ 1`) yet `pRank Q q = r_q(N_G(S)) = 2`. Feeds the
`Z`-construction `exists_invariant_cyclic_sameExponent_regular`. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_sylow_tau1_cyclic_notCentralizing

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_partial_centralizer_of_abelianSylow

/-! ### Agemo of an abelian group is the set of `pⁿ`-th powers (`S12_Theorem1212b`)

`agemo_eq_range_powMonoidHom` / `mem_agemo_iff_of_comm`: in a commutative group `℧ⁿ(H)` equals
the range of the `pⁿ`-th power map, so `x ∈ ℧ⁿ(H) ↔ ∃ y, x = y^(pⁿ)`. Tool for the Case 3
`C_E(S) = E` branch (`Z = ⟨s⟩` with `Ωₐ₋₁(S) = ⟨s^{p^{a-1}}⟩` the good line). Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.agemo_eq_range_powMonoidHom

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.mem_agemo_iff_of_comm

/-! ### BG Theorem 12.12: Case 3 — the `C_E(S) = E` branch (`S12_Theorem1212b`)

`exists_generator_of_card_prime`: a subgroup of order `p` is `⟨w⟩` for any nonidentity `w`.
`exists_cyclic_Enormal_regular_of_CES_eq`: in the abelian-Sylow regime with the regularity
hypothesis, `C_E(S) = E` yields a cyclic `Z ≤ S` of exponent `exp(S)`, normalized by `E`, acting
regularly on `M_σ`. Built from a good line `L = ⟨w⟩ ≤ ℧^{a-1}(S)` (`℧^{a-1}(S) = A` → Theorem
12.5(f); else `℧^{a-1}(S)` is a characteristic line via the key fact) with `w = s^{p^{a-1}}`,
`Z = ⟨s⟩`. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_generator_of_card_prime

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_cyclic_Enormal_regular_of_CES_eq

/-! ### BG Theorem 12.12: Case 3 per-prime `Z`-construction (both branches) (`S12_Theorem1212b`)

`exists_cyclic_Enormal_regular_of_abelianSylow`: in the abelian-Sylow regime with the regularity
hypothesis, `S` has a cyclic `Z ≤ S` of exponent `exp(S)`, normalized by `E`, regular on `M_σ`.
Splits on `C_E(S) = E`: `= E` uses the agemo construction; `≠ E` produces `X` (front-half) then the
invariant `Z` (back-half). Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_cyclic_Enormal_regular_of_abelianSylow

/-! ### Frobenius complement: prime-order regularity propagates (`S12_Theorem1212b`)

`inf_centralizer_eq_bot_of_forall_prime_order`: if every prime-order element of `H` acts
fixed-point-freely on `N`, so does every nonidentity element (`C(h) ⊆ C(h^{|h|/r})` for a prime
`r ∣ |h|`). The reduction for "`E₀ = E₁E₃·∏Z_p` is a Frobenius complement". Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.inf_centralizer_eq_bot_of_forall_prime_order

/-! ### BG Theorem 12.12: three-case assembly building blocks (`S12_Theorem1212c`)

`exists_regular_cyclic_of_mem_tau2`: per-prime `Z_p` extraction for `p ∈ τ₂(M)` in the abelian
Sylow case — a cyclic `p`-subgroup `Z ≤ E`, normalized by `E`, of the same exponent as a Sylow
`p`-subgroup `S ≤ E`, regular on `M_σ` (wires `exists_elemAb_rank_two_le_E_of_tau2`, the Sylow
extension, `sylow_chain_of_abelianSylow` giving `S ≤ E`, and the per-prime capstone). Unconditional.
`isPiSubgroup_le_of_normal_isHall`: a `π`-subgroup is contained in any *normal* Hall `π`-subgroup
(companion to `Subgroup.IsPiGroup.normal_le_hall`). `frobFact_partA_of_abelianSylow`: part (a) of
Theorem 12.12 in the abelian-Sylow case — `A₀ = E₂` is abelian normal with `C_E(x) ⊆ E₂` for
`x ∈ M_σ#` (`C_E(x)` is a `τ₂`-group by `hreg`, then in the normal Hall `E₂`). Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_regular_cyclic_of_mem_tau2

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.isPiSubgroup_le_of_normal_isHall

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.frobFact_partA_of_abelianSylow

/-! `⨆_{p ∈ T} Z_p` internal direct product (for the `E₀ = ∏ Z_p` aggregation, part (b)):
`le_normalizer_finsetSup` (`H` normalizes each `Z p` ⟹ normalizes `T.sup Z`),
`card_finsetSup_eq_prod` (`|T.sup Z| = ∏ |Z p|` for a `Finset` of primes, `Z p` a normalized
`p`-group — via `card_sup_eq_mul_of_le_normalizer_of_disjoint` + coprimality),
`mem_Z_of_orderOf_prime_mem` (an element of `T.sup Z` of prime order `r ∈ T` lies in `Z r`, by the
`r'`-cofactor quotient-order argument). Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.le_normalizer_finsetSup

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.card_finsetSup_eq_prod

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.mem_Z_of_orderOf_prime_mem

/-! `exists_tau2_product`: the `τ₂`-product `ZZ = ∏_{p ∈ τ₂(M) ∩ π(E)} Z_p` for the abelian-Sylow
case — `≤ E`, nontrivial, `E`-normalized, a `τ₂(M)`-group, fully regular on `M_σ`, realizing the
`τ₂`-part of `exp(E)`. Bundles the per-prime choice (`exists_regular_cyclic_of_mem_tau2`) with the
direct-product lemmas (`card_finsetSup_eq_prod` / `mem_Z_of_orderOf_prime_mem`). Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_tau2_product

/-! **BG Theorem 12.12** (`frobenius_factorization_of_regular`, `frobFact_of_abelianSylow`): the
abelian-Sylow Case 3 aggregation `E₀ = ZZ ⊔ K` (`ZZ` the `τ₂`-product, `K` a Hall `τ₂'`-subgroup)
realizes `exp(E₀) = exp(E)` and is regular on `M_σ`, so `M_σ E₀` is a Frobenius group; with the
three-case glue this completes Theorem 12.12. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.frobFact_of_abelianSylow

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.frobenius_factorization_of_regular

/-! **BG Theorem 12.13** reduction (`S12_Theorem1213`): `mem_sigma_normalizer_le_of_two_maximals`
— a nonabelian `p`-subgroup `P ≤ M` (maximal) has `p ∈ σ(M)` (Cor 12.10(a) contrapositive: a
`σ'`-`p`-subgroup is nilpotent hence abelian) and `N_G(P) ⊆ M` (Cor 12.10(d), `P` noncyclic).
Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.mem_sigma_normalizer_le_of_two_maximals

/-! **BG Theorem 12.13** Heisenberg piece (`S12_Theorem1213`):
`exists_conj_eq_center_mul_of_expPExtraspecial` — in an exponent-`p` extraspecial group, the
conjugates of a noncentral `a₀` cover its central coset `Z(Q)·a₀`. The map `q ↦ ⁅q,a₀⁆` is a
homomorphism onto the order-`p` center (commutators central), nontrivial as `a₀ ∉ Z(Q)`, hence
surjective. The conjugacy half of the 12.13 line-conjugacy argument. Unconditional. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.exists_conj_eq_center_mul_of_expPExtraspecial

/-! **BG Theorem 12.13** (`S12_Theorem1213`, σ-side keystone): a nonabelian `p`-subgroup `P`
contained in two distinct maximals `M ≠ M⋆` is impossible — equivalently, any maximal `M`
containing a nonabelian Sylow-type `p`-subgroup is the *unique* maximal subgroup containing it
(`nonabelian_pgroup_isUniquelyMaximal`). Proof: `P` → Sylow of `M ∩ M⋆` → Sylow of `G` forces
`r(P) = 2`; Cor 10.7(b) extracts an exponent-`p` extraspecial `Q` (order `p³`); `Q/Z(Q)` acts
coprimely and noncyclically on `K = C_{Mα}(Z)`, so Prop 1.16 writes `K = ⟨C_K(Ā) | Ā cocyclic⟩`,
each generator centralized by a rank-2 `A ∈ ℰ²(Q)` hence inside `M⋆` by 12.4(a); with Cor 10.9(b)
+ Lem 6.5(b) this puts `N_M(Z) ⊆ M⋆`, and 12.4(b) produces `A₀, A₀⋆ ∈ ℰ¹(A) − {Z}` realizing
`M, M⋆`, contradicting line-conjugacy + ℳ-uniqueness. Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.nonabelian_pgroup_isUniquelyMaximal

/-! **BG Proposition 12.15** (`S12_Proposition1215`, σ-prime ↔ maximal interaction): for `q ∈ σ(M)`,
a nonidentity `q`-subgroup `X ⊆ M`, and `M⋆ ∈ ℳ(N_G(X)) − {M}`, with `S = Syl_q(M ∩ M⋆) ⊇ X`,
the five conclusions (`sigma_subgroup_maximal_interaction`): (a) `M⋆` not `G`-conjugate to `M`;
(b) `N_G(S) ⊆ M`; (c) `S` is the unique Sylow-`q` of `G` in `M⋆`; (d) if `q ∈ σ(M⋆)` then the
`M⋆=(M∩M⋆)M⋆_β` factorization, the prime-guarded τ₁-transfer `∀ r prime, r∈τ₁(M⋆) → r∈τ₁(M)∪α(M)`
(shared Sylow `Syl_r(M∩M⋆)` of both `M`, `M⋆` via the `M_β`/`M⋆_β` diamonds), and `M_β=M_α≠1`;
(e) if `q ∉ σ(M⋆)` then `q∈τ₂(M⋆)`, `π(M)∩σ(M⋆)⊆β(M⋆)`, and `M∩M⋆` is an `M⋆_σ`-complement.
The τ₁ inclusion is prime-restricted (BG's `τᵢ ⊆ π(M)` are sets of primes; the repo's `pRank`-based
`tau1` ranges over `ℕ`). Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sigma_subgroup_maximal_interaction

/-! **BG Corollary 12.14** (`S12_Corollary1214`, `maximalContaining_centralizer_eq_singleton`):
for `p ∈ σ(M)`, `X ∈ ℰ_p¹(M)`, and `p ∈ β(M)` or `X ⊆ M_σ'`, `ℳ(C_G(X)) = {M}`. Proof: `X ⊆ M_σ`
and a Sylow `p` `S ⊇ X` of `M_σ` (`= Sylow p` of `G`); a uniquely-maximal `U ≤ C_G(X) ∩ M`
suffices. If `r(C_P(X)) ≥ 3`, take `U = C_P(X)` (Uniqueness Theorem); else `p ∉ idealPrime`,
`X ⊆ S'` (Lemma 10.8(c) normal-`p`-complement), `r(S) ≤ 2` (Cor 5.4 + Thm 5.3(d)), Cor 10.7(b)
gives `S = P₁ * P₂` central product with `P₁` extraspecial, and `U = P₁` (nonabelian, `X ⊆ Z(P₁)`,
Theorem 12.13). Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.Cor1214.maximalContaining_centralizer_eq_singleton

/-! **BG Corollary 12.14, faithful form** (`S12_Corollary1214`,
`maximalContaining_centralizer_and_someSylow_eq_singleton`): strengthens the above to also conclude
`ℳ(S₀) = {M}` for some Sylow `p`-subgroup `S₀ ⊇ X` of `M_σ`, matching the textbook
`ℳ(C_G(X)) = ℳ(P) = {M}`. Same witness `U`: it satisfies `U ≤ S₀` in every branch
(`P₁ ≤ S₀`, resp. `C_P(X) ≤ S₀`), so threading `U ≤ S₀` through the unified engine yields the second
conjunct. Needed by BG Lemma 13.6 (issue 8002). Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch3.S12.Cor1214.maximalContaining_centralizer_and_someSylow_eq_singleton

/-! **BG Corollary 12.16** (`S12_Corollary1216`, σ-subgroup ↔ maximal interaction, `q`-group form):
for a nonidentity `q`-group `Y` (`q ∈ σ(M)`), every `p ∈ π(E) ∩ β(G)'`, and every `H ∈ ℳ(Y)` not
conjugate to `M`: (a) `r_p(N_H(Y)) ≤ 1` (`pRank_normalizer_le_one`); (b) if `p ∈ τ₁(M)` then
`p ∉ π(N_H(Y)')` (`not_mem_primeFactors_derived_of_tau1`). Proof: conjugate `Y` into `M_σ`, then in
the core either `N_G(Y) ⊆ M` (direct) or `M* ∈ ℳ(N_G(Y))` with `M* = (M ∩ M*)K` (Prop 12.15(d)/(e),
`K` a `p'`-group); a rank-2 `A ∈ ℰ_p²` forces `p ∈ τ₂(M)` + Thm 12.5(e) `M_σ ∩ M* = ⊥` (contra (a)),
and `deriv ≤ (M ∩ M*)'⊔K` is `p'` (for (b)). Lane G (S13_Lemma131) re-points to these. Fully
unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.Cor1216.pRank_normalizer_le_one
#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.Cor1216.not_mem_primeFactors_derived_of_tau1

/-! **BG Corollary 12.16** (general `σ(M)`-subgroup form, `S12_Corollary1216`): the `q`-group forms
above lift to an arbitrary nonidentity `σ(M)`-subgroup `Y` via a characteristic `q`-subgroup
`O_q(Y)` (`N_G(Y) ≤ N_G(O_q(Y))`, `pRank`/`derivedInG` monotone). These are what `S13_Lemma131` now
cites (replacing the former S12_E `sorry`'d forward-decls); fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sigma_subgroup_pRank_normalizer_le_one
#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sigma_subgroup_not_mem_primeFactors_derived_of_tau1

/-! **BG Corollary 12.16(a)**, *headline form* (`S12_Corollary1216`,
`sigma_subgroup_conj_into_Msigma_general`): a nonidentity `σ(M)`-subgroup `Y < ⊤` of `G` is
`G`-conjugate into `M_σ` (BG's `ℓ_σ ≤ 1` tool, mmd L3801). Proof: a characteristic `q`-subgroup
`X ⊆ Y` conjugates into `M_σ`; either `N_G(X) ⊆ M` (so `Y ⊆ M ⟹ Y ⊆ M_σ`) or `M* = (M ∩ M*)K`
(Prop 12.15) with `K` a `σ(M)'`-group, and `hall_D` pushes `Y` into `M ∩ M* ⊆ M`. The
`σ`-disjointness gate (Theorem 13.9, downstream) is a hypothesis `hσdisj` to avoid an import cycle;
§14 callers discharge it with `sigma_disjoint_of_nonconjugate`. Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S12.sigma_subgroup_conj_into_Msigma_general

/-! ### BG §14 (`S14_TypePCounting`) -/

/-! **Derived subgroup of a split extension** (`S14_TypePCounting`,
`commutator_eq_sup_commutator_of_isComplement'`): general group theory — if `N ⊴ H` has a
complement `E` and `N ≤ H'`, then `H' = N ⊔ ⁅E,E⁆`.  Used to reduce Theorem 14.7(h)
(`M' = M_σ ⊔ E'`, so `M'` complements `K` iff `E = K ⋉ E'` inside the `σ(M)'`-complement).
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.commutator_eq_sup_commutator_of_isComplement'

/-! **BG Lemma 14.1** (`S14_TypePCounting`): for `M ∈ 𝓜` and a prime
`p ∈ π(M) - (σ(M) ∪ κ(M))` with `A ∈ ℰ_p^{r_p(M)}(M)`, one has `|A| ≤ p²`,
`C_{M_σ}(A) = 1`, and `M_σ` is nilpotent.  The `r_p = 2` case is Theorem 12.5(a)(d);
the `r_p = 1` case uses `p ∉ κ(M)` and the fixed-point-free criterion of Theorem 3.7.
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.msigma_structure_of_notMem_sigma_kappa

/-! **BG Lemma 14.5(b)** (`S14_TypePCounting`): for nonconjugate maximal `M`, `N`, the
conjugacy saturations `𝒞_G(M_σ^#)`, `𝒞_G(N_σ^#)` are disjoint.  Proved citing Theorem 13.9
(`sigma_disjoint_of_nonconjugate`), which landed in §13 (Lane F) on 2026-06-15, so this is now
fully unconditional and axiom-clean.  (Lean uses the `M_σ^#` restriction of BG's `M̃`, which
makes 13.9 alone sufficient — no `R(x)` / `M̃` machinery needed.) -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaConjugacy_disjoint_of_nonconjugate

/-! **BG Lemma 14.5(a)** (`S14_TypePCounting`, `xRsub_disjoint`): for distinct σ-length-one
`x`, `y`, the cosets `x R(x)`, `y R(y)` are disjoint.  Proven via the σ-class partition + the
two-block decomposition (`isPiElement_mul_unique`) + Theorem 14.4(e); no §15/§16 needed. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.xRsub_disjoint
-- **BG Lemma 14.5(b)** (faithful `M̃` form): nonconjugate `M₁`, `M₂` have disjoint `M̃₁`, `M̃₂`.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.Mtilde_disjoint

/-! **BG Lemma 14.5(c), Part A** (`S14_TypePCounting`, `sigmaSaturation_Rsub_count`): the double
count `∑_{x ∈ 𝒞_G(M_σ^#)} |R(x)| = |M_σ^#|·[G : M]`, counting incidence pairs `(x, Mᵍ)` two ways
via sharp transitivity (Theorem 14.4). -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaSaturation_Rsub_count
/-! **BG Lemma 14.5(c)** (`S14_TypePCounting`, `sigmaConjugacySaturation_Mtilde_ncard`):
`|𝒞_G(M̃)| = (|M_σ| − 1)·[G : M]`.  Part B (the disjoint cover `𝒞_G(M̃) = ⊔ₓ x R(x)` via the
`R`-equivariance `Rsub_conj`) combined with Part A.  The type-`P` counting bound for Theorem 14.7. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaConjugacySaturation_Mtilde_ncard

/-! **BG Lemma 14.11** (`S14_TypePCounting`, `exists_maximal_of_typeF_notMem_fitting`): for
`M ∈ 𝓜_F`, `E` an `M_σ`-complement, `Q ∈ ℰ_q¹(E)` with `Q ⊄ F(E)`, there is `M* ∈ 𝓜` with either
`q ∈ τ₂(M*) ∧ 𝓜(C_G(Q)) = {M*}` or `q ∈ κ(M*) ∧ M* ∈ 𝓜_{P₁}`.  Sorry-free + axiom-clean.  The
supporting `exists_typeF_complement_cyclic_commutator` (cyclic-commutator bundle with `C_{K'}(Q)=1`)
and `exists_elemAb_rank_two_le_E_containing_line` (the A-choice) are registered below. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_maximal_of_typeF_notMem_fitting
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_typeF_complement_cyclic_commutator
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_elemAb_rank_two_le_E_containing_line

/-! **σ-decomposition keystone** (`S14_TypePCounting`, `length_one_of_isPiElement_sigma`):
a nonidentity `σ(M)`-element `x` has `ℓ_σ(x) = 1`.  Existence half of the σ-decomposition (BG §1):
`⟨x⟩` is conjugate into `M_σ` (Cor 12.16(a)), so `𝓜_σ(x) ≠ ∅`.  Foundation for Lemma 14.6. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.length_one_of_isPiElement_sigma
/-! **Every prime divides some `σ(M)`** (`S14_TypePCounting`, `exists_mem_sigma_of_prime_dvd_card`):
for `p ∣ |G|` there is a maximal `M` with `p ∈ σ(M)` (BG §1, via a non-normal Sylow `p`-subgroup). -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_mem_sigma_of_prime_dvd_card
/-! **σ-decomposition factor extraction** (`S14_TypePCounting`, `exists_length_one_factor`): every
`g ≠ 1` factors `g = x·x'` with `ℓ_σ(x) = 1`, `x'` a `σ(M)′`-element (commuting, both in `⟨g⟩`). -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_length_one_factor
/-! **Coq `cent1_sub_uniq_sigma_mmax`** (`S14_TypePCounting`,
`centralizer_le_of_maximalSigma_ncard_eq_one`): if `𝓜_σ(x)` is a singleton, its unique element `M`
contains `C_G(x)` (`y ∈ C_G(x)` permutes `𝓜_σ(x)`, fixing `M`, so `y ∈ N_G(M) = M`).  The linchpin
of the `|𝓜_σ(x')| > 1` step of BG Lemma 14.6.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.centralizer_le_of_maximalSigma_ncard_eq_one
/-! **BG Lemma 14.6 core** (`S14_TypePCounting`, `signalizer_coset_or_kappa_of_sigmaSharp`, Coq
`s'g`): for `x ∈ M_σ^#` and a nonidentity `σ(M)′`-element `x'` of `M` centralizing `x`, the product
`g = x·x'` lands in either the signalizer branch (`∃ y, ℓ_σ(y)=1 ∧ y⁻¹g ∈ R(y)`, witnessed by
`y = x'`) or the κ branch (`ℓ_σ(x)=1`, `M ∈ 𝓜_σ(x)`, `x' ∈ (C_M[x])^#`, `x'` a `κ(M)`-element).
Direct consumer of `sigma_diagnostic` (Cor 14.3); the τ₂ branch uses
`centralizer_le_of_maximalSigma_ncard_eq_one` + `exists_neighbor_eq_Rsub`.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.signalizer_coset_or_kappa_of_sigmaSharp
/-! **σ-element of `M` lies in `M_σ`** (`S14_TypePCounting`,
`mem_Msigma_of_isPiElement_sigma_of_mem`, Coq `mem_Hall_pcore (Msigma_Hall maxM)`): the converse of
`isPiElement_sigma_of_mem_Msigma` — the image of a `σ(M)`-element `x ∈ M` in the `σ(M)′`-quotient
`M / M_σ` is trivial.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.mem_Msigma_of_isPiElement_sigma_of_mem
/-! **BG Lemma 14.6 core, `g ∈ M` corollary** (`S14_TypePCounting`,
`branchA_or_branchB_of_mem_maximal`): for `g` in a maximal `M` with nontrivial `σ(M)`-part, `g`
lands in the signalizer branch or the κ branch.  Combines `mem_Msigma_of_isPiElement_sigma_of_mem`
with `signalizer_coset_or_kappa_of_sigmaSharp`.  The form consumed by the full Lemma 14.6
assembly.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.branchA_or_branchB_of_mem_maximal
/-! **Hall conjugacy** (`S14_TypePCounting`, `exists_conj_smul_le_of_isHall`, Coq `Hall_subJ`):
in a maximal `M`, every `π`-subgroup `X ≤ M` conjugates by an element of `M` into any Hall
`π`-subgroup `K` of `M`.  The general-`π` form of `exists_conj_smul_le_isHall_kappa`; the tool for
the `g ∉ M` case of the full Lemma 14.6 dichotomy.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_conj_smul_le_of_isHall
/-! **`σ` conjugation-invariant** (`S14_TypePCounting`, `sigma_conj_smul_eq`, Coq `sigmaJ`):
`σ(Mᵍ) = σ(M)` as sets.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigma_conj_smul_eq
/-! **BG Lemma 14.6** (`S14_TypePCounting`, `sigma_decomposition_dichotomy`, Coq `BGsection14`:1189):
every `g ≠ 1` lands in the signalizer branch (`∃ y, ℓ_σ(y)=1 ∧ y⁻¹g ∈ R(y)`) or the κ branch
(`∃ y, ℓ_σ(y)=1 ∧ ∃ N ∈ 𝓜_σ(y), y⁻¹g ∈ (C_N[y])^#` with `y⁻¹g` a `κ(N)`-element).  Proof = Coq's
second half: `branchA_or_branchB_of_mem_maximal` gives `s'g`, then the σ-decomposition factor,
WLOG `x ∈ M_σ`, the neighbour `N = N(x)` of Theorem 14.4, and Hall conjugacy of `⟨g⟩` into the
`σ(N)′`-Hall `M ∩ N` force the σ-part `x = 1`, a contradiction.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigma_decomposition_dichotomy
/-! **BG Corollary 14.9, type-I cover** (`S14_TypePCounting`,
`exists_mem_conjClassSet_Mtilde_of_ne_one`): under all-type-`F`, every `g ≠ 1` lies in some
`𝒞_G(M̃)`.  Immediate from `sigma_decomposition_dichotomy` (the κ branch is empty since
`κ(N) = ∅`).  **Gate 2 of the BG Theorem E cover is now sorry-free.**  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_mem_conjClassSet_Mtilde_of_ne_one
/-! **BG Corollary 14.9, the `G#` cover under all-type-`F`** (`S14_TypePCounting`,
`sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`): under all-type-`F`,
`G# = ⋃_M 𝒞_G(M̃)`.  `⊆` is the discharged cover identity (BG Lemma 14.6), `⊇` is `1 ∉ M̃`.  This
is the `cover_nonidentity` field of `BGTheoremETypeICovering` (modulo reps-vs-all-maximals).
Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF
/-! **κ→Ẑ identification** (`S14_TypePCounting`, the Coq `mFT_partition` part 2 core): for a
type-`P` `M`, a `σ(M)`-element `y` centralizing a nonidentity `κ(M)`-element `y'∈M` has product
`y·y' ∈ 𝒞_G(Ẑ)`.  `typeP_sigmaElement_mem_Kstar` (`y∈K*` via `Z=K⊔K*` cyclic) →
`kappa_branch_mem_zTilde` (`y·y'∈Ẑ` for `y'∈K`) → `kappa_branch_mem_conjClassSet_zTilde` (general,
via conjugation).  All axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_sigmaElement_mem_Kstar
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.kappa_branch_mem_conjClassSet_zTilde
/-! **`G^#` cover dichotomy** (`S14_TypePCounting`,
`exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one`): every `g ≠ 1` lies in `𝒞_G(M̃)` for some
maximal `M`, or in `𝒞_G(Ẑ)` for some exceptional `(K,K*)` — the `⊆` of BG Cor 14.9's `G^#`
partition (both cases), from `sigma_decomposition_dichotomy` (signalizer→M̃, κ→Ẑ via
`kappa_branch_dichotomy_mem_conjClassSet_zTilde`).  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.kappa_branch_dichotomy_mem_conjClassSet_zTilde
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one
/-! **BG Lemma 14.6, exclusivity** (`S14_TypePCounting`, `not_type1_of_type2`): a type-2 element
(`g = y·y'`, `y'` a nonidentity `κ(M)`-element of `C_M(y)`, `y ∈ M_σ^#`) is not of type-1
(`g = x·x'`, `ℓ_σ(x)=1`, `x' ∈ R(x)`).  The `T ∩ H̃ = ∅` input to Theorem 14.7. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.not_type1_of_type2
/-! **TI-subset saturation count** (`S14_TypePCounting`, `ncard_conjClassSet_of_isTISubset`):
for a TI-subset `A` stabilised by its normalizer-bound `L`, `|𝒞_G(A)| = |A|·[G:L]`.  The
disjoint-conjugate count feeding Theorem 14.7 step 5 (`|𝒞_G(T)| = |T|·[G:Z]`). -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset

/-! **BG Proposition 14.2** (`S14_TypePCounting`): the full structure theorem for a type-`P`
maximal subgroup `M` — `K` (Hall `κ(M)`) is prime on `M_σ`, `K* = C_{M_σ}(K) ≠ 1`, the
normalizer identity `N_M(X) = K ⊔ K*`, the `(d)` clause `K* ∩ M^g = 1`, and (for type `P₂`)
`σ(M) = β(M)`, `|K|` prime, and `M_σ` a TI-subset of `G`.  Both cases `κ ∩ τ₃ ≠ ∅` (`K = E`,
Corollary 13.11) and `κ ⊆ τ₁` (`K = E₁`, the Frobenius core via Theorem 3.10(a) + Lemma 12.17
+ Lemma 12.19) are discharged.  Sorry-free and axiom-clean — the §14 funnel keystone. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_structure

/-! **BG Proposition 14.2(b2)** (`S14_TypePCounting`, `typeP_elemAbelian_le_neighbor_Msigma`): the
clause of Prop 14.2(b) that `typeP_structure` omits — for `X ∈ ℰ_p¹(K)` (`K` Hall `κ(M)`) with
`C_{M_σ}(X) ≠ 1`, every `M* ∈ ℳ(N_G(X))` has `X ⊆ M*_σ`.  Proof: `p ∈ κ(M) ⊆ τ₁ ∪ τ₃`, Lemma 13.13
gives `p ∈ σ(M*)`, and `X ≤ M*` is a `σ(M*)`-subgroup.  Pre-positioned for Theorem 14.7's neighbour
analysis (`Z ⊆ M_i`, `X_i ⊆ M_{iσ}`).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_elemAbelian_le_neighbor_Msigma

/-! **BG Theorem 14.7 neighbour-embedding** (`S14_TypePCounting`, `typeP_neighbor_embed`), step 1 of
the §16-independent pre-position: every `M_i ∈ ℳ(N_G(X))` (`X ∈ ℰ¹(K)`) is not conjugate to `M`,
contains `Z = K ⊔ K*`, and has `X ⊆ M_{iσ}`.  Uses Prop 14.2(b1)/(b2) + `σ`-conjugation-invariance
(`sigma_conj`).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_neighbor_embed

/-! **BG Theorem 14.7 neighbour `κ`-transfer** (`S14_TypePCounting`, `typeP_neighbor_kappa`), step 1b
of the §16-independent pre-position: every prime `q ∈ π(K*)` lies in `κ(M_i)` for a neighbour
`M_i ∈ ℳ(N_G(X))`.  Proof: Cauchy gives `⟨x'⟩ ∈ ℰ_q¹(K*)`; Cor 14.3 (`sigma_diagnostic`) on
`(M_i, x, x')` must land in branch 1 (`π(⟨x'⟩) ⊆ κ(M_i)`) since branch 2 would give
`ℳ(C_G(x')) = {M_i}`, contradicting Prop 14.2(c)'s `{M}` (`M ≠ M_i`).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_neighbor_kappa

/-! **BG Theorem 14.7 partner existence** (`S14_TypePCounting`, `exists_typeP_partner`), the
§16-independent core assembling steps 1a/1b (`typeP_neighbor_embed` + `typeP_neighbor_kappa`):
for a type-`P` maximal `M` with Hall `κ(M)`-subgroup `K`, `K* = C_{M_σ}(K) ≠ 1`, and a line
`X ∈ ℰ_p¹(K)`, the maximal subgroup `M* ∈ ℳ(N_G(X))` (which exists, `N_G(X)` proper) is type-`P`,
nonconjugate to `M`, contains `K ⊔ K*` with `X ≤ M*_σ`, and has `π(K*) ⊆ κ(M*)`.  This is the
nonconjugate partner `M*` of Theorem 14.7 with its basic neighbour data; cyclicity of `Z`, the
TI property, type-`P₂`, and the §16-gated covering/uniqueness layer on top.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_typeP_partner

/-! **BG Theorem 14.7 swap argument** (`S14_TypePCounting`): the neighbour-`Z` machinery.
`typeP_normalizer_inf_eq` packages Proposition 14.2(b1) for a neighbour `Mi` (producing its Hall
`(κ∪σ)'`-subgroup internally), giving `N_G(X) ⊓ Mi = Ki ⊔ C_{Mi_σ}(Ki)` for a Hall `κ(Mi)`-subgroup
`Ki ∋ X`.  `typeP_swap_Z_le` is direction `⊆` of the swap (mmd L3999): `K ⊔ K* ≤ Ki ⊔ Ki*`, the
`K*`-part using Hall conjugacy (`K* ⊆` some Hall `κ(Mi)`-subgroup `Ki'`, with `N_G(X) ⊓ Mi`
independent of the Hall choice).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_normalizer_inf_eq

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_swap_Z_le

/-! **BG 14.7, `M ⊇ N_G(X)` from a unique centralizer-maximal** (`S14_TypePCounting`,
`normalizer_le_of_maximalSubgroupsContaining_centralizer`, mmd L3992): if `ℳ(C_G(X)) = {M}` then
`N_G(X) ≤ M`.  General fact (conjugation fixes `C_G(X)`, uniqueness forces `Mᵍ = M`, `M`
self-normalizing); supplies the swap argument's reverse direction.  Axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S14.normalizer_le_of_maximalSubgroupsContaining_centralizer

/-! **BG 14.7, swap argument — the `Z`-coincidence** (`S14_TypePCounting`, mmd L3999-4001).
`le_centralizerFactor_of_le_sup_of_le_Msigma` is the `σ`-projection: a `σ(Mi)`-group inside an
internal direct product `Ki × Ki*` (`Ki` a `σ'`-group) lands in the `σ`-factor `Ki*`.
`typeP_swap_Z_eq` is the full coincidence `Z = K ⊔ K* = Ki ⊔ Ki*`: direction `⊆` from
`typeP_swap_Z_le`, direction `⊇` from the role-exchanged swap using `M ⊇ N_G(X*)`,
`π(Ki*) ⊆ κ(M)`, and `Xi ⊆ Ki*`.  Axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S14.le_centralizerFactor_of_le_sup_of_le_Msigma

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_swap_Z_eq

/-! **BG 14.7, `K_i*` pairwise disjoint** (`S14_TypePCounting`, mmd L4005).
`typeP_centralizer_singleton` packages Proposition 14.2(c) for a neighbour (`ℳ(C_G(Y)) = {M}` for
`Y ∈ ℰ¹(K*)`).  `typeP_neighbor_Kstar_inf_eq_bot`: distinct type-`P` maximals `Mi ≠ Mj` have
`C_{Mi_σ}(Ki) ⊓ C_{Mj_σ}(Kj) = ⊥` (a common line would force `{Mi} = {Mj}`).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_centralizer_singleton

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_neighbor_Kstar_inf_eq_bot

/-! **BG 14.7 density backbone — inclusion–exclusion** (`S14_TypePCounting`,
`ncard_biUnion_subgroup_add_card`, mmd L4031): for a nonempty finite family of subgroups pairwise
meeting at `⊥`, `|⋃ Sᵢ| + |s| = (∑ |Sᵢ|) + 1` (each contributes `|Sᵢ| − 1` non-identity elements,
disjoint, plus the shared identity).  Gives `|T| = |Z| + n − ∑ kᵢ*` for the TI-set `T = Z − ⋃ Kᵢ*`.
Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.ncard_biUnion_subgroup_add_card

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.ncard_sdiff_biUnion_subgroup

/-! **BG 14.7 internal direct product cardinality** (`S14_TypePCounting`,
`card_iSup_of_pairwise_commute_coprime`, mmd L4009): a finite family of pairwise-commuting subgroups
with pairwise-coprime orders is an internal direct product, so `|⨆ Hᵢ| = ∏ |Hᵢ|`
(independence from `Subgroup.independent_of_coprime_order`, then `noncommPiCoprod` injective with
range `⨆ Hᵢ`).  Gives `z = ∏ kᵢ*` for the `Kᵢ*`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.card_iSup_of_pairwise_commute_coprime

/-! **BG 14.7, canonical `Kᵢ*`** (`S14_TypePCounting`, `typeP_neighbor_Kstar_eq_Z_inf_Msigma`,
mmd L4009): given the swap `Z = Kₙ ⊔ Kₙ*`, the factor `Kₙ* = C_{Nσ}(Kₙ)` equals `Z ⊓ M_σ(N)` —
the `σ(N)`-part of `Z`, independent of the chosen Hall `κ(N)`-subgroup `Kₙ`.  Lets the family
`{Kᵢ*}` be defined choice-free as `N ↦ Z ⊓ M_σ(N)`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_neighbor_Kstar_eq_Z_inf_Msigma

/-! **BG 14.7, per-neighbour swap package** (`S14_TypePCounting`, `exists_neighbor_kappaHall_swap`,
mmd L3997-4009): for a type-`P` maximal `M` and a maximal `N ⊇ N_G(X)` (`X ∈ ℰ¹(K)`), there is a
Hall `κ(N)`-subgroup `K_N` realising the swap `Z = K_N ⊔ K_N*` with canonical `K_N* = Z ⊓ M_σ(N)`.
The per-neighbour foundation the `M_i` family iterates over.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_neighbor_kappaHall_swap

/-! **BG 14.7, coverage of `κ(M)`-primes** (`S14_TypePCounting`, `exists_typeP_neighbor_mem_sigma`,
mmd L4007): every prime `p ∣ |K|` lies in `σ(N)` for a nonconjugate type-`P` neighbour `N ⊇ Z`
(via a line `X ∈ ℰ_p¹(K)` and its partner).  With `M` (covering `σ(M) ⊇ π(K*)`) this gives the
coverage `⋃ σ(Mᵢ) ⊇ π(Z)` forcing `⨆ Kᵢ* = Z`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_typeP_neighbor_mem_sigma

/-! **BG 14.7, internal-direct-product factor normality** (`S14_TypePCounting`,
`sup_le_normalizer_inf_of_commute`): in `A ⊔ B` with `B ≤ C_G(A)`, both factors are normal,
`A ⊔ B ≤ N_G(A) ⊓ N_G(B)`.  Applied to the swap `Z = K_N ⊔ K_N*` it makes `K_N`, `K_N*` normal in
`Z` (input to pairwise commutativity, pairwise nonconjugacy, and the `n = 1` collapse).
Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sup_le_normalizer_inf_of_commute

/-! **BG 14.7, internal-product cardinality + commute helpers** (`S14_TypePCounting`):
`card_sup_of_commute_of_disjoint` — for commuting `H`, `K` with `H ⊓ K = ⊥`, `|H ⊔ K| = |H|·|K|`
(via `noncommCoprod`).  `commute_of_le_normalizer_of_disjoint` — subgroups `A, B ≤ Z` normal in `Z`
with `A ⊓ B = ⊥` commute elementwise (`[x,y] ∈ A ⊓ B = ⊥`).  Used for `|Kᵢ* ⊔ Kⱼ*| = kᵢ*·kⱼ*` in the
pairwise-nonconjugacy argument.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.card_sup_of_commute_of_disjoint

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.commute_of_le_normalizer_of_disjoint

/-! **BG 14.7, pairwise nonconjugacy of the family** (`S14_TypePCounting`,
`typeP_family_nonconjugate`, mmd L4015): maximal subgroups whose swap factors `Zₖ = M_σ(Mₖ) ⊓ C(Kₖ)`
meet trivially (with `Z₂ ≠ ⊥`) are nonconjugate — else `σ(M₁) = σ(M₂)` makes `Z₁`, `Z₂` disjoint
normal `τ`-Halls of `Z` with `z₁ z₂ ∣ z = k₁ z₁`, so `z₂ ∣ k₁` (a `τ`-number divides a `τ'`-number),
forcing `Z₂ = ⊥`.  Feeds Lemma 14.5(b).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_family_nonconjugate

/-! **BG 14.7, per-neighbour swap package with normality** (`S14_TypePCounting`,
`exists_neighbor_kappaHall_swap_normal`): the per-neighbour swap restated with canonical factor
`K_N* = Z ⊓ M_σ(N)` folded in and `K_N* ◁ Z` added — the exact per-member data the `M_i` family
consumes.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_neighbor_kappaHall_swap_normal

/-! **BG 14.7, full per-neighbour data** (`S14_TypePCounting`, `exists_neighbor_full`): the complete
per-member package the `M_i` family consumes — Hall `κ(N)`-subgroup `K_N`, swap `Z = K_N ⊔ K_N*`
(canonical `K_N* = Z ⊓ M_σ(N)`), `K_N* ◁ Z`, `N` type-`P`, and `K_N* ≠ ⊥` (`X ≤ K_N*`).
Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_neighbor_full

/-! **BG 14.7, two family members nonconjugate** (`S14_TypePCounting`,
`neighbor_pair_nonconjugate`, mmd L4015): distinct type-`P` maximals `N₁ ≠ N₂` with their swaps are
nonconjugate — Proposition 14.2(c) (swap factors meet trivially) + `typeP_family_nonconjugate`.
The per-pair input to the family's pairwise nonconjugacy.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.neighbor_pair_nonconjugate

/-! **BG 14.7, the base member `M` (`i = 0`)** (`S14_TypePCounting`, `typeP_self_member`, mmd L4003):
`M`'s own data in the family's canonical shape — `K_M* = Z ⊓ M_σ(M) = Kstar`, trivial swap
`Z = K ⊔ K_M*`, `K_M* ◁ Z`, `K_M* ≠ ⊥`.  Aligns `M` with the neighbours.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_self_member

/-! **BG 14.7 `n=1` collapse helper** (`S14_TypePCounting`, `le_of_coprime_index`, mmd L4043): if
`N ◁ G` and `|H|` is coprime to `[G : N]`, then `H ≤ N` (the image of `H` in `G/N` has order `1`).
Applied with `N = Kᵢ` (normal `σ(Mᵢ)'`-Hall of `Z`) and `H = Kⱼ*` gives `Kⱼ* ≤ Kᵢ`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.le_of_coprime_index

/-! **BG 14.7, unified per-neighbour data** (`S14_TypePCounting`, `exists_neighbor_data`): the single
per-member source for the family — raw swap factor `K_N* = M_σ(N) ⊓ C(K_N)`, canonical identity
`K_N* = Z ⊓ M_σ(N)`, `N` type-`P`, `K_N* ≠ ⊥`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_neighbor_data

/-! **BG 14.7, uniform per-member family data** (`S14_TypePCounting`, `typeP_family_member_data`,
mmd L4003): every member `N` of the type-`P` family (`IsZFamilyMember`: `N = M` or a maximal over
`N_G(X)` for a line `X ∈ ℰ_p¹(K)`) is a type-`P` maximal containing `Z`, with Hall `κ(N)`-subgroup
`K_N` realising the swap (raw + canonical `K_N* = Z ⊓ M_σ(N)`, `K_N* ≠ ⊥`).  Case-split
`typeP_self_member`/`exists_neighbor_data`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_family_member_data

/-! **BG 14.7, family pairwise nonconjugate** (`S14_TypePCounting`,
`typeP_family_pairwise_nonconjugate`, mmd L4015): any two distinct `IsZFamilyMember`s are
nonconjugate (per-member data + `neighbor_pair_nonconjugate`).  Feeds Lemma 14.5(b).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_family_pairwise_nonconjugate

/-! **BG 14.7, family `Kᵢ*` pairwise disjoint** (`S14_TypePCounting`, `typeP_family_Kstar_disjoint`,
mmd L4005): for distinct members `N₁ ≠ N₂`, `(Z ⊓ M_σ(N₁)) ⊓ (Z ⊓ M_σ(N₂)) = ⊥` (nonconjugate ⟹
`σ` disjoint by Thm 13.9 ⟹ `M_σ(N₁) ⊓ M_σ(N₂) = ⊥`).  Pairwise-`⊥` input to the `|T|` count.
Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_family_Kstar_disjoint

/-! **BG 14.7, type-`P` family as a `Finset`** (`S14_TypePCounting`, `ZFamilyFinset` + `mem_`/
`_nonempty`): `{N | IsZFamilyMember M K N}` as a `Finset` (`M` always a member).  The index for
the `|T|` count and density sum.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.mem_ZFamilyFinset

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.ZFamilyFinset_nonempty

/-! **BG Proposition 14.2 support** (`S14_Prop142Support`, Lane F, issue 7000): generic
`κ`-free conjugation-transport utilities that Proposition 14.2 cites.  `actsPrimeOn_conj`
transports a prime action `ActsPrimeOn N X` along conjugacy by a normalizer element of `N`
(case `κ ⊆ τ₁`: WLOG `K = E₁`); `smul_centralizer_singleton` / `smul_centralizer_subgroup`
are the element- and subgroup-centralizer conjugation identities it rests on.  Fully
unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch3.S13.actsPrimeOn_conj

#assert_only_allowed_axioms OddOrder.BG.Ch3.S13.smul_centralizer_singleton

#assert_only_allowed_axioms OddOrder.BG.Ch3.S13.smul_centralizer_subgroup

/-! **BG Corollary 14.3** (`S14_TypePCounting`, `sigma_diagnostic`): for `x ∈ M_σ^#` and a
nonidentity `σ(M)'`-element `x'` of `C_M(x)`, either `π(⟨x'⟩) ⊆ κ(M)` with `C_G(x) ⊆ M`, or
`π(⟨x'⟩) ⊆ τ₂(M)` with `ℓ_σ(x') = 1` and `𝓜(C_G(x')) = {M}`.  Branch 1 uses Prop 14.2(b1)/(c)
+ Lemma 14.1(b); branch 2's `ℓ_σ = 1` uses Lemma 12.11(a) + the general Corollary 12.16(a)
(`sigma_subgroup_conj_into_Msigma_general`, discharging its `σ`-disjointness gate with Theorem
13.9) + `M_σ` conjugation-equivariance.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigma_diagnostic

/-! **BG Theorem 14.4** (`S14_TypePCounting`, `sigmaLength_one_centralizer_structure`): if
`ℓ_σ(x) = 1` and `|𝓜_σ(x)| > 1`, then `C_G(x)` lies in a unique `N ∈ 𝓜` with
`R(x) = N_σ ∩ C_G(x) ⊋ 1` a Hall `σ(N)`-subgroup of `C_G(x)`, `π(⟨x⟩) ⊆ τ₂(N)`,
`N ∈ 𝓜_F ∪ 𝓜_{P₂}`, and for every `M ∈ 𝓜_σ(x)`: `τ₂(N) ∩ π(N) ⊆ σ(M)`, `σ(N) ∩ π(M) ⊆ β(N)`,
and `M ∩ N` complements `N_σ` in `N`.  (The `§16`-circular sharply-transitive headline and part
(b) are deferred to §16's `RData`.)  Proof: Theorems 13.9 + 10.1(b) give `N ≠ M`; Proposition
12.15(e) gives `(d)`, `(e)`, `q ∈ τ₂(N)`; Corollary 14.3 (`sigma_diagnostic`) gives
`π(⟨x⟩) ⊆ τ₂(N)` and the uniqueness `𝓜(C_G(x)) = {N}`; Corollary 12.6 +
`exists_subgroupESetup_with_le` give `(c)`.  The `(c)` clause uses `∩ piSet N` (BG's `τ₂(N) ⊆ π(N)`)
since the repo `tau2` predicate is not prime-restricted.  Fully unconditional, axiom-clean.  Helper
`Msigma_inf_normalizer_eq_bot_of_tau2` (`N_G(A) ⊓ M_σ = 1` for `A ∈ ℰ_p²(E)`, `p ∈ τ₂(M)`, the crux
of `(c)`) is also axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaLength_one_centralizer_structure

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.Msigma_inf_normalizer_eq_bot_of_tau2

/-! **BG Theorem 14.4, `C_G(x)`-witness sharp transitivity + Cor 15.3(b) `hconj` input**
(`S14_TypePCounting`): `exists_conj_centralizer_of_mem_maximalSigma` strengthens the
`isConjugateSubgroup` transitivity to keep the conjugator in `C_G(x)`; `mf_hall_conj_realized_in_M`
is the §14.4 half of BG Corollary 15.3(b) — for `H ≤ M_σ`, `G`-conjugate elements of `H` are
`M`-conjugate (via `N_G(M) = M`).  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_conj_centralizer_of_mem_maximalSigma
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.mf_hall_conj_realized_in_M

/-! **BG Theorem 14.7, type-`P₁` Hall complement card** (`S14_TypePCounting`, `typeP1_card_eq`):
for a type-`P₁` maximal `N` with Hall `κ(N)`-subgroup `K_N`, `|N| = |N_σ|·|K_N|` (the σ-part
uniqueness; `K_N` Hall `σ(N)′` complements the normal Hall `σ(N)`-subgroup `N_σ`).  Feeds the
density inequality of Theorem 14.7(e).  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP1_card_eq

/-! **BG Theorem 14.7, the density inequality** (`S14_TypePCounting`, `exists_typeP2_member`): some
member of the type-`P` family `{M} ∪ {neighbours}` has type `P₂`.  Proof = the BG density count: if
all members were type `P₁`, the pairwise-disjoint conjugacy pieces `𝒞_G(T)`, `{𝒞_G(M̃ᵢ)}` would
cover more than `G^#`.  Entirely a `ℕ` computation (`omega`) over the landed counts.  Supporting
lemmas (`typeP1_member_Msigma_index_eq`, `typeP_member_two_mul_index_le`, `ZFamilyFinset_one_lt_card`,
`one_not_mem_Mtilde`, `density_pieces_ncard_le`) registered alongside.  Fully unconditional,
axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.one_not_mem_Mtilde
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP1_member_Msigma_index_eq
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_member_two_mul_index_le
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.ZFamilyFinset_one_lt_card
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.density_pieces_ncard_le
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_typeP2_member

/-! **BG Theorem 14.7, the `n = 1` collapse** (`S14_TypePCounting`, `family_card_eq_two`): the
type-`P` family has exactly two members.  The type-`P₂` member's Hall `κ`-subgroup has prime order
(Prop 14.2(g)); every other member's canonical factor `Kⱼ*` is a nontrivial `σ(Mᵢ)′`-subgroup of `Z`
(`isPiSubgroup_le_left_of_commute`), forced equal to it, but pairwise disjoint, so at most one
neighbour.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.isPiSubgroup_le_left_of_commute
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.family_card_eq_two

/-! **BG Theorem 14.7, the unique partner `M*`** (`S14_TypePCounting`, `exists_partner`): from
`|family| = 2` and `M ∈ family`, the unique other member `M*` is the nonconjugate type-`P` partner;
every family member is `M` or `M*`.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_partner

/-! **BG Theorem 14.7(f), the type-`P₂` dichotomy** (`S14_TypePCounting`,
`isTypeP2_or_isTypeP2_partner`): one of `M`, `M*` is type `P₂` (the density inequality's type-`P₂`
member is `M` or `M*`).  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.isTypeP2_or_isTypeP2_partner

/-! **BG Theorem 14.7, the partner canonical factor** (`S14_TypePCounting`, `partner_canonical_eq`):
`Z ⊓ M*_σ = K`.  The partner's canonical family factor equals `M`'s Hall `κ`-subgroup — a `σ(M)′`-
subgroup of `Z = K × K*` lying in the `σ(M)′`-Hall `K` (`isPiSubgroup_le_left_of_commute`), and
`K ≤ M*_σ` since every prime of `K` lies in `σ(M*)` (`kappaHall_primes_subset_sigma_partner`, the
line→partner argument).  This is the structural keystone turning `T = Z − ⋃ Kᵢ*` into
`Ẑ = Z − (K ∪ K*)`.  Both registered.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.kappaHall_primes_subset_sigma_partner
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.partner_canonical_eq

/-! **BG Theorem 14.7(e), `Ẑ` is a TI-subset** (`S14_TypePCounting`, `typeP_zTilde_isTI`): with the
family `{M, M*}` the union `⋃ (Z ⊓ N_σ)` collapses to `K ∪ K*` (via `partner_canonical_eq` and
`typeP_self_member`), so `Ẑ = Z − (K ∪ K*)` equals the family TI-set and inherits TI-ness from
`typeP_family_T_isTI`.  A conjunct of the `∃! Mstar`.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_zTilde_isTI

/-! **BG Theorem 14.7, `|Ẑ| = (k − 1)(k* − 1)`** (`S14_TypePCounting`, `zTilde_ncard_eq`): the TI-set
`Ẑ = Z − (K ∪ K*)` has `(|K| − 1)(|K*| − 1)` elements (`|Z| = |K|·|K*|`, `K ∩ K* = 1`).  The count
underlying the density bound `|𝒞_G(Ẑ)| > ½|G|`.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.zTilde_ncard_eq

/-! **BG Theorem 14.7(e), family `Z ⊓ N_σ` collapse** (`S14_TypePCounting`,
`family_inf_msigma_union_eq`): for the type-`P` family `{M, M*}`, `⋃_{N} (Z ⊓ N_σ) = K ∪ K*`
(`Z ⊓ M_σ = K*` via `typeP_self_member`, `Z ⊓ M*_σ = K` via `partner_canonical_eq`).  Factored out
of `typeP_zTilde_isTI`; identifies `Ẑ = Z − (K ∪ K*)` with the family TI-set in the density count.
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.family_inf_msigma_union_eq

/-! **BG Theorem 14.7, the density bound `|𝒞_G(Ẑ)| > ½|G|`** (`S14_TypePCounting`,
`typeP_zTilde_conjClass_gt_half`): the conjugacy saturation of `Ẑ` covers more than half of `G`.
`|𝒞_G(Ẑ)| = |Ẑ|·[G:Z] = (k−1)(k*−1)·[G:Z]` (TI count + `zTilde_ncard_eq`) and `|G| = k·k*·[G:Z]`
(`card_kappaHall_sup_Kstar`), reducing to `k·k* < 2(k−1)(k*−1)` for coprime odd `k = |K|`,
`k* = |K*| > 1`.  The counting heart of the `∃! M*` covering.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_zTilde_conjClass_gt_half

/-! **Two `> ½|G|` subsets intersect** (`S14_TypePCounting`, `ncard_inter_nonempty_of_two_mul_gt`):
in a finite group, `2·|A| > |G|` and `2·|B| > |G|` force `A ∩ B ≠ ∅` (inclusion–exclusion).  The
combinatorial core of the covering step of Theorem 14.7 (`𝒞_G(Ẑ) ∩ 𝒞_G(S) ≠ ∅`).  Fully
unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.ncard_inter_nonempty_of_two_mul_gt

/-! **BG Theorem 14.7, the density bound for every type-`P` maximal** (`S14_TypePCounting`,
`exists_zTilde_conjClass_gt_half_of_isTypeP`): every `H ∈ 𝓜_𝓟` has a Hall `κ(H)`-subgroup `L`,
`L* = C_{Hσ}(L)`, and `|𝒞_G(Ẑ_H)| > ½|G|` — the same density count run for an arbitrary type-`P`
member (BG's "we also have `|𝒞_G(S)| > ½|G|`"), with `H`'s partner data produced internally via
`exists_partner` fed `dummySigmaDecomposition`.  The covering step applies this to both `M` and the
arbitrary `H`.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_zTilde_conjClass_gt_half_of_isTypeP

/-! **BG Theorem 14.7 covering, the `σ`-part matching** (`S14_TypePCounting`,
`exists_inf_ne_bot_of_mem_zTilde_inter`, with helper `isPiElement_mem_right_of_commute`): if `t`
lies in both `Ẑ_M = (K ⊔ K*) − (K ∪ K*)` and `L ⊔ L*` but not in `L` (the two coprime
direct-product `σ`-structures), then `L*` meets one of `K`, `K*` nontrivially — BG's
"`T ∩ S ≠ ∅ ⟹ L* ∩ Kᵢ* ≠ 1`".  The `σ(H)`-part of `t` lands in `L*`, and its `σ(M)`- and
`σ(M)′`-parts (powers of it, so in `L*`) lie in `K*` and `K`.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.isPiElement_mem_right_of_commute

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_inf_ne_bot_of_mem_zTilde_inter

/-! **BG Proposition 14.2(f)** (`S14_TypePCounting`, `typeP_sigma_subgroup_le_Msigma`): every
`σ(M)`-subgroup `Y < ⊤` of `G` meeting `K*` nontrivially lies in `M_σ`.  Not packaged in
`typeP_structure`; derived from Corollary 12.16 (`sigma_subgroup_conj_into_Msigma_general`, the
`σ`-disjointness gate discharged by Theorem 13.9) and Proposition 14.2(d) (the conjugator fixes a
nontrivial element of `K*`, so lies in `M`).  A step of the Theorem 14.7 partner-symmetry argument.
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_sigma_subgroup_le_Msigma

/-! **BG Theorem 14.7(2)(3), partner symmetry** (`S14_TypePCounting`, `typeP_partner_structure`):
the partner `M*` carries the dual Hall structure — `K*` is a Hall `κ(M*)`-subgroup of `M*` and
`K = C_{M*_σ}(K*)`.  Short via the family machinery: `typeP_family_member_data` produced `M*`'s Hall
`κ(M*)`-subgroup `KN` with `Z = KN ⊔ C_{M*_σ}(KN)` and `partner_canonical_eq` gives
`Z ⊓ M*_σ = K`; two applications of `isPiSubgroup_le_left_of_commute` (π = σ(M*)) give `KN = K*`.
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_partner_structure

/-! **BG Theorem 14.7(1)** (`S14_TypePCounting`, `typeP_partner_centralizer_singleton`):
`ℳ(C_G(Y)) = {M*}` for every `Y ∈ ℰ¹(K)`.  Proposition 14.2(c) applied to the partner `M*` (whose
`K*`-role is `K`, by `typeP_partner_structure`); the `K`-side companion of `14.2(c)`, used by the
covering step to conjugate a type-`P` subgroup to `M*`.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_partner_centralizer_singleton

/-! **BG Theorem 14.7(7), the covering** (`S14_TypePCounting`, `typeP_covering`): every type-`P`
maximal subgroup `H` is conjugate to `M` or to its partner `M*`.  The capstone of the `∃! M*`
bundle: both `Ẑ_M` and `Ẑ_H` cover `> ½|G|` (`exists_zTilde_conjClass_gt_half_of_isTypeP`), so the
saturations meet (`ncard_inter_nonempty_of_two_mul_gt`); the `σ`-part matching
(`exists_inf_ne_bot_of_mem_zTilde_inter`) lands a line `Y` meeting `K` or `K*`, and the double
`14.2(c)` / `14.7(1)` singleton (`typeP_partner_centralizer_singleton`) forces `c·H = M` or `M*`.
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_covering
/-! **Type-`P` data constructor** (`S14_TypePCounting`, `exists_typeP_data`): every maximal `M`
carries a Hall `κ(M)`-subgroup `K ≤ M`, the swap `K* = M_σ ∩ C_G(K)`, and a Hall `(κ∪σ)ᶜ`-subgroup
`U` (Hall's theorem in the solvable `↥M`).  The missing constructor feeding `exists_partner` /
`typeP_covering` from a bare `M ∈ maximalTypePFamily` (used by Cor 14.8 part 2).  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_typeP_data
/-! **BG Corollary 14.8** (`S14_TypePCounting`, `typeP1_conjugate_and_typeP_twoClasses`): the
type-`P₁` maximal subgroups are all conjugate, and the type-`P` family is exactly two conjugacy
classes (`M` and its Theorem 14.7 partner `M*`).  Part 1 uses `isTypeP2_or_isTypeP2_partner` (the
partner is type-`P₂`, so `N ~ M*` would make `N` non-`P₁`); part 2 is `exists_partner` +
`typeP_covering`.  Both via the `exists_typeP_data` constructor.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP1_conjugate_and_typeP_twoClasses

/-! **Hall `κ`-subgroup inside a nilpotent group is cyclic** (`S14_TypePCounting`,
`isCyclic_kappaHall_of_le_nilpotent`): a Hall `κ(N)`-subgroup `K' ≤ N` contained in a nilpotent
`W` is cyclic.  `κ(N) ⊆ τ₁(N) ∪ τ₃(N)` bounds `pRank K' p ≤ 1` at every prime, and `K' ≤ W`
nilpotent makes `K'` nilpotent; `isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one` concludes.
The cyclicity engine for both Hall factors of `Z` in Theorem 14.7(d).  Fully unconditional,
axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.isCyclic_kappaHall_of_le_nilpotent

/-! **BG Theorem 14.7(d), `M_σ` nilpotent for type-`P₂`** (`S14_TypePCounting`,
`msigma_isNilpotent_of_isTypeP2`): for a type-`P₂` maximal `M`, `M_σ` is nilpotent.  `IsTypeP2`
makes `κ(M) ⊊ π(M) ∖ σ(M)` proper, yielding `p ∈ π(M) ∖ (σ(M) ∪ κ(M))`; a maximal-rank elementary
abelian `p`-subgroup `A ≤ M` feeds Lemma 14.1, whose third conclusion is `IsNilpotent M_σ`.
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.msigma_isNilpotent_of_isTypeP2

/-! **BG Theorem 14.7(d), cyclicity of `Z = K ⊔ K*`** (`S14_TypePCounting`, `typeP_Z_isCyclic`):
`Z = K ⊔ K*` is cyclic.  One of `M`, `M*` is type-`P₂` (`isTypeP2_or_isTypeP2_partner`); the `P₂`
member's Hall `κ`-factor is prime-order (cyclic), the other factor is a Hall `κ`-subgroup of the
partner inside the nilpotent `σ`-core of the `P₂` member (`msigma_isNilpotent_of_isTypeP2` +
`isCyclic_kappaHall_of_le_nilpotent`); two coprime cyclic factors give `Z` cyclic.  Fully
unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_Z_isCyclic

/-! **BG Theorem 14.7, unique nonconjugate partner `M*`** (`S14_TypePCounting`,
`typeP_partner_existsUnique`): the `∃!` heart of Theorem 14.7 — there is a unique maximal `M*` that
is type-P, nonconjugate to `M`, has `K*` Hall `κ(M*)` with `K = C_{M*_σ}(K*)`, makes `Z = K ⊔ K*`
cyclic with `Ẑ` a TI-set, has `M` or `M*` type-P₂, and covers every type-P maximal up to conjugacy.
Existence from `exists_partner` + `typeP_partner_structure` + `typeP_Z_isCyclic` + `typeP_zTilde_isTI`
+ `isTypeP2_or_isTypeP2_partner` + `typeP_covering`; uniqueness from the partner symmetry
`K = C_{M*_σ}(K*)` pinning `ℳ(C_G(X)) = {M*}` for `X ∈ ℰ¹(K)`.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_partner_existsUnique

/-! **Derived subgroup via a `σ`-complement** (`S14_TypePCounting`,
`derivedInG_eq_Msigma_sup_derivedInG_complement`): for a §12 `E`-setup of `M`, `M' = M_σ ⊔ E'`. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.derivedInG_eq_Msigma_sup_derivedInG_complement

/-! **BG Theorem 14.7(h) core** (`S14_TypePCounting`, `typeP_derivedInG_isComplement_kappaHall`):
for a type-P maximal `M` with Hall `κ(M)`-subgroup `K` cyclic, `M' = [M,M]` complements `K` in `M`
(Proposition 14.2(a): `M' = U M_σ`).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_derivedInG_complement_of_eq_complement
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall

/-! **BG Theorem 14.7, type-P duality** (`S14_TypePCounting`, `typeP_duality`): the full Theorem 14.7
for a type-P maximal `M` — `M' = [M,M]` complements `K` with coprime orders (part (h)), and the
unique nonconjugate type-P partner `M*` with cyclic `Z`, TI `Ẑ`, type-P₂ side, and covering.
Fully unconditional, axiom-clean — completes the §14 long pole feeding §15/§16. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_duality

/-! **BG Theorem 14.7(4) / Theorem C(6) / Theorem I(2)**, the type-P dual pair intersection
(`S16_PairIntersection`, `typeP_pair_inf_eq`): for a type-P maximal `M` with Hall `κ`-factor `K`,
canonical `K* = M_σ ⊓ C_G(K)`, and the `typeP_duality` partner `M*` (with `K = M*_σ ⊓ C_G(K*)`),
the pair intersects in the cyclic `Z`: `M ⊓ M* = K ⊔ K*`.  This is the reverse inclusion
`M ⊓ M* ≤ K ⊔ K*` — the genuine missing §16 structure restating `S ∩ T = W` — proved via the
σ-decomposition (Step 1: `M_σ ⊓ M* = K*`) and Proposition 14.2(b1) (Step 2).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeP_pair_inf_eq

/-! **BG Theorem E, the `π(G)` partition core** (`S16_MainResults`): the two unconditional conjuncts
of BG Theorem E (issue 8019) — the partition of `π(G)` by the `σ(Mᵢ)` of a system of conjugacy-class
representatives of the maximal subgroups.

* `sigma_reps_pairwise_disjoint` (clause (a2)): distinct representatives have disjoint `σ`-sets,
  from BG Theorem 13.9 (`sigma_disjoint_of_nonconjugate`, landed sorry-free) via the `∃!`
  non-conjugacy of distinct representatives.
* `sigma_reps_prime_cover` (clause (a1)): a prime `p` divides `|G|` iff it is a `σ`-prime of some
  representative — forward from `exists_mem_sigma_of_prime_dvd_card` (every prime of `G` is a
  `σ`-prime of some maximal) + `sigma_conj`, reverse from `σ ⊆ π` + Lagrange.

Together they give `π(G) = ⨆ᵢ σ(Mᵢ)`.  `exists_maximal_conjugacy_reps` constructs the system `reps`
itself (a conjugacy transversal of the maximal subgroups, via the `IsConjugateSubgroup` setoid and
`Quotient.out`), so `exists_reps_sigma_partition` is the **unconditional** `π(G)` partition (no `reps`
hypothesis).  The remaining BG Theorem E content (the thickened-support cardinality,
tilde-disjointness, and `G#` covering) stays gated on §13–14 (`theoremE_…`, issue 8019).  All fully
unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.sigma_reps_pairwise_disjoint
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.sigma_reps_prime_cover
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.exists_maximal_conjugacy_reps
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.exists_reps_sigma_partition
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma

/-! **BG Theorem D(1), `M_σ`-fusion control** (`S16_MainResults`, `msigma_fusion_control`): two
elements of `M_σ` conjugate in `G` are conjugate in `M`.  The one unconditional Theorem-D conjunct,
from Corollary 15.3(b) (`mf_hall_centralizer_control`, axiom-clean) at the trivial Hall subgroup
`H := M_σ` plus `N_G(M_σ) = M` (`normalizer_Msigma_eq_self`).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.msigma_fusion_control

/-! **BG Theorem D(2), `M_σ ∩ M^g` cyclic** (`S16_MainResults`, `Msigma_inf_conj_isCyclic`): for
`g ∉ M`, `M_σ ∩ M^g` is cyclic (BG Lemma 12.17 third clause).  Abelian (TI part
`Msigma_inf_conj_inf_derived_eq_bot`), odd, and rank ≤ 1 (a noncyclic elementary abelian subgroup
would give `C_G(A) ≤ N_G(A) ≤ M` via `norm_noncyclic_sigma`, contradicting the σ-uniqueness core),
hence cyclic (`isCyclic_of_isMulCommutative_of_rank_le_one`).  Supplies Theorem D's `hD2`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.Msigma_inf_conj_isCyclic

/-! **BG Theorem B(1)** (`S16_MainResults`, `theoremB_U_sylow_abelian_rank_le_two`): every Sylow
subgroup of `U` is abelian of rank ≤ 2.  Standalone, faithful (explicit `U ≤ M`; restricted to
prime `p`) form of the first conjunct of `theoremB_U_and_A_tame`, derived cite-only over §12
(`exists_subgroupESetup_with_le` + `SubgroupESetup.rank_le_two` + `nilpotent_sigmaComplement_abelian`).
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.theoremB_U_sylow_abelian_rank_le_two

/-! **BG Theorem A — ungated conjuncts** (`S16_MainResults`, `theoremA_ungated_conjuncts`):
`M_σ` is a `σ`-Hall, `Kstar ≠ ⊥`, and `M_F ≤ M_σ ≤ M'`.  Standalone bundle of the four conjuncts of
the faithful Theorem A whose upstreams are all proved transitively; the genuinely new content
is `Kstar ≠ ⊥`, unblocked once Proposition 14.2 (`S14.typeP_structure`) landed sorry-free.
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.theoremA_ungated_conjuncts

/-! **BG Theorem A(5), element form** (`S14_TypePCounting`, `typeP_centralizer_kappaElement_eq`):
for a type-`P` `M` with cyclic Hall `κ`-subgroup `K`, the `M`-centralizer of every `k ∈ K#` is
`K ⊔ K*` (BG's `C_M(k) = K × K*`).  Sharpens Proposition 14.2(b1) (rank-one normalizer) to the
element-wise centralizer via the order-`p` subgroup of `⟨k⟩` and `C_G(k) ≤ C_G(X) ≤ N_G(X)`.
Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_centralizer_kappaElement_eq

/-! **BG Theorem A(4)** (`S14_TypePCounting`, `typeP_hall_inf_centralizer_kappaElement_eq_bot`):
`C_U(k) = 1` for `k ∈ K#`.  Faithfulness resolution (issue 8017): the conclusion holds for **every**
`(κ ∪ σ)'`-Hall `U ≤ M`, not just the `K`-invariant complement, because it reduces (via
`typeP_centralizer_kappaElement_eq`) to the `U`-independent `C_M(k) = K ⊔ K*` plus coprimality of
`|U|` with `|K ⊔ K*| = |K|·|K*|`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP_hall_inf_centralizer_kappaElement_eq_bot

/-! **BG `defUK`** (`S14_TypePCounting`, `typeP2_kappaHall_commutator_eq_self`): for a type-`P₂`
maximal `M` with cyclic Hall `κ`-subgroup `K` and abelian `(κ∪σ)'`-Hall complement `U` normalized
by `K`, `⁅U, K⁆ = U`.  The coprime decomposition `U = (C(K)⊓U) ⊔ ⁅U,K⁆`
(`fitting_coprime_abelian_decomp`) collapses because `C_U(K) = ⊥` (Theorem A(4) at any `k ∈ K#`).
A signalizer-functor prerequisite for BG Cor 14.12 (`typeP2_neighbor_is_typeF`).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP2_kappaHall_commutator_eq_self

/-! **BG `kappaJ` / type conjugation-invariance** (`S14_TypePCounting`): `κ(M^g) = κ(M)`
(`kappa_conj_smul`) and the type predicates `IsTypeP`/`IsTypeP1`/`IsTypeP2` transfer under
conjugation (`isTypeP{,1,2}_conj_smul`).  Each `κ`-condition (`τ₁∪τ₃ = {p ∉ σ ∧ r_p=1}`, the
rank-one centralizer witness) is conjugation-stable via `σ`/`M_σ`/`pRank`/`ℰ_p¹`/centralizer
equivariance.  Prerequisite for BG Cor 14.12 (`sK_FD`).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.kappa_conj_smul
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.isTypeP1_conj_smul
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.isTypeP2_conj_smul

/-! **BG Corollary 14.12** (`S14_TypePCounting`, `typeP2_neighbor_is_typeF`): for `M ∈ 𝓜_{P₂}`,
the κ-Hall `K`, abelian `(κ∪σ)'`-Hall `U` (Prop 14.2(a)) normalized by `K`, `r ∈ π(U)`, `R` the
Sylow `r`-subgroup of `U`, and `H ∈ 𝓜(N_G(R))`: then `H ∈ 𝓜_F`, `U ≤ M_σ(H)`, `M ⊓ H = U ⊔ K`,
and `N_H(U) ⊄ M` (the FT-path clause for BG Theorem C(1)).  Translates Coq `P2type_signalizer`
(BGsection14.v L2243): `H` type-`F` (no covering partner is conjugate to `H`); `U ⊆ M_σ(H)` via the
`HsDq = M_σ(H)·O_q(F(E))` machinery; conjunct 3 via the σ-decomposition `M = M_σ ⋊ (U⊔K)`,
`C_{M_σ}(U) = 1` (Lemma 14.1), and BG 6.5(b) `N_M(U) = U⊔K`; conjunct 4 via the normalizer
condition in the nilpotent `Fu = O_{(κ∪σ)'}(F(H))`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.typeP2_neighbor_is_typeF

/-! **Matched `κ`-Hall / `(κ∪σ)'`-Hall pair for type-`P₂`** (`S16_MainResults`,
`typeP2_exists_matched_kappa_hall_pair`): the BG `kappa_complement` Frobenius factorisation
`E = K ⋉ U` of Proposition 14.2(a), giving a `κ(M)`-Hall `K₀` and a nontrivial abelian
`(κ(M)∪σ(M))'`-Hall `U₀` (both `≤ M`) with `K₀ ≤ N_G(U₀)` — since `U₀ = E₂E₃ ◁ E ∋ K₀`.  Type-`P₂`
excludes the degenerate `κ`-group cases of the `E`-setup; `U₀` is identified as `[E:E₁]` and shown
`(κ∪σ)'`-Hall via the index of the `κ`-Hall `E₁`, abelian by Lemma 15.1(b).  The matched pair that
Corollary 14.12 consumes via its `K ≤ N(U)` hypothesis.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeP2_exists_matched_kappa_hall_pair

/-! **`TypePData M` for a type-`P₂` maximal subgroup** (`S16_MainResults`, `typePData_of_isTypeP2`,
issue 7007): every type-`P₂` maximal subgroup carries a Peterfalvi type-`P` datum, `sorry`-free.
The carrier-constructibility milestone for Proposition 16.1's forward bridges: the matched pair
`typeP2_exists_matched_kappa_hall_pair` (abelian `U`, `K ≤ N(U)`) and the `M_F`-internal Fitting
decomposition `typeP2_mf_internal_fitting_decomposition` (the three deep `M'`-complement/Fitting
fields) together fully discharge the gated-endpoint constructor `typePData_of_isTypeP_of_inputs`.
This closes the deep `M_F`-internal residuals gating all three (`hP2II`/`hP1neIIIIV`/`hP1eqV`)
forward bridges; `hP2II` now reduces to the type-`II` last mile (`isTypeII_of_typePData`).
Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typePData_of_isTypeP2

/-! **Type-`P₁` structure: `M' = M_σ`, `F(M) = M_F`, and the type-V `TypePData`** (`S16_MainResults`,
issue 8015, the FT-critical `hP1eqV` forward bridge).  For a type-`P₁` maximal subgroup the Hall
`(κ ∪ σ)'`-complement is trivial, so Lemma 15.1(b) collapses to `M' = M_σ`
(`isTypeP1_derivedInG_eq_Msigma`); when additionally `M_F = M_σ`, Corollary 15.5(d) (`F(M) ≤ M'`)
plus `M_F ≤ F(M)` give the type-V Fitting collapse `F(M) = M_F`
(`fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma`).  Together these fully
construct the type-V Peterfalvi datum `typePData_of_isTypeP1_mf_eq_msigma` (`U = ⊥`), the
carrier-constructibility milestone reducing `hP1eqV` to the lone Peterfalvi (8.8) trichotomy
residual.  All three axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma
#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typePData_of_isTypeP1_mf_eq_msigma

/-! **Type-V trichotomy common part** (`S16_MainResults`, issue 8015, the `hP1eqV` (8.8) residual):
the two proved building blocks of the Peterfalvi (8.8) `(e2)/(e3)` disjunction.  `M_F` is non-abelian
for any type-V maximal (`not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma`: the datum's
`W₂ ⊆ M'' = (M_F)'` is nontrivial, the Coq abelian-`H` exclusion), and `¬FittingIsTI` yields a
witness prime `p ∈ π(M_F)` with cyclic `O_{p'}(M_F)`
(`exists_prime_cyclic_opiCore_compl_of_isTypeV`: the shared non-TI witness
`exists_inf_conj_fitting_orderP_witness` fed to the `cycHp'` block).  These reduce the `hP1eqV`
trichotomy to the lone `|W₁| ∣ p ∓ 1` `W₁`-action divisibility.  Both axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma
#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.exists_prime_cyclic_opiCore_compl_of_isTypeV

/-! **Type-V trichotomy disjunct (e2) — the `|W₁| ∣ p − 1` Frobenius divisibility** (`S16_MainResults`,
issue 8015): the two engines that close disjunct 2 of the Peterfalvi (8.8) `(e2)/(e3)` dichotomy.
`C_{M_σ}(k) = K*` for `k ∈ K#` (`centralizer_msigma_kappaElement_eq_kstar`: `K` acts primely on `M_σ`,
Proposition 14.2, so the fixed points are constant `= K*`), and a `κ`-Hall `K` normalizing an
`M`-normal order-`p` subgroup `Z ≤ M_σ` with `Z ⊓ K* = ⊥` acts on `Z` as a Frobenius group, giving
`|K| ∣ p − 1` (`kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot`, via
`card_dvd_sub_one_of_isFrobeniusAction`).  These reduce the `hP1eqV` trichotomy residual to the lone
deep `(e3)` Singer/`SL₂(p)` case `Z ≤ K*` (`|O_p(M_F)| = p³`, `|W₁| ∣ p + 1`).  Both axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.centralizer_msigma_kappaElement_eq_kstar
#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot

/-! **Type-V disjunct-3 faithfulness brick** (`S16_MainResults`,
`kappaHall_inf_centralizer_opiCore_eq_bot`, issue 8015): in the Singer `(e3)` case the cyclic `κ`-Hall
`K` acts *faithfully* on `P = O_p(M_F)`, i.e. `K ⊓ C_G(P) = ⊥` (Coq `tiKcP`/`defKs`).  A nonidentity
`x ∈ K ⊓ C_G(P)` would centralize `P ⊇ X₁`, forcing `X₁ ≤ M_σ ⊓ C_G(x) = K* = Z`
(`centralizer_msigma_kappaElement_eq_kstar` + `kstar_card_prime_of_inputs`, `|K*| = p = |Z|`),
contradicting `X₁ ⊄ Z`.  This is the faithfulness input to `pRank_opiCore_le_two_of_kappaHall`
(`rPle2`).  Axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.kappaHall_inf_centralizer_opiCore_eq_bot

/-! **Type-V disjunct-3 Sylow input** (`S16_MainResults`, `exists_sylow_eq_opiCore_of_mf_eq_msigma`,
issue 8015): for `M_F = M_σ` and `p ∈ σ(M)`, `P = O_p(M_F)` is a Sylow `p`-subgroup of `G` (Coq
`sylP_G`).  `P` is a `{p}`-Hall (Sylow) of the nilpotent `M_F = M_σ`, so `|P| = p^{v_p(|M_σ|)}`; as
`M_σ` is the `σ`-Hall with `p ∈ σ`, this is `p^{v_p(|G|)}`, and `Sylow.ofCard` exhibits the Sylow.
This is the Sylow input to `mFT_rank2_Sylow_cprod` (`card_opiCore_eq_prime_cube_singer`).
Axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.exists_sylow_eq_opiCore_of_mf_eq_msigma

/-! **Type-V disjunct-3 centre order** (`S16_MainResults`,
`card_center_opiCore_eq_prime_of_omega1Center_le_kstar`, issue 8015): `|Z(O_p(M_F))| = p` (Coq
`defZP`/`oZ0`).  The cyclic `κ`-Hall `K` centralizes `Ω₁(Z(P)) = K*`, so by **BG Theorem 1.11**
(`actsTrivially_on_of_fixes_omega1`, coprime `Ω₁`-rigidity, Gorenstein 5.3.10 — already ported) `K`
centralizes all of `Z(P)`; then `Z(P) ≤ M_σ ⊓ C(K) = K* = Ω₁(Z(P)) ≤ Z(P)`, so `Z(P) = Ω₁(Z(P))`
has order `p`.  This is the `|Z(P)| = p` input collapsing the `mFT_rank2_Sylow_cprod` central product
to `|P| = p³` (`card_opiCore_eq_prime_cube_singer`).  Axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.card_center_opiCore_eq_prime_of_omega1Center_le_kstar

/-! **Type-V disjunct-3 `|O_p(M_F)| = p³`** (`S16_MainResults`, `card_opiCore_eq_prime_cube_singer`,
issue 8015): the order of `P = O_p(M_F)` in the Singer case (BG Theorem 15.7(e), Coq `dimP`/`oP`).
All four inputs are discharged — `r(P) ≤ 2` (`pRank_opiCore_le_two_of_kappaHall`), `P` non-abelian,
`P` Sylow of `G` (`exists_sylow_eq_opiCore_of_mf_eq_msigma`), `|Z(P)| = p`
(`card_center_opiCore_eq_prime_of_omega1Center_le_kstar`) — and the **Blackburn rank-2 Sylow
central-product structure** (`S10.sylow_structure`, Cor 10.7(b)) gives `P = P₁ ∘ P₂` with `P₁`
extraspecial of order `p³` and `P₂` cyclic; `|Z(P)| = p` collapses the cyclic factor `P₂ = Z(P₁)` into
`P₁`, leaving `|P| = |P₁| = p³`.  This closes the first of the two type-V `(e3)` residuals.
Axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.card_opiCore_eq_prime_cube_singer

/-! **Type-V disjunct-3 route-B final arithmetic (L5)** (`S16_MainResults`,
`card_dvd_of_injective_to_cyclic_forall_pow`, issue 8015): if a finite group `K` embeds into a finite
cyclic group `C` with every image an `n`-th root of unity, then `|K| ∣ n`.  In the Singer application
`C = 𝔽_{p²}ˣ` and `μ k ^ (p+1) = 1` is the determinant-one (`= N(μ k) = μ(k)^{p+1}`) symplectic
condition, giving `|W₁| = |K| ∣ p+1`.  The reusable last step of the `(e3)` Singer divisibility;
axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.card_dvd_of_injective_to_cyclic_forall_pow

/-! **Type-`P₁` `M_F`-internal complement** (`S16_MainResults`, `exists_typeP1_mf_complement`, the
construction core of the FT-critical `hP1neIIIIV` bridge): `M_F` has a `K`-invariant complement `U`
inside `M' = M_σ` (`M_F ⊔ U = M'`, `K ≤ N_G(U)`, `M_F ⊓ U = ⊥`).  The `K`-invariant
Schur–Zassenhaus complement (`exists_aInvariant_complement_within_normal`) applied to the `σ`-Hall
`M' = M_σ`, with `M_F ◁ M` Hall in `M'` (index-divisibility transfer) and `K` (`σ'`-group) acting
coprimely.  Discharges the `hUle`/`hKnorm`/`hDcompl`/`U ≠ ⊥` `TypePData` fields; the residual fields
(`U` nilpotent `= M'/M_F` nilpotent, the `F(M)` decomposition) and `N_G(U) ⊆ M` are the deep Coq
`Fcore_structure` content.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.exists_typeP1_mf_complement

/-! **Type-`P₁` (`M_F ≠ M_σ`) `M_F`-complement is nilpotent** (`S16_MainResults`,
`isNilpotent_complement_of_isTypeP1_mf_ne_msigma`): any complement `U` of `M_F` inside `M' = M_σ`
(`M_F ⊔ U = M'`, `M_F ⊓ U = ⊥`) is nilpotent.  Theorem 15.2 (`mf_ne_msigma_typeP1_structure`)
supplies `Q ⋊ D = M_σ` with `Q ≤ M_F` and `D` nilpotent, so `M_σ/M_F` is the nilpotent image of `D`
(`Group.nilpotent_of_surjective`); the restricted quotient map `Ū → M_σ/M_F` is bijective, so `U` is
nilpotent.  Discharges the `U` nilpotent residual `TypePData` field deferred by
`exists_typeP1_mf_complement` (the deferred half of Corollary 15.5(c)) for the `hP1neIIIIV` bridge.
Axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.isNilpotent_complement_of_isTypeP1_mf_ne_msigma

/-! **`M_F`-complement is a genuine `M'`-complement** (`S16_MainResults`,
`isComplement'_mf_complement_of_sup_inf`): `M_F ⊔ U = M'` and `M_F ⊓ U = ⊥` give
`IsComplement' (M_F.subgroupOf M') (U.subgroupOf M')`.  `M_F.subgroupOf M'` is normal in `↥M'`
(`M' ≤ M ≤ N_G(M_F)`); the second isomorphism theorem (`relIndex_sup_right`) plus disjointness give
`[M':M_F] = |U.subgroupOf M'|`, hence `|M_F.subgroupOf M'|·|U.subgroupOf M'| = |M'|`, and
`isComplement'_of_card_mul_and_disjoint` concludes.  Discharges the deepest non-Fitting `U`-field
(`hDcompl`) of the type-`P₁` (`M_F ≠ M_σ`) `TypePData` gated by `exists_typeP1_mf_complement`.
Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isComplement'_mf_complement_of_sup_inf

/-! **Coprime inner-induced conjugation is trivial** (`S16_MainResults`,
`mem_centralizer_of_inner_conj_of_coprime`): if `x` normalizes `N`, `orderOf x` is coprime to `|N|`,
and conjugation by `x` agrees on `N` with conjugation by some `n ∈ N` (inner), then `x ∈ C_G(N)`.
The induced automorphism `φ(x) = φ(n) ∈ Inn(N)` (via `normalizerMonoidHom`) has order dividing both
`orderOf x` and `|N|`; coprimality forces `φ(x) = 1`, i.e. `x ∈ ker = C_G(N)`.  Reusable
coprime-action core of the type-`P₁` `M_F`-internal Fitting decomposition.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.mem_centralizer_of_inner_conj_of_coprime

/-! **Type-`P₁` (`M_F ≠ M_σ`) `M_F`-internal Fitting decomposition** (`S16_MainResults`,
`fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma`, BG Corollary 15.5): for a type-`P₁`
maximal `M` with `M_F`-complement `U` in `M' = M_σ`, `F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.  `F(M)` is
nilpotent with `M_F` normal Hall (so `F(M) = M_F ⊔ (U ⊓ F(M))` by the Dedekind law); the crux
`U ⊓ F(M) ⊆ C(M_F)` is the coprime-action core (`mem_centralizer_of_inner_conj_of_coprime`) applied
to the `F(M) = C_M(M_F)·M_F` factorisation.  Discharges the `hFiteq`/`hSDfit` residuals.
Axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma

/-! **`TypePData M` for a type-`P₁` maximal subgroup with `M_F ≠ M_σ`** (`S16_MainResults`,
`typePData_of_isTypeP1_mf_ne_msigma`): the type III/IV carrier-constructibility milestone — every
such maximal subgroup carries a Peterfalvi type-`P` datum, `sorry`-free.  The `K`-invariant
`M_F`-complement `U` (`exists_typeP1_mf_complement`) is fed to `typePData_of_isTypeP_of_inputs` with
the four deep `U`/Fitting fields discharged by the new BG Corollary 15.5 lemmas
(`isNilpotent_complement_…`, `isComplement'_mf_complement_…`,
`fittingInAmbient_eq_mf_sup_inf_…`).  Mirrors `typePData_of_isTypeP2`; together they construct the
type-`P` datum for every non-type-V type-`P` maximal, leaving the `hP1neIIIIV` bridge gated only on
the type III/IV last mile `N_G(U) ⊆ M`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typePData_of_isTypeP1_mf_ne_msigma

/-! **Type-`P₁` (`M_F ≠ M_σ`) `TypePNontrivialCore`** (`S16_MainResults`,
`typePData_nontrivialCore_of_isTypeP1_mf_ne_msigma`): the common type II--IV hypotheses
(`U ≠ ⊥`, `|W₁|` prime, `M_F#` `TI`) of a type-`P₁` (`M_F ≠ M_σ`) `TypePData` with `U ≠ ⊥`.
`|W₁| = [M:M'] = |K| = p` prime from Theorem A(8) (`theoremA8_structure`); `M_F#`-`TI` from the
`FittingIsTI M` clause (`fitting_isTI_of_mf_ne_msigma`).  Discharges the `hcommon` input of the type
III/IV last mile `isTypeIII_or_IV_of_typePData`.  Axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.typePData_nontrivialCore_of_isTypeP1_mf_ne_msigma

/-! **`hP1neIIIIV` bridge COMPLETE** (`S16_MainResults`, issue 8015): *every* type-`P₁` maximal
subgroup with `M_F ≠ M_σ` is of type III or IV — `isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma` is now
fully `sorry`-free and axiom-clean.  The former Peterfalvi (8.7) / Coq `Fcore_structure` residual
`N_G(U) ⊆ M` is discharged via the Coq `typePfacts` argument: a prime `p ∣ |U|`, the unique Sylow
`p`-subgroup `P̄` of the nilpotent complement `U` (so `N_G(U) ≤ N_G(P̄)`,
`normalizer_le_normalizer_map_sylow_of_isNilpotent`), and the fact that `P̄` is a `σ`-Sylow of `M`
(`typeP1_complement_mem_sigma_and_factorization`), whence `N_G(P̄) ≤ M`
(`normalizer_sylow_map_le_of_mem_sigma`).  Two reusable axiom-clean helpers plus the bridge. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.normalizer_le_normalizer_map_sylow_of_isNilpotent
#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.typeP1_complement_mem_sigma_and_factorization
#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma

/-! **`hP2II` reduced to the `M'`-type-`F` residual** (`S16_MainResults`,
`isTypeII_of_isTypeP2_of_derived_typeF`, issue 7007): a type-`P₂` maximal subgroup whose derived
subgroup `M'` is type `F` (with `F(M') = M_F`) is type II.  Discharges every `isTypeII_of_typePData`
input that is BG-local for type `P₂` — the whole `TypePNontrivialCore` (`U ≠ ⊥`; `|W₁|` prime and
the `M_σ`-`TI` both from Proposition 14.2(g), since `M_F = M_σ`), `U` abelian, and `N_G(U) ⊄ M`
(Corollary 14.12) — leaving exactly the deep `M'`-type-`F` structure as hypotheses.  Corrects the
stale belief that `|W₁|` prime is lane-b (10.11)-gated: that is the *partner* primality, not the
type-`P₂` `κ`-Hall's.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2_of_derived_typeF

/-! **`hderF` complete + `hP2II` COMPLETE** (`S16_MainResults`, issue 7007 cont.¹¹): `M'` is type `F`
for every type-`P₂` maximal `M` (`isTypeF_derivedInG_of_isTypeP2`), assembling the *same* type-`F`
data as the type-`F` maximal (`M' = M_σ ⋊ U` mirrors `M = M_σ ⋊ U`): the `M_σ ⋊ U` complement
(`typeP2_mf_internal_fitting_decomposition`), abelian inertia `U₁` and Frobenius factor `M_σ ⋊ U₀`
(Lemma 15.1(d)(e)), and `(M')_F = M_σ = M_F`
(`maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2`).  Hence *every* type-`P₂` maximal is
type II (`isTypeII_of_isTypeP2`), with **no** `τ₂(M) = ∅` / Theorem 15.8 gate.  Both axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeF_derivedInG_of_isTypeP2
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2

/-! **BG Theorem C** (`S16_MainResults`, `theoremC_paired_structure`): for `K ≠ 1`, a type-`P`
maximal `M` has the full paired structure — `U` abelian; `N_G(U) ⊄ M` (conjunct 2 = BG C(1) /
Corollary 14.12, via the matched `(K₀,U₀)` pair `typeP2_exists_matched_kappa_hall_pair` and the
`M`-conjugacy transport of `(κ∪σ)'`-Hall subgroups); `K*` cyclic, `1 ⊂ K* ≤ M_F ≤ M''`, `M_F` not
cyclic; `M' = U M_σ`; the unique non-conjugate type-`P` partner `M*` (Theorem 14.7); the
`A_0(M)−A(M)` TI-set (conjunct 10); and the prime-order / `F(M)`-TI clauses (conjuncts 11, 12).
Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.theoremC_paired_structure

/-! **BG Theorem A(3) decomposition** (`S16_MainResults`, `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma`):
`M = K U M_σ` for a maximal `M` with Hall `κ`-subgroup `K ≤ M` and Hall `(κ∪σ)'`-subgroup `U ≤ M`.
Type-F via the `K = ⊥` `SubgroupESetup`; type-P via the `M' = U M_σ`/`M'`-complements-`K` structure
(`typeP_auxiliary_structure`), pushed from `M` to `G` by `subgroupOf_sup`/`subgroupOf_eq_top`.
Standalone form of conjunct 3 of `theoremA_maximal_structure_faithful`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeP_maximal_eq_kappaHall_sup_U_sup_Msigma

/-! **BG Theorem A(7), first clause** (`S16_MainResults`, `derivedDerived_le_fittingInAmbient`):
`M'' ⊆ F(M)` for any maximal `M`.  No longer `M_F ≠ M_σ`-gated (issue 8012): the `M_F = M_σ` branch
runs `M'' ≤ M_σ ≤ M_F ≤ F(M)` (`derivedDerived_le_Msigma` + `M_σ` nilpotent), the type-`P₁` branch
cites Theorem 15.2 (`mf_ne_msigma_typeP1_structure`).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.derivedDerived_le_fittingInAmbient

/-! **BG Theorem A — faithful monolith** (`S16_MainResults`, `theoremA_maximal_structure_faithful`):
all 11 conjuncts of BG Theorem A, `sorry`-free.  This canonical form includes the explicit
`K ≤ M`, `U ≤ M` of the BG setup
`M = K U M_σ`, making A(3)/A(4)/A(8) provable).  Assembled from `theoremA_ungated_conjuncts`,
`typeP_maximal_eq_kappaHall_sup_U_sup_Msigma`, `derivedDerived_le_fittingInAmbient`, and
`theoremA8_structure`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.theoremA_maximal_structure_faithful

/-! **Proposition 16.1 input `hF_not_derived`** (`S16_MainResults`, `typeF_not_exists_hall_derived_eq`):
a type-`F` maximal subgroup has no `(κ∪σ)'`-Hall `U` with `M' = U M_σ` (else `M = U M_σ = M'`
contradicts `M' < M`).  Powers Proposition 16.1 clause (e).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeF_not_exists_hall_derived_eq

/-! **Proposition 16.1 input `hP_derived` / BG Theorem C(3)** (`S16_MainResults`,
`typeP_exists_hall_derived_eq`): a type-`P` maximal subgroup has a `(κ∪σ)'`-Hall `U` with
`M' = U M_σ` (constructed `K`/`U`, `K ≠ ⊥` from type-`P`, then `typeP_hall_derived_eq_and_abelian`).
Powers Proposition 16.1 clause (e).  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeP_exists_hall_derived_eq

/-! **`W₂ = C_{M'}(W₁#)` centralizer law** (`S16_MainResults`,
`typeP_derivedInG_inf_centralizer_kappaElement_eq`): for type-`P` `M` with cyclic `κ`-Hall `K`,
`M' ⊓ C(k) = K* = C_{M_σ}(K)` for `k ∈ K#`.  Theorem A(5) (`C_M(k) = K ⊔ K*`) intersected with `M'`
via the Dedekind law (`eq_sup_inf_of_le_normalizer`, `K* ≤ M'`, `K ⊓ M' = ⊥`).  Discharges the
`hCentW1` field of the `TypePData` constructor.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq

/-! **Prop 16.1(b)--(d) forward bridge — `TypePData` constructor** (`S16_MainResults`,
`typePData_of_isTypeP_of_inputs`): builds `TypePData M` from BG-local `IsTypeP M` + a nontrivial
`κ`-Hall `K`, discharging 12 of 18 `typePData_of_inputs` fields from `typeP_duality`/`typeP_kstar_in_mf`
/the centralizer law, gating only on the deep `M_F`-internal Fitting core (BG Cor 15.5).  The
foundation feeding all three forward bridges hP2II/hP1neIIIIV/hP1eqV.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typePData_of_isTypeP_of_inputs

/-! **Prop 16.1 reverse — `r_q(M) = 1` machinery + type V ⟹ type P** (`S16_MainResults`, issue 8015
W1 frontier, relane #9): the `π(W₁) ⊆ κ(M)` rank-one ingredient for the reverse type bridges.
`typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived`: for a type-`P` datum and `q ∤ |M'|`,
every elementary abelian `q`-subgroup of `↥M` is cyclic (it embeds in the cyclic abelianization
`↥M ⧸ M' ≃* ↥W₁` via the `M_complement` field).  `typePData_pRank_eq_one_of_not_dvd_card_derived`:
hence `r_q(M) = 1` for `q ∣ |W₁|, q ∤ |M'|`.  `isTypeP_of_isTypeV`: a structurally type-`V` maximal
subgroup is BG type `P` — `U = ⊥` makes `M' = M_F` Hall, so `q ∤ |M'|` for all `q ∣ |W₁|`, giving the
rank-one input for `typePData_kappa_nonempty_of_rank1`.  All axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typePData_pRank_eq_one_of_not_dvd_card_derived
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeP_of_isTypeV

/-! **Prop 16.1 reverse — types II–IV ⟹ type P + `IsTypeNonI ⟹ IsTypeP`** (`S16_MainResults`, issue
8015 W1 frontier, relane #9): the `q`-element fixed-point machinery closing the rank-one gate for
prime `|W₁|`.  `prime_dvd_card_inf_centralizer_of_mem_normalizer`: a `q`-element `x` normalizing `N`
with `q ∣ |N|` has `q ∣ |C_N(x)|` (conjugation action `conjActionOfMemNormalizer`,
`IsPGroup.card_modEq_card_fixedPoints`).  `typePData_not_dvd_card_W2_of_card_W1_prime`: prime
`q = |W₁|` ⟹ `q ∤ |W₂|` (cyclic `W = W₁W₂`).  `isTypeP_of_typePData_of_card_W1_prime`: chains these
to `q ∤ |M'|` (`centralizer_W1`: `C_{M'}(x) = W₂`) ⟹ `r_q(M) = 1` ⟹ `κ(M) ≠ ∅`.
`isTypeP_of_isType{II,III,IV}` + `isTypeP_of_isTypeNonI`: the assembled reverse `IsTypeP` halves of
Proposition 16.1 clauses (b)–(d) `.mp` — exactly what `not_isTypeI_of_isTypeNonI` consumes (P₁/P₂
refinement discarded).  All axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.prime_dvd_card_inf_centralizer_of_mem_normalizer
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typePData_not_dvd_card_W2_of_card_W1_prime
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeP_of_typePData_of_card_W1_prime
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeP_of_isTypeII
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeP_of_isTypeIII
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeP_of_isTypeIV
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI

/-! **BG Proposition 16.1 — type-`P` data construction layer** (`S16_MainResults`): the shared
`TypePData` core and the type II/III/IV/V "last-mile" bridges feeding
`proposition_type_classification`'s forward bridges.

* `normalizer_eq_sup_of_isTISubset_of_isCyclic` — the genuine `normalizer_V` reduction (Peterfalvi
  (8.4)): a nonempty subset of the exceptional set `V = W ∖ (W₁ ∪ W₂)` of a cyclic `W = W₁ ⊔ W₂`
  that is `TI` relative to `W` is normalized exactly by `W`.  Pure group theory, unconditional.
* `typePData_of_inputs` — assembles `TypePData M` from the BG-local structural facts (taken as
  named hypotheses, the gated-endpoint pattern), deriving `W₁/W₂`-cyclicity and `normalizer_V`.
* `isTypeIII_or_IV_of_typePData` / `isTypeII_of_typePData` / `isTypeV_of_typePData` — the
  type-specific bridges wrapping a `TypePData` into the shared Peterfalvi type predicates.

Each is axiom-clean: the deep §14/§15 content is held abstract in the hypotheses, so the engines
themselves cite no `sorry`. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.normalizer_eq_sup_of_isTISubset_of_isCyclic
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typePData_of_inputs
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeIII_or_IV_of_typePData
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeII_of_typePData
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeV_of_typePData

/-! **Proposition 16.1(a) `hFI` infrastructure** (`S16_MainResults`): the self-normalizing helpers
and the TI case of the type-I `alternative` trichotomy (Peterfalvi (8.3)(a)).

* `normalizer_eq_self_of_subgroupOf_normal_of_ne_bot` — a nontrivial `M`-normal subgroup of a
  maximal subgroup of a minimal simple group is self-normalizing (`N_G(H) = M`), generalizing
  `normalizer_Msigma_eq_self`.
* `normalizer_fittingInAmbient_eq_self` — the `H = F(M)` instance, `N_G(F(M)) = M`.
* `maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI` — `FittingIsTI M ⟹ M_F#` is a `TI`-subset
  (the first disjunct of `TypeIData.alternative` in the `F(M)`-TI case of `hFI`).

All three are unconditional / axiom-clean.  **The full `hFI` bridge `isTypeI_of_isTypeF` (type `F ⟹`
type I) is now axiom-clean**, together with its `TypeFData` construction `typeFData_of_kappa_eq_bot`
and the wrapper `isTypeF_groupTheory_of_isTypeF`: both former gates are closed — the non-TI residual
(BG Theorem 15.7(e)) by the per-prime witness `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`
(registered above), and the Theorem A dependency by routing `typeFData_of_kappa_eq_bot`'s A(3)/A(8)
through `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma` + `isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot`
(Thm 15.2) instead of the retired bare overstatement. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeFData_of_kappa_eq_bot
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeF_groupTheory_of_isTypeF
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeI_of_isTypeF
-- Prop 16.1(a) reverse bridge `hIF` (type I ⟹ `κ(M) = ∅`), now fully `sorry`-free: the type-`F`
-- Frobenius FPF against a `U₀`-element (`M_F ⊓ C_G(X) = ⊥` for `X ≤ U₀`), the `κ`-element placement
-- (`p ∈ κ ⟹ ∃ X ≤ U₀` `p`-group `⊆ κ`-Hall `K`, via Hall-D), and the assembled bridge.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeFData_fitting_inf_centralizer_eq_bot
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeFData_exists_kappaElement_le_kappaHall
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isTypeF_of_isTypeI
-- The FT-critical consumer `not_isTypeI_of_isTypeNonI` (a non-Type-I maximal is not Type I), now
-- axiom-clean: it routes through `isTypeF_of_isTypeI` + `isTypeP_of_isTypeNonI` only, no longer
-- citing the `sorry`-bearing §16 type-classification reverse bridges.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI
-- **Prop 16.1 reverse bridges `hIIP2` / `hIIIIVP1` / `hVP1` — the type II/III/IV/V mutual-exclusivity
-- layer, now fully `sorry`-free + axiom-clean.**  `not_isTypeV_of_typePData_U_ne_bot` (the `U = ⊥`
-- core, generalising `not_isTypeII_of_isTypeV`) gives `III/IV ≠ V`; `typePData_exists_conj_U`
-- (Schur–Zassenhaus inside `↥M'`: both `U` complement the nilpotent normal Hall `M_F`, coprime) and
-- `typePData_normalizer_U_le_iff` (normalizer transfer) give `II ≠ III/IV`
-- (`not_isTypeII_of_isTypeIII_or_IV`).  These refine `IsTypeNonI ⟹ IsTypeP` (`= P₁ ∨ P₂`) to the
-- exact type, closing the last two bridges — so **`proposition_type_classification` (BG Prop 16.1) is
-- fully `sorry`-free and axiom-clean.**
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.not_isTypeV_of_typePData_U_ne_bot
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.not_isTypeII_of_isTypeV
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.not_isTypeV_of_isTypeIII_or_IV
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typePData_exists_conj_U
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typePData_normalizer_U_le_iff
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.not_isTypeII_of_isTypeIII_or_IV
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.proposition_type_classification
-- Peterfalvi (8.10)/(8.11) `M_s = M_σ` bridges (issue 8020): from Prop 16.1 clauses (c)/(f)
-- + `isTypeP1_derivedInG_eq_Msigma`.  Turn BG's `M_σ`-stated Theorem E into the `mainSubgroup`-form
-- `BGTheoremECoverData` needs.  Axiom-clean exactly because Prop 16.1 is.
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.A1_eq_sigmaSharp
-- Every maximal subgroup has a Peterfalvi type (exhaustiveness of I–V): from Prop 16.1 over the
-- exhaustive BG trichotomy F/P₁/P₂.  Supplies `BGTheoremECoverData.tau`/`typed` (issue 8020).
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.exists_peterfalviType
-- Signalizer maximal's Fitting = its σ-core (`(N[x])_F = (N[x])_σ`, type F/P₂): the identity making
-- Peterfalvi's (8.14) `R(x) = C_{(N[x])_F}(x)` coincide with BG `Rsub = (N[x])_σ ⊓ C_G(x)` (issue 8020).
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2
-- 15.7(e) conjunct A divisibility engine (Coq `regZq_dv_q1`): a `U0`-invariant order-`q` subgroup
-- of the Frobenius kernel `M_F` forces `exp U ∣ q - 1` (Frobenius semiregular action).
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.typeF_exponent_dvd_sub_one_of_invariant_card

/-! # Peterfalvi Appendices (Lane H)

Axiom-cleanliness guards for the sorry-free Peterfalvi-appendix results
(`OddOrder/Peterfalvi/Appendices/`).  Only fully unconditional, axiom-clean declarations are
registered here; results still conditional on an open `sorry` (e.g. Appendix I's Lemma
non-cyclic case, deferred to Gorenstein 5.4.10 / issue 2004) are intentionally absent. -/

/-! **Peterfalvi, Appendix I (Huppert), Proposition 2(a)** (`SemilinearField`): a commutative
group `T` acting irreducibly on an elementary abelian `p`-group `E` yields a finite field
`F = 𝔽_p[T] = End_{𝔽_p[T]}(E)` over which `E` is `1`-dimensional, with `|F| = |E|`.  The abstract
core (`End_{k[T]}(M)` is a field, `M` is `1`-dimensional, `|End| = |M|`) plus the bridge from the
group-theoretic data.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.Peterfalvi.Appendices.Huppert.isSimpleModule_end

#assert_only_allowed_axioms OddOrder.Peterfalvi.Appendices.Huppert.finrank_end_eq_one

#assert_only_allowed_axioms OddOrder.Peterfalvi.Appendices.Huppert.natCard_end_eq

#assert_only_allowed_axioms OddOrder.Peterfalvi.Appendices.Huppert.exists_field_of_irreducible

/-! **Peterfalvi, Appendix I (Huppert), Proposition 2(a)+(b)** (`SemilinearField`): the field `F`
of part (a) together with the semilinearity of part (b) — every `g : MulAut E` normalizing the
`T`-action (via some `c : T ≃* T`) acts `F`-semilinearly, with field automorphism
`σ = conjugation by g` on `F = End_{𝔽_p[T]}(E)`.  This is the input Appendix II uses for the
field automorphisms `σ_y`.  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms OddOrder.Peterfalvi.Appendices.Huppert.exists_field_semilinear

/-! **Peterfalvi, Appendix II (Near-Fields), Proposition 2 — irreducibility/counting + field
structure** (`NearFields`).  The orbit-counting engine (`add_one_le_card_of_aInvariant_ne_bot`: an
`A`-invariant `U ≠ ⊥` has `|A| + 1 ≤ |U|`), the elementary-abelian Maschke split
(`exists_aInvariant_complement_of_elementaryAbelian`), their assembly
(`rightMulAction_irreducible_of_index_two`: a commutative index-`2` subgroup `A ⊆ Fˣ` acts
irreducibly on `(F, +)`), and the resulting unconditional field structure
(`nearField_field_structure_of_index_two`).  Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.Peterfalvi.Appendices.NearFields.add_one_le_card_of_aInvariant_ne_bot

#assert_only_allowed_axioms
  OddOrder.Peterfalvi.Appendices.NearFields.exists_aInvariant_complement_of_elementaryAbelian

#assert_only_allowed_axioms
  OddOrder.Peterfalvi.Appendices.NearFields.rightMulAction_irreducible_of_index_two

#assert_only_allowed_axioms
  OddOrder.Peterfalvi.Appendices.NearFields.nearField_field_structure_of_index_two

/-! **`M_F` is automorphism-equivariant** (`MaxNilpotentNormalHall`).  The maximal nilpotent
normal Hall subgroup `M_F` of Peterfalvi/BG is natural under any automorphism `φ` of `G`:
`φ • M_F = (φ • M)_F` (`maxNilpotentNormalHall_pointwise_smul`), with the candidate-set/subgroupOf
transport helper `map_subgroupMap_subgroupOf` and the automorphism-action equation
`pointwise_mulAut_smul_eq_map`.  Reusable building block for the BG §13 / Peterfalvi §13
conjugation arguments on `L_F`/`M_F` (e.g. the (14.12) `L ≅ M` reduction `H_cyclic_of_L_conj_M`).
Fully unconditional, axiom-clean. -/

#assert_only_allowed_axioms
  OddOrder.GroupTheory.maxNilpotentNormalHall_pointwise_smul

#assert_only_allowed_axioms
  OddOrder.GroupTheory.map_subgroupMap_subgroupOf

#assert_only_allowed_axioms
  OddOrder.GroupTheory.pointwise_mulAut_smul_eq_map

/-! **The Peterfalvi maximal-subgroup type is conjugacy-invariant** (`MaximalSubgroupTypeConj`).
Every structural datum of `TypeFData`/`TypeIData` transfers along `φ : MulAut G`
(`TypeFData.conj`, `isTypeI_pointwise_smul`), so conjugate maximal subgroups share their Peterfalvi
type (`isTypeI_of_conj`).  This is the unconditional, axiom-clean **gate-4 piece 1** infrastructure
of Peterfalvi (13.17.b).  Its downstream application
`OddOrder.Peterfalvi.S15.not_conj_of_isTypeI_of_isTypeNonI` (a type-`I` maximal subgroup is
non-conjugate to the non-I `S`, `T`) has a sorry-free *proof*; its §16 dependency
`not_isTypeI_of_isTypeNonI` is now axiom-clean (registered above), so registering it is left to the
Peterfalvi lane that owns it. -/

#assert_only_allowed_axioms
  OddOrder.GroupTheory.TypeFData.conj

#assert_only_allowed_axioms
  OddOrder.GroupTheory.isTypeI_of_conj

/-! **Frobenius-kernel fixed-point engine for Peterfalvi (9.1)/(13.17.b)** (`CoprimeAction`).
In a finite Frobenius group with kernel `N`, a non-kernel element centralizes nothing nontrivial
in `N` (`IsFrobeniusGroup.centralizer_inf_kernel_eq_bot_of_not_mem`) — the engine of the
fixed-point-free action that, with Wielandt's formula `wielandt_fixedPoint_frobenius`, forces the
Fitting kernel `L_F` to be trivial in (13.17.b).  Axiom-clean (the Wielandt corollary
`coprimeFrobeniusAction_card_eq_one` itself transitively cites the sorried Wielandt formula and is
not registered here). -/

#assert_only_allowed_axioms
  OddOrder.GroupTheory.IsFrobeniusGroup.centralizer_inf_kernel_eq_bot_of_not_mem

/-! **(9.1) I-5 chief-step multiplicativity of coprime fixed points** (`CoprimeFixedPoints`).
For a coprime solvable action `φ : L →* MulAut H`, `X ≤ L`, and an `L`-invariant normal `N ◁ H`,
the fixed points split across the chief step: `|C_H(X)| = |C_H(X) ⊓ N| · |C_{H/N}(X)|`
(`card_fixedSubgroup_eq_mul`), via the surjectivity of the reduction map onto the quotient fixed
points (`map_fixedSubgroup_eq_fixedSubgroup_quotient` = Isaacs Cor 3.28).  This is the
group-theoretic core of the chief-series assembly of Wielandt's formula (issue 2014). -/

#assert_only_allowed_axioms OddOrder.GroupTheory.card_fixedSubgroup_eq_mul
#assert_only_allowed_axioms OddOrder.GroupTheory.map_fixedSubgroup_eq_fixedSubgroup_quotient
#assert_only_allowed_axioms OddOrder.GroupTheory.isAInvariant_comp_subtype
#assert_only_allowed_axioms OddOrder.GroupTheory.fixedSubgroup_restrict_eq
#assert_only_allowed_axioms OddOrder.GroupTheory.card_fixedSubgroup_restrict
#assert_only_allowed_axioms OddOrder.GroupTheory.wielandt_card_combine
#assert_only_allowed_axioms OddOrder.GroupTheory.wielandt_step

/-! **(9.1) existence of an elementary-abelian `L`-invariant normal subgroup**
(`MinimalInvariantNormal`).  A nontrivial finite solvable `H` with an action `φ : L →* MulAut H`
has a nontrivial `L`-invariant normal `N ◁ H` that is elementary abelian
(`exists_aInvariant_normal_isElementaryAbelian`): a minimal such `N` has trivial derived subgroup
(abelian) and trivial `p`-th powers (exponent `p`), both forced by minimality applied to the
characteristic subgroups of `↥N` mapped into `H`.  This is the existence input driving the
chief-series induction of Wielandt's formula (issue 2014). -/

#assert_only_allowed_axioms OddOrder.GroupTheory.exists_aInvariant_normal_isElementaryAbelian
#assert_only_allowed_axioms OddOrder.GroupTheory.aInvariant_normal_map_of_characteristic
#assert_only_allowed_axioms OddOrder.GroupTheory.aInvariant_map_subtype_of_restrict

/-! **(9.1) chief-series assembly** (`WielandtAssembly`).  The group-level Wielandt fixed-point
identity follows from the per-chief-factor identity (`WielandtPerFactor`) by strong induction on
`|H|` (`wielandt_formula_of_perfactor`): an elementary-abelian `L`-invariant normal subgroup `N`
splits the problem via `wielandt_step`, with the per-factor identity on `N` and the induction
hypothesis on `H/N`.  This completes the *group-theoretic* layer of Wielandt's formula; the only
remaining input is the per-chief-factor identity itself (the representation-theoretic (†), lane-f).
-/

#assert_only_allowed_axioms OddOrder.GroupTheory.wielandt_formula_of_perfactor

/-! **(9.1) per-chief-factor discharge** (`WielandtPerFactorDischarge`, piece C).  The
per-chief-factor predicate `WielandtPerFactor` reduces (`wielandtPerFactor_of_dim`) to the
*dimension* identity (⋆) on each elementary-abelian chief factor (`WielandtDimIdentity`): for the
restricted action on `↥N`, `card_fixedSubgroup_wielandt_of_dim` raises the dimension identity to the
cardinality identity on `↥N`, and `card_fixedSubgroup_restrict` rewrites `|C_N(X)| = |C_H(X) ⊓ N|`.
This isolates the sole remaining representation-theoretic input — the kernel-FPF dimension identity
(†) — into the explicit hypothesis. -/

#assert_only_allowed_axioms OddOrder.GroupTheory.wielandtPerFactor_of_dim

/-! **(9.1) item 0 — conjugation permutes the isotypic projections** (`CenterProjConjugation`).
A linear automorphism `τ` of `W` intertwining `ρ : Representation k U W` with its `c`-twist carries
the `i`-th isotypic projection's range onto the `simplesAction φ c i`-th one
(`map_range_centerProj`); this is the `hperm` of the free-orbit dimension count.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.GroupTheory.CenterModuleDecomp.map_range_centerProj

/-! **(9.1) item 1 — the free `Γ`-action on the nontrivial simples** (`WielandtKernelFPF`).
Packaging `gamma_free_off_trivial_simple` (3d.3c) with the canonical induced `Γ`-actions
(`Γ` on `ConjClasses G` through `ψ`, `Γ` on `Fin N` through `simplesAction φ ∘ ψ`): there is a
simple `i₀` fixed by all of `Γ`, and `Γ` acts freely off it.  Axiom-clean (the wiring of the
kernel-FPF dimension fact (†) to the real Frobenius carrier, issue 2014). -/

#assert_only_allowed_axioms OddOrder.GroupTheory.WielandtKernelFPF.exists_fixed_simple_free_of_fpf

/-! **(9.1) item 2(g) — the trivial isotypic component is the `G`-invariants** (`WielandtKernelFPF`).
The trivial primitive central idempotent `φ.symm (Pi.single i₀ 1)` (augmentation coordinate `i₀`)
equals the averaging idempotent `GroupAlgebra.average` (`symm_single_eq_average`), so its isotypic
projection is the averaging projection and its range is the invariants
(`range_centerProj_aug_eq_invariants`); `exists_aug_coordinate` produces that coordinate.  This is
the input that drops the trivial summand in the kernel-FPF count (†) when `Wᴳ = 0`.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.GroupTheory.WielandtKernelFPF.symm_single_eq_average
#assert_only_allowed_axioms OddOrder.GroupTheory.WielandtKernelFPF.range_centerProj_aug_eq_invariants
#assert_only_allowed_axioms OddOrder.GroupTheory.WielandtKernelFPF.exists_aug_coordinate

/-! **(9.1) the kernel-FPF dimension fact (†)** over an algebraically closed field
(`WielandtKernelFPF`, item 2).  For `U ◁ L` a `p′`-group, `E ≤ L` (`U ⊔ E = ⊤`) acting on `U`
fixed-point-freely by conjugation, and a finite-dimensional `k[L]`-module `W` with `Wᵁ = 0`,
`dim W = |E| · dim Wᴱ` (`finrank_eq_card_mul_finrank_invariants_kernelFPF`).  The `U`-isotypic
decomposition drops its trivial summand (`Wᵁ = 0`), and `E` permutes the rest freely (item 1), so the
free-orbit count applies.  This is the representation-theoretic core (†) of Wielandt's formula;
`isInternal_restrict_ne` is the supporting drop-zero-summand lemma.  Axiom-clean. -/

#assert_only_allowed_axioms OddOrder.GroupTheory.WielandtKernelFPF.isInternal_restrict_ne
#assert_only_allowed_axioms
  OddOrder.GroupTheory.WielandtKernelFPF.finrank_eq_card_mul_finrank_invariants_kernelFPF

/-! **(9.1) the kernel-FPF identity (†) over `𝔽_p`, via base change** (`WielandtElabFrobenius`,
item 3 + assembly).  Base change `𝔽_p → 𝔽̄_p` transfers the algebraically-closed (†)
(`finrank_eq_card_mul_finrank_invariants_kernelFPF`) to the prime field
(`htag_of_frobenius`), discharging the `htag` of `finrank_elab_identity` and yielding the
per-chief-factor dimension identity (⋆) `wielandtDimIdentity_of_frobenius`.  **This closes the lone
representation-theoretic input of Wielandt's formula `wielandt_fixedPoint_frobenius`, which is now
fully unconditional (axiom-clean).**  Likewise its corollaries and the (13.17.b) engine. -/

#assert_only_allowed_axioms OddOrder.GroupTheory.WielandtKernelFPF.htag_of_frobenius
#assert_only_allowed_axioms OddOrder.GroupTheory.WielandtKernelFPF.wielandtDimIdentity_of_frobenius
#assert_only_allowed_axioms OddOrder.GroupTheory.wielandt_fixedPoint_frobenius
#assert_only_allowed_axioms OddOrder.GroupTheory.coprimeFrobeniusAction_card_eq_one
#assert_only_allowed_axioms OddOrder.GroupTheory.isFrobenius_kernel_eq_bot_of_frobenius_subgroup
-- Peterfalvi (9.1) kernel-centralizes corollary (ambient form): a Frobenius `U ⋊ E ≤ N_G(N)` acting
-- coprimely on a finite solvable `N` with `C_N(E) = 1` has `U ≤ C_G(N)`.  The §8-free Wielandt step
-- of (13.16): `K W₂` with `C_{Q₁}(W₂) = 1` ⟹ `K` centralizes the Maschke complement `Q₁`.
#assert_only_allowed_axioms OddOrder.GroupTheory.frobenius_kernel_centralizes_of_complement_fpf

/-! **(9.3) the order relation via Wielandt (9.1)** (`Peterfalvi.S11`).  Definition (8.4) makes
`U W₁` a Frobenius group (kernel `U`) acting coprimely on `H = M_F` (`typeP_uW1_frobenius`,
`typeP_coprimeAction`); the three fixed-point subgroups of Wielandt's formula are the concrete
centralizers (`typeP_card_fixedSubgroup`, with `C_H(W₁) = W₂` from `typeP_H_inf_centralizer_W1`),
giving the quantitative core `|C_H(U W₁)|^q · |H| = |W₂|^q · |C_H(U)|`
(`typeP_wielandt_order_relation`).  This is the Wielandt content of Peterfalvi (9.3); the
fixed-point-free §8 inputs (`C_H(U) = 1`, `|W₂|` prime, `C_H(U W₁) = 1`) are the remaining §8
obligations. -/

#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_uW1_frobenius
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_coprimeAction
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_fixedSubgroup_map
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_card_fixedSubgroup
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_H_inf_centralizer_W1
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_wielandt_order_relation

/-! **Peterfalvi (8.5.b)** (`Peterfalvi.S11`).  `U ≠ 1 ⟹ U` does not centralize `H`, *derived* from
the type-`P` data: if `U ≤ C(H)` then `F(M) = H ⊔ U = M'` is nilpotent, but `M'` is also a normal
Hall subgroup of `M` (`|M'| = |H|·|U|` coprime to `[M : M'] = |W₁|`), so `M' ≤ M_F = H`, forcing
`U ⊆ H ∩ U = 1` (`typeP_U_not_centralizes_H`).  With `C_H(U W₁) ≤ W₂` (`typeP_centralizer_uW1_le_W2`)
this discharges the `C_H(U W₁) = 1` input of (9.3) for types III/IV from `|W₂|` prime alone. -/

#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_centralizer_uW1_le_W2
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_U_not_centralizes_H

/-! **Peterfalvi (9.6) the chief-factor order** (`Peterfalvi.S11`, conditional on the (9.4) chief
factor `H̄ = H/H₀`).  The `U W₁`-action on `H = M_F` descends to the chief factor `H̄`
(`typeP_quotientCoprimeAction`, a `CoprimeFrobeniusAction`); `C_{H̄}(U)` is `U W₁`-invariant
(`isAInvariant_fixedSubgroup_of_normal`, `U ◁ U W₁`) so vanishes by irreducibility, and Wielandt's
formula together with the prime computation `coprimeFrobeniusAction_card_eq_prime_pow` gives
`|H̄| = |C_{H̄}(W₁)|^q = p^q` — using that `C_{H̄}(W₁)` is the image of the cyclic `W₂ = C_H(W₁)`
(Isaacs Cor 3.28), hence cyclic of order dividing the exponent `p`
(`card_dvd_prime_of_isCyclic_of_pow`).  The Wielandt content of (9.6) is fully discharged
(`typeP_chiefFactor_card`); the remaining gap is the (9.4) existence of the chief factor. -/

#assert_only_allowed_axioms OddOrder.GroupTheory.coprimeFrobeniusAction_card_eq_prime_pow
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.isAInvariant_fixedSubgroup_of_normal
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_quotientCoprimeAction
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.card_dvd_prime_of_isCyclic_of_pow
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_chiefFactor_card
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_U_noncentral_on_H
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.eq_top_of_forall_sylow_le
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.exists_characteristic_complement_to_sylow_of_nilpotent
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.exists_chiefFactor_seed
-- The chief-factor kernel and its elementary-abelian + `U W₁`-irreducible + `U`-noncentral
-- structure of `H̄ = H/N` is axiom-clean.  (`exists_chiefFactorData` / `chiefFactor_basic` assemble
-- it but additionally carry `typeIII_IV_p_eq_W2`, which cites the still-`sorry`'d §12 prime-order
-- result `theorem88_caseB_prime_orders`, so they are not yet axiom-clean.)
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.exists_chiefFactor_kernel
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.chiefFactor_quotient_card
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.iSup_smul_eq_top_of_irreducible
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.card_eq_pow_of_iSup_aInvariant_irreducible
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.isAInvariant_comp_subtype_pointwise_smul
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.forall_aInvariant_le_pointwise_smul
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.card_pointwise_smul
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.chiefFactor_clifford_dim_dvd_q
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.chiefFactor_clifford_U_dichotomy
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.elabRepresentation_isIrreducible
-- thin subgroup→module Singer adapter (issue 9000 dedup): the former subgroup-level Singer
-- wrappers are retired; §9 case-(b) cites the shared `SingerField`/`SingerLineBound` leaves
-- through this single conversion.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.singerAdapter_isCyclic_card_dvd
-- (9.7)(b) structural core: an irreducible action with commuting image is fixed-point-free off the
-- kernel (the Frobenius structure `H̄ ⋊ Ū`).  Pure group theory — no Singer field model needed.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.fixedPointFree_of_aInvariant_irreducible_comm
-- character-side FPF: a fixed-point-free automorphism of a finite abelian group leaves no nontrivial
-- character invariant (the inertia `I_U(θ) = C` engine of Peterfalvi (9.9)), via mathlib's
-- `commutatorMap_surjective`.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.eq_one_of_invariant_of_fixedPointFree
-- abelian `Irr ↔ Hom(·,ℂˣ)` bridge: an irreducible character of a finite commutative group is a
-- linear character (1-dim rep ⟹ scalar action ⟹ character = the scalar hom).  Lets the char-side
-- FPF engine apply to genuine `Irr(H̄)` characters (realization-free inertia route for (9.9)).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative
-- (9.9.a) character-side inertia `I_U(θ) ⊆ C`: a nontrivial irreducible character of the chief
-- factor `H̄`, invariant under `φ_U(g)`, forces `φ_U(g) = 1` (`g ∈ C`).  Realization-free
-- (FPF core + abelian Irr↔Hom bridge + char-side FPF engine).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.chiefFactor_caseB_char_inertia
-- (9.9.a) inflation equivariance + abstract inertia reduction: the inflation `compHom (mk' N)`
-- intertwines the conjugation action `typeP_conjAction a` upstairs with the descended `φ_U` action
-- downstairs, reducing the concrete conjugation invariance of an inflated character to the abstract
-- `φ_U`-invariance that `chiefFactor_caseB_char_inertia` consumes (`typeP_conjAction`-inv ⟹ `φ_U=1`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.compHom_typeP_conjAction_inflation
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.caseB_char_inertia_inflation
-- (9.9.a) realization: the iso `↥(H-in-HU) ≃* ↥H` preserves the underlying `G`-element, so it
-- intertwines the concrete `HU`-conjugation `conjBy g` with the abstract `typeP_conjAction a`
-- (same `G`-image `↑g = ↑a`).  This is the last realization step feeding `caseB_char_inertia_inflation`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.hInHuEquivH_coe
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.conjBy_compHom_hInHuEquivH
-- (9.9.a) capstone: concrete `HU`-inertia of the realized inflation of a nontrivial `θ̄ ∈ Irr(H̄)`
-- forces `φ_U(a) = 1` (`a ∈ C`) — the character-side inertia `I_U(θ) ⊆ C`, fully concrete
-- (realization + inflation injectivity + `chiefFactor_caseB_char_inertia`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.caseB_inertia_realized
-- §9 degree infrastructure: `[M:HU] = q` (`HU = M'`, `[M:M'] = |W₁|`) and the resulting
-- `(Ind_{HU}^M χ)(1) = q·χ(1)` — the degree formula every (9.8)/(9.9) count uses.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.huSub_index_eq_q
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.induceHU_apply_one_eq_q_mul
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.card_range_dvd_card_sub_one_of_prime_card
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.typeP_commutator_U_centralizes_H
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.chiefFactor_caseB_image_cyclic
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.singerAdapter_coprime_fpf
-- Peterfalvi (9.7)(b): `Coprime |Ū| (p-1)` (fixed-point-free) and the resulting unconditional
-- divisibility `|Ū| ∣ (p^q-1)/(p-1)`.  The FPF input `C_Ū(w₀) = 1` is supplied from the Frobenius
-- structure of `U W₁` via Isaacs Cor 3.28 (`coprime_fixedPoints_quotient`).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.chiefFactor_caseB_image_coprime
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.chiefFactor_caseB_image_dvd_norm
-- (9.7)(b): the `U`-action on `H̄` is fixed-point-free off `C = C_U(H̄)` (Frobenius `H̄ ⋊ Ū`),
-- the structural input of Peterfalvi (9.9)'s degree-`u` Clifford analysis.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.chiefFactor_caseB_action_fpf
-- Peterfalvi (9.7): the Clifford dichotomy, fully packaged into the carriers `CliffordCaseAData` /
-- `CliffordCaseBData`.  Case (b) wires the Singer divisibilities (with `chars.u = |Ū|` pinned); case
-- (a) builds the `q` order-`p` factors (the `SupIndep` orbit family) and the bound `a ∣ p-1` (the
-- restricted `U`-action on an order-`p` factor).  All axiom-clean.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.exists_supIndep_aInvariant_family_of_iSup
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.aInvariantRestrictAut_range_card_dvd
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.clifford_caseB_data
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.clifford_caseA_data
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.clifford_dichotomy

/-! **Peterfalvi (9.7.b) chief-factor Galois-field model, axiom-clean** (lane a, issue 1031).
The actual case-(b) irreducibility proof feeds the shared faithful irreducible Singer constructor,
giving `H/H₀ ≃+ GF(p^q)` and an injective scalar realization of `Ū`.  When `C_U(H/H₀) = 1`, the
model transports along `U.subgroupOf (U ⊔ W₁) ≃ U`; no legacy opaque `field_model` is used. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.caseB_exists_galoisField_repr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.uActionHom_injective_of_cSub_eq_bot
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.caseB_exists_galoisField_repr_of_cSub_eq_bot

-- Peterfalvi §13 (= repo `S13_MaximalIII_IV`, types III/IV) structural cluster.  After de-opacifying
-- the `Hypothesis` scaffold (the `C = C_U(H)` field and the deleted opaque conclusion-Props), the
-- two *unconditional* inclusions of (11.5)/(11.6) are axiom-clean: `secondDerived_le_HC`
-- (`M'' ⊆ HC`, = (8.5.a) via `TypePData.secondDerived_le_fitting`) and `derivedU_le_C`
-- (`U' ⊆ C`, = (8.5.b) via `S11.typeP_commutator_U_centralizes_H`).  The reverse inclusions
-- (`M'' = HC`, `C = U'`) are the coherence content of (11.5)/(11.6), gated on Theorem (10.8).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.Hypothesis.secondDerived_le_HC
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.Hypothesis.derivedU_le_C
-- (11.6) the `U`-centralizes-`H₀` clause via Wielandt (9.1): given `C_{H₀}(W₁) = 1` and `U ≠ 1`,
-- the Frobenius kernel `U` centralizes the chief subgroup `H₀`.  The Wielandt content (lane-h's
-- `frobenius_kernel_centralizes_of_complement_fpf`) is axiom-clean; the fpf input is the §8 gate.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.U_centralizes_H0_of_W1_fpf
-- Same clause restated against the cleaner subgroup gate `W₂ ⊓ H₀ = ⊥` (the fpf input reduces to it
-- via `H ⊓ C_G(W₁) = W₂`); isolates the genuine §8/chief obligation.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.U_centralizes_H0_of_W2_inf_H0_bot
-- (9.6)/(11.6) the genuine §8/chief input `W₂ ⊓ H₀ = ⊥`, discharged unconditionally: `|W₂| = p` prime
-- + the chief-factor order `|C_{H̄}(W₁)| = |W̄₂| = p` (`coprimeFrobeniusChiefFactor_card`) show `W₂ ⊄ H₀`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.chief_W2_inf_H0_eq_bot
-- (11.6) conjunct 2 fully assembled: `U` centralizes `H₀` with no character input (the above chief
-- input feeds Wielandt (9.1)).  This is the unconditional half of `core_structure`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.U_centralizes_H0

-- §16 character-data producer (`section16CharacterData`, POLE-1 `cd`) — S-side grid building blocks.
-- `induce_compHom_subgroupCongr`: `Ind` is invariant under transporting the source subgroup along an
-- equality (the cd-grid transport primitive).  `Section16CharacterData.muS_definition`: the S-side
-- (13.1.e) `mu_definition` identity `Ind_W^S(ω_{ij} − ω_{0j}) = δ_j(μ_{ij} − μ_{0j})`, read off the
-- `certainTypeS` certain-type machinery (`chiColumn`/`columnFamily`) via the `tpW_subgroupOf_eq`
-- W-identification + the (4.3.b)/(1.4) bridge `S06.induce_chiColumn_diff_mu_diff`.  Both axiom-clean.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.induce_compHom_subgroupCongr
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tpW_subgroupOf_eq
#assert_only_allowed_axioms OddOrder.Section16CharacterData.muS_definition
-- S/T-shared-`ω` symmetry transport infrastructure (toward the `nu_definition` field, T-side).
-- `monoidHom_eq_of_eqOn_W1_W2`: a linear character of `↥tp.W` is pinned by its `tp.W1`/`tp.W2`
-- restrictions (the internal-product generating-set principle).  `gridEquivE_coe`: the S-side
-- W-identification equiv preserves the ambient `G`-element.  `gridEquivE_mem_W1`/`_W2`: it carries
-- `mp.K`/`mp.Kstar` elements into `certainTypeS.W1`/`W2`.  All axiom-clean.
#assert_only_allowed_axioms OddOrder.Section16CharacterData.monoidHom_eq_of_eqOn_W1_W2
#assert_only_allowed_axioms OddOrder.Section16CharacterData.gridEquivE_coe
#assert_only_allowed_axioms OddOrder.Section16CharacterData.gridEquivE_mem_W1
#assert_only_allowed_axioms OddOrder.Section16CharacterData.gridEquivE_mem_W2
-- `omegaProdCharS_apply_mem_K`/`_Kstar`: `certainTypeS`'s product character, evaluated on a
-- `gridEquivE`-transported `mp.K`/`mp.Kstar` element, keeps only the `W₁`/`W₂` factor (the
-- `tp.W1`/`tp.W2`-restriction values feeding the symmetry).  Axiom-clean.
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaProdCharS_apply_mem_K
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaProdCharS_apply_mem_Kstar
-- `omegaProdCharT_apply_mem_K`/`_Kstar`: the T-side mirror — `certainTypeT`'s product character on a
-- `gridEquivE_T`-transported `mp.K`/`mp.Kstar` element keeps only the surviving factor (`mp.K` is the
-- `W₂`-factor of `T`, `mp.Kstar` the `W₁`-factor).  Axiom-clean.
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaProdCharT_apply_mem_K
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaProdCharT_apply_mem_Kstar
-- `chi2enum_zero` (step A): the `W₂`-column enumeration is normalized so column `0` is the trivial
-- character (the `j = 0` base of `nu_definition`), mirroring the `w1CharEquiv 0 = 1` convention.
#assert_only_allowed_axioms OddOrder.Section16CharacterData.chi2enum_zero
-- T-side mirror of the W-identification infrastructure (step D), toward `nu_definition`.  `certainTypeT`
-- carries `mp.T` with the factors swapped (`W₁ = mp.Kstar`, `W₂ = mp.K`): `certainTypeT_W1_eq`/`_W2_eq`
-- pin the factors, `k_le_T` places `mp.K ≤ mp.T`, `cardCertainTypeT_W1`/`_W2` match `tp.p`/`tp.q`,
-- `tpW_subgroupOf_T_eq` identifies `tp.W.subgroupOf mp.T` with `certainTypeT.sdiff.W`, and
-- `gridEquivE_T_coe`/`_mem_W1`/`_mem_W2` are the element-preserving T-side transport.  All axiom-clean.
#assert_only_allowed_axioms OddOrder.Section16CharacterData.certainTypeT_W1_eq
#assert_only_allowed_axioms OddOrder.Section16CharacterData.certainTypeT_W2_eq
#assert_only_allowed_axioms OddOrder.Section16CharacterData.k_le_T
#assert_only_allowed_axioms OddOrder.Section16CharacterData.cardCertainTypeT_W1
#assert_only_allowed_axioms OddOrder.Section16CharacterData.cardCertainTypeT_W2
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tpW_subgroupOf_T_eq
#assert_only_allowed_axioms OddOrder.Section16CharacterData.gridEquivE_T_coe
#assert_only_allowed_axioms OddOrder.Section16CharacterData.gridEquivE_T_mem_W1
#assert_only_allowed_axioms OddOrder.Section16CharacterData.gridEquivE_T_mem_W2
-- **cd `nu_definition` (piece 3, S/T-shared-`ω` symmetry)** — the harder of the two real Prop
-- obligations of the cd producer.  The shared `ω`-grid is re-expressed through `certainTypeT` by
-- transporting the S-side index characters along `eTS` (G-element-preserving): `eTS_gridEquivE_T` is
-- the round-trip; `colT_apply_mem_K`/`rowDualT_apply_mem_Kstar` are the matching of the T-side duals
-- with the S-side index characters; `rowDualT_zero`/`rowT_zero` pin the `j = 0` trivial base (needs the
-- step-A `chi2enum_zero`).  `omegaS_eq_omegaT` is the symmetry (`monoidHom_eq_of_eqOn_W1_W2`), and
-- `nuT_definition` is the `Ind_W^T(ω_{ij} − ω_{i0}) = δ'_i(ν_{ij} − ν_{i0})` identity (mirror of
-- `muS_definition`, via `S06.induce_chiColumn_diff_mu_diff` T-side).  All axiom-clean.
#assert_only_allowed_axioms OddOrder.Section16CharacterData.eTS_gridEquivE_T
#assert_only_allowed_axioms OddOrder.Section16CharacterData.colT_apply_mem_K
#assert_only_allowed_axioms OddOrder.Section16CharacterData.rowDualT_apply_mem_Kstar
#assert_only_allowed_axioms OddOrder.Section16CharacterData.rowDualT_zero
#assert_only_allowed_axioms OddOrder.Section16CharacterData.rowT_zero
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaS_eq_omegaT
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_definition
-- **Canonical T-side `ν`-grid supply (issue 1029)** — the certain-type construction supplies every
-- grid-theoretic field of `NuGridSupplyData`: index negation/conjugation, irreducibility,
-- row-injectivity, full orthonormality, degree congruence and base sign, row induction and reverse
-- dichotomy, the (4.8) support estimate, and the (4.3.c) value identity.  The separate structural
-- field `V_commutative` is intentionally not included: it is a post-(14.9) type-II fact, not a
-- property of the canonical character grid (issue 9096 API audit).
#assert_only_allowed_axioms OddOrder.Section16CharacterData.colT_finNeg
#assert_only_allowed_axioms OddOrder.Section16CharacterData.rowDualT_finNeg
#assert_only_allowed_axioms OddOrder.Section16CharacterData.rowT_finNeg_eq_rowInv
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_irreducible
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_row_injective
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_orthonormal
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_degree_modEq_deltaPrime
#assert_only_allowed_axioms OddOrder.Section16CharacterData.deltaPrimeT_zero_eq_one
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_rowSum_eq_induce
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_reducible_dichotomy
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_diff_support
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_apply_of_not_mem_W1
#assert_only_allowed_axioms OddOrder.Section16CharacterData.nuT_conj
-- **cd `tau3` (piece 5, real Dade σ-integral)** — `tau3W` is the Peterfalvi (3.2) σ-isometry of the
-- G-internal TI-cyclic structure on `W = tp.W = mp.K ⊔ mp.Kstar` (support `Ẑ = W \ (W₁ ∪ W₂) =
-- S14.zTilde`), as an `IntegralCharacterMap`.  The TI-set fact is read off the proven `BG §14
-- typeP_duality` (Theorem 14.7), the Dade isometry from the general §4 producer
-- `S04.Hypothesis.fullDadeIsometryData` (`HConjInvariant` automatic since all `H(a) = ⊥`).  The
-- genuine (not formal) `τ₃` so that `η = τ₃ ∘ ω` is a real virtual character downstream.  Axiom-clean.
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tau3W

-- **cd grid property package (issue 3002)** — the (3.2)/(3.3)/(3.4) character-theoretic content of
-- `tau3W`/`omegaS`, read off the `S05` σ-isometry lemmas (`sigmaIntegral_*`) through the extracted
-- `tiCyclicW`/`tiCyclicWDadeApp` and the `S05` ω-orthonormality (`omega_inner`) transported along
-- `gridEquivE` (`ClassFunction.inner_compHom_mulEquiv`).  These discharge the grid property fields
-- threaded onto `Section16CharacterData` / `Section16Inputs` / `S15.Hypothesis`, which the §15 norm
-- cascade ((13.5)–(13.10)) consumes.  Axiom-clean.
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tiCyclicW
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tiCyclicWDadeApp
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tau3W_isometry
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tau3W_trivial
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tau3W_mem_ZIrr
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tau3W_apply_of_regular
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaS_inner
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaS_apply_one
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaS_mem_ZIrr

-- **Concrete eta-axis Galois orbits (issue 3004 frontier, lane c)** — the S-side dual
-- enumerations are literal powers of prime-order generators.  The S05 sigma transport therefore
-- gives full class-function Galois orbits on both nonprincipal axes; the former row-only vanishing
-- theorem is now just their pointwise zero corollary.  These are concrete producer theorems and do
-- not change the abstract S15 carrier signature.
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaSChar_row_eq_pow
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaSChar_column_eq_pow
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tau3W_omegaS_eq_sigma_omegaSChar
#assert_only_allowed_axioms OddOrder.Section16CharacterData.omegaSChar_injective
#assert_only_allowed_axioms OddOrder.Section16CharacterData.orderOf_omegaSChar_row_base
#assert_only_allowed_axioms OddOrder.Section16CharacterData.orderOf_omegaSChar_column_base
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tau3W_omegaS_row_galois_orbit
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tau3W_omegaS_column_galois_orbit
#assert_only_allowed_axioms OddOrder.Section16CharacterData.tau3W_omegaS_row_vanish_of_one_zero

-- **cd producer (POLE-1 `charData`)** — `section16CharacterData_of_isMinimalSimpleOdd` packs the
-- proven grid building blocks (`omegaS`/`muS`/`nuT`/`deltaS`/`deltaPrimeT`/`tau3W` with the
-- `(13.1.e)` identities `muS_definition`/`nuT_definition`) into the `Section16CharacterData` carrier.
-- The fields `Sset`/`Tset`/`A0S`/`A0T`/`tauS`/`tauT` carry honest placeholders (`∅`/`0`): they are
-- verified-vestigial on the FT path (the §13/§16 contradiction in `S16_NonExistenceG` routes through
-- `eta = τ₃ ∘ ω`, never the S/T-side coherent isometries), and `Hypothesis` places no `Prop` on them,
-- so the placeholders add no unsound dependency.  Closes one of the three POLE-1 producers
-- (`mp`/`tp`/`charData`).
--
-- ✅ **issue-3002 keystone (2026-07-05 landed; 2026-07-07 honest close, lane b)**: the producer
-- also supplies the three Peterfalvi (3.9) η-grid Dade fields (`eta_intCast_of_coprime` (3.9.c) /
-- `eta_principal_of_coprime` (3.9) / `eta_pair_of_coprime` (3.9.a)), now **all `sorry`-free**.
-- The former (3.9.a) gate (`finNeg` index negation ≠ character inversion for the old
-- nonconstructive enumerations) was closed by rebuilding `w1CharEquiv`/`chi2enum` as
-- **power enumerations** of the cyclic duals (`S06.cyclicPowEnum` — Peterfalvi's own (3.5) grid
-- indexing `ω_{ij} = ω₁^i ω₂^j`), under which `finNeg` *is* character inversion
-- (`w1CharEquiv_finNeg`/`chi2enum_finNeg` → `omegaSChar_finNeg`), so
-- `tau3W_omegaS_pair_of_coprime` follows from Galois-equivariance (`sigma_mapRingEquiv_comm` +
-- `galoisMap_conj_omega`) and (3.9.c) integrality.  Assertion re-enabled.
#assert_only_allowed_axioms OddOrder.section16CharacterData_of_isMinimalSimpleOdd

-- **Peterfalvi (5.7) standalone constant-degree coherence producer** —
-- `coherent_of_constant_degree`: under Hypothesis (5.2) + equal degree, `S` is coherent.  Proven by
-- the one-shot auxiliary isometry `χⱼ ↦ β − (χ₀ − χⱼ)^τ` (`β = χ₀^{τ₁}` the common `R(χ₀)`-projection,
-- independent of the auxiliary member by the (5.4.b) two-sided norm argument `pairDecomp_two_sided`
-- and the 4-case independence `commonImage_inner`), fed to `coherentEqualDegree`; single-pair `S`
-- routes to the (5.2.d) base case `isCoherent_pair_of_differenceImage`.  All Dade-specific data
-- (ℤ[Irr G]-membership of supported differences, support, `1 ∉ A`) are explicit hypotheses
-- discharged by the §13 consumer.  Axiom-clean.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.isCoherent_pair_of_differenceImage
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.pairDecomp_two_sided
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.commonImage_self
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.commonImage_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.xFamily_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S07.coherent_of_constant_degree

-- Peterfalvi §10 (10.9) coherence-free support: the general Bessel `NC` bound
-- `sigmaNC ψ ≤ ‖ψ‖²` (`ψ ∈ ZIrr G`, `⟨ψ, ψ⟩ = N ⟹ NC ≤ N`), generalising the norm-1/2 `σ`-image
-- support bounds.  Fully axiom-clean (the σ-grid orthonormality + integer Parseval).  Used by the
-- coherence-free (10.9) `inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2` (lane-b W3,
-- which is itself char-gated, so not registered here).
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S05.TICyclicHypothesis.ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast

-- **`|K*| = w₂` carrier bridge** (lane-b W3, BG §14 group theory) —
-- `card_Msigma_inf_centralizer_eq_card_W2`: for a type-`P` maximal `S`, κ-Hall `K` cyclic, and any
-- `TypePData d`, the dual factor `K* = M_σ(S) ⊓ C(K)` has order `|W₂| = w₂`.  `W₂ = M' ⊓ C(W₁)`
-- (`centralizer_W1`) is sandwiched by `W₂ ≤ M_F ≤ M_σ ≤ M'`; `K` and `W₁` both complement the normal
-- Hall `M'`, so are `S`-conjugate (Schur–Zassenhaus), and conjugating `M_σ ⊓ C(K)` onto
-- `M_σ ⊓ C(W₁) = W₂` (with `M_σ` `S`-invariant) gives the order.  No character theory; this is the
-- group-theoretic half that, paired with the §11 reduction `w₂ < w₁`, closes the unique bare
-- `feitThompson` sorry `card_kappaHall_lt_of_isTypeIIIorIV` (whose residual is now the genuine
-- Peterfalvi (11.8) refuter core `S13.exists_zeta_residual_not_orthogonal_H0C_of_refuter` — the
-- §14 Sibley glue (6.7)/(5.8) and the (9.11) caseA refuter, issues 1019/1020); it also supplies,
-- with
-- `typeP_duality`, the (8.8) Type-II partner `S10.exists_typeII_maximal_with_w2_of_typeP`.
-- Axiom-clean.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2

-- **type-`P` support is the derived sharp** (shared `GroupTheory`) —
-- `typePA_eq_sharpSubgroup_derivedInG`: `A(M) = typePA M = sharpSubgroup (derivedInG M) = (M')#`.
-- The `centralizerSupport (M#) M'` definition collapses on `(M')#` (each `y ∈ (M')# ⊆ M#`
-- self-centralizes), so `A(M)` is the sharp of the normal `M' ⊴ M` — the `A = H#` shape Peterfalvi
-- (10.8) uses to apply the (7.6)/(7.8.b) coherence estimate.  Pure set theory.  Axiom-clean.
#assert_only_allowed_axioms OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG

-- **`𝒞_G(T)` conjugation-invariance** (shared `GroupTheory`) — `mem_conjClassSet_conj_iff`:
-- `g * h * g⁻¹ ∈ 𝒞_G(T) ↔ h ∈ 𝒞_G(T)`, i.e. `N_G(𝒞_G(T)) = G`.  Pure group theory (used by the
-- BG §14/§16 counting and the (10.8) TI-counting).  Axiom-clean.
#assert_only_allowed_axioms OddOrder.GroupTheory.mem_conjClassSet_conj_iff

-- **Peterfalvi (8.16) for the type-`P` support `A(M)`** (lane-b W3, §7-input prerequisite) —
-- `Hypothesis.normalizer_typePA_eq`: `N_G(A(M)) = M` for the genuine (10.1) `Hypothesis` under
-- `hG : IsMinimalSimpleOdd G`.  `M ≤ N_G(A(M))` is the `M`-invariance `le_normalizer_typePA`
-- (`derivedInG_pointwise_smul` / `conj_smul_eq_self_of_mem` / `image_sharpSubgroup`); conversely
-- `A(M) = (M')#` (`typePA_eq_sharpSubgroup_derivedInG`) makes a set-normalizer of `A(M)` normalize
-- `M'`, and `N_G(M')` contains the maximal `M`, so it is `M` or `G` — `G` would make the
-- nontrivial `M' ≤ M < G` normal, contradicting simplicity.  The `M`-invariance half discharges
-- the formerly-parametrized `hN` of the §7 inputs `toHypothesis71` / `toFamilyHypothesis71`
-- (Peterfalvi (10.8) line 79).  Axiom-clean.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.normalizer_typePA_eq

-- **Peterfalvi (8.15) for type `P` = the (10.1) "Hypothesis (4.6) holds"** (lane-a, issue 9004) —
-- `Hypothesis.toHypothesis46`: the §10 `Hypothesis` instantiates `S06.Hypothesis46 (A(M)) M` with
-- `K = M'`, `H = M_s = M'`, `A = A(M)`, `A₀ = A₀(M)`.  The `A₀`-side Dade datum and isometry are
-- *definitionally* `hyp.dadeData.dade` / its `fullDadeIsometryData` (both (8.10) `typePA0` and
-- (4.6.d) use `conjClassSetIn`); the `A`-side datum is the `restrict` along `le_normalizer_typePA`;
-- `A_covers` is trivial for `H = K` by `A(M) = (M')#`.  First-ever instantiation of `Hypothesis46`
-- (the carrier was latent-unsatisfiable before the issue-9004 small-V/M-conjugacy fixes).
-- Axiom-clean since the Hall-coprimality input swapped its BG Theorem A cite to the sorry-free
-- faithful `S15.typeP_auxiliary_structure` (and `proposition_type_classification` is proven).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.toHypothesis46

-- **Peterfalvi (4.8)/(4.10) on the §10 aligned grid** (lane-a, issue 9004 payoff) —
-- `Hypothesis.tau_muGrid_zeroRow_diff`: `(μ_{0j} − μ_{0k})^τ = δ_j(ω_{0j}^σ − ω_{0k}^σ)`, and
-- `Hypothesis.tau_muGrid_fourCorner`: the δ_j-scaled four-corner Dade identity — the §6
-- `certainType_diff_dade_eq` / `fourCorner_dade_eq` cited through `toHypothesis46` with the
-- σ-side bridge `certainTypeOmegaSigma = alignedOmegaSigmaGrid`.  These discharge the `h48`/`h410`
-- threads of the (11.8.3)/(11.8.5) β-reality chain.  Axiom-clean.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.tau_muGrid_zeroRow_diff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.tau_muGrid_fourCorner

-- **Peterfalvi (10.8) line-87 arithmetic** (lane-b W3, §7-estimate input) —
-- `Hypothesis.card_typePA_div_card_lt_inv_w1`: `|A(M)|/|M| < 1/w₁`.  From `A(M) = (M')#`
-- (`typePA_eq_sharpSubgroup_derivedInG`, `|A(M)| = |M'|−1`) and `|M| = w₁·|M'|`
-- (`card_W1_eq_derived_index` + `index_mul_card`): `(|M'|−1)/(w₁|M'|) < 1/w₁`.  The strict bound
-- (10.8) uses at line 87.  Axiom-clean.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.card_typePA_div_card_lt_inv_w1

-- **`‖ζ^{τ₁}‖² = 1`** (lane-b W3, Pf (10.8) line-81 input) —
-- `Hypothesis.inner_tau1_zeta_self_eq_one`: the coherent extension `τ₁` is a lattice isometry on
-- `ℤ[S]` (`coh.coherent.extension_inner_eq`) and `ζ = params.zeta ∈ S` is irreducible, so `‖ζ^{τ₁}‖²
-- = ‖ζ‖² = 1`.  This is the norm-one hypothesis `S09.family_inequality` (7.5) requires of `χ =
-- ζ^{τ₁}`, bridging the self-contained `toFamilyHypothesis71` to the (10.8) line-81 inequality.
-- Axiom-clean.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.inner_tau1_zeta_self_eq_one

-- **Peterfalvi (10.8) line 83** `Hypothesis.chiRhoNormSq_zeta_le_line83` (lane-b W3): the mechanical
-- (7.5)+(10.6.b) combination `‖ζ^{τ₁,ρ}‖² ≤ |A(M)|/|M| + (|famG₀|−|G₀|)/|G|`.  Applies
-- `S09.family_inequality` (7.5) to the self-contained `toFamilyHypothesis71` (norm-one via
-- `inner_tau1_zeta_self_eq_one`) and drops the `G₀`-part via `sum_zeta_tau1_normSq_ge_card`.  **Not
-- AxiomsCheck-registered**: it cites `sum_zeta_tau1_normSq_ge_card`/`tau1_values_and_norm_bound`,
-- which carry the existing §10 `Hypothesis`-carrier `sorryAx` taint (same as (10.9)); no *new* sorry.

/-! **Peterfalvi (13.19.c) parity branch under the (14.11.1) strict gaps**
(`S16_NonExistenceG`, lane C).  Once the faithful row/column alternatives are supplied explicitly,
the two strict quotient inequalities eliminate their size-bound branches and leave the actual
`β_M` odd-integrality conclusions.  Its proof body is pure order arithmetic, but it is temporarily
not registered here: after `MHypothesis.h78` became the computed accessor
`coherent78.h78 hG`, the theorem's `Mdata.betaM`-bearing type transitively exposes the existing
upstream Dade-isometry `sorryAx`.  This is the same disclosed gate as the concrete coherent bundle,
not an additional sorry in this theorem. -/

-- **W4 §16→§7 bridge (lane-h, βM (14.11.2) de-opacification)** — `betaMExpansionData_of_hypothesis78`
-- certifies that the (7.8.a) field of `BetaMExpansionData` (`β_M = 1_G − χ + Δ`) is a genuine
-- consequence of the S09 §7 Dade decomposition
-- `S09.Hypothesis78.beta_eq_constOne_sub_zetaImage_add_delta` (`β = 1_G − ζ^ν + Δ`), given `M`
-- instantiating `S09.Hypothesis78` with `β_M = β` and `ψ^{τ₁} = ζ^ν` (the `χ = ζ^ν` branch, so
-- `chi_norm` is `rfl`), together with the conditionally derived `e = p q`.  It isolates the
-- remaining conditional engine work: coefficient projection, norm tightness, residual vanishing,
-- and the χ classification.  The proof body is complete, but this declaration is temporarily not
-- registered for the same computed-`h78` transitive `sorryAx` described above; its result type
-- contains `Mdata.betaM`.

-- **W2 §12 (12.17) normalizer bridge (lane-h)** — `maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`:
-- a maximal subgroup `L` of a minimal simple group of odd order equals `N_G(L_F)` whenever
-- `L_F = maxNilpotentNormalHall L ≠ ⊥`.  `L ≤ N_G(L_F)` is `maxNilpotentNormalHall_le_normalizer`;
-- `N_G(L_F) = ⊤` would make `L_F ⊴ G`, excluded by simplicity (`L_F ≠ ⊥`, `L_F ≤ L < ⊤`); `L`
-- coatom upgrades `L ≤ N_G(L_F) < ⊤` to equality.  This is the genuine group-theoretic core of the
-- Peterfalvi (12.17) Frobenius-family assembly `not_all_maximal_typeI` (the `normalizer_eq` field of
-- `S09.FrobeniusFamily`), which together with the (8.8) dichotomy `theorem88_dichotomy` (BG §16)
-- discharges `theorem88_caseB_holds` — the all-Type-I non-existence the Feit–Thompson endgame
-- consumes.  Axiom-clean.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.maximalSubgroup_eq_normalizer_maxNilpotentNormalHall

-- **W2 §12 (12.17) type-I covering core (lane-h)** — the structural heart of the (8.17.a) type-I
-- covering, isolated as two reusable group-theory lemmas behind `exists_typeICovering`'s `covers`
-- field:
-- * `supportKernel_le_maxNilpotentNormalHall`: the §8 thickening kernel `R(x)` of Peterfalvi (8.14)
--   is always `≤ L_F = maxNilpotentNormalHall L` (both branches of its definition are).
-- * `thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall`: if a support set `X ⊆ L_F`, then
--   the thickened support `⋃_{z ∈ X} (z R(z))^G` lands in `𝒞_G(L_F)` — the coset factor `z ∈ X ⊆ L_F`
--   and the kernel factor `r ∈ R(z) ⊆ L_F` multiply into `L_F`.
-- This is why the `A_1(M_i) = (M_i)_F#` thickened cover is, up to conjugacy, a cover by `(M_i)_F#`:
-- the genuine group-theoretic content discharging the `covers` field of `exists_typeICovering`
-- (Peterfalvi (12.17), all-type-I case).  Both axiom-clean.
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.supportKernel_le_maxNilpotentNormalHall
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S14.thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall

-- **W2 §12 (12.17) → (8.8) dichotomy (lane-h)** — `theorem88_dichotomy`: for a minimal simple group
-- of odd order, either every maximal subgroup is type I, or the case-(b) pairing data
-- `Theorem88CaseBData` exists.  The case-(b) branch is constructed from a non-type-I (hence type-`P`,
-- Prop 16.1(a)) maximal `S`: BG Theorem 14.7 duality (`typeP_duality`) supplies the complement
-- `S = S' ⋊ K` (its `IsComplement'` first conjunct, `K` a `κ(S)`-Hall subgroup), the dual maximal
-- `M*`, and the cyclic `W = K ⊔ K*`; a second application at `M*` gives `M* = (M*)' ⋊ K*`.  Now
-- axiom-clean: both `proposition_type_classification` (BG Prop 16.1, issue 8015 reverse bridges closed)
-- and `typeP_duality` (BG Theorem 14.7) are axiom-clean, so the (8.8) dichotomy is honestly proven.
-- The full `theorem88_caseB_holds` chain is now axiom-clean: the type-I Dade and covering
-- residuals are discharged, and its guard is registered in the Section 16 producer block below.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.theorem88_dichotomy

-- **W2 §12 (12.9) rank-two witness machinery (lane-h/lane-c)** — the minimal-counterexample structure
-- theory of Peterfalvi (12.9), now axiom-clean since its sole `§16` gate (Proposition 16.1's type-`I`
-- clauses (a) `κ(M) = ∅` and (f) `M_F = M_σ`) is closed (issue 8015).
-- * `exists_sigmaKappaCompl_hall_ge_P0`: the noncyclic Sylow `P₀` of a type-`I` counterexample maximal
--   `M` lies in a `(κ(M) ∪ σ(M))ᶜ`-Hall subgroup `U ≤ M` (so BG Theorem B(1) gives `P₀` abelian of
--   rank `≤ 2`); via `p ∉ σ(M)` from `p ∤ |M_σ|` and `κ(M) = ∅`.
-- * `counterexample_P0_K_structure`: `P₀` is abelian of rank exactly 2, the structural core of (12.9).
-- Both cite only the now-clean Proposition 16.1, BG Hall theory, and the proved BG Theorem B(1).
-- (`exists_rankTwoWitness`, the full rank-two witness packaging, still transits a `sorryAx` through a
-- further §12/§16 cite, so it is not yet registered.)
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.exists_sigmaKappaCompl_hall_ge_P0
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.counterexample_P0_K_structure
-- Pf (12.16) (1.10) congruence core: from `ψ ∈ ℤ[Irr G]`, `x^p=1`, `g` commuting with `x`, the
-- (12.14)/(12.15)/Dade facts (`ψ(xg)=ψ(x)`, `ψ(x)≡e mod 1-ε`, `ψ(g)=mval∈ℤ`), (1.10.a)+(1.10.b)
-- give `p ∣ (mval-e)` (i.e. `ψ(g)≡e mod p`).  Materializes the (1.10)-wiring of (12.16).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.psi_int_congr_e_mod_p
-- Pf (12.16) magnitude step: an integer `≡ e mod p` with `1≤e`, `2e≤p+1` (12.12) has `|·| ≥ e-1`.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.abs_ge_e_sub_one
-- Pf (12.16) value-magnitude conclusion: chaining the congruence core with `2e≤p+1` gives
-- `|ψ(g)| ≥ e-1` — the lower bound feeding the final norm inequality of (12.16).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.abs_psi_g_ge_e_sub_one
-- Pf (12.16) closing endgame: `index_ratio_contradiction` (reduced ineq + `[K:K']≥4` + `e≥3` ⟹ False
-- via `(3e-1)(e-3)≥0`), `norm_ineq_reduce` ((12.11) `|M|≤|K||H|` reduction), and `counterexample_closing`
-- (combined: norm conclusion + (12.11) + `e≥3` + fpf `[K:K']≥4` of (8.1.c) ⟹ False).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.index_ratio_contradiction
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.norm_ineq_reduce
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.counterexample_closing
-- Pf (12.16) middle glue: `|ψ(g)|≥e-1` + the three §7/§8 norm bounds (A/B/C) ⟹ the norm conclusion.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.norm_conclusion_glue
-- Pf (12.16) FULL assembly: the entire argument as one sorry-free theorem, parameterized on every
-- gated §7/§8/§12 fact ((12.14)/(12.15)/Dade/(12.12)/(12.11)/(8.1.c) + norm bounds A/B/C).  The
-- remaining work to close `counterexample_contradiction` is exactly constructing these (§7 ρ machinery).
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.counterexample_contradiction_of_facts
-- Pf (12.16) ungated input bridges: `two_mul_le_succ_of_odd_dvd` ((12.12) `e∣p+1` + odd ⟹ `2e≤p+1`),
-- `four_le_of_dvd_sub_one` ((8.1.c) `p∣[K:K']-1` ⟹ `[K:K']≥4`), `exists_witness_g` ((12.9) centralizer
-- witness `g ∈ C_K(x) ∖ K'`).  Discharge the non-ρ-machinery content of (12.16)'s cited steps.
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.two_mul_le_succ_of_odd_dvd
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.four_le_of_dvd_sub_one
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.exists_witness_g

-- **W1 §16 Prop 16.1 `hP1eqV` disjunct 3 (Singer/`SL₂(p)`) prerequisite (lane-f, issue 8015)** —
-- `IsExtraspecial.of_card_eq_prime_cube`: a nonabelian group of order `p³` is extraspecial
-- (`Z(G) = [G,G] = Φ(G)`, `|Z(G)| = p`); Coq mathcomp `p3group_extraspecial`.  This is the structural
-- step that promotes `O_p(M_F)` of order `p³` to extraspecial in the type-V Singer case, reusable for
-- any nonabelian `p`-group of order `p³`.  Its Burnside-basis helper
-- `isCyclic_of_isCyclic_quotient_frattini` (a finite group with cyclic Frattini quotient is itself
-- cyclic) discharges the `|Φ| = p²` exclusion.  Both axiom-clean.
#assert_only_allowed_axioms
  OddOrder.GroupTheory.IsExtraspecial.of_card_eq_prime_cube
#assert_only_allowed_axioms
  OddOrder.GroupTheory.isCyclic_of_isCyclic_quotient_frattini

-- **W1 §16 disjunct 3, `r(O_p(M_F)) ≤ 2` assembly (lane-f, issue 8015)** — two bricks toward the
-- type-V Singer case's `|O_p(M_F)| = p³`, both axiom-clean:
-- * `isNarrow_opiCore_of_three_le_pRank`: `P = O_p(M_F)` is narrow once `pRank P ≥ 3` (the non-TI
--   witness `X₁` with `rank(M_F ⊓ C_G(X₁)) < 3` realizes the BG §5 narrow characterization).
-- * `pRank_opiCore_le_two_of_kappaHall`: `r(P) ≤ 2` (Coq `rPle2`) — a faithfully-acting cyclic `κ`-Hall
--   `K` with `|K| ∤ p−1` forces `pRank P ≤ 2` via BG Theorem 5.5(b) (`solvableAut_of_narrow`).
#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.isNarrow_opiCore_of_three_le_pRank
#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.pRank_opiCore_le_two_of_kappaHall

-- **W1 §16 disjunct 3, route B `|W₁| ∣ p+1` (lane-f, issue 8015)** — the Singer/symplectic
-- divisibility for the type-V case.  A cyclic `p'`-group `K` (`p` odd) acting on an extraspecial
-- `P` of order `p³`, fixed-point-freely on `V = P/Z(P)`, centralizing `Z(P)`, with `¬|K| ∣ p−1`,
-- has `|K| ∣ p+1`: `V` is a `2`-dim `𝔽_p`-space, the action is irreducible (else the split-torus
-- case gives `|K| ∣ p−1`), Singer realizes `V ≅ 𝔽_{p²}` with `μ : K ↪ 𝔽_{p²}ˣ`, `K` preserves the
-- commutator symplectic form so `det ρ(k) = 1`, but `det ρ(k) = N(μ k) = μ(k)^{p+1}`, whence
-- `|K| ∣ p+1`.  All axiom-clean (`det_eq_one_of_compLinearMap_alternating` is the pure-linear-algebra
-- "preserved nonzero alternating top-form ⟹ det = 1").
#assert_only_allowed_axioms
  OddOrder.GroupTheory.card_dvd_succ_of_primeAction_extraspecial
#assert_only_allowed_axioms
  OddOrder.GroupTheory.det_eq_one_of_compLinearMap_alternating

-- **W1 §16 Prop 16.1 forward bridge `hP1eqV` COMPLETE (lane-f, issue 8015)** — a type-`P₁`
-- maximal `M` with `M_F = M_σ` is of type V, now **fully `sorry`-free + axiom-clean**.  Both
-- type-V disjunct-3 (Singer/`SL₂(p)`) residuals are closed: `|O_p(M_F)| = p³`
-- (`card_opiCore_eq_prime_cube_singer`) and `|W₁| ∣ p + 1` (route B, wiring the abstract
-- `card_dvd_succ_of_primeAction_extraspecial`: extraspecial `P = O_p(M_F)`, conjugation action of
-- the κ-Hall `K`, prime action `C_P(k) ⊆ Z(P)` from `centralizer_msigma_kappaElement_eq_kstar`
-- (`K* = Z`), `K` centralizing `Z(P)` from `Z ≤ K* ≤ C_G(K)`).
#assert_only_allowed_axioms
  OddOrder.BG.Ch4.S16.isTypeV_of_isTypeP1_mf_eq_msigma

/-! **Genuine `σ`-decomposition of an element** (`S14_TypePCounting`, BG §14 opening / Coq
`sigma_decomposition` / `sigma_length`; lane δ signalizer-functor port Chunk 1, issue 8020).  The
element σ-part `sigmaPart M x` (a genuine function via the two-block π-part decomposition
`exists_isPiElement_mul`), the `sigma_decomposition`/`sigma_length` of an element, and the two
foundational facts: `sigmaLength_eq_zero_iff` (Coq `ell_sigma0P`: `ℓ_σ(x) = 0 ↔ x = 1`) and
`sigmaLength_conj` (Coq `ell_sigmaJ`: conjugation-invariance).  These construct the carrier that
`SigmaDecompositionData` only posits.  All axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.piPart_one
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.isPiElement_compl_of_piPart_eq_one
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.isPiElement_conj
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.piPart_conj
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.piPart_mul_of_commute
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaPart_eq_self_of_conj
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaPart_eq_one_of_not_conj
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigma_cover_decomposition
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.not_conj_of_mem_Msigma_of_tau2
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigma_cover_decomposition_signalizer
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.mem_sigma_cover_decomposition_signalizer
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaLength_cover_le_two_signalizer
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaPart_conj
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaLength_eq_zero_iff
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaLength_conj

/-! **`Msigma_ell1` and the σ-part collapse** (`S14_TypePCounting`, Coq `Msigma_ell1`; lane δ
signalizer-functor port Chunk 1 cont., issue 8020).  The genuine bridge to the
`SigmaDecompositionData` scaffold's posited `ℓ_σ(x) = 1` for `x ∈ M_σ^#`: an `M_σ`-element is a
`σ(M)`-element (`isPiElement_sigma_of_mem_Msigma`), so each `σ(L)`-part is `x` or `1`
(`sigmaPart_eq_self_or_one_of_isPiElement_sigma`, via `sigma_conj` / `sigma_disjoint_of_nonconjugate`)
and the σ-decomposition collapses to `{x}`, giving `sigmaLength x = 1`.  All axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.piPart_self_of_isPiElement
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.piPart_eq_one_of_isPiElement_compl
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.piPart_mem_zpowers
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.isPiElement_sigma_of_mem_Msigma
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaPart_eq_self_or_one_of_isPiElement_sigma
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaDecomposition_subset
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.Msigma_ell1

/-! **`ell_sigma1P` and the genuine `SigmaDecompositionData`** (`S14_TypePCounting`, Coq
`ell_sigma1P`; lane δ signalizer-functor port Chunk 1 capstone, issue 8020).  `sigmaLength_eq_one_iff`
proves the scaffold's *posited* `length_one_iff` (`ℓ_σ(x) = 1 ↔ x ≠ 1 ∧ 𝓜_σ(x) ≠ ∅`) for the genuine
`sigmaLength`, so `genuineSigmaDecomposition` **realizes** the `SigmaDecompositionData` carrier the
scaffold only posited (consumers can drop `dummySigmaDecomposition` for it).  All axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.prime_dvd_orderOf_piPart
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.exists_mem_Msigma_of_isPiElement_sigma
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.sigmaLength_eq_one_iff
#assert_only_allowed_axioms OddOrder.BG.Ch4.S14.genuineSigmaDecomposition

/-! **`FT_signalizer` construction** (`S16_MainResults`, Coq `FT_signalizer`/`nsRCx`; lane δ
signalizer-functor port Chunk 2, issue 8020).  The concrete `R(x) = (N[x])_σ ⊓ C_G(x)` object and its
first structural facts: `R(x) ≤ C_G(x)`, `C_G(x) ≤ N[x]` (nontrivial branch), and `R(x) ◁ C_G(x)`
(Theorem D(3) normality).  The deep `FT_signalizer_context` (transitivity / Hall / uniqueness) is the
remaining content.  All axiom-clean. -/

#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.FT_signalizer_le_centralizer
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.FT_signalizer_eq_bot_of_not_branch
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.centralizer_le_FT_signalizerBase
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.FT_signalizer_normal_in_centralizer
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.isHallSubgroup_subgroupOf_inf_of_normal_isHall
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.FT_signalizer_isHall
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.centralizer_le_normalizer_Msigma_inf_centralizer
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.maximalConjugatesContaining_eq_maximalSigma
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.conjSharplyTransitiveOn_of_pointed
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.RData_of_inputs

/-! **Theorem D(3) conjunct 3, the centralizer complement** (`S16_MainResults`, Coq Theorem 14.4(b)
`R ⋊ C_(M∩N)(x) = C(x)`; lane δ, issue 8020).  `Subgroup.IsComplement'.inf_centralizer_of_normalizer`
is the general mathcomp `subcent_sdprod` engine (a complement descends to centralizers when the
centralized element normalizes both factors); `signalizer_centralizer_isComplement` applies it to the
proven structure's `N`-complement, discharging the one genuinely-deep `RData` input;
`RData_of_gt_one` assembles the full `|𝓜_σ(x)| > 1` branch of Theorem D(3).  All axiom-clean. -/
#assert_only_allowed_axioms Subgroup.IsComplement'.inf_centralizer_of_normalizer
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.signalizer_centralizer_isComplement
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.RData_of_gt_one

/-! **Theorem D(3) full `hD3`** (`S16_MainResults`; lane δ, issue 8020).  The `|𝓜_σ(x)| ≤ 1 ⟹
C_G(x) ≤ M` dichotomy (`centralizer_le_of_maximalSigma_le_one`, the shallow converse of the
singleton lemma, Coq `not_sCX_M` direction) plus the `> 1` branch (`RData_of_gt_one`) assemble the
full `∀ x ∈ M_σ^#, ∃ R, RData M x R` (`exists_RData_of_mem_sigmaSharp`), discharging the `hD3`
conjunct of Theorem D.  All axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.exists_RData_of_mem_sigmaSharp

/-! **Theorem D(3) `|R(x)| = |𝓜_σ(x)|`** (`S16_MainResults`, Coq `oR`; lane δ, issue 8020).  The
sharp-transitive `R`-action (`ConjSharplyTransitiveOn`) closed on `𝓜_σ(x)` (via `R ≤ C_G(x)`) gives
the bijection `R ≃ 𝓜_σ(x)`, hence `|R| = |𝓜_σ(x)|` — the cardinality conjunct of the signalizer
first block, foundation of BG Theorem E's Lemma 14.5(c) count.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.card_signalizer_eq_card_maximalSigma

/-! **BG Lemma 14.5(a) `σ`-cover disjointness** (`S16_MainResults`, Coq `sigma_cover_disjoint`,
`_of_inputs` form; lane δ, issue 8020).  Distinct `σ`-length-one `x, y` give disjoint cover cosets
`x·R(x)`, `y·R(y)`: a common `g = x·r = y·s` makes `{x}∪{r}^# = σ(g) = {y}∪{s}^#`, forcing `y = r`,
`s = x`, whence `x` lands in the trivial intersection of the `y`-centralizer complement at `M' = N_x`
(`signalizer_centralizer_isComplement`) — contradiction.  The deep core of the 14.5(c) `R(x)`-cover
trivIset.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.sigma_cover_disjoint_of_inputs

/-! **Peterfalvi (5.3.b)/(14.9), T-side eta-grid orthogonality** (`S16_NonExistenceG`,
lane c).  A calT1 member difference is supported on `A₁(T) = (T')#`; the T-side Dade
map is the restriction of the full type-P1 `A₀(T)` map, whose image vanishes on the
regular `W`-set.  The norm-two rigidity engine then makes each coherent image
orthogonal to every `eta_ij`.  Both the reusable support input and the final
orthogonality theorem are axiom-clean. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.T_typeIII_calT1_difference_support
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.T_typeIII_coherent_image_inner_eta_eq_zero

/-! **Peterfalvi (14.11.4) `ρ`-norm bridge** (`S16_NonExistenceG`, lane γ/POLE-2).  The
family-inequality `ρ`-norm `(toFamilyHypothesis71).chiRhoNormSq (ψ^{τ₁}) 0` equals the (7.8.b)
coherence-norm `h78.zetaNuRhoNormSq`, since `S09.Hypothesis71.chiRho` depends only on the support
hypothesis `H71.hyp` (not the Dade map `τ`): `chiRhoCF_congr_hyp` + `psi_tau1_eq` + `h78_hyp_eq`.
The linchpin tying the (7.5) family-inequality layer to the (7.8.b) coherence-norm layer of
(14.11.4).  `chiRhoCF_congr_hyp` remains axiom-clean.  The two `MHypothesis` projections below
are temporarily not registered because their statements unfold the computed `h78` accessor and
therefore inherit the existing upstream Dade-isometry `sorryAx`; neither proof body contains a
sorry. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.chiRhoCF_congr_hyp

/-! **Peterfalvi (7.8.b)/(14.11.4) lower bound** (`S16_NonExistenceG`, lane γ/POLE-2).
The unconditional genuine content is `1 − e/k ≤ ‖ψ^{τ₁ρ}‖²`, where `e = |M:K|`.
Combines the coherence-norm lower bound for `M`
(`h78_zetaNuRho_normSq_ge`, the (7.8.b) `NormEstimates.zetaNuRho_norm_sq_ge` with `smallIndex`
discharged) with the index identities `h78.kernelOrder = |K| = k` and
`h78.complementIndex = |M:K| = e` (`h78_H_eq`/`e_eq_index` + Lagrange), and the norm bridge
above.  The conditional `normCascadeData` rewrites `e` to `p q` using (14.11.2).
Its proof body is complete; its temporary AxiomsCheck omission is covered by the computed-`h78`
disclosure above. -/

/-! **Peterfalvi (14.11.4) §8 support identity `A(M) = K#`** (`S16_NonExistenceG`, lane γ/POLE-2).
For a Frobenius group `M` with kernel `N`, the centralizer-support `centralizerSupport N# M` is
exactly `N#`: forward by the Frobenius FPF property `centralizer_kernel_le` (`C_M(x) ≤ N` for
`x ∈ N#`), reverse by `x = y`.  Applied with `N = K = M_F` this is `typeIA M = K#`, the §8
cardinality input `|A(M)| = k − 1` of (14.11.4) (Coq `PFsection14` `Dade_cover_inequality`
`#|A| = k.-1`).  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.centralizerSupport_sharpSubgroup_eq_of_frobenius

/-! **Peterfalvi (14.10) `|M| = e k`** (`S16_NonExistenceG`, lane γ/POLE-2).  The order of the
type-I maximal `M`, from `[M : K] = e` and `|K| = k` by Lagrange (`card_mul_index` +
`subgroupOfEquivOfLe`).  The conditional (14.11.4) upper bound rewrites `e = p q` only after
(14.11.2), yielding the denominator `|A(M)|/|M| = (k−1)/(kpq)`.
(`card_typeIA_eq`, the numerator `|A(M)| = k − 1`, cites `typeI_frobenius` (12.7) so is body-honest
but transitively gated on (12.16)/lane β, hence not registered here.)  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.MHypothesis.card_M_eq

/-! **Peterfalvi (14.11.4) orbit measure of a TI-subset** (`S16_NonExistenceG`, lane γ/POLE-2).
`orbit_normSq_term`: `|𝒞_G(A)|/|G| = |A|/|N|` for a TI-subset `A` with stabilizing normalizer-bound
`N` — the real-valued form of `S14.ncard_conjClassSet_of_isTISubset` (`|𝒞_G(A)| = |A|·[G:N]`), via
Lagrange.  The reusable bridge turning each (14.11.4) orbit `(W#)^G`/`(P#)^G`/`(Q#)^G` into a
`1/|N_G(·)|`-term.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.orbit_normSq_term

/-! **Peterfalvi (14.11.4) `W`-orbit TI core** (`S16_NonExistenceG`, lane γ/POLE-2).
`isTISubset_sdiff_sup_of_normalizer_eq`: the exceptional set `W − (W₁ ∪ W₂)` of a cyclic
`W = W₁ × W₂` is a TI-subset with normalizer-bound `W`, given the singleton/subset normalizer fact
`N_G(X) = W` — generalising `S12.typePData_V_ti` to the abstract `W`/`W₁`/`W₂` + `hnorm` inputs.
The `W`-orbit TI input to the (14.11.4) §8 TI-count.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.isTISubset_sdiff_sup_of_normalizer_eq

/-! **Peterfalvi (14.11.4) `W`-orbit measure** (`S16_NonExistenceG`, lane γ/POLE-2).  The `W`-stab
`conj_smul_sdiff_sup_eq_of_normalizer_eq` (`W ≤ N_G(set)` normalizes the set) and the assembled
relative measure `orbit_sdiff_sup_normSq_term`: `|(W − (W₁∪W₂))^G|/|G| = |W − (W₁∪W₂)|/|W|`,
combining the TI core, the `W`-stability, and `orbit_normSq_term`.  The `W`-orbit term of (14.11.4),
reduced to `hnorm` (= the §13 `normalizer_V` fact, from the partner type-`P` structure).
Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.conj_smul_sdiff_sup_eq_of_normalizer_eq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.orbit_sdiff_sup_normSq_term

/-! **Peterfalvi (14.11.4) `|W − (W₁∪W₂)|` cardinality** (`S16_NonExistenceG`, lane γ/POLE-2).
`ncard_sdiff_sup_add_eq`: `|W − (W₁∪W₂)| + |W₁| + |W₂| = |W| + 1` by inclusion–exclusion with
`W₁ ∩ W₂ = {1}`.  The numerator of the `W`-orbit term `|W − (W₁∪W₂)|/|W|` of (14.11.4).
Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.ncard_sdiff_sup_add_eq

/-! **Peterfalvi (14.11.4) `P#`/`Q#`-orbit machinery** (`S16_NonExistenceG`, lane γ/POLE-2).  The
`P#`-stab `conj_smul_sharpSubgroup_eq_of_mem_normalizer` (`N_G(P)` permutes `P ∖ {1}`), the assembled
measure `orbit_sharpSubgroup_normSq_term`: `|(P#)^G|/|G| = |P#|/|N_G(P)|` for a TI-subgroup
`Subgroup.IsTI P` (= `IsTISubset (P ∖ {1}) (N_G(P))`), and the numerator `ncard_sharpSubgroup_add_one`
(`|P#| + 1 = |P|`).  The `P`/`Q` orbit terms of (14.11.4), reduced to `IsTI P`/`IsTI Q` and the
`|N_G(P)|`/`|N_G(Q)|` sizes.  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.conj_smul_sharpSubgroup_eq_of_mem_normalizer
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.orbit_sharpSubgroup_normSq_term
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.ncard_sharpSubgroup_add_one

/-! **Peterfalvi (14.11.4) `G₀`-drop set reduction** (`S16_NonExistenceG`, lane γ/POLE-2).
`MHypothesis.famG0_sub_filter_card_le_orbit_ncard`: `|famG₀| − |G₀| ≤ |(W−(W₁∪W₂))^G| + |(P#)^G| +
|(Q#)^G|` (as `ncard`s), from `G₀ ⊆ famG₀` (`G0_off_dadeSupport`) and `famG₀ ∖ G₀ ⊆ orbits`
(`G0_orbit_cover` carrier) via `Set.ncard_sdiff` + `Set.ncard_union_le`.  The set-theoretic core of
the §8 TI-counting of (14.11.4).  Axiom-clean. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.MHypothesis.famG0_sub_filter_card_le_orbit_ncard

/-! **Peterfalvi (8.17.c) `Ã₁`-disjointness bridge** (`S10_MinimalSimpleStructure`, lane β,
issue 0096).  The faithful (8.14) thickened `A₁`-support is the BG `M̃`-cover:
`FT_signalizer_eq_Rsub_of_escape` reconciles the two Theorem-14.4 signalizer choices through the
uniqueness of the maximal over `C_G(x)` (escape forces `1 < |𝓜_σ(x)|` via
`centralizer_le_of_maximalSigma_le_one`, then
`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape` pins both `choose`s);
`ftThickenedSupport_A1_subset_conjClassSet_Mtilde` sends `Ã₁(M) ⊆ 𝒞_G(M̃)` (escaping points are
the defining `x·R(x)` generators, non-escaping points the bare `x·1`); and
`ftThickenedSupport_A1_disjoint_of_nonconjugate` is the (8.17.c) disjointness for non-conjugate
type-I/II maximals (Coq `FT_Dade1_support_disjoint`), by BG 14.5(b)
(`conjClassSet_Mtilde_disjoint`).  The `Ã₁`-side geometry consumed by (8.18.c) → (12.3) → (12.16).
All three sorry-free; axiom-cleanliness gated on the BG `Mtilde`/Theorem-14.4 chain. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S10.FT_signalizer_eq_Rsub_of_escape
#assert_only_allowed_axioms OddOrder.Peterfalvi.S10.ftThickenedSupport_A1_subset_conjClassSet_Mtilde
#assert_only_allowed_axioms OddOrder.Peterfalvi.S10.ftThickenedSupport_A1_disjoint_of_nonconjugate

/-! **Peterfalvi (8.18) mixed support disjointness, type-I pair** (`S10_MinimalSimpleStructure`,
lane β, issue 0096).  The (8.18.c) mixed `Ã₁(S) ∩ Ã(T) = ∅ ∨ Ã₁(T) ∩ Ã(S) = ∅` for
non-conjugate type-I maximals — the geometric obligation of (12.3) — assembled genuinely from
three precise §16 pins ((8.13.b) `escaping_typeIA_mem_A1`, (8.12.b)
`typeI_centralizer_le_and_unique`, (8.13.c2/c4) `supported_sigma_coprime`):
`mem_zpowers_mul_right_of_coprime` (the `π`-part power extraction, sorry-free/axiom-clean),
`escaping_supported_of_A1_conj_mem_typeIA` ((8.18.a): `σ`-order bookkeeping via
`sigma_disjoint_of_nonconjugate` + the unique-maximal pin), `exists_A1_conj_mem_typeIA_of_not_disjoint`
((8.18.b): escaping side lands in the PROVEN `Ã₁`-disjointness, non-escaping side collapses the
coset by the power argument), and `ftThickenedSupport_mixed_disjoint_of_nonconjugate` ((8.18.c):
two-sided support forces `orderOf x' ∣ gcd = 1`).  Axiom checks record the pin-gating. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S10.mem_zpowers_mul_right_of_coprime

/-! **BG Lemma 14.13(a)** (`S16_Lemma1413`, lane β, issue 9003 loop¹⁰³).  The signalizer
non-disjointness lemma `non_disjoint_signalizer_frobenius` — for `x ∈ M_σ^#` with `1 < |𝓜_σ(x)|`
and `σ(N[x]) ∩ π(M) ≠ ∅`, `M` is type `F` with no `τ₂`-primes and Frobenius over `M_σ` — is
**fully proved and axiom-clean**, closing the last Peterfalvi §8 type-I support pin (the
(8.13.c2) cross-coprimality core `escaping_sigma_disjoint_centralizer` in S10).  Assembled from:
the type-`F`/no-`τ₂` Frobenius consequence (`typeF_frobenius_of_tau2_prime_free`), the reduction
(13.9 non-conjugacy, Cor 12.14 `ℳ(C(Q))={Nᵍ}`, 12.1(g) `p∉β(M)`), the no-`τ₂` core (Cor 12.9
`commutator_decomp_of_tau1_action` + `exists_conj_smul_eq_of_le_of_card_prime` cyclic-Sylow
conjugacy), and the type-`P₁` core (`kstar_isHall_sigmaM_of_partner` = Coq `Ptype_embedding`'s
`sMhallKs`, via 14.2(f) `typeP_sigma_subgroup_le_Msigma` + σ-disjoint commutator). -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.non_disjoint_signalizer_frobenius
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.kstar_isHall_sigmaM_of_partner
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.exists_conj_smul_eq_of_le_of_card_prime

/-! **Peterfalvi (14.11.3) support half, axiom-clean core** (`S16_G0Coprime`, lane c/γ).
The concrete Frobenius-kernel model (`commute_inl_mem_range_inl`: in `F ⋊ U*` an element
commuting with a nontrivial additive point lies in the kernel) and its `σ`-transport
(`FieldNormalizerData.derived_inf_centralizer_le_P`: `C_{S'}(x) ≤ P` for `x ∈ P#` from the
(14.2.a) carrier) — the (14.6)/(13.12) discharge engine for the `hfrob` input of the
(14.11.3) coprimality chain.  (The chain lemmas themselves — `not_mem_conjClassSet_sharp_W`,
`orderOf_coprime_p_of_not_mem_conj`, … — are fully proven but inherit `sorryAx` from the
`W₁ ≤ Q`/`reconciled_typePData_T` upstream cites; they join this list when the T-side
reconciliation closes.) -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.commute_inl_mem_range_inl
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.FieldNormalizerData.derived_inf_centralizer_le_P

/-! **Peterfalvi (9.7.b) faithful conjugation field carrier, axiom-clean** (issue 9097, lane a).
The generic `ConjugationFieldModel` bridge constructs the actual additive `GF(r^s)` carrier and
multiplicative complement character from an elementary-abelian kernel with a faithful abelian
conjugation action. The first endpoint identifies every injective cyclotomic-order image with
the norm-one units; the second packages that equality together with Singer's field construction
and equivariance. These are the missing upstream inputs shared by the `P/U` and `Q/V` semilinear
models. -/
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.ConjugationFieldModel.range_eq_normOneUnits_of_injective_card
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.ConjugationFieldModel.exists_normOne_galoisField_conjugation_repr

/-! **Peterfalvi (14.4)/(9.7.b) T-side field model, axiom-clean core** (issue 9078, lane c).
The side-agnostic embedding `SemilinearFieldModel.fieldModelEmbedding` (injective
`σ : F_{r^s} ⋊ V* →* G` with kernel `↦ E`, complement `↦ C`) and its lift-compatibility bridge
`hcompatLift_of_equivariant`, together with the T-side producer `tFieldModelData_of_repr`
(instantiating `E = Q`, `C = V`, `r = q`, `s = p`) and its `σ`-transport
`TFieldModelData.derived_inf_centralizer_le_Q` (`C_{T'}(x) ≤ Q` for `x ∈ Q#`) — the T-side mirror
of the `P`-side engine above.  The symmetric swap construction now supplies the unconditional
T-side case-(9.7.b) facts without the former asymmetric `S_typeP2` gate, so the assembled field
model and its Frobenius-kernel consequence are axiom-clean as well. -/
#assert_only_allowed_axioms OddOrder.RepresentationTheory.SemilinearFieldModel.fieldModelEmbedding
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.SemilinearFieldModel.hcompatLift_of_equivariant
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.tFieldModelData_of_repr
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.TFieldModelData.derived_inf_centralizer_le_Q
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.t_side_caseB_fieldModel
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.t_side_frobenius_kernel

/-! **Peterfalvi (10.8) unconditional + (10.10) case-(a)/(c) engines, axiom-clean**
(issues 1020/1021, lane a).  The unconditional (10.8) `S_not_coherent_unconditional`
(issue 1020 ★★★★), the (10.10) case-(a) coherence `typeV_caseA_coherence`
(Sibley/(6.8) route, ticks 19–24), and the case-(c) coherence engine
`typeV_caseC_coherence_engine` ((10.10.3)/(10.10.4) SHC route, ticks 26–33; its
`hstruct`/`h8`/numeric pins are engine hypotheses, discharged by the (10.10.2)
structure work).  **The three (6.5) gate lemmas are now honestly closed** (issue 9089,
lane a, 2026-07-12): the type-V `𝒮` noncoherence chain was unblocked by generalizing the
§11/§13 six-two decomposition chain to be `htype`/`chief`-free (they were unused), and the
`hcoh` irreducibility bridge (`induce_linear_isIrreducible` — a linear source of a type-`P`
`Hypothesis` induces irreducibly, since the reducible-inducing sources are the nonlinear
certain-type `χ_j`) was proven.  So `typeV_sixFiveA_bound` / `typeV_sixFiveB_pGroup` /
`typeV_sixFiveC_not_dvd`, the assembly `typeV_forces_coherence_v2`, and the (10.10) capstone
`no_typeV_maximal_unconditional` are all axiom-clean — pinned below. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.S_not_coherent_unconditional
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.typeV_caseA_coherence
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.typeV_caseC_coherence_engine
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.induce_linear_isIrreducible
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.typeV_sixFiveA_bound
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.typeV_sixFiveB_pGroup
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.typeV_sixFiveC_not_dvd
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.typeV_forces_coherence_v2
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional

/-! **Peterfalvi (9.11.4) Mackey norm + support, axiom-clean** (issue 9083 Phase D, lane a).
The averaging-projector coset-sum vanishing (the `⟨γ, ψ₁⟩ = 0` engine), the Mackey
conjugation count `‖Ind_K^M 1‖²·|K|² = Σ_x |K ∩ ˣK|` with its `(H·U)·W₁`-fibred evaluation,
the `γ = Ind_{HU₁}^M 1` context facts (support in `HU = M′`, degree `qa`, orthogonality to
`Ind_{HU}^M 𝒳`, cleared norm `‖γ‖²·u = a·u + (q−1)a²` under the (9.11.2) TI-witness
`NineElevenTwoTIWitness`), and the `Hypothesis`-level (9.11.4) bundle
`caseA_nineElevenFour_norm_inputs` (`∃ N, N·u = (a+1)u + (q−1)a²` realized by an
`A₀`-supported `α = γ − ψ₁ ∈ ℤ[Irr M]` with `‖α‖² = N` — the `hnorm` half of
`NineElevenNormBound`; the `|𝒮₄| ≤ N` half is Phase E). -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.sum_apply_mul_eq_zero_of_not_subset_characterKernel
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.inner_induce_trivial_induce_eq_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.inner_induce_trivial_self_mul_card_sq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.sum_card_inf_conjSMul_eq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.nineElevenGamma_inner_self_mul_u
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.nineElevenGamma_inner_induceHU
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.caseA_nineElevenFour_norm_inputs

/-! **Peterfalvi (9.11.1)/(9.11.2)/(9.11.6) Phase-E layers, axiom-clean** (issue 9083 Phase E,
lane a).  The (9.11.2) TI-witness discharge (`U₁ ∩ U₁^w = C` for `w ∈ W₁^#`, via the
`W₁ ↔` Clifford-summand conjugation dictionary and the free-orbit structure of the summands),
the (9.11.1) `𝒮₂ = 𝒮₁` extraction (the saturated-bound subset form and its degree form
`nineElevenSTwoExtraction`), the Bessel constituent count, the `hunif`-free member
`R`-dispatch cross-orthogonality, and the `τ₃`-coherence of `𝒮₃` (Peterfalvi (5.7) at the
uniform degree `qu`).  The `Hypothesis`-level corollaries (`caseA_nineElevenTwo_tiWitness`,
`nineElevenNormBound_of_sevenEightRefutation`, `coherent_sOf_H0Cprime_of_sevenEightRefutation`)
carry the pre-existing upstream `C_eq_cSub` sorryAx debt (as the Phase-B/C corollaries and
caseB do) and join this list when (11.5)/`H0_eq_Hprime` closes. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.nineElevenTwoTIWitness_of_degree_dichotomy
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.conj_smul_cuSubOf_of_Hpart_smul
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.forall_w1_exists_Hpart_smul
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.nineElevenSTwoExtraction
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.caseA_sTwo_subset_degreeQaCut
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S13.card_le_inner_self_re_of_orthonormal_inner_int_ne
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.sOf_H0Cprime_memberRFamily_orthogonal
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.caseA_sThree_coherent

/-! **Peterfalvi (9.11.7)–(9.11.8) coherent-pair adjunction, axiom-clean** (issue 9083 Phase
E-final, lane a).  The union-pair coherent extension (Coq `extend_coherent_with` +
`bridge_coherent`, Peterfalvi (5.6.3)), the (5.5) partial-sum evaluation of coherent
extensions (Coq `mem_coherent_sum_subseq`), the `coherent_ortho` cross-orthogonality, and
the (9.11.7)–(9.11.8) projection budget (`‖Γ‖² = 1`, `Δ = 0`, `b = 0`, and the bridge
`β^τ = Γ − e·τ₁ψ₁`).  The discharge `nineElevenSevenEightRefutation` itself and the (9.11)
capstones `coherent_sOf_H0Cprime` / `coherent_sOf_H0C` carry the pre-existing upstream
`C_eq_cSub` sorryAx debt (as the Phase-B/C corollaries and caseB do) and join this list
when (11.5)/`H0_eq_Hprime` closes. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.unionPairExtension
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.isCoherent_union_pair_of_bridge
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.coherent_extension_eq_sum_memberRFamily
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.coherent_extension_cross_orthogonal
#assert_only_allowed_axioms OddOrder.Peterfalvi.S13.exists_bridge_target_of_budget

/-! **Peterfalvi (8.13), axiom-clean** (lane a, 2026-07-12).  The escaping-centralizer control:
for `X = A₁(M)` (any Peterfalvi type) or the type-`P₁` `A₀(M)` (`typePA0`; the `P₁` restriction
is honest — issue 9008: `typePA0` over-claims for type II), every `x ∈ X` with `C_G(x) ⊄ M` lies
in `A₁(M) = M_σ^#` and `C_G(x)` sits inside a *unique* maximal subgroup of type I/II.  Pure
assembly of the BG §16 signalizer machinery (`A1_eq_sigmaSharp`,
`escaping_typePA0_mem_sigmaSharp_of_isTypeP1`,
`existsUnique_maximal_centralizer_le_typeI_or_typeII` — BG Theorem II / B(5) / D(4), the book's
Reference line), all of which is axiom-clean. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S10.escapingCentralizers_control

/-! **The `W₁`-orbit congruence `u ≡ 1 (mod q)`, axiom-clean** (lane a, 2026-07-12, issue 1024).
The Frobenius fixed-point-freeness of the `W₁`-conjugation on the `U`-action image
`Ū = U/C_U(H̄)` (`fixedSubgroup_quotient_uActionKer_eq_bot`, the coprime descent of
`C_U(W₁) = 1`), and the prime-order orbit count `|Ū| ≡ 1 (mod q)` — the `q ∣ u − 1` input of
the Peterfalvi (11.9.c) non-Galois contradiction `q ≤ u − 1 < u = a ≤ p − 1 < p`. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.fixedSubgroup_quotient_uActionKer_eq_bot
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.card_uActionHom_range_modEq_one

/-! **ZIrr-Galois 内積 transport (shared leaf), axiom-clean** (lane a, 2026-07-12, issue 9085).
`mapRingEquiv` の ZIrr 上 ℤ-等長性と Galois 係数定数性 engine — (10.9)/(11.9.a) 型 grid 解析の
(3.9.b) 行/列定数性の generic 核 (S16 TGapGalois の generic 部 hoist)。 -/
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.inner_mapRingEquiv_eq_of_mem_ZIrr
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.inducedFamily_closedUnderMapRingEquiv
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.mapRingEquiv_muColumnZero_sum

/-! **(3.9.b) chiFam pair-move (Galois 転送), axiom-clean** (lane a, 2026-07-12, issue 1024 G3).
素数位数 W₁/W₂ 側の punctured 行/列上で (3.5) family の 2 点が Galois 共役 — (11.9.a) 行0射影の
係数定数性入力。 -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_mapRingEquiv_chiFam_left_move
#assert_only_allowed_axioms OddOrder.Peterfalvi.S05.TICyclicHypothesis.exists_mapRingEquiv_chiFam_right_move

/-! **(11.9.a) Galois 補正層 (S13_TypeIIIGalois), axiom-clean** (lane a, 2026-07-12, issue 1024 C0).
Galois twist の S(HC)-stratum 安定性、τ(ζ−σζ) の τ₁-展開、および補正項の grid 直交 —
a_aut 定数性 engine への hcorrection 供給。 -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.mapRingEquiv_mem_SHC_stratum
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.tau_zeta_sub_mapRingEquiv_eq_SHC_extension
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.w1_prime_of_typeIIIorIV
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.mapRingEquiv_tau_muColumnZero_sub_zeta
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.inner_tau_muColumnZero_sub_zeta_columnZero_const
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.inner_tau_muColumnZero_sub_zeta_rowZero_const
#assert_only_allowed_axioms OddOrder.RepresentationTheory.sum_sq_inner_le_of_orthonormal

/-! **Peterfalvi (11.9.a) 行0射影, axiom-clean** (lane a, 2026-07-12, issue 1024).
h118 ((11.8) 非直交) 下で τ(μ₀−ζ) の σ-grid 係数 = 行0 indicator。a₀₀=1 + Galois 定数性 +
(3.7) 分離 + Bessel (w₁+1 予算) + 整数 case 分析 (列0形は h118 で排除) の完全組立。 -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSigmaGrid_columnZero_sum_inner
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.inner_tau_muColumnZero_sub_zeta_rowZero_of_residual_not_orthogonal
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.caseA_exists_irreducible_qa
#assert_only_allowed_axioms OddOrder.Peterfalvi.S11.caseA_a_dvd_u
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.rowInv_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S06.certainTypeRImage_conj

/-! **Peterfalvi (11.9.c) 非Galois u=a pin 部品, axiom-clean** (lane a, 2026-07-12, issue 1024).
muColumnChar_zero / exists_muColumnChar_inv = Pontryagin 逆列 index。keystone
`caseA_u_eq_a_of_residual_not_orthogonal` (u=a pin 本体) は証明完備。
⚠ **訂正 (2026-07-12 lane-a census、issue 9088)**: 残 dirty は「lane-b の (9.11.2) refuter sorry」
**でない** — `coherent_sOf_H0Cprime`→`nineElevenSevenEightRefutation` (body sorry-free) の
optParam DEFAULT `(hncH0C := S_H0C_not_coherent)` `(htype := isTypeIIIorIV)` = **lane-a の
(10.8)/(10.10) legacy 汚染 (issue 1025 [[lean-optparam-default-contaminates-axioms]])**。honest heir
(`S_H0C_not_coherent_unconditional`/`no_typeV_maximal_unconditional`) 既存。着地 = 1025 の
optParam→explicit+wrapper rework を (9.11)/(11.9) chain に適用時。 -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.muColumnChar_zero
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.Hypothesis.exists_muColumnChar_inv

/-! **nilpotent + cyclic abelianization ⟹ cyclic, axiom-clean** (lane a, 2026-07-12, issue 9086).
Pf (11.9.c) caseB 帰結の一般群論 engine (mathcomp `cyclic_nilpotent_quo_der1_cyclic` 対応):
下降中心列の安定化 (γ₂ ≤ ⁅γ₂,⊤⁆) + center-quotient cyclic → abelian。 -/
#assert_only_allowed_axioms OddOrder.GroupTheory.commutator_eq_bot_of_isNilpotent_of_isCyclic_quotient
#assert_only_allowed_axioms OddOrder.GroupTheory.isCyclic_of_isNilpotent_of_isCyclic_quotient
#assert_only_allowed_axioms OddOrder.GroupTheory.isCyclic_of_isNilpotent_of_ker_le_commutator

/-! **Peterfalvi (11.9.b) character core `card_kappaHall_lt_of_isTypeIIIorIV`, axiom-clean**
(lane a, 2026-07-13, issues 1025/9091).  The FT-spine endpoint `|K*| < |K|` for a type-III/IV
maximal subgroup — the honest heir of the retired legacy chain — is now `#print axioms`-clean:
the (10.8) legacy `S12.S_not_coherent` (bare-sorry `typeII_coherence_contradiction_estimate`) and
the (10.10) legacy `no_typeV_maximal` (bare-sorry `typeV_forces_coherence`) are fully rewired to
their axiom-clean heirs `S_not_coherent_unconditional` / `no_typeV_maximal_unconditional`
(`S12_Noncoherence`) via `isTypeIIIorIV_unconditional` + the `_of_noncoherent` explicit-parameter
threading through the §11/§13 (11.3)-noncoherence chain (the optParam-DEFAULT contamination of
commit 435b057a replaced by explicit params + legacy wrappers,
[[lean-optparam-default-contaminates-axioms]]).  `card_kappaHall_lt_of_isTypeP1` (the type-`P₁`
consumer) is clean as a corollary.  ⚠ `feitThompson` itself remains sorry-dirty via **other**
consumers (cross-lane §14/§15/§16 T-side + the legacy `no_typeV_maximal`/`S_not_coherent` still
cited off the card_kappaHall subtree); the spine character core is the lane-a contribution. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S12.isTypeIIIorIV_unconditional
#assert_only_allowed_axioms OddOrder.card_kappaHall_lt_of_isTypeIIIorIV
#assert_only_allowed_axioms OddOrder.card_kappaHall_lt_of_isTypeP1

/-! **Peterfalvi (8.17) BG-Theorem-E cover interface `bgTheoremE_cover_data`, axiom-clean**
(lane a, 2026-07-13, issue 9087 census 訂正).  The §10 covering interface (representatives of
maximal conjugacy classes, `π(G)` partition by the `π((M_i)_s)`, thickened `A₁(M_i)` counts) is
fully proven off the BG §14/§16 σ-decomposition layer (`genuineSigmaDecomposition`,
`exists_peterfalviType`, `mainSubgroup_eq_Msigma`).  Tripwire: this is the B2 input
(`card_LF_coprime_pq`, §15 gate 4) and the (12.9) `exists_second_maximal` cover step. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S10.bgTheoremE_cover_data

/-! **Peterfalvi (14.9) T-side type-III determination `T_isTypeIII_of_isTypeP1`, axiom-clean**
(lane a, 2026-07-13, issues 9077 T1 / 9093).  The `hVcomm` residual (`V` abelian, (11.9)-gated)
of `T_not_isTypeIV_of_isTypeP1` is discharged by the universal (11.9.c) Type-IV exclusion
`not_isTypeIV_of_mem_maximalSubgroups` (`S13_NonGaloisExclusion`, sorry-free), citable from §16
after the 9093 import inversion broke the `S13_NonGaloisExclusion → §16` transitive edge. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.T_not_isTypeIV_of_isTypeP1
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.T_isTypeIII_of_isTypeP1

/-! **Peterfalvi (8.17.a) coprimality (gate-4 B2) `card_LF_coprime_pq`, axiom-clean**
(lane a, 2026-07-13, issue 9087 RULING #4 carve-out).  For a type-I maximal `L` not conjugate
to `S`/`T`, `|L_F| ⟂ pq` — proven from the BG-Theorem-E cover (`bgTheoremE_cover_data`,
`primeFactors_disjoint`) by transporting `p ∈ π(S_σ)`, `q ∈ π(T_σ)`, and `π(L_F) = π(L_σ)`
along `Msigma_conj_smul` to the conjugacy representatives.  The (13.17.b) type-I-branch
kernel coprimalities `q_not_dvd_kernel` / `p_not_dvd_kernel` are clean as corollaries. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.card_LF_coprime_pq
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.q_not_dvd_kernel
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.p_not_dvd_kernel

/-! **Frobenius kernel contains the Fitting subgroup `IsFrobeniusGroup.fitting_le_kernel`,
axiom-clean** (lane a, 2026-07-13, issue 9087 RULING #4 carve-out, 2/3).  A normal `p`-subgroup
of a Frobenius group lies in the kernel (`normal_pGroup_le_kernel`: quotient-order coprimality
when `p ∣ |N|`, commutator + Thm 6.4 centralizer containment when `p ∤ |N|`), hence
`F(G) = ⨆ p, O_p(G) ≤ N`.  Tripwire: this is the (12.7)-side input pinning `F(M) ≤ M_F` in the
all-type-I `FittingIsTI` gate (`allTypeI_fittingIsTI`, Pf (8.13.c1)+(2.3), `S14` covering). -/
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.IsFrobeniusGroup.normal_pGroup_le_kernel
#assert_only_allowed_axioms OddOrder.Isaacs.Ch06.IsFrobeniusGroup.fitting_le_kernel

/-! **Peterfalvi (7.9) Frobenius-family conclusion `hypothesis79_conclusion`, axiom-clean**
(lane a, 2026-07-13, issue 0044 cont.⁴⁹).  The (7.9) dichotomy `⟨β_i, ζ_j^ν⟩ ≠ 0 ∨
⟨β_j, ζ_i^ν⟩ ≠ 0` for distinct members of a `FrobeniusFamily`, via the parity route:
`hdelta_even` (`hypothesis79_delta_even`) assembles `Δ ∈ ℤ[Irr G]` (Sibley coherence), `Δ` real
(the delta-reality milestone `hypothesis78_delta_isReal`), `⟨Δ, 1⟩ = 0`, and the odd-order
parity primitive `cfdot_real_vchar_even`.  Tripwire: this is the `hbeta_ne` source for the
good-index norm estimates consumed by the completed (7.10) `card_G0_lower_bound`
assembly on the (12.17) chain (`theorem88_caseB_holds` → FT spine). -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis79_delta_even
#assert_only_allowed_axioms OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis79_conclusion

/-! **Peterfalvi (7.10) family-wide weighted orthogonality, axiom-clean**
(lane a, 2026-07-14, issue 0044 cont.⁵⁰).  Every non-principal induced-family
member has a distinct conjugate partner in odd order; coherence carries their
difference into the Dade support.  Disjoint kernel spreads then give
cross-orthogonality for every pair of members and hence for the weighted sums.
The diagonal weighted norm is evaluated by the induced-family Burnside
degree sum as (h_i - 1) / e_i = BsumWeight i. -/
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis79_zeta_cross_eq_zero_at
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis79_weightedNuSum_cross_eq_zero
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_weightedNuSum_inner_self_eq_BsumWeight

/-! **Peterfalvi (7.10) weighted Gamma projection and concrete B-set, axiom-clean**
(lane a, 2026-07-14, issue 0044 cont.⁵³).  Integral cross-family coefficients
project Gamma onto the pairwise orthogonal weighted coherent sums.  Subtracting
those projections constructs Gamma₁, while the (7.9) alternative makes every
coefficient on B = {j ≠ i | ⟨β_j, ζ_i^ν⟩ = 0} nonzero.  The final theorem exposes
the decomposition, diagonal BsumWeight formula, residual orthogonality, and
nonzero coefficients consumed by the existing B-sum norm bridge. -/
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.Cert.exists_orthogonal_projection_residual
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis79_gamma_inner_weightedNuSum_eq_mul_BsumWeight
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.exists_weightedGammaDecomposition_on_reverseCoefficientZeroIndices

/-! **Peterfalvi (7.8.b) concrete Frobenius-family Gamma norm bound, axiom-clean**
(lane a, 2026-07-14, issue 0044 cont.⁵⁴).  The induced principal source norm,
orthogonality to the distinguished non-principal character, and Dade isometry
give `‖beta‖² = e + 1`.  Combining this with the proved weighted-sum norm and
the canonical beta decomposition yields the exact quadratic Gamma formula;
the odd-order Frobenius inequality `2e + 1 ≤ h` then gives
`‖Gamma_i‖² ≤ e_i - 1`. -/
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.gammaAt_inner_self_re_le

/-! **Peterfalvi (7.10) concrete B-sum bound, axiom-clean**
(lane a, 2026-07-14, issue 0044 cont.⁵⁵).  On the exact set of indices whose
reverse cross coefficient vanishes, (7.9) supplies nonzero integral projection
coefficients and an orthogonal weighted Gamma decomposition.  The concrete
(7.8.b) Gamma norm bound therefore gives
`sum_{j in B} (h_j - 1) / e_j ≤ e_i - 1`. -/
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.reverseCoefficientZeroIndices_Bsum_le

/-! **Peterfalvi (7.8.c)/(7.10) concrete good-index bound, axiom-clean**
(lane a, 2026-07-14, issue 0044 cont.⁵⁶).  The distinguished coherent image is
first resolved as a signed irreducible character.  Cross-family orthogonality,
the nonzero reverse coefficient outside B, and the integral (7.8.c) formula
give the local sharp-kernel ratio bound; rho-linearity transports it back
across the sign to the canonical coherent image. -/
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.reverseCoefficientZeroIndices_good_bound

/-! **Peterfalvi (7.8.b) canonical selected-character bound, axiom-clean**
(lane a, 2026-07-14, issue 0044 cont.⁵⁷).  The canonical distinguished
coherent image used to define the concrete B-set is fed through the proved
BetaDecomp coefficient identities, induced-family degree sum, and Frobenius
small-index inequality.  This identifies the selected-index rho norm required
by the final (7.5)/(7.10) CharacterEstimateData assembly. -/
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.distinguishedNuAt_chiRhoNormSq_ge

/-! **Peterfalvi (7.10)–(7.11) final Frobenius-family assembly, axiom-clean**
(lane a, 2026-07-14, issue 0044).  Choose a member of minimal kernel order,
take the canonical distinguished coherent image and the reverse-coefficient
zero set, and combine signed irreducibility, norm one, the concrete B-sum
bound, and selected/good-index rho estimates into `CharacterEstimateData`.
The explicit per-member nilpotence input is constructed by the FT consumer
from `maxNilpotentNormalHall_isNilpotent`; it is not an opaque carrier field. -/
set_option linter.style.longLine false in
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S09.FrobeniusFamily.characterEstimateData_of_isNilpotent
#assert_only_allowed_axioms OddOrder.Peterfalvi.S09.card_G0_lower_bound
#assert_only_allowed_axioms OddOrder.Peterfalvi.S09.not_trivial_G0

/-! **BG §16 → Peterfalvi §10/§14 → Section 16 named-input producer chain, axiom-clean**
(lane a, 2026-07-14, issue 9087).  The three tame-embedding consumers now cite the faithful
Theorem A interface, so the maximal-pair construction, its type-I Dade consequences, and the
assembled Section 16 inputs depend only on Lean/mathlib's standard three axioms. -/
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.theoremII_tame_embedding_of_inputs
#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.theoremII_tame_embedding
#assert_only_allowed_axioms OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_of_subset
#assert_only_allowed_axioms OddOrder.Peterfalvi.S10.dadeSupportHypotheses_typeI
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.hypothesis_of_typeIData
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.typeI_frobenius
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.not_all_maximal_typeI
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.theorem88_caseB_holds
#assert_only_allowed_axioms OddOrder.exists_section16MaximalPair_data
#assert_only_allowed_axioms OddOrder.section16MaximalPair_of_isMinimalSimpleOdd
#assert_only_allowed_axioms OddOrder.section16Inputs_of_isMinimalSimpleOdd
#assert_only_allowed_axioms OddOrder.sectionSixteenHypothesis_of_isMinimalSimpleOdd

/-! **Peterfalvi (4.6) type-`P₂` Dade producer on the canonical `muS` instance, axiom-clean**
(lane a, 2026-07-14, issues 2038/9081).  The honest `A₀(S)` Dade data now constructs the full
`Hypothesis46`; its Dade-free core remains separately guarded as the exact prerequisite of the
(4.7)/(4.8)-(1) support engine. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.dadeSupportHypothesisData_honestTypeP2A0Set
#assert_only_allowed_axioms OddOrder.Section16CharacterData.hyp46Smp
#assert_only_allowed_axioms OddOrder.Section16CharacterData.hyp46SmpCore

/-! **Peterfalvi (9.11) caseA-`T` base coherence on `Ind_T^G`, axiom-clean** (lane b,
2026-07-14, issue 2035).  The degree-`p·a` irreducible cut of the `T`-instance §9 family: the
(9.8.d) base count with conjugacy doubling, the (5.7)∘(5.3.a) uniform-degree coherence
re-grounded onto plain induction via `tInstance_dade_eq_induce`, and the assembled caseA-`T`
`h0` entry point. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.sSetIrrDegT_pa_two_le_ncard
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.sSetIrrDegT_coherent_indT
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.sSetIrrDegT_pa_coherent_indT_caseA

/-! **Peterfalvi (9.11) at `T` — the full refuter chain, axiom-clean** (lane b, 2026-07-14,
issue 2035 refuter-`T` campaign).  The complete `T`-mirror of the discharged `S`-side
(9.11.1)–(9.11.8) chain: the (5.6) pair bound, the (9.11.1) extraction, the (9.11.4) Coq
gap-patch support + Mackey-norm bundle, the (9.11.7)–(9.11.8) budget refutation, the
(9.11.5)–(9.11.8) norm bound and equality refutation, the assembled equality-configuration
refuter (formerly the one intended sorried obligation), the full-family `𝒯`-coherence
dispatches, the (13.3.c)-`T` pinned carrier, and the bundled `τ₁T` ν-row pin. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.nineElevenPairBoundT
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.nineElevenSTwoExtractionT
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.nineElevenAlphaSupportT
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.nineElevenFourNormInputsT
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.nineElevenSevenEightRefutationT
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.nineElevenNormBoundT
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.nineElevenEqualityRefutationT
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.sSet_caseA_nineElevenRefutation_T
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.sSet_coherent_indT_caseA
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.sSet_coherent_indT_A
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.sSet_coherent_indT_A_pinned
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.tau1T_ofHonest_nuRow_eta_row

/-! **Peterfalvi (13.3.c)-`T` ν-row pin machinery, first layer, axiom-clean** (lane b,
2026-07-14, issue 2035 #41 step 4-5).  The coherence-generic row-independence
`c(ν_r) − c(ν_s) = ∑_j η_{rj} − ∑_j η_{sj}` (per-column `tauT_nu_cross` through
`tInstance_dade0_eq_induce`) and the (5.3.b)-at-`T` grid orthogonality of coherent images
(the `A₀(T)`-Dade regular vanishing + the (3.7)–(3.8) norm-two engine). -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.coherentIndT_nuRow_diff
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.coherentIndT_image_inner_eta_eq_zero

/-! **Peterfalvi (13.3.c)-`T` ν-row pin dichotomy, axiom-clean** (lane b, 2026-07-14, issue
2035 #41 step 4).  Any coherent extension of `𝒯` on `Ind_T^G` sends a reducible ν-row either to
the aligned `η`-row or to the negated conjugate row (γ-trick + (3.7) rectangle relation with
row-0 corners + `‖·‖² = p`); the clean pivot pin propagates to all rows through the
row-independence. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.coherentIndT_nuRow_pin_of_irr
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.coherentIndT_nuRow_eq_etaRow_of_pivot
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.exists_pinned_coherent_sSet_of_all_reducible_T

/-! **(1.5.a)-at-`T` membership layer, axiom-clean** (lane b, 2026-07-14, issue 2035 #41 step
5).  `Ind_K^T θ ∈ ℤ[𝒯]` for irreducible `θ` on `K = QD` with `Q ⊄ Ker θ` (two-stage induction
through `T' = huSub`, constituent kernel transfer), and the degree-`0` `A(T)`-support of
`ℤ[𝒯]`-elements. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.induce_K_mem_zSpan_T
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.zSpan_sSet_degree_zero_support_T
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.Hypothesis.induce_K_mem_zSpan_sSet_irr_T

/-! **The (13.4) dirr cross-orthogonality bricks, axiom-clean** (lane b, 2026-07-14, issue
2035 #41 step 6): the conjugate identification `B = Ā` for conjugation-antisymmetric norm-one
`ℤ`-irreducible pairs, and the cross-`τ` lead orthogonality `⟨A, C⟩ = 0` from orthogonal
differences — the "pairwise orthogonality of `η`, `λ^{τ₁}`, `θ^{τ₁}`" of Peterfalvi (13.4). -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.conj_eq_of_norm_one_conj_antisym
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.inner_eq_zero_of_conj_diff_orthogonal

/-! **Peterfalvi (12.6) `frobenius_typeI_coherent`, axiom-clean** (lane c, 2026-07-14, issue
9077 carve-out item 2 + HUB RULING #4′).  The (6.8)(c1) structural input `sibleyTarget_frobI`
is now honestly constructed — the TI bound collapsed to `L` through the (8.15) normalizer
identification, the (12.1) Dade datum transported exactly (`tau_eq` on the nose), and the
`card_L_odd` faithfulness fix (`hodd` hypothesis) approved by RULING #4′ — closing the last
gap of the (12.6) case split: all three coherence routes (a) TI/(6.8), (b) abelian rank-2
(5.7), (c) cyclic-quotient (6.5.c) are real. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.sibleyTarget_frobI
#assert_only_allowed_axioms OddOrder.Peterfalvi.S14.frobenius_typeI_coherent

/-! **Peterfalvi (14.6), sharp case-(9.7.a) Sylow bridge.**  A faithful two-coordinate
block-scalar embedding of sharp square order has noncyclic Sylow subgroups at every prime
dividing the coordinate exponent; odd-order scalar images specialize the exponent to
`(p - 1) / 2`. -/
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.sylow_not_isCyclic_of_card_eq_sq_of_injective_pi
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.sylow_not_isCyclic_of_odd_blockScalarEmbedding
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.caseA_sylow_not_isCyclic_of_sharp_order
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S11.caseA_sylow_U_not_isCyclic_of_sharp_order
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.caseA_sylow_U_not_isCyclic_of_parameters

/-! **Peterfalvi (14.6), BG Prop. 1.16 centralizer witness.**  The ambient image of a
noncyclic Sylow subgroup of the abelian `S`-side complement normalizes `P`; its `r`-power
order is coprime to `|P| = p^q`.  BG Prop. 1.16 therefore produces a nonidentity element
whose centralizer in `P` is nontrivial. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.exists_sylow_mem_inf_centralizer_ne_bot_of_not_isCyclic
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.caseA_exists_sylow_mem_inf_centralizer_ne_bot_of_parameters

/-! **Peterfalvi (14.6), ambient Sylow carrier.**  For every ambient subgroup containing `U`,
the noncyclic `R₀ ∈ Syl_r(U)` extends to a Sylow `r`-subgroup while retaining the BG Prop. 1.16
centralizer witness. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.exists_sylow_over_U_with_centralizer_witness_of_not_isCyclic

/-! **Peterfalvi (14.6), Sylow center trapping.**  The named complement `U` is Hall in `S`;
the BG Prop. 1.16 witness belongs to the honest type-`P₂` TI-set, so its ambient centralizer
lies in `S`.  Sylow maximality identifies `C_R(x)` with `R₀`, hence `Z(R) ≤ R₀`. -/
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.coprime_card_U_index_S
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.sylow_center_le_U_sylow_of_centralizer_witness
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.exists_sylow_over_U_with_trapped_center_of_not_isCyclic

/-! **Peterfalvi (14.6), order of `Ω₁(Z(R))`.**  Under the explicit (13.12)/(13.13)
inputs `c = 1` and `q = 3`, the two-coordinate scalar action on the actual `U` is faithful,
so `rank U ≤ 2`.  The nontrivial elementary abelian subgroup `Ω₁(Z(R)) ≤ R₀ ≤ U`
consequently has order `r` or `r²`. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.caseA_rank_U_le_two_of_c_eq_one_q_eq_three
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.omega1Center_card_eq_prime_or_sq_of_rank_U_le_two
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.caseA_omega1Center_card_eq_prime_or_sq_of_parameters

/-! **Peterfalvi (14.6), fixed-point-free action on `Ω₁(Z(R))`.**  A subgroup of
the Frobenius complement normalizing the Sylow subgroup also normalizes its characteristic
center layer.  Frobenius orbit counting gives `p ∣ |Ω₁(Z(R))| - 1`, hence `p ∣ r² - 1`;
the (14.5) type-I-over-normalizer carrier supplies the concrete conjugate `W₂^y`. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.prime_dvd_sq_sub_one_of_frobenius_omega1Center
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.TypeIOverNormalizerData.prime_dvd_sq_sub_one_of_omega1Center

/-! **Peterfalvi (14.6), final case-A contradiction.**  A prime
`r ∣ (p - 1) / 2` has a noncyclic Sylow subgroup in `U`; center trapping and the
fixed-point-free `W₂^y` action give `p ∣ r² - 1`.  Odd-prime comparison gives
`p < r`, contradicting `r ≤ (p - 1) / 2`.  The case-A parameter equalities are
explicit inputs, so this capstone does not use the issue-0116 analytic producer. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.false_of_odd_primes_dvd_half_and_sq_sub_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.caseA_false_of_parameters_and_typeIOverNormalizerData

/-! **Peterfalvi (14.6), S-side Galois-field model.**  In Clifford case (9.7.b),
the §9 Singer realization transports from the chief quotient to the named groups
`P` and `U` because `H₀ = ⊥`, `H = P`, and `C_U(P) = 1`.  The branch-independent
endpoint eliminates case (9.7.a) using the prime contradiction above.  The sharp
parameters are required only conditionally on an actual case-(a) certificate;
that producer and the type-I-over-normalizer carrier remain explicit, so no
issue-0116 analytic producer is hidden. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.U_le_normalizer_P
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.conj_mem_P
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.caseB_exists_sSide_galoisField_repr_of_c_eq_one
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.sSide_galoisField_repr_of_c_eq_one_and_caseA_parameters
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.sSide_galoisField_repr_of_parameters_and_typeIOverNormalizerData

/-! **Peterfalvi (13.3), the λ-free core** (issue 9094 案 A + issue 2035 #92).
`CharacterDegreeCore` is inhabited unconditionally: `τ₁ = tau1S_ofHonest` with its five
guarded field supplies, the (13.3.a) `𝒮₁`-witnessed `μ`-facts, the (13.3.c) `S`-side
signs `δ_j = 1`, and the (13.3.c) column formula.  The δ′-half of (13.3.c) is
restate-dropped from the field (consumer 0, issue 2035 #92) with the standing supply kept
in `deltaPrime_eq_one_T`, so the core producer is axiom-clean without waiting for the
ν-carrier threading (issue 9096). -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.characterDegreeCore_nonempty

/-! **Peterfalvi (13.10)–(13.13), issue 0116 Core full-flip chain.**
The analytic estimate and its order consequences now consume the honest
`CharacterDegreeCore` route with an explicit canonical ν-grid supply.  In particular, the
unconditional `c = 1` endpoint uses the λ-dichotomy and the upstream type-`P` structure of
`Q`, not the later type-II conclusion, so these assertions also guard against reintroducing
the former (13.12) ↔ (14.9) proof cycle. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.CharacterDegreeCore.analytic_inequality_of_caseB_facts
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.CharacterDegreeCore.c_eq_one_of_caseB_facts
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.CharacterDegreeCore.caseA_parameters_of_caseB_facts
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.c_eq_one_of_lambda_dichotomy

/-! **Peterfalvi (13.12)–(14.4), symmetric T-side Core chain.**
The §13 carrier and `Hypothesis.swap` are now genuinely symmetric in `S` and `T`: the swap uses
the unconditional type-`P`/commutativity facts from `T_nonI`, so the old downstream
`IsTypeP2 T` gate is absent.  These assertions pin the swapped `d = 1`, full Singer order, and
the assembled T-side case-(b) facts to Lean/mathlib's standard three axioms. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.d_eq_one_of_swapped_lambda_dichotomy
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S15.Hypothesis.T_caseB_v_eq_full_of_swapped_lambda_dichotomy
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.T_caseB_facts_of_q_lt_p_core
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.T_caseB_facts_unconditional

-- Ch.10 (More Transfer Theory) §10A: Thm 10.1 Yoshida — P Sylow, v(G) < P/P' ⇒
-- G は C_p ≀ C_p 上へ全射 / Thm 10.11 (self-normalizing 系の帰結)
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch10.exists_surjective_wreath_of_transfer_range_lt
#assert_only_allowed_axioms OddOrder.Isaacs.Ch10.exists_normal_index_prime_transfer_mem

-- Ch.10 §10B: Thm 10.12 Huppert — p > 2, nonabelian metacyclic Sylow p ⇒
-- p ∣ |G : G'|, Thm 10.15 正規 Sylow 版
#assert_only_allowed_axioms OddOrder.Isaacs.Ch10.dvd_index_commutator_of_metacyclic_sylow
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch10.dvd_index_commutator_of_normal_metacyclic_sylow

-- Ch.10 §10C: Thm 10.20 G/G' ≅ Δ(G)/Δ(G)² / Thm 10.25 v(g)^{|K:G'|} = 1 /
-- Thm 10.18 Furtwängler principal ideal theorem (transfer G → G'/G'' 自明) /
-- Cor 10.28 Alperin-Kuo g^{|G : G'∩Z(G)|} = 1
#assert_only_allowed_axioms OddOrder.Algebra.abelianizationEquivAugmentationQuotient
#assert_only_allowed_axioms OddOrder.Algebra.transfer_pow_relindex_eq_one
#assert_only_allowed_axioms OddOrder.Isaacs.Ch10.transfer_commutator_eq_one
#assert_only_allowed_axioms OddOrder.Isaacs.Ch10.pow_index_commutator_inf_center_eq_one

/-! **Feit–Thompson end-to-end axiom audit** (2026-07-15, issues 9077/0118/0121).
The honest T-side `(13.12)` producer supplies `D = ⊥` downstream of the character-degree layer;
the explicit-`D = ⊥` `(13.16)`/Huppert chain avoids the genuine §15 import cycle.  Rebuilding the
BG Appendix C bridge then certifies the complete path from Peterfalvi §16 through the
minimal-counterexample reduction.  Every endpoint below depends only on Lean/mathlib's standard
three axioms (`propext`, `Classical.choice`, `Quot.sound`), in particular not on `sorryAx`. -/
#assert_only_allowed_axioms
  OddOrder.Peterfalvi.S16.Hypothesis.V_inf_centralizer_Q_eq_bot
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.normalizer_W1_of_D_eq_bot
#assert_only_allowed_axioms OddOrder.Peterfalvi.S15.complement_le_QW2_of_D_eq_bot
#assert_only_allowed_axioms OddOrder.Peterfalvi.S16.nonexistence_of_G
#assert_only_allowed_axioms OddOrder.BG.AppC.final_contradiction
#assert_only_allowed_axioms OddOrder.noMinimalSimpleOdd_of_section16
#assert_only_allowed_axioms OddOrder.noMinimalSimpleOdd
#assert_only_allowed_axioms OddOrder.feitThompson_of_noMinimalSimpleOdd
#assert_only_allowed_axioms OddOrder.feitThompson
