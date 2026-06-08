/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Lean
import OddOrder.Algebra.AlgInt
import OddOrder.GroupTheory.ChermakDelgado
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
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch05_Transfer.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main
import OddOrder.BG.Ch1_Preliminary.S01_Solvable
import OddOrder.BG.Ch1_Preliminary.S04d_GorThm415
import OddOrder.BG.Ch1_Preliminary.S04e_GorThm37
import OddOrder.BG.Ch1_Preliminary.S04g_Thm418
import OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups
import OddOrder.BG.Ch1_Preliminary.S01b_Prop116
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
import OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal
import OddOrder.BG.AppA_PStability
import OddOrder.BG.AppB_Puig
import OddOrder.BG.AppB_PuigB3B4
import OddOrder.BG.AppB_Thm62
import OddOrder.Peterfalvi.S03_PreliminaryCharacter
import OddOrder.Peterfalvi.S04_DadeIsometry
import OddOrder.Peterfalvi.S05_TICyclic
import OddOrder.Peterfalvi.S05_SigmaIsometry
import OddOrder.Peterfalvi.S07_Coherence
import OddOrder.Peterfalvi.S07_CoherenceGalois
import OddOrder.Peterfalvi.S08_CoherenceTheorems
import OddOrder.Peterfalvi.S09_NonexistenceCertain
import OddOrder.FeitThompson
import OddOrder.BG.AppC_NormSet
import OddOrder.BG.AppC_FrobeniusClassSum
import OddOrder.BG.AppC_LemmaC2

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

-- Ch.5 (Transfer): Lem 5.12 (N_G(P) controls C_G(P) fusion)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.normalizer_controls_centralizer_fusion

-- Ch.5 (Transfer): Thm 5.13 (Burnside normal p-complement)
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer

-- Ch.5 (Transfer): Thm 5.20 (focal transfer kernel is A^p(G))
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.APrime_eq_transferFocal_ker

-- Ch.5 (Transfer): Thm 5.21 (Focal Subgroup Theorem)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.focalSubgroupTheorem

-- Ch.5 (Transfer): Thm 5.25 (normal p-complement iff Sylow controls own fusion)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_controlsOwnFusion

-- Ch.5 (Transfer): Thm 5.26 (Frobenius normal p-complement)
#assert_only_allowed_axioms
  OddOrder.Isaacs.Ch05.hasNormalPComplement_iff_isPGroup_normalizer_quotient_centralizer

-- Ch.5 (Transfer): Cor 5.29 (prime-divisor obstruction gives normal p-complement)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.hasNormalPComplement_of_no_prime_dvd_pow_sub_one

-- Ch.5 (Transfer): Cor 5.30 (odd p, order-p elements central)
#assert_only_allowed_axioms OddOrder.Isaacs.Ch05.normal_p_complement_of_order_p_central_odd

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

-- Ch.7 (Thompson Subgroup): Thm 7.8 Burnside p^a q^b solvability ⭐⭐⭐ **character-free**
-- |G| = p^a q^b ⇒ G solvable.  Goldschmidt-Bender-Matsuyama 9-step proof (no character
-- theory).  Steps 1-9 + Step 3 の faithful-action 分岐まで full discharge; §7D 内に
-- sorry / project-axiom 残無し ⇒ 真に unconditional.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch07.burnside_p_pow_q_pow

-- Ch.3 (Split Extensions): Thm 3.12 Schur-Zassenhaus conjugacy ⭐⭐⭐ **FT クリティカル**
-- N ⊴ G finite, (|N|, |G:N|) = 1, IsSolvable N or IsSolvable (G/N) ⇒
-- any two complements of N are conjugate by an element of N.
#assert_only_allowed_axioms Subgroup.IsComplement'.exists_conj_of_coprime

-- Ch.3 (Split Extensions): Thm 3.14 Hall-C ⭐⭐⭐ **FT クリティカル**
-- G finite solvable, π set of primes, H K both π-Hall ⇒ ∃ g, H^g = K.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.hall_C

-- Ch.3 (Split Extensions): Thm 3.36 cyclic extension existence (Phase 4 完成)
-- N, m > 0, a ∈ N, σ ∈ Aut(N) で σ a = a かつ σ^m = MulAut.conj a
--   ⇒ ∃ G ⊇ N (N ⊴ G), G/N cyclic of order m, generator g, g^m = a, x^g = σ x.
#assert_only_allowed_axioms OddOrder.Isaacs.Ch03.cyclic_extension_exists

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
-- on `|G|` + `solvable_of_ker_le_range`); the only remaining gap of `feitThompson` itself is
-- the upstream `sectionSixteenHypothesis_of_isMinimalSimpleOdd` (BG §7–16 + Peterfalvi §10–16).
#assert_only_allowed_axioms OddOrder.feitThompson_of_noMinimalSimpleOdd

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
