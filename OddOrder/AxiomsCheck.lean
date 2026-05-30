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
import OddOrder.GroupTheory.RepresentationTheory.ColumnOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.BrauerPermutationUnconditional
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
import OddOrder.GroupTheory.RepresentationTheory.RealClassTISubset
import OddOrder.GroupTheory.RepresentationTheory.Clifford
import OddOrder.Isaacs.Ch02_Subnormality.Main
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch05_Transfer.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main
import OddOrder.BG.AppA_PStability
import OddOrder.BG.AppB_Puig
import OddOrder.BG.AppB_PuigB3B4
import OddOrder.BG.AppB_Thm62
import OddOrder.Peterfalvi.S03_PreliminaryCharacter
import OddOrder.Peterfalvi.S04_DadeIsometry
import OddOrder.Peterfalvi.S07_Coherence

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
| Ch.2 (Subnormality) | `OddOrder.Isaacs.Ch02.baerSuzuki_pCore` | Thm 2.12 系 (lean-eval Baer-Suzuki) |
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
-- RepresentationTheory (Peterfalvi §3, [Is] Thm 2.18/6.10): second (column) orthogonality is
-- unconditional — the `CharacterTableIndexing` and weighted-row-orthogonality inputs of the
-- matrix proof core are discharged for any `[Finite G]` (issue 0027 closed unconditionally).
#assert_only_allowed_axioms OddOrder.RepresentationTheory.column_orthogonality_diagonal
#assert_only_allowed_axioms OddOrder.RepresentationTheory.column_orthogonality_conjugate
#assert_only_allowed_axioms OddOrder.RepresentationTheory.column_orthogonality_not_conjugate
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
-- RepresentationTheory (Peterfalvi (2.10.3) transversal value): the induction sum at `g`
-- collapses to a sum over only those `x` with `x⁻¹ g x ∈ H` (off-support terms vanish via
-- `induceTerm_of_not_mem`), in unscaled (`induceSum`) and normalized (`induce`) form.
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induceSum_apply_eq_sum_filter
#assert_only_allowed_axioms OddOrder.RepresentationTheory.ClassFunction.induce_apply_eq_sum_filter
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
-- Corollary (Isaacs Cor. 3.12): the degree of an irreducible representation of a finite p-group is
-- a power of p.  Immediate from `finrank_dvd_card` (`dim V ∣ |G| = p^n`) and `Nat.dvd_prime_pow`.
#assert_only_allowed_axioms
  OddOrder.RepresentationTheory.exists_finrank_eq_prime_pow_of_isPGroup

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
