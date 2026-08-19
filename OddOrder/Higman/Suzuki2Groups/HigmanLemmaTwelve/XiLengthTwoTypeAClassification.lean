/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.LengthTwoModels

/-!
# Higman's Lemma 12: inclusive classification of xi-length-two groups

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
pp. 88--89.

Immediately before Lemma 12, Higman uses `A(n, phi)` inclusively: the case
`phi = 1` is the homocyclic abelian group `C₄ⁿ`, while `phi ≠ 1` is the
noncommutative group classified in Lemma 11. This leaf combines those two
honest branches into a classification theorem which does not depend on a
larger ambient xi-length-three group.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 12 (pp. 91–92) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

/-- **Higman Lemma 11 and the abelian case preceding Lemma 12
(pp. 88--89).**

A finite 2-group of exact xi-length two, with more than one involution and
Higman's prime-support hypothesis, has an inclusive `A(n, phi)` model. -/
theorem isXiLengthTwoTypeA_of_xiLengthTwo
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    IsXiLengthTwoTypeA.{uP, 0} P := by
  by_cases hcomm : IsMulCommutative P
  · let : CommGroup P :=
      { (inferInstance : Group P) with mul_comm := hcomm.is_comm.comm }
    let : Nontrivial P := by
      obtain ⟨x, y, _, _, hxy⟩ := hmulti
      exact ⟨⟨x, y, hxy⟩⟩
    obtain ⟨ι, _, ⟨ε⟩⟩ :=
      exists_homocyclic_four_of_commutative_xiLengthTwo
        hP hxi hlen hmulti
    have hFrattiniNeTop : frattini P ≠ (⊤ : Subgroup P) := by
      obtain ⟨M, hM, _⟩ :=
        (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup P)).resolve_left
          bot_lt_top.ne
      exact fun htop => hM.1
        (le_antisymm le_top (htop ▸ frattini_le_coatom hM))
    have hAgemoNeTop : Agemo P 2 1 ≠ (⊤ : Subgroup P) := by
      rw [← NormalInvariantCover.frattini_eq_agemo_one hP]
      exact hFrattiniNeTop
    have ε' : P ≃* (ι → Multiplicative (ZMod (2 ^ 2))) := by
      simpa using ε
    exact ⟨xiLengthTwoTypeAData_of_homocyclic_four ε' hAgemoNeTop⟩
  · exact
      isXiLengthTwoTypeA_of_isTypeA
        (higmanLemmaEleven hP hcomm hmulti hxi hlen hprime)

end

end OddOrder.Higman.Suzuki2Groups
