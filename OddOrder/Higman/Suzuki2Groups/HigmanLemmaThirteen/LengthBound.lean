/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.LengthFourContradiction
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.LengthFourProperDescent
import OddOrder.Mathlib.Subgroup

/-!
# Higman's Lemma 13: the Xi-length bound

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, pp. 92–93.

Higman's source-facing conclusion is that the Xi-length is at most three.
An action with Xi-length at least four either has exact length four, which
the exponent-two and exponent-four arguments rule out, or descends to a
strictly smaller noncommutative invariant subgroup with the same lower
bound.  Strong induction on the group order excludes the latter alternative.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP

/-- **Higman Lemma 13 (pp. 92–93).**

Under Higman's standing hypotheses, the Xi-length is at most three: there
is no chain of four strict inclusions among the normal actor-invariant
subgroups. -/
theorem higmanLemmaThirteen
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    ¬ HasXiLengthAtLeastFour Y.subtype := by
  let motive : Nat → Prop := fun n =>
    ∀ (P' : Type uP) [Group P'] [Finite P']
      (Y' : Subgroup (MulAut P')),
      IsPGroup 2 P' →
      (¬ IsMulCommutative P') →
      (∃ x y : P',
        x ∈ involutions P' ∧ y ∈ involutions P' ∧ x ≠ y) →
      IsXiActor Y' →
      (∀ p : Nat, p.Prime → p ∣ Nat.card Y' →
        p ∣ (involutions P').ncard) →
      Nat.card P' = n →
      ¬ HasXiLengthAtLeastFour Y'.subtype
  suffices hmain : motive (Nat.card P) by
    exact hmain P Y hP hncomm hmulti hxi hprime rfl
  refine Nat.strong_induction_on (Nat.card P) ?_
  intro n ih P' _ _ Y' hP' hncomm' hmulti' hxi' hprime' hcard hlen
  by_cases hexact : HasXiLengthFour Y'.subtype
  · exact false_of_hasXiLengthFour
      hP' hncomm' hmulti' hxi' hexact hprime'
  · obtain ⟨S, hSinv, _hSnormal, hSneTop, hncommS, hlenS⟩ :=
      exists_proper_noncommutative_xiLengthAtLeastFour_descent
        hP' hncomm' hmulti' hxi' hlen hexact hprime'
    have hScardP : Nat.card S < Nat.card P' :=
      Subgroup.card_lt_card_of_ne_top hSneTop
    have hScardN : Nat.card S < n :=
      hScardP.trans_eq hcard
    have hSneBot : S ≠ (⊥ : Subgroup P') := by
      intro hSbot
      apply hncommS
      rw [hSbot]
      infer_instance
    have hinvS : involutions P' ⊆ S :=
      involutions_subset_of_nontrivial_invariant
        hP' Y' hxi'.transitive hSinv hSneBot
    have hPS : IsPGroup 2 S :=
      hP'.to_subgroup S
    have hmultiS : ∃ x y : S,
        x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
      exists_distinct_involutions_subgroup_of_subset hinvS hmulti'
    have hxiS : IsXiActor hSinv.restrict.range :=
      restricted_range_isXiActor hxi' hSinv
    have hprimeS : ∀ p : Nat, p.Prime →
        p ∣ Nat.card hSinv.restrict.range →
          p ∣ (involutions S).ncard :=
      restricted_range_primeSupport hSinv hinvS hprime'
    exact
      (ih (Nat.card S) hScardN S hSinv.restrict.range
        hPS hncommS hmultiS hxiS hprimeS rfl) hlenS

end OddOrder.Higman.Suzuki2Groups
