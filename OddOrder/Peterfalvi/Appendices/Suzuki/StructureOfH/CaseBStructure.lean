/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.OrderFivePairing
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ModelCenters

/-!
# Case (b) of Peterfalvi Part II, Ch. III §1, in its own terms

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §2, p. 118:

> **Proposition.** If case (b) of the proposition of §1 holds, then
> `(SK) ∪ (SKtS)` is a subgroup of `G`.

Case (b) of the Proposition of §1 (`SecondCaseHypothesis.trichotomy`) says that
`S` is a Suzuki `2`-group of type A, that `st` has order `5` and that `W = 1`.
The Proposition of §2 was reduced in `OrderFivePairing.lean` to that plus the
standing structure of `S` — `Z(S) = Q₀`, `S/Q₀` elementary abelian, `K` free on
`S/Q₀` — and this file reads those three off the type-A model.

## Main results

* `Hypothesis.center_eq_Q0_subgroupOf_of_isTypeA` — `Z(S) = Q₀`.
* `Hypothesis.isElementaryAbelian_quotient_center_of_isTypeA` — `S/Z(S)` is
  elementary abelian.
* `Hypothesis.tConjMiddle_mem_K_of_isTypeA` — `h(x) ∈ K` for `x ∈ S#`, i.e.
  `t S t ⊆ S K t S`.
* `Hypothesis.typeASubgroup` — **the Proposition of §2**.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- **`Z(S) = Q₀` for a type-A `S`**: the center of a type-A Suzuki `2`-group
has exponent `2` (`TypeAData.sq_eq_one_of_mem_center`), and `Q₀` collects
exactly the elements of `Q` that square to `1`. -/
theorem center_eq_Q0_subgroupOf_of_isTypeA
    (hA : Suzuki2Groups.IsTypeA.{u, 0} ↥hyp.Q) :
    Subgroup.center ↥hyp.Q = hyp.Q0.subgroupOf hyp.Q :=
  hyp.center_Q_eq_Q0_subgroupOf_of_sq_eq_one fun _ hz =>
    hA.some.sq_eq_one_of_mem_center hz

/-- **`S/Z(S)` is elementary abelian for a type-A `S`.** -/
theorem isElementaryAbelian_quotient_center_of_isTypeA
    (hA : Suzuki2Groups.IsTypeA.{u, 0} ↥hyp.Q) :
    IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center ↥hyp.Q) :=
  hA.some.isElementaryAbelian_quotient_center

/-- **`h(x) ∈ K` for every `x ∈ S ∖ {1}`** (Peterfalvi Part II, Ch. III §2,
pp. 118-119), in the hypotheses of case (b) of §1.

This is the content of the Proposition: `t x t = g(x) h(x) t f(x)` with
`h(x) ∈ K` says `t S t ⊆ S K t S`. -/
theorem tConjMiddle_mem_K_of_isTypeA
    (hA : Suzuki2Groups.IsTypeA.{u, 0} ↥hyp.Q)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (h5 : orderOf (hyp.distinguishedInvolution * hyp.t) = 5)
    {x : G} (hx : x ∈ hyp.Q) (hx1 : x ≠ 1) : hyp.tConjMiddle x ∈ hyp.K :=
  hyp.tConjMiddle_mem_K_of_case_b (hyp.center_eq_Q0_subgroupOf_of_isTypeA hA)
    (hyp.isElementaryAbelian_quotient_center_of_isTypeA hA)
    (hyp.kfree_mod_Q0_of_center_eq (hyp.center_eq_Q0_subgroupOf_of_isTypeA hA))
    hQcard h5 hx hx1

/-- **The Proposition of Peterfalvi Part II, Ch. III §2** (pp. 118-119):

> If case (b) of the proposition of §1 holds, then `(SK) ∪ (SKtS)` is a subgroup
> of `G`.

Case (b) says that `S` is a Suzuki `2`-group of type A — hence of order `q²` —
and that `st` has order `5`. -/
def typeASubgroup
    (hA : Suzuki2Groups.IsTypeA.{u, 0} ↥hyp.Q)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (h5 : orderOf (hyp.distinguishedInvolution * hyp.t) = 5) : Subgroup G :=
  hyp.orderFiveSubgroup fun _ hx hx1 =>
    hyp.tConjMiddle_mem_K_of_isTypeA hA hQcard h5 hx hx1

@[simp] lemma coe_typeASubgroup
    (hA : Suzuki2Groups.IsTypeA.{u, 0} ↥hyp.Q)
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2)
    (h5 : orderOf (hyp.distinguishedInvolution * hyp.t) = 5) :
    ((hyp.typeASubgroup hA hQcard h5 : Subgroup G) : Set G)
      = hyp.orderFiveCarrier := rfl

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
