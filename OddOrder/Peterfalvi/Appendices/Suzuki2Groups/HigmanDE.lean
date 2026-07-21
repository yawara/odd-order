/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ElementaryAbelian
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups

/-!
# Peterfalvi Appendix III: Higman's two-summand conclusions

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Higman theorem (d)--(e), p. 141.

This file records the concrete payload of the two-summand part of Higman's
theorem.  If `Z` is an invariant normal subgroup of `P`, clause (d) says that
`P / Z` is the direct sum of two invariant elementary-abelian subgroups, each
of cardinality `|Z|`.  Clause (e) says existentially that type B is equivalent
to the existence of such a split whose two restricted `K`-actions are
isomorphic; it does not assert that an arbitrary split supplied by (d) has
isomorphic summands.

The inverse images of the two summands in `P` are constructed below.  Their
`K`-invariance is derived from quotient equivariance, and their cardinality is
`|Z| ^ 2` by the cardinality formula for the preimage of a subgroup under a
surjective homomorphism.  Thus these conclusions are not separately posited
fields.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

universe uK uP uX uY uZ

/-- An isomorphism between groups equipped with `K`-actions which commutes
with those actions. -/
structure KEquivariantMulEquiv
    {K : Type uK} {X : Type uX} {Y : Type uY}
    [Group K] [Group X] [Group Y]
    (rhoX : K →* MulAut X) (rhoY : K →* MulAut Y) where
  toMulEquiv : X ≃* Y
  equivariant : ∀ k x, toMulEquiv (rhoX k x) = rhoY k (toMulEquiv x)

namespace KEquivariantMulEquiv

variable {K : Type uK} {X : Type uX} {Y : Type uY} {Z : Type uZ}
  [Group K] [Group X] [Group Y] [Group Z]
  {rhoX : K →* MulAut X} {rhoY : K →* MulAut Y} {rhoZ : K →* MulAut Z}

/-- The inverse of a `K`-equivariant isomorphism is `K`-equivariant. -/
def symm (e : KEquivariantMulEquiv rhoX rhoY) : KEquivariantMulEquiv rhoY rhoX where
  toMulEquiv := e.toMulEquiv.symm
  equivariant k y := by
    apply e.toMulEquiv.injective
    rw [MulEquiv.apply_symm_apply, e.equivariant, MulEquiv.apply_symm_apply]

/-- The composite of two `K`-equivariant isomorphisms is `K`-equivariant. -/
def trans (e : KEquivariantMulEquiv rhoX rhoY) (f : KEquivariantMulEquiv rhoY rhoZ) :
    KEquivariantMulEquiv rhoX rhoZ where
  toMulEquiv := e.toMulEquiv.trans f.toMulEquiv
  equivariant k x := by
    simp only [MulEquiv.trans_apply, e.equivariant, f.equivariant]

end KEquivariantMulEquiv

/-- **Peterfalvi Appendix III, Higman theorem (d).**  The genuine
two-summand payload in the case `|P| = |Z| ^ 3`.

The two summands live in the actual quotient `P / Z`, are invariant under the
induced `K`-action, have cardinality `|Z|`, and are complementary. -/
structure OrderQModuleSplit
    {K : Type uK} {P : Type uP} [Group K] [Group P]
    (act : K →* MulAut P) (Z : Subgroup P) [Z.Normal]
    (hZinv : IsAInvariant act Z) where
  quotientEA : OddOrder.GroupTheory.IsElementaryAbelian 2 (P ⧸ Z)
  left : Subgroup (P ⧸ Z)
  right : Subgroup (P ⧸ Z)
  leftInvariant : IsAInvariant (quotientMulAutHom hZinv) left
  rightInvariant : IsAInvariant (quotientMulAutHom hZinv) right
  leftCard : Nat.card ↥left = Nat.card ↥Z
  rightCard : Nat.card ↥right = Nat.card ↥Z
  complementary : IsCompl left right

/-- **Peterfalvi Appendix III, Higman theorem (e), module-isomorphism
payload.**  A split of the form supplied by (d), together with an actual
equivariant isomorphism between its restricted `K`-actions.

This packages the existential split occurring in (e); it does not claim that
every `OrderQModuleSplit` has isomorphic summands. -/
structure IsomorphicOrderQModuleSplit
    {K : Type uK} {P : Type uP} [Group K] [Group P]
    (act : K →* MulAut P) (Z : Subgroup P) [Z.Normal]
    (hZinv : IsAInvariant act Z) where
  split : OrderQModuleSplit act Z hZinv
  summandEquiv : KEquivariantMulEquiv
    split.leftInvariant.restrict split.rightInvariant.restrict

namespace OrderQModuleSplit

variable {K : Type uK} {P : Type uP} [Group K] [Group P]
  {act : K →* MulAut P} {Z : Subgroup P} [Z.Normal]
  {hZinv : IsAInvariant act Z}

/-- The inverse image in `P` of the left summand of `P / Z`. -/
def leftPreimage (split : OrderQModuleSplit act Z hZinv) : Subgroup P :=
  split.left.comap (QuotientGroup.mk' Z)

/-- The inverse image in `P` of the right summand of `P / Z`. -/
def rightPreimage (split : OrderQModuleSplit act Z hZinv) : Subgroup P :=
  split.right.comap (QuotientGroup.mk' Z)

/-- The inverse image of the left summand is invariant under the original
`K`-action on `P`. -/
theorem leftPreimage_invariant (split : OrderQModuleSplit act Z hZinv) :
    IsAInvariant act split.leftPreimage :=
  hZinv.comap_quotient split.leftInvariant

/-- The inverse image of the right summand is invariant under the original
`K`-action on `P`. -/
theorem rightPreimage_invariant (split : OrderQModuleSplit act Z hZinv) :
    IsAInvariant act split.rightPreimage :=
  hZinv.comap_quotient split.rightInvariant

/-- The inverse image of the left order-`|Z|` summand has cardinality
`|Z| ^ 2`. -/
theorem card_leftPreimage [Finite P]
    (split : OrderQModuleSplit act Z hZinv) :
    Nat.card ↥split.leftPreimage = Nat.card ↥Z ^ 2 := by
  calc
    Nat.card ↥split.leftPreimage =
        Nat.card ↥split.left * Nat.card (QuotientGroup.mk' Z).ker :=
      Subgroup.card_comap_eq_card_mul_card_ker
        (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) split.left
    _ = Nat.card ↥Z * Nat.card ↥Z := by
      rw [split.leftCard, QuotientGroup.ker_mk']
    _ = Nat.card ↥Z ^ 2 := by rw [pow_two]

/-- The inverse image of the right order-`|Z|` summand has cardinality
`|Z| ^ 2`. -/
theorem card_rightPreimage [Finite P]
    (split : OrderQModuleSplit act Z hZinv) :
    Nat.card ↥split.rightPreimage = Nat.card ↥Z ^ 2 := by
  calc
    Nat.card ↥split.rightPreimage =
        Nat.card ↥split.right * Nat.card (QuotientGroup.mk' Z).ker :=
      Subgroup.card_comap_eq_card_mul_card_ker
        (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) split.right
    _ = Nat.card ↥Z * Nat.card ↥Z := by
      rw [split.rightCard, QuotientGroup.ker_mk']
    _ = Nat.card ↥Z ^ 2 := by rw [pow_two]

end OrderQModuleSplit

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
