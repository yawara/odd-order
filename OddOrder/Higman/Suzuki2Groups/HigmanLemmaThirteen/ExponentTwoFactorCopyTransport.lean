/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralTransport

/-!
# Higman Lemma 13: transport between copies of one pairwise factor

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 13,
p. 93.

In the exponent-two branch, one ambient factor occurs in two different
pairwise joins.  Its two `subgroupOf` copies are canonically isomorphic:
forget the first join subtype and insert the same ambient element into the
second join.  Because both restricted actors come from the same ambient
actor element, this equivalence intertwines their actions.

Combining that observation with the functoriality of elementary
lower-central layers gives the equivariant linear equivalence consumed by
the cross-join Frobenius-parameter comparison.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uP

/-- The canonical equivalence between two `subgroupOf` copies of the same
ambient subgroup. -/
def pairwiseFactorCopyMulEquiv
    {P : Type uP} [Group P] {R J K : Subgroup P}
    (hRJ : R ≤ J) (hRK : R ≤ K) :
    R.subgroupOf J ≃* R.subgroupOf K :=
  (Subgroup.subgroupOfEquivOfLe hRJ).trans
    (Subgroup.subgroupOfEquivOfLe hRK).symm

@[simp]
theorem pairwiseFactorCopyMulEquiv_apply_val
    {P : Type uP} [Group P] {R J K : Subgroup P}
    (hRJ : R ≤ J) (hRK : R ≤ K) (x : R.subgroupOf J) :
    (((pairwiseFactorCopyMulEquiv hRJ hRK x :
      R.subgroupOf K) : K) : P) = ((x : J) : P) := by
  rfl

/-- The canonical equivalence of factor copies intertwines the restrictions
of one ambient actor element to both pairwise joins. -/
theorem pairwiseFactorCopyMulEquiv_equivariant
    {P : Type uP} [Group P] {Y : Subgroup (MulAut P)}
    {R J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hRJ : R ≤ J) (hRK : R ≤ K)
    (hRinvJ : IsAInvariant hJinv.restrict.range.subtype
      (R.subgroupOf J))
    (hRinvK : IsAInvariant hKinv.restrict.range.subtype
      (R.subgroupOf K))
    (c : Y) (x : R.subgroupOf J) :
    pairwiseFactorCopyMulEquiv hRJ hRK
        (hRinvJ.restrict (hJinv.restrict.rangeRestrict c) x) =
      hRinvK.restrict (hKinv.restrict.rangeRestrict c)
        (pairwiseFactorCopyMulEquiv hRJ hRK x) := by
  apply Subtype.ext
  apply Subtype.ext
  change (c : MulAut P) ((x : J) : P) =
    (c : MulAut P) ((x : J) : P)
  rfl

/-- The lower-central layer equivalence between two copies of the same
factor is equivariant for the common ambient actor element. -/
theorem lowerCentralLayerLinearEquiv_pairwiseFactorCopy_equivariant
    {P : Type uP} [Group P] {Y : Subgroup (MulAut P)}
    {R J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hRJ : R ≤ J) (hRK : R ≤ K)
    (hRinvJ : IsAInvariant hJinv.restrict.range.subtype
      (R.subgroupOf J))
    (hRinvK : IsAInvariant hKinv.restrict.range.subtype
      (R.subgroupOf K))
    (c : Y) (i : ℕ)
    (x : Additive (lowerCentralLayer (R.subgroupOf J) i)) :
    lowerCentralLayerLinearEquiv
        (pairwiseFactorCopyMulEquiv hRJ hRK) i
        (lowerCentralLayerRepresentation hRinvJ.restrict i
          (hJinv.restrict.rangeRestrict c) x) =
      lowerCentralLayerRepresentation hRinvK.restrict i
        (hKinv.restrict.rangeRestrict c)
        (lowerCentralLayerLinearEquiv
          (pairwiseFactorCopyMulEquiv hRJ hRK) i x) := by
  exact lowerCentralLayerLinearEquiv_equivariant
    (pairwiseFactorCopyMulEquiv hRJ hRK)
    hRinvJ.restrict hRinvK.restrict
    (hJinv.restrict.rangeRestrict c)
    (hKinv.restrict.rangeRestrict c)
    (pairwiseFactorCopyMulEquiv_equivariant
      hJinv hKinv hRJ hRK hRinvJ hRinvK c)
    i x

end OddOrder.Higman.Suzuki2Groups
