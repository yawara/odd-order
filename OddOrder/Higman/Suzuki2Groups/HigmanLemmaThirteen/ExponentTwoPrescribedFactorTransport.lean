/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoFactorCopyTransport
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.NormalizedFactorCoordinateCoherence

/-!
# Higman Lemma 13: transport between prescribed pairwise factors

G. Higman, *Suzuki 2-groups*, p. 93.  The fixed-coordinate pair theorem
returns a prescribed factor together with an equality identifying it with
the actual `subgroupOf` copy.  Two such prescribed factors in different
pairwise joins are canonically equivalent: use each equality to reach the
actual copy, transport the ambient factor between joins, and return through
the second equality.

This construction preserves the restricted ambient actor.  Consequently it
also transports zeroth lower-central layers and identifies normalized
square-law parameters without eliminating dependent factor records.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance prescribedCopyTransportLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance prescribedCopyTransportLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- The canonical equivalence between prescribed factors identified with
two `subgroupOf` copies of one ambient factor. -/
def prescribedPairwiseFactorMulEquiv
    {P : Type uP} [Group P] {R J K : Subgroup P}
    (FJ : Subgroup J) (FK : Subgroup K)
    (hFJ : FJ = R.subgroupOf J)
    (hFK : FK = R.subgroupOf K)
    (hRJ : R ≤ J) (hRK : R ≤ K) :
    FJ ≃* FK :=
  (MulEquiv.subgroupCongr hFJ).trans
    ((pairwiseFactorCopyMulEquiv hRJ hRK).trans
      (MulEquiv.subgroupCongr hFK).symm)

@[simp]
theorem prescribedPairwiseFactorMulEquiv_apply_val
    {P : Type uP} [Group P] {R J K : Subgroup P}
    (FJ : Subgroup J) (FK : Subgroup K)
    (hFJ : FJ = R.subgroupOf J)
    (hFK : FK = R.subgroupOf K)
    (hRJ : R ≤ J) (hRK : R ≤ K) (x : FJ) :
    (((prescribedPairwiseFactorMulEquiv
      FJ FK hFJ hFK hRJ hRK x : FK) : K) : P) =
      ((x : J) : P) := by
  rfl

/-- The prescribed-factor equivalence intertwines the restrictions of one
ambient actor element to both pairwise joins. -/
theorem prescribedPairwiseFactorMulEquiv_equivariant
    {P : Type uP} [Group P] {Y : Subgroup (MulAut P)}
    {R J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hRJ : R ≤ J) (hRK : R ≤ K)
    (FJ : Subgroup J) (FK : Subgroup K)
    (hFJ : FJ = R.subgroupOf J)
    (hFK : FK = R.subgroupOf K)
    (hFJinv : IsAInvariant hJinv.restrict.range.subtype FJ)
    (hFKinv : IsAInvariant hKinv.restrict.range.subtype FK)
    (c : Y) (x : FJ) :
    prescribedPairwiseFactorMulEquiv FJ FK hFJ hFK hRJ hRK
        (hFJinv.restrict (hJinv.restrict.rangeRestrict c) x) =
      hFKinv.restrict (hKinv.restrict.rangeRestrict c)
        (prescribedPairwiseFactorMulEquiv
          FJ FK hFJ hFK hRJ hRK x) := by
  apply Subtype.ext
  apply Subtype.ext
  change (c : MulAut P) ((x : J) : P) =
    (c : MulAut P) ((x : J) : P)
  rfl

/-- **Higman Lemma 13, cross-join coherence for prescribed factors.**
Normalized coordinate data on prescribed copies of one actual ambient
factor have equal square-law automorphisms. -/
theorem FactorCoordinateData.theta_eq_of_prescribedPairwiseFactorCopies
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)} {R J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hRJ : R ≤ J) (hRK : R ≤ K)
    {FJ : Subgroup J} {FK : Subgroup K}
    (hFJ : FJ = R.subgroupOf J)
    (hFK : FK = R.subgroupOf K)
    (hFJinv : IsAInvariant hJinv.restrict.range.subtype FJ)
    (hFKinv : IsAInvariant hKinv.restrict.range.subtype FK)
    [IsMulCommutative (frattini J)]
    [Module (ZMod 2) (Additive (frattini J))]
    [IsMulCommutative (frattini K)]
    [Module (ZMod 2) (Additive (frattini K))]
    {hPhiFJ : frattini J ≤ FJ}
    {hPhiFK : frattini K ≤ FK}
    (c : Y) {n : ℕ}
    {ePhiJ : Additive (frattini J) ≃ₗ[ZMod 2] GaloisField 2 n}
    {ePhiK : Additive (frattini K) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (dataJ : FactorCoordinateData hFJinv hPhiFJ
      (hJinv.restrict.rangeRestrict c) ePhiJ nu)
    (dataK : FactorCoordinateData hFKinv hPhiFK
      (hKinv.restrict.rangeRestrict c) ePhiK nu)
    (hn : n ≠ 0)
    (hnormJ : dataJ.theta = 1 ∨
      ∃ r : ℕ, 0 < r ∧ 2 * r ≤ n ∧
        dataJ.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ r ∧
        Odd (orderOf dataJ.theta))
    (hnormK : dataK.theta = 1 ∨
      ∃ s : ℕ, 0 < s ∧ 2 * s ≤ n ∧
        dataK.theta = frobeniusEquiv (GaloisField 2 n) 2 ^ s ∧
        Odd (orderOf dataK.theta))
    (hnuPrimitive : IsPrimitiveRoot nu (2 ^ n - 1)) :
    dataJ.theta = dataK.theta := by
  let e :=
    prescribedPairwiseFactorMulEquiv
      FJ FK hFJ hFK hRJ hRK
  exact dataJ.theta_eq_of_normalized_equivariant dataK hn
    hnormJ hnormK hnuPrimitive e
    (lowerCentralLayerLinearEquiv e 0)
    (lowerCentralLayerLinearEquiv_equivariant
      e hFJinv.restrict hFKinv.restrict
      (hJinv.restrict.rangeRestrict c)
      (hKinv.restrict.rangeRestrict c)
      (prescribedPairwiseFactorMulEquiv_equivariant
        hJinv hKinv hRJ hRK FJ FK hFJ hFK
        hFJinv hFKinv c)
      0)

end

end OddOrder.Higman.Suzuki2Groups
