/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoFactorCopyTransport
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.NormalizedFactorCoordinateCoherence

/-!
# Higman Lemma 13: coherence of one factor across pairwise joins

G. Higman, *Suzuki 2-groups*, pp. 90--94.  In the exponent-two branch of
Lemma 13, one actual ambient factor occurs in two different pairwise joins.
The canonical equivalence between its two `subgroupOf` copies intertwines the
restricted ambient actor.  Consequently, normalized factor coordinates in
the two joins have the same square-law automorphism.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance pairwiseThetaLayerCommGroup
    (H : Type uP) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance pairwiseThetaLayerModule
    (H : Type uP) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13, exponent-two cross-join coherence.**  Two normalized
coordinate systems on copies of the same actual factor in different pairwise
joins have equal square-law automorphisms. -/
theorem FactorCoordinateData.theta_eq_of_pairwiseFactorCopies
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)} {R J K : Subgroup P}
    (hJinv : IsAInvariant Y.subtype J)
    (hKinv : IsAInvariant Y.subtype K)
    (hRJ : R ≤ J) (hRK : R ≤ K)
    (hRinvJ : IsAInvariant hJinv.restrict.range.subtype
      (R.subgroupOf J))
    (hRinvK : IsAInvariant hKinv.restrict.range.subtype
      (R.subgroupOf K))
    [IsMulCommutative (frattini J)]
    [Module (ZMod 2) (Additive (frattini J))]
    [IsMulCommutative (frattini K)]
    [Module (ZMod 2) (Additive (frattini K))]
    {hPhiRJ : frattini J ≤ R.subgroupOf J}
    {hPhiRK : frattini K ≤ R.subgroupOf K}
    (c : Y) {n : ℕ}
    {ePhiJ : Additive (frattini J) ≃ₗ[ZMod 2] GaloisField 2 n}
    {ePhiK : Additive (frattini K) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (dataJ : FactorCoordinateData hRinvJ hPhiRJ
      (hJinv.restrict.rangeRestrict c) ePhiJ nu)
    (dataK : FactorCoordinateData hRinvK hPhiRK
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
  exact dataJ.theta_eq_of_normalized_equivariant dataK hn
    hnormJ hnormK hnuPrimitive
    (pairwiseFactorCopyMulEquiv hRJ hRK)
    (lowerCentralLayerLinearEquiv
      (pairwiseFactorCopyMulEquiv hRJ hRK) 0)
    (lowerCentralLayerLinearEquiv_pairwiseFactorCopy_equivariant
      hJinv hKinv hRJ hRK hRinvJ hRinvK c 0)

end

end OddOrder.Higman.Suzuki2Groups
