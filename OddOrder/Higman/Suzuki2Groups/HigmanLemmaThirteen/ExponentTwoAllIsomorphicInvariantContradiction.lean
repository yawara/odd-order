/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoInvariantGraphContradiction
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoThreeTermGraphPreimage

/-!
# Higman's Lemma 13: the all-isomorphic invariant graph is impossible

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

The all-isomorphic branch produces a three-term graph in the ambient
Frattini quotient.  Its canonical preimage is an invariant type-A factor
with exact Frattini intersection with the target factor.  A primitive
eigenvalue propagates the seed bracket cancellation across the whole graph
and target families.  The two actual factors consequently commute
elementwise, contradicting the type-A factor geometry.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance allIsomorphicInvariantContradictionLayerIsMulCommutative
    (H : Type uP) [Group H] (i : Nat) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

local instance allIsomorphicInvariantContradictionLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance
    allIsomorphicInvariantContradictionLayerZModTwoModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 13 (p. 93), three-term invariant-graph contradiction.**

This is the group-theoretic endpoint consumed after constructing the
canonical preimage `U` of the all-isomorphic three-term graph.  The
normality, proper-join, and restricted-length facts are retained in the
interface so the complete canonical-preimage witness can be passed without
discarding provenance.  The contradiction itself uses its exact Frattini
intersection and type-A model, together with the quotient ranges and the
primitive-eigenvalue seed cancellation. -/
theorem false_of_threeTermGraph_canonicalPreimage_primitive_eigen_seed
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {U T : Subgroup P}
    (hUinv : IsAInvariant Y.subtype U)
    (hTinv : IsAInvariant Y.subtype T)
    (_hUnormal : U.Normal)
    (_hPhiU : frattini P < U)
    (_hPhiT : frattini P < T)
    (hUT : U ⊓ T = frattini P)
    (_hUTtop : U ⊔ T < (⊤ : Subgroup P))
    (_hlenU : HasXiLengthTwo hUinv.restrict.range.subtype)
    (hmodelU : IsXiLengthTwoTypeA.{uP, 0} U)
    (hmodelT : IsXiLengthTwoTypeA.{uP, 0} T)
    (hinvPhi : involutions P ⊆ frattini P)
    {n : Nat}
    (hn : n ≠ 0)
    (c : Y)
    (iU iT : GaloisField 2 n →ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0))
    (lambda mu : GaloisField 2 n)
    (hlambda : IsPrimitiveRoot lambda (2 ^ n - 1))
    (hmu : mu ≠ 0)
    (hUeigen : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 c (iU alpha) =
        iU (lambda * alpha))
    (hTeigen : ∀ beta,
      lowerCentralLayerRepresentation Y.subtype 0 c (iT beta) =
        iT (mu * beta))
    (hseed : ∀ beta,
      lowerCentralCommutatorBilinear P (iU 1) (iT beta) = 0) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    U.map (QuotientGroup.mk' (frattini P)) =
        elabSubmoduleSubgroupEquiv 2
          (LinearMap.range
            ((layerZeroToFrattiniQuotientLinear P hP).comp iU)) →
      LinearMap.range
          ((layerZeroToFrattiniQuotientLinear P hP).comp iT) =
        (elabSubmoduleSubgroupEquiv 2).symm
          (T.map (QuotientGroup.mk' (frattini P))) →
      False := by
  let : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  let : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  intro hUmap hTrange
  have hcomm : ∀ u ∈ U, ∀ t ∈ T, Commute u t :=
    invariantGraphPreimage_commutes_of_primitive_eigen_seed
      hP hncomm hxi htwo hn c iU iT lambda mu
      hlambda hmu hUeigen hTeigen hseed U T hUmap hTrange
  exact false_of_typeA_factors_inf_eq_frattini_pairwise_commute
    hxi hUinv hTinv hUT hmodelU hmodelT hinvPhi htwo
    (fun u t => hcomm u u.property t t.property)

end

end OddOrder.Higman.Suzuki2Groups
