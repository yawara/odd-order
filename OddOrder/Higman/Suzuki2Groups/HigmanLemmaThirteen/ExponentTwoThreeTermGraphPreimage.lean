/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCanonicalInvariantPreimage
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoGraphOverTargetAxisGeometry

/-!
# Higman's Lemma 13: canonical preimage of a three-term graph

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

A nontrivial graph across two quotient-factor axes may be sheared by an
arbitrary multiple of a third, target-factor axis.  A common nonzero actor
eigenvalue makes the resulting three-term graph invariant.  Its direct
geometry against the target axis then supplies the canonical Frattini
preimage, including the normality, length-two, and type-A conclusions.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

noncomputable section

universe uP

/-- **Higman Lemma 13 (p. 93), three-term graph-preimage assembly.**

Let `gXZ(α) = iXq(aα) + iZq(bα)` and
`d(α) = gXZ(α) + iTq(cα)`.  Directness of the three quotient axes makes
`d` nonzero and disjoint from the actual target-factor image.  A common
nonzero eigenvalue under a cyclic actor makes its range invariant, so its
literal quotient pullback is a normal type-A factor of restricted
`ξ`-length two. -/
theorem
    exists_canonical_typeA_preimage_of_threeTermGraph_exponent_two
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthFour Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {T : Subgroup P}
    (hTinv : IsAInvariant Y.subtype T)
    (hPhiT : frattini P < T) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    ∀ (n : ℕ)
      (iXq iZq iTq :
        GaloisField 2 n →ₗ[ZMod 2] Additive (P ⧸ frattini P))
      (_hiXq : Function.Injective iXq)
      (_hiZq : Function.Injective iZq)
      (_hiTq : Function.Injective iTq)
      (_hXZ :
        LinearMap.range iXq ⊓ LinearMap.range iZq = ⊥)
      (_hXZ_T :
        (LinearMap.range iXq ⊔ LinearMap.range iZq) ⊓
            LinearMap.range iTq =
          ⊥)
      (_hRangeT :
        LinearMap.range iTq =
          (elabSubmoduleSubgroupEquiv
            (K := P ⧸ frattini P) 2).symm
              (T.map (QuotientGroup.mk' (frattini P))))
      (a b c : GaloisField 2 n)
      (_hab : a ≠ 0 ∨ b ≠ 0)
      (g : Y)
      (_hggen : ∀ y : Y, y ∈ Subgroup.zpowers g)
      (lambda : GaloisField 2 n)
      (_hlambda : lambda ≠ 0)
      (_hX : ∀ alpha,
        elabRepresentation 2
            (IsAInvariant.quotientMulAutHom
              (IsAInvariant.of_characteristic Y.subtype :
                IsAInvariant Y.subtype (frattini P)))
            g (iXq alpha) =
          iXq (lambda * alpha))
      (_hZ : ∀ alpha,
        elabRepresentation 2
            (IsAInvariant.quotientMulAutHom
              (IsAInvariant.of_characteristic Y.subtype :
                IsAInvariant Y.subtype (frattini P)))
            g (iZq alpha) =
          iZq (lambda * alpha))
      (_hT : ∀ alpha,
        elabRepresentation 2
            (IsAInvariant.quotientMulAutHom
              (IsAInvariant.of_characteristic Y.subtype :
                IsAInvariant Y.subtype (frattini P)))
            g (iTq alpha) =
          iTq (lambda * alpha)),
      let gXZ := commonEigenvalueGraphMap iXq iZq a b
      let d := commonEigenvalueGraphMap gXZ iTq 1 c
      let D :=
        elabSubmoduleSubgroupEquiv 2 (LinearMap.range d)
      ∃ (U : Subgroup P) (hUinv : IsAInvariant Y.subtype U),
        U.Normal ∧
          frattini P < U ∧
          U ⊓ T = frattini P ∧
          U ⊔ T < ⊤ ∧
          HasXiLengthTwo hUinv.restrict.range.subtype ∧
          IsXiLengthTwoTypeA.{uP, 0} U ∧
          U = D.comap (QuotientGroup.mk' (frattini P)) ∧
          U.map (QuotientGroup.mk' (frattini P)) = D := by
  classical
  dsimp only
  letI : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  intro n iXq iZq iTq hiXq hiZq hiTq hXZ hXZ_T hRangeT
    a b c hab g hggen lambda hlambda hX hZ hT
  let q := QuotientGroup.mk' (frattini P)
  let gXZ := commonEigenvalueGraphMap iXq iZq a b
  let d := commonEigenvalueGraphMap gXZ iTq 1 c
  let e :
      Submodule (ZMod 2) (Additive (P ⧸ frattini P)) ≃o
        Subgroup (P ⧸ frattini P) :=
    elabSubmoduleSubgroupEquiv 2
  let Tbar : Submodule (ZMod 2) (Additive (P ⧸ frattini P)) :=
    e.symm (T.map q)
  let D : Subgroup (P ⧸ frattini P) :=
    e (LinearMap.range d)
  have hRangeT' : LinearMap.range iTq = Tbar := by
    simpa [Tbar, e, q] using hRangeT
  obtain ⟨_, _, _, _, hDneBotSub, _, hDTinfRange, _,
      hDTtopRange⟩ :=
    threeTermGraphOverTargetAxis_geometry
      iXq iZq iTq hiXq hiZq hiTq hXZ hXZ_T a b c hab
  have hDTinfSub :
      LinearMap.range d ⊓ Tbar =
        (⊥ : Submodule (ZMod 2) (Additive (P ⧸ frattini P))) := by
    rw [← hRangeT']
    exact hDTinfRange
  have hDTtopSub :
      LinearMap.range d ⊔ Tbar ≠
        (⊤ : Submodule (ZMod 2) (Additive (P ⧸ frattini P))) := by
    rw [← hRangeT']
    exact hDTtopRange
  have hDbot : D ≠ ⊥ := by
    intro hD
    apply hDneBotSub
    have h := congrArg e.symm hD
    simpa [D, e] using h
  have hDTinf : D ⊓ T.map q = ⊥ := by
    have h := congrArg e hDTinfSub
    simpa [D, Tbar, e] using h
  have hDTtop : D ⊔ T.map q ≠ ⊤ := by
    intro htop
    apply hDTtopSub
    have h := congrArg e.symm htop
    simpa [D, Tbar, e] using h
  have hgXZeigen : ∀ alpha,
      elabRepresentation 2
          (IsAInvariant.quotientMulAutHom
            (IsAInvariant.of_characteristic Y.subtype :
              IsAInvariant Y.subtype (frattini P)))
          g (gXZ alpha) =
        gXZ (lambda * alpha) := by
    intro alpha
    exact commonEigenvalueGraphMap_eigen
      (elabRepresentation 2
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P))) g)
      iXq iZq a b lambda hX hZ alpha
  have hDinv :
      IsAInvariant
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P))) D := by
    simpa [D, d, e] using
      commonEigenvalueGraphMap_range_isAInvariant
        (IsAInvariant.quotientMulAutHom
          (IsAInvariant.of_characteristic Y.subtype :
            IsAInvariant Y.subtype (frattini P)))
        g hggen gXZ iTq 1 c lambda hlambda hgXZeigen hT
  simpa [D, d, gXZ, e, q] using
    exists_canonical_typeA_frattini_preimage_of_invariant_quotient_pair_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hTinv hPhiT hDinv hDbot hDTinf hDTtop

end

end OddOrder.Higman.Suzuki2Groups
