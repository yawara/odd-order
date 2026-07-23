/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCanonicalInvariantPreimage
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoGraphSubspaceGeometry
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoGraphSubspaceInvariant

/-!
# Higman's Lemma 13: invariant graph preimages

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Two disjoint quotient-factor axes with one common nonzero actor eigenvalue
produce an invariant graph subspace.  If their sum is disjoint from an
existing factor image, the graph is nonzero, meets that image trivially, and
does not complement it.  Its canonical Frattini preimage is therefore an
actual normal invariant type-A factor of restricted `ξ`-length two.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

noncomputable section

universe uP

/-- **Higman Lemma 13 (p. 93), invariant graph-preimage assembly.**

A nontrivial graph across two disjoint quotient-factor axes is pulled back
to the same canonical subgroup classified by the length-four chain.  The
conclusion retains its quotient image, so later commutator arguments can
work with the original graph coordinates. -/
theorem
    exists_canonical_typeA_preimage_of_commonEigenvalueGraph_exponent_two
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
    {W : Subgroup P}
    (hWinv : IsAInvariant Y.subtype W)
    (hPhiW : frattini P < W) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    ∀ (n : ℕ)
      (iX iY :
        GaloisField 2 n →ₗ[ZMod 2] Additive (P ⧸ frattini P))
      (_hiX : Function.Injective iX)
      (_hiY : Function.Injective iY)
      (_hXY : LinearMap.range iX ⊓ LinearMap.range iY = ⊥)
      (a b : GaloisField 2 n)
      (_hab : a ≠ 0 ∨ b ≠ 0)
      (_hXYW :
        (LinearMap.range iX ⊔ LinearMap.range iY) ⊓
            (elabSubmoduleSubgroupEquiv 2).symm
              (W.map (QuotientGroup.mk' (frattini P))) =
          ⊥)
      (c : Y)
      (_hcgen : ∀ g : Y, g ∈ Subgroup.zpowers c)
      (lambda : GaloisField 2 n)
      (_hlambda : lambda ≠ 0)
      (_hX : ∀ alpha,
        elabRepresentation 2
            (IsAInvariant.quotientMulAutHom
              (IsAInvariant.of_characteristic Y.subtype :
                IsAInvariant Y.subtype (frattini P)))
            c (iX alpha) =
          iX (lambda * alpha))
      (_hY : ∀ alpha,
        elabRepresentation 2
            (IsAInvariant.quotientMulAutHom
              (IsAInvariant.of_characteristic Y.subtype :
                IsAInvariant Y.subtype (frattini P)))
            c (iY alpha) =
          iY (lambda * alpha)),
      let d := commonEigenvalueGraphMap iX iY a b
      let D :=
        elabSubmoduleSubgroupEquiv 2 (LinearMap.range d)
      ∃ (U : Subgroup P) (hUinv : IsAInvariant Y.subtype U),
        U.Normal ∧
          frattini P < U ∧
          U ⊓ W = frattini P ∧
          U ⊔ W < ⊤ ∧
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
  intro n iX iY hiX hiY hXY a b hab hXYW
    c hcgen lambda hlambda hX hY
  let q := QuotientGroup.mk' (frattini P)
  let d := commonEigenvalueGraphMap iX iY a b
  let Wbar :=
    (elabSubmoduleSubgroupEquiv 2).symm (W.map q)
  obtain ⟨_hdinj, hDneBot, _hDlt, hDWinfSub, hDWtopSub⟩ :=
    graphSubspace_geometry
      iX iY hiX hiY hXY a b hab d (fun _ => rfl)
        Wbar (by simpa [Wbar, q] using hXYW)
  let e :
      Submodule (ZMod 2) (Additive (P ⧸ frattini P)) ≃o
        Subgroup (P ⧸ frattini P) :=
    elabSubmoduleSubgroupEquiv 2
  let D : Subgroup (P ⧸ frattini P) :=
    e (LinearMap.range d)
  have hDbot : D ≠ ⊥ := by
    intro hD
    apply hDneBot
    have h := congrArg e.symm hD
    simpa [D, e] using h
  have hDWinf : D ⊓ W.map q = ⊥ := by
    have h := congrArg e hDWinfSub
    simpa [D, Wbar, e] using h
  have hDWtop : D ⊔ W.map q ≠ ⊤ := by
    intro htop
    apply hDWtopSub
    have h := congrArg e.symm htop
    simpa [D, Wbar, e] using h
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
        c hcgen iX iY a b lambda hlambda hX hY
  simpa [D, d, e, q] using
    exists_canonical_typeA_frattini_preimage_of_invariant_quotient_pair_exponent_two
      hP hncomm hmulti hxi hlen hprime htwo
      hWinv hPhiW hDinv hDbot hDWinf hDWtop

end

end OddOrder.Higman.Suzuki2Groups
