/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.PrescribedFactorCoordinates

/-!
# Higman's Lemma 13: factor isomorphism from a common square parameter

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Two actual factors measured in the same ambient Frattini coordinate have the
same underlying type-A group as soon as their square-law automorphisms agree.
In the commutative branch this is the prescribed-kernel construction of
`A(n, 1)`.  In the noncommutative branch the actual lower-central kernel and
quotient coordinates give a central extension with square map
`alpha ↦ alpha * theta alpha`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups
open scoped commutatorElement IsMulCommutative

universe uP

section /- Higman Lemma 13 (p. 93) -/

local instance factorIsomorphismLayerIsMulCommutative
    (S : Type uP) [Group S] (i : ℕ) :
    IsMulCommutative (lowerCentralLayer S i) :=
  lowerCentralLayerIsMulCommutative S i

local instance factorIsomorphismLayerCommGroup
    (S : Type uP) [Group S] (i : ℕ) :
    CommGroup (lowerCentralLayer S i) :=
  { (inferInstance : Group (lowerCentralLayer S i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian S i).comm }

noncomputable local instance factorIsomorphismLayerModule
    (S : Type uP) [Group S] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer S i)) :=
  lowerCentralLayerZmodModule S i

local instance factorIsomorphismLowerCentralTermOneNormal
    (S : Type uP) [Group S] :
    (lowerCentralTerm S 1).Normal := by
  dsimp [lowerCentralTerm]
  infer_instance

private theorem lowerCentralTerm_two_eq_bot_of_layerKernel_one_eq_bot
    {S : Type uP} [Group S]
    (hK1 : lowerCentralLayerKernel S 1 = ⊥) :
    lowerCentralTerm S 2 = ⊥ := by
  have hsub :
      (lowerCentralTerm S 2).subgroupOf (lowerCentralTerm S 1) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hK1]
    exact le_sup_right
  rw [← Subgroup.map_subgroupOf_eq_of_le (lowerCentralTerm_succ_le S 1),
    hsub, Subgroup.map_bot]

private theorem lowerCentralTerm_one_le_center_of_layerKernel_one_eq_bot
    {S : Type uP} [Group S]
    (hK1 : lowerCentralLayerKernel S 1 = ⊥) :
    lowerCentralTerm S 1 ≤ Subgroup.center S := by
  have hterm2 : lowerCentralTerm S 2 = ⊥ :=
    lowerCentralTerm_two_eq_bot_of_layerKernel_one_eq_bot hK1
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro x
  have hzx : ⁅(z : S), x⁆ ∈ lowerCentralTerm S 2 := by
    rw [lowerCentralTerm, show 2 = 1 + 1 by omega,
      Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator hz (Subgroup.mem_top x)
  have hcomm : Commute (z : S) x := by
    apply commutatorElement_eq_one_iff_commute.mp
    exact Subgroup.mem_bot.mp (hterm2 ▸ hzx)
  exact hcomm.symm.eq

private noncomputable def CommutativeFactorCoordinateData.toTypeAModelData
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative (frattini P)]
    [Module (ZMod 2) (Additive (frattini P))]
    {S : Subgroup P}
    {hSinv : IsAInvariant Y.subtype S}
    {hPhiS : frattini P ≤ S}
    {c : Y} {n : ℕ}
    {ePhi : Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : CommutativeFactorCoordinateData
      hSinv hPhiS c ePhi nu)
    (hn : 0 < n) :
    XiLengthTwoTypeAData.{uP, 0} S := by
  letI : CommGroup S :=
    { (inferInstance : Group S) with
      mul_comm := data.hcomm.is_comm.comm }
  letI := data.fintypeIndex
  letI : Nontrivial (S ⧸ Agemo S 2 1) :=
    data.eQuot.toEquiv.nontrivial
  have hNtop : Agemo S 2 1 ≠ ⊤ :=
    QuotientGroup.nontrivial_iff.mp inferInstance
  exact xiLengthTwoTypeAData_of_homocyclic_four_prescribedKernel
    data.equivPi hNtop n hn (GaloisField.card 2 n hn.ne') data.eKernel

private noncomputable def NoncommutativeFactorCoordinateData.toTypeAModelData
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative (frattini P)]
    [Module (ZMod 2) (Additive (frattini P))]
    {S : Subgroup P}
    {hSinv : IsAInvariant Y.subtype S}
    {hPhiS : frattini P ≤ S}
    {c : Y} {n : ℕ}
    {ePhi : Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : NoncommutativeFactorCoordinateData
      hSinv hPhiS c ePhi nu)
    (hn : 0 < n) :
    XiLengthTwoTypeAData.{uP, 0} S := by
  let hK0 : lowerCentralLayerKernel S 0 =
      (lowerCentralTerm S 1).subgroupOf (lowerCentralTerm S 0) :=
    lowerCentralLayerKernel_zero_eq_of_squares_le S data.hSq
  let left : Multiplicative (GaloisField 2 n) ≃*
      lowerCentralTerm S 1 :=
    lowerCentralExtensionLeft data.hK1 data.eKernel.toAddEquiv
  let right : S ⧸ lowerCentralTerm S 1 ≃*
      Multiplicative (GaloisField 2 n) :=
    lowerCentralExtensionRight hK0 data.eQuot.toAddEquiv
  let extension : GroupExtension (Multiplicative (GaloisField 2 n)) S
      (Multiplicative (GaloisField 2 n)) :=
    GroupExtension.ofNormalSubgroupCoordinates
      (lowerCentralTerm S 1) left right
  apply XiLengthTwoTypeAData.ofExtension n hn
    (GaloisField.card 2 n hn.ne') data.theta data.theta_order_odd
    extension
  · simpa only [extension,
      GroupExtension.ofNormalSubgroupCoordinates_range_inl] using
      lowerCentralTerm_one_le_center_of_layerKernel_one_eq_bot data.hK1
  · intro x
    let xZero : lowerCentralTerm S 0 :=
      ⟨x, by simp [lowerCentralTerm]⟩
    let alpha : GaloisField 2 n := data.eQuot
      (Additive.ofMul
        (QuotientGroup.mk' (lowerCentralLayerKernel S 0) xZero))
    have hright :
        (right (QuotientGroup.mk' (lowerCentralTerm S 1) x)).toAdd =
          alpha := by
      rfl
    have hnormal :
        data.eKernel
            (lowerCentralSquareMapAdditive S data.hSq
              (Additive.ofMul
                (QuotientGroup.mk'
                  (lowerCentralLayerKernel S 0) xZero))) =
          alpha * data.theta alpha := by
      have halpha : data.eQuot.symm alpha =
          Additive.ofMul
            (QuotientGroup.mk'
              (lowerCentralLayerKernel S 0) xZero) := by
        apply data.eQuot.injective
        simp only [alpha, data.eQuot.apply_symm_apply]
      rw [← halpha]
      exact data.square_normal alpha
    change x ^ 2 = left
      (Multiplicative.ofAdd
        (typeAQuadraticMap data.theta
          (right
            (QuotientGroup.mk' (lowerCentralTerm S 1) x)).toAdd))
    calc
      x ^ 2 = left (Multiplicative.ofAdd
          (data.eKernel
            (lowerCentralSquareMapAdditive S data.hSq
              (Additive.ofMul
                (QuotientGroup.mk'
                  (lowerCentralLayerKernel S 0) xZero))))) :=
        lowerCentralExtensionLeft_square data.hSq data.hK1
          data.eKernel.toAddEquiv xZero
      _ = left (Multiplicative.ofAdd
          (alpha * data.theta alpha)) := by rw [hnormal]
      _ = left (Multiplicative.ofAdd
          (typeAQuadraticMap data.theta
            (right
              (QuotientGroup.mk'
                (lowerCentralTerm S 1) x)).toAdd)) := by
        rw [hright]
        rfl

@[simp]
private theorem NoncommutativeFactorCoordinateData.toTypeAModelData_phi
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative (frattini P)]
    [Module (ZMod 2) (Additive (frattini P))]
    {S : Subgroup P}
    {hSinv : IsAInvariant Y.subtype S}
    {hPhiS : frattini P ≤ S}
    {c : Y} {n : ℕ}
    {ePhi : Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : NoncommutativeFactorCoordinateData
      hSinv hPhiS c ePhi nu)
    (hn : 0 < n) :
    (data.toTypeAModelData hn).phi = data.theta := by
  rfl

/-- **Higman Lemma 13 (p. 93), factor isomorphism.**

Two actual factor-coordinate packages over one ambient Frattini coordinate
define isomorphic groups when their square-law automorphisms agree. -/
noncomputable def FactorCoordinateData.factorMulEquivOfThetaEq
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative (frattini P)]
    [Module (ZMod 2) (Additive (frattini P))]
    {S T : Subgroup P}
    {hSinv : IsAInvariant Y.subtype S}
    {hTinv : IsAInvariant Y.subtype T}
    {hPhiS : frattini P ≤ S}
    {hPhiT : frattini P ≤ T}
    {c : Y} {n : ℕ}
    {ePhi : Additive (frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (dataS : FactorCoordinateData hSinv hPhiS c ePhi nu)
    (dataT : FactorCoordinateData hTinv hPhiT c ePhi nu)
    (hn : 0 < n)
    (htheta : dataS.theta = dataT.theta) :
    S ≃* T := by
  cases dataS with
  | commutative dS =>
      cases dataT with
      | commutative dT =>
          exact (dS.toTypeAModelData hn).equivModel.trans
            (dT.toTypeAModelData hn).equivModel.symm
      | noncommutative hncommT dT =>
          exact (dT.theta_ne_one (by
            simpa [FactorCoordinateData.theta] using htheta.symm)).elim
  | noncommutative hncommS dS =>
      cases dataT with
      | commutative dT =>
          exact (dS.theta_ne_one (by
            simpa [FactorCoordinateData.theta] using htheta)).elim
      | noncommutative hncommT dT =>
          have htheta' : dS.theta = dT.theta := by
            simpa [FactorCoordinateData.theta] using htheta
          let eS : S ≃* TypeAModel dS.theta :=
            (dS.toTypeAModelData hn).equivModel
          let eT : T ≃* TypeAModel dT.theta :=
            (dT.toTypeAModelData hn).equivModel
          exact eS.trans (htheta'.symm ▸ eT.symm)

end

end OddOrder.Higman.Suzuki2Groups
