/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.AmbientCentralExtension

/-!
# Higman's Lemma 12: factor coordinates over the prescribed common centre

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
pp. 89--90.

The common coordinate on `Φ(P)` is chosen before either factor coordinate.
This leaf assembles the equality-tracked Frobenius normalizations from
Higman's Lemma 11 without changing that kernel coordinate.  The quotient
coordinate alone is adjusted, first to undo the tracked shifts and then to
absorb the remaining nonzero type-A coefficient.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.RepresentationTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

universe uH uC uF

noncomputable section

local instance prescribedFactorLayerCommGroup
    (H : Type uH) [Group H] (i : ℕ) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

local instance prescribedFactorLayerModule
    (H : Type uH) [Group H] (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- Restore a prescribed kernel coordinate after a field automorphism has
been used to normalize the second layer.  The returned quotient eigenvalue
is measured in the restored coordinate, and square-map equivariance gives
the exact source relation `nu = lambda' * theta(lambda')`. -/
theorem exists_typeAQuotientCoordinates_of_prescribedKernel_from_shiftedNormalForm
    {H : Type uH} [Group H]
    {C : Type uC} [Group C]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (actor : C →* MulAut H) (c : C)
    (hSq : LowerCentralSquaresLieInSecond H)
    (eQuot : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
    (eKernel : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] F)
    (lambda nu : F)
    (hcompatQuot : ∀ v,
      eQuot (lowerCentralLayerRepresentation actor 0 c v) =
        lambda * eQuot v)
    (hcompatKernel : ∀ v,
      eKernel (lowerCentralLayerRepresentation actor 1 c v) =
        nu * eKernel v)
    (sigma : F ≃ₐ[ZMod 2] F)
    (theta : RingAut F)
    (hsigmaTheta : ∀ x : F, sigma (theta x) = theta (sigma x))
    (epsilon : F) (hepsilon : epsilon ≠ 0)
    (hshiftedNormal : ∀ alpha : F,
      (eKernel.trans sigma.toLinearEquiv)
          (lowerCentralSquareMapAdditive H hSq (eQuot.symm alpha)) =
        epsilon * (alpha * theta alpha)) :
    ∃ (eQuot' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
      (lambda' epsilon' : F),
      epsilon' ≠ 0 ∧
      (∀ v,
        eQuot' (lowerCentralLayerRepresentation actor 0 c v) =
          lambda' * eQuot' v) ∧
      (∀ beta : F,
        eKernel
            (lowerCentralSquareMapAdditive H hSq (eQuot'.symm beta)) =
          epsilon' * (beta * theta beta)) ∧
      nu = lambda' * theta lambda' := by
  let eQuot' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F :=
    eQuot.trans sigma.toLinearEquiv.symm
  let lambda' : F := sigma.symm lambda
  let epsilon' : F := sigma.symm epsilon
  have hepsilon' : epsilon' ≠ 0 := by
    intro hzero
    apply hepsilon
    apply sigma.symm.injective
    simpa only [map_zero] using hzero
  have hcompatQuot' : ∀ v,
      eQuot' (lowerCentralLayerRepresentation actor 0 c v) =
        lambda' * eQuot' v := by
    intro v
    change sigma.symm
        (eQuot (lowerCentralLayerRepresentation actor 0 c v)) =
      sigma.symm lambda * sigma.symm (eQuot v)
    rw [hcompatQuot, map_mul]
  have hnormal' : ∀ beta : F,
      eKernel
          (lowerCentralSquareMapAdditive H hSq (eQuot'.symm beta)) =
        epsilon' * (beta * theta beta) := by
    intro beta
    have h := congrArg sigma.symm (hshiftedNormal (sigma beta))
    have htheta : sigma.symm (theta (sigma beta)) = theta beta := by
      rw [← hsigmaTheta beta, sigma.symm_apply_apply]
    have h' : eKernel
          (lowerCentralSquareMapAdditive H hSq
            (eQuot.symm (sigma beta))) =
        epsilon' * (beta * theta beta) := by
      simpa only [LinearEquiv.trans_apply, LinearEquiv.coe_coe,
        AlgEquiv.toLinearEquiv_apply, map_mul, htheta,
        sigma.symm_apply_apply] using h
    have heQuot : eQuot'.symm beta = eQuot.symm (sigma beta) := by
      apply eQuot'.injective
      simp only [eQuot', LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply]
      exact (sigma.symm_apply_apply beta).symm
    rw [heQuot]
    exact h'
  have hnorm : nu = lambda' * theta lambda' :=
    kernel_eigenvalue_eq_typeANorm_of_normalForm
      actor c hSq eQuot' eKernel lambda' nu theta epsilon' hepsilon'
      hcompatQuot' hcompatKernel hnormal'
  exact ⟨eQuot', lambda', epsilon', hepsilon',
    hcompatQuot', hnormal', hnorm⟩

/-- Restore the prescribed kernel coordinate and then absorb the remaining
nonzero coefficient by rescaling only the quotient coordinate.  The actor
eigenvalue and the relation `nu = lambda' * theta(lambda')` are unchanged. -/
theorem exists_typeAQuotientCoordinates_of_prescribedKernel
    {H : Type uH} [Group H]
    {C : Type uC} [Group C]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (actor : C →* MulAut H) (c : C)
    (hSq : LowerCentralSquaresLieInSecond H)
    (eQuot : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
    (eKernel : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] F)
    (lambda nu : F)
    (hcompatQuot : ∀ v,
      eQuot (lowerCentralLayerRepresentation actor 0 c v) =
        lambda * eQuot v)
    (hcompatKernel : ∀ v,
      eKernel (lowerCentralLayerRepresentation actor 1 c v) =
        nu * eKernel v)
    (sigma : F ≃ₐ[ZMod 2] F)
    (theta : RingAut F) (htheta : Odd (orderOf theta))
    (hsigmaTheta : ∀ x : F, sigma (theta x) = theta (sigma x))
    (epsilon : F) (hepsilon : epsilon ≠ 0)
    (hshiftedNormal : ∀ alpha : F,
      (eKernel.trans sigma.toLinearEquiv)
          (lowerCentralSquareMapAdditive H hSq (eQuot.symm alpha)) =
        epsilon * (alpha * theta alpha)) :
    ∃ (eQuot' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
      (lambda' : F),
      (∀ v,
        eQuot' (lowerCentralLayerRepresentation actor 0 c v) =
          lambda' * eQuot' v) ∧
      (∀ beta : F,
        eKernel
            (lowerCentralSquareMapAdditive H hSq (eQuot'.symm beta)) =
          beta * theta beta) ∧
      nu = lambda' * theta lambda' := by
  obtain ⟨eQuotOne, lambda', epsilon', hepsilon',
      hcompatOne, hnormalOne, hnorm⟩ :=
    exists_typeAQuotientCoordinates_of_prescribedKernel_from_shiftedNormalForm
      actor c hSq eQuot eKernel lambda nu hcompatQuot hcompatKernel
      sigma theta hsigmaTheta epsilon hepsilon hshiftedNormal
  obtain ⟨u, hu, hunorm⟩ :=
    exists_ne_zero_mul_apply_eq_of_typeA theta htheta epsilon' hepsilon'
  let uUnit : Fˣ := Units.mk0 u hu
  let scale : F ≃ₗ[ZMod 2] F :=
    (uUnit.mulLeftLinearEquiv F F).restrictScalars (ZMod 2)
  let eQuot' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F :=
    eQuotOne.trans scale
  have hcompat' : ∀ v,
      eQuot' (lowerCentralLayerRepresentation actor 0 c v) =
        lambda' * eQuot' v := by
    intro v
    change u *
        eQuotOne (lowerCentralLayerRepresentation actor 0 c v) =
      lambda' * (u * eQuotOne v)
    rw [hcompatOne]
    ring
  have hnormal' : ∀ beta : F,
      eKernel
          (lowerCentralSquareMapAdditive H hSq (eQuot'.symm beta)) =
        beta * theta beta := by
    intro beta
    let alpha : F := scale.symm beta
    have hscale : u * alpha = beta := by
      have h := scale.apply_symm_apply beta
      change u * alpha = beta at h
      exact h
    calc
      eKernel
            (lowerCentralSquareMapAdditive H hSq
              (eQuot'.symm beta)) =
          epsilon' * (alpha * theta alpha) := by
        change eKernel
            (lowerCentralSquareMapAdditive H hSq
              (eQuotOne.symm (scale.symm beta))) = _
        exact hnormalOne alpha
      _ = beta * theta beta := by
        rw [← hunorm, ← hscale, map_mul]
        ring
  exact ⟨eQuot', lambda', hcompat', hnormal', hnorm⟩

/-- **Higman Lemmas 11--12 (pp. 89--90), noncommutative factor
coordinates over a prescribed common centre.**

Starting from the caller's generator and kernel Singer coordinate, construct
the actual Lemma 11 field model, retain both equality-tracked Frobenius
normalizations, and absorb the final nonzero coefficient on the quotient
side.  Thus the returned kernel coordinate is literally `eKernel`, while the
quotient and kernel actor eigenvalues satisfy Higman's source equation. -/
theorem exists_typeAQuotientCoordinates_of_prescribedKernel_noncommutative
    {H : Type uH} [Group H] [Finite H]
    {Y : Subgroup (MulAut H)}
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (hH : IsPGroup 2 H)
    (hncomm : ¬ IsMulCommutative H)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions H).ncard)
    (c : Y) (hcgen : ∀ g : Y, g ∈ Subgroup.zpowers c)
    (eKernel : Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] F)
    (hnTwo : 2 ≤ Module.finrank (ZMod 2) F)
    (nu : F)
    (hnuPrimitive : IsPrimitiveRoot nu
      (2 ^ Module.finrank (ZMod 2) F - 1))
    (hcompatKernel : ∀ v,
      eKernel (lowerCentralLayerRepresentation Y.subtype 1 c v) =
        nu * eKernel v) :
    ∃ (theta : RingAut F)
      (eQuot : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
      (lambda : F),
      theta ≠ 1 ∧
      Odd (orderOf theta) ∧
      (∀ v,
        eQuot (lowerCentralLayerRepresentation Y.subtype 0 c v) =
          lambda * eQuot v) ∧
      (∀ beta : F,
        eKernel
            (lowerCentralSquareMapAdditive H
              (lowerCentralSquaresLieInSecond_of_agemo_eq H
                (agemo_one_eq_lowerCentralTerm_one
                  hH hncomm hxi hlen))
              (eQuot.symm beta)) =
          beta * theta beta) ∧
      nu = lambda * theta lambda := by
  classical
  let m := Module.finrank (ZMod 2)
    (Additive (lowerCentralLayer H 0))
  let n := Module.finrank (ZMod 2)
    (Additive (lowerCentralLayer H 1))
  letI : Nontrivial (lowerCentralLayer H 0) :=
    lowerCentralLayer_zero_nontrivial_of_xiLengthTwo
      hH hncomm hxi hlen
  letI : Nontrivial (Additive (lowerCentralLayer H 0)) := inferInstance
  have hmpos : 0 < m := by
    dsimp [m]
    exact Module.finrank_pos
  have hfinF : Module.finrank (ZMod 2) F = n := by
    exact eKernel.finrank_eq.symm
  have hnTwo' : 2 ≤ n := by
    rw [← hfinF]
    exact hnTwo
  obtain ⟨eOne, mu, _hmu, hcompatOneAll, _hlambdaOrder,
      hlambdaGen, hnm, hdegreeOdd⟩ :=
    exists_originalXiActor_degree_dvd_and_odd_quotient_of_generator
      hH hncomm hxi hlen hprime c hcgen
  let lambda : GaloisField 2 m := (mu c : GaloisField 2 m)
  have hcompatOne : ∀ v,
      eOne (lowerCentralLayerRepresentation Y.subtype 0 c v) =
        lambda * eOne v := hcompatOneAll c
  obtain ⟨iota⟩ : Nonempty
      (F →ₐ[ZMod 2] GaloisField 2 m) := by
    apply FiniteField.nonempty_algHom_of_finrank_dvd
    rw [hfinF, GaloisField.finrank 2 hmpos.ne']
    exact hnm
  have hnuPrimitive' : IsPrimitiveRoot nu (2 ^ n - 1) := by
    simpa only [← hfinF] using hnuPrimitive
  have hactorOdd : Odd (Nat.card Y) :=
    actor_card_odd_of_primeSupport_xiLengthTwo
      hH hncomm hxi hlen hprime
  let d := m / n
  have hdegree : m = d * n := by
    exact (Nat.div_mul_cancel hnm).symm
  obtain ⟨r, eQuot, lambdaF, sigma, epsilonF,
      hepsilonF, hcompatQuot, hthetaNe, hthetaOdd,
      hsigmaTheta, hnormal⟩ :=
    exists_higmanLemmaElevenFieldCoordinates_with_trackedKernel
      (K := F) (L := GaloisField 2 m)
      hH hncomm hxi hlen m n d
      (GaloisField.finrank 2 hmpos.ne') hfinF rfl hnTwo'
      hdegree hdegreeOdd iota eOne eKernel c hcgen lambda nu
      hlambdaGen hcompatOne hnuPrimitive' hcompatKernel hactorOdd
  let theta : RingAut F := (frobeniusEquiv F 2) ^ r.val
  let hSq : LowerCentralSquaresLieInSecond H :=
    lowerCentralSquaresLieInSecond_of_agemo_eq H
      (agemo_one_eq_lowerCentralTerm_one hH hncomm hxi hlen)
  obtain ⟨eQuot', lambda', hcompatQuot', hnormalOne, hnorm⟩ :=
    exists_typeAQuotientCoordinates_of_prescribedKernel
      Y.subtype c hSq eQuot eKernel lambdaF nu
      hcompatQuot hcompatKernel sigma theta hthetaOdd hsigmaTheta
      epsilonF hepsilonF hnormal
  exact ⟨theta, eQuot', lambda', hthetaNe, hthetaOdd,
    hcompatQuot', hnormalOne, hnorm⟩

/-- **Higman Lemma 12 (p. 89), an actual noncommutative factor over the
common centre.**

Fix the ambient Singer generator and coordinate on `Φ(P)` before choosing
coordinates on the invariant factor `S`.  The second lower-central layer of
`S` is identified with the ambient Frattini subgroup, so its kernel
coordinate is literally the displayed composite with `ePhi`.  Only the
quotient coordinate is normalized.  The returned actor equations are stated
for the original ambient generator acting on `S`, rather than merely for an
abstract generator of the faithful restricted range. -/
theorem exists_noncommutativeFactorCoordinates_of_ambientFrattiniSinger
    {P : Type uH} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P))
    (hncommS : ¬ IsMulCommutative S) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hEA : IsElementaryAbelian 2 ↑(frattini P) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
      hEA.zmodModule
    let n := Module.finrank (ZMod 2) (Additive ↑(frattini P))
    ∀ (c : Y)
      (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n),
      2 ≤ n →
      (∀ g : Y, g ∈ Subgroup.zpowers c) →
      IsPrimitiveRoot nu (2 ^ n - 1) →
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∃ (hK1 : lowerCentralLayerKernel S 1 = ⊥)
        (hterm : lowerCentralTerm S 1 =
          (frattini P).subgroupOf S)
        (theta : RingAut (GaloisField 2 n))
        (eQuot : Additive (lowerCentralLayer S 0) ≃ₗ[ZMod 2]
          GaloisField 2 n)
        (lambda : GaloisField 2 n),
        let eKernel :=
          (factorLayerOneLinearEquivAmbientFrattini
              hEA hPhiS.le hK1 hterm).trans ePhi
        theta ≠ 1 ∧
        Odd (orderOf theta) ∧
        (∀ v,
          eKernel
              (lowerCentralLayerRepresentation hSinv.restrict 1 c v) =
            nu * eKernel v) ∧
        (∀ v,
          eQuot
              (lowerCentralLayerRepresentation hSinv.restrict 0 c v) =
            lambda * eQuot v) ∧
        (∀ beta : GaloisField 2 n,
          eKernel
              (lowerCentralSquareMapAdditive S
                (lowerCentralSquaresLieInSecond_of_agemo_eq S
                  (agemo_one_eq_lowerCentralTerm_one
                    (hP.to_subgroup S) hncommS
                    (restricted_range_isXiActor hxi hSinv)
                    (restricted_range_hasXiLengthTwo_of_xiLengthThree
                      hP hncomm hxi hlen hEA hSinv hPhiS hStop)))
                (eQuot.symm beta)) =
            beta * theta beta) ∧
        nu = lambda * theta lambda := by
  classical
  dsimp only
  let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
    IsAInvariant.of_characteristic Y.subtype
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  letI : IsMulCommutative ↑(frattini P) :=
    IsMulCommutative.of_comm hEA.comm
  letI : CommGroup ↑(frattini P) := inferInstance
  letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
    hEA.zmodModule
  let n := Module.finrank (ZMod 2) (Additive ↑(frattini P))
  intro c ePhi nu hnTwo hcgen hnuPrimitive hconj
  have hSneBot : S ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiS)
  have hinvS : involutions P ⊆ S :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSinv hSneBot
  have hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  have hlenS : HasXiLengthTwo hSinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_xiLengthThree
      hP hncomm hxi hlen hEA hSinv hPhiS hStop
  have hprimeS : ∀ p : Nat, p.Prime →
      p ∣ Nat.card hSinv.restrict.range →
        p ∣ (involutions S).ncard :=
    restricted_range_primeSupport hSinv hinvS hprime
  have hPhiNeBot : frattini P ≠ (⊥ : Subgroup P) := by
    intro hPhiBot
    have hcommBot : _root_.commutator P = ⊥ :=
      le_bot_iff.mp
        ((OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP).trans
          (le_of_eq hPhiBot))
    exact hncomm ((commutator_eq_bot_iff P).mp hcommBot)
  have hinvPhi : involutions P ⊆ frattini P :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hPhiInv hPhiNeBot
  have hPhiCenter : frattini P ≤ Subgroup.center P :=
    (commutator_eq_frattini_and_frattini_le_center_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime).2
  have hK1 : lowerCentralLayerKernel S 1 = ⊥ :=
    lowerCentralLayerKernel_one_eq_bot_of_xiLengthTwo
      (hP.to_subgroup S) hncommS hxiS hlenS
  have hterm : lowerCentralTerm S 1 =
      (frattini P).subgroupOf S := by
    rw [lowerCentralTerm_one_eq_frattini
        (hP.to_subgroup S) hncommS hxiS hlenS,
      factor_frattini_eq_ambientFrattini_subgroupOf hSinv
        (hP.to_subgroup S) hncommS hxiS hlenS hinvPhi hEA hPhiCenter]
  let eKernel : Additive (lowerCentralLayer S 1) ≃ₗ[ZMod 2]
      GaloisField 2 n :=
    (factorLayerOneLinearEquivAmbientFrattini
        hEA hPhiS.le hK1 hterm).trans ePhi
  have hcompatPhi : ∀ v,
      ePhi (elabRepresentation 2 hPhiInv.restrict c v) =
        nu * ePhi v := by
    intro v
    have h := DFunLike.congr_fun hconj (ePhi v)
    simpa [LinearEquiv.conj_apply] using h
  have hcompatKernel : ∀ v,
      eKernel
          (lowerCentralLayerRepresentation hSinv.restrict 1 c v) =
        nu * eKernel v := by
    intro v
    change ePhi
        (factorLayerOneLinearEquivAmbientFrattini
          hEA hPhiS.le hK1 hterm
          (lowerCentralLayerRepresentation hSinv.restrict 1 c v)) =
      nu * ePhi
        (factorLayerOneLinearEquivAmbientFrattini
          hEA hPhiS.le hK1 hterm v)
    rw [factorLayerOneLinearEquivAmbientFrattini_equivariant
      hSinv hEA hPhiS.le hK1 hterm c v]
    exact hcompatPhi _
  let cS : hSinv.restrict.range := hSinv.restrict.rangeRestrict c
  have hcgenS : ∀ g : hSinv.restrict.range,
      g ∈ Subgroup.zpowers cS :=
    forall_mem_zpowers_restrictedRange_generator hSinv c hcgen
  have hcompatKernelS : ∀ v,
      eKernel
          (lowerCentralLayerRepresentation
            hSinv.restrict.range.subtype 1 cS v) =
        nu * eKernel v := by
    intro v
    exact hcompatKernel v
  have hnPos : 0 < n := lt_of_lt_of_le (by omega) hnTwo
  have hnTwoF : 2 ≤ Module.finrank (ZMod 2) (GaloisField 2 n) := by
    rw [GaloisField.finrank 2 hnPos.ne']
    exact hnTwo
  have hnuPrimitiveF : IsPrimitiveRoot nu
      (2 ^ Module.finrank (ZMod 2) (GaloisField 2 n) - 1) := by
    rw [GaloisField.finrank 2 hnPos.ne']
    exact hnuPrimitive
  obtain ⟨theta, eQuot, lambda, hthetaNe, hthetaOdd,
      hcompatQuotS, hnormal, hnorm⟩ :=
    exists_typeAQuotientCoordinates_of_prescribedKernel_noncommutative
      (H := S) (Y := hSinv.restrict.range)
      (F := GaloisField 2 n)
      (hP.to_subgroup S) hncommS hxiS hlenS hprimeS
      cS hcgenS eKernel hnTwoF nu hnuPrimitiveF hcompatKernelS
  have hcompatQuot : ∀ v,
      eQuot (lowerCentralLayerRepresentation hSinv.restrict 0 c v) =
        lambda * eQuot v := by
    intro v
    exact hcompatQuotS v
  refine ⟨hK1, hterm, theta, eQuot, lambda, ?_⟩
  exact ⟨hthetaNe, hthetaOdd, hcompatKernel, hcompatQuot,
    hnormal, hnorm⟩

end

end OddOrder.Higman.Suzuki2Groups
